-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1470
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:08:43.116765+00:00
-- url     : https://prove2.me/submissions/d87715a9-95d4-4a25-ae70-307f568d67de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 264208633 ≤ n < 264388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 264209883 1250 264208633 264208639
    0x12a03020c150d050a0e0d080a05010f05030d030b0f1e030c04050f1501020c4c0e0d060507080108010e0d2705060f04090b180402011b12050301080606010804021e0f 72
    0x518510b0031000792881e8030032740c1e038940d15518081c00003400c9a40315151506403203009024002001e6080021000380c00360038a000d5006180c0d9981c000305946000700d0740d003686520203c000081c06c1d104105420004495100c90095080c902008a0b8000d051400340c0d000c541042c034140d1200f06400100e1804910070406134200545440b030300301000040d0404400f0224404400115641400c2648005080c00602d12801a0030b01e907040c840e18050b600050203200301820041c04000c00e070300c072601543c4065843c0c10104800b88010300c0880c0083c0034951918489100812020054007170040c842c420903024044020050395810741c5603044641c01c6001440b0041c441d985444c070000c18210598028855100ca00c1c0c54980142282d043c501c02407201c642e900d4240d81c4c1d190756190015219442514011f040401e20309443c080024110760b14a0000742c0155580340c1c0701c0d81003c1c005464020080d0406045c48408001c010043e50b0b40141029245060240540c1000c01032010030000381000303480d5a8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 264211133 1250 264209883 264209893
    0xa02090d140f1f0c1d04200a0305160813030f020f0105070305181212060a170d0e0405280e100e010612150506012a03020c150d050a0e 59
    0x210751442815510f205002d00582045099105501a42c1429103859407a007a244400000c0e401e528059000c000c180b507007040d08504010402c58205000e40c091044100403a644109000c481f0101e4080c460030f6440b641004500c50a256a81c5510010311500090070001d60211414010f8404d0080b4484034500340000d0043c4e080040d0086d0141c88200c036022090101d0700d811610b0600b002031004141c03110580c01c14500f01207a18814904070008010315000010840f00144082014495103203284c0c1410191801c03555580e00182000b80200b07010780304c0c5041c602440711022202c0510100b2960a000410b031201204484070054603c4003810001409003150500c84002a60495600140c00d00000c000183e11480700310030902c5044800340200c44629900009902c5580c04150030a005061900c04011624001690301800c860011514140100380104060301000046000c00003260985c01c4031000c4e40c8160414041c08504100b4103440c1c00204a004400f03038041d501c070b5456602916 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 264212383 1250 264211133 264211153
    0xf0f0f190c0b060103090c0b0a0306030f0308060405010b180108040507080a0b090f010c0f0f0306030605270303060f040203180313080f0a02150d06091509050a02090d140f 75
    0x1030880344401e0320648442c0040c07000140c442d07119124101a1650212501d0485401c0191078081d40c0c1040c581c01082c1580d42c440403000c6081440100c0034940b09503a00500c0d80382c01403d10081c0c403c10303403003107a100f007043c007460f01c480003000801480d10f40e00380391800c245c1d80d842c106103261407020751044402c6d0151840000501052a030010310800480f4100d942d04488112a28201d41c005d401000001e1200c4803c0300800d40304644c1c4c85c440e001c5514000c100d40d030b12606c0320f0040300c505071502c007607106510605415103550031840c200c082c048900554218540341d80858030000820049174842d9a00100040305100140090500c00b00c12500f00c9854010300360404941278014010f40600f03106184c4841c0c84420300003109844e2940c041c04041c43c0f18011301d4001c503203802c00d00701c52010075100c03c0003207400603152049000e002c0c4014500045286020010710480b50081c001c0d845407801000884203c1d01c525240344442a84000c203104401122400507052861907014603c0a0140f03c41c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 264213633 1250 264212383 264212387
    0x180305041811040603020933031021230714060c06010e070206091212150d030207090c02150408070302100903090e0601050a020706051608070503030403080c0f0f0f19 73
    0x3e0f240311fa1040d034098076000b1b4440c40d40c07031490320000c0e203100200c2c003043c092007041000c2c1c002550b007211041c020918002d80700c070f5400300c0912500d501c030320454080c4c412030740030300200c403180319502010700a9151440101d034140a03183c5125003e8041003014204c441003941d200d200442c1c0440b0510002d40b003195856580603c2c48500c19242c0c1d40c0180724001c041849882c01040d0504540c0f04000c0840c9400350007015150345500080141d00405424502c1006607103484071500b401340e1007039000c6d00026041403501000c580326140c00c1c03002c41d40880b0401001118040b82c2c10340241c0c04c0040c50b51141003500c0c7c100c0ca0014035049120041c0d05140121042580140c894130540740c414a842c046641c907000110b07000d0241000642c0107a00c1007000f0052300d030081e8001c100800749250404403809803a150020503500016048800394000001c000500da80039000701c0d005141ca01007146011065902d484141c0030381d0000810000d800200c0c1595294030310100d03041060100c1c15021031b4903e100b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 264214883 1250 264213633 264213637
    0x120312020c0715050403022701050916030c0309061410080f0613020a0b0f03040c0501050c0d0c111c051603020d170412060b0906091911070503030103051018030504181104060302 78
    0x4203038048c4410038008202403920848a500c40c256000a81180455282d8210080c0c8003100c42c66041c1035840f0980c60105515015504101c06180c0c00c0c032106040c0700c071010413101450391004c8415001041e81c803810400c04502c40380c1202c408800c010710401d01d400003490070040d980c40034096072400203050703d5004c003810203940301c0c3d0300441403a6080390351003005451512405561500903000040c204c0f032010301512405d07000078012000c1200244e032290100b40404211415100112542422003080120421142d0081c0c032406500c010038a1941d40410160100400000c001466440350074001990503001d86004001025907640030380014246000100711380f2035200c0c01703021041d00084141c144400042d0003203e0b600c4900310301c0007449541000620310522061100c1e1010000300020500c10000355010358002c00107840f52160480c4400b0440c0c03d8910704541724034101072842d010940100568089903500303040c291105003a8081c0c4e00080802100a0007002804500031400a51640c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 264216133 1250 264214883 264214939
    0x1080a0309080304030206030601080a110f0714070501080711032b051605031b090301050702011508070305030304080c010b0409060b0f0a0e01030f02060d0204120312020c071505040302 81
    0x12001c44075038490000c20345034482e030302010b90014400c201180c1c880d445224410780c419121030000400f418620300803140c503406003c000c142d009010500d41c003441929414804400369031001401650300c2d000000e051044000d0050040c0301d41844403ca5014043c0110b500340b040b000201101140e031240d504580c40c064a000b80c400c2846d143c00034114440c00b0404c0e010f02c3d20180c8a080c10350f56400312a1b00c608a4405158541c95030502c100802918240656800b504040d000481c4103004051020317102001030b8402107065205100410100301e0100445c0e030007580161080b80c0d40c2042d0f035401405414160102c0e904039280214180c203100b400c1d400f01e051801e045420391860b496540400c144c5104a000d10700340300d2850001080046c0005a10149081c03005d48058280440155010b0803604543e22010450911462803420035601c103000c001c02010301d1400314107200003150710b155502d0450141c44901ca50344840400740c02c0c000c1c6c0989000316030045c00902c8110052000140c0190984 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 264217383 1250 264216133 264216137
    0x13050414300901080a0e0a0c0e090d020331120c0e010f1d06040b19090b0916031a0301150905060303121b09040c05070212241e01080a03 60
    0x35415802140498211507020b4016036408002d03840b0030407030320300425840850100364440e422002d800a403801c841e010051000f103165500d14030f0014001414909105c01050840d0070420a90540d46810101c46480a00101001040d61035144586601d4080b0340c1060142c2e21307095900c001004402e1006100b0f8400080301c011003640c1c0c82c007440304036428038010580e0b504800603a1613501041c40317805a038044001000411304400c103002150202d03454284030300030898403a9042c031000da45401015990f10056549620074a480902c0035008001c1900e01c408140c0c44001c5048a800d82503202c80d100d2200500030048100d450303e05106000c060b100b00c02c0383c9401c220024a4510380441500c4e401c5811403440c0b0025541c0d6805c0c100c41c80d0300005003031400102031004c0c1d00d40385c450388141110a010790325083d80d01c0c0c4c45401000144500140d000c24664000400284000001c0508200c2c190b1141c4080d0b0188d00c40d0342c000c8800c401c0d0040c0040102d250800001021600080c8000856001e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 264218633 1250 264217383 264217453
    0x20a0b03160f110c040e070504060f0f0b0307171b03090321040f1202010603050d081f1401110f0d0305010f0f0e07080903090301110904150513050414 66
    0x118000360342001580d842e0781060f402000c01c0304081d080a0f04a03880d01010314040d07d02113500d8000141c1101e055401109020446100034000c00c007518485a003e0306096840d0703805c41c0350a201c010840481411a00054203590020aa0250026048031070704480b480a140e00e85c82c003010040c2e9240c000451528448c4e030400004c2d0a11080c1c40901c0d401340d904070003854149159900d40100f071000341d4481004640d03075800008080b550038051240f001039a83c0c1e811441d414008100c0020031070b00c0503881301008a40600300031590069022048900081c240050742072210701400b03040203000503101d0014029043c103e041700d40d0507408035040c0d991081e004401c007030f244c1c0031005420004d03008603001c4640b80c10200745144d016a480941c00b40c03814045034034000c1418082425610501104204010003143c1c4002900e464041c1da20310041c1641c03c5074820345401c0014180345401032808650b1907548001c03034203104400894440c441d013464111081180e180c403d00c18400c4400500b00e00382c40013 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 264219883 1250 264218633 264218657
    0x2030a240603021804020a030b13150c0e040b220221040803041b0302040e0f010b060c1018020a0e0109110306030a2a080609010606050c06040609020a0b0316 69
    0x514440c440070341c0d40184c004200000d410110320140880a04207a81c0400d14040000c00a030000d0300a030b100c0c6012006506204840c0c7c41c00c54014200711010502c464204280e081500f82d00142c4135404034021140441c1c442c4848001c40c40c40c0144451a91807003d19040aa90403500c0fa00108030220a83c411a03c0c5000400b129411400090782d00600035041003010501296203e0110459841071f10b840c0d8048035902e40c0014101c58100310040a16040b0301895000c041080c030841051302c1342611281c0c80c101c0403048880d140c0c11015001d058a5a5030300c140742039441c441348400d20081d80609440308207a00c070030440310b01d40c009100c0c1700a05030410010203500c1140c6400d0b44d00a500c0900205a1401aa0354102c1c00d108820b0720148071103203152800d1030b4407000034003031300042c07518101400d0b0500380060313040c0c00c0d01e00c80c0d003007002071103810000c400328003100041c290761044d000640000c414051348002001180355a128507403108000c8180f15550740501c501504410407902e460300c804034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 264221133 1250 264219883 264219953
    0x8040c0b040f0e1509040f0c0b0705011b0e01090306050c07120c060b06040f140102100c1d090103030219030e04020319050604090206030a15030507030f0b0903160f02010c02030a 78
    0x100c04406a411580e05c00102c2c2c000346141d00c0103c0154401c0400490310b03038649840c103585030000310042e07031180c0d1601040c80341400c1502d0080206111864410038071a10000040c1c1a08914800102a603590b40002241d411b12803081c0c900641e4408540c0300c44e0f4030400300c010000440004190f5405260950700306075403a020741143d085640c0c50881c01450352600880610501340b60741420305501403641e000d1400d600700d03c40c12024220580f11360030a03200600340c480d0f030000d50b540d4444c001c4840e00010700200f6000a01d203a10220020203405180321503140841d0040c00041f80036030048d001009101111070040070440d098152807a04001c20341d21003042009a41c0b04210203074009008002003850f045c481e40080d0303410092040d021195580d03030b60781c061030300340980c0c010358402152190a0f0208164005140e03003100485008505200e900c120100613541c1001c1c0081070f00354010004411640200b68480768190000d054401202d11070900034200c003590f0900146240c484001200144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 264222383 1250 264221133 264221161
    0xa050609030406091505090409050105010f1a0d0c050f040e0a0b03151f03050307060c080609010608012106050f040302070f060c0b3102041d0604020108040c0b040f0e 73
    0x43d11580c40381d203000e1a0220000315603840040b000c013007040400c4403038401d0712540a22640346103c2c9000244c5989030111840a0810680052070002140c611010303544807000b040c1e8000710600c3c4400194100d40c0f520a94052040004101c1001401300307001503802c0e6401c6a4611130081108140903150400081503100c0d17028076240b80f002000c11000c6000780c02098610000c00c008105d020704403540340d8641034a90b800c00b003000c5820684992482d241c0ac1e5002041c180c11000a451846135541804000f50102005010304001d4800041000321110415690300000315000f1000304518108200cbc44c02c0d107110101d40a8000d0303c50420001200300c03240010b002210005d90b00c44038008030303954494544046c00303070205048094600031040b141d0200389600202c480e05542e0403008800c41c2c41400146c404004c800a03516035000b03403d00031540b002c205180e02580c24a8000495500c624160859080981040040782c0000c1408640685404e056070305482030314021130b625688444202c036481c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 264223633 1250 264222383 264222389
    0x20106030f051507081603111e180f1005030c1309092609010e040f02040e01170d050901080a06150908061b09060c0109060525020601030506061e0a080a0506090304 72
    0x4114566005450343c4030380d106404560150300682d1400c9092401454140405083c08030300c0f840014075180c0d00f80700c92290b404220710a507095032000e142c0b00001035031500ccc0d0f0443c01050100010000303981038044001c075060b198113000e5941d6280d8494071580011b040700f0000300c1e485007061100803036084a0f201001d21580c4520241b51074402c014004456041010588540094554440503214003d40c00a8009841c0c4a0b00c13410407585410340038482101c900408a24a410a0b800206d00d41e074480c00701c2d00e80300000e007001101034407030501754401803480d640210380035600b01814101040d48154402c0440c1c0d100822641c3c16100d5110b0b0580307001313466165114228040002c0042c50812102030880c090b0158000519017001ea01c079a0142c42d0102c40b0a092925200e00702e0200c03100000e4855088103803440140740f60760650740d95681e0707950042c203030300d02c10714003480c3c0c08000311940c2d0744407402c040e800341040041ea503442c12260fa54026000702241d441c05404c0c00100855400015a011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 264224883 1250 264223633 264223651
    0x10504021309020a0308210705090603010905040f0507151115041101050d050a02030601030c050307211d0313170705130e06090c03060a110d0b01020106030f05150708 73
    0x440920601c00c0041c00e89480403a00000741800020100710114090080d4190110607440c18800d0701c0d00c600da50715030040a40e07060010510500c0390f1a03d80c0016a8155955000c0c001555251401c080305c044c058180000d0141c0b05000700882c01400c0781c2011000c0100a895000ca00b620a40b1055190b0079030305400e14881c00000c0000740030401c4004943c01000060602c5494511070001d0101600c4084031035035081d5400005028555a241c03069544003c07403894110b09508140384001c204141d22250925601170f01d1003011021107071a03010401001d4984800309200c182c010410703440390440300b400c604500c401e10380002c440003101007070360664080b0740c081c1205900f00b404008032005e48200820b10746554030105081d0050170890360b4081c020b108020a0b0307000c05502058a858070003441c00f103541e424840128040c042e003205070359404111b4000441e400d902d013070040b0700400d00d603800a0b2806091fa1044d00030700030041440e11502814000882d540c0c0c0c0c4031101030740e5111054031104a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 264226133 1250 264224883 264224899
    0x417010b0a0f1d22052b1d0105090604030c0f0e010302011407030513030506060a080714040209371202130903020f071502010b030109020130140105011101050402 71
    0x107050410442c1544903000740e58a0302081c102520451190740101300881d0503078041004103460061805034892802015840404000c655880080c101c03a100b402400720707003107080640b0546a001d20300342c4440e590080c00203034480780d4038149104008810311a2200c504d444030008a03c0d105a18000c0d41600c0e010384034090b000d00140740d40e0160754400310080d403c0001c1070207203101c0001485003000085008100502003404c1078410440031101c42d501c0082103078000d4504200c40c445e2210a110904011200140c039504850081500528154408840303945402440000c1a0004244000d001d001e081c0e00d00c3d50540b2101141c04030f0380a0013000c2e600583c80c141804000c103a54009543c8980720340306480c4401d0361a410180b07003090301d402c0340440c00d40c0000154000741d824414400d0f600c01c100c00a01110115400207000c0001c1c0a82c40c81d41c0103000c0e0f06d11144c81c072180001400d85140e01f507040009602001c1000420f9200303028444c0011000e6481704003008050003118001c41d00185106 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 264227383 1250 264226133 264226169
    0x180303070230161b0b0a030c18060c0807060c03060303140304050703020d0f0b0c03150f0604050402030702030c0d020a20090c03100506030406060f0e10030803060103020417010b0a0f 80
    0x100300d4040000104c5100c000315028159034416007981c20002d01c40c1494040d1125036401002c0c064492040405040150714005c182ca089070b000d07110421640c40e41451800514a07040030b60036441519800b40c4801c0c02c02c0d007074612003549544604100d0f03010b030361890f17035946498042044074882904c02400503030120f031007407015207001004003c00c01d2142044540d001c0d1a6a90010130b140c04a84000c01600080200b0108081d07100c450070807010119072005503c41d00368001800d500981c06914092a0f010000811841c0200210b40e080d0102d002100d184901e501002503940e03048507030488010320707150851a841c2010041121072440014113070200c640e1108000d0582d604014178880c41100c0341c45001840741c85200085001c0c07406070001049250038003410142282e05a4041e004850340ca2080040300070a00c10200c003a41e50040c01e1556a40710035004030047d001d99082000c1c1a0640f2070f02030040b00056000d000181c1c8103079040c0e0403a50350385a03ea02c1781126446800b0140060132164 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 264228633 1250 264227383 264227407
    0x50f040302061609060f050903060405070501030b031204030609020301061707030623241305040506090c0310020c1501150f2102090a170d170709030308180303070230 73
    0x244441b40b10b01c2c41d0403030401048600180ca854001c1e80c040e9100e0300100380c00d1020756814001c1c414508415801802c4001c0c0140310212644942c1c4805840507030b8854007101159000c1d0003c60003440d5084003c80344540841240d902c0705c1071032004a0300e840c40c003500c03400d158400140c6444a40302001030442513a480d103a111001000005001240c0d2200341c01924031566922480c0300452000d003c0000d10340382500c0c11924108002d004406698030008110070541c2d0009803950031a440000d026131956070207203d6601e00010302940c11860419034001081d002c0e00b500240c00030200310360b40c1c14480000c1c0802964504011040c1c1103c005184032084a400301c2500148000103003c1c01114941b40d036003200120f03c0300450f281c0e61440d040086010390880d4050580344804203148913a0205040c02c11000d40250540d20004090080305800180300f039128000c0540000c02c62010f80e03950f032603c0c4100a459035016040481c0410b00201a45103010407010b24880d55240c6c541140d107000041112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 264229883 1250 264228633 264228647
    0x180f3c011409010c06050a0f060b04140d05011104090903020c0405070210151203020102130f053109030203031008060c07080c120414040506040203090717010b0301050f04030206160906 81
    0x851810b02004d44100e00c009042480350b28440c604402000804680c3c10500800782c46a0780e2048034a104103003c203200210298600c0789902100322034404a07402d0618100e400351083e10701c01c85c64182c0100e8009101f00484d00701d48402880b0b80e083c1c4202103004401c000c202c0b80140d44104c0180e215401040700c6803030030b501c84000040d141d03100e1201560760b005240b40300709985404034010703500403404031070b00d0100041c0c10001d07082202c514400f1a0900000c01c41707000d040b5404220f0214061800000d540c114030110440d4192100c00340710764a02d80c100655254416030f0903007a40100001d00003051a80810341c24016134144440c90702e8005a41c1b240002e03500704c0482411140200210582042180b50080c0000c1c4880d681c2895400026020001217460081550380183d004104000302e182001c0b50003420f89002d14044ca1440c4007104000740104840c1c070328640c0562800c0140040443c4280f2800e1050744285c1c01c80318150355480303800c1010360161041c0408226401014000c86005e441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 264231133 1250 264229883 264229897
    0x90d0f0c020d081b070e06011b200a0b070b040b1807091b110c120c0a09060305011d03032a040608090f070605180f3c0114 54
    0x1829410041150300000e04403030b1841000c81c0d0304100042d01e6100d010320301d400404c10704a0f29000c2d0038a40d140c40b0324424010b0005207814104050480010345599031b00c1c1e491401c907a0401c461040c030000ca0000754404c2d00c03a00706e40700c0c402e04081e440003a8000c082000c445031158080341100060303d80d965100c84141015040702c4001d0780d20710340b050022604010007001856174010200d41d1000701c020300180251214400030400c03c0024400340320f040d00003140c81142c4c3c0252030500c100c007442c164040c2071094004459071310088403040011440e0300780d084803044d01d002e07400810a00b42d440e1401ca0009003950301809041d00148001124141c1030b640501003018415464400b00d12195a11a55a8042d82003a800b09400a05000c0c42c80c0c010008203c03400300180c01081407508100c4060001d014a0149a07074841c0054210358064541c030840204241020b0801a0000785031048201c000d50802c00c0004404103810020408940e840b10389802000c3c180c680750305030100c406c4c00b05441c2d40400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 264232383 1250 264231133 264231137
    0x80706020d14160216050918030c030a030e010203061503040c05031207200312090409050d0305060907030b090a02070602070f0303240b30040305040f080303090d0f 72
    0x4000c18004151034041d080c0c4038025441c409006280c0000410301109824143c4400c5601c0303083e03203540076042600014240e034001c549142c40b03a42c2c0c80c1e005d83d000081e903101d4035036980000b184420b0300d0b50b00000a044080d40d1528240080fa8244817036a080f80411242fa6904c910f01c402c1c4d01210881c0348008640050040c004400e2507901e0703101191902021001d2141040c00005d41001400700c0c040c0c1e4000c0e11382031621060750b6009210f0000e660f1344550041c0400e0940000b030032508558840c1e020804080e440019614030b00780304c0707501400400c0b00f00c1d010b500844501c40000c030401d00c80c0c4103c0c907030900018054010364841d94112002500003420403a6a10b03420041c601c0407500751142d03101400c2c413960300440d131042210204d03149002041d00b982007000145e4024401e0002040c243d4518455000340c03030f8440040c1c02d1441d010040c0001c1f612450340e0000c011b0005241d80700c0024415112036846034505507a40b61115652803008803031520a1307410a80608104a01c81c0f050100741c59924 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 264233633 1250 264232383 264232387
    0x3010510020a050106031110050306010f050c0a1a0f012412140f070914010203031308092d0d02010f03051f060c021201061a0903030706110d0b030607020a08070602 72
    0x141e076441c4c00c4542941050352803248107451107000745400c4140007407034041450b00600711706042c0c00291460200c0340000e41031050202e0b83c00b0300c2032020032603641d1043c0c001100d0700100740036910850741202d0590341105601a0500003080820003150380c1806405118000581103000f03420442c0c0b485425003844c0102511048088401b6155031030311405240f4500c500c184c0e40c1058500030301120712945c00078068101080c0440301aa0700841030700d038070202e50308510b61060800c0c03500150754424200d84690040031074618680101009000c80108101c440200000c440c0c10010015551b000c1e1000900003400100016641442600a0303500070b81c002407040c00000c01d01084500d40d00264000d1000240700e11080740940ca00481107402d0f008450008001090902e110100c9050342c240120281000c0003c105131680c4041040b07030107584e0404805c1100c01c040d0044221150702a103180b141b25420301001640318540852080d002d440e194004000c41ca0183da24080d554100c5413081d918180d00f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 264234883 1250 264233633 264233653
    0x40602090a0801020a030501140d020d061407091d3102040e010b01020c090f0408031e04030305010503060a0608070611011401080601051509090601050d1d0304080f0c03030301051002 80
    0x80c1d94181e201030005007001603215805084001c084500507804503541d810121601e80c495160308640c9250a40c041d6001003503001a810071102801010600c040b901e0450410860340309d902500007803e8a04c030340b09100c4491910b450b1168207031350580b0300420002c1d401c100c1c000c00108880002c88031b1104c60490b4803001c11181c0000e4201ca14208160f021030351501440c041e25070b4180b240c80c03030745001210860560b0810395941d04120b24020f00080807001300001103400c3c0e07600814610240380d1a508045540c0c500303450010301510302071003002d000344074207070121748038191900802c0199010407000f0460360b4038103c801c951840441c0c1d0b00c1c846655959030880001c030043c02c0c000d4040d140e238100800455240000340407000c50740b500420381000f824404410340c1c0d61080c0c803860b04103030309280240d151141c03070a841d0b00501084200000039110b058401c510b408001c0080c0040303c40c8402625020034000403c030b038031044690340030381d03051700300308010700051030021031002040107588100c48400013 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 264236133 1250 264234883 264234889
    0xd0c03031d0d0f02030f070201030c090f0f0e0a091104380f01020313050f040e030c0c09060102070f03080c011b030e1902010c060e010213090b0909010c0903030804060209 75
    0x6105000700800760001d010450307030715400036410105010144015440c00e04141c011010300c0c003503140000c0c10036480d030700000c404030700c01c1400c0d4000d1300781140d2403802070b50f8030700c40d0031032000d0148241030f0302c03004010004024504501c64540d0154201600621200c2c107001084014516410321500f090706194803a001d1040c21801d0700b603036400002408651a0151041004100e071801c2c0040c1158000c0280607021245003181e4400c48106840301c100c40c2c0a6440002c014080e00703a86c240e8544000b00780c015145400140715490013100307480c00000b03516180300490b101c294a00510310009a0741c041000007540c507000030440220702000000d000385c6490209502c40d01006401c4000039103480d800b80f903a200c10300c420800c8140c4046c0e107405102041e030010b0032481c801907025024560707580103200e20040c00c0d01155407540d540039840c4865521012003000401c0290f0500e8000c6840e40c0018001490510504841c1360305900c0306801585103940071611000d00800849040d038003413000e00d00c151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 264237383 1250 264236133 264236171
    0x2303100e010204030b010e04031409010903080c0a02040501090e070e04080706020a020715050304121101090206030c0703030f060501140307050909010b0307110c01050a03020d0e0303010e0105120f0d0c0303 90
    0x440c00003603511840d5003030443d42442e040e0426500c2a40310014000041d8102e1001016400710764403c6868145503001070703494034000d5002612698002507030f00740303605010807040e0215100b200c003001103036220b450000071105a40003100158dc05480b06001c2020052400c507401485030314910b00c0c0aa0b00c0c1d980e5401d0b83c01030007a0001681c4030a2060128141101403e4540400c901e081381c114034054480c0700200000d544107070244119400400c0c4e11010a400207488542c025000f40d0341e9003400c0c0c001418547c005402500001d19084a81c000c16000d806100c084581c140e4501c050074507402c010404a900142c03096047c45010000c910940d02c590031858002e000c1140c01030740364a0a0350016008048949001d400b81d0026205244607a8000b0141e41a01e09580790041e242e01e504a1500003c040b40d101c1c3c084284408800000c540101d80140360580c2d10950b12410040c1c0500000c17581d802c2c1c19002c1ca016608458130b8051030912401040380d03034038000d250102d10144039845c0c01c81c2003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 264238633 1250 264237383 264237401
    0x30801080624190f0e0108060721050705130303050309281e050703050304030605150a060807052503021917091804050d111609020706060f090b030d09230310 69
    0x38199000040200b071070284001d59000c401c42c102174051014012b0350710310140d160070f40455078542d200c000c41c0fa26842502910b5000c00354140e000e5415031241000780c955042242e070768600c0d1244540313452860200e800d0503003120702443c1030702c0711561540c0d403000f521202d8640e440d010070b085c92103407102086003001110019802240595515811130a20b4410b60b040180070481c06142c90a203000a510b61448503800c60380145441144e5890300103040320b85110380c0a180480400191840c000b1300c1807410109a405d02c86d070200c0d803540002c0304884d8882282190080d142d000b40d2034410000c41000f900510b1032100c01000e20b014815a0711042010f2002aa01540c8941c080303613203c800c590f0800711030540244107100424050b101d560301c05012081e58042c030a41c80742c010560b44d040016a800c4480985121600c2000341c940b0780241d40018840d4407000e91003841520442d120090041014a0070389049028060700c1149070080e22404058122a850f01803142508540c0c84d00e1080c8036560310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 264239883 1250 264238633 264238649
    0x31c0905120c10020708030f06040b0d1b0e07090b0a0507020a08031809010f12050a020d15110301140f030a050709021216050a120b030a030801080624190f 68
    0x202d9908a07002e51401c0101c011074026a0b104124150104e04a8000e4070b9205858544441540e5180e00129010b0450908450380110702c40710740c402000b160401805c0301030394540074050519505c6585812244098468070302241c902c0314144480d880402c000c140a010701d0404514000e031aa01044146105511800441d007012507040c1000030741480c0c003401c4440032201030404e54100040d070f88148240344210740b007550b505d03454001002804d0140d00c9209030018007842c051115400c203c400c085100392001000d902d003450344040300d20014141c9068501c100e09064041041d0002e002d421400c2043c1c00e0b82c180f10700c00c100ca00080d010072810001d40404100035844040c61601c00000c0070014010b00030340401c24180d201050707400407c0d900600e0062400b80501030719840c10b03000800e1503005d1a50140502070080003450b1300410b0381812a6040012205250f550201c0c80d8452000b9840701c0e0040c0d9101d1a0b082c895240803c5180d0101c00141041c0304c0442c0e403150314281e01d02e16580b008031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 264241133 1250 264239883 264239887
    0x13060614070c030f2603060306160504090209130e07061b03020a03050304020105070b180c0904080d0518070803030609010e07020703151404050f0106080610090510090903081f03020102031c090512 86
    0x447d400d0038001140c002400d1900302040c14010040078040340264041d24a20945c08500d041e50b99a86025000181c062054100090140740c42125201c042c28090400443c80e240701c034070060007002c030351000c445816038007400100801d96421a815480507005034104032082c45010003040b501110340380500402124042044402c0c800c3c103062851449842d03105180c82010070010480b003004942d40007640c800700242940da05071142e066400c820650b40440e01c01d0f19000304090f140000210301920341211100c0c0c440c0e03a1000010303081c03481101e541005801409040000800c415100c03155080b25000108001d00c60f0400c001c100c040c00c59082e9903c0d8810b01500840a40a10444000d00701e0107015200c00d14003803601400c505482e00c100640d50343c0d1600082c5401d800c0b4044035014060141e000d010b0300c105814000c20003c002c1d140c10340e1529469071665035000c445001902160760603000345042c400e55644007118580c0c800450080c19403201440e100091003400140d09446003e00195 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 264242383 1250 264241133 264241141
    0x31003030806060c0303130c03080d060e0c0f07030e0a051206180c0d03051c0908070c08030301060e0108090c0d030908210702040b03070513060614070c030f2603 71
    0xa2074a01d002d40214020360081060300d03a5090040101da03401600d600742c503c060202441d00100c1107085078009000ca003004280e0a80c4404141c03c03041c02c445d8071540040d55500c407020282014403d555804a62417030801c00000041c0c003a14418040110041c0008480ba58030408581040450750410f0380b66007201080012010600900d10b030350041000c0141244160640462680c03001000c000c3d00b400030200d054203102403d0020115550819007086c420303020301c1e00c0c0c01d0300c064109980031104401546004070300c20400000380c0e0304170740b595a80c024448080c280107481d400b00c0039152082602801802c054652905d8001c21034091103540d841c9903482c94505100d007410f50030714003285400c3c082502e411210101005940c410f64044800040c210728070790000307250154582c4015048500310380e52010058103503012200b00c40d4192206c401080074141522554030a19034003d0884007221000e10200b804404c410ba41c80d07100b4103c55545400c03e60045a2a083c641045040701000000304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 264243633 1250 264242383 264242387
    0xa090204140f010b0c030705070b0a020c0108090d050705010906060305030a0f03090c051203130f060e010804080417070308120a0c020f0d0f031d010609150b030a0203061503100303 79
    0x29407414200d07400210440c10100c02e940219001882421940c400100748881442002c0c0100c42d0102d9004044900840d0350701e0012140c0c0d088000c41d00050b005249008007154042c0d14401d114503000c00c098641c00090b200d056859400051003610135658a03940000012000e03c01c0e000a1805000250f85a400a00c4010503e09844481e03034101410140d103c800944030b62045020b40d2001c4800c400440702054003545140100b4100e02c13031060881100285141c018203404042c0c9040e6501c50018401e01401514081800e8a005001100400040002c8015004900403080340301f000d0b611129640c2d10390204a41000385041000402e010034010314054910820a03182c0c1e06001038440c040350b02400a03140c240804541f401c0c0150f40c2403d101c0d15110b0f038012104020102c045014800e0f002030384900070802402501d5040d45001d0300c50f4072901c28030115904030307078440c0743c014a1552542580b501940002d4002900700400d0203030856141400005181310386118a8110001880e500700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 264244883 1250 264243633 264243641
    0x160902030f0603030c0703020409020f040c080f16230f0403140723010e0312040f030605060609061905160602030603060117030909090705220501140108060f0f090a090204 75
    0x94180301364020400d104841c007000c81d00d201200e8044500240806050000c104605c0c19031105560080c034000d00904a5504800741c24090024510041040d588850910002565150b031900c0030076168040c1a00950040390080b08440a8086a5007004048111803c05411541040b141c0c0e00380080366503122002000140c0007808144512100340c05c400401c2040120341c102c3d55810480420407ca1154800b0048034220640d41210310360760b640d845204140480c424001180c1c1c650514000c0b85903440c1c6002035408130803005100a1900c2e40807810488080300d001c1c3c2e90003c0c44810300920b59003540304204800c1c5140207000259036460501c04150512074160170010404410000706440d10300b000060f07403450314007644d102e6500c1d1585260649000031a90165500001041d4864503021640c104d0001981140b1014015a600c5080b000481c54520300001d00050351a40042e2480c584100c012a50410141110184041300c80c081010b00e001121402c012545a9211318218103183c41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 264246133 1250 264244883 264244891
    0x314100203010f080f1f02090f031b011b050613050708060403030608061605090d0203101503030f090e0708070c050f0c03070504060b0417030d0608060709090e0705040e160902030f 79
    0x83c1c65000c1080c4006d8a0a881c031a6048807000d41c0481ca0011540305e41e000d10030b9804004040390400d045030296040e00c41d9070410950300089040c0f001c1d02c120003040c103081a441354400b000e0241e55031011500801d034880078500f984d1600c00d000d00010884810b100302d07805640281e83c0858900d04103207440b850110041c01c020300080b201074800d915250b101d4266406c0480c00c883d0190340400500010b490b00f41003690300c5001c41c1c608020721205640906608040f03078800e403a070658108802c0303010b0751034001a1084921403107005000414161140114650211040c01d0940d4a12407949440785000c1e503041c0702000b5075001080741005490200f000354001d140c1100c003442102d052081c14650382c0914841c02401c0c00005490900401c018820b507220a84506410000c43c2ea80d1450f45603924000c0e035104002c0303408201c001c608001c81d0b0003440288140c540085c0021464100bd00005204000c05030a0318020344449000e0096841d144000a0a00190158490400d0100b0100240c00a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 264247383 1250 264246133 264246163
    0x1a090a0e0c1e0a0806042003010b0c010615050d1d0f1501050402093f0a030306050603040f02010c02060405121c09180b0d060c020d020f03130314100203010f08 70
    0x1c80043c200a40c001131556100106560204681c50b00c500f020030030a40305101c50300446004000404c0648250700035004201c103440090002565400070a520b1000c114008400200100001554644140c00c0440c0747c28855800c05070361100181c1050030322040540d81e440c9a0841e84448039a5614048004e01408040f41c0031480c1c0401d20700002c3c00f505940c05603002c214220306620325107000d04040c808403805404008840c1c030503059001c507103403000b101c03045011924242002c1941d0400c407064a2040382d004000b09003010361500195450511041d04070b9006c4400c1002051a0715401844141002441e004101188605007403c1e00008502040d104128100004000862685c0c040d1010071030f507444c0020b1490032590104aa011030346801805441c00c0916100342c1c0c5070f0000d14600312040650a0b07486554100c01120b443e8803131074200801d505081002840032400065003c0c580480d680c04580c3c40d031a03038800010076038009910641d01d1010a03042000985001d1100c001e03150085 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 264248633 1250 264247383 264247387
    0xa0e06010e2b1a07020304030512030402010905042c010c0908030a09030305031009020708031f03080f0d0e0601030b0610110304152607030f061a090a0e0c1e 69
    0x510031400c04841088210007040e2840902e80144940000a0101140b400300406070078988104041e40d84c0d48548022103480c810400c0000c1440c001d103056034000c96050b956110064a0407080101500000f061208140d08905c951121099084a8a6032000c4850000701e002200318070050301e03800c81540701101540040003900e040f294050030f40c0c070950b40c0c142001500c80c0c541c2c8001361141d400507000000480c0c4001111000d10080e200590b2045460f046100800000040c500090701c00b90720008200d603406000d801804150710f40503200c8000c600d0700c0019405591080980b4022084e071080e20824241c0003070221909001b0b104182100090a0001c078600b04035503081c4c0c0d00d103e42e204001ba00250707480c1d045480c9200d9940c03001c0410905561400040800c041c44c0c141d16401d0f1000c001180c40c00b4048681541d860107010202c560030023200ca4005071514000b00542d204030991648620502030120700c5000c3d5011207400340400d13007141d6450301000c01e4020003803201803888a03145802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 264249883 1250 264248633 264248659
    0x1201060f090501121b031d0c030a0b090a05030f121f06030b0622030201110624120109201210020307140a05090301050c2a10020a11010f06051008060f0a0e06010e 71
    0x800c0ac02d16035101000038a19915403620f207040a00c1440c4c0100103000000c0c02042c80c0b0b03407803009000c1c172103912080f00407107448001004801101366000d40d40304c4507502100700103850182e072005d10301e0200544001d1818402d1040300c40d203201540c4482e400500f400000744155644207042018201c581c00081c406400e04010504d003080e0304068411004108030080d410946441c0805024842c584c0c0090016803103a03e13040f00301c1030b4088000080c042c1c541c9160103191034030904040b040384541c00601070040b00344a140c00a540010884002e00440100414407040100020280d201081d52003036182c192240800d800d540340a0001c0d0072030304052240f484064441c0003500c107250104480542e03403040200207281094004d542007000644042a1100d42581007032525000d981540001c015a12641204104a070000d01490742c001c058814841c9902e40600d001c00d400140042042196012a100080e03140e0b0044e0402c0c01c4084035071050000c656000806011601012906000c562513 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 264251133 1250 264249883 264249889
    0x40510110c3901120e0303060405160909051005030d110d140409090312020301060f02060f0f0601050304061e0902130603031b03090314031201060f090501121b031d0c 73
    0x1060b0050300c480c055000780410740c80e0307008800150b980007008105010030249418501d132030b1341007260914099418000042d00381c4c07000c1d00040400d40b00c562036075000b060418031140010130000700351241c0002214400b0803542d0317003009407150340200c0d0ba58180001078408850360170006a008007131b040c41100d00c0c0421010310110192420358a4000000445403d0360a00b00e500141d40d407101c030504d500c00000410384a9000c20180d20200c80d540848040b611404d05a401007502118161148020315000c075081c0d602c0f981c021900303d03000b40004941e40c2d405040d40442000b1011003d00303100e980d9188001142820b03441d56a08030100c5104201daa85591800b800c0e21410008420f4000140484407081602644980010b950041400c610041c205446155680d101944d0703c4110300c125400050018428400494000350039555490060718080055800ca000c0304440c0d070a80340c42d00192849003921070781c403411190b03455a0100e4450f00e648040300060303030803102d14213098200a1050455407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 264252383 1250 264251133 264251203
    0x1515030f020301020d140901184d120a05151012050c01020c060721030212160f090f030206070c05060c01090c05011e08040510110c 58
    0x94010034112000020340c40000d00a21035020389a0895282c0b13202d154440c25440c00c090b00c5421039500030048442888d0010b250403d03480307070003400480303402034101c120821156a6000c104c0f04031a12111020401c01c50801101d05050a80b940d010508140303000b480c040100c49014594000500b071540c800e601c6940d01e130008280900e00034100780f000320700020741224541c40209404071401c08414150703d8401d031101e40f01c142d120300500c80d04003406903514041c400c560302140d00100400c15412100c89142c0008145030007802495428003065003041010300089114880703214007640e0000c10158050300160624150200b00000c500003440421012981300e402c4d01d03012a00503840e00700900d13143c1000c04850b089540c00c840d002c40c3d282842c400540040a055200381059817815031550011220b80c0303418500c2c2c038034031001042350300c8516004590094005000b00140e40b0f06d03941c0a000032013a10707915070380030800f540002124002801700b880303658000b0258240b14840301250543e502106 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 264253633 1250 264252383 264252389
    0x2010212070504260708010c03020403110a05030a110103090f030e0a0e010609061b080a091701150b030901200901030f200a120501060309140705131a1201091515 71
    0x3448079102c92600c0618200305d508004c00341c1c82d001b48240c04131818018041d4001e13100803106401c1d500000009031400c07140003016541c010300103140c00e203820f895003010812400001e505142d602d074044070114160008d5030005070b0094588240c03041510090144121f0558000b400e07500303090005000359540003846004880f6507181513840144190100b0760925030626005100308000920302408a4011030050708441c1c03004089881c40030a2080c0078242c03400401201c07030a4040000034840300c0d01c0c01000e03507007080300746000003000d503000d00304071010341ca090340480c0321002c02040b2071351207603814003400808a64080041c8035038011034116088181c40054030a100c0c0402250446000e446491100308540d48444144515652002c2c0540106200b00003a14414038a0951081a1031700013410400c481c400340c603080c0c141000680c1b4100a001c0b80c1810303294a80c820a8002031b40d524110a0240340890100004a25000d490480a032562400356600f0050806c01c0094501c001c0203603240c12 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 264254883 1250 264253633 264253679
    0x3090b06120c060a03050f1003020d020d1a0108010f0e0106080a0f0f0b0a020a0e09040b06011409040203010b0d06080616030f020904020d0902040e16090b040b1002010212070504 78
    0x540c1103450249424080488002c5400980c0030410458565240d04032038014104141d071107806844804500503c2e25660002030b410815040d248001810a03103082d4240c1d40c011038014000d02100036002c06071001c02c1e400410940c0d1200000083e5034842d00c6a000c402c503016008002c43d51a110107a519111400000b0340b40c1c00541c0510310a1000f245c844140e40c660041d01460545410070b200350080d04008501d40000e08080b00c0c40440c0e05001181718000c51b0007552010715541d682004481f58000d07107900c008103410900000540b078403a0f001a501030141980f00703d40714a1414152011161aa444194590700c03500c2440303400c0c05207005d1802c140b911441d0100305405c0e00e400100c00703481419643c9030040d01c00100c20344190a0360344001e060b60b20848040c014030b000d10314407079524002d400d48949031a05e441410440350003294411448a08081c20220f100b40c02d0390001183c0446c0d4401c4040540d40009080006c0283d1018081d40040740e424414113290520b101c0c024030060b40790300341403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 264256133 1250 264254883 264254899
    0xd17060d080c0a0308010e0f0403170405010617010504110409080307050a0e0a080f100b010f030b1504230d0b0408030a110a0c0b0a06150c1a0f041203090b06 69
    0x20a0081000448090301030b01d10848696000c54500100700e42400d100e10b840c00351700c03007000c103040202081445015a4040c0e40d18504442c18403400c210b4000080e204903a10765807060700080e01402052550b600d6202c5100000b840c0c41d06007000240d880c0c0712100144668604500640090740f01825290007540c1e031706d815a11122001c80c01d888090403100c4c030907440344804a000a90000001e420610040d003103080d00c810030322410081054455070030045004c01c4000c888580c0c1d0600c01da00c540323070701c2000038141a1b1003500364103034089a600035009003105034551a409200c9401c810400580c0c4402600c0729442e903103c0f920f443c81401d0b009440200400000400715444883c60340000000d020b5012240b0b944191511024145000d000004c0701c0c6c0848040000e0b0740c001f803e105d02c200700e81c17001c0625018120000c0301100c444103036402c00c03500340e400d0510959142c11200200e500c01c1014a41b90000b604144c03d03d03094560b41a00b0680c101402c211200c00021102e100f000e0300000180c0d4045 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 264257383 1250 264256133 264256159
    0x3030c0d0608010f091101111e070b03070e1207050a0b090303070c060509040c110715090e13030305090c13020901090302060d02030a0b0a03080a0f050903030c010504050d1706 77
    0x5000d4001640409210b6003000081300280195038800703007000d882208040c004009950041d40c040d01480b0380110950420b8152074081c4d0300035008512088880802c3d1a10703140c9031502001039030000d8451074005015805001c6013800c003061004807042214000301101b910b0480050800c00c4980582c2c0840040400d80001c1601c04005540c03000b61f001c00001760180c0c507060b008106400c4404010710440c144161011001e0288400f900350100800c0070f0518942070103114403070b444200c8510300410000c2c40e000240c0107401200240154220501e00d40800343c3d0307003401001d0360405070000300d958014180182d90360765040b5880e0302ca82030f2600050384881100005075160b200c10b610182d08444000761405c10007185500031803040124650800080c05001c090100c208002d01004200e008100b110140b454090810700014158515140d032034451004042800c540011803c2c9407980c0d141c1c000c0c0420044141b0100c00d20080794a031408907170300b40d42c81e2448080400340c01180290034102c510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 264258633 1250 264257383 264257407
    0x607020d2d031b0e09061c060c050712020706020d0518011805031509100603031205150604150311180105070c0b070b0a0605030309130507021006150311040803030c 72
    0x50b0550a494626628003096040152000132103244081c030540702d00740003c02034540140940c4040d084d140c0141c050300d102303a82c0d4030b00419001904d1000d1000030b0000307000080d80500708a6040c9081d5014048213031900e60041d00c0e0547c40040c801c00e018040c0b0841e4040340c0c2107440d0b0070007207400b40f030480d90000668064005c041c50301c1e00860341502600d030740e509400c20b90000ca90300a12500c82222809090100304108442c814000240002c0740e896290340e04500303e40080f90081107207040166001e0013480003605645c025070040c00c0a054140103214100e40500c84c01c40e80d98104a00d040c50316040b01004141503880e150600d0511001190000c1404a0076100b03202610306034410310764803030050600d08080305040751803440300307818804085154140803098900c1d806e0041e0404200e0003001e4682d40c05420001e21603421440b40720001e01c4a01403d000f020020548181035207078103566108014107590140c0b1181c52004010807007080640c400004895204451f01842d54545400b0882 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 264259883 1250 264258633 264258641
    0x2031914040f1112030c03040311030307030e010c060e06130201021c0e01030903210e0d02011503110d05161d01030206030109051b07060b040b040b031e0114090607020d2d03 76
    0x1308100030301c40440c03403d040190000c010419640911600d000340c81c1c00008141d924403800030010000b8038016209102540641c0707522000724456080810300800016030586420000c44030403152290030b140c3c0d00b040d940c040c4260701092420202c40c8100c60001d41000d0321008910465034105a9a00c201c04141880f6000d04041e0750345041d01c0b19611041005081c02400c00c0003d50304807030081518038080c0c0c80c014801c074400f0542450030200e000c0e1840d21003048640880700d54a400c01001200000005c5062007010303030906444406003ca80d0415039551b40003082072031021541d061007001400541d5403c01900e04550806002160540d84c140c06980340601d09005486000d4021800b001041880c0d0441540720b4030036074003005802c02d40b508200075102c0804680703406030003041030751822842e002d0000e505201240e0000c51003001c3c1048a40c103500d01200c081440750400c2c41449540340c3e041c452907031035026602d80401c4242e18204200c00d960780002d080349016280c102c1049915029400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 264261133 1250 264259883 264259909
    0x20c150603030d050c031b12150a08010c03050906010b07110d02010e030607051e07020d030311040b0d02040302130c1d0a0e090c09070f09090902040f02031914040f11 73
    0xd000c141444400f118864100351f85261a8100289000b04080410016129a4241c0c3d20300780c1c0035a1200504505219948020360341c000c8003040700071880000034015400c14018a0f98002070b545024403541d400c14106800400045030100900800700e00308601c0740e480f0b03e50482d4048400512071006a400c2c0d101001800d416025010403c007029401a02514030300502c007000d103403400c40c03030400c0c3c00c02c52142d901c001303501500440345000070900ca64404850407000080c0c0518103503c403014202240c000c8440c80c14402d0300014180114207040701e504c4d080303080208091099403481180a4610040c000d844025100d020750302c2042981c1e110103840c001c02c00c0780440d11080c10a14411038959001d0b1707642602510760320004c109613901c00d0b0245128042241e5a2021840c1401d2003640501405c0700142d034403e8071200701690b105100e00c000d5000300c041545000e0301040b0b1400400a45404520011640b04c0c0039080002003490080c1d071132040359110ba00b91b042203141c040041c0500017158 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 264262383 1250 264261133 264261157
    0x3060303070c0314151b0a23090a09110906030c040b07061d0d0801060f0207090609090309061d100c050601060306050102120301080706200307150b04020c15060303 72
    0xd0720000030704c041d07600c1c901d1100d8090f6045e1954122901245c00139610f05480c03140c4003200e8091070030b01c95480795025281b111514903101e41540c01820b039101c00181400030b5410601800a40442949804145003000b480d030590240500c802047e0481c03035a00500091a004100010010f100c160303c0c613044a0260942200041d112000b500307008000740142d4a110504201c00c8035110283c11000560b804201443c2d6a80c0082da800e283d41107855a41c0c00d0300e040c0c20f40c0700d8800c0214011581b8040d042c042c0c041c004001881c0b03115410010f02c04192603001c0d506101400c00c1248403800400b035080000030099038901c82081c10b03141c003111300c0c00b03104402800a004950000c1a850340c181c204000703d4001342c0c203c0d2540e2103101100b4400d84400e1255074007551269008205845c00390410202c4e2900a8a44050030158400c01c0c5055511020003241d80303045d005548502c0703510324460b50088031002d6a04608011450303101683c0c5148969526803e046035000181d407542d01003003190085a00d41d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 264263633 1250 264262383 264262403
    0x80c060a15060c12050c0115150206130c03031407020603090d03061d010e040201022103100611032a0a05060a0b0f0a0b03040510020f09120706020c060306030307 71
    0x1200c014000c146030003a41c0022010080d00003415440740010082450f00314032841c003c038640010583c1c0035805110340c60090354840d0115030a281410600c84000d0601408032080c06031600c0000b424050b001701405010701402c89003a021036a01c03490a03058a41c542400040c0c9048186412824051007200941c044000401c009108001041503520302801c1c3c4c03030a0012648402000c1040350421410600d40c00c0c101c001009008980f030005070700940180103076001c01d061850395400ca40b9412100d202090400400c0c810712170343e042104002001c491a041e5010250318807469128890b0400d03000c400d11107a90903211404401488900c50f2410104075500100940784c8151149030464058080520b802141ca0081c2405901d039480010b00400804c000303030030030003151384940020308259040e00c03600100401c1d81015100410100281d080d0307503a20748c81042d0400044130313001c45140d49203412410f401c016082d00040e03e04000c21040300c6460320b0380d88072004a80f550240c0800074080b0328003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 264264883 1250 264263633 264263641
    0x3161803120905010201051b07080d020f041a0a051b0c0604061701170607110c0d0609111504060f0c020402031302090c0405090f070516050d0917070909080c06 70
    0x305505201c0c60300196202d480349660b80d00016403ca0b0b4084500c8803490401d400340d0345c50802030701d0060507107910840b5150304110600148200320380142d00c0c440e000c0c020015040c4041180c040030401e00c010100384035442c04862400040c120300803803500e0300c280007000c1100c0c80c12034000d00103955003003030107002145c41e01d5480b00c1c000e06421801044440c2c0c2d60f0030b031001046010403141c0d0165009100030060600d620b81c140308075064031143c0c0c1e51070b44034020300b05455115510380700311410084c0100317000b103a14045810f00b81441510504140c1c81080c1400480702003410144c2030310102d41c41820404902d010300f59003514035056410000394007a04c0007080094151001602030b080c54000da510208a64422202516600c120b000307055203d40d440c1c0c0000c2c82c0c2100c006420358880240d181060800408810454a5240d020b00031101ea40100340645001a444003100d0010300740345a000441100d21481c06e40c40d40c9080c045c0ca22040d849000d5401480300d803800700c501c17104c058400c441071458 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 264266133 1250 264264883 264264893
    0xd06050109110c0705010f050d062304050402130b0a08030c010e0105180712030516031e05040608040206030901090503180a06080c030a050423030d0f0e0303161803 72
    0x5800d01940751440d290000c40e00440082d42d0a5511940d5000000d1540c03604140040d44c0105000404a0400c84101b00d1107152500318000c07640142113003090b442e55040310300c40c3c0c5000f103007810809074001c44ca45401c01015a8580c40f0300c1542d002c0b1040005000f0b0034880104040e045070342c2240d42107102c0004c6001052805620880d035111b1000020000d545450222415006000a80013010313070120380709010080e0018a0881007500c0307803c00618006a8410b80c480d2081c0404090380410a094590300440c1ca152800403c04d0640307160051a00c0d0501002030484103002d0f2001e03014940100024010100035403000d48240d0308241141d886d40e4940b00912240000f03985401d015000b041c80025a4501615030796000d41d5001200c60308550302c0c3c0450400030b010051040e1501c415180754055041c80079081c2214030383d150006507035680c07400344000b030035035030303c001590030a5151031103c105440380481640d4101c031341d11900304900c106001c0304480d405507038090040d200c003003d60000f04100c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 264267383 1250 264266133 264266141
    0x301021909150807051804020403060c170c040b0414060c0105012405030f0c070302010b120c0406050303040b0304030810030611031603060e060d02010c0b2d070507020f040b0d06 78
    0xb610342020040c00070800901103c10400c01c0ea466408140284204d1030225031307a2062412203480540018100317562519204103580040c0e0b03285010034020360b1501c400c20000715940c3da03c906500d015500d000c1c50a080b8a042c2d00ca0352060a41110403400e03450416503610044900b030321907000092200e9610f5003001c188005803d0359020310b9049001c840035000c1d020700281c910401d11800c1101d840d5640110401c0c240c3d1200302c080302195682d28190081d40d443d0108048030751090002008425410000d0004640b00c40d00882d101e6070042c0402c010701c140c0300c03044076030050385850218000d4079034010700380c1000d5031034000511803030402e04480c141d200c640020b03501c50014144614074601d08120103504991450142415507000180060f00500f44051343c41c400720f1061400090020107500c42b0b01345110240c0301580c82e0641103982c41c003a4103031446000045800407108603070b18100440701826a11500308024041d4201c404120000d94565100440d42c000182055103280401d15010000b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 264268633 1250 264267383 264267389
    0x120f060504050f07120b01051911010c021f0b0d08070305040b0705060f060103090f02061b07090c0908070f0612090209040f0b0108010e101508070305030a08160c0f020301021909 78
    0x300604242c030802c40586c09409403502068652078a410440380d00008900b400400103800d214201c80b02c1440c068007440342102e543d4959003d0424201c211040300200b440600d0035a83d80c0f0b0600034244000d079200743c4038009032507004110780d550310541e15080d6071a0003241e229288600c00812010140800859054030802018011308419a02c003001502242d24a0601904c0f601c0e020394488010304000300140800c5050700380144509031103c00041c640781c00ea4015101c26611080881101500451410050250000134186d21800c0c07100580700140c60340b0445040160614160316280c1c21644020419900501203045500c5c107428208164001c01400300d034280030913800020110010721078003504401c1440078140200441182c41d0241000805080d4403141500002840038010407900c0000e51040d400b55031100359450002d080040d0040c801c40100c1c45000c05583c50551010080e0030003580729103042004078003400440e009006c2c14220b50362041e84070020b48207036071700000c0000403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 264269883 1250 264268633 264268637
    0x18031101030c081302130b21070b0a080c031009182a0b090307080609070e0f100b0703020a06020310080708010603170d090c26010507120f060504050f07 67
    0x3142c294900122000e900441c0c1400e010030f21080f15100603d40140203c8100848100200e0001c0025002820001c0007440c0d00e40f00c0d0700100216402118103108580051080d0403801e803c11007201c0028041401c0240403007400c04001002071410401c21a991024102411080241b004982070034680a4040c1c3c0042d10900c441d60380140b01003000c440c001e41c1c02c560f0100010b10b080c2ca4812804025000002d03200e03854080c942d804503118100300843c0e8882d8a40c0d40003041c400c0e1500c4c1240290400242c00440078000003010801240c43c045550740840d1100e8034901e07030301d0301e060078120b0424259100082c90a4000014850b50100e01ca41b604103407560320081d942c0c0c066903440c0040c2210203c5c0300042185100e044e0080034008801c024281080803044042030040d115a90203001d03070340340e8000016004448481c003060302000340d1705050b41c0c5594002000716050010024144034041c9481ca800c8680b556821000603000c0e0700002e0007440c01401c10302560800d503880344052070302184d10f100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 264271133 1250 264269883 264269891
    0x30705010f0c031a1e040209100f08070203030402010c020120161404090c140a0e07050d060608191e1107050f0303130213060b1204060b01050f040b09011803110103 72
    0x421100040f80f07501040780051007003031039208020005c1144100780d07402960040c0d003440481c140351140d0202810b40400c680e05c04000c1560088081c0004801404c100215032003407041000607600b00c8581d0100d1078090800240f6801c0e40c170001c0c40e2000d6040c05100d214011400d0b250854241d0300240c50030340f00c1c0c0b40c0c8052907030300307400040c04121410754401070a03046169400300029a400d01d6065051035018003841000c83d16042d2050356101c040c1e64810015900080781604822144902000f80000e0314103040c0b03a040050124030b050110842c00c1610380c0d500d0410f04280c040c1c01c491143c03050b858200031312000740d40440c0601c064101c0ca400b642c050203041c481c800c8599020044a1103440f61070351806805a440c1c0034040041038250302009929a64580450481a030b2005881c40081c507840400c814a081d00d010425280c6040c0c1060502005010300c00c4641c6004090f1000c1d14241102d56031168043e60048490108891031001144000400031060203401840c181c000301083c0c03000c1c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 264272383 1250 264271133 264271151
    0x60306090102131509080604030504030c0e060f041a1009050907020102040b0307030b01020c0604120606050a0b0a1d3303040c060804030207230906030a020604030311030705010f0c03 80
    0x307030030b0b8030424041c042c2081c08201c0500203041042c0c0d080400001c03e1404403411034840f06010f10b002c2e400c0e1410307000b00310045001c00400091441450240c142004000550305003100803480c140c004020040c415504e544984600e5503080303841550481000702401001c510920004d080003c1500841e0300400c881d10004075210300500803202210b14600c1d09034615900e929086008146501d0071504600641889480c01c0e0345a101500227001210248a8041268640038089507104c1c1e200074000e07071580c7c6040001c0e14070784050310204406802c0c100c0c07091003242403e42292030300300c00044e8894855101c0701000800d5809841c0300004200c070031880c121440444804500007290010441c1030945424441c1741d1082c081160050f1180c0101d40005803121242403a80610a11540d07180002440608a514200c01e8407900104281c010b081004c0141e004a102c912941c00003030306118024441c050a4803040080314191a0048003c0182d500c1d0020000082c0111248010019090501c41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 264273633 1250 264272383 264272401
    0x60f06140a02060103030c0c1a0406020124120203070504050403020d0801090608030318030d0603030e0a0603051506030601050412030909050f060d140a1b0f120f0f110414060306 78
    0x36010302030346800030461a0301c0c690b41284c07200c041f1801141c16400f00500000c420191072094220b022070641c6143d2520b0a1240c02400c507844580c41005c040c03069403007419000c003600204c0040d0307442162204810801800480c3c44c000c0594070460f0001d107000c1c1008241640410a0b02050050303075603480d490790743d46610704160381590050354925041000820010010324022003510b040c024256818400c0746000f000071111140d1054002c0742400518000a241180c040c0b400b411071f50170200706030b042801e8445140b01c2c0112a140c01048000b011800c26070182050b9801803c000b98107001070715103450b006140281a20039041124140700c0821801a072403c0724030f100703507400303006040c001e001601c81003401100c0b420b1403140b500072121034101007201c01108102e582c481500302520607203808600c1d412850180d0000003928051003544002400905000700c507d504903100084858007420a2aa412520558580d01a150800d642c3d456400f4001461168004800ba40c3c000d035184484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 264274883 1250 264273633 264273637
    0x102030103020a1e05060703090e041208090304082a0a1202090106030b01020604060902040b060a090f0e10030b040503040b04030b04020a06110d08092d0c1008060607060e01060f0614 80
    0x80410401d054000500c51403c0400260903050700074135141a07165034ad0300e41c0300e92a090695044c0c0e2103002c0c055002445070f802c8000507820400c2c1c030b0021450203161242450325140300300340d000e040c030840406231a07a1050101c900b10700018010402d9100c5503a5a441c1c010300042e10104a004441030030001404a000344a041c80002040e005828107985555410004100c51501240c0c410303901c0c510302c403043d00d1740070103007241c4036090700c681c5940c90801440c0798012000c5d502c203140481c000020807103ea26021004421658450764001c181d449600e4010b0039030155030410041c8200215002060190320301e58140668025a0a40d07425521000d0880b81d4140503c140a42d0350b10035800d92076000d1091102992000003d42510440c40400e00c1c0b44110541c0034640c40809604158a00d4840b1011710810000c01801ca403c08024010f282002c1c10a440040c0344c94480c51000c00c40c07100b4006950001008404498000c020182d00c400080310b25602c180540c0002600000e20003500000c0402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 264276133 1250 264274883 264274919
    0x10c03110313020d060c0c0620120c0c01020f041403121b0307020907050307084c030b01150314040609080705030a030903080903180405060607140102030103020a 71
    0x60403072440e542d03400700304108505500101e0304070a95107a141e01040162103407103c06d841070780d103000301d0307841c1400d01000b500c03248281e140709121101040c07601200c10300101c62001b101d6540c51341190f541c00003203002da402604440c0188c0d500010780c5590f4117285c10000d100755074940340400c91101c1380c0418143c1c3e8108112100420310010000104027001600240c14140d801d03034100c9280c218a64003183d40240165a01d002040d4080b040c082c60341e8100c1400d0360300408001e159403480211159840d44400d81d074070480d40e00700c401c05000f602c00f500700c9482e00e28003e00e03510500e5400c1c2e5918013110f107030509100c0c000002000c0720621400d140319010b80e42c04102d20300104030542e103945d29044d000f0400d4020840309118100007480002c4c8082c00a40901c200d903440000740b4840070b04015004000040000503150000c1000d42e4806004044c444520001680c0008056a4502c0845c1c0313175104070100034240f220101c5a41c2413062054000714141d91003514490780403540e40841c00c02d0600d01e5a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 264277383 1250 264276133 264276161
    0x1140306010e040b0f1c0b06060a050703081e040f060c051c02090a0f090f0501050f1818010603110307050a03030504061409090406051b03090c0105130b0a0809010c03 73
    0x34400842807409800c419440b800040100801035503280000700e29140101030740500c0c4d1080c1003240240812a03403012351180c0140d81480c5019180c92000b00306220311500102407144a80124500446810644400d090240720350050b80c18242441e13841110320043c111081c070704003241864428443c10075507480d007000d0600350031010120502e690107500101c1405400074094540001c105540308072890040191001c005a02c0d030104000e10151041604007901030001410721120030307200e5410900071541103d0100825403038001c1000304400c00c0b500101e10b9503003019004000d0010b01440c090080740c0440460314020f51310741c01e00242c0e184621018012403014001000041c0c054280c000c4000407554410b450b05980b0400142162819541903549641e10b1082280c4200500b180c040142030903c0414103500d8504402d9580341440c20a07030b8104017010a00c1a880c010740700c05034002c3c01d00e0100050300c41414100003404401c04030744147d200d60034200c0c0c0c0004c0600a1242403058400300d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 264278633 1250 264277383 264277397
    0xc0f011a090c0c120703030c030506060702060d0b091602070503163b01091a0f01030c0201140a0b010810080705060705030d09051011030906071116080307020114030601 74
    0x10041011518000b8405002c619040040c1103919000b40941078501c1d1071000e203c0c1c0c0701c20300b9007401022191020503280516107401c4c14071016998040076201035507811108141c0c1e941007910300c200500249100550080c008800b4003074045100304400b1300c091090740c03c84089075034810815640390019050f0704000e408209080c0264010242c0d04003a90008006e010401032011108210388601ca85004c480300042000500400e04a4020030040da031710079203401c2800c1140000079908100a1000c6030606642ea4410460a4002c1d0040032008032400e500003601d142c12130390740c40a4020f1404060000b442840080c94074100076030031400f962211001080d01c01d080505008243c3e2102c801651648010f01141981403024003030040100c0c4514054404003820440d004166a11000c5540307138050f00f84200728000304009020b544c8000940340460070321000c1c040040c2800000072070710440012100c070200d405080003009100c180d02c00ea031203108285410454004c03600081e11168005601 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 264279883 1250 264278633 264278681
    0x9060d15090b040c0827070810060e090c15090109030c03050c0a06050a050403061e050403020d02100e210f1801080604020304230f191a010308030403031515050c0f01 73
    0x260034291b40310440402c00c8940698841c990b00e407038031100c0c111282d442d81d00e9980a05c281a050401550481c07031410040803440110350000380b4400c01414a15000341003c0341035021a849054034800868000b420405a281c03241419a00d40760400d60440c001d590501001035810b10880403a0701400007965074502b420304544d90340020303008195000342d07840a524400600034505118031350081d4841d400611807800300c0385020f03092454510221840500d80001c0740c1d008580807550602c28404140403640984851035070294034051001064040d14010450100c0d03501c4000001c0b6800c20240c9a1604941d40c5a04000c268401198020310b102c004d5100e8034411301240803528442c0605100390307402c00c111810070700d02e0401c040c0501c0c1d09038580c5090f01c005103c3c0400d254041b006003151052103940c11a19400e08621029000404069854041e152603406008140e0050300449240d0274107260600b10081440e04142c1035582c0501030034801114040052041c5950010019200604003003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 264281133 1250 264279883 264279931
    0x5070c0b0309010908160201030605030c1302090307080d050307020105061c141510060809070812070f0804090f150305060105060c0114010312020601080c010509060d15090b040c08 79
    0x150040030150349444101c4c00040000c00642809040300022001e104014000141030784c0c425403044d0300940010150301d806841e450180b0204150442d805070303480280d0008680f800e001c0d81c3c4003010300d000300c54150102c554407030015800358800350b000348280c0c0c9800b02041808218006950148a108061100000d0352014000c1c510b00d403000c00c4d2400003d080840d005e448004403160742100d04c000c00d0511000e600300300c085030000d4a0000a046031401c01c0001d80c1d446404d00c02c2100f5040c0042421402c2001501e2440402e550040d912506c49966100c07080141000c5c00c1c02c80081805c228036514038410590390756044942060003007d1592900d01400141d900510103418103548850101045e880107070350060003144162070070100700302110310090030904180c0010210f0741101403100d0040c0c3e802000d4425285044034025a00c0d0f040c0d582c00401850304881000380c0021910f000103440102e94010819407100752024443c0f40480641114012021203011b413500d100c166440c1c4a81d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 264282383 1250 264281133 264281137
    0x615030905030904050a0f0f020f07032a0303060509060f0d06020a050904021801110607080c30040302011d03070803090708031b0709050112120912060605030c0105070c0b 75
    0x607008100740e0340303442c545102007026100129491010b40303403141034850010f019032003050308581c0c41040c11400c000300c540000c170040c840c040000c2c0410115912380c4501c110540340340400002c00104000c400e0f14a4600500a040c1511885103d401c401d80004c00b41d040003484182ca814008014811000807035503400025009102c01200300042442840403a44176480109298401c01d0f902c1c0701003075010341c00108807404020071521950040e0b400d000000c0c1d04040306542210994112603256040420100a80c82c480b0b24200fa5145440c1c078042e4000020900c51030007240240c2c000d01103280d4146101480c0d40004061500a171700c20071600001c283c0300380166820a03220350035903000c5941c0e00155407640d0041c030190400c003008507000b0350712803404000d0f0340010700309000107111540c0f400345aa030403042c20890180051610344440ca003954414000301002c2c0500f4500101c4c0796076503080040040c820340c041c0c10f0091084615245040d80143c06030b44d811a4000d5168204508042c41c6580c15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 264283633 1250 264282383 264282401
    0x806070819060b030a0501060302131518031b060305090d0806190312090f06050304230607090303030f0212070f020712030806040f0b06030c070309080f06010612061503 74
    0x92541c1000c6660310180c05074000910300a0025501e9040c00c16040b03084600c1a030000091510401070055452110b1620008886c500f00e61030518003540301040c1c542a11031400707904600850400802008800b0b18044082c00303844001041071078441c40107070111a404d0314074003145d034003101540a20034070070a540e50740030402070012030740480400c10402c610f8860f60421544e0b0030070148241c0c48680e0103842d0300024824102608a141d1802002401501c00680301030411544070034848141e88040c0300c1a03c505080c0b008a903507624121100501001450000310f000034106251203003280315900a5503207002091180c0d07401d82d1110282038400d408050451800e50184480004110040c036440d040818001d480c0e0509519040f005c000440d00098030401d103039840c1501c4081140c0b00c10058941c00442030302e00701d564441d5810151001302140d4080c1c0305511a02010402e01800450100d0484000f51640c0c50420b07081040c60342641d103607000d0b1010039440d0ba0220012180300e50800c0d022 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 264284883 1250 264283633 264283651
    0x60e0d080d1d030c070515070f0f0201261b130e18030a09050a08011a010315050a0b09011e0503040305030a06050d030f0f09031a070201021204050c0a050a08060708 72
    0x4100301000e001c1c0c0c11030f003201c0031500304d9402040e400c06c018103000d03910710300144040b00d00ba45400042d0fa9401c0e4414020103010303040100d02074440086900409003d4440c803100400243c403030010308240c4410100803145501548042c800c030381c2c2c0c056140020303201c041d003c00b0502d1250b503003031410b070070075240c2e0080c45aa41c3c591411901028032000b0720003041058055601c62040314144024803011010302d9000b08080d070300d0201d00090020034000d04112860342442c0100c3c0780515140c41d18051040f80d003000b5445900c1d03d80010345420340c40000c10304190b00b81c1358001c240041c03042c0d0f14105145241c002c0040352003040010006481a0015940622007aa0000e0080d407200701240c6071000106086020400b607040c407290443d040b00300c001c1801ca05143c506180c0e41183e8a00e00d01000b81c40034400c03004c2810003c600d040e4000c1d0162601c031010080e5440c0c06160500f09a03550341c541880140c0241d0306210045420700703201040030f05540316030008058070b844507041140c03101c900034104c40b071b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 264286133 1250 264284883 264284921
    0x21e030402010c1401090b060d0302100c050f0406080411030102030f0a0b01170705130f0b040314030904090804030c080303072106030203060a0606021c1407080d060b04060e0d080d 79
    0x2061061300c0c80d20703104075000010f95a034151408001d0f4160250101d8816060710750030b6400030f50700003905407010f00c1100012510701d80340d100c207550340e01a0340c07800c4848041c04100840c0040e403040e0b115101c0d500942002940a203101d06040c200d20040d20001c1c2c940c58500d0000d03100d054150000c1e01e100c0018908004451180c060306400180183e03803a100140c400100a03038100c00c00e081d00000350a074003420480581c503001c10360f9154420340c40002d02a02c40d1400c4481c500e003007030081ea0203140024000f40041090b82c82c01072006c2e0b1150000b1203074840520000708101c0000801c0da40f28002a40311031000340400d40d0042080704250400c140c06a84440000c001a182403228902800e0f02c64004501c0508050010b030030700061105201e69070500110010105611101a51078a9100c0ca005550f030302d600e00b040702d8540700d008040304205d41081e03c00200c0d450448002c000b207510320ba84640e410000c40041114880606102808a07001400704607041075255101401c5070501e148041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 264287383 1250 264286133 264286157
    0x20120030a03050103030e040b0a05220203070e0a0603050106020304030209130606090b011d0a03121107080307020907030b130b010903021507110d0506281404030210021e03040201 79
    0x25145501c092002400a030b01d8800400405411411040b102d0804803001d0150030f0808001ca0074035038183c0b2956200e00e841100407054582d0341340c02c00303040c2205003900755074a2400c02e10103422044422000c0740a440300300701c0080e05601c6442881d0507280c0e598007551030b191039034081040130517000d00760040c1c9100845001000032410310412004000c248000f0071b021050074009031886600084202c2050000101072030030b9518002104141c80d4012040719030032505100854000b44c441800d244503200c0c0741c0d8080361a200c00800b03401083e100312981d001e2a99028800c90940e050440400e070002e90125005016003443d400988200780180352544c5680d41c1d9800160340070409041e404403541c00000c01c00148101080c1c05061500250743e2501005500d5444a80d1410700a0904064040d030001d120300d00048000a0094404064800d000c141c6400f04002203d14083d00d0450240c401d56546011490349030007615410031580b80c200503a840f00031080e400951004000300c0c10042191180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 264288633 1250 264287383 264287447
    0x5060901110105070306051c05070b1b0a050601030c0f0e041709040606050d06140d120c0f06020307020618030a0503040503120412020c0118090b0d0b0c0d0b0409020a030201 76
    0x184d02c00c0185903008102c40e45890240b11100b00d122410880b00b00d0b010000101203400014000101c1e442d201d1400d81c1c3d401e20900850306c20fa400581143d03203000c0c1100351800d1040000d0b109040e0390103182040301c851764850303140505141510030090303c6818000000d0100e0b080044441300440310100080c607041d400000074003100c9a0b500200c01050021445070803c48043c4540c2000c1c002200c050705102c2c41c2c00000a0b0280741400004100c5030f40c2c14040501c803841007100030180342d482003080d02c0201d1b140c5024000303908212a2400103200b0000081e015800e1951840011620030020310f191150b030f400203d0700d40d48010f200352a21300c07080000c026001074031098280310354000c8003880c0c03905a1400d0300904001401e80440d040202d4040b01420300e01024416404031345c204a00000d54825800204040c0b01c05808041c02300800b2204200103801c1010042007080703080c01081112584010400040710381b203900282d04030180400500055000385241d400003000344040c41d00301c00750702c41c1d9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 264289883 1250 264288633 264288641
    0xc010237060204080714040204121401020403150504140604020a0605220803041a03331201020c070506040305030d110706021801033c02130f0608090313050609011101 73
    0x101d02da065101c2176040007211841603001c200068211000c3d842d051800344150640600460003800c2540b0005d48200154070940c101c40086a00102440070000e40c1000f080040c10111400d0711198450342c482001c01d04080307401da10460340144414815410b0030b40445094000f032044c0342d00001001d4a60780031580c2c210700c1c1030003031035800010b40e41c03203007403003440c440842d400349003001c4d00d00040c003e100c00c9004951072817050180e100710301d400340e0b140480c0040942e16906d48642e000351404a0200d1014410340090a01007070020440741e05c103a445050082e1449580710140c880d810500c000c920001c956000074910b244020406410600103889090403648404241c0440000403102a111940c05008005007000c0340b1505054442007215010448984040b5115260804844402504110b0342c1921003c40d401ca001d20f241035126100c001d0600c0780c501589011602440000394a02000811160210001079054285501d000305000070350300b19121850610022040b110004d02c0240703d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 264291133 1250 264289883 264289889
    0x11d13030513120c15020d0c030e0612070801050910060806040903020f030c030d0f05090a0b070201110f0c06010e04022b0f080a0305070201060627050301090807050c010237060204 79
    0xf030013000551070b210444008000008407107065400000c47d4902494012052002d01901800d181a5410300940055901d22036414204250f503030f03120502640d1a400350340d03141030700c006072013075000d5440308860145140500e10072800011083c60005600c4d0034240c2084110301e109004682105283d4254036056400c007200340e40135a032010800d030910041d9401880105409850100114104905829118190500c1c0545105803400c0860b41441c400d40c8038036584801414415154103c2412410f840d900c0084043e56501c100c50000c07462400d03c80149000f140d0061000140081d9240307000034070320f00300340450017425115040d84046400d1480f614003036885019182d5440c03080f46406001c580c0c02900720400c5a01d00f010910815810032104480c40780346c45075010b280440b03641800c21002c40c2d0340141c0d03007550800c00810100303d10380700940159072065007950240031080b0f00480e0769421170041c3c0c00030b00c981210743c540154807080d440551208400d002c0040102c00382c03034000907a03010354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 264292383 1250 264291133 264291143
    0x60309060a180c05040e15070309030305160e1e0411030702011506020601170c040603080705190b0118180308070f0215010605030c070c030b011d1303051312 69
    0x32040040d003212910980540c048910701100b5a40020345034072203801514040c03540903580c0c0d281040020030080044441481d900c404150b0745183c200c0000303000d850a01c0044000c6811b10f00070600402c0302c06d0018100045603a0391040c140100801c02050030390702c04c0340c07144240301c10785460115101d0340a42c42c000311101011075502d08007890001e0071115043c458031614014a202405110b43c00f00782a81154041041c2d0211803000110481c20440c00e0b2a9071a4030514000000040051820141c80c0c814001d2042c0c0d005c0380d8810401f059040140b1900a110704884401803202204d4000d154408034042600064011911000e11001c811a840241d021401c40400c200500d98013035040f0500204500c0609020101030594001c0c0e15410300511061100100004101100381d0099624142d00a044644030550304d051440046900380990200c0341c003c440000c44107c80704800502400301c0366061485640740e0745049416402c0a6540c0b1842e0808440c005034a95a01c010104414020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 264293633 1250 264292383 264292393
    0xf0a061d19140a03080606031e0f010f0605030c3901060504050c0a02210f03010f090c0e0f0d0204020408030a030209040b030c031902060712120605010207080a1b05060309 75
    0x182002a80004280d6a03180c1d143d000d00707030040000e60700541aa412107030589000b41c0b0707034691503103150702c2c0390100d00f070b040c18000000d041000c0490314450300c0c4e0403144640c0c8511640340d190001154140300856a411140c0e80800c00c81a0303d030440426102100c81e85c218410240c011000c902d004240a0b0480c80e640783e466600c240a903140911400e03801481d249540d0746007072490800a52140b0b02c0e80581d6060003034003040c8481070143e180c02c03140440c14900055541c0d6855008801d4451002e000d0741055602d0b0002c54402c0324000c100c400e440e1000280100304481d81842042210000f0050498000741c00f4000061179080800c00387c0390490301520056240c1c841c0e0b409000807030313840030720540c441c0d4081b00428140381c40101d094258440000e1800d20813400354008203c080c070681100030540460b1514005402d98000d6070580d402641842c1071250030341c1c135801207a81d0303c042d004004440d00000a9070002410721120099007404451042c40210707550320000e0200c0d0006c4440c0e540b29000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 264294883 1250 264293633 264293683
    0xf1b06020a0f0f0e060f070b0408030a0b031207080c0a0615060e0a0e0601080403022a03100e1c030b0301020f030105090a050408071104090203011b0f020f0a061d 71
    0x5200030354000742c0380b52010039540f03e0000100804540c41c85036004035800501c51012075084d40c00c42e1001d68011231450300354101840c1035055540102d51020381c0c2464072840030814075021030302d441345802d52000b1a0134032010b03444683c05980412000003851140e03801c0c040c0098010701030440400207489000c0c0f20a4a0250003800c25055052024815581482c0034070400d4004e2058541110080c42c0c440203940d51480d0070380c0350440551600150381480b1005080d6003480e0a0303008070700c89003a41075035025a414202d1400b91880c0040040142d000390f80505045889081000603040541c500403a41c1c10ba400042400c80e8041030b260100da5400100500041c01d0001030355400144803c010819840c05407200441d500614100034815100701d002480c441e51103400020086070000d0081003000b10326134002a44002012504e408185125003c0d0340550001c00c03070b11801051b0b080030b803210302910359a290043c80682800d55002e2a2100d0140621404008104800c10303a450082c600c0a8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 264296133 1250 264294883 264294887
    0x305010c21053612180f060708161a060a0801091a0c0706060b0c0708030a0905060307050d0e0d1119110d0c06020a170304030507030c080409090f0204050915070f1b06020a 75
    0x842641314078080c0e206c0012020060300d8441c01c40b40c5858004254580701d102845041403808074040000e0103011900241c80041b24501604a014800488282c2d601e0b90b506e03441e582c262141c82901500d40c0d412030300c80d29165203550001960040d90340103131074076019061740c6040031a10680c0221040e40030204140d80c2c444410080680034107407080045003403c2600b10001c00a0039135000e4a80244c1000c00030413540c40c017402c00e41d14885000a030601900b03c000003c0d03a0703580c151182d80c0c40000d11211280c5810000402d80031070350840c400d041300050602e17895002c1c801c402441055003000304083d000010408000017207010742039607400b402e640b211608150300b901e6410222200e401ca400c04c24480000d80140403a50b070316034103003403615080400e82010000c40c02a81c0c0312040b030074106a43c5a00300914071303040c3c0d82420300c2140c3c10401038682c000d10680e070311020074400101da844200810045800341080d5a952803840c5080325414941d002c00403c81c4480310400c8504035000f1580e00c40c816 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 264297383 1250 264296133 264296167
    0xc0607030806180603060a0f06090e0c0414060303090d080c0307050a0b0109050114040504021210020a08010b16020105180406060f17060a1e0305010c21053612 70
    0x300100e0f101d52182031013000280c4410000d04000f003095540e58100034020119006100140b00c0c2603402c200c1501c2c40e980b030940752a80b0001040c801c0c1d10300f800c40001074010381d0702c050241340007400850801800d01c0900c980b0102d051001d40d4000300500c08507010803410002000064800c2c1c0240070f00c040149801c0781441c10607000404c10307030b013842e0043c0105154008040280c0004a40c0800d440c0c03500d0008c550462100039104e0f416000d1440c0b50180c3c00459002480180ca0556580c9100d85c1ea4204031581400f94540355911844003591800140d07110310040c0145913031148003580c0e48a00a000103085500903407045011910741d00701402007540081d842c9501070900710100e00c031413a00400241c0d40c15401d005400101050f0741c0c0010f032000010700440c0203142e03c80001c12200105000107000d402645442815100c00201d030440d00c40300c0c038080d0318040c00403101140e03814200c800380940501858610048420006055003440000400941e21499411501c0075600c80c1e200a00d49408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 264298633 1250 264297383 264297409
    0x6071b06050304261b010b0f010c0203030f1309020309010c030c030c1e05040902041e05030d0c021e0d03080a0f0e0619180c081c1d030c0607030806 65
    0x2002042c000c000c040360740a424881074018420f0a40b19045070801e010340c0501a0f403000c03000d0b0300c40c0d40c50251800741056024111012046425580101203140115102d800529000750950014004580d80203070420107000c01c9188181d4010341180c46078a414100c1c1c1084030021520381d140c07a004c4005a40502c60343c01120703190314040c4071011213000003808110340d000a40b18800c1c1034801044507144144240d4001c1d000d0342c14195525136032880354042544070035a803d0001001c1d4000000c29207800980c20b440302c8465110009521805d40130071030020181110b04e00403003510600306040742e0710030f0141e0110740d2103525400001d080c07040d204d0003110154961400040c0c44c1070801c40d00d04000081c5164003040d40e510110107030f0840304500001d41110403a801100040540c2041000114882401520184411140c86010805045001e003400304100f0002c6a05e84034420b01c11151140c0700d46030810040c044070001a04e66011650f260310a1500b900000d104006100907031800612880e11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 264299883 1250 264298633 264298637
    0x5030d0501120203030910020c0a12020a0501032a02070e01061d0906220e01111e04050105070201180e010902070b06120c0d060e120703120504030905040e070506071b06 74
    0x90740b4295800f090f5a442400800c5104030304000c1d0b20030086108000c60341002c0006000d14610f00d58606141d00b07481c40b6041d00706d1103014100740108895100c0e00c14800d0a5003051000c15010903441c030a0f01191401c00c41700320440c010400c0214104021203070150081c08960b80c0c000c90000c12811481c1003248000e9810320990f03643c01400310329038a84401c54106440300440260100c50361529100510084201c0001c80d42403032007200706e0303c4406c00640070b404000c1c94850300e442000000602c1900c203034000c1c00d000c40c4050101c2000b55200b0030051490134103124407540515140c002e200101d450036803040300020340004000041040000c001c5800c11000d46103030324141c05030000e0342e880c0c0d00f000304400d00800500000c001130040d160081402800e13054242c2d0325101040302c0980380707a0b00629050f0040340d4046007101044920348100742c13059030556280d0456504090402014040001e00d041f8103100303a60002c202c0e80c2d40c0900038004644203188080c1419540c00b80a00000340982c82581 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 264301133 1250 264299883 264299909
    0x9030307020d0c1e0626160908010608060702060c030f0412030f0e010b100503060f0616080313030905030607021c0e04020d020d050903070b06060d020d020a0305011a070f06180f05030d0501 83
    0xd42c2551b40400381e904912003210324040d011030032030304481c0e80b0313041d512900307076982002800102c908000c00c456000312900c1d03083c0c96aaa680c0c0028107041e100c203482d500c1300020030b10005804a200f9105401c1545aa8a00440c49140f001d4241065680c80303c4524100c0e50360b81c1e625806403400c0c1800b9071003484141000c0b4114905500029100640f071020707075014450010b1440c0d04c0c2014080401e030302c1c036408a055610b80c140b00c00396117480011084100c000ca2402c0070003040c9460b0010f0b414cc407510880e030003400c03104e905541001480003c90131035420b001c0795143c403083d140da503400602142505011300681381e01811407048140c81d0090102c00554000700900000701e0600d42c00b460340030000340c0c1d800e951074041c8145580284070b090205407a480c03002c2440d5925942c99080b03941242c04aa50315482c030304040100d660203120b1418000c120b102c5000c494000107149401800300130001c1802c0700d95061454541d030380046031f0000c0843c0c5a400002e40d418088103203120b402d001d088001503200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 264302383 1250 264301133 264301187
    0x1a0306060d1a04050a020a0305010506041820060405030d120c030203010b0d0b0a0905280b060d18080a0c0b0108060618270304080c040209030307020d0c1e06 69
    0x70380310850315690011040307150000383c1800700c20441c1c43ca6080d405008800b801c1d03034a00700743d4024441611322500c40c0b420f080505200b410b10100c03101d01240c024070ad68980c1d00d10442005c1c403035500d0300800c1c1e1300700c46c05110001d50795a06010485401c0c0198942211a400d07004005013101c064001d000241841400180a1050341409807005112550300020764803214100040a0074000d50002890034182010061079000ad40c1d01e1104544c04910314400401c44024000240c0d04004046038100405002440e003803219900a946402c5003082c8101c044815034032205025440404c1080c04207100c3c034114010400c404800c180140365130b0018141d24184400040c1c49540c44170300418040980c2070210712513450341d40380e840000c000e0310310940d1104000403089890390840d100e8401701d40250540308e4a5810180216080010028003951501085908100341c600f203020054070b4a003480100410f42101e1b001307030041d94945d5519005041032070b0030030051810b0761001848000ba14071110780 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 264303633 1250 264302383 264302393
    0x318030b010512070e0a0e0d03050610050f13080f1b03030a0305150a0303030c09093b0610090c05090d060e0102160605010608250c11041a0306060d 65
    0x24078191682259640060701c0d0304046549001069005107020314840f43c00d0054801c01640040340e180c103100d00780c0300c0b10700c035045040d0215080ac48450740c1000d00c40b16824140d9200788000c14402c6001e1480760b080c04200340d203c201150035600f00d001540e00204014400000030070040d801c84102d0300000c150024841f001c00e032a400340240c103c3c14542c955020803203c0c0000c080f80001c0d4a000b80244d80365640da402c005010704800141c110100d0840b0b81c002c64005483d0091003084130640f480c081686134801210541e00400041070500c3e01146002c0c5c41c40108240207003802000f140c81140d02081c1820040700441d2242c070404010720104010021407500d4400c48540400d03081900054605650b00c24140a840740c1710440003960160307030044040000e903a022a05031181d07541c0e44800f03a40c40c2c440210180c600321380700030541e445d0404001849031140042c0c0c1d00031446203000505a8900300041015200c0340c1028803110b0350075807004c11140c1810450154482c00031a9911292100d030748403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 264304883 1250 264303633 264303653
    0x905072105150703180b010504050903120c090d080d050402040b090712051f09060305300708041a03040b090c13110906040e100902040303051c060807080a031803 71
    0x1000c22046584000540d81d0f80c00380d88540654070044405104a5080d45418607010400b402514407407840c04020581340a000400d8620103140e102102c0f41c0c0761030740c0280313940700c0c0c029140782c503845046440c0c11400551103002038903c501d42d65002142e5400c06104101c161081c60924038041c0c0b850704200070603d68403004007000c41181c5140040c090721a1a025803044e03050303c40d494042c489406002800b00e5042d400101183d000c0c00076201520105d402e0200f003450140706445c11290394001c0c900d078269501009011061040c050715141c660b44007000d905c0904042d030300059001c0c01000700800d0081c0f8559442e48203034100003030082c089051000542049840c840c0c20981c9a4038528135203042011401c03940d00300d13401081c140d00c80d9980e24600d0180c01d0200c0310f00210407030540c000034194030a402a1800e40358507460b803d09201503000c0e4140300c02c60180e560850780d0b40343c0030001088181408804040c00521001d042c001589007000707468503d545d400b03140c036001034840070000300d0b242001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 264306133 1250 264304883 264304903
    0x30c080f060603090f0607020a020427031103040f090b040b030706051e0c0a14150405060406050a0f060e070e010915110a0b240d050c1c060905072105 66
    0x30b162601d0391680080b941c50070070241a021300c1c0d440f8050034090117540000343c0b5140c2500c00c0f14144074100040c402c40d41c4401c50440040c40040c0e003c03500c040003030300540e0701002d003a400e04101d9051595403a2003401e00c50042c0d0141101580d501d802c48880c0c10640294940342e00c096005100c40340c80c000c2c0080130f074400c5680c1a107130b000b0350742003030001c0740f80910448990743c00000480e010600641000d00c2038291a4200456500c50499205814040500610704c1a40c0010180c09241d840780c07901c5001e413070b0040241c590142e43e000c9a00c0c228070070b881076102078002040c0e0101103140001003e0109103910001c0d50500c07141d00e10810820304403004c00800c2d01340340c0c80c0c60b80c8141101c1c51868a40071464000a1401d078050080180f11103180d00345042041e50705c404214030b403203400184403070101d048001030305a4128601081135401c00140c1c1200c2c401c030801083c50043d00036100d900c00c0300d052400444040d0441c100c10418154610091200c08003802c4210768590007a59038140d44142c03400d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 264307383 1250 264306133 264306139
    0x60819031404090609022a030a0309020d020d05010c02060709050a03170f030a0902010311030f0a0905030f04030302010b0306180a20060d050415180201080a02040f06050307030c080f06 81
    0x580030795454034100740c400800e6100421301c540c54aa500c140d006e90003004001101e036900454121200c02034102d07004408009501543c40d256404204902610440c0801c0e40c00c82e016100100c016120f56007881c000c64003035130002544100f4907000134148440036000b142002001c0e9020b00c5903541c0d4000c002c1c21a58001081c0e4900b90201d02c0c0c0c4152400740b8002c1c1040c4d0341b00031003000800e14550304941d140354800d9130100071401d040800030407580005d544481e03400000c1070002d190541c1e01d03404005002d0103481145c1c1045c250741e034890030a81c0941c0003140141d465404002c214101000115000440b040d080700b070207068015020350360900c404025000201c40c0f10403203400030750072005e0000703031030060301c1a030383c40300500c0c40c5101070071040d10f0441d4005410000c0401802d2140305214200e40f101000c10760720070580e0011128100f01524001880e603080200084d8560040b084000401283d00d90540f00d15100001a084035045503610041c8981030042010303502e6030403c5560312031411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 264308633 1250 264307383 264307397
    0x105070f031d03040b0408010507050f04030f0f02150409050f0c0316120c0c0b0a0509060112030e0909070312030203011401200106141e1f0c1a04030306081903 70
    0x100b05100358514008803000d080c3c0400580858410114001042680d150100030702c20340c1c6070144204c2c2c16114170000c4c401d6003d818481800007503001c03800007080f035000d001941c244e042160001404200c032203902c11011500002d0070801d400d240d02405074880301000107110586008080206c5502c401010304440104840d00d0240160054880403029645c40390104640b041001c0d024007001c00b07010083d61084140d20006000c110580102031103800100e02800250346880e010b07143d4604801021814040c3d80100c01a0644804900510641c0d4620042c41458914104a1022250908020f042600400040c0280312106030f80c00a0b00c6030a103000402c0d04804562103008409070700341c0e480254249900041c00d01083e0500d6900e0860440c0e40da90702c2e81500da00d54000c2d04040403040e03005210404d0714412904412500c00c4040c2c0c50381400255003c040d624075030a20140902e0401610300482880181985441a2030281420400400c0c40100d4041502d44a80b22040c00804000c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 264309883 1250 264308633 264308651
    0x607050d111204060c14031c0b040b060c0307030e090403050315150c0d09170a0209070c021003060e06090105091305101505030f0d090b03091906020901110105070f03 73
    0x81000d11400035690035002d4440c1d80302c0c44d00400803c4d010105030b411151480f6030041c1141c0100440748403004500c40455070056a666950142000760243c07a8800e565440d1105142c039008028150b15102101450b5aa1800d00c0c01403d0064a0000d041c0250384076010440025000000c4a401248041f1400181041c200c005141517401d10400e507001a8007048200029200084141100c1c0e5991981c00c4950746400350003900c02024514294181e10034a880e0000d030400b0340007280c00c100140340041c845d842d03503004070360350180d101d02d4040080d581d040d04000713501029101e0341e00203900719840d00c2c3c0380d45000001441401c01401000c282c00b10480d50108000307080142100c001001c0001388040c0713040a812291134071040c41400d00a003daa142e000c805403012030040141c8003251186030442c2c0c18908018015040100795403803d11440c1582d00e60b029280d000c45d4810340c03082201681d20248400010108525007022500700e80c10702c000c0c054580e4000308003000c00d0b95103203000030705c42c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 264311133 1250 264309883 264309917
    0x1003080d0209130e0a20010906120b0604080706090902030103020906011b02030f01060302030f0a23030c061006030e010e030a05131e0602070803120c0f090a0e010f050607050d 77
    0x3c4610001c4086807800032106100000412148000d5015100100e401e00c0c801c0381c10301c04494940d2030079000400d9240c1c14004e850180f0350036254403600e079000042c4146002c010845503070168101040b1035010010410096500034602400f0300030016007036086515603404030340403140251015043c002e01c22104d803d400c3d562540402c0c030780d400404458000d0051843c0720300802d45400260b019000345481900e4410f000075500c110154050311029504060300000400c500e1809002841800200000ba0b06030300e0400c100750142007a1000e04041516106002e012200e0444648800d039060680e40c000410011040d941c0f40c00007410225035030408408180c2814030103403c6a0703042c44c40407078072b494010701e410708807020307118642c080300c045546582441e6581e000303050361441c403001000000f442c4006c1460150901d00b001007003103420a5158400101401403a03005004080d105400402403016518201001082c05132500b07450403081d0307210541c80b50f581a01140c00e010b040c51814580f54 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 264312383 1250 264311133 264311149
    0x12201b010b1f170f09190c030f0c081b040506040c0c03180905010f05010f050c060103030c02010c06182616020637030501060e1302090613030203061003080d0209 71
    0x2040b050f0360280c0341e15042c101d4060500c030543c3e003401e0520603900721041c182501e50798081100c0e0445a903008083c55903403021101c0d052400125000e0380307850780000e00800208000d05040d1260410440c1310f80d014420b0108031140100703510b1080742000d94170480e96070032152100e4415050b01d003205005503001881c0809696540c40081c50924003000081c400910003d20f40c04c2d28000d9030f9801080607844c00441c1c050290700540411074004200420010740078203101c50a1070f1041c1000f116a00d866102e001c11a18005c1e916510000c0360015042006481911405c0b03030460207050840c041131854030032074a4010964100b869200240f2500255628142910646101000c9a0a00310403001d400040000c0155002c1d1b0342010383d80441c2001800f9004040c141e99181e0f03200c02e0312801603070801c8035107002c405204045940c20007848000c0d444010040c821445d4014624400c1480c1d481030610b4190001d00e070307140d00070f01358200740000b038403202c2214043e1094a0f00940c5540950740000e035a0b07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 264313633 1250 264312383 264312407
    0xb0f0906030403030c021b09153016030203072705130314030115050705101104090b06120f040f050d0c0201091502070b07030e130f151512201b010b1f 66
    0x3c1c44440991460070408404c5032130144ad024415503004058503160301c0e0002c80076001c000d5041c0c100c100144201c14a0100601c40768801e180580b511b100241c0000c07084900940d00c603280c03140240e80c03c20900d03030451144002e065051010501d19894a800c0d030080651124000040020004040082c01002c000c0814810801c086c00c010700090304040511540c014410440d140d401c1c19075180e024504001136a188002c4e09607200c04d29511502112800341000340119020015803c080b004640704004040702260303562210940c104641c00090030301c42042d441381000b0803004065509207540400c030030085403500b959060701c401c480e1034250742c07070207800710b40540017207580c05c0c45441c5290700d811440700030019038010026500d464500101000c5da030300a41d2405444003d0358403816220320b43c1c1d40e11044156800064032030300c00d01040d0820501410840000401003613420000304071142c845d180320040300080041d40707401c00114109405e02e42403206166401104060309a015080c40e0202c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 264314883 1250 264313633 264313669
    0x4050607030e2521083a1a040e0706260708010f050d0515090102040504020708070501050612060c0315060a0908060606130b0f0906030403030c021b0915 67
    0x10454801812040800d110b00c10071140f0080c4d0032241314240580d005900300c00b6080090f0714501102d03aa102c422030710078075000e08442400c1d1081416150440d0301410a0381c0610103000c21550744c0c100705840c00300400c0c8a0a84580d140149007075102e00002070070b008540c55814801540800210440746102c5105001c00101e84034008007e1b400e58482022410b0311005500c041c0c0e0103444034280700340d444800d43c008101b42d10281c0200c0420304003004141c4c1c03162030390001600d81a1901e021406a8202c42401c03a4034000100e480300030441d00703006d01d6500034029200421440300315110103079124800f0306248141e020010224240c040d194400d0889003030090030035130342c1e10f151010040c545641842454001e01406002c50b0113464444205c40050f1801030000c80385c681410031303071142540a40c00140d41c50b201041041074a03124180034510881c000d480009004001280183c06e020150482000750011782c0e1a140c0580c2c1c03034036011508200e807280b08071440c024840c08101c442401100c4008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 264316133 1250 264314883 264314923
    0x50a17010b0d030c0201020709141b04081036060509010605040504080c0601060504051e0d0203060106050d0609090b070806040b030303240307061b061401090b031504050607030e 78
    0x3e240d002215400054800e9084544465859603a10b084800c010254094080c0325008686140c903403143c411150814400352615040e40d403d0954a80105c0a8000c0c00c69a210407502c241303000c8210200b50108107550722509c002000b041000013110501c1c400078409607503400032800c9070009611601c041c240207081000b042c01c0034284000b03d1340021030003240307510441c0004903001d0320800545040f070f000605200c000e40070250719213031034244000802e60081c1d901414407001d40d4003040910b00a12258480680d620400c18102003a260550080d42c03d2605080050001a0f0200b803207540c084024505030f003143d114100000d02911044505035071503c004828452041e0103460a01e60401c0c00b440f00e115482ca110f0281611540d05201c0d84000c2010361043c40e00c2e00082d0005065410300c105800074a150403c00b1890a54500ba000116080c0da219010411414100f0074008401d801282507102c901e80b41e9901655600004d2540b010151510780031006d8580800c10740310b69440e50003100c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 264317383 1250 264316133 264316159
    0xc12190902060a1d030c220905030a0804030f030b0d020f0301020c0a0302100b0a1a2a011409010b0a051306031a0403080105120d030c050903011a01031104050a17010b 73
    0xe110b4504c94019030982c0100c05026616407400141c21158170380301814204005036110b440e0349448400c0c0c50340048042c0c542020400081091006019070281c984400c92305003094240104944085800712013454900b0304059010354072940c1d20041c1650454081c81449068400329029014036110b028861045040d800c04041d000b050307000304503914240404c05c01038642c040200f106d040307104140d10b491355105030b80c080b00c0c04c01004180424084110740c40c1c44410f1651032400b9000320030112516551050300400345640c2101e5541c101c0d407010001d2112010300d0b030004151311701500c50340340300781400d00b42c0303400f84e140300d030410401581c0115030442500d4095100700700d4440c0032101100028600000440e09183c041010b90074400c03d04010100041c8034031081c1c0080c84011134035028030005001c070650039034bc24007443d610310f150081c180060280003c0003500740c0e500c007480000c0342c030b905200622130b076116180da40e021652903003554081e02400c50b41250050242104040d00310b02c0100d001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 264318633 1250 264317383 264317387
    0x60106080c0a0903240e03090901091517060f010e0c0306010c03140409050a0605010f0f12110c032703030d15050402120f0a02070b0a050601020f0102210c12190902060a 74
    0x445c190082c0071401d202c42c45440744419207034032400141c96030061500e0018406141c0590024100c5002c3c04071640d1126226002d011400780c8012800d05030740d000c401040a15400360311054010041001e03d14000e0900c0c541400140c00700803c02e5040140340001d1f8001d06129540c202581d51902840c0f5507900d4680c0c6811001d8039040b2480c1c110381c0e0403e900000c2a520909040006807100d5540704078003c081c50b421122010310310000180182c4075456460301c88a2000117188880c2940c0003541d8640c6200360800126030042074800c0c00c0080040b40d1001381d14084210307012004c01d040d000820070200e2140d01003010b0150849501b0910100718807012003000500c9030301507420314400c1211035407183c140700164461458001c0048408034003048c1a551039170881c9400c614140151107282c0300390003080d42280c00c6584101c100844035524812240701d04050302da0000b03500380d4618917112409045611301403002d0044188200c02d03416401d03142145030702002d14154000d200b80c0d80c0d81164000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 264319883 1250 264318633 264318683
    0x4030c122001060816050a03080f040906120b07030905120d020c01050705071a04030c0f020607060e07050a0509040b0c032205101404050607210e011508060106080c0a0903 75
    0x3d4610140300317505035582568500d0001c001100c80080002220501b16503e641003604503100441e070a80e07040c44003040c124203a028060140c102d80100d03500e02c044504204034074000203130841c4149860f140f0840b001c60004564040c002d1502c8400c50350315002d40310550000e2140419401d09546020244000c032a40a030041030a40c5c01110844030200c0c1c003d945030180d40d03050f200200412950301011001a180c40354403030b1040c0c0014207103410710b5060b442d010140e603443c0d11440c0490b04050010300c0186049040103014200036503880106240a43e11160f1054011b00070406940c80840050105d00e400e4801c41402140c0c13030140b8401500d140f800707681e0b039039086450060780b5007400c0d9040040f0442d243d180b441143c1000090500d916104402d6034030302241c001e0002c0001c11003080c01980390060080c0204030350710b44000518194400021500e8038881d0304040100d4010900420501d6405400703c0e400c0030389035100c00c4e99000c122501355500d20a65000030f051256034240341e0281d55072116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 264321133 1250 264319883 264319889
    0x80904060f0f090b12031c0e0f0309040e0703020a0f080c0609030d0f030b0a1202121516020a021003150f0605070809120f030d0f020304030c12200106 66
    0x94203100c0952202114030401e40c16005a482079148010200410030a54201890240000c0d240c100310060b07210013030341164003130203510700b0508508038a91a0300000f0b10840048184a20140980151a164035034480c4603500c092440b95132168404111f4a5082c410a001140e0041500400300d5440c4207220b5401c1d110f03c150100303805940018090f50402008a0300f404000401800070202540300540f032045e1140501000c05580f2095a82652602010b000251031207407c100d2520201c1d104005079030495a2404107030350031883da0615a480b2107003006421141c800a0301e0300c1050551000c030b142102c01040603500c640c10701c507080103c90301030f44242d00908882a00e50000381d124820705581003150700c41c00002400400c8a8800324612070058822981c00510490580c2c280c4514a4a01029050321601c0e642000500000c0b520017072042d2042c11120400942c15490540c138081c0603404c1100c030191070801000c407100010340c461170000700180881d0000307078125600e40d0030160080107540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 264322383 1250 264321133 264321139
    0x60c03020f010501031106030a0b0415031b030c05090702010e121b0a03050f090409050714270c0c01020903010e0d0e030312130c0b0d091502130302040507020a050a0809 74
    0x8100c00800c1d00041c000c45060301e40200c01c5041940c4072100703102c07040d84014510b141c8030b540d50707222905940e100d010341448040c251029808050441c1440c902a11910401c0326000217503910420014511003208011034200700c800c41c0c8196141c0c04246c5c050300649161a04c6401402c4c9440d0b90262070b48080e040518525002000c02c89410410607a200340c01980a000f0034028007102e880350400b54002d220344140900301044d0040300e81d4a15190050940014403401042d000b441900d0500690010481904d0407480211741c140a0660803c000c0280140c0c044c10000103d844031a50250111182c181010b4002c10000b000038400c5510341742e40b00c492000048240d0112039140c80d002042d1071075860700ca004015681c44001e03803d46988546481203444001d0000001064010f0030003609080900c040003007054001483c00c2062082c54010b9044003a04c1440740e01c0c82070810f03011560030b0741d42c1079400260944411001fa03140449c0000e008080d4801c90301308004005071000a4401d050b815 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 264323633 1250 264322383 264322393
    0x905030c0a0c0e180c0f0307030c030620040f05091e0f060901060309050c0f0a08060703020406120c0e01080a0e030c01020d05071707051608030108060907171b0a05040501060c0302 79
    0x1d05109407004e0402c403070180c080c1e03004d1248002c480ca001165003c2454005007280c06807980d83c0c0e51103d1080311340d401960030b159160311480450021000d41e0b05070400144840d4905400c1400b040806d044078001d0b140500c01c40c4000070356149400e682400c1c030b803c031402100100d00c1e00d0001612420303011600c190007040346000004070075029020788072807164000301520004c41407009000b44290000a00790b80850094400140d9003c148a124011807c566000d40d680e403c004026011611003261403540c2c0d0b15051064a0094fc4600f2001c200c640920704a85113458119001001e07000000d14030a00c2d00000400306101041507000303043d8002003520502c202d5454100595846808440d65000009140006186284240028096070001c1d62640c40c035014103480b141c840c0d400c00d81004c890755102205001003101c0400240c0000d180c410001000c10300d280110a864110000c403101d0116480545051146d88000b8544050403000d04104040d41e511180142a00802c0000350301600407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 264324883 1250 264323633 264323641
    0x317150a09060506090d082b05010b13030605070c12090303020606040b090f07110a0b041b0b09040b1c03020a020916080103020105030c0d06031202070918060905030c0a0c0e 76
    0x407500560040325001800b6505105009050003130010f00b850088804950401909140102204901c0c0c0d00060818841c9010103031000c0f132504541042c1c020341117520042c4401014440200081d0003600d91180000c50759807200c0c403040d1101480050000e20015188400c42480365020b1501c5086900a500304d0b14551542018041140d1b00d03440282d030030034020b0300014080e000e15511143c000d0740e2440e105910707038a041d004904000d0041b0040300c440f900c200070f00c018005050706005100745403980d058046072030324584841521820610f94060f40c2c44422210342a43c0348000c0200141014800c04284041443c00a4592102100480c8900c070083d0210728903040c640d502c42c07410343d02515840b04590854005607100c3c0c100038400c5121710b83c2004040369102688c0a83e500a501c5000e0741c0065642d600c201a003440702d240c1005108518194042d208981c45e840610140c940048001079504075130b00b401411031044542e960f01c684230741480d00c42044a503900b80c40c200c404420441c3d0541d26 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 264326133 1250 264324883 264324899
    0xa09060804080406081f120c0501030b0d021c050601140102120444212503020106080312150406050f040e1e060a0b1002060f040317150a 60
    0x8400c1d5800780001c04144400e2054a020b12001d40d08001e51102d4921a09002044050303130701501d4200f52044070503494083c0c20020165004030140400342024402480800302081d0b04a443d030070041d201e1340304a280300d100e000248660264450300942626281d41e111004075010110740940280140715850359030311441c440302e0564064840b030807240c1840320013503111041c2c140200c011040018014031244140d05c0180900c07000420040c038040c0c4005204201350004521105003075841c0404100308200400b1900300c1100180400e041d0034606500311170804900408180d00010a5440300051582d5a100c09131425441412803071501c1c03148880b0f0303100340300580d410391044940000300c4254010302813405800a120f81c02c2924122607103138410181c44e11078a045e410301e40c1c0b4650801c00070300c0f82c000700b03600904481300c01c00d4400844000111000a695140091031101d0305100000403808051050050b460400d800410340c600500b0080002e44030104518440c0e40302d902c2011000554031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 264327383 1250 264326133 264326147
    0x6060942031a0616080a09090204090b09010603020319050903090d0f151109040e0c0406060509090c0a0c14150709050909060f06011101060801020f03010806130b151909020a0906 78
    0x519582d64440c00f006641380c2496800020851042c40390500002c06c8c450a20f201400c01480c0c4000302042d8000c5000c1803103e0788030180c210008250041080044005481c10140706041c00c6400000d01b650307403215014114050307074003502e50212441d0400401d0007264015010b00da4043c20150006526580e0b4800445200c0703040325107000424020003031186801e6200c14110010042662513007440c0e500041c00700c803015045200421000704103c0f816003498900c0a0384000440481d80c41c3c05010f1710040c3c001c0d8412880204280184590340ca0294424045046d02031580410030a140c01c010070050280c020074002c4601441c0440f00060a1842c00200f980c0125038010420810341c41781c01c01100d403100c0b01c840d901031640d00c4400006030110248020311404500340081516541480c2c0c1c69800d105024003090040614102104041101c1c4010581c08c10804000c5451002c50300c03020aa407100b0f039200e0655001c8003140c000030408400c2d00100800b0b00035941e00c06034252211010340d000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 264328633 1250 264327383 264327397
    0x8060906010302010e01020a150518152d040503070b0a290103060b0c0106090e0f0d0806040e0604140721170c160906060942031a06 58
    0x40d805a00104007550140c001d5020202061043c2d6804881c26107030b00d44404001e42c00341c2441641c039420440c3c50f6030072000010351018001c014019105441c040500e00035030140c400d120200c10610b074282a6007018041c8030030009282e0103800c0b40d140070300b09030b612038104c0c0b0000c0c1d030b1240e8003070002111481907205401484118030000c0402c031440004140000300c0035620141410b40d1000041098070304203019040e1400305500118034281400901402e65030000d81c1740c1401d81c01380422020030b0002080c00c0701c00d11082d242c0031109a071840e0014018104c0c06224200d58042d41050105101d0750340c51141445404200b1690034940e90f41803400450340200e119128003110613200c80000e00f254120620750344000d82a90708168007035090078182035486400c900703602204201080320496500130707880200708900700b001d1001c0c40c001d04d00034074000d61035541400d0340010f0b81c0c0101407d8504021070940c40d03110810181e007420040068020694203084050030500a50360b040c6d5440d02c50700312058 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 264329883 1250 264328633 264328651
    0xc070f05040b06090d15110c060105100503010b030c090a05100c0317090c040f02070210050a0906090f05040c0311031509010506040503030909100e040f060506010905222003100806 79
    0x20889035407621b4000840e2003c4110116807644d0240130440c0c4d408001c0c15001d16000003070012949031a08004484000300b03001c1083c0700c0300303000411941e40b035041034a910442c1c0e1008540e07102d0303003400042c00c40405600010ba00c40940c1001d059816441182440c89912030740390070060180d903031814880034000700c0d140602903012544c5910982080d4000c410b54810380340025041c24030030b50006c1d86e044900e084200011701c01149203100954811b03a014020507007420821091400c101040c001c5440d10b0180781d01450301c0e400003c10341c0d0f1180d401207039030380c400c944c4071510b90601e01898205209540350a91013090b008001040d54070b0f08000300c2c0e0440318005c1c000c5d4030304101c0800384451a50000e007500081e409004001a109104500b1144154410610340410044500e4003c003201c0014004a04014004006006940f5854000c5227002800b050100e003034509218110701404206556030600c00101440a0071084100041c50150040e80401405642c0747e08580340e40b40300c100c1d19590 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 264331133 1250 264329883 264329899
    0x2070506030c03160c051f09060204060327020108010e060105130b0d0e0708030403020d080705190303050a0504110108100b16021017040803061c030905030d090620030c070f05040b0609 81
    0x4494040c007036100c0507041c0307010008a80f13964235031104070880c1c00a81c06240880d4841c01940c420031030b022030b00c601d00122204600c2a114103500000c0000702d0500441000422000126155a0080b020766034022480c94007041641e0312078001d09580d030408801c0103412410034030310f100e03207a001082103030070790b400c00e0000e6042c42d10715020045980942002610601000c002500c0891320a0001c1a0304c0044080e08001c0012286002001c4035070051107001401d00e4513051000007585c00c90040c080d034100340b034980981e84a0350f11220b002c00180d40050040600024000006c0f42181105010035008907030300c40b02103181c0e08050340c00c0005d03200e00c8800e110460000800003010360000c1e641100700039100100d400d48180322014004580d14054021552014041140345420040103100059030325010981503c4c05e04041c18152840c0d100c290620160248079851403001c0050300e8203600b49008442d00180d40318080383c07036403025006032800350303083c0194110b5a080c48421600000c4000d04029 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 264332383 1250 264331133 264331153
    0xb070c170703050c0f0102181f0c051c1e051e0a0903120c140c010c060b0d08070f060b030a080d0b0d17090102010f050408160302070506030c03160c05 66
    0x90101d51000030100c082c80020300c61200380c0d000030084c8070118a001c80c00103075550703006910240c145140311102442054500958818403201c03403800c001c01d41d041d0400c0c008042d40c6103030035030400342410f5000b05c40980c1004c26a812503801345a407201c47c680c42d21413008188400c28216400d00c1405503440451001c04421103400d81c0d4032000f41043e010516181400e507407665120340c107420413101341c0c10005800c184003000b44019141c40342880c0c030b8280b00405020072400c0010303000e960010405040550b44107201802610781c0442101210342c440880da5444002d85031081d801e207084a0f00756000d5140c0b104010044c100007a501c11480e4200c9406070426150100d80009006c281040d150400501100c1c04001000c41c0c144404444400074141c1d154900c0600090071603048820041c4c40c1428a030502c000700300310004451203c082800b00c44060952401c040e403618115601070741e0842000000c000c07003203403501d006c0c41c00f07182c00401003440c8441208040724411000503001c0c0c603503005984c0f80c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 264333633 1250 264332383 264332423
    0x2013050906031926030a06031a01030b0a09020604031a10090b01020309090403020f010507022a1e010504080f070f15080a0f0b030307050f010513050a020d0f0501020d090b070c 77
    0x8441042c03c81c0b00d079214040403166411413076003081d00c0c0e056000d500c0b1a410b008001c002e24605000125001d40a412989503450300c0200201c05405480990340c2e80f003e281c19500c0d0502140c0186800842640c0058888040851003460803a600801800b203640045840986409490b6006805038021030030300302d107001000500d45005d4400c03004e5120b941c1c2071490842e0207010b0786200d20320613006070030000e00c55400314002e00d411070401c810002590300e503a00c0580c1c40c255050b86191600c00210f40341c903000c3c0010f85c0d8078407541d0003400e0548140031840071040030028049041e6032440c0c0e07400c42d040d50b0350aa5480c25070303145c100071710214241500068120040768801222000a0310000c81c0c240c1c0400c010909560100d0000d4480e82c11191400c03230002024055240c11000040e4034039503800154031465250102c0c8e00d0000c1c85000200d81403018440007031a003110700c9070010021540c440b4219480d100030b21104404a4030030440000288201c1d01418046103415002044061060f00400d02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 264334883 1250 264333633 264333653
    0x5090403170a020c012a110718091505011805160f02120a02070e131a0601021f090b06040c0512100e0c0414030a030e0420130509060319 60
    0x25038002d20f60300303010403078288400f4050741c02c0c07000c0614403003a5044031000380a03110300ca08080072400e01c16009050101000300154483c115508a5101011203141300d02400182c40c0d004c2000c6d10b2910000300035a140911a03109034104c032048403070194010305001d00401641d5081302c50103461043c420700050018000d0b100714403c1b10080c03043c0d42500e400312031340b074049400c04030303240005900200f4180181103c00688a800480005543c100001c81c0c0e034410781013100b1003c0040107401c3c2c00740441ca40345d0081000c0c008002c411b072041a283d50104141c03000078580b040040d11035140c070a020074400d0905200d8074106065503641d00e1705c9d200d140104c001020304040e2450040c0c0d141c0c000c0008800d40c032198214020040303502607507030721803800c01a50032881d03280107020700c250490b94103100000d1700322584c02e41490050b42d01244042009450742800c502c0c0c0c500c070514040f0700150f0a6000b915003503481094a074100c1c0c940d1101d0b10f5810500d92756800b03490003c4404858040640049844108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 264336133 1250 264334883 264334891
    0x160501052d0f0909090610150504091d1b1f051e040510050408070603050718030302010c0210110301030b040206070804030309030c0e040b010923010b130509040317 72
    0x1598551540c440e244501095000d004611041c020101d0f511505161540185412460001c010100c500700020303226003c000030b00c91414803000f03a21403e00c015010b14280c400501c03505604110398000c1043d180700b100c0210001d2006800340b407a0300c84d0741b000c14031a203e500e488041d200c480450015590629426400640d07102070020500c20607042d4010107480007400d42e480ca000948542c540002c3c07100300310038042080d082c04024407051094240004075202280e00d03c0c41e01050f99100c0510541721100324411240114041450200c18907405404c925050a01a821180700b2101c18003118200c1d14002c0d050260000300f08010400b0829507507a894100380000c1c55185010456030b02c89503e0743c89a8811004a45100001c2041c0b01034408a080201407410039211a0320b090f03514000a1407050151175002a592282d0b5020700000c54100006d980040f07010007510350f11094440d205400c5280c00942c181e2207060302150b141050031000d409035505844000b513030840ca00002d40745c1d0100070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 264337383 1250 264336133 264336187
    0x8010b0c01060803030c19080c030408030411030307050115050103060807030f300807050f22050d03020606030f0d020a11010c0c0b27010f0810080106080d0216050105 73
    0xc03c81c03101c180025402651480c00b84c558070040c60000718003000c140720410b410f010307401c070802c580398000508483d03101d0392083d10b05940e6510792a0850050034113030380c6039400d8480071078000308010055110b1416600c401160b5080d20790f442c40114162140c0303002d03507540e07030f003080d10104000358010603d044114810140c6825098110000b5205d44080d2520405840910500400c00a8014250302d40104403850300703602e0000ca100d87e14105204000042a2000d42030118845440201051401404009010103841e20305401e00954508081c2d072510710a004251048a00c110002002e500307040c91034001e0038400005403500c0c83c40d03a401c0c031442c0d4103014480e2858000900301c2814074000c1c0c442c00c40304580b03175900d140d000c801800a00c0004041320b041c0c000ca400c009d81c1c0204070024402c825280c440717000d51791030f40d1221450846d03503c4000d41e0743c01e080d00420780e210042403449203003060341e0803100c820161490000e1480854814203011840410459007910140e40328000b40c08199 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 264338633 1250 264337383 264337391
    0x4061103090616060b01031104120203010f110c01060f0302090f07020307060c030609180809060d0207050703030e1513150c02130f0b0301020306030d0302030402181603051608010b0c01 81
    0xc0c0041003065201d942c040ca4420403c0d5003d00411496108007101c0c41403e2178200401811541c41031101c0c0b02c1c1d4091100c442002d106030303104540e425081881c181082d10030501c1051006990308507660462a03002c1c08550a226012462940d02c6030030900b01d90b001803000c051a110b140c20110607c8001c1c04a41c03c6000400540c030100f8424040c120140c0069135000604600c0c08090000312206401007901b0141031808032000302c0d0070034050b583d0701601128400e44c0d0b40c0c1c85050100080c1f0074008000d103240540361001007810b40003812084409429140441d07441741c60741da4002c2e103202d0501400d03040c640c005800e2040c03410b41c003680c071481905810181403c2180350005003840480703d0f21014455101c41100c00204110700918504d20b05c142c00a500f18204200082c1d00c2c0d002e25216403080560100010b0190350340d00000c4c80340c1040d1410480e41d03a0030310303904081002c0700c0301e104180480d04040200d9100700d81038000b0b680010513a5103130040d036400c0c0f540d00011540505400ca14540d29 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 264339883 1250 264338633 264338647
    0x60705071b0308041d1306050618010306021b030f0406030b0f2e0c02090f0703061503060305060c18010c05161e05010e030a11030118030e090610020304061103 70
    0x141c107014001841c05a0f215070703180c2d072410070241e404043c2100b49402594012061010807000c0c429050f580e66480000030034542e0703555000c6403240b034941d40c0d030180c10184a4000018400c03aa8000c01c4900320708498644480210f8074529524440c210701082c0110080208001c0710307100303521080c484540200400314200d01800014100d00202403403030076406000d044d0304040c42222000c4190101c2a040205c00b8001076000034106070801840c211a000180002600d018480d9002c803000d003a1503800240c02c0f440405c03005009242d5400111094801c803030200b0006619001a00e50b006554041d444035285008011a0300100610084a461203440030008428500055500103807a120307100110241084001400100c03451380240d060001d120a084480c2c0c4010942da0a6a50018480046102c8030f002180c01821300c603000300010810141000101a80104c44401640302200d400b2141d13101c00c010080813010b04410b40c0090381c001c1208010702d80c02400080160341c0000181d80c10b1000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 264341133 1250 264339883 264339923
    0x11e030204020d021215130b030703080f1201091424100e03070909032304080304060503070339110a24021305150c010f0f06050f0306070507 62
    0x3042c40c20a04641d004184051030360520051190f001b0044481002e106803000003041c1200721080e4011041602c1d00107104a6840400c840d400446d405a4a5580c0c0c7d8a016940c4000fa0050002c0300002c0c080400000340d4036000e40a054280d00e06008640311540ba0f801c0f52049110880249064013204e03582c11102999940900c3c400d45ca5058940c41c41413481082014101b03d1540c00400c003061422101c4008254400d0023206145607030b05031059201e185030f41240d258000c1f0380c0802c0c0d0a2000040205502ea03101000d94015682030700c0910541085a0701b07840404031a650301a403694034805400201c000d6031014104801d40c030b0521104408103010054280013044c0d4050752000c009180d4041e000500b007040c0c0f0315010140c4411424034101d660000884541803080c14031502c0e841e0141002d0058240c02c8400902d00d0340003c104d031080d00e08952001d048115107500010745001c038000b6040c00d000c01828490708c2d00401503e0b696031021800e403942d4100c040203481d0380f014a0a48100340c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 264342383 1250 264341133 264341137
    0xa020901080d2a02040b031c03021c09052d06250207080a1101140d09050c19050925020a0b16050733021917011e03020402 54
    0x29065000e000500035280303014000407411410400000f00c104810540702c0c1a44018084803581241c0101d82c8524481c0060302d410882d0310b076a45a0500c01c8990502d25400d5402403161200382c002e020b0f060035601c2e210004803840c440004e489604661109880b81800403c103110b40c048038a042c2c05840d03101c02d40c4501c1d240301101c1040c003c00c07501c4d001c0c100d100401103900b00d007604540300424100e82044180d50700c1c0d54003510300404141c0300150781c1c5510303802012007140d800c800f154030544541a06c4598805843e02d0740040e16940500d40759800c0300c0c144080ca404280d6a0340140c901014642024403110010051080c0e640303142c07459898020030011418010f07015020b50040034481014200041c1c50500601150310700014196201d0619404c00150794400390850000c00007104150581c08001244134190041088100d031003c0460030a40d000e006964041103122441005102050f00c6002441c10000c0c540c041e4100100050a100d500e000c0c2d081c2d00343e000412129030349501103011b03a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 264343633 1250 264342383 264342389
    0x209040b0604061a030109060b0708040b0703022a010f08011508040f0204021201181518061a04060305090c1c17030a020301031b0b030606070f080a0201023f0601020a020901 76
    0x113410000c010890814a8042c1d20040d00720714070214a09078041c0c0d5110b01a00c01c1d8401c2035441c11012801c401458001e11004c240c00a9641c0440c02c81d000400344042d0071020318140d917000c95048400c0f201042d10491206050f15080190307409070b274171008000d0759817803401082101c60844152000300161203d0010b0f0114003c1c1e15003070000381d41841503040e1f0b810008250b51780b100f40742c020f4400109100c0000700044819007920340d422015104030b0f2a025001640100d940181c00c01201c03c980c6410100820441e6003c1d94100415294109a20348074024801660741c0035810080c180000200d40c580c800149105030040902c05482000560325074004554450304c43c3d034007200410611640c6e1143c1c40046140f03191710505282805024000ca000c003508003805074401103000010402124450f203a00c42c0c00c01c45007a260383e907104000b0b0107235005100000045100502800c256400c0760b14400d0800070314540c0d100b16001c01d104401510700010303c19070440c458804001c0258841d030010a0203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 264344883 1250 264343633 264343679
    0x206060d0507031a01150c0305040311060d15080f03040e0f180601060f0e0904020a0306051909080c16180f180303060f0803160b060103060b0c01090203190209040b060406 75
    0x558075210546c013250308076002070818442e203200303441c000035409411a400c2e66405030781c9040c030140704804154a8050181007030388140c0351000c407080f01c04180754810101e81c0d55104803561480142c101a0301d0340120311407044001445804102c0416003502010b9202014041180308044a4102603262520a074020004507000b60803c6400c50ba02036481c600143c01551941c010b410290b004c520382003610701c0007500b140c0d034078800b040809130840c2904c0514a605030b01440030900d2814104010f501407510010f0601c10b0520903110409080300400440d61601701140c001195148100d01900800103c1c1d8a005e0791100701180344074941c00d01c0c1e4051030107650009445820714003140002c0300c0c981c1003000694024485182c10103096120380d07111980c045d94240b11921980e00580c090701258011420000c000304140000b10b0b015806206454000c90881396995107990001400c3c42220f5000307504070391050006000b0407007500c1403079040400a04001527007070f52401440b942080350041400707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 264346133 1250 264344883 264344933
    0xb0d0b13120e010e010327020a0b0c0c1201090201050a0e0301140f04030206090111070609110a0b030f0c0403021e031524030d0c0b040c0315020a1b030206060d050703 73
    0x20482d684140c2e5008461406e003820002c5100282d61150381001c1716080360711034000928114115114404408001c0200d55207968803400200100e64070380d46803494041c0600401480140480014058000780c00d4040e15401c3c50700c060983e0468900d59842034a540540d26282d1400ca8042c41c90f0f40079102d000344000441e000e090a10f402820b00f040a407290034a070f81001482c80b40c080007101240c070b01680c46900084e03100603520700040c1494a901d0700315071220050900091140c1c3c0c280044d4400c807503070724280381c00760f9498071024220300540c00040e4005030080708160851649220340c240341000103080f980a800d01503440e00c00d509080342e0800301a07011066100c184c039620440310302e006408501038582058010001003030120a55009011164010040b4080c80b5164040c0e81c05190004554801d004003104100c1c0a035001c0060350000071120002c2071103603400d01240c1c414956041d400b618054403900300300309101c48070038429199401801c0e40080091141d4600031068415000107407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 264347383 1250 264346133 264346157
    0xf0b01060f1b02010801051c06060b03010302030706110d050d0227040f09050606040915051e01290c030f0c07060305010509250302040b0d06030c090b0d0b1312 70
    0x240745030400303440c1101d08100b001c00000142c0e081009107055500a5951080c4054140554000411202400360040e451f2520211b04403002000550503240283d0454142d50b6440c0c1007281c100c41c0340a138290b92a040401c2c1c0102c010300c143c00824142c120240e0142c00e0425400c2c41e80c1e807603101607021b20b000310142c034040140c50500b40510746050014601c100700e41d41103174660a0711108004c1101d481680d031210350004002121020003c1062604410402032400d50410007010b0341046500680341c04e2080001480028039800400c450f03070400c00000c002c107403101f55511039000b004007425a800188440c81c401840c00d005400d001c0350002c0140300003403030907070050221130060304002c0c040c404180800010000d951880103601045c1c00000800c240003240480c000d00960b00050ba07240d40004103000103060542080d4180c0740584c40e032040b816918182d10007114070745655540c000148901c5d00001c18070401da410b500c00043d140340100c401541e40c5481004400d56581030202d04860303611 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 264348633 1250 264347383 264347387
    0x52d0f030d081009060807050411070c0627211e0b040215090108151909090506070e1305060d0803010308030412050a17070207030b010f0603050a060509070503040f0b01060f 76
    0x150041c13146000400c012400e00c01d2103a20b8140e280070b203500a43e103a085001800c0c00c864100e1358125042410101990703180d100050291003a0114014076190910301c840607059021007180494840c800c0d11581c0503044400c41b408540a0801580c01c030303401c0e5003000d00a40000340a40c40d071600c0740c9003503031440c42c007072040112000c19012441c0700b00e80c081c014a5813690b040f000b09904070103180c114a41141d1040001107441c0051100940307c0d2005e0000003440e900c10f42c1041d00070034030550541f0704581d40d243c1c04580761300e82d242c620b80d8070044449040740d05c01850b901081e0405405408210350030407a0b01c542100d903000380d01c01c0b10713915000010030041c004c01d1820450200f0141c54a0b9250001c02e0788000c11030f04040c01d03401c08500e0f01c58003003070282d402000300720002c50740107140c1d603011740e5a41c0120550107400e10907400864140ba00003600c035140c078481c00d01a518000c0c1a48910b4a0340c9a08940a400052049440407030461003440407507410380c2c2c0b02d4000c054035603c0c03541c420090600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 264349883 1250 264348633 264348661
    0xe0a0e06090c04060905090a0312020705010606110f15010b0a05090607050706090605070f0204230a0606030e061308092205060f0603100603020a120501030c03020a052d0f030d08 78
    0x109038401846c00d014040142c03004103010303042e01c0d050b18040590340c4d2a0304061000b881110740c000c0641d86040c2c1d00098440d003201c80031115070b510b4029a0309104c14840301a03140c3d0900106081c0d030504290040c4000d402c00005840c01c0d03c00c0d858094104903030725000c02e03400e03031020b4401e0b100b650102c202001050340c0132480c1c20260000303140c070904024050b51042e28403d02c1c01002445a911580c02c1451070400c2c08440080c2080d0903001210f5041c0009034070018401c0740030703400007c2d04000780c00780c8071200002c4a90044a2004140b03507000e009495103480c5030401c01c80e66600044e2075414110100c4400c0504c4c54a00202c0000107580c10316900b00f011030f0014010080c012842403003001106281c803000c100803100b25090243c0d03600d260307420484107408041e201e41104c524050020013404420226102030b644240c413003c2c0116100d0080280c076035400344032404611070020180c510007c0800240b0349201d00a040d030a80d0318001070001e41070250a041d0840010700c00010000100c4078986 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 264351133 1250 264349883 264349889
    0x405030d020d020a0f060906020703200d020309040507140403030201050a061211040e1204080c0a0605121b0906030c190311180a03120906080c0a090e0a0e06090c0406 73
    0xd00e102c100d0300001940b01d0440d8103000c0c0080e401a130540c2d0034028103030032070070060342c3c014800c664540d598030b0060480074003214100240000c00c64440444080041c149a180300c13550019030801e002907041001820001b000c1c4020032100c403072605a048480350150003d076200e900003240a1070244420f4085070b20603808260001d49400c4010041500c02ca541e00d101c10042d2000f1684107000c214583c908030740c1e400c1c040080c4ea030004000403030903408689041003810403a400b08100350b882d80f049840303004409000d80382411fa1404a06003602c4011607016966400f5100c0d4109030240000540a810898081100050002e0369010b50208551006852607032400c0420a000d000e40319000180204468140a0101041e040b1902e0307070b41d4002e00d0011170744103c0901c2d030b40e01e40350340c01409400c1d030384500c0010a118101060404d8244810b580f40295103948110505150850f00112030401074480ca190300c1d903e000d000f90b007c0b428041c007445000c0c00b030001c02541e043c660030300044902d00d0f4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 264352383 1250 264351133 264351137
    0x90105060f060703030e120c0705040509060c16050c15030105040c0807020318040b0604080304030302190807060c03240501120e0304260a0506040204141302060a0c050703080405030d 80
    0x9080c41180341e9441081d070704500e4242c40e0002d0303111040c601c640d14041f4105800c001055001c81e0303200e6181c00c00030300c510076a10199410700c900d4480201d010354170001078543d0390a8034024400303001c041c0202c4681c56001c0c0d018504998102031044042040d101c1c94100d255060400000184600e05003800f80011001c041e1620502901d030101001b0b4880c01140a101810218140c030700a441d56150804121302c0c1004001668403541c0d90000781e9242e205100407409409005a44c10054140245410196401400682c0341c00e0059841c0801450748003298028035a56000e404030014100c507e801007080707048080c4050904050025240080d40c0f2428181c00342000907505403050701006071021507a1080100108011820014104042c2003150422500c12010710f01c00740302000440a008500079101002034604a0003011400c2200322440526100e07890301600041c10034034000e1900d02d00b1860089100095070362640e00701000c42c0e1040e1001c07103011a051200707140500c04031031703480c0041c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 264353633 1250 264352383 264352399
    0x30f1802090403120603050f010903030c0801120303050a2903011d100b120d02010506090c070807030c020103060f0b091201020304030c08031b0c0f070e10030204091a040b09010506 79
    0x2a400241e034400700500c001d04011000f0310b40789803c1c1058020901555020060316001d03403803030070450b0080c1391140066000a0500b2925905140650240c42c10780d0300340c2c05101110815924203402825015003155442651503e85c825401c1000c01c0394260440d02e592642543e1070b8541c2007509403681140a8014205050384903c41c1581c00680034011507002d007008560750b000c0d42d002907000640c1130321b10b4083d4000c0300c00340030360f081d41035004502c210412200044a6258400901d4140c001c148001700101c0040010102090040c0c00c0140e805205140114815894120a14070700c02650300480c80c035007000c50940741502d00b0807183c80d9410785600c0210300b9880c090301c0c01800481c2e50030000e0041d280020124010300001c02005400d601e03003040d05551400200d5a0580d0b61a00f0321456020b4001d00d080495a0f142d0ba2074000d00681c9000701074481c0340c0c159000c02004000864080f2007000c21051030030103041d21002054800c034058441842d00703145c140b11490940e0b0005011501c500c0348 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 264354883 1250 264353633 264353681
    0x7030f06090506130b03030d0c0f1103040506041707051309050c09060901032009010e060f0904080f160b01080309010810060c0b0408090d050319050301050d060c050415030f 76
    0x6802c0600d00004c0c0021020400010a0010070300703507c00d500004214600700b44140f00240e410a0348030146088940c0c4620132a880c5c030b01e0094881c0101c0c0078060340000100010008803184048000c00c542c920302c01d03542000d54480c0003411403004000d140111644851908050020a102d24082d1102c151060862840c003030000650280b0305000003800301c2002510340c501c80c1d489600007900d0700300c0603060407030f5561104010044244211025485112240a185001d0400d0920385000b2075100c2401408d012082c0c0e2a1030098005c94001030300700da050580400802e0004110354000c083c1103004e1960713684540001401c412004222005e0813105000c1000348a610495a081c9590417180d030160b141c4441c0f03803c03160b91052100701135200352604000014800c0100c0100043e81180d114202a000d100c4002e4400340000d01c200ca50011000e9182000309405400a01c014001031910b5450903840d410703424610380b0060503a070001b03913a440c0c1d0520b80890301d102c0d2407003900d4074031208400018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 264356133 1250 264354883 264354889
    0x101d0306160c1b08010203060405010b13090c0c0510021207090303020706030203070c05430e040804031202010902010207050604030206031f09020c0c0f0d0804171507030f06090506 79
    0x248010031400300020019090140300c52080d22000c01c0242c0340400c40f8441c0d031121000c0c040d4206482591180d880c3c0b400001d11100c20108035040c007042180d0503110319240ca8511401442c1942d0000107000c140c0a601002910500000d08441200d403001600ca00150150b202081d600915140500c81500c0040c00032036000a0320204581861802580d25565004101c4040584481c000c0440c841e549200341981c500e04510202004c211440f06500c056031310150301c062025000071140c16511003014040000c028000d158400d010701d2441e4030300b80e0361b80e1343c0c9801203101660071001030f59926540705c1150f90510041008040031210141000d0a40d000120b0501c0060102180142440d003c07050312000082c00e100207100b1024115201c0703101c1c403d4107460f12442c50145100e0214540c81081502d01a0058400325821150705400c050912141082c580e1031071034588007a12840d0551076000e210032050302c0c42034403981d0b03010400141d020030100c1039500a80181079918101020056162 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 264357383 1250 264356133 264356161
    0x60c08040311060906120412030612031d1809070b03100501050c01090501050c0912010c020a0b0a0b220e010c08070e0127030c0605040803070803090c101d0306 70
    0xe4100521500303190042d40020140d2003500c180a40200021440d15080080f0040140c07082e401107025420111000c0030032001ca500500518184480403280400440d219070100610031744814103200e0070300c00c03e4001402000a00b14240740c0000c1103020458600d100388043c900400b45007044a0942c102190b128002085500a01d410090b002c0341c041b040d900c09400035075400e504000200803178201210406041c1c2d01c159a1030307003d00111010780040743c405126109040e030441c3e0140600c2d403802d64526032500030192020032115210780070b000055503071000700d405052920b0b02030381c400c030742d80990241650013600c50354070264940b10b10440b1154001c8041640f2003a98584100406140c800503952003680300080101804104210b5107961040043e403000c0e60f0042000d40c8030656694400c8402d40b0890044c2d030b0303441d0000d01010b400602000083c5811a0101c400c1d20419003c0802054a080c1c810f02c8800002c3c410340c2c240c206c1421501d0b200d2080c40c00540c0a045140f42481443c4258 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 264358633 1250 264357383 264357389
    0x21015030c30110a03050f0706170105010e0604082b170712110d09051203100509040206120405010b120a26040807120510050105180703020409111201060c0804 70
    0x10034048403404200050100a0701c43c101006040310740a68407418043da491a80c0c2c50340b041244a00c0c00e0100b92280030b0781c90304c00f00c1d240f40e07540c04025a09144c01120811000701201d50004414440411406418080300100010707589205090018081240c220280c1820030001480303200074405010b8541811550390041290512081c2c208a0504140080221101050414a003c90280e2842509400c0780e490f0600078000c540820740c0c2880520f41b544001c0c0e4403109884200700040000b814048a0507a02c0f5000820480c01d00e5650001841990801c481c21900341c1d40d10070035070240b4a400c800044082d0f64040060920300030540c3c0b04644090142c0410301644000e0300704100342c0050360704803000b409031131069444880e03849400000448a410003102c007805590903030040c01545120301c42c12100c008100c0300d84c0500303a0301052121040980b1160070940c08010104074800035010700320900303101c070038615968180c1ca90715801c00700307040e0414030811071411401030204003107005940503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 264359883 1250 264358633 264358709
    0x1112b0b060d0504230f0d09061209050a0f0b06010908010209010905010e0a03061404120503220f020a14090906070c02120a21030e07060f030c021015030c 68
    0x2044d00d0314107064120444104200b5042d83d00e41030882800070001c45c0c10303080d003090101100c0440e03008410940f403440050143c0c10004010101a031090700c00d41e045642602e005030300352002c4240a4645003401e0020740003d40713481203000c0500049584c001c4c400b400070100540218200062200020048021442401c0c10025191543c682030369810113100d004582c8104200840c48144205c2403802d01d04035810b4038082d681103010308600e40a03000303ca1140f203440800e04440d1810581c43c00c410b0003000b130107880c0f80302c0030b00300000143c40b030800100c00740c12940728004543c2001030410060307002c010945040c5030486401c0c0030f0070710303001841c610f401941101c22584007026861464a0258561000307440078110041c0010312041402c000400070545990520400c2e1601e103455955402c03d20508001401345040200d0b8603102e03500000d00202c1d03070701c19286050401c0d00440181c40702c866001160351910305042082024294010b8010300d10840030408074001c5e4500d020814004401d9020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 264361133 1250 264359883 264359891
    0x8090c031c12180b010501080c0307020606061c050c03150d0c090e030c1f05090f070e19050c0c010b15070609081606060302010815150a0201112b0b060d 67
    0x2058500ba40046054492849a901015203142803410204000b072107218003042049010542101100080300e2180351960010403042d103c41c2e0600110754010294078071134840c08681d000c5000f5480c01654002d0503090700441e00c0381092100d181200007054000341c410611066080000340c00014400122140c00740001201904251000e0461184404000c0745004a0314560503820010402d007055500e003140422244d5241007480e40d8503040b0b024009190fa20000c2e041080b17002c0740e05440c0d8040c032001141d200c4208031511314402d4403026a4403000005001c500c0541d113240902c224100c0010407a1281548080c400b0350550314850848054a401c2e2141340c244c041c4403071138044600480c519181800c03100814203125008214500089000548420101c1d500b5035440c4040215464024181510b50340310035800d054540c0070310001c50a42d501d50144d00410300c17000020301507901103000007111030080a203041c510380c0085040090603503d400e00c4000d668603007000344e454480407200001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 264362383 1250 264361133 264361157
    0x100305100f140c040e060a0302030c0405040809120a06050a021e0904151403010c0306140f0414090607021002030717041119080106080f0d0c08090a030308090c031c 72
    0x1030261420303121400c0415949024004100309210041045840804400308a9151b102c200054800144006945a440304401c1001454290b201c075410030f100d02c0c842403070022070402060a00c4c3c0c0d00b042529180d0412aa4001480307560b00401b540081203100440c9084407044544e0140714403003410307541d40131001c00c05206686980d03020fc0b600c09039003013212813130907a603c1106035044e0680c04000d0095080c060034240c114007a0192200b03441620b4904a014150002071117040203020030318990190700e5103110a00400c55403001c2d07000c0d40c0003001074080c44c54a600b001c1d2400e480900e00700d030030920400401c03503400d030321a401203202002d124842e07034035881e1418400c22040c001e612480c0d10000b0300b4900ca0034a84071600c00d10071180b0f036100901203150350b4003205450701105000030180d03401040200c0c000d903100e6040d091110b4401c107a002d040c1071041011920000b001c0d00103c01184c2c00c1420320130002d404100e414036495040b0010400300744031003441e40c1c5400c40411128180500e0389030325 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 264363633 1250 264362383 264362411
    0x100b0a03110f1c09030905040209062104020108010e0601080f07030e0f0d09080601050603040b040c0b0c0c090609091c230a0f080c071502161a10030510 67
    0x48800321440344055a150001824040e40c1680b14040007140c010191481c000000d11502031003020720303050b1b1a4009013500d008148000b070751056858a40c004801c011660640741c3c0d200c0c00904071200301001442615091001524600041e000000e4511001041040580e031000f02e49510010198003402c603600c0b00d103800d83c090403d490306041e86004400c415861148001040071907031100369101d401c910b81d100b4003140c5940b020301a11f500b0000400c0051f02140d031400c036860f000f512078130304801502d0341c96840300c6042c0c000031180310703083c3c1120304080010702d404030007660450011280c42c01a410f05144641d50350b09002070509025151000818153740551008600c090144603407403104030845508440036400314240101050011000c9125980b14401c0c46106108007080d49203412501d80b6041d050104414442115a8003009410b000c001400183c1010034070400524010103200c0b100c038244070034028030074181e08000b074200704045100000d1240e4102960480011420041481 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 264364883 1250 264363633 264363641
    0x50604150c03110118051b01021903020c06040b04150806011e03060506040902120a0b0319082106030f1204260607180503120301031e050601121a100b0a03 68
    0xb46100f075520b0056044c14442041d6007414000c1e1103907041e54030761041409030201410000d050180180d0040990b00401001c81410410082c0240115150700c541341001400b41d0f40a500006044c610200301007000c0700c592140002d0500140c1010350341d61a144000806916184240d00807010075102c2100d0000c2c020f500100c003518000c1c1466540e45d4840204c680030f540301c1c15401c000078100c200014140c100610800c94440c000502400303580703080501c0b039501d0307030941d050558001c0c900300004100707905000428144101e140c103998000d49071980801d42000060508891035422108090343c1d9150500f08031015568807094416071803000079000c442105c003c4020855a1043e6024040c52580105504400c000241d512004481e203500605880d41e01e03c0e40980c082d108140300600000f00043c801c170149004510400210f81419151549031031802e911080030248150a01014021a0701c0c20045500c1410442115410f01c4107486604410310f2203050b80240002c9a46049513201ea04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 264366133 1250 264364883 264364907
    0x40603021314060307060507120207090203040c140a0302010e041d100b19030201020304090e01020d090b090114040203030a0806030f010c02010507110f07050616080d0b0109050604150c03 82
    0x303000100c02042444005041c032401911440300682c001814514000810f01d0564003147e0f82c0d203081800c155030700304030841703100710150a60162180102d41d203c203510195124500030340c5c80042651030548114032082d41e0340d24860059192400070310150341c000d030b100c014010081d900001c078203954561403002c1c4000503000300f502d0701504540d482c1c1d54800c0d82140404080444500502100032540380a03907008178070000340580c000384010000780640368003808000e100c10001501d4441500c4194084411815048540c0031484d01070044d00f190034422008050360008510425041c00d400007542e0380144074903a41000b00c404001081c07a00c050003c5400351500c6d0000307204809160780302034040d100840320301f00021212040044046030000300700078070814803405007030310908181c107000850303224400c1e06500f0140c0006a000290000008023040985c5400019040a5600004014041c0d55018510456051006015018010521001d894841d0074942d0040e6010724042e81c20340850a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 264367383 1250 264366133 264366139
    0x5071707110a0b0112120c0f020108100b032509060207230a09020a020606060a0806010c030e03070617010f0e0a090c050d030e1005161b0807080a050c0103050606071104060302 77
    0xa0000640034000c2c0121445c15440740805040744050300504590003416101c01400700380d03401c03c0d0344000d540910700300c5411920030324403035600b41e49079030000141c0c0c2e0050f500680c0543c403450002150485125400e80315064614015200c1450088000d42d115594040c3c0c038003c000074490485a07060610740c2d0030003850083c03d071220103075841171058001d401c80314198016001e8403000840700d28040044a8110080b40c81e00002922600700444807440c0032542101480300c031040041032583e0411441c1c0051240c0d6694a4000850b00c0d11200b0009069100750020000107201344a01d20302c140819500403490200020400c50034140074244403c00c0c0d000580202c20101010145984244444000c1c8004e41d058004560100e4003118180300c0d140031020035500e40f54803100042c0c1c3d40b603900340081801c8407185112a03101c00c141420003075594012805544404031010070040d0502c58585000d00c00d09003007201d031909002003402481003020040080861b000c840a01d0b6440764030002c0599005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 264368633 1250 264367383 264367403
    0x405180a080409060503070e010b0703111e01150806040b070e131406150412050c0303030906100e10092304030f03060e0114040e0f0610060305071707110a 68
    0x340c2010841503000c0d0050400031400c0000100c5c140c10002600c2003100c68090b10700549030700c0c04060900c81d800c110400c40802c28100030001100d58100b203520002c072a203071403c10075100d1070107115007120303089200300c401d0381ca45034410071003c3c0001c619140d1094100038401002d60791050212030100001c0e6015500030007024a020709000290b100c03c2034640741010300e03e80ca864490070002e410600b8041071180c03040c100b00901014010030850081300d0f00c6801194620120300340002e082d0341080314110402c0d0301801c04c11041016640424000341244503680c000d1742071240041600007600d01521444989440e50b1004591603856031002840d032501c120752180c00c19203001041c2c851085007003000607080c44804a543c0c0d0300c1c901994101d84030201c60b4051980700b4818080540950200e1090783d014100d2404001201440540c2c032511725030b807500ca411400d100c400b07001c5541c06042c01d02048000701c070450340030f544000491380140031810030b0407540041c461594500001854000c0c000401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 264369883 1250 264368633 264368653
    0xf020f010c0b0109060e0f100504020c01020f1207030c0f020a0308191d0c10051204020d12020601030203011104151206181b03090305040b070c0b0f09030601060914040518 75
    0x219a101d1020358800c0c06408696403554187c0b0001814103a51500c503401c10384c8802c10162030280c0c003c1c44200303244070000d824034001d030362610143d80052940020050580c001c004859606102d02042d0b0308950820000b02d411544000f5542d54000c40001d050140e4030020030003000030139001070b000e4a0751981c148240c5042104050060420f0290320400e4420803218543c0d901c0c2588030070400c0c040d2039940606000480320341c02c0e4480d201910a0340c019018042d50f502050300d040c1c4001300b03107240350000d00072545580b06060131541840c02440380c03500103000030b07c5a01000c001c0140d440700b0b1403030140041000d010740c0e0001003103d580130440310039400c112003250700190703040800810b00f60080994400864201907041c0d80c5102d00c0200018001c000030f02408002c0c0002d0140316018410300c2c3d50880c0c845d41d071100613a2113081e21000501000c05c3c2802c0ea860304120071405042c6038a45000c18515105689a40300500c11900d0301c60b54840c0e0000c1e85600b064000111081400c601b00c1c0d66600d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 264371133 1250 264369883 264369899
    0x60a090c0b0c100f02070506073002040f0602070303080703180209041410090c050d110622060905040524010c020102010917040303020f06060d030c15060b04140108040f020f010c0b01 80
    0x840540c080b01c490048c903000500310f6000b0401c0d0b040c0003040402c0621000e03000c00443c9000b030845542d00c0241d9038203001c046480011840c640000c3d010540003400030b0360960601401c0004010120030425040403008040c00341c0421192400c680d050791406600d03142c03440c244c1411060a40d4441c9a44a88a50007409a090b5000007804034080c0d5591100715441d0380c01d00c040586080c1028000440d4424241d1060504c04001c010030902e0504001026802d2180100c0c111110b9101c02c0020345444401d101d1440c0602c40c064000b0210940320045d0180303501c0c400a60b0080c031801c103044c4403d0500c16010341e4000c1d00184201c5500c0811103c014500da030f410401c40c0c005000581c014421290300d10004200000c05030b000c0d5030001c02001c520700d40d50f902100c02100a0320110b9074514074040c0c6004030041c03402403e0191508007074403500c1b1420a034180c0c090310340034483ea0341000400018030000c918000300c10320001341c0640302d03030440625200040e9581e5072020002000d01c1c1c400c10000a00c60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 264372383 1250 264371133 264371137
    0x50d0b090a06111305030105061f0c0c080304060e10020723040e1506010206040b0411040e030c1c0201020a08010902070c030206191b020f010c0c120f0203060a090c0b0c100f02 77
    0x301200c943c0130714940700c0082c9800c07100101e80e5140c00107a49801d2207545481401d1b481e00800da18581901c0d2100169a2443c903049254000d10306a44007041c24860310340c11548000c01d0a03810307500300501d0392503000d0080d03a8014a101e504c41043d000344082001c8008000c0310445100094018000200402c0c81c25507100b880c00a0641d20800a0b00400c03000e41c80030500d6400341d41c00501400040e111619240d00701d8008410507a07106a03a0404401c0100090001d13098294002e0042c29001c400407001d001200784605034081164030400401c803116400c4090641034583e540c00050703c03403019181104a400e10750700069800400403483c24581c3d560118048210ac41664442c210415040d00c5600e498640580081d03110070f0244082d4840d5214502d0742c0c07115800307201451a80d0f0744d507102010b8400125902550100f0402d10358005605003088126007101c0265401c000d40300050301c804254580c103005420b00340600050024030180200810210507601c0a420440b4144e543c0106000f5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 264373633 1250 264372383 264372397
    0xf04080a020f1804081804050f070206071e0c081b07090b0315040305090307091805071a0901051303080a0503060f040b09062e05030916050d0b090a0611 67
    0x6940c01d607401210500384030300c00f401800801a1600c0c065281e41d9542206600a820000c52410503d001c0084a070b80c1c1d401002e01a2000307959441b0203003016030b002030803c100103050106108911803d0f050030540034914203807145980c548048001802e16202d000ca1003141100d401c6244078400140514001042080440315210010088080b1f0030b8140342e12107649200c0d07441442004c1d00000c0100b4080c000811081d14024180d032101912400c00408403101c4007542c0030f5403d40712100c1c5081080030807004000e041c01c1445003100c084030400030021031050b103015038100b080208a040e180150201a41c002c0c560049d40b00b03403100c00d0404000c0c190340040395030f41e04c82e8485420862207400c1c03d100e10341d00d40c030026140c40d42c1555513038144083c0884865000c0854401c00030a40400b0350520500503000860b41e44050b030328109a641c2601e084203406d48150300c200c0c407500170440707669508501c0f5400c980c462400d980607500c90311414102410000c01500d41410301e0207829413403140000030100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 264374883 1250 264373633 264373639
    0xa02031207090506090103240f1406030603072c07120606080f07080606070b01090e010b0a080d0c030504050409050c01030e0d08010326070b04210c03030f020f04080a02 74
    0x56840303860803a1410100d10589402220401170908154031a401a02c152907203003100d58030700c030300d621080d690b076690320f034807516542078a148144400f00d00012001c0900400303c0c0ca030384c15030522000194a42070b50b4400d1840c02d070f504c5d000809140e690b40000c1603400078070b10041005458400e102510032007844011689283ca03000000c500b1a009102e0207008800072a26050b181c0e1720400c041c0c5d6a12400703400264009024000f24002035110902540640903038103010031402c081c103c195083d034180d004524030880803a8018808450005488407119080303150480103086a13080035030b00740c40707290091a0840e0503d01c40c1c030184400001e2034001c0c240282c0c1c0400525802d05880c82d1144030030301c1440d0000b03884500400100301e80c20041d0b505803900d002450041500b000000642e41c4c00008200c481d00704441c10441803002d441c0c2e41804000e10a03100450360002400c00601062510b08021309041d613031362500700c05d0500d13503050310072840804170700596503034036002800e0351682c6020040348 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 264376133 1250 264374883 264374917
    0x20d020901092007080901210905150114060f09042007050f01020a02100911030304170d030902090604021318020d06141c17030a0204030b0a0e0d0e0303070204020a0203 74
    0x800306502d01c0c00c81d11850f401c59032190070321a041c6c0c01146c0324400e400c2e00280c0040560040c02403c0c11030300c503407488580b048008125000001000c0c03c0f803910144d2103019440c03503080c40c0041507100c0c1c030101c070b2000e200c03003a2943d51440c1900000e0b000340320441c40f141109034084650351611000344014440d05020700e00715001c2d603102940381802e078400c034403030302005030441c590304d42d095001c5801c07001c19984541e46091140702060046032554205600451700c0205121001004410500a8022507201031905200c0580700c2e4020580c0c410000c5c2c0884d00407a4006003005000c03020b01044005080a00c0d11220134000b1204800040d4100f040c541c1001ca203412800290791110750881ca41c4c00308050890340d4401c04811582d07068581c00714081e02c0034134104003500604494480210300c101c580440041c1c4880c11810300b0795607980c0c010708240c1c002c1d10f040c03030500d4218000581d008041c0c0c8030b840c090305554000c4c804203095001c1c01000941003800403c120b00c805401201a04040270603801d062 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 264377383 1250 264376133 264376181
    0x90408070503071a130201090b130305010f051f06090e1909110f0f030a02010315120c0f0923061507051b10122a120c09051309020d02090109 62
    0x1011441d02c5d00303802408190345840c20004141c22002400c8210750291466801c0b5507241c40e2036081d524030b40c0b20740c504603965608000200599889500124900250b66104103081110143c42260540191100481d0384800102c40028450384842100134000381400102050f04d0840854420744070541c0c880c12501f08210910b0404e00c2204140302d100034006c03c08110a900190005c05542c1c0000c800e8060007400032544400640c00300d5911882000349070030f004c0c5007120131420501a0b400a4545a0420a508001d8440d4025480c4140e5020034240d29940710040001c00220043d42e055408440200f208003d1007000f0543d10a00046540c48074050200c4c0c4082001c0e0720000e800440104249240910760103040380c0c8500700300080203800680030000d141c1d0340c2c08411010580c42d0005120500c180258180901810a984500f4105043d901c0e00348030014034107504052003040010380c1c2d488000103555032003058810558000c2c3c14a6003d507110b0480e44007606000c0c0280c01e030814050400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 264378633 1250 264377383 264377401
    0x501080a030801050409030207080a0305070b071403070e011e05070b0906070c1401090b0a090c051203040501050904020906130e010e070909052503060501081501020705090408070503071a 82
    0x280c0c4146525036207019050782031404010003404e0404081d01140305112000c50044002c0200318551030098803a5a160403052400010624000f400d400801c80030216071020f200007281907a4000080f030508940412610004a40114144031192503015000b000c0381e004a400c40c00600c800e03070185030f8200103a40c0f081152661a0416200280042e0b00740c540d61020810710b000d8254007580120000c6501c5000b51100f0760360603815a401031260799204629000c00209070003540c02040b00351084180c94a007140c01c0e5445c3d02443c82180d042c450300203488540ca03981c5504030362154100030304847d01d0760031000032402d81d240580591100c40c854800003050f01009420098032507811591000040d5040105820140c071004c2d040c0c51440c02c40d50f405c00c030f01c008030b07807001110592182e500203041403070000010058007010b0044900107a0180088846990106010007910405e0701c000140342c4440c60301280e03074860300c880503090340000b00e80302c81000740c0c2d2038803d03106180c81c00000350207460b0440c0c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 264379883 1250 264378633 264378643
    0x141c09031109060a031b080304060f08180d050a090e041b0902071509030c0f030201020903070f0506121b07030518060c0c040b040213090c0f0203030c090f0d0222050108 74
    0x8954810b505400820000d8045c40140401c0e101128043d506e041d03584501030310b1074125800901c0401d000c0180200c20540c040c050b80d500411a0076468021294041640d446440c1c070368440040110000d040445140204c54410086c010003c12040d00d00d06410406000390540c08500000b00c0c1d010b500084c034542c02c0c000d549504d50040d05103220100c41443c180000d045610049080c40510814500072a164010800303000d4065000942e6900e1050304050030040103070410000c0e0480c8250a0010f900c41a00f6120b038040c485620120540b54000980501203044020b00031310007000440d0810154008040d0070060b195405000c1110016402c0100500030780ca00c0050035800007000038454509a0000800c10310050030052801c40718882d08110000c039030308070305c0c1401e444011805016600a604403581c070780741d10283d0700b54148681204010310552481030b00c550030750500d20040380e075100000903005500600008034000301c101141449000d0651028031540380a000140141b0045a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 264381133 1250 264379883 264379891
    0xf040f030b09011d1c0e060a090806280b150a0f020d0507030c060b011b1a0f0402010801060e06091e030106050a08150c070804080f06060f0904141c09031109 69
    0x409403808907000d268040325000c01060340002c12a5404a50545d515180c00605034941e041d45c60a5100c1d00b4801a02d14040c8007074114008401241c0d407650b803d952100d5a102e4007100c0580100f03214040303800056210ec060b6000b02d82060740000c008100e2a000b81c10303002d04407141d400341d4182113450442503c3c1c030701030403101401054903101030f200041c1a0f03031f005500b16081414000c100f1100b0708282da1040000e00300880d0112041e5690004a0b19030048095110400c0a4808401e1070241d000030080b440610480003844600c02c40c404d145e079940410740d502c800c0c02a1000368a20303615024400e026541118080c0254a80306010030b5a060120182c1c0c02d0302e280030003c0c41060700a25190340c501000904d000b50300c04040c0306400000d040040200000d0000500510000d408000100d0a00c0d00c007401e040d10034144425248059201c00c80382c1a031050300b00c01002400c0001c02c0e02d880c00c1c00a0034100480c21858a049908216040700c103070350135640075001c24030b075032014201841640d0b0010b43d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 264382383 1250 264381133 264381191
    0x81b0901050906130e011b080a0c0509190902030f010e100f0b18030a0501020702130501051003020a031b2f0c0603070c0501090b180d0e060f040f030b0901 68
    0x120006001d030504030321968803600783c2100010000c1100584a00315900c15500444401c003481456801f10f500c07010980c0c200d9698582007000c00d00a0b040075120748184140640108101e1a501210070000c100003401044203030019582d034607202c00000440c520074003d242c6105009008203e20344c0c140090b800507224008198a441414503080c401242c0200214116141c6040c148810984042c04880b03c42031041c1c00150b16250035204108143c0c0f136038186490762900d031a00400c030940d2070011030000d6103868280180e49503003191b42180901054480352029104400c800b0600e543d00000304009400804034015a104a09601000c1d5680c20076211103580d200604005240c036140d030096030400d04506000600042594816080d5050340000342c8040000504000d451012208008011178101c009003841c1400c211015101c0050400b51902621020841e040740c1c2110004507030140005403c0b5118066403840d02c8c000d500c00803038a4141550802402c4080455801d142003c002224 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 264383633 1250 264382383 264382399
    0x703140613060305120705120f040513022b0501080d09230d05030c1902060d0f0204050316081002030124020a060c020303060111030319090606030c081b090105 70
    0x20004009450181d4031980700115564000080000c401300520749000340e1054201d900e030007481c00e0050500343e41000740103500d001041030740050f2484c5400c44041d00c0d81100c01c00784000301e0a18940080c0925000c22a20083e0320601c6040040110700d00000f00141c00700c01c4c041a80c0751680a40c80b1051701c41000080307040d500301404809030b007240032030000c0403140d0b6001c01000b1800015440d048400d10646441d04000303082805000300b8031a400c48890f1307014103039401803441d5020031510b101d5142c0d41d4101a982e6131720394003401d580703404490040a00400300c40980c2280000d005555400348039092403403207042c1d040c0e81c00c2241d50007541e040340c9160f1451501d4040a090005802001c1da2a0000318003035516908001000c900c00c80600c81040d900542c2c823850401d0000d051884d00311104001030340140100591a04103440d0642591148003002c03074280614900f90000d40440d400003003180c0b492003400300f5a5880002d5821002e05420047d0312070002003030610107503142c203004072600b007045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 264384883 1250 264383633 264383641
    0x140c070312050408070b2a030c0d02070c03050106080a03140306030115060302090406240c03020a08070b0613150b0a020309090a020a080a050c0d0b180c0306040e0102090303071e05010207030305040b070314 90
    0xd00703022319404141a81901d141182403e5000101d81c81908200ca102c000e1031024818480240b040c0310103401803100500c80078400d0344000c2d00c80c0741160008100c0d03400000025505413020b41144201d502404d91540d0700d140c44850150203034104c020407d000302c1c0b0b4004000f44940c0ea1800b100ca010800c43c1c182041401c0114048895410590055040d88100300840c030015003480001d110342406451400d60368100241040300c4078849010300d00d40c40d82406190b2907200d20720b900e610226540284015529100d10009a0030340c02441c0c0c1845d40b004070320307080081070915900107080000e2280d9400d11a40c0d85c4040d400101c6138240c1c2c0180c5a200c0500c04400000c0c0641c1c007004c03014100030180032000d00303454005500d40d07004850001a01002205200d401d041a005030000c0c5480c10000f541849441030129507640280f440c00f428400b0310194401034104181c0340c1c0b1542d036402c0341c0255640c506504000d40074200940741201d21950340c40000c0ea03482c3c401d11802091006070400941c691301e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 264386133 1250 264384883 264384961
    0x50d021b0319030804050304030f0b04020a08010c0e010f0e04050a0e0d0504120312090f0609050105100e04020d0f151a2d030c120619140c070312050408070b 69
    0x5008004864a2108000100101d100802c039401e59501c032f180500241d10b0944144040220180d04c1128282c0c107107810300c8449034100c2d1412000c04820703e04202901140202240c901c070015484a402078500020f1200e0100d02d03402041810244800b2210520310100c0101e5041c4203900c513201641440b60071131400640300d007a8415106000e804085480402031b11502c50462241108444040e0780d40c07a0a0308000003030140c540c0c440c90480194044602d00300c101c0646e2440180000d11842e2401d4100b0200001800625400c54120441c0c40c1c0005603a41c51030b0042008980001191550b503070782c030643e49800000f8142d05514408892280c0d1403041c040032078251500310156040c0911058600c40751030b4105a00c10007020350005000d641811010144101c40c1503500325001411f0682e0500b070f00c0c10b000d01c0f554001104503145943c030601800c04032403c10b09010b0020762107041009201c28420550081d101c1c1600030b491041c0c21b5203c80c0c000031104400400101e0390014902c4209041d45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 264387383 1250 264386133 264386147
    0xf07030213110d0c050903070621020906070507080f070909120804050a05010515040f05130b090f0111030402010815150706090f06020301080f0a0209130f050d021b031903 75
    0x80780e41002c15042014981103a01a507000301c4c200d4000400201c0c2a80c2580340801200c1c000700090300f0700c3c0800c251103135403104840d010311000806072500002d2800c0c2c542c0f0790000b100c80880d0032100f600d841c5d940354900f05813501c00e41840008544a11703000450700d5001485524089079020024440c0c1200d1407105840361103008106031000c1c0102044070010a20a02680348500e0764000c123080c030140d201c0e04000403150100042c0149074a00b0042204003d0100203240d036039a00041403107200da880211040c40e1054103c0c62001c03650034100300d11080c04880010314022032003603d5a0b0030983c1c65418200211003007011013944000c00040c00c0c40844c29060042a880c0d000d041d011070742d0460ba84a82e01d0090000004680d101c0d4000010084c4040500541044040517809447c00880ca82c00007a0064070141503142c4200440e01003000b0090001c40713003146d280d401001d4446e013a9807a00041e44070030000d6151030b2100d4180d5500041d510f8041039600d00d012100c1c0525180d1051a2011a404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 264388489 1106 264387383 264387401
    0x1503020c070e1008010908040e16090b16050303161e0e0415090c0c1104230c1b01020405010212030403050d0506150c030c0f07030213 59
    0x19200109a4030304403040010701d20003e07141c990111003800070b2644010802e43ca011800e50410849a0103801110340382ca881603d599a0841c01d560f08082c04c40407070000403489001802080403286c00b40842070802080c20a407150241e407506d155a0060718013030076140842122070301066112510103c00035141101c520540401d420103400b6080e200d014600c901c0d200d11170b09007003030741b8003080d4001401040e006002c061490030020b005c200040b076003920703014031150f40400c032810240102421640329001e0709040300c10500d10800e102c0300203002821210003c10403c4040d00c07080301444c0c4641040310005070360b50300d000000381c0340c9002c500110803110428000c20000c40d81110903078404018503032001c104c564654001600d000030b1201d602400c00008202c00c0c40403603000028000740c0058201700c0e080040f00c1c4074829950070305844000d6000130300c1418001d0844481c0c01103020 = true := by decide +kernel

theorem cover : BRFrame.Cov 264208633 264388489 := by
  have h0 := BRFrame.cov_init 264208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 264208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 264208633 ≤ n) (h2 : n < 264388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
