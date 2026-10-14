-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3499
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:50:26.035798+00:00
-- url     : https://prove2.me/submissions/9f1ccdad-412d-4e8f-a546-fca46bea6f42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 629136690 ≤ n < 629316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 629137940 1250 629136690 629136707
    0xe070e0103180c0b0c01140406050f070809072d06050c010c17040813080307060c1b0c0e07111b0a050a030b04020402160f0302011a010f020709051506130303 69
    0x4034104101035030402d039641c50f00740c89481c055600c0300d00c070104040071001d07000d401c1344a440c203055000d4981d03410f0600703140000c2c4c070044401004d40880300740841c2d040c43c840e90342c40d842140703004050301801e41888602c05281d1600c248050090008094840381482c6085580c1c00502071a114980c1c2c800c0c500d0f40603030a443c948001e40c400d021b44e20b8140380071000100c00300c5900a40c0f003c49240d9a0080e800444114074a942103503500b844082052003c0003070300e81c05005020915251980f808105010049003002404c0d0010304840a8210800a91410007220354000b801030902541c4208038075841c0d85060000900d65450000000380c0c90a0b5046c00818603015003015501c20840c2e60640c0c907007609502000e08000d00032540000c041018841c1d4084401041d6400344d007002070624181402070103030101021100b48000e82d00c800c2e540c83c0d8010340060703240b04940c0d0094248645496400c50081c50006c1c852402075105804100700c55865200030003175a442c0b00040601c0900f9820000c0c039501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 629139190 1250 629137940 629137961
    0xb151830011a0d11040e0604030e03010f050606091912030210050c04150c061d030d140601090909020312041d01050d03080a180b1612060e0c0c070e070e0103 69
    0x82c00c0d81c5801c1866100c0940700e04030035410402c8101075078801c50100e0010264114200114002d507014441015402102c40c1300082c0c00720f00a00110300030b03203600011508103031032603540210100620201801c000b803101c0282045c6012103111150360b840301c0580d101402500f1401130f04078048040f441c4901e440350540003d15001c00c1070425041000002e440c0841910490900802044000401006802c000701c554012920b40c170018280c8a40250340c2d800000480c1c1905090500102c1c0c880c29a03070200e84100d10503035a40a0b182e01c6c1290340402000d5120003aa054020818040702100c40c110060008100c4002c0e203900074000d441032546070982c1a00300c0703440f5030380c02080750001c00d50000c6140d07041010b1000000e0b0100802d081d000b40000300500080603614521300704044004023416000492601d62501a100c0d40c0c20048841110303024041c40485450002c0400c4c2240100740c050121100703100304031807100f03031500356005c01c04030110303078480015480c1c1c6000251940e16000700409203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 629140440 1250 629139190 629139221
    0x105131d0127030806060705010209030307030903050f0105040b0613060e0f160908120f09040c050301080c01030501030b040f1a090105160c05070611030d05090109060b15183001 78
    0x266507001040f08101420b9141b04100103d0b8010030f00400794116065030100404403940c134480d030314019000e04407900c0161040e0007103c80c07000b13401c401030089a124980c4411105040d40e241004c10205203090707100a11116070b213013004111034000990190042410362400c40403460840400903241c00405034080820944007420072007803500040000d16101003a40407503c1e00d2001d01c1141c0640a45001e980d44142000f82540c1c9060708040194141d503d0300064600c02602e203401541603850a20008100c680014000380100e5094061125514481c100648111800b016541d02c588000d480c0300101c2d07550780c41403008842940c1d5198000d4801403d01203000a45520743d1030302d8030310503c5180140580d121268000700300030b00440300e500030b500d64100010300701034071682c0c0240021001181c0c060301d8003d00e4455894501e01440c00c4d400c44602c807918088809841d0a40d01076285510f0b900302c01050111009040e00c4903022503441c0040410000000559900c0360039980c1403130782144003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 629141690 1250 629140440 629140511
    0x3052b02120601020a03050a0509220e0d030b06040312020a0b0c09240d1113080c0901140d080715050103080a1d03151e091c02070b030105131d01 64
    0x90301f060175109094801d00302152249402000b050031420207401d40c00c0307203141d4010348414843d2180d102600740411581160349980c074154041d01120f448011196201c40140000c200140010024120030140d03032055460b08a016660a13111102c265943d0b1844400458124007a082540c0000d0013121300703178001e440400d20404400001e21a001d04130051b40e8813082c3e1a146075501d8001c4603100d07411a05501c40c4281d03074003240b5490314101d0702c489100c2d0017420b00004011b11810100d42c07000e14010210706451110f03690f10340391984070303000803034850380c81d110890b000d44042d05c1914000c60144a2503a034503d1504c1004203c00f10504c014801c803920403c0c0700306140c0f40007030180d074018650032501c20581c40e0350040a080c404c030010f4030a407440e0f4440400c801d620000c42c4020702c495008000e8001c031541d016050340c46183c41d004030b41120601f030004020b1b80c9000303004101408030076040000d400c9003070044d041c1090104141440c85a444501034604c200e40d8140c0d01c03480783d42c07001c40c8407034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 629142940 1250 629141690 629141693
    0xf031406010518040905160e060d08030c0d11040e010602251401030b0a090c021903080f0c0706090305090109050a03021c38090f0a03052b02120601020a 67
    0x214001c810710b0421101040215040d5515698445c031070054010007140c0802d001c09074083c1e20241c3d107000300701d651200d041c0807891a007041401d01d0031095005803070718210741e81e5082c41d04c1590000420a130016440b10945070b900d5040c0340080c406450260a07207070780c0b907040247c003030b14200d03240b0140c09000066800e071a40f1026401241d00035a2402034000f44100613000040b800f80224031025540001c0e50100000d050505501c04d003122000c82d0240c442c4800309100311030352040c0102018000c1021400041c0102e02c0d00c440c026405105480c065007040010380f101400c03100c20020441c0407890001e0b207484039603003281986c0c000700f400320f81c4a030000707041d07501042d02a21000740b41c10041c40340074180d2081000c4100b45092004d02126800716050440c2190813143c04030898940c50000c02c400801c47c0d110010035043c5074100000001e00304111aa40c04072515401072181c80209410a400500304804003104c0020b100309440c00541c407400889100c8120740d401618017070555115104140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 629144190 1250 629142940 629142947
    0x1208070e0d05100203131704080d02061504200334020a0f060209060f091804021e0316230306130b0912070f1101020705180405030d020403030f03140601 67
    0x81d143c141c1e0000581c80e5100e41c004011020321850008145803000c1140c4002a20010081d10031a11184c0480e21001204a01a03886042c1030300d0410050700c00c0c100c00c00450401c0c3d001400515001c02c40f038244000504c074000a150029602400400c040d0304c00641c28a88a182110740012200d1020000b1085814040c0d5108001e030320003000d0410310000341301030000c9941680c060060182105648800405080240b5440030010901c1242014071880302240350040d2030340700e258040c01d075204541d000c2c100041d00400c150725003503240c4540112041103812107008003004108c0340307210b082400301c0c08220141d080a0402041d003e0741c0400104010000b649000b2a651030300503d4001e199122500341e0740c1040d40700d4100151640e00020b00c8c07802c00c0015050b84070ba05014210300006140c6a07801240c54031114410315501c0500d10342d81c600c07a0080c944400b904103200d2001c40b803510083c0318820060f40c1140e8802d801080305d41d80684827407074141c040d28801e4650032604481524240c40040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 629145440 1250 629144190 629144203
    0x1112040f030318031a01080118021c060f0c020a020109090c050a11030c0106260a050c0f0a050a061116180902060c1006050a060503150603131208070e0d05 68
    0x160801a800d1a110740000b83c800c00711010b075401040e6000061918006190900c0c02032090040c1907183c150701d130071411001c48070002850b82c0180301101d122901410101c43c80001c0005441311503841c0c1c09186141d28500c40d04c4160302468014090090060002400c602d0390756200e07801d06814103280481d01544281225443d04280c206414000708412040d85103000d18240c640c125864620041050a246e4091070801c560202c82e140302c003007400241540b50000800000c1699000d610507500a2400707240040e002c1e000a04070146a6990b500052540020759000c40c0210f08080320717083d03037142d0910081e5210000c0c0b900c0840c80c10314016104928919850744403250315680c0242c0000c555415084680501ca004201c031030058002d6040c0004000d1442124462030044a0001d44140207400f030324811600ea00301c1278062000e0900f4006c0325803000f0f084552038501c2090080001e11070070b00038075103240c456961081c1440c1c40744d009071440342c2d55a50f031807150b203500300c0d0f420000e070000520 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 629146690 1250 629145440 629145443
    0x132c090f01180b040f05030f071110170408030a020f070b0105100512011404020706021b0c04091e0503040b0309151e060d05010f09050102091f05030a09030c060c1112040f03 76
    0x554406845da040080c1507004802c01004455000105032043c4100b80c074000805d08805c88100d41800300c1c0000a41d42c01045c080176800d2031120400250200b03600c003010f55401450118054549820541c40c19280d40c000c0038102c45040ca40c100501c03050920400e220a4660f103400c02d030f0318228016840e0003003001c0500c00c0741080e5031030260f00e00b4a070f05c85030140d0750010740c408829521144910011000072a100a81580c0382c41a01206009450030303024940c0d606070840c1d02041c0762507001040042051444134160362a00c000c001c00104400c0007030007548100b0107107001d040151010040c41c000d8036800340210300c00748452025050000101190306030065002c031107003170005015161641c05090010452104a841c0c4040c1105106064008180f505012500c003095a8004828a00301c2c00d0b1840502d00090303000e00c000b46408160740d001d040304074080c1c241042060000e070703100340c141c170042c04540001441c40300d00c84070306200410050b050500703060300460405061406001c01c08919110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 629147940 1250 629146690 629146703
    0x31514090f041b060309050c0102060c0f030a020405060a0504031b060909020327210a0807050d060f030818090118090204091202061902132c090f01180b04 68
    0x3240820044a0f83d40c070941118005096401e03a8602d800750041103006400c2c3e800340616104924150320100d442072240311151491403c01c4880100c1401c01d40006003035003811542040045203039980c2801a04034405a03a07501c03603807982189440340000c2c0d003072613600700b16201c4484103020003500075008400b580c010040050302c980d90441810320084e2220f07414103501688041600104801007980c440da0030080c034000c0d4003c4403030120700c01036100e005641000070b1018000301e44014800d50081000140458010526036180c0c0f141e8411002e0540c011928160002211007501d50380c0c41002c1020341342102e450301c0035850b040d060b5400d01190624904e03110340d141d459108660725076001400940d000941c907035085040340000b0303680e414240c5080d511822000d44a802d50351040c0226803100c62130460302c51845150000c0342000e503004000380402c0c0c854042c4014050321401c2e003454421078601e0020000d0b680303000c603064215011301038800300306142c1c1d04c481e8010401a40655421980c040d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 629149190 1250 629147940 629147971
    0xa14190e0105091503181b120708070803071a16271502010e12040510050f0a0903021309021c05010e0a03020a0b070c020d0308060a090c03151409 64
    0x80040314a44107008406034002145801d54100481130030113180300b10400302c0e21260f01c4089200782035641c0f04100c0d052641160131081c0314094100307600e90031994048041180c80303964450007400d051510607001300d0030941c00480c410090000030409180020140118441c0600300341c02d1140103151840300c10014004510a05241c11401818000c00c0940308107244140d19194009050b462002c0410600190300f4861000340948020a186a200c00d0f40b1100720710300352a00e010310044c20200c00115050103024000707081c002e5283c1e002031652009680c0c48043c1182544100310194400e014000303e000c0c84c0c48014801601d03144146c0245a04801410408400600e840ca0141c50400ca481270f413801490aa0f100300b580004601480381c1c070031a108182551940012100d0103c0300c1030284d4000380c41030b6030001182c02180304941111015000690154480401d00180e5652000300000079949a00d030b804145130800701900a400c0c00855150030300c908800150780d011019011001200146 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 629150440 1250 629149190 629149217
    0x51b191d07080f1b0d0c0e040e1f0507092301091401021b0d0507030b0109140f0a0b0a051507060f021914040e041a070c02030d0e0d060609020a1419 65
    0x20043e5001199901001d204242d0681d00090443c0c1860340482e01945c2040c5880270003a4020071150f900c07034a0351400c0d2079124016400c64015001c0540350105000014801062003c00d1801c85503082c132900c40003680c100d0540c4001056040f850740448102c244054070007420340c0c0c0c045006200c113443c0e60b10304245580b074000090000d540008004003240b040060001c100300c1100951812280300d01e40c1044001c0b9008400e19007100125003404880300c00300c001624450b615030240c0070070745c40506100101030700e50000c900c0d0f00c0701c403005104081601003080070410110f0300804180c41d4045c4003d5040c10101c4500e802c5c160300c1d01c40808140415a440b60960034900d10648008026840385813a442c2041e04294003110b0003120002c0f804101d484c0000c0c05907008404444045034050010000038920b107204681203201e510740154054002d03c1120042841d40c0510130203460401c100580c1d8007401e0310090710742075041340c41106001041c4114114480044400d03501c5000c1800c2540000400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 629151690 1250 629150440 629150491
    0x61903110d0c08030a020616020d020c1e03060f0a20030a110c0d090f1401080a020f0702041104140901120b15030a05010b040c030603051b191d07080f 66
    0x2c3c1c0c0012402d4400450681c03901940042d002d4000c10700ca0402141c3d801808800b00d8846040e4400034015a10044002c02c084c10900d001028900a0030ba00340d01042207180042c0c108a402d4401184c00e40900b02030252005042c0b01d01503d295450120810b001000e8005408030f000040201820f42c1d9100018891445200b00315003882c04681c059a180b4480042d01610702e0442d8058002101d61192020407484255620401c40e810140c45800f0b041d17440c004204040c0d031100311080c002107424490880140c480340120103542d0111103140d03032102e050010352503500b04109000b0384203240003401007003c14418001090b005070046071f000642e949507035030321100b400e580420302d401d0310665142d50300780103065000f2905030504940a102140701a04101c06987d03207800064601e40040d14040142d151006100c050070f8005400151a840c6112008480c00025403014043c0580700010344122a20061065031060082c01c000107141004084c282d61480d0040034410012540304403ca03e050300f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 629152940 1250 629151690 629151713
    0x1b0b04061d3423040b1009090c02010507120e15090a060b0102340302060c0303220b0106030e10060801021c090201020a0b130204050708061903110d 65
    0xa4208036115a8031500c0d0805852030040e1180380c0d4900c0000c44000c2c4041d4407540c03142107420401c0c4a20740b9007000c02155601c60034444401e03500690703410140941d03403207010000031754000130348030010b0b0703507203031805d40320035a0084203102d01164500800c0001254010754014000d014080700001c000c0e810750341003450000308501104a4140d003104000101900003807070030800f4421081803200d80300040041e82c0c1c074064120303c11521074008400740000e42109400c2401140b040c00d000e10820341d6500400c64079807050240d035106030400400c0100f4543c2c5528a0580f40f0662151811800320b00c1c0c480d80c5820300180680da04054848010a00b281e804104012524030002001c00009958002e0a4003d50100003094203074403078602c95401c0e1045510030400da85d50180c02800a0000c55510b6074161a8020301c111961742c40c2c1d01b4040301584562041e00c0c03180384162a04260350810701c041054082c143c10301c60b861700d512003000b440055203035101c503000200c060340e140d00e802d5414036080d120f619 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 629154190 1250 629152940 629152991
    0x1b0a0308130c030b0c030a0b150a03110d051503060c0403080318010b090709080c060903060403080612030d0f050109021801030b040e1606090602030703051207170a0c1b0b0406 77
    0x1283c0d1085c0101c1c04800402180118200755041002509030000d009009480090344490100280160702c07245009030800c03125070480301320151400c0460002801200e40c151020b40c603407000304001c02d2040c181084016004440a00b610f4101440e5075210790440c4070080028981003140580e0a4a548003500040c1c40c401c0007d24141091500d404010070804152050413007a1040c0312258005040c020101e0383c0800024010780001d907503584003907a120304060b00042e00001c100301d1140c41060188081d1000c408818400b0440f508041c03c039409445040e0070040b4900d104011812081850024a020041017800d0200302c4410400c009002016082e003500114010502118500f040140307100050f1159a11011142a2174001c00ca0780c1c0c6c0120180100400c03400c02c034040070401c4134080d4540c0142c4a1130b01050302030140c03440704805201a200146140c1e00c40301109084c540125942c942103d41100601c410001501d544c1040640a070000d400d441d550a142e450141200c4481d00004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 629155440 1250 629154190 629154203
    0x20403020306041a0c04030206070809010216061101061703121b0d090212010507050412170711013207140105070f03050604090308180708121b0a0308130c03 69
    0x140f80c0303428070307440d0f41041c03c00c40d21090b04402d0025661000c54401e40d01035a4025000d0750030119255a00311031079100110b000d0541c810040303200e90542d42200d00c1b00140c08141d80d2607910720103140006095400e00e8018481407801d0203400041c1000000039522141c10041c0b40c0e000948a80ca9216030f0003002e00191961400005031103102000c96030482c00c01d03180300352490b5040040c000222400c8800c1a2241c00007c0e10820080001d04000403480c2000c6010354030103036158505086101844d13000c09021911a80c00711103610140d84c00c5100c160500e04590600010108140c07000905403410504540c044200400c00301c081c0a1101031a04071289001d00800ca43e083c080e801502c00c415003590080001d08110028149041c1400b488040e181d16485201d034a4548807039030060700b01041d0703e00c881441003100000d1041d07000c20071805401d410040b500d94411244c19003609030400c180c04107100ba440646800d00181c2d01a038515840007031074101c008201034601d00300c0048403c1e94000b6200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 629156690 1250 629155440 629155453
    0x6060f1206050a0902070b012c0901020903030a0f0e0f0a15020316210309050606060c0a05010516020f2d0304030c0b030703051806060108060418080c060702160510030204030203 78
    0xc4132403039801403440e1400745c04141c22581c0e07105481c124104590f454003c580c3c1c400c040714000401400c01203900250654000340c1420003a030701183c65900140001c4000840c101e9031041001d0300441c0b4111000b006990b54501c41032180046103019205214501510202502e52019548240700b5144668605200d02c0300c49142c80c00d20043d0030200c0301c5044014420858581d005a0103442901000d1350302801806d09540c0e000104000750f046031600710084d0088080c0c0b107002032800c2c0f080511900c02c011510344454103c400c000d14000f010b4000200c594801341c40c0a5144c43c452003003002c400b401002213403c0500c0390032103600314060765000a0001c48030031404a52180d03503134080d520480d00340c2d82c20015551030300e6030580620101c070a00b1905800200210710107500c6121400d034410b002800c01f00e030706101d03450100e201c400c00c141d044e1010360001c20303d8010442d043c03003159042001440200215610180704007040c4c10303648a040e1081c5180d18840b145d8a010780c05480086400801340d0b101c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 629157940 1250 629156690 629156699
    0x525020c03060a020a0908030414010e0105040b19020607051204110d0210050a03050a0204050603040204050c040b0c0f0f072105071502010c020c0415060c05030c0a230106060f1206050a 81
    0x285d003018104c00041440198041307040b40300002600d0860303d070400c0140300d00100340015a5070307407501c0c0e81c51410403208210110310422040e00a009006952003955a90010508002d05122024160f501040420131402e58526039900300203401c030340c0100702c10034500000c00001c0c4800312030040081d04007440d94007045916401901811784e06517240c0742449290341e0304442c20200d1155004030383e8021010710104015062990026a002c101c4002c1035140c84d448035004880c1b0741003070342c5484865200d03120b400031003542070201d002d5a8000000404e0104e0520003007624400d00088041d00328011486120b05110040014000401d0102d040c080200e600e0507000b4041c3c55401c10003009407003900d881213100e0500344a040e5514042e801502911410000106d40d8061421b0050b10700b03200511818002680c24081131842ca441040d481c1156055540303a10b00c00b800400b079081c1a649024010040300e5004907000d40c0d1020603103881c1c00380009414102d030060800e50402d54003c0401c210109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 629159190 1250 629157940 629157961
    0x5090312010f0b04140a050301020c0330161e0801151701051003090c0e041403031b0708160308180c0307170f060c090a05040525020c0306 61
    0x808921009204402680c0b2004200d40c124900d12941c80040002c00007081000d94200038031000400040c0b03110400ca84c1c0c3d00010342640c00038601005240c00005001d0b003444c4085856250103144074031005180c10140ba09064181002020040f1f032900486c015021140302e00884420010100a2141c2444503401d004101003024001d00356400302c2200e86804e02e40c0a4034200840001030001c850b00c980c01c01d801c2c08a034050043c0c412003459281c01c40d010001c0c2c044612107000d803a0001c28450789181500381400b200c00100c98001003074101b0030520210380d010307000500d21840714107030070f5941e13003c5031034004030910070300c05070028084400400300200360b840a082c0d40180985e00b0628001c90503da141900c41a002020301d601d40c0c400c00007002640451a0100140c24046099a010b00040031209003000d20440e58200c0d01040024080306070714000354220007601040d24204114a81110035040c0c1030f40300d200500c1c0c0380c0d000158102c0244d100704011585000050180c51142c1004080013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 629160440 1250 629159190 629159197
    0x1303060c0905040b0310150e09010b0f240711040509061504290604180209011e020a0b06061317010c020a0302070306020f04091a040507030c050f0d0906050903 70
    0x8205010020750391425005005210304005c002d0b03c240115074943c0c000402c0d84a805240040d1041d400240309003407000d800f40b09004210000c154010000b00b0001d012603941800351140d4113380d01584480c101100da00204c44032030320240d44e204224140407911005079400154094107050411a0900c408511103002e410364000c1141d1100c040410001074031800c1c0071007596041514000b1308040090040000403150260506161503219003201c540f580280081004541c0c0000d80101d4650348560305100d500e284d6141250302085000c00251140c030760f10006441c0561480115160f981e4204c2150324281c540f901d0390101d25966a000352024081d03a03401c40242d46407a61071040c0c1400801c0308203171164568060540d8500b141e4034034000b03400c80903070200810024007010a60f030b0080d218108610010380310746010301021408100039603800405ca0003c00d410613504880c030b103030001c05941034070700e5a41d0007580b104d020480e5000140490f40020340b4550600d42031108005010009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 629161690 1250 629160440 629160461
    0xd0e030a140306030d080a090501180b10031e0303060b04182307080c0705060403112103011505070b0c040302030f06010b03040b0402030c130f061a091203130306 71
    0x440c0c62540e9110641d41e268081190502d403d60440884042c9a074800c030650b96100e00400000500311445032a41d50844444070a2038800408552000c014044180141a4040c1c00517425903012070131a42c2c0c0210180a105080320140c03074542d00740e01050700942290002e01603071041c080c2c0f030f542c2e0b440840100001401e6095056880c001440e0800c81c4560100c20202c104001a06682c0d114110111000d00005100c070b0032104050041000080b0280003060241e4025524000c030b0f01030010402d403c0c2101c42400c0d440003400ca03044c042881c0c5007202035904540a100d1030a10309038101c88251014442c81c0c0303004000071003000c10064840442c0c00500144c0340254105c503403020340c1c025036507aa0502030103117116059060000500281a82c1c7e00746500074406800c1c7c2d11340303250b840e020564400c1170a8482188685450f1181d41140c070600c122002003c45802c0d0041e10340c9041c6484125100c2c0f207000038055010068172084142c810011951042c1c90300c410003941a0752420004002c000701e200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 629162940 1250 629161690 629161697
    0x220309060e030f0d08060d080d0501060f030903021e0102040305030c0601080c0909071a0904021209010e011404230318010816080a1a0d0c030c05060a0f03020f0d0e030a 74
    0x800011402c0c00500380c421075002e84020b00c5001e0484d88240c850140003410030340c1c001094000700c030010f807060003e410342d050003c001299550502c000502407007a8050502c1c10945000040000b090f0300145d28000030b10b40c03282c8400c4036018100c1240c064072881e00050241d201c0001d043d040076800154160403210311206864540d080d00342003009003041520000d8403903200c421b05202c0e900c0e55806175040c5840d060f516034900070b40ad10125041e41c000c14102601400c422042103000c04003800b604502d000c0d0781008010080301140c0c0c0c1003654401920180100e036581c00440714208950350700c120124502d100f200c1d21f60300e103503d00c901c1070707840f50102c00d00055101d8040b42105040c0d28040070810000c1c1c6501180350340c1c0f04c06a0b0f00420501e01c0d040c00c3e40042e41c0d1681030380d80390242104183c9000d20002d888c001d00310704226005e081264000f50041000300400001264055003020b20a000382c6009039072041e582c91350310813034000c08000001d11032034210180000c0f4070010040441420711784 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 629164190 1250 629162940 629162957
    0x30412021c170a091505060102070302040f020904051b07060209031006030b0405010e06100630020d0510030218071404060908160b0a110a0609060501030314030c0d0522030906 77
    0x40e401d0240c40000c8002084072452402e000072405e440e0304019848001841140c82103a600e07000901500e44004881c0321042d80000c41d08010b080c98082c05ea88041082500d0380f5103548409194518400d6410103006030b640460445001da500740900f2900005024050140715124106403140c0c240a9600b15529840d1001000700030a01040d8035216082c80208160203600d403070000d079459181040c10070303404090030000144a00b010710449201c084000e00050700d80c0c3c0148694001c403a405050752082801c1d5110400040e0341e01091450880200d0002030f5594030380d9503041da0060030f0002a80c0e0302d0070f40441c0204525500c00c008204888000b8101d410003112800e43c0e900e5080f144c00b604441c8882082043c00c902d0242002c40395401d001411030b091031503240c40f80d0302100c168140c21501700e51100010000d2584c0711800c0ca00040074100e89500d582031088224189120700c1d2815020745443c0c60029024403200211348281c0310740c0d00381c4007010b0780d400d2800030844246806114007144540c2e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 629165440 1250 629164190 629164201
    0xb01081c030e0718020705061807080304051011030d0e010b0414040b04021014130f0e1e04020609030a030f08010b0f270d0c060e15030412021c17 64
    0x30b02807603060030038070800341070030300d04001641c02c84003030900e840610300d07400300300d000000340742040007030b11490f80018155181412078650600b02080c030f6002c035805910600003444036075600b82c0210413200d05410f01c200c1c00c00400c0300f143d0842c0204270783d070107040d0310305021040302403070640000089039011103040000000d800d41130300f0360708000d41c0c000c5c10350391100c00018014100321129000903181810240d070104036001241e11aa440100b94820076407404030108018041340685070040c0004034401c0b5201e2034035800141c08185030240f004480000000807a00399110740d01261081203001d0b06442c2d0070300c200c2c00c01605115070502c980c0000b0302104000129040700c031007510070000252040c0b0345040109842d82c0d10942144000f05681a008a101c61981c0d4540b182c02c44410311601351039405610b091400307020050102d200364010b0083c6141100300c0030581040301d41c0154490403200e004440710800b2132414000c40103074105022041c41d07008e80113070000b032920300322003d04e003601007582c2c0d69 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 629166690 1250 629165440 629165447
    0x31d09070c0308100f08031b010b06030a0f11120f06030d022d030a080907060c030c061503081305031902032a030102030c090418020105040504020a03090b01081c 71
    0x12100200003603814581d003030000c0e00c078034403480d001010f00030007a600c2d90b25214170480f542c4070b5034400c000070303071000503039146440240c8601940b4002080c004c11100111001103251444010201003040783d44609031026548560b200382c2458015030b001d6520ba030518503103174034101c009442807810342c411400011242e00d000540510640c0482d80030b01a604070045050981255020301203140c1c4c0c400c6003002e4000d40003007020300304441c00c5945e00030700750408800c140d0a1503200d801280400c030030030b0819804280c1103a00079034000d5105000040d806200c5a1074842c0d00c0c20303500010412000000c0662802c91250100010740314100e0070b5580e0400c00c2070344009000b0052030001d4258112007243c0c05080342c1804601c800380c0c20ba0710610b01c40c4e0300c000002400c903802107031100036441003c5000c03d018205841981c1c228012108400606011900040c2c41d0340600e200f058459500007500c0d8614030b100360048400035521081103892540c5602c01030f605c4001164a600d618034404880d07000c098403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 629167940 1250 629166690 629166709
    0x3150509030a0315030b09160603090f032115090e0625170f01140d050618010b03030f0c15130609020609030a060b01121109060a0e0904031d 62
    0x100500440c640702c200a400c0d8040d1501d00d44140795801c82420000c00b040340301444034482e511074800b400d18075000500364240701003150400800c051038018103000007039404620044880d01414906042802503403240c00840101d450b011500d0704046080b4009401c000c0d21200b554603114082c016400e469900c203590b240300315400381c2c2c9103550700320b0034502020020700f00e88079411918040c072012039030f0503907010100d800b941c0045514541740300400c554804c02100380404d03101202c042c0354070314480d07d55558408001e40080d404400d81501c180c8042c0003580103948400d40030702540e40300c400c40051261aa0480e10001e0340d94000c01c2901d0007a000043c89040c407444c51020b100b5013256898030344c2c400803c5605006c90f040401040003104940e001c002c95030760310344070300c81c00702d0183d6500000508400006201e510f05900300072080100c00020f070191810000c0aa441689910703009204039a6210030700802508810203106000500da44814003940c241c0f4500c041402000780b24080c401080c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 629169190 1250 629167940 629167951
    0x40e011109040209010c022806080c12180d20070515031f12170f180619080f010b09010507060c0306080f0c0301050f06030c0118030605010609031505 66
    0xc001c0226052600d429070140003a040c0c10316001010101c25030229604d100c41d1400202500400d01c06030558107030101c4900c014048a151011a03801c00004120540c02801e161f041d00e00700040c0000c03803a038400c00002107100425811a4400d50908002070b000c000070015044500001610152581c10001103401c212580a45440100c1c1d031105424038240c0c10143c80220b03040d000c0b01d842d1b00700740301000040001d4843e00313000d000350903032030720f440d00d0b00e0800c0401c10710a4110521080310a15084000d81d050203103000004400f080c09031000a4041c49008109000d8011130288420401d5009041502c03408800c40800340c10398881031007000b94082c024002d80012000c000c54400a445900300b030381c20040f14180401c505841e0003405041914400c00c401d0264003286080d410307441c00f40500340e040328808020030002d040c6000840d072511031061249042c00001103091320382840c0d80b10001c0056410580800195031123a400816580c00342c031060301c1404121190b403043e00010302c907c0340a003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 629170440 1250 629169190 629169221
    0x92109081203040807050309030106090f0b0a030c05040b03030d021801080702120301171606020102090a0509061507050f030d150b0c06011a040317030106090f0f05061602120606040e01 81
    0x10743d610f694503a0302d58007502084660340000d101c44a0316440c2406244d01900e505a00450000940f4628000310740032100554482c00c205030080000c107810000d030b1400c2d07500964004c14012030300d6020134170f90b00c41d510041842a1000908240c8280040098010b85c88240d98801060321045d60072a070720110107901c4150748400700010008452001800c0501007c002c0030382d0161210144490000506688090007507500001c484c43e03070b031902c1d215203006040100c0710710b42c0c0c5040c12004107104044850952411181c0040d0b40c85c140041048100c0c03505030701381c003125680d4240155407409015a0b0345580c1c400d6100300404200250400b05886441c040352004001603860007200200007040c031480d4040c2d110080002101141080e5a800c0c4010403c25029589502d0040d001300010f443da48400e40e00810624280824000054450f0031240c0c22141292103040c00c3d140c2c070a220410310070003944000c0f481403810503154042215841100d044600f0000241d0510310036082c0d84064590310040f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 629171690 1250 629170440 629170447
    0x20d050c0c1506041404050a060b0111030409020a0302220503010b0d030215040311070608090609030f04060807050d050702010506030c090601020a14120a020703170f030117010921090812 82
    0x2c0c0030103500c5641d1000380100040748400d210a0b05518461081d0340c196031940000f4200d4040c03201c1c81c01070380358030003080c81c14801884035811000d40b2801180a1048001c0d00080d0307807180c01d84290180e070246a03544211310b280342e09150303840e00300c1080ba00c1040e00a50034210354030101c0c600020704038190354058014007041c0f84c00441e20044101c000f4030480c280309072491495485001040303910040c19058588860501b40108031030720300580289a800d441d4420450a030702c0c1c1c9210802d4034101c4420f03092006041d25000030646080c01101d41800d02e0380c0c0390804014a05d47d0541000f406075206805a035103c0841d14203001c2010011610540940d001c240b4101c00135030001040410b4202c44800d40d094900070403008400d65006060707000042e44006e5082c400d01c104d02d440c04000d142c444422a01e8069455940b45140c00144140c03a528140c51441030341000c002e40003841c8442c0d00070940d04c02d06510200302280303800008001390014a00080100d807020380090040d107501e2031131401e01e05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 629172940 1250 629171690 629171713
    0xd1b02060403110a08030a020102120c0a21020c100603060f0603050304180f0501060810060908060f040f1a100e0907030f0305040e2701051303030b03011806020d050c0c 74
    0x6940043e002140e0000c4080038009901e01003070015000b481382646c00960349480b0b803440e0303a8806101611034094090108040c500c802d0300000001100700d10300181000e25000711010100074010f403140711500d0b016400900c06140080e41c80202580d00c6150204042c00004c1c80d03440889500d0300000304654030800c400d00c4143c868039001c000307640400d0780204940104a1980d420f581080e070094020072035400510013603907405605040a01010314102d008946050300d11542ca000c040c00014044032a01c0202d000e010b0744004c441e4505030024003d84d600300600c02c0d03805200c8011525500c50708803010001c02e8501500302402d009010340002808803500319101c1c0f00085080d12422801d20008102c0024007000885003d40301b55001d1041d4000d10203810b8010085442081c41503150b80d00d0002041411035104a018601c15090301e000149028200003003170050000086070110351008405038000c001c103640080460701a602410b01164640c0c411411190040c03058210079034009191042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 629174190 1250 629172940 629172953
    0x1f210c12020315040e030d021b0d0804050706030908090907020d0e0a0e1b04050a08100c05090306040b2d10090e062202060c030705061006050405130b0a080d1b02060403 74
    0x90000203101c152441c20520059000403070380014041015045520740c4184d24030400d00c02b01c199049581030030300f22490b02ea0380c0c643d2200301c24042c001c281940e07500c075102800244025111202c1010f490b10026003442c8002a64a00058600d540044c0c5005810000d50600b0341c0701c1400c0b2020032801640c152181e100c0c0340c1f1401451428002e4680d8180000169591040301c0c40000b01071180203010300391071200b5510117940c81e0a0906040c042d0070420b04800c0e4400003801940282c00009601c01900c4818101a189070015007181d03000c2d61100c00071100e0040c0e581305038001c0850012084c0700c15a07030412002550700410320201d281e048040040c2550304440c1c1800e18800320310450a1915012b90f000804035000342049200c603a0000c15070504008042040a07000340e10314060490300d030b1401800503d548145e004a90240d600d5161035004c11520781c00070100000014001c80300369072160b414655030041c440d4400c0000340c02d60907400d00041480d0400d034031a0b0b005045240303014195100c1c0c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 629175440 1250 629174190 629174201
    0x10504170102210a050604110a080a110d150f0f12050c0307030b040201030e0c030706050714010c1806030c050f09060c0706080618061f210c1202031504 67
    0x110495502000000401c010036204071404202c2d0310f40040d5103061900540c81201c1c0e008100d40d0049117001c986407449420f24058440400042c50510115a41d00c150100031341301c0044a025000404940d81705403031649d40180d00c101ca01c0a2500d03042c16a51b0814103040d0480d07100b02d03d400384001d03505000d400e00a5180c049010302600c11590f004400d0b40210b450b08174994000d841544010050208640c2d05019180c9040c10000040c4011244000000e40b5901c2d103106a4040c0800041e03550204109000c000c040c644910008000d000184030001d00f844051001c41c803c01510408040f508600901c80c2000b04c50b2255035231414412001107501c480c0e40240781d100d41c802c4041c088240c90354030070042d0a0140000341d41e00341d01e40c10035000344071a201512a0075006601c40702c080000507200c1d03002d2074000b04002c102210a180c2503941c2900d0f2186081050180c40640c02c1e000703000032a01e500400e000c00aa40d44140d0544080b100800c101d0101307503520200c42244018580c00b030b140c1074100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 629176690 1250 629175440 629175479
    0x5011404051e10030f0812090307020f010f17010801020a030c0f080f270a02040b0406140904080c0f0a0b0610020616121a0f040c080414071d04050c030c010504 70
    0x103901c1084c3e1203403103100007204881e030101c0302450006680e5180c21041074541d034100e01d6400c0194140b128540c005504032241004640c1000843d1164020140c801c880d4070400400072220101c455071144140c0d07000c0e40c07100e184500824280301c417480d00c1d01d2007040c044c10004010340d292030320b50312a858214461070001d041c2c1030592140d00c1d41e01d003101d84410703941c611007495103000745105202d901c18401a10200e00d0f006120300d1508004022285801c2d40000b10214201c84100c8207a0380e0345050021401220800065803144e20307010348206200103410b1514602411b4092050341d070301c0040000c600a20700200d40141c0000e800308160050081445441c00d40354140000710344142100c1008030b404078948450308100034900106a41000c0c0e0070806108400d0350140850040c2c1003000d0700c07914024200401c184101484004003c4042c00346101030111072201e0803030082c40301115a0040c0003520241c500780540c41c051401880c000501e01c056441c10384409003002c1c41c2400541c103c00c2132410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 629177940 1250 629176690 629176711
    0xb12100f0e0a09032d0e0301050c090d050f070612060504020f0d020a200c120309010831060608010c0903020310020a11060403030903120908070f02040b09010905011404051e 76
    0x11001908601030b8140446411a40d81850b40c014050b00401e201e80042986029909d814140300308149040d08481b050082903440c000c0c900a985443ca1504040450904050088940c01314005901c412100c200e074111840500c40b151b203500401003248110001c4812104d03041001428044a5401070260b455050404c01c681003031540c01540030000700c2d0b04d0350002c2c0e04032010080440c6424800040b044c4044001942000d880c000042c005503405401108100c034400d5044090580c0c440a141d25200700d2240d02e04001524644500030300500d01075207005500784001280360074401c040520440b03800400800e5200342c1c40b4802d000070f40c40b404c024000c10000000d0807400480403c00107010f144a550001071102103424000d102c0c00741840212030080c140804100403600d5502616141078101028221011241c4001401081440c20783d54010b10740724000200000e4070340c007050481d40c40c201e0754807145655004200855800b00c41c0200d068071200d90b443c0150103070340000c039030100b001c25 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 629179190 1250 629177940 629177957
    0x105090d02121e16030c05150c010c02070306140906010302060315060f1207110d030507030e0d0903060c05070b04060b0609030a0c050307050a03030c14070b12100f0e0a0903 76
    0x9060b0404103d0303000e84800e00610001000142c2c820000d401070381c0e5005020a1410307095070b031002d01c02c040e00c4c0301d90b92180b0004a0a813024404482c01c86403d000d290001300300ca024403e1005e5260035a038482603c2e0b80d860300d403d034820546190789840c07103241d8540151032903a0071036080004030782002c0c10100d41c41c10f880b81d0190088d00c03683e005004094ae60348440d52681b148420210741c6110050001c81003180c50786d02e111400f180007034003503c681c540c0d0801044607610315100b01c0080c0307020b0003081d10301d1240010081c0130941082048003074074001d0400f0300c8030300603102080c0d8491181a1000300140202400100441c038240d102081082000780941c0c9010502d00c0000c1c949111440d0666050450140030086494100203520046c103050b500700071068a941c80107800d51503010390141040a5444160310400024810280940048071640d500c0e8052801103c06e80c04007100d450051141e600c2c0c01262001c40324031403c00721440a4842035065950b00004000740103501411003d221250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 629180440 1250 629179190 629179219
    0xc080a0e030c011109040b0a0e0f090c09150306010905010b070f0c09020f18030c0d02040203070c1e052a010f0c02060f09030c0f280b0d140702010b0105090d02 70
    0xb03002d01041c2213107402d902500c8403a00d900304011a0340840850788603070141d840810402e0501811680d2140d40007004c07c4071940d0b105c0803030b810509402d2440768880c40d4401003000c01c075800041104c6e086026021105103a0322211100c040b10001e000308642e03040140480b000127071004001c00b400520a240007104160380c0c00c00e01c801d81c1c0010040d80640072000c500400e104088040500c203d2504400421520a95201059550340b404001901441d000000592200d001c0c203058544540d0001e03961041c1c072485462400c4540b003c01c1d00321424003601304000120400d50400640f00b400700000348201b54003400040d10307200d00c034440f01001d20246070801009a91114043c10345c0a0702185070780c1d46c0d4203404d000c1605100c4045041d80c45414516851140e030340705c8031030140858800052109080040035a0001c5000b501ea2050032030304000241d0b00c03107003007141e0080c0741030100e00341541000ea100c1c90016820307106285d172040c1c00600d040c05201e07001d141c200c600d441403500241000c803044c80038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 629181690 1250 629180440 629180443
    0xd02040605040303140a09060305060f54190e0c040501082a0a0e190e0316060b040615020610061403010b031806010305010905100c080a0e030c 63
    0x240c0d02560200d01c01103010000c1c5904a04000440100b40030603d10b071401d8028090074842d03803402a0403c26070b40e4000140c0c15180d070b006c400c2141c140182440151014012801003401c420b0508100000042c001e00c1d0400c02011860696141080300b0762124814800e81c035000d081c0001c1070341c4c1d5808182c80f01c0c9841c218040c03007601c00d41c0044002522a00c4009801d1001b6200181c0c00389096501a1001c610940422060717924203680040a5900c2828800c00213080d00050380c00c2104e0b4094568140840c086c402c807090003548000e5401405030320f1070201c00d251a070285d0b8a00090746402e03802c561b0000b034040c4d40f004101400013400003900a0300d81e802c0301c0f030380d6040c188001d003d80d03c41000e000c2c8007040c140e2904003c280d60b140c210070341c1c4105900d0155900040c0b244005c0810f000c00407602211100d01881c0d10719841d070044401d0741d80d51703040250280101840580d110f003c2e19000c40d00d650386a00440b2182c0c90749031125191921a20302e030b40c004141050303c085003804140b100303030f610316030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 629182940 1250 629181690 629181697
    0x20402040e0103290105010e0d2604290d090606121a0f0108070311040204170d140a1b0201020c100f0e0d02150a0522060e040504020a12080d02 63
    0x2d42483c00503071044c05112402c148001000081003502d00010046130307034003407030381c0074541c1060380d458611015901e04000c01e01424142980ca491401c0a140700e840d000201900440c1c03090303103e02c04441400004502a0501d5007844a9001c01c2003001c043e04040d01e400c210b10319846400d00150003a520300d00f160b80d4141c41c0320101d580c1440142400c40740011041245d41007113010f00d40d610355525084a080d550a03a520004100c05101045c40c0410394030342c4d06030390090400008100552024000154440c24064012408681c40000000041e404101650958070440e1103114031000d007402403a40718407040000b20b0461244021150403a00ca4900020600890b0f889003280705041c03150242040d401400090702482c9181e4170b5102690391150b0b901c0c443e4100f007500540d0740c900050211454840e0307094a1841c0705a034080340c0983e408070300d6090200c41a640e00d0300c042030118001c100c25554281c4020f903111101060a0160040442c1031590a41c400e244492400003040c0000c81a41c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 629184190 1250 629182940 629182943
    0x15070339021002010b061911010f020c10050403080c03270f0d081015140a020a060b091018090506040c1505130b07080403050a05071e06050f07020402040e0103 70
    0x3580c882540440c00c2c0861407144060306800240b01510f90b8034080b0311320f4058000f03103080441c1d4400b40c61000074001c1e10600d056507865002840204c0404441074040d40c40b034180400d40b80300d104036813001c5081c20300c01d40e40140d40c5995201416190400b0503280d40e0000703840d042500c00b811070202035980b9611020740d1085040c40c007078001c42c2c90040070113013881c4003011914203110202c2c0070080241c0442b203000003070301c3c16403103502801000303e00c048811410201c0350075a032250024151403840e40019109051074410300c002c0c40000002001c1c403003104002d499003400c4880e80b03a000d222a60014814a01000f00020300140d01039041d15010326006055500340c1d84945200c0040c0840002e07a410381138540c2c11420070902d80f05951041d14002b082500c07031b002502d50b001c11100100700380801207400858000d0100c820340b66403800c040742c444100380300d400481c1ca440007501d0300615080c1c401004603802c54035240e0801c03541100e00810759228240890b0320690330003001c544402c0c0a41c41c2400f85 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 629185440 1250 629184190 629184287
    0x21203070609212708030708030f0705070510090501180f05010e060c0403031d0406080c100201060f0b090a091e14040c0501210509030711150703 64
    0x701c0c81c01c0484803000f0011a5401c41205540c0d44100e031030300110300040003100307052900700200a492000c40c001c0d404c4e80010a050000156040a010010f030145004024031125101c980d111b07c8015226482001802800b0340c00c4410206048144c40d403223414250300410011031012072603d2015001080c5030380c00c80d00d0415013070307044007404824850006000c07040c1004141c91304041d9002c40c0303140120312000b0100424041c0b003404507907030b00c50000f54807400074000b400b900751180300481e101ca07120302e865801101030701048040107105026440443d1038120f00d40080c0ca082454950f00c0f580002c000303e80002c048480007800b5103d03481001c01020f80301096402040c0307040b60400a07105101300b007440c0030751024103101c04607245921103400c440d402d003446500d401c00491445e8100c103c100c1501003075032401007001104100800140005881006010310034102d02042000380a41030032500041c030340500400700040d0081c4804e030880e4481c28103118035040d150b01c880c1c21212410b105410306 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 629186690 1250 629185440 629185451
    0x1090e130c0b0c0a350a050f120f130c1701060b0a080906070914010c050c03010c030e0c03060108100b01090e0c1806030f0a1a0a030b060108010e07080a090212030706 73
    0x42c000d0341010305440174550343c148404100480c0803052001000d41e00202428400660f4000c1d043c050003c40d500b1802c034003080c0707443c2c50030021045a151000c50306400394030103c000040105182006a40001d41c0c003140303110400d03051100c00482e9000c1e1511018442d9a208008100c00300c12030301074041c6401036900c07600c603071034031120301c606212010703000000f4003c2900c0d0500070522407414808800c08286048070003079095050461502c1c907220812a01075203442400512950706401c000c0c0b00d0300106041741c0c284202c2500b4980d42c0e8900340310783d40064100c01911520300a040e080260301440514141c3c0f00180c5031074403041200b400f681d8903038034050002915101411b10354210b041c000b030116005030551920107100c1c46910f0740201030401c4999078010418060b040c06002005140700a40320b11107080e101c0c44c0461a840c4281c3d01070740400c003c2c40002411801c1c1c800340603c01c00300c1d5500d503000ba4442404080c054054424102d80c44040018581e000e101e08101410001d070040501180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 629187940 1250 629186690 629186693
    0x162a0b0706150303120b0612160915021b0f06030117120a02100f020d06080705040e0c180405120c03034609050304081b01090e130c0b0c0a 61
    0x31100309600d800c0000e002c501d42080440d800c195040c2e0926280e00c1c2c00300700d8101c103000003010b0703200d8510a94450244901030000607038440c0c1e03400c12454199150075001580701d4001c0000f10202d05100d00050f801461402c2c16448101900340000c80054403920055204400203900780c0c000340c1180464208503041c1c0050b884080150410800c0385960152600c7c00c2c43c04000c0d1115001c9601602094030b46140011010187c2c0c101c0d903a1a11035001040242d484458803600c40c0294820340c1d118500344095807448002c04140072140d05001401c42c0c0d03c60030f451840c0424a0b400800940f0b40e4003600d5249140d9140e0030b002001f14121210140d5581e14040c9517035410b07689041e21040904030086401004c0141005a1492407540203034101d4542003000a4034010f4041448000c02901000c030f000205841c000401c80c2c00d08d095064a000b450f10280011109200c042c80740c001c0650201000c00d1065614604050381f580c05a541410369585420f03007150300354060041c40c01d5544c80001c1110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 629189190 1250 629187940 629187953
    0x30803040b04030207060f120c020c130b0906061921090b06190e07051c06031a090c0a060305060103020c010e161706040204020f130b07060c0203162a0b07 68
    0x1020304650b00f00544500b026800052051903685404241641c9d10f10001203000c1c020081c0c03103194032005065810880e280c1d10074002500722512154014070840e008100c0500c2c1c09c00c161001c1074400111681241036001c0111980400c400007000903800340030a0308201c030640c1c01880006402103209414505140e000d00c455541f90340075001c06284581c905100d585e00003c030a0760804001e10340243c5685040300c030142c0c0d911100c90500c00003443d242e0000f0070030000100c001f01881c4030030758240040d640d1003911612090641036159111354414801c0c081a4000c0d0b12042e04407506140060500030040c0a0608507004e03009001d02c16409005000c002240c0031040002800d0048045082903600898040e0b6828015000174070682e0041003120700120b114042c0d0724030900a01c6c0306c0062a503102ca455580781d014000c140d88550901081071000d81c00001103402e210f080440340d00f0855001d8840307501082070710a4098402d000a1041c00701440c5204580028000c0803420a54031513a9103041c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 629190440 1250 629189190 629189203
    0x312090503130602060411040509070f0806060901120b06060307050906030a1a011815020312010e07090b0306010503040204110d09030201020d0f0504020604030609060f0504050f070801020f070813030803040b040302 94
    0x20f04550100080200160002c0d00e480501c4c08159400706e805e4950301046418445150050049400400c07000a00280009465401054142c5031085141d8840b582d1046452189070040c211566a00c00304143e4101440210f9001c455403030110300309a4001c000900e1680f05940c18040d8540700c45102080d01c10100903503454000900340449082c001014002c902c4c0c00912071456280210801c01440d0f0307000380111f601154840407564040e40e101c1c110035550b02c6040d83e1f0328001070030503c00880d06c0003100b02224000d080585440341144d03201da0800c4007600720740591220080c000d003c0da034001c1c0303690b0050300701c0944a50005030700c80040c000b81108079035038002c08904050401c3c0512000da01d13160121010360350000c60104441e03065082450240001075a10741c14039141608000502c2004501105a150300d1420340b440150b40d402c8682c281c1c05211100b0801600801200001403101c0c002010010601e4006692003952602e4450740c0e078200311419600d102900c820001019811f0114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 629191690 1250 629190440 629190449
    0x402090a0510030b0c070f0c0e0702030f0906130902040f0518130210110a0b161107050d060603060c08011d07020c100309050d0f02010b0a21031209050313 68
    0x8001e58600100302070034490700d42c480500886481c00200e6440724400c0225024a6007120f0307181044a031514025441c50350320f10501181c2624040801d0300248040216540540601c443c182045070720710412045501c090300c4c4542540306258000b5041c1040d001802c0102a1f03030204880d8075107840c1c180810f003401500001c150303000500801c020030003002c048405440e01035030210310b00c542c041402da802031031100041d07215208001c0a03000700300b607401180c2e110380d8590002001195140100f07803048022401c1d42c3c0810303000300c0024092420304600803014280a2880407400355666141c40c400c5907001c00d10400010310741c00040c0300740c051640c1e540703250070601c091140503842c1c5048000d445111781e0000c144264020100141c216100e41c00c8680c6480c1c0180590ba1306060801d07010300a88861300000000d542000580b81c1180341a075941801c650300c0700000f02ca4403490100040044039008011000c0c0206211f0340707113807003000d403060b0304000d846040215940d11030f03403d03601442c007400e511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 629192940 1250 629191690 629191711
    0x50301020f0a030903170109051603020a0c03110a0804090c09080a050c010e15120708130b010509070513080d0e0a0b0913110c0c10090305060c1612030203040209 71
    0x1007030301e00034002110340d494228a0001218040307440d08580b0b2054089140449114001c00441c0c1d2403131581c0014003030f046082803071504d00ca404034140c083e030080840b0720b408680d14881c8200828020301d0382d10f03800b034a03500030341d42000c20a5030f59102d40c0d0081d0300100c2c80903a03100d0404071442c1e003106000c009000405e004202c2d41c941d942e20359507110501c0442c94100480c1000103405e40c0c0300c840c1c0140c0071401c500102526007400c0719a42c0d2704904222440400140480b006c2a040c9100d01c4541030100d80180300f46140346c0c205030901501e00d0005d00b800080003020032405030709075802200c1c207007d000110f010f0b190890854600501c0d6019040101c1d1088031070f00f0007001600034141c1101c400b5001030310340024480010108100030003280c0d180c540140c2002500082030b82c0c012555407404070040f101080c00083c51181280e5880e024000141b03e50b00000200b050f940000c405406401c01000300e159420250f0f42c1e50309107c0711084140c0c00801c0e00070081c04114030303240345c48540c40940c440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 629194190 1250 629192940 629192947
    0x304080c03240a0c09150f031d191505090f010f050f131b18050f070f1d03030d0c0f020a24060b1216030b03210702090408090a05030102 60
    0x2140710400d00207011450000da40c0c03000084094081e21a1000826189181e21426030740c920780500a120316400d1f0900003407404083c00e401008446400d6103800d2544020058000750948142040181f05425501125600314980c040318660240d20700c1040100e01406a100c44094aa03080d204030520580526082004010003c1841280150b00c069800c25a59990300e913030a00c84903045086c401009078038a001c1010401280740304030310408264030081080346695000c1181407507503056a403400010700c40014924114407400d003400c280828a08442c0300c030408080003d20b103610400081c040192103124622051350000c0c000008004c4e240040d200d000c041d517403a02c42c2c0380107101094070780b1041c000c140311510358580d01010107040c5060105030b8507111441d0302e16034260111889015078091805004004d8841d004007010036101900811801c00d80010240700000c03003259602d85110203104401c090790312000c2c50b80c0618050704281d0b54a5421400b803000001443c1c0005000740e0041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 629195440 1250 629194190 629194243
    0xe10030b090f041a130506070e0f01050c1b1305040317130b01062a050106030c1a040b030415020d060906142209050a050c010306060e21010b030304080c03 68
    0x85400c54240200c0e401344c00e64403c10b1202120b840c0e000040c2c120701c11070080044d0140c0140005030503110450b221b1222844070b400440303061040344074220407a00580e01c00809100d01000c0030030790788d000030b040000060301010030208456040f50150001500000c0da0900f40100f40c0720140c02c8045500550000e2006445540d1080e00c180b00354420801e4040d08440e200c0d2400da01483c62092000140d07001c0b11080c01d040d0b000e001c00d4001550b440780210000244851004075240d031400c4c4010100d030600b40703000d09011207078200410941d281001020703c96078841d0039100a03c000c03200072100295040c10310280c0c50440e80681c02c200b50f0742d8400000f10b25150350720a50291900780003e00340400c3c0c031000c200348001d491829070040c0107100b10401001044400b06401201620a9808000c2c0d2951050103d4508403100d181c140c00520810300071804603610f501001d01a1444e00011500b8410794000c207203035034081d0b8050150ba8001065008091074180221241d11911000d00b81e48035445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 629196690 1250 629195440 629195453
    0x15040b0c070b060d08040f060203090a090e340e0a140910091b030f0b101802070c1802040509090a050c1c0606030606092f0702010e10030b090f04 64
    0x26111620130801039100404000341c6208950242c1044800035084540c4c0340c101030760701d41000603414070440c90380300003140d03485552044900c0702014100800c0e10f40741104100c1072204400b240390701180d8200740d644e2040495250394000500782400080990315003003042204652401915017060440d050503c6009400012180c91510b6840000100a40540340100d44038014203a408220b1030310f11400402d00c0f00c421003002c1c3c45805000802d04540d00e9234502a00012035000d4608132180580840000c400c266011b8049503210350f070540c8506860744d01034030904600e920f0001d4900d0f000181071100d810503114231a08065030320000d00410140c2d98419890b0302d41d90310410300415404401410004a011004988581003101004516144e013403d01c054070807030080d1481c00c2e00301001020114804552550070002400045410b0f9050440c1e800d100c3e404083c0c1a4100080d41015101c95030f0b41e00c21070030109429480014029030b0070740500402c1540100803240c1c42da803100401011401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 629197940 1250 629196690 629196713
    0x405011e02031803150c031012020616241506020604020a1a0706090c26100b010909020c150106090807060e0d1202151f05040507020703020315040b0c07 67
    0xe03d110030400082050000c68a05408003101c503c04421180034030404010040041d801b41c5030700d0390b81c040740d6a201c0c00c000361080c40e011402900100300b0403c07401d50041581035251002c0c0f00d5116016008403200113a241e50b8654a0b40c0b0144554402c005004035003036011441c0108040c0c00602510302d09a000151485414070624061848001c6110740c02c0d07074510112041c06a0051741084040e0090901020040e20b60042045004080d0380120005400024845031404840700400700d1142e041c5890003e410200e135114140030002e14040358841c1d00c0e0016084202a02000b4803a20209c5140a41d65000c103a000c030b070502091789000c0c032103601c0c0400c5000951701203080c60310600840c40c021a405408580700504a501e0300800282d0542d0f001ca1844450804104039103050b842d00310802400b510240d4460344540c400c84e41c00c01c1142030607084075510403068010345080660740e0f008641461040c0d01035480440b40d8808200030041c3d06201e40d90072540c18072915050601540c1e80f600320380d9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 629199190 1250 629197940 629197957
    0x1208010e090106060c1b030804090905070b1c0902030f120c010f0c09062a12090b160201030b03070e07090807140f0f0a0302060406030e1203100302060309070902040b0405011e0203 79
    0x907904140701615148100c8480112340c00704095075615074611190307008099420049595006140c4002401c400d60340a40d40303018104c281401000c0c0312800c1c00c00042c00104e4040b0303054003503140d41d0a00c50005200c0f4a075141404200c0540e901c86c0c00d15541e00712110f00e01c42040da03e1902101406003036020711181f05035200350518421041403c51401008640400d0a8014160b0240303840c4c20800c45407007034246c01c0903907266907411580ba00d0840d041070050b0000c0d40ea0000c10040b00d10302640c400e0f000301140d038034094140c81c48181c8880312180290422501c02c00071401c200d5040007100c1c0c0400c042d00050100200d103c1e0440822070008807002c0903031a8451040d40b4440f50b181d45581c80340280002150b00a08103540d9030740d98078004e809407070016100c030114080d0140341c0100341c2c1080100c03031241410081d00401641180e00300892034001402d0300210384617100c0c010403500c0241c4001d00c0640701490400307403980c2c40c102c001010541135803492041c40b00d0f8404050718007a0000291900907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 629200440 1250 629199190 629199203
    0x90f1a03190b070e0310020403060f0b13151206020910090e0c030c22080c010806030a060c0c06060303031409010c020c0907030b030304030c24021506010c1208010e090106060c 77
    0x540703d8040c00c6030b2101c503c030740392540360040c069024019000d40c1d008004a9105e84814089482042c20140481d90701c2c0b4a8690895111030452121049a82c4004a441c603030600400c1d903c0c1d103400c0031000300071036404222903055000805489074900840244e511600c42d1404468403800c3c0100800820b80c080c1c0151a03000740400403420801c8000300390740d846166a90720905e600009801c1040e00314140c81901850700440038441d506500c581180352180070b010700144520112540d8820050041d44d081008018007000300e8000501a40100c0c0c00450280c0d901203201c1e014644c5643c3d41d0007014061103540e07032500d5074401c0403070340103c3c0503920701c40100c030300d00b0b030550310010b094001d040b0020009600d8000040c000c003c100c005032010099030030742200746040400380843c4000c011070b40f0740c41c54050fa00c070162000c03071003500304101580100c06241800040556030303103d100113802d101c405404240490011b002d091199801c1c1035000010310300074403140340f82403000303008004400c0014100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 629201690 1250 629200440 629200463
    0x16051612061a030a03080a05180c061602060d05091218040b0a0513150503030703360303020a060b062b060305030f030403090608010b030604020c07090f1a0319 70
    0x50140c00e01115030b0710001505540b40381405150050605030200c6100c80c0c024038140110360b91800c0000b040700e81110000003810401d00000411040d070b00030f095216020f202c401c10440041e11020003600400c001900045503d0620344601401e000e64810071500420302405a81d061103024060800c1c02c400990f40060006140c801050400c94190030403074001ca410075042d122201241d0000c041a0b42002c6035655545d200e8080545030320808074090001041c0d801480d4030003420b48000900504a0403071140b09813441500144030f074151368410b80142e0080702c0c600052010a00890600041c00c0b01d24500c2c1c0481c00d43c0900341d4800454170130b03003280a1240ca0034210115035000c100a941c00104a0344c0790402f5007006c3d5800c0c0d20854080b000540c40d900300080d86406014118141c0d10f4405000e4150755500052000a400814014450380b00e21400019500080e1041110104003c2c0303000c0343c1d2400d6000e03c05e445055803a17007603009a02410800d000780c000c000041408641c000d151080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 629202940 1250 629201690 629201711
    0xf011205010f1b110303010f0611010605040906090605060a033215090d050a05031902090a0b0a031a090c0309030403120f1e020d050a050403081605161206 68
    0x141000400200003910f001c00441004aa040302510781d16510303965985459400c41d2029101d001c01e00c21101100540c40041c030906004030040080405c0030000042d616a41d507000a09580300c07800c0c02d580d00c0c1d40d40c11040c030038040f6601400344d1118041c0c440c1900c0b13610710343d5074141246400710348940b56103004e40114a0140e00d60f40d0f05240001d0b00d012214803d02c24240915142d20a0320380301c9007032080800c06a02a4001c2003900d2002e02c0e81c0e100c01d03040d1307039030340c40c101d401003503d200e0700c0c0c041560807c001d500c00d60b10a4a4200075081e07020603503840b14501e8a010741143c40c00100d00300d51600101e2008142e543d00c00e04180d11181101000d912511401101c0b86180940c2c7c20050200c2e0120808480c900c2e0702042e410300c5042146c1c0c410309601c0310305040c64503203034410188100503000f0b84030f0101a40d0054005148000652602500c1e00340e9945a220090300240030103c0900611003c082c00e20104024420801c0c9e060340703001130801e00e4032802c24002071264034002c041079103440c015030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 629204190 1250 629202940 629202943
    0x501030c020729030c03090f06090c040c050f0a08090d030603150f020f03090a0b06010516112b020310020a021e01020d020d050718080c04020c010b0a1e0506030f011205 74
    0x954481d86051110303202e003000c1716900340702d801c200d503a00d40d144910141c00d0042d480008a840c015040040030384482d10792181800080e001014020040c40001c008850324106d2000040003105640d586014443c20404012810402e22518400805003008401e0000c103140c000303a868140c03c18a40050b40f0614008140c2c0640200341e42c07810f20040100400c070001c9008284c40d6421440b5400395911079640700010356035805042d503c00700c0101c210141100040442110740003c000041001400c00c9402d071082c030709003c03680400082300416581c0c0c5011428104481c0c200900c49402c00c2d4104514004020341d034180840141d06d0092140c015400e09000a5046a2030050008810f6680d24a404490406048282e58140006203040d5414100691008000341030b038a84c00050000f01c10880c0800001c0e4008100701c3c4500e558400326540d565031041c507074a00610356a040880300c078481c156000b03890400d5901c030901400c0101f0070050030300f0072070403058151a10311314184582401c9040c4503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 629205440 1250 629204190 629204249
    0x70b01080c0102251a04030c0e0c0706020c151806010b04080c061b071523031603021213020114030906180a020406060e031b03060a0c020f03071a010501030c0207 71
    0x2842d20307541604003607681703000744004109590003540c02c10501c035698048002d505d5002c0f10065600801480460001040c0b03030020002000d40e8403c0312090045080340c034044060a652803007600203104205400303040e0520801d0300400030781c200e980c206840c25540e07a1300d841c9500140ca10511000500c05440c0b0b040c80036107910110790204944d00a500d4040b28401d01c8604100300000c00d190700c3d400141e00181101200345818a0148541562580c1e10303203841c2071a0340031450040c15000d1140128564a10341d0940c0315128983d810038120215000140203401c0c1040d10121045041040110750900010126004116034502c114403804c5100341508100811a009511070304107540001c0050b801003041405180490589441e400c038103200081d0040369203030307103038040d0845c07400210300f010b140c0c0c1f00011110b2980191032005a885681d1425a8402c0e401241c1340440c10341d00c40081d0740c0c1c114485002d08400e0034100b20152842e40060360f110280c0c0308130040b0500e4240f1880360448500d854 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 629206690 1250 629205440 629205449
    0x1404030b180d0201020315100903110103020f070f060e2a01121e1d0c04090203150708041b0605030f040c09020a0201020c06060a06201c020102070b01080c010225 71
    0x503910750b40b002d1000203001c0d610139929040b0baa100d9510b44c90b05403510030312240c110a116261110220318680e641d0241c0c0d0300468086060507070074840203610011800c02442c015210b418100382000182c41c24008030303000405000c2060b4441c0e003400706800203216800c104e030300a00d0a074450741d200a00040380c0b160000035001300a00d04102900c550788005504800a175865602c0612403020445610001220010b0a410a941c0520b01c446280d040070380c02051550f0025081e01c0d42c21011100c0800f8801e420ba445400103800a0100405d02c002040c1e590406c1c110314a14110f01403034a03074010032501014050140003400da502140c00c01c098541030380001c04003074100703540702c1c402c40c103000c0d000790000f110070f0b44035000e03000010350149400038518080e00c03159110302050f030300d88900c1c00c4c040d2800104011110b1068a55101071081e0400c5102ea80c1c500650025a0b110000e1400c886041d0060307000001c1540415051242c680c0c010071400c0071101101c8045201c0c0741c0300082c040c540e60545d4071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 629207940 1250 629206690 629206693
    0x2030604090c081b0909030a05070c1a0a170403080f070905191a0306060403120201060f090915060503060c0c0a0b0a050907080f10090501020702040617010b011404030b18 75
    0x40010340354101080c0313010340c07049042d0181c80c450314400c1801501c050403210029150002c011000300180628050003941c0d0150002000d50341e11582600000b6510318140204003c2c0030074080415076204400070390202004a441c11039062070740c1d004c1c00340b8001910798049072417043c0000304801e20451f1410b0082c03000402200c0340e02060003580758412128000c603030010881c0050b603240300111404590040768003800a074a41440c603114001410404000581155250100003c104520b02080300103480d099200003803009561034040340503ca2005a202c0d49414520704010a503400305460ba4010720000c00295280042c100060a003400000c0040407a59454144000b003541c540c0820700c00c030a84011182c4c029142c0140c20342d141d01c4008000742e1076004050344600d0401540002c08807900c650005800c2a200e5400541a1500e6401c0204414011010b0310b40c200001d000b02d0660f03440130b0a00c030b810100c4016214085114a000c084c14010106001c00c0100c1d19a01000c1070560700f960 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 629209190 1250 629207940 629207963
    0xd020c011a13090b0f041a010605191e0813020306040501050f01080a120c06270506151c080f0706021305010908150702010608070602030702041a130203060409 70
    0x1240c1220360050000914000c2c2c0d80c41d120744002e07125030b10404000c2a000a6020056503c50a0880071108014000c46000c0701e0300000000c00c0050300c405901901c03040c0c44403900c4020704a01c0d001c40c065404e50070010031440700c0700f0301e1071602d480502e031240103403a1401c80c140390740d00800a5803089a025009416100300802c220a05c101035000300c0c050055240382443c5640e8800302966100300700003003e03200703200401074a5912030180f9501e00035140f0a46022a5010851400b115600d18102c204400703540465000c900b0444207010003940800b600c1c894882120303c5102140444981c0d02501d00c0e04130b9902c0003102030107405000d40c1d41c40348141c035045985480901c1c103030000c1d4001c141440c20b6003120041c0031901e507004100300030985011030300a10300101500a14003140d94090100d4080d5580c50070046100341040c00200b005d4281c0760001c594030300b068818081140c8403520020840354030790102e0b0031296034064410369802c1050301c01584a4842d00c00040003030821041c000c00007415074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 629210440 1250 629209190 629209211
    0x60e0703081b010203010b0d05060120100e21070501020d02030117011401150828090302100908040b13050414160e0109051e0402070507050a06140702060d020c01 71
    0x98005004004042e0340348030a0302c50000216003030340004c1c003c12202c06030a00a210701c3c03504540c0480c0d407040051402d90100108076101c807014110300c00d410705482d00814081c09494949000f08000c68513618010008011036204001698001400466061200007180400d228094040c0c1c2d9a44c01882011562565a01222400c0d01040e9035003489035420025016505081049068101c1d446425031100030401d4810482c0c0800d801015501011024205145a0b440c44008100c40703c06541001a9459490078042c2c80c0808000c0406800c40c00c1c50260340000708402e069808640381e02c1d4407940c8032002103812881d00f01268100541140c0360407840500550209000c60042030321448099400a1000c001c0701c10711803030682e2a0221b00c2c0345404100d582804111606003e0107104030300610000800009d06a90000300155a01d501500f0300340924504007100b80024082030800070210400c2411031101c900642c80080c0c0f054201180001c0c590a81c1d0b012503040c0300d20107001304942c8500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 629211690 1250 629210440 629210453
    0x30e010c29061c030c021314010806060a09050c0703051c0f0c0e010804020f190e1009050105181906091d070b1c05070c050a0302210316030504060e0703 67
    0xb1111180300d901e43d0408010707042d02002401c104941c16031303030f240202c00c0c00c1e03004d218403c2c00c0c40030f6107481c5036aa40c1e400303c0c46000c15100940030b0008180603007800c0c00c14504109005400b50400040c00d4034100c14054011306020845001d943d2500b030298952544805a40c0c05050702214200c1c1756041541c0d60703030a00540e070300c00001583c00c0d8440300c80d040d1003032004548194080314001c0d0805240d0410420b00c2c900b00300515544a01d010700380c440d9035100c81911540600c1542c0510b22030384040c40078000400c0c2405858094981030ba030115010805070030380341140f0406030440c80071030052650161a0f2240d500701c40c002e804000c80500c141245a00303001005110254001c1450141110125040d03202e00b044500d45030b100c000080c40b140040d82c400009040181c2604103020308452204009181031000103002c0d40241c02500c0c054400d03103000500c9004410100004460810410019202c816200807941640f46800600c0d691940b40c004010907000d603400702140701f0040c00004120740b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 629212940 1250 629211690 629211773
    0x9040f02031c0f0e03030c190506072a051501080a05060604060609051210050f160507210212041412011404173f0103030e010c 56
    0x10941c1190400d07040350340036000e0381d10402c040301d0028207412500360700700d4401c8402035004440141039a107000b1300b1188217460710f41d4000560503e1b030f464001c0700c01070100a11140b0f51049280c14010303e03c000c20801910000130100c40300d011803131a01c04002c24400200320304c0103141040d0f42da50781c02e96100c1c0c0e0f40380c1d500c5040d00c00440b0b0318403c10f030004185084c280a220103c0710b50742c46c0d038554107003410100040b11903101900c0b00c05128009034000700c0a0385024845c00399003020b282381454200a0700460203505403030500418804100072140000d500010803990700c00750900c2c801c80082c2030100072400c0280301201e0380481100494041210f0b1070b025283c6400803002c442d1544e40310b415241c09402e0f540300d000e91058a042480008020610504c001030000e8894520980f401e00c00d9100c06024840c8409116030a12069000c4408032040c04940b030b0320f00241c42d68241d007a40c956540107065510094595040100d01d0021404101c01e40080340e0705903c4100d149030480b4143c1508075281c21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 629214190 1250 629212940 629212943
    0xa0605060f0f010e01050a0e0406031101021606090b03042f010225030303020c0f123403051602060c01090209010b040f0b09060403060e07090b0307181a09040f 70
    0x30311007a407901625016001c114000d0068492203900c00048006441036041440d03600c0c1800842c005000380c65403103114205c0958031036150b42c151803610340002454400a110402c070b89400c594024440740750494508821030f0441c0020365a0303981d682c6400441803c040c1442641005051a0700146540c0011103850301202a8200c030051400e14200400302c0b90318020403529010481c5062010074407940040002c4040c0700201c811403000c80a0251924207501460800881d022a4003000440c6040701600040c5185c650340c00d4010350402c1c092020860301c8802010b01800107a071241540c180ca0000d685250010305031500c5917000a405070180603203001c100d214070300c0c1c40c001241c900c10031000d44c0c040d1410030080b072180b14100504207100d944103206455001106000000000c2c01c20700a0300c0d0142c40754005051118505604601a280d4134156a8400d4120708400c0c0700004421010100e000071202d4003051041d61101c02d00201c002000b80c0700e4000e1078100801c0103102d0389071034952509 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 629215440 1250 629214190 629214199
    0x21210050321091c0821070504210302070f03080409050105030a030c032d021006051f03050406060306050f0114180606030a1b0f11030f070807060e0a060506 69
    0x160005010b601c00b00700d60341d0301100103a0501c070601050030465582465910b500c0006481d04500b61501041780d0000760554284821078000c80842146203403555170810a5802d100341460b00b000c2d00c0c8400c40c84001031507070802503415a02070615100700709030b100500346541c0d8070b429285c9070b040c408a198014003400050908040000030a07003000958140e0080d09580d4881d080c0d051aa001c5070b0300c100c01c158800a4403038880d00e071400382c54061401900d91130f00b90010082d0b20341003403189003500e15681c881c82c412804000f100b03080002c02904001c0a103007500d000641c17960360703160090007004c5c6500041c1034546004200078000d6014004103060b501f220800300e410130010fa0402c034035101d030b0001041000e041ca20208a041c1402006107400c10401140855014550a403020342a1525035030040000c100345005000180c011544541e1064558003862070320115105804461048000003461400000b8045c02401862317803055036a01c010f0070542c0e100480d0703801d00d01d0291100b542c80b60700c42d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 629216690 1250 629215440 629215453
    0x50106050c15130b0a02091c05160b04153f050603190305091e0f0105190c0c0e15010912020f01270b030a0c08010e04150212100503 58
    0x100c0c0b40310380500f8494503c0e1207482d1141e07001a074410000308400b42403500400d40a20003c1901d656032103e450425600c150b4103400e050003410203c0c0381000c521929141e420a110062084500007002c45081c1d481c1c01a96007400d1108440481d000c40200c41074041c140d21080e00070400b16004541e88503801000480c3c0c4450303044074400744084650542e101030703140d80704180040b441c00c038000e0603d65450080c2000c0341031204460105e4a0b02c90780c0400300c56003c1001d4030312001442c00c0103407103141c40000c0c40c2c014140540c103d200319051140c000b245050100c0342c2d10380e01c00c001105450f680030705810280d010260404030b200030000940041c10f02c2c0810030700c3c000451520624103005803450b8000f0898100414001e0045d00c100c0c034035181000110380581404040c0d0b5915502ca84001c01240320380c0c0f50b80e031902e030200000b220b0300e09402c0420171000000400920702810186a08241c204501c2880280803210400c020700c240540c481c443c40c0720300304004030050741204a2048070700903030a4544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 629217940 1250 629216690 629216713
    0xb04090c0f08070207231f120b01051e13150f1e0c150e03070215070b1503160803070203010e012d09020d08070302010c0801060f030519050106050c 65
    0xb001603003100c48200590000300200189150030002d195445800c0e08141840880c84d4085030090071511080020024511070601e0b01c99403120809007050140d2504220000315000002c2c5144550403089141e20801072401508003034000445010640036400c6d06045507480d84020780e81101e42c045140400c014110400c02c840c000c41c41d081e903201382e850400b46030440c0e03084140c0e01c400d00c40300d00769a00514007447d10381c0300d601481102801c007a40303002561190300c0c4c0d00c104040507641010310070111a06001c000b00040e11001150b811a07480c101e06010b0b0300c0c1c541d010034a03004010300089038500e034084000894140c0400108556030083c1c00a121500c00210850b00361030030076080617010310101424807070300741c000003400d0100070300003002160000ca540c001812603002650141c2c0c150000141c020201074092090049110751400d24954661400001601880ea841d60803014540c842d400102d07071024911104130100701201c810840342d40c40d1040140250840a0340408078401c1c0e511140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 629219190 1250 629217940 629217947
    0x7021c05030f0103080a1110060f050a0312050703020307020603071116060509060c0a0b0412120507050d09032706110f03042601020a03051501051809100b04090c0f 72
    0x78402c15140e072a070b50340c0e64690b81d52080240d100701c03030890801c2042145035440701b4080c40300d801012644070340412854180b0388485807001d121350100d4414040070104100140f0f019901c4080d081180c21700395260040f90400380e01350701c14404c00a5203c1000420820000c0d003001c1612049092403007100c1100c0305214002c82152003600408001c40c00900c05007005141c401e00510000a189040d03404540d907503a200344050308262400c443c1c464135100e07038040310b541c865039083ca040c203440390500c02030900b403602418078440c0700c5c00c0d940c13040e4507601c00d01c2c2450f00841d44401c800b0b1448075290b1784140b0307008224150384258020140000c0c0480207852403001c0c00140c0d01410300900001c0d52038146413590162004c601d04604604001c0c441c0d005442c126000e10142040404c25240455103103442e8100d1072014281084080c10b00609000500b90300c580b81c4816a804d00c002d445964080c1c450007001e50344010954403c0014040000300440d40c1301d41900701c504842c2d025111000d80b060362a100f41e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 629220440 1250 629219190 629219197
    0x6030303060815180a060f05070305060a0f050d08071203050103023c0d0c0e091c120b0a12050307060b0d0b0417040f06030b100207270f020307021c05 66
    0x1a07502d100c43c00f0400c0c2c0080c60320083c0445000c0e10844100703000c00d565050075a14000e994440703943d03451003000889a0540079071540030700101ca6482c41507003001c0222034812614028035000c0e500c4409210700304005181120b501c41d8000c24040c0c6800f40c10ae0004000d05000d0200301e0151000d0b5048620303035008121400c40c1d8588496220669003c500c1080c198203883c2c401041e03111808040035000f042c0c2d080481c001a02074048054010710f0500041c80ca095048410100030b000c55400c0c3d0042d4941c810841503600360001c50114000f40e0074000070302d40c000e5942003c6000c000c07104480003000400002089a58070909062142c0210700c8200443c0c0401d840c07014025211100001d0002043d00081012198808510b107040c0390720f4403a85994885550401c6e004241d980d05000360314541028026920503041c4010132051341009100d4080111408850099100f096299035407030303031550006101400295400c43d2a071418040c020340d541180318903d00014600030303d40b00e00c80e1260f0101c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 629221690 1250 629220440 629220463
    0x90e0a0303110f0403020d0215130317031012020f120a2105041509090504080d0515031009080d090602031b04030b06010507110a090501060e0f0a1403031c060303030608 74
    0x3e8604145c80c5400b1711a10003803640049a00030458003501c1d150710700c480042e103074024405040000340c50941c030740000d02040f64074500b00c0b00b905c203004110140c0c0c1003110751300c02c2e04e0401c00075902d080064030118040d14810035070203500c0601d03540107540030000001d40d400d40c0f90007203400c40d2003020043d40d489118074013a034001b0001081007006100328242803a241410400a1401200c170701e507902031140c111340c0e050f5812212240000740b10b02c041c9440340200358006516002c1e1400307541110000030350310030031000d02c020b4032500c8c0d0b40058284140c16090301e10801d00654288928031052411400940c0119803841d0030b407407050300f010034920303d2509403025642d1090a05030309865a40055070141c03c0101c04172a41c0019900442c0303aa12410843c00051034000300100b40c03035040c12000351210b0085000b0300c0c019603144e10f900b1025521081c2d03010031500c00030419404244a04040380c1507201e06184000c00e8100d80420542d44a5158414000c0301d000365401c0240f035031034200103510380c5c54544a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 629222940 1250 629221690 629221717
    0x20a021b0a030b060a090216150b030703120c080d150b0406080c030a0e01022b0b010c0f060b0303130504050604050708060f010e19140607021f0504090e0a030311 71
    0x3003800001c0740d80f15030a42204000740340b502c286a6480c80721069030b2020b10050452101041404c04001c1c0c0d6101c2c3c4480013080030001c0c0300141d9580c01003030341da0201c0c0c0705c0600220300c2140d100101a010320801030061741c00042041d6200c0b0390100c030401800000e409420b094691407800240c05582c1426038080e5106561001c010340c4541007100190380000d031084208139503d05640712041801d2004254440030300c0c520b2010541c19000c0c058050b0702801c4801442030a05144003003036039001211420b01030340200060350242080c10031000a0510842c065010300c000500d122004240c2c1da840404c558040758180710303555801051105481080c2da160f00421001000302d1010320b441d24510800c001d043c980a901600441e0008000000cac410144000442030030303090020990840e17a6000d10791050741c1c003d00c2c0c908158081200507081c201c80b603240010a8102ca05c042d407160084070010000c010042c0140c4000503505529082c1065088020a2402c014008500186400d580c90040c890b032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 629224190 1250 629222940 629222959
    0x2012105040b160504060c08042c060915120c1504030501051536011d06060712180e0c120601020601051003110f0c01060815040c03060c0e09010603020a021b 69
    0x204142c03103a07d01704400702c8007000c082c0004910884c8c0f0b8400030032b001800041c0d103005100c4030750500100d0b402c00703080315001c1c030803505c104200c05501250891005030180e51048002d040d8451450030200340f852016408802c01100240040b0940040c00560380990700030001c540758280072030140d0003501142d540151201510f0b010941c515040c1a84500307401c900b0b07982458207090081d400b003100b60402003540c20600c4c0384a035080701d40503078a640480207450300c610b4032600361222103661480555000400809004800c001c0030180c00d050014040c0640150341414009a0150940c011800c410400038a003400904290300c0001c600f81203440c041c1c008049150030b00b008401400e0700d4075031004540d0080120381c02c4402d805005001c078420240002401508001c411401c2000030a032110031001c240c414400030810807200c1408480e03000740000380c0d86d41101420341e102007540b14495070003404d00000240030342d056002001300c06555420f81da01c030103a48510706070b510b03424844983c0242081 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 629225440 1250 629224190 629224199
    0x41d0f060f060d020d1a0901020a14040308030f090709110a030e011509110408060a1506051e030a06050d03090806011203091719060e0105070c1e02012105040b160504 73
    0x1c840c51901c03240507003034181440d04d584101c0c850b074030007c2d0380e1005a0b030350000d1807031051603006888003503100201c1000e601c0c06103140c89007146404080c00c1c9100314183d900115100c0041001140020b0100038001e20014642c0729401d03000780c0000d10031401290a01d40c84400c1c08406110b43c26a00a12600428000d0708011704d440c000d01c241d542120b919201000701113164042000668410700c20404046402c40f50000340104541c1c82e68000c0d0300b403084c18041132540c080080d08401d5400d02c1606907a03280c4d40c811074100d02802007a480b4a4120050f094080c00307159000913170400742c440c4d05049840341e9036250035014890142a0740a000100d1082c000e0100079909044000403d02c404200c5003180d19412145504145c1000205c4201d5501e0b10302148501003805005d5000400e03081c03540c5610001d480744003001400079004034042d80c0000b01c00d41168082d1030100c0040e003002298184049541c8240d05c004c000a41e010b54072404050006505002ca140c8624000c090581d6100d0406181 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629226690 1250 629225440 629225449
    0x306091f0605031f0b031204090c080708011205160b0c070b0306010509041d030c10180221072607050d0206120c0702130501060e032a041d0f060f060d02 67
    0x10f030080400c4180e262480211780b9681001084c84103110030108540e150307c1d2810003000c45201c0e928040c103100c850800c00c1040f54100210300e0441d00402c000d002c1c104064640f0030f007403900240251450091000000c20107400710005041081203500490346056160303c0080d4507804100da1040c00604e04000020103800c284c3c02030b84907684101c000082d0440d000480c075045030841e440b001107607440020001d00b0400e0b82e010f4604603d01591200109210030740205090281b200783d881d03808240000d20311003c40341000140000c00c00d50b585503040914019240d1105100c20122a1851042c800c010400385051800c0d8080d0703990042c00340d0300d8a001002c61640002008100010b164024403d050240c4c54241c114400c001c0202000200766041c0a00a442e540784110f0581c02644582c00785203945040d41c1c07158030650340c0c08030000161040c40b070004001d0490700040e404540052460300129402c0040c91005405c0c010041c3c44495545c1040d140206208585443e448101341d50700b440075041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 629227940 1250 629226690 629226733
    0xc090103150e0c0901080c0108160f080c1608180a0e2701090b1b0c10050a11120609062d06070f050a050c01020a03050f0a0e0306091f060503 62
    0x1e03090300703803107a610f409000141e60072400d91000555800110300b03501e00f50fa1081c40b9039806000b03414030038081200a10010182040c48580a0500c00000701146140ca85103003954160b03401d2659140f4860704030700c3e2081c030f603811103c030248280c01041c59948842c50403d01c03a00a070f0b40c00d04100300e00b03075440f0200914003140c00c0c103414440810598114130301900070f00424100038012040d50f040d80c14041c00b4500745102c040100d890050f03003440100840c00000c1000d4002c0044800049026210440440700524000c0b2501c0006075002130306500140d00707203036002d00c40c40301210b460b0b4050390b9050512042d8070150440200e514041000780e000100380c2c80800c216001c01400141c14103451740e540418441480714256500d034441c0d026035040040c104201e04d000c090a1001d402d03903410300c0c0d03409002d0707004286021013050740209115203501e1003031140c15004003004007164010308002480c0c0b40c60b0f891191003080300c116048803201c0c85002d03501640301180c001400030a802000404100c140ca0b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 629229190 1250 629227940 629227961
    0x1090b0135011e12030f030b0301230a050c0f0403240f02120601030b10030e0a0c0f0608010b1908150402030c040e0f06100f09080d08090c09010315 65
    0x3604084800320000e07400c0c4003640070344002c003403040b06840c2001c12038160000741c0d805581200401150300c0d0000b640101d440101a84c0c500b00858100d02070030020380034100300f0300c8001d070f01152174400068886c0e42040c40c60084000706002c201a44880740164114424500000355041f410082000025070981d01c0340c4c1d03440c0550301c00322000361103c42c0c140c064484200690304500e801054144000d9040094641c004100342010030400f42040d0118904000411542e41030566401d811a8501c1301403002c5021154400c08141449885281d507551404650280034000742905001080c0030100e070b42120401030200004030010b00404208482095000300a4542c64036000100c001c962510b00146000c0c80340c0158241c1c40301e05254510b9081c3c00020500c0958091440a003e8243c03504949207100070058604050f102e002c045054070040080e80c4005c2c03051043e5030400840592110301e0601400607903050719002c035840010080345110a02015102c0300f400e03103030090a441140e102e03114030f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 629230440 1250 629229190 629229257
    0x206040302060f2209050a0c080a0b041d1c020601061409130603030509030c01080408072d1b05030615012106030b0a0e03070b0c0a0c20040501090b01 66
    0x3142290b4054604c02d608484c40e03c5200804e005130040c5004044c0c2c008000e41041007200300000d002405600301420910401d943d800c940000342e12660042002c1c0605901840c1c0d07001480091140c3e0b40e140e0101b804000c0484a100452003480459001d04036065a95100baa92500d032a110b50258010f030440303035000c0c60440d00418981c116004d41c100a5020340c403415102d02d076035070505040039400c884441c10040c9440030840060360840c1620403094018000c0d03000e5441390505000d41892001c2c4a00141d804141e00c0003c000e034024000d0482d11131002082d40242c4e03100c0a01d41e60300340a50310205824075065140c10a5446425840181840c429041c003815520b11043c000710b81280e0002d44940320356004012071181c0e24010450015108801585841c4280d1620030051001030011400c6103000107281801901c204003148800c0c0d0440d10b80343c0144a14144805040e1030740c49038900541c102000040c61006512a40030811341c182c480c000400440b5000c0140c101a100461060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 629231690 1250 629230440 629230447
    0x703030507031206050d1a01171c03020714030c011835040f090e150c03040206070b0a1b0f0c0b0402060d060b1c0b06090402160501021818040206040302060f 69
    0x100e9580100e140c21150044035a451010010034400c02007c405800005580c101a0b080140c152000501d1802c0d02c590110403000101807050110080d1103401c20181032001c404144901368000480105860004a8002c21404040c04109030710029019000b0700f0a098440c0d010095404484d280800085000302e0f0404100245a0325a410781064000301e6400182a07428002e82c5500e20a103010216150000c254400003070191000d500720083c049052400040042021503c90f182071310341080d88200420820325041c1c103403030010007000401072280301001148103d8240078610048d0440e0183d030b10060348400f9030306ea011145001600c201d0700003404100016180d00b007886100090418071404550300d0100d68aa45103401403400741c80d00741c9280080d240c0300c1c0e03035603507040322514981610050f8455070680001c056031421743c0da000c0c0072940009005408076114100503105072030304452203803c46075115411000b40000303d60003034204a04001c01e0016240c01d00250282c02006a4040d16 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 629232940 1250 629231690 629231699
    0x130507030203011e0605192d06050703020d0c051b0d050105040f020111060f0f06010e0901140a0b1201060311160b24030a02040209010c08120412020703030507031206 73
    0x3c54a0142032944c0e80000b0880c80c00e15050319003c0c80000b0441120900f50402030f0342619040c03115188075407040641c3c40e813843c00035040300d0008104862801024007203425900c030005800c0e03900505088005000d20b2000c4d010b0503004008840015800100401c0d400c0c0411070041890783c00c600406038001c0006441c280060720174068103114900c602104944001140300240c0365000a400d600c01c03a07001a002c00c482e0302e00a0b02400d038007604940007042c4944580d80160f035002c00a104041e04101d0403000402c0685800b5466880c245054608000d8941d481c90019400d003d00031520144515000040144503c82e0700318196503426500054506040540c610403c1c412182c021180c542400c400c02207805023041160401c0e40f041c541c401d21200c00400045e48404c5445402441135601240c02403542c1d2261020340d1040390321a00241d603c031128901c9007030610003241c0c11207202070f40c0e01036011103d10110b600d00450b035058030342c281054803542d070030f032011904214111003050385d41c0f03000038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 629234190 1250 629232940 629232943
    0x1c02100c230705010816080408090301150828060c050f04030623040b0720010c050304051c05030a0203060d08040311011d03070b07140601170c0a0608130507030203 72
    0x180068628455000e401c40310604203820a4441e51181e41030080038001c00907440b01a0281103008000c600d040141a41c2d0342c60454214014100384c00e4140d0700e010400c101c0c2e00034102402090310011411248002c00c02e44014401034400001122a2040051018000707111038010340031140d100d040450401011488001564006620545045407103140030302e0306168030514030a5400080c000e1020901d4540c8901c400c0d504094040c901708658041e12200403580380e0700e00020301c10010024016952520301c0186990810744050360b990188561801c10f07408404141030060995440c2d641c2146d0b1111402002500010500742e002200f05000c40009901c9000400295100f07041e640140d0041e1000185805211b01e00c08080c030340c2c040d00300c410316900005d00c1030855055104003541c0344030b0b900d001c02051071000c0400e0014850b04001048041280ba20030f8402150310f41110513105902003002400c01d424820380000c207140b130340410500e0044c84581010903004800310385000c0d55035400709 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 629235440 1250 629234190 629234213
    0x30a090f0c090c0815010e04110a020a0203160e1306020f040f091503170d090c030f050f01060e061c05060a1e1a01030e0a0807201c02100c 61
    0x3110045454075042c00110414412080c0c1e403d582c1c609500580b90403042c59011301c000c942c40c2814005010884c21450b9141d41010b07501940313880d0f1090315518500c60203555607000200880c03090003115402591680450340c2c0c0401c4580107c5000c1c056216802461401c041800068440c3c0740c01700309103c0d141125030001c00040501e50100183c0501c1e100f0000101c6885984601012100e21000c00110303420141c611400061070400035a10028144080000d00407203000600c4001e01c8100001406000040240c849008030141d461b01078801c88810300b25001805450b01f240034240c085040340c10b192040c0300c06242e64141a61074084943ca81528010b4101ca480505c25281d803000c5140910b1a000300c1808086104107000c5003100300e001000a2400c501e01504055845004070680e10041062468030364110141c036545840700d003044080f0041440c01400c0400002d09240c1e00d608000c41c503043e50309000751a40c15401c0c0650b08100510b0001d20041d1b0030000c0340f000304408501c805051 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 629236690 1250 629235440 629235443
    0xa1809060e0f0105120604170c07080714010f09140409080c010504060c0e0a120812040803040209010609150f030209030f1606090e041104020417060406140c0f030a090f 74
    0x10200986898002c00c445201d050300071074081c460448000759180c200041164206034002c8050a940c160668000f40e14059050100364034803803c040010000c05c00b04121042c0c1c0c00403109100e62001c0c00d001514000d60400d51880080d0101004008052440040c0c170000c0e5002040030031304150540b140f1005402c00b142590041c1d5503103084c8030400c5a1480f40d5508039006040007004840721030002019081503200d8001e011402240c18004c02c18044205c450074a2101c050284504003410b03c448550002c4400b203015020940c00800c185015211741c0003246c008215107041188024000c84848100130802e100b41a020300c140080c136641400101c40060310b900c010f00e0000c2813000c001c600740d005944618107111608100f0b105405000c508540c0c010b4025000c1e1004111020100d0000d01c941e602000c1c0d21440d03d0440c1350000c0000c142c960044d07000348814040c1c5c0c1e446200103c182c10007940c80c188039007420410014405034480c06940e0040c2c8180d80000d00102c03645030403090b1030008a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 629237940 1250 629236690 629236709
    0x60106030e03122e060f081902031f08162331052214060f011e08030315030c0607080a080703020702033409020c010b0102010506060a180906 62
    0x340a1401c052000e2003505142c074503c144c0d0300780d916080b000b424216110386e502c0200540500003d44d5290043d143c482c403000c040104640c0c0307240004850300d045601000c41071400f00d6410f00000c004d540001c600c0d43ca011000000004a843d1020003940e840e0403180719200700c444141a50155540c0070040a02c0b59003419070400c104480c8502031a00c2c1d40440c400c501d641d0b00c0d11050041e22241200306895181c2304038402a05076500c3d0078000c0148140c000d903100184242170400c0300400803106000d04036407100c203542c4580d500c81d014003507400d1000e000b03041c8954400c1c0300041024505080a800400001c0c054680705100d103000701322140e03c00d050654030804005001900b01358450000d40d4400420b150441c1000890381c00241c40d01c09001c40004036410000d030f0001240d10841d140004000d00d00101400d495a86840c48042d400003d00ca40842d440c0c24000d81c6554010f004035845420002c26031460b288100e402510111500385820400001016000c21940a04c2c820200030f001c0009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 629239190 1250 629237940 629237971
    0x90108010608010b1c02061b030f0d0c1b170d020705010b120609070b071109070306030302160b09040504031e090f3203160b040e06010c05060106030e0312 68
    0x403005084d110904240b501030b8a4002c04070404a0103902a03c01c01541250055514020b25081c0d005100740900110f80314003000500d04400341d83c01c401400205e03003000c414803003140349440c2500c2c801c00f02c000401100d284468818000354001c0000000e5140c181001802d005c99003007400304981003a0003c03242c980d51030000405a00d0310b0342c11141c84040f0080248628600342072078603202d5165211301504a40040f595608200b40c0b2031200440401c080c5c00d2043c1460800b500802810241c441a000741c0622101744242039501c0c4030140c02d803100c100c00d80d0b140c940050203100013404010f1003542000286d12054100c2c400e00f1741d8081c01c00752141c0c0c2c1c002c8030038180001d45030350620341e0b4081100641840e0401c03400c580a050f03681030b1a0304203901ca076503071352428001c00d00f054580841124032100031100411844000009001074035900f1290740c055948440043d510311b210044058080d40c850380041011605c2a0080031a030580c510549003403800156020b0500d04095424551140016 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 629240440 1250 629239190 629239199
    0xc030204031b030503160f020d08091e0f060708040f03080d0e0105040b04080702011e0309030908060c07020d0321050402090f0408031512030706060509010f0b040902180901080106 79
    0x10440c40107030b01c031031a00904140c2c555075903070f0360b60302c507601c89030411407200c220f0358040c0400c0c44d02070113419402030001700b10300c0c01929020402d9801480311350301c9191144900c44401e0340c1c0e180c041041c40805400801d03a0488482000b006400c0b240301207514800070000402c041d601114101d0055206010540d29402040350810954035854104030560303151808020104001034000750b001908002002e903103d100c0d0004a405030039141419080c14440e00250f08801d51643c8603013680360080da22041d1a42c2c980d8011600c481d402d855078030b8912400e000314405480c12684070300751307244a410300d1a012203000c07060003480b103941160706001c55622401c200643c10700c0d0055586c01094000411003a15042ea1810a00c2c0000f0b00158454200380ca02401d55032584034140803002503800450b500e403069490441c0242c5510b000f105d0041c1c5400e000002c40c801a404881c09680b8800c44039400e00e41805020340007504a81c600e540c000e80f0a02031746005403105001d0902034131804002081603402e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 629241690 1250 629240440 629240453
    0xd050f010b21100e0309040903120f0e1c05130f0302121f0c020c060f0d18030807080709090c02061b040302060301030b0603011d0c0907030c020606090a06090c03020403 74
    0x241020542407850050380c0c0640b8580800d07210a080301e60100094a55520003210f455400780c00c1915400a181c44040300516801c8100c9030f481030310104041c083d841d9915002010b5403400709018140d50311a05511548901110300000804203914145040062060b070f001d0325032000d540201925050550240190300301648102d104680711401032200c5080e90200506040301e11090003141592403900e20701c1c141c8280001156100c0017030103d6100e0365500400145540025001e0b00b010b0724001d615041c0c08042141620026016103410b40316640d400320645815100071300b4103041054010000c00d614a4901c030300c080c0ca044d9940288242d262520315442c0100000b006407a003c40103000400059a5600403641548e9215080c42000e0f140c403404240501442c0090032100124401307943d0740d0110020740c0440c8a00d04a86000032511580e07010b50032900111041c0006820600c009000ca0030b0802d0101c3e04441108800280300b503a41ea10700c000c6035494a4240b000035000903041090022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 629242940 1250 629241690 629241709
    0x30c0b070c1a01060203073008010f1517060d0f0803090706090503071a04091d0114060a120212010608011505030712030c0c05180a0f0e07060c020d050f010b 69
    0x1002c00c2d01d440c550400401954900849078028522145801c3c0c2c4450340e000741804140c1c50300d94801135012800d5400c009480504240194102c0c03401c0a2000a0700d12180c000d90000a43c2d1602c662070504600f4942c4405a00010030340d030f030421200700c40000025142e0303001c1001c03203008074462903c2e81440c1c6a001d0404c94030703612a400700407601005016030740c0c0204600c0102c84503203410340c2c87d203e501020a039803030103154040c11055140c00360884d258852003214000d00c90b00c0500030405c0980c100d21094110b0b6056804079040000c03040d090020000060b01003841500080c0300c0b010002d80f91211509440b0b403a00504036694441c1000e580c5103846004410152508074054468581890542040005003203030190401c0000138044090016800d10b61014200242640d842e0740122840b034840d4004c00d450300003000e4600615064a400148540c2c2025800302c005064011f24101044541090907203007681d014002d04410300c0002d2040101c0450b140d40040081050301d110700c100584600d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 629244190 1250 629242940 629242973
    0x1110170901050709121a07020a020118030c050d050a02031e1605182205013201030245070503090304051009080a110f0a0e040f030c0b070c 61
    0x2e0620042c41803071500151010165181101500001105424440c0241151800c1016544c0c158000d0004940e0302040c3e03030030744d01d0003038889420f100040800180f04c4500e91101400340007004000f44183c1c68890035001015009004588132003c05400190802440d003106440c003024610348803071980d005201c1900b0741403c18803103441d59860040411302180112441d0400002c004000941c40e5803005182c090030310036405446048502458450700814502d480e03032244000c110341020f49580a0b407504454a84d9031106060503074a59402d0005800101642c8100034280c40b00349501c03240043c200d003c25100f500c040c800340410320705d901c4040302409004402004010010041810380000448003112810b6031800c55000200c8822500d01d1441d8200d200b241c0103019400d020f01c103004a04d01c980c01c3c070803141045024808000c00502480034030070110040c100b240094041890480d80c00003d6003e8284141c013100e256440e0071210500302d0b890000b04047c1c1c034411081c4140b040e017001055 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 629245440 1250 629244190 629244193
    0x30d08151203030c16050708010504060f06060c140c13020418020f1902030d09030509131e05130b010b03040b060a030309410114070305041211101709 66
    0x55600c004071685034440200240c4800344001002241218124654605030b500b0000340c0301903907150784140e8060602542e041c0d03005814101c2c601100030f010711540f0215a0300c0d885030301d88448603544288058a10a10310401c500850194854a0f207468008502c190401c0000581e52030800104036a40110003051840403071051101e4043d21101d007088558844410003070310300e520f2800c2d10407461442030b0b11b003400510707090840000401d40c0003070141c80e60020854040301802e81780e65900044601c0002c2c20f202c200300d10103d241d582003043d40502d4004140c0761041450080304d4688100d8020300303a0010420078000003c000500c4190002d03a90000c1040780c039142403900c3c60310f00030480c17085401140407110303070840c0c00f880400603500e403880c0590520000c031a140e0300d64200d2010341e04d000e41d080c5000c181c040f2090b0142d42c2041c822909007541c991a5282401e08041112404141341e1070308840e41e54a0203001141030762141c10804100b50b45035200342440554800c40400310f0405090203029 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 629246690 1250 629245440 629245459
    0x4150b1b070b030f190b030109030903050c0f130e120c0a020117100306022b0e0f061605092b0c050603041a1320040e070e0402040b010e030d0815 64
    0x70890030080e02c5d00144103030007600c105652420f6041c002c0041c0318841d50715600c1c1400c69020150070540e290704403800b40c4203542c0300081504c140203449900320401a80b020000107810410183d03980103510780d2888104540211004944040240e404980341c100c065000b0740e4000c045607440124100103c00d14443c0100303d081c40154080b402540b800b0060200ba00890f0602990308500c40300c80c084002c1c021503c49491806501c83c004200161030344005d40110060180c0c03140300002c969000f15a106003d2500f00101401220240c002d5842d035648070f80c3d8011a1030880c101200001c00d2038000c141e20081c0c4844038500450b1410440c0d0016006600c107204000100b410360941080b010441075016140d81c3c7d5443c4402e240360642d840081001e00c02038810000b14808903409480a04195807c0111281d803507881995600288915a100001d0000140c01400c058010100404042c1000002207091400083c100405070b0064000101e001c8104000d1070712042c10154000390680d10000d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 629247940 1250 629246690 629246701
    0xc06130f061d01080415050a0f0e010b01270f08010204080106381e070506180a03050c03131217030c0f0f040509091e060f0604150b1b070b03 62
    0x342c800310420906120146000400344200350780040c000c50b82030001046149000c10080e80200211401c0d030461514050f10048041014482d155040340143c40b0101d211411a0008025206454614081001c0502d001418100001130365000e007900070000741e16141410061803c54403140d02c80c4414184104010144035400341590034080303041c818414102c1e45d6010f802950b80300702c00d0402c0100e203150712400101d242203400340001d6441541a5181a2140f0150b0300600401070b641d1503164016000d003c000030f00650050011741c000c501070b603080042c2d089404036a54400d500070110110303031001c040100540e481ca14401c2d008200304090031800e0a019000860080c0007820300c641c0740c00109440415a103409840c001d03e4005d001c0121762500202c455250680d010143c0b0070743c682801c0d1320362180000b10b1064400c03c40074094101c6035540c1800c000c0030f40302c1303041d50720100000190701266603000e1500504241c4d511880010111107122106860304269500201d18a07005205012 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 629249190 1250 629247940 629247977
    0x307020604090c2304030b060409050d0809150403030c12050403091418090106060914010507082101080705010f031a22090605040209060418080a020c06130f06 70
    0x1400d54403003050001e1409000390013521144941540c0d000703894a42c00d028083c2603025001417050780d1088000d0b50707494a846040c40140ca01c100300040054001c802c0009040b4401d075000e95000c1e9001c402c80c1c1d1606101d501c0c80716603c0d015542500000d0b202d0b402a1943e03a00541090001300c0c1035502048903107080d0304c0040804841d0700a02c010780d0b56894026000e9a0b8207141c400c003685800c0340100c0c1a0a0010a05000701200e00c550b00200d00300410000d800c0c624003940001c03080c0c06031a0145405440d03a11288554000c450542c1c184c0a400e1031032010003641032030940680044c400804c1c107981041b0000d0031604404140c50b0805080c098a503400c501e8050b00800d032071005480e00c40d910040c41c1c003644d54000c1491b1034a54010300d40340c03196051005c03075001300b80650b009807500070a0382c99040603c41a5099510030001c1e01c4002c46c0c2d03500000e55448000c1110b5451441038a1500d0040d40001d402d42d4000800000d8250744074406006010000c00d1000040c641c50410185d84540c061854 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 629250440 1250 629249190 629249197
    0xf06010206040b07110616090807030c05092211031b150d140a0603061107050307030e220504020306180a031d0901080a05010b0f0d020405060d06020705060f0903070206 74
    0x40010401d10013151501d40214000c0480360300e000259200e81c80c08903221a550200c506803c00010074450340083c0f550400f1a455003965005041007115509010900125090240401e040004105226003400c60010318090300d291168200c04109a8800105440c00f261011541c0c4002d0030205101040d0759101300c00c1e0401c104400310661621100750300080108020314444501008110403c440850f141d070200c07065900c20313042002034500000a2079400d01820034020a03944c0b04004100120380170b000440c1110a008100e403503150030101401c107007140080a440785603602c035002e01046250070311000740c0c40110360381c0c0066440020f0712019035582c0c03034900140c1030040f061442c010340e0300c007500711540158026001842c00d59580750502e5591001c02e2080d03170325501c0c1914000082c98440000c91143c0402003075050072440a408200040202901480e403000643d60500c002071443c0c005401c2d030900400182009107400d028000c607129004040003916001004404010380e6201e064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 629251690 1250 629250440 629250443
    0x7022b0605090a020a030b07080906010303051c0f2d02031005210d080105031b012109050604030504080f0a170901180306021902031602041503060203090709050f0601020604 76
    0x1058075154040c86600f003854800020350400e0032804080184481081954062450ba42c0e84584507521a203060f07844070420f000080002d1010000f03409061030607400b80114401c00030307001039600c40d98401c60049070760b6040400440e106007000c05004020018025601d2040058154a1894120070041d000401c0b40a42403048014541042c00e03803614400000c0000c90100441d040f05040e80009400001e0901c252403083c49242c00400d1000d0360f2003c035144441040e11344070f00a002040d40c5030000d5407506203082c00c00342d4070b00c0c401012400800000b4001d90094642c1035445003405146418900703880d1801301a540720f1101b000000d500600c0105400f580051099100c0000d8001240e480d0f43c1d081004c4842d083c041400b00501c07455500401c3c05a0726407050030002c44003d90113907100c2c0a41d01c200c0084020380740c00003015081c9074200c880780382c004801010066480e0b59840301240c100b034030f901055501001090022280d2072203104d400440e080e42100c824a440b80000390b031200010300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 629252940 1250 629251690 629251703
    0x915060f0e061c050111091320030702010920150301150c020a090903020f06070c030c02091e010803040603200316050c0307060902031908030f061302040b07022b 71
    0x50340d0b070520351800480342213035102c002480130300b44040d8481c04503080302c107400d0f01c10308011079080140051442000000100382074a80720544c02460303091004c1c0c10040032403042d5500c5044c40c4d8005000b82c14100a42c01c001515008100912014494000d00c50310740c215410404100521601c482511a80035032001c034074003040c1c0d00c01644042041a002030b40310360100d80c10607021900700346d000f1845101c071102c04811100310ba6140002145e50040d084c0001c0e005c0764605000310701508049400c15030141c40e640c113240795084680c8000c54040d00903801406660030108060090a074180210b5100a4001003100450714413800101218440030700442c1086d0070385400d01001300e0140d01a96040008070082da81c442e403280c00c01402410341844124400c3c0070344600200d50409018200400980118a043c11684c1d4100105095900076040ea40d1000ca0101d440d50304c05000d0008201400403441c0a0383c40d00b500b1710501c0703454003121322840c5190400d20001804c0c1013118050b0740c03c2e0340d0040ba = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 629254190 1250 629252940 629252959
    0x30210020a03060b0a030c03050604061401120b1f11010213150e040c09080f011103070c05010e0d09031103010b131a0d1202072408090c03010915060f0e06 68
    0x1c005500610340c80c0c0c40042007000c0030921004442d015403207104144c050b0f80781800540c0c1c03000100422520b8602602d601c031020541403641c0d0354400c0e026040240ca55110000300c618454001030303080c2c14900b0030742d005217814160608180d648085075050002c5a2402941080b0f00303c2d01e404081c900502407600d00a82d001c012440f9244105030b641e44045019000700000c000c6030340c0050060314a801818443c1c4581340c11840c4a001c14414240e40c00d0300c2e00441d50560f00c41e4a0b007140c20005071841a6003641d04e914001e0441d81c000d00c90901c0441241c4c8035441480c2c036524207040407446486c4001c2c400d034542007004d055900d480310103006a540c03403c000100340e40030600030300c44601c064811740d070440c000c4100b0030300300003e0b0310615480d41101e03001c64004950b00c2021440b4542c0d07800c903d0359400c41e00c0580d20f5149000d4881b0b5500482c4401c180c401401040001c00d0071150807113826210401e000041510710046480b07460090a5010742c65000a030601000c561504005080d0078011071a90 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 629255440 1250 629254190 629254207
    0x10302070c060302030907060905030c0415090507030f0c0f0804021215190e07211502070c0501030b030708062415090f120a060f150305062203021002 66
    0x254100c4420035808400890642c1e11108014000c2d0411203503c002c1d403003081408250769008281c4001224001001880c1100fa10014400581482105686d84450060300810491342901801d413044540e03685c0000c41800701c00100d41554004c044800900041102e0301d1415070340a40c410358015010340c4c6034020000c54608042c40c0403d00400e01c20340060b21000d00c00e07802c07020412040f85503030b00b400501c00303403d51443d0381e9110080b034818145c10740c08040780f00d054454180500130009000e09801040c1c207041c800f2520503030348807501c02c81c1c050100c00e0b03082c40b0720368040c0305001d40c09409070002c1030041d0401640c07590f605c0d000b074050144105940c1241204060144800188000c050b1030850140c0084000300b1a0b6009000800d100c1c203081c002c0d000c800c1c10403401d00200b110044005011840c00b80d210100148080510030b10019207601d60000108101405076009602c0340d002400300d4580192005000b841b004202c003541d0f040d5401d02e00102ea40000c42c500a50170f441d80040e03649004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 629256690 1250 629255440 629255447
    0x60402091305101e05090906160e030a060c1101050a0b060703080402120f03042108040608040c050a080714031c14130e060306100315020d020d0203010311010f0206090a020f01 77
    0x10313507200e100400c1c1c0655800722004080143d000803504140c800d4126519031100d071a4507564201e50000e4540400340140e01e1242c41180c0c503452003800641640c4228500d07858a0741514003042c01c882c00b01d01e440e1000481d84400744540303548124481030410044401400146c0702d40b18001c03002d030030820b02001180c10756486401041c0407049180854000300000c004854403038109114000b83e43d00340d1841a200020b00c504a405056070203403a241c501401c000c8195081400a4010307940311017405808a02c549408034000c02400e00a0000c101407440e000e03220080c40d4000c502e15000e508035042500c001c40d000f807007100d81c0d4140c0d403c009021405210843d0754602581200c144200d03100200051284592410540140420f03025158980d96030303410107941c60f040d803200414804401a80c1d28800d811f550241c101030030089400b51424062061100036070300300380c006603040c6a0606100c0381940c2c20000340f18886580380094a2585132001d0029103901e12541c0c040d025065204005a07560720 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 629257940 1250 629256690 629256721
    0x10c0806060d15091521030f20030c07120c05150d0c030501050a060206040c1413020f0409050f0c0a0e1c0f031214011701060e0f060108060402091305 66
    0xc03c407001e490815a500780340b138091303c0e00f05520000400344e80004512000c810f0340c181d4411400425140700601503580c21500354507168640310800003001c5481d12202000d146240568440c80d0045840d1200e030f00c100d50500b0465806040000003250414000440b400d503194210b902c101c0300e00422007035a0000c4003a034421380f07450410b41458145100141909a846681614826111000c4461321b07080180d94a10b81540d000d48a0f4058034410003403c1900d49082884260151080c140b40440e540203405a800582c0340d81c20006010a0501c0700600030300c03405500c14200b451080305818803c1c0e1002880c0b095488100400002c00b9200295407105405402c20f0040c803c02c03540c155030241014640540d4980342100040c001d900f07401720009079802545d065000740b08800803142d01c0c11049000c0c1b04500044c08096540711741d0000b40310916550f2442c4122005050015949040c01c001850b08100412042c800c40c410f02c02407ca540340e100481c0b1000500707441c0003030140c9415030740002c40070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 629259190 1250 629257940 629257961
    0xf020412060e0a051915050405100f1506030e0c0d2a03140f1c020c1909020703050a0207052706010c0b0c0903010f0b090c070804151d03010c0806060d 66
    0x11950042e18030480311750942686940c02600d03812001c08000c2010f0042e40d9041c0e9028015901201680c04200010313405404d1112000c072000601450a014618104800354002004650749560a501c84142403010035898035040703452034200c14060340e9080d800001d40d40d1720801ca02e030b8440514160008910b00d01d007c0c54200c03a881400300d84c41030003280e40c6e01c0980030003003090280c26141652111b950203154012240c03074001c0e1440c04044401c0c01524500000481c032101409040040c02500d60710007441c40303500a60701c2f40c0c1d41c2c451090740640352001c55400f482c02259a20380244031081c0e100280c01003105000c45001c5142c884000491300603149141c0a0b1040c0f4031841440000c0703040c40010261000158028400e001041d03400500300c0302105845d64010503200b0000c2c080501e03140041403250303c0b50f2081c6041940702e0307400d04248054403440d500864103a00c12a240000c0b00148600c4101c001c80c020b001c11040c11200034a1000040c0c01c1c180603400104254019a8554002c0c90603403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 629260440 1250 629259190 629259193
    0x703081b01061206180c1401021504050d17010503070603050a021315090e06100318080d09030e4509030306040b0d0302150411040e060a0f020412060e0a05 68
    0x82d450f18440505410709200403201d5a151507a0b41d408601500c904043d0950018468525a0301d040c800400c01501c4087d2281140585491400303010613010700e950007035005400030b203a0000c0f20700b0003074203031a02c0d140031540d10200e2000400070356600080312070644140c0e01e4085625100e0014001c00390040c112402c400505802c40070848000d58040b0650f446980c3d60351142c0d050b500c0303a0514618000351383c01a0420f407100d042a0000f8040d1300710200010691000b0f81007610141c42d9022107400018000d07a50f80d4032001c6920505901080c600d080000c1151f500d800e0f03007090f2860002124540030f42920307004001618050200c030f4050200c9040b4410325000c412468005100c0d526a4001c4920324461490080210903508000ca000f41040750700d07400400d5094124900c166010500910489180c196002c2c14500c40e25a40190941020f15900a158505100f2880c0003500c0d1b00710f400100d118810b00c000c0010300e4241200301c1c54180c02c03890004000d00480071227414105000d6014182d0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 629261690 1250 629260440 629260451
    0xd09110d24090302100218060403060b010818100c14040906080607021f050c0f0f0307030e0f0c061c050c1c0209010503040605090a0c32030703081b01 66
    0x50000008042440100081044851601901c45007048500e649030140041e40002d1401540d000039078001c0186000107030999110010040c0047c03500c0d8400c0e001107410faa1180b47d81d801c2941c0100c1c60b035801500d0700f6104d03614200c2e001c110300e9843c2c404118000c17031260ac1c2d003030003010030b801844100500c60a100c082d0350f031151030316620005071465104101080c4a21400220101e101182e002e040c007200c440e81c1c00020b00d000315480c0c09880042c00810860504200c21650035214800402003401c441d45815168980500041c086a445441c420300c16084100c800000e0310011403140744400048640c40e171980c0c000d03041c0401d0041c000e101d103000a494242400010500700b000342c0084214803034075510701c032020300140c4268000e041c001c50106805001003000210940c10a6034411038000485001d446540c42b210307528640c07030b40002189541c00307100c05404560750040c5120b030340d0300e0100c9510401c03c00000c0390707403420184000360403050302080050031982101c1102d0340c0074010f000240003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 629262940 1250 629261690 629261693
    0xb040609060915021b03070203212502180c2b090506061507080a0806040920011101090203031204020112090b0f0a0b1e0f0409080405040c020307080d09110d 69
    0x3d522010003207948902c3d040ea03035401085c0010440729034641c00f902071b110380c0711000640614401141510003050340306001c80d10704a000c41c0001108224402320940903440903006000d43d40d010078441d03ea400031504100725100000342c040f505161160312028441407080c404d8020f081e0800b2020049041c100b0f60500e041c414001640c500414080f500d0051121200203c005a0310070300d500204901024482030501a010786403850340040040c001007610205030f41c8044040d54084100c00c110581c0303a0029070340d075901009990b10302844100820541460f034000079aa800790061380143e50350220001070443e4420200950740341690302050085103118642088440c004032480c070b00d41c016035800035440381d200f8000e6943d84200581020b0008400441e4403a22941451200c0d4118610103030310609038449128442c03c0304d001d03845440d29142440104001c0e1079542c0021011507105101074004182850111065888818400507242890f840d104a00a66280c50395600c40d1100c0c56150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 629264190 1250 629262940 629262983
    0x1171e01030b0a0c08100306110708071b0b070507031b05060d0c18060806011224051c0b0c030402030c0612040b011a07021e09040f0b06010302070b0406090609 70
    0x14040c0c2d0750200305214403041d080d41110b103400101c41d0030f9132100c1b902904001051701a8001e051510080408520307204007610f0b500300c070b079001c000c04582e208085281c40c18000f003140e1594020b84040391120f46451400d803034aa644502902001d800e40e1110003490f240c40c0d1042d02160300511000c4c1485407030300b184500742001403001c011443c0c0481d0b40d407100c800801201598210a480082d00d681c080e5480d21401100c9034a525204a40d81d40d40c1c43d1000c9a100c044007101001940d030100018440c58103020901c070390500ba0981004005041c124401c002800002c80e16a2010390358038210b0312a03480d400000d2510703050707000d07003a0020303c00500340041d41c01d0f0700c1e85944518043c80440c0c0e41a41c1c0e0782c1c000604d03403e21800d51801c1170024041c1034010300d00101107a0b20101c0340110342410b46040300001380495000d03a800c8840b5400042200100714110114581c060307000d00301181480304a40b140f12019400400040002e13a841542e036041100342d9103d25007454002c811111171491301ea0300003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 629265440 1250 629264190 629264213
    0x10608030a020114100b07300207241101020f041829041505040e030c0d03020a1e030906050c1c0204032a12080712020c01171e0103 58
    0x50055081010320b01d1300348452902d443c0201400242011000c1c07910350788080a0f0400003049405200003420100c58801083e02136090520701d180f6140300451084c0c029151640c5035100c028441e406645422041d01c80030042440c5000c02c2c02c10160b1284481e07621802441760792041c05c15600040340108003506801d0400c1c0300341440090402502000712141180e0000e41c103c02000d02402418045003402d2a800c41090500001070400c07409441c0c0d000203059402e000300c0b0f03030b0007035102041c03041000c0420407440c0c1e90b0023031509007103141c4074034010010308216a41c0038900c007048114034540342841c42603101901e0260449030406c000c1c282115a03020552007007101a03140008480da1030800c003035a00c226002c503a130004c441d034110903088030076400c054140b4000002c0d150100c2e81c0080d80f118400220301c039103841200030a540c0e01c0a864103d115080e01a885011540043c95070061030b42c03c0041a54001c0a41044070480d41e90501c06804040ea5180c41e9041c0004101c000010070502c00c409 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 629266690 1250 629265440 629265457
    0x30c060206060f040b030c13060b03040803070305100e0c090105040e070f0e010e010206010911190819050610080408040f060e09010902030402150705070302150a0908030405031011040801060803 85
    0xe803c4501e04a0401c0300781d130707600d00c44070358035400c00c064240b500e10b4501200d48100e002814040399039907550303e080f6a190011036041d10b14542c0003042200295040c4102c80d40a0b91541140090b035040a0052000f418028441e44d889000010002041c1e80604240c400030000c0011508040c40d0400004000e041d02b00c4a82000c035240521920141d0702480c0442c1e160401039004110a038a4200000003600403140907443c0b0318820044840241d01158144410b1049510340f400f160030840c0300c04900658403c0c0302001a031406050080302c0e41c5990005900103410f1038401c0c1d181d16541040c040903c1903500c4004044840140055103070380111041c0340b0080f00301d1380898a030383d8030160b0034103911045074000d52011072424080210803504010b481034600030005c03500040c0c1c0320350101c3d4840088070041e01d1807510200305043d40550004d018809040404050b50406149c5000729980d5440851080304890700e0f0441025001c1e12501038600400034840244511503407407c04c683c0303e500140f103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 629267940 1250 629266690 629266699
    0x304110a0816050301063014061e0402010e0111070f2d060917010b030304030605091c1e0c02180f1003150b01021009060e070611060718030c06020606 66
    0xb000100c5150600c00c2c00c086800803411208507190058038540005070a110110b014613103811036001080d0071002c07100c4e154000100401060800c005142c3c00a00000428031061101000300310050740d2003c1141c403890343c2802c02407a10ba070081d0303080741800c00300d400200443d811284002818030004421a00c421010b4103011030f4a51440342c52a4251098018400807030300d13035035041128410070148440005008800024819140b0303001900f50340c003562003a03a0305038880050041024080c003160354030560101e451021054181d00103884079442074508078528803405243d03010035000705110420250300030b084000e4100c0ca446000294041901c0d13102d0191444000106c150040e440020300b41c07034100d0f401807079000b81804407102138180d41c04258114001d000c00c2c400001c0050007154001031180f070010541c00c40004a0030b103401c901d54004c108010000d41d0030707521201c0201c1c200e030708641d0702d10300a401c0c50030080c882a03600c0b40c1644014030b60303602100700050541d404502240030f00000c84 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 629269190 1250 629267940 629267983
    0xf0c06070209041e150e07030c0506070311011404060c0314010501140d060b1810050d0507030209040e010614010203040b07020f04020403080310090c05030402132c0a1703040b0c0304110a08 83
    0x4606c950b110242e0000921482a4a40a00817484c080d07000e000c907136100b80b0349001c190030041d520a0a580c088800d40035906014803e00081181600a02da550301861800704111070b1070100701e90744a08103205141c1802800140400c03611044412030b200c51400042c02e00c00180e032144415619844500240baa07401044141c0b083c0b89022030121045003a20344c2d9103820306180c034000b58010b01020704150141603081001d10200e4495022300228401c10b60300000e840362030510320b040c3c400c0200c80c01ca030440d0010042480003800e0b4409941c0102c0c3c0646042c0712940034800420001d1103150000b901d000008020001e00454000299054540c029002d0003011004001502c00d4001a280294400c001e101c2c00015140c1c1a407002c034940703610585c01031011090001401468801196640c02d039000121802e0500c0050a202031314400e8010003c3c0c518a0306d5100d000441d24040c0400010700f5000000c101844983c03040340040800040c0340418003551580708a540702562032542c1a0812080d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 629270440 1250 629269190 629269211
    0xe01110f0421051002030907090c08070f08070507060e0a020402070804080118020f060c4305060f031f0b040302040506090903040611030c010e010506030f0c06070209041e15 76
    0x10b5000d10600d588040104024040450620080d400c0248901c016201d60100040c0311000c07030140d4580c564507900c0f4000030b030416580013402d096100c241c200502c010700c403c0c442d5003a07000341220b0300b981e0410301c00180d00300f41e082136a06201c001c043c080c0d405400403800c03400744082034004204441c40d809c020452080c2682003600c038561299030103940894036608200b1581400c000138580800d0380b400755000e16052407402c407007281c0002200b0b8400d0312403404603510760b40001a8943c001c504440c6809515107002d00207005840b803030344482440d84010021500c489084600e139441c180303a52a50240e240e884001e454500d8209110580c030450402002c00c4960034020b0b8402d0040f1516000f8510f41410804150780d8000c020840c0185444200805940500c0c28494245080c0702030001069508004040510f040c0501e02044801d8220b0340410300156141d6013140c00444e8156001112660746090507000b041c018410041001441c0041d502000104880500840c0440340c00300241480d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 629271690 1250 629270440 629270489
    0x1020307140705010912020d24062c013507030302011506030506011205060315040f0b061203220b0705070e010b040e01090905010e0a06150b0a0807030e01110f04 71
    0x3c410042c2d0052020040540415090544074098213150034030032071400c0010f012700e811900340e03a0216070304007a0005403100b0301c0c201c542c5c00000c403180601c180e2455410111511140c0090b0069000b1400072041c941c0203145020b0b410f41d60507a205019281c28503aa428068040e0000050b2040c03180741c44480403650714004e00c0390b98013032401070752801e01c5240141d0a1900400025001c25418030a580700c1ca075505191070003da225522500201115000618108070307016406407400d403064036421a4041d41e00000026202144410007081c440244a40001043d811054101301d5a5040008404c42031100c0042c1d2042200c00c14040c0030380c140c0c4c0c2d908824019010f14022986001c10000040007801c1854000031103180c011000050351048054845203041e824400c00c40b402c07501c401031003010020031100c1d48010035103141190301d04603103140b005202080042034442403555468200d00318031401d40c030081905002400c5e0325503a04440b0071085160b0000d02c10384000280d441d1102c2e500b082d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 629272940 1250 629271690 629271719
    0x5070f06033b010b22050601080103020d111f02061005030715080a060e01031a130201052a0303100f0515190c0206040f090c030b0a14010203071407050109 68
    0x880164080b80c000d1007001c426001802e0184207115903403030301034040389a0713039031140991043e0501c0c0741d03002c840345034180000a443d40141040c0c140440400104056107802c00c0151000d070703014065000010b082000605821400314155918030350760203448030307820303000079031603000386801c52400083d560355004041c1e03600082d00a0519002c0e03580725480c4e11900074020b8a42103c41c80328003040d0151510420350314a8000d9209640b88146100c405580d00e0316a030b1000d400400c2080840c40d90880d035000030384540b140b08200c106075850090800420001c0da5030003c81d40600b0400d0365564244804040c0104505000f0307801c11072610500040c9516040b00044041d86052412a00703190300500c0702120303414070258800c00d01031051000401170b0b55520040001c5c080c007039034100101e81000b1031070702215603070303240a400e0600d429001c030030507038a101482044030409100c007042007042000407800e6010310308004003500c8610300d03407941d034800110b0074009840d0288d031044461a56400e9240c0002e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 629274190 1250 629272940 629272991
    0xe07080a062106020d020a05130801020304110915150306100c020306150d0c03031d06070507051003140a0c0806010c0b070e060705030703080f0c04030201021504020d05070f0603 78
    0x3014901101800b0301d81400c0c444941c0c081e0100509188151001900740d911150324040010800502c20712403401d40c3d20060040d0514000071810351503e9925103000c0d01d0003000040c400c04500707002482190300340c4000d0180c048054004400c0c00035203403510110380c00a0b21001c0c81810145816001c0d64400c04d001001d6a40040c02404152248100600c01081d08100642c000d454401044003288050301401c0040d0f210313a8684458036030240420100311200083c0c58803131360042080b80040341c80011100142d0341c045620181e0306d00003070801c3e0010202c52413a210b0f40310556040044070b00c83c650144544003480d894903009562107100460b5490310001d0002d0050300088007260180c4d100780402400c04030042c06c11882c110302c0c0c1c0c50305481e40c6c12001c000c03000030320710740300704503a40401d03e001942110103615802d04190450380081d4580e060b551b0200c041040c100001030a66880c0c0703c03519841074101041e5845151511341031030000402c3d0042d40046030400200c031000050307a05040b90000f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 629275440 1250 629274190 629274209
    0x201110910020f0303100e070801030206190e0d150507020c030a0b0618040506073b04020f121e130f0515070f09050d020a0512030c070e07080a06 64
    0x80392200c00c00041e202145aa01c085200307116194039005010001580100c1010244541c4946014071140940d50010211000c00151000410068507040242c44d080c43e00102e07440030b03000700040c0c1100c0506240804a5100111020745828010030140d1004801c680a400f4861a40e6042050384e844610003c0f040e0503600164885010070b00a40729a6043760008103041202200d525104003201401d032030940342c41d004001400100e540145007170301e030b01140311401c40ca500c0e2a00806006c0d02d0150403650b0f01d544002c1162200c90380d640e4100c1d8500500040c402e5107130f612034400044054000c40e105024100c0d51880700000261170740020b032203403400056010300d403100e9954a03840200c26180444091084582504010b0300c45131030035208100c1c5544095008a0318540244034613010b80c01140540d80485c00c01015882e02e06030742c02034541c140c640080c1061303c0000945140709a04010220b0b006190000c606c09508941080c080c94082c0e45d0800303207407100600c44044071541d00c18008038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 629276690 1250 629275440 629275447
    0x50c0f0c0309090c1207141b0f3f16060f1a0f01050c060604020703021509070f0b09090402010e0409060513301407080a080f0106020111 60
    0x118000000500c0040089015a4200803241d8041000c40c0015a5814200c64000c1003014040c001c00002a90002d05403424007501e4883e240d01200a10402c50075602500c1d070103512003803280003003040c0203040c00c1030021568201c1885c02080800c01d407070500d0a460340c11801120070392861007440c691144c2402040c852808810400302c05543e0300b90242158410f44480c00c1e4180b4040070b214007001003401340f103a04a96a40401000070f0f4200040401e810710400b44004090020000340003a800541a903005a40303c07000d06040e0b02d0a401400481e070050744501c01c01181e40c1000c2001c5003203a6145c40e803070030950748406d003010b07482c090301c10304c190400002c100103805980300d0a0240d858180113000005c070030030f4944a4030306480044680d000500311590218041010305c0e0798509a090b00031544841c00501c4040c07010110703031285003140401203100c0e55844811f007410300b100d640320391180c451642c0d0448901d01801d85d20b070480301030005010391000081c80c1da00602400c0b08460801511614 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 629277940 1250 629276690 629276707
    0x30f03020901171501031b0c06050403110f0708070f03120309020f0d050106030b09010903020a0321020406020609011a01020307060e0106030609050a1e0b060d140d170a050c 76
    0x94101071031180c10010311421250702c1e05022a8030318000c042d030043e070031030441d040d00000d01038034a420101c10300040c644c0803051019501c0607030f41c50125071001c4045501d40307440c141152a0005981c0465840c02001c500c5ca10100c0c00040c01400c444061040e10354459542c0502403882510780b002a02c44100850290103152095200d442c081d440240f1450000118001040c554501048100c1d40ca0317540b42c41c14400e211520390015440603c807802400386088aa90003515400320300401018407801c4400c0c02c40503182c0030a030342026030f41c2d004110b4840b17aa48030020b540d0700040d941c005095113001001056000043d12110140340e041c0c00942c41d00b0444c0c0c1c3d44100500000c60301c1031980d541c4036004000079481d80540c1e583c42d4001c20045c44200c3c00c6081c030514500000022904803a58040b50100052400c5400c2d940314004a45181c1e2001150501c000c1c00100c0141c048402e004600c44c5825440c2c120403585400c441000c4602102d540c0c2c4449001158030a603002e006d03200090142e5034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 629279190 1250 629277940 629277947
    0xb040f090b030106083003160c030509030a06051608010f060c0503040506041413050f010605030403030e0a0b1b1e090a030f0803060405070c230f030403080315010c030f 74
    0x440000002d40001140396449854506100100c000e10789a5803080d200d107441c440040c1c00c0410244140303491540f0303505060410300d0a1844a800c83e80501c080d918032001810f005106840b2111009030030703500220480d03c2d00000900084481c2c00b01e01d4029604206807a102d801528180c40030105240c0a02d41020002e551b500d800d144101c40d240710402c004149500c41e40d000d48000d100010080121515010410000c0d0011220a002c0c0e0303403404040020326500e49090300e04480007820301650b641c40f1800c08901411410085280354403c2c920098208086000500d00c11020320028a402e03161407007400d04907208120340500c983c03007030741640c0c240c50008800401c0c05900007001c2c80031042e135a64641d0020610f044054445440201c01c01003181002e008545e4050030034508a001105559902c07240d26214120110403800700703541b101c1404008000e044100c248013412030f80c890703640346400c0045034822a240a000701e0b04495811465004042e5a0b10721503140c0c071030556641280354200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 629280440 1250 629279190 629279201
    0x3020405090a0203160f1d0f040f0b10050103050c0405221506020a060c1416020609030f06040c1d0c130e04030507050c0616080f0904240b040f09 64
    0xd48103405001460360041c1d13030030041112020f1000c640c00c1c42c1ca619049408090488a81c030003190a00c50300c41c45c11204200d00d40d103d03408032040080710360703603116810000700350245084028000382e02282807008200440e0360002c103c0710242d0b4140400c0e911286000c03070070b001700e200d1541c00c4a0801080b00329402074100510328091121000509070600310103c0b20340d1a000e03031190b00560491603900c0140a140c0c050900d490046003002038200d084080031001e03030b01c0790004544c06074000407603400441d6079a030100e03000d6100c008c1c12540030b8420b011080ba111641554121100f0b080c21400251064901030905915200030888540c03550340c411241d0302c2c940c0480000d109010100760085203903d1071142544c0218000c2d0358054480c091454000e1500c90300c010411310a00080c0806032070550031221a15106078000380a64a0700a0048030030600d000e050f40e440d43c45401d01c050464648544070080d0170504040c0080c444a90341c60400a070148181d000380554118505800d2011441a8021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 629281690 1250 629280440 629280451
    0xb0a0b040603021c061e050d0c090e0f030301091508120909040804030218010501030507020106180b1207030b040516030201050a0e0f10111002190f050403150605010906020105040203060103020405 86
    0x134410240f070b00403130040486a05401521041444160202c81409205d800b000581001d035904035030715003035868564600015100c1c0a11181c2c031a200b04e00304040501149022698100842e0303102c1d61200d40301c00c06044035600c04100c041942000107800c54000809401e24407030074146a140000c3d0744207001c082c541c02841651141e00c10800000180c44d0203161030041460144440f41c5541400001003e0b10b601801074011a03040150502000755140102c0c800584101d0001501018400204100c0020406401c0280c018040b0001c1032041b58200c5900c51803050041d45c440c150680d2510b2840400c5010107400100c0500800c40c03854081d100354169510000c051034840d4024100144c036010030210340d0000541e140b0381d18101084200a828405160002c0950405202144135041c140054a00e0740c200030032013044416850117681110080e540203000b01c154545405041070140c45240b040340d000403030b2440005038440c8184916400746034001c0240045901c1c40c0c08020113003101404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 629282940 1250 629281690 629281717
    0x209160c050303010306140f06210f03030a090501060602031207030f110d0b04060f0e0f0c0f0a020c100f170703060b180901050102030a0819020706020706050a0b0a0b04060302 77
    0x240e000c204200041d60096105150125500c0403420080a10f0140034149004403020002448000c2d964079280c5007081d04000000541c60004201243c6042040d04025900b800000144550140603401000100b40206e00911440b40e41d05000ca95a10444481904c15102503012a80e40b0b4400c0d00300e40180f843d8007102007454115038008814503405001d80101c56561031055400034105802100c00801202291141039450310401c5540000300601d60420500f00c3d00000b41280143c1f0196140f01110020983c1c844a0411001c1e42d5080e00c014514031030b003000900b1654103840351210703e041c45810358880300903000360b003400740c0c0d442c602800d00000d060315508045284040c81001c3d0040307003d01c000b581e40c4034242d6401d004110300706800150442d003041010101464100042d580c0000ca0076550406d680815001d140003402020402056035000194140030b01405402140c05098036840400c149405642002070079140f5206d41c0310781070300078801045128000c4e4090b0048155524 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 629284190 1250 629282940 629282957
    0x6010b0f03070e0607150c120e0a140106030b0723090f0d03030906050c1c0603020607020d03020a02180a0c0201200a05040e0907081002030903121302041508010f09020916 75
    0x40c0c640040c0c6003140c6146c01d48a540f4120140300c590301801c020f042c400c0c83c4004000550b0a50101c644481d0010005800c4881018002a901c83c003580134000643d0840300c0e03400d041c00d04400040c919140301c481d202803c030031400c0406081c07104c07030221403440c1002414000d039481c048060014005140a054090550b500e1800c400b28105024040c0700d000422310301a607030b10300c0700d00380070081b45040d01c1c20102c80e14100f01031005845400403103081c0b41c2c045841e1030300e07403445240403442c0c030800b044002d40003000e1080d407000e4124240074042c01007000d030300309000ca511007a104901b2500321a4405135181e110010400c819103014008011000652910f5842c0c5615405c0203810101c0c10749003094964855401017041e14002d100d8a410081e455a00358510b061143c40c040d038034002d0800210224801102150b0041442038280e040030307a01170030910244640001490001101e4416001d413942010203441105801d0702c69290001c0d0300804e0507041c1c0d01c0d0804041b812981d800945401d0241c0350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 629285440 1250 629284190 629284193
    0xf0f070c020f120d0e0307060302251b0801020d0c0809070905070302090a08030c0c1e0402130518060103272a14010e0114070f060f02070606050306010b0f03070e0607 73
    0x180141202c4c08815110503020716418401c0c0352070000c140c0c0c171074010184148200a542c0022043d030f50b012001101200d94500d1490a041445142c403003103102040401e203900155002e0103401074600c41c440780d1401c11080341c2c998000c1c0c1d5641c8045410341c61a41181e00c1c2030042010503800b4a4010215240c0142082c02c3e1201180d50f50036035400c000c5030f0758004180014148410000c01700c894400b038070a1160003024100e0450f5100e11007503045c0c070442e00440c56904020708022400c005010007400c07140c0b41c100350007070800b19003400c1e540e80e400070303042c203032680d01144060003055000e88680c40345208011850700d4221480034540010039601100c24010f0401003400302014014004910341c3d0f888580c2d8034400946070403004290309050140c803544c5414500b4144081d103071601e40129840e20b80c0c86562509000034200801c1d0300f14060720100d04041849150750004083d80c00907411200f0b03d0340c80790301e45c01c0749001d1031200d03544220f000c00015400c40d00c5090a503003c03900181001d41040c105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 629286690 1250 629285440 629285443
    0x71206050d14010c020309030d2604060915270c17030316140d0f090615090506060c0606011d030304140118060203220312080f0f070c020f12 62
    0x30038070559101e80403182c0018920028032039414410050f00056140a00f00380209032207840d0040143c0900403500071441056a045502146074020510844024501840c0c0030005101d603050588820850103101c20303d031a214070450707080d000c05602000c4602d40c15200401c0b520000c4104440a0441c40c1c3c00040003903000303103152514800c070000f554980c684004010182482448414204000d070380c1401444204001181e0410014680200303a050780324000e40041e001e8600024800b17403400e40705007a4140c02da8030120645664080078421a2980c004101e210300400c4079031000c5421440115074190701600c92800c514980000c0c4801000035900003e041da00586d1020800280f01455148203680c007840c81509a9003042c58000300c2c03070821500942d40d000b42c807a410384000710403014240519445403200000e42e488601e04002c40e66040000b80540f074280c40c02c0325440b411001243d20280d0008006e48100040d50300c0e19140ba070141c0030001108480c10005400c1400c3d1030010200240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 629287940 1250 629286690 629286709
    0x22805270603040f1b0b03010b0307020114090c0f1e09060d0b040609021507030207060f020a06060803091011030a1b06020304050d08060402041d1b0c0d18080607120605 74
    0x20403400901348a00c0c18807503481142c00101d803814000d0050284500b0f050300b803e407070645903040c10041d100c0e525094181c3c01000070b200200303c03440c4a00708000b5109000111001d12180990750003113a40d078408240302d1452002d11801e40d48554801d01808542007000c640340c0c2c03041c0c0040c03001e0b5691804d0380b1418840102a2002c2d0748035501d5040410070742c204100892030910140070100d20342205034900030345404050190900300204100c5072204a0301c04c01c5180e07a4542c001104201081c0c0c0d030f1100a60701e902814403203005299030711100550a01607240001c09a900e00003640c5030000c0d40310100e0f44403900b00e043c8440c408452000e2008541d8030302c09540704501c103400a284402440c1c1010300003140081c1014446c500420050006800701c02070480b08a69200c3e9112080c1c54100154061114032052001c0d103001c0070034512554640040d20000b454040c4e207681903403044609400c0e004040c00e0044c81c10507400304000c072f400180304580411003060740c480d0004000e80c41e040065902d00f07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 629289190 1250 629287940 629287943
    0xc03070f1b0f050301140c070201030509010608150907050102012304020402160f06060b13060e18040b0f160c03120b0a08010c12060f030b090f01050a02280527060304 73
    0x401c107034401c1c49141000d10840304006c50b800310107110780c98480d8012055100d0201d000781015282e0f0b020681c00380c025001080504080e0301501e022080c15400501c02c0070048070b05c3c02c05c8bc0300742c0360001619401840346669900316034001d50240b8680310700e6000c4d00f94020340102c1e007103a8200481e0684d82188440c00c41e81342d2042041d100fa02c2214101801510340315000400642e07402c00006100c01b1700e502c400c40803101c16082042d5181074a400240100611001034540300010070100810042034009151083c2d1042c26060003035102c400d06000f03c020b000103c400485d1814203d580030902905c3da09400c81a40140031400450b004082040c075240c9900c5050140e454950004103903030007030703010500742a4611040002d10310f400080c61454420384401b0b0700122540303022519003407050081e003942c0038400c00207114504180c0c8810000358000201c1c89940342201207100d8000d80081d0942c1e00c035500fa84d56803400c2021100c44041c4900030340040201d90512015076080a8072000041c0d4400ca = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 629290440 1250 629289190 629289209
    0x170a02091e0a020918060109150908030a170c0703082814010501030605010e130b0303121e0705271201090501090c050a150e0103180c031203020c03070f1b 68
    0x561204003403003000c1e144844140d2202d80071404000300769902050260449091140a03840c09d2a40202902c03990541e400010b150700000440c0708009030802d41418007810f00468012030359440200c204802c2c015614024001000b200210b101c0e03034600142d041040b034003c18417041403e01490860200c444810349283c0c0d4046000042000f580c0500c03603000141802c1c00c01a52005014002600645256040c00515640c0300c2e2012482c1c1c4042050718113040343d42542617441d042020725200c101c0d011084400c0100300020015841c64458025030358001041c00e55200030401c1c80203121342c070829410f0059004203810002e001d401c0c00034016645583d004400000d068416030a00700701044094100034000c121a600c00c1145242446d502800c0350102d00d0805800804000100d01a290408031001d00d1003181c2d5414003030000300400c040850348900d10035803001e084050182c0c02e90040310329640d0990814400180421a803000c0a100207110700024085e9105000d015048902ea907003210010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 629291690 1250 629290440 629290447
    0x30e1c03030e120f0c1203040f0510090803040b0705190302120105120a03080606040b1b010b01030605030a0308090a060c26100b0c0c100c020406170a02091e0a02 71
    0x505405100d24544003101c0e00c060b10501d00300b400c50120b2407140c600300d00802c1304005011031210720240209540700040c556843d9407410705007841030301120f011905491500825003440c003100750610810240d16031020046007199944d4076020194140103100307009210701000322140c84200c0030f54440c00c2d003d0a0700c0040e1242a800484846500140c200d5402006401c16108554500082540b145a41480d05000300d40d5070b280464914000c82d44110315000d408a22446441c160315120f0100390f0071a402000b0050b80c01e001101580d04031f208098140c0c02c40c80300000441cac8280009035001d00c40c1d004a45852845644078422038183c0c076141d600055000410405a0302c0c00d0360465241d0504144480e043d08000c03218409141d43c034414403005990010381050a0001030040c0050007000501201f4541c110f06800341003420b100708102c0c49549060008154416030f880702c140e50000610042441951a9090101d1064060302007148043c01c0403840c17a540c00401d48280c803440d04d8440150301c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 629292940 1250 629291690 629291693
    0x1509061d0f0c030c1f0e030a030e03012315030f06040f0b01170309060319050712060b032a07050607090e0114091609120b0f0105060412080304030e1c 66
    0x14440b405a10500c00e4110243c1d4204543c0d0318640402c1034412003d9554502145040c165000764080c40280c2d007501442c00600240360b00b2025180c0c00c0c90f400e5000344100d4030381000314110000c000300210007155030321001c110800c045880858103144054116450104580e81403850310104a6089804a00b41d564100402204c12003050041001124186000c41700c3c894064403400b0700310402d40140004000901012941c000c050302114110004121a08002d00002c00003000214012403aa090403800201c0da5003080860b8031944e403800c00603c0034990400c40491401a120800380c54000038411280448d04c14000c090007070409458485245203000b02c084d1504205902c0f510a2042c0080f640d007464036040b1010b40e201e80c40c0920380e003003005000c0007900d405689400080d0f41e1140441502c1c10040040d45140c01909060803070700c2c03541c5c0d9550811003580305030300524204030340c980c0c4034a00041928000d11f4000340300b41440340058400c1000309152080040b5500c0126948041110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 629294190 1250 629292940 629292943
    0x30b0c090406080f0a0b1b0d0e07050607210507020312030403080606090d0f051f0b040b091003240e0d0905010201050702191a1f0b0301031509061d0f 66
    0x401880343c03401420300b08680c503001075115a03c0c2d84014080a6240d4001202140300d0034a013000a03140642d50b80c2c0303c0a404140b1030043c041c1050700041031080e1480400c0740c4c42d00c10250f038480f90b4444c5203d51040004d070403080c00b1400d00b24074075090040a0200c0750042e5000d020568000031160388040e140c2c035003401c0061080c180a02018081d00007040210b001c0c1e212440341c44100c40d081000d90001030040e18000740f40010a4032141603c0e10080203428000225401064250b00100c0f4203000314072008040240c0f1900c15908040352000c0c150013000040c0c0c5003400c03280300010006545041d90300385603014059403d81e443c3c0c0255500442d086144141d0030624450140c0428402042189807200000c0c3d600c01700070900e4030040300f41030700720f00401908580b410740303814205181c800c1d0350030400c26040b10030215441c044074102c1a180b0104d482030290040d28122900701d4603605840f0020850240108041c200c10f849803900ca0f6006003101d070f0190003945d10100160000e0000b0107041403000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 629295440 1250 629294190 629294201
    0x50d080105010c080f070f05060a0614060301140112150608041b051011190506070207060f09140f030a140d051612110d0306240c0b060a030b0c0904 65
    0x95052241d4402042d01081031034040e5070101e417041c82d815a492001c0d003849415101e404e44000c04d2449240d0410031540c60701d03005442190143c4001224081c10710040103e140801d014080701c0d0b43d05400c0c5c1d06555842180101d200b04501f21000803411000226000564080d030480c2011031a14400d100400c4084a01c030f41ea100120318201c45411b041100140308680a075581200f004012110401d02c0341c03040c002c01e42ca41e100000207410b0502c1a1822640700c3c1c008403031000c00346c0180000000c0329401051104910365055407034011603401c0400034062003c1d00001c0e2500140e040c1ca507a09681c0741005110701d41c0e0b00071070801d40b011072050700c01071800c0f240a8184041190501c42c031121244006030465049510016015611040c1d68080300d000c048145049400d110745c1054104540d055400320095903460881045441c0096004800e6442424803c0000035a540340d11030110303807807070f105c5a0400710040910a80c01e590362506401c1010960f82c4800c1024001285c0e002803901c0d1154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 629296690 1250 629295440 629295449
    0xe09010801021c0b04021b0a170301080601180e0d1d060c0307150207150f05150f090a02130303090906050d0c0e090a020616031d100e06040b0403050d0801 68
    0x298980351003405403140c00c1801643c03000a00da207480703c44510781d480e40c05664030102d107044009448a64030141d60303600c04010300e095036501072103590400094003810480c1d041e103081400402d5503910b08010100090007161144d01019542e110304c501e04c200502c801000342c1c005940c2c0074060140381c0140011841041e5060b480780f202085402d810794008130a85c1d103140d402054001070503641c1400c1001038441c010004240300300c209008185109075601409110007030304d20822043d550f00b24520032000036030041652003403c0e1100351110385000381442d80e000b10380c00c40240c10920750130408103d4200a0304114041646c80d00207000c004158030038080100400c643c04076600350a629100f00741c501c9809800c840e9469a80042c0102204108242000d40c0c050040c0d941e40c070280f403801101d072141c090124001001042803c02c0c0a00c02c0c4400142c0300b00040908040c801407820035280382070420701e26500404d0500c40040e600200d4809400118040c0300070300451100301c02d0007030403c10141c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 629297940 1250 629296690 629296693
    0x40905010506030d03020a1704050a050640061a0301060609081c14070317042001080910020904060f090603170307050d0b040f060902041811030609060d050d0e090108 73
    0x49070070038503840502c0c0c232401e030540c0324808000c0c5c581d414450f0800424213030160903031050a06100c00010310084c2074000d90380980039010000b840c0e00a41c08203040e20b0783e00700b1180d0f41158808011540980c400301260b086002d940303d46005c04d001081c207580040c2d2011010801440c2d082001540900c5880c40000400c40c28051340240d03403902a14184540d29882c440c1a004140a001c241c0165a80700360600041c41130100d074a424a0f0800706444910745500b02800740700240c1c4d500b075000d1182e441c0900101c9001e0103444001040100c003e4000c000450352081c1c4840000030f00c0380381c0303025030009800700140c040340283c01c1d400c01d4030406600c3c100014a82208000304a80c4541c082c003624001c800c40f944c0810081c900400060290540c44100c18140380382200019440b030443e80104101d4901c010b008100d841d04101c0d100441d8405e0b940c04064540410018482d45441100240d01c0440200340007019401a01e03040d2404215030303c00c502150084001c00e00394030709100d049006105200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 629299190 1250 629297940 629297947
    0x1080309281403160801061508090c01031e0504080304141207020d0c15020709060803040e0103080306030a080309010903170402030312070504150914040203010506070b04020609040905010506030d0302 88
    0x15030380307041003218400c0700c0203014428115201950103129001420040c5155400101d8461400c140240142d206060740c251050a8a03c1858054200d440c031a640c90302c090b00c0a400380324015405403070720100107a400503828000d2002e203502441124001c0d401450b04548a00d07103440c02022800c60072146416681c001078060a021150b0f5045400c400e50594a1038400007aa103041400c0301035a4000d40d81180000030220300c100d41c0064800c0407607220346002e002d1165100001a103c1c422070107003102c200e840c00300500125003c1001560010f601a007211244902d03616008440d410542d86060507035194404c5205140d8444410030141e00c01c0710600d40b950409600183d680e1040303c030350780548494100020591809001603500420030b600c004210021302003c01085c0a50034020102400c044560080190500d03100b686d06840003e801c1c149440040c1e1a03510f15800005c00c101da100604108002550300c0d1800740101051080c0c0010443d0b0500d0410103040503020000c5008042c07050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 629300440 1250 629299190 629299249
    0x114060405100e030a1e020102060f130212030f070c1706011203110106182309070501050c011e06090507020109051b060918010609063e0601080309 65
    0x950341c0781140390302da00b014914101e034030340807034103080750360700082d0407550300181c82042c1c0841040100c00041c400da09892642c0d440d40ea80c031740562070665145500d8920008030000504090130641e13a611165822a030074542880602da585034020002198141010b80040107201c080400154a40b4070b80d02c0505002c6d0705040241c3c000751804074010302000b10908231030b81907030400c0d44284003a011106201c1c00c510300c4038007010082c0030400d4a60b54880c00d074440340000b165040c2d249078061550b503005086150b2601d401150a60040c0710009129541c1e480fa0000b90000008402014101c44c64045840c628010041c42110b000402c01025a410031140c82c0021740040b0300c40c00d003056024500f100e40302c0084041a000e001d0561015005220035034126040c01d03124a0460480f80c00d99548903140e500c80703000b203c02401e211140ca0064411400445219100c126805001905071515007445526075920303501c2e054080e40080c0c0150800185030505007084103901d0201c0b10040d100b81020200e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 629301690 1250 629300440 629300449
    0x60c0715092303030f2a061801181428060e01020a17070309020414010f0b0a050a03050705090d1a1b0d11430809010c050f0102120114060405 62
    0x110f64200c4405d850026521024540d90340c698014415001c000b00b401000940f01c4590703464041d141c9002e50703a480c4c881030f861000d0501601c2c084004c0010302c3d5000d41c80c0c03a0780d214034a01ca0000300703086601404941225034444140d8035038007170300000a10100c106841c00e007070b000c41c0d00b0710116a010340d004008296005400681090580d1851540713121a83d40b042e00841c005c02c0c02e040001c0d841420421512012414040f040341038907070039148803010a50fa202c40100c98850b07811000046030051000c40f0806000b603102a61048090415030320700400301d0001001d01344040012140803034501513a50184c005000d000b58841c80c94160201c40031000780c106c030800e014200785140f00f281c65203412405080008181c8102c00c03001e07424818007080306452034078618000000c40b8804c144003102081c81103512007400c0010f5420003006440e22603c500116580c0d81c070344609655a214100d40e0046540c000d10007001e615941c41c1c1290303465410042c01c00007805010500b00e115880920080c41181d0760f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 629302940 1250 629301690 629301697
    0x3080a1a01020c010c11031203040c0f061428020307060606031523040509070303080601081303030905120c031804090b010e0a230f06090403080105060c071509230303 73
    0xc00d00f8401c12082e0989002540c0c46c9130a000e003a098002d035a03840c00400d01d070b10061030150b481200003001d405d4440c589034102c0c81c040d1080c000040d20303d4032240301d02c0800d18010480500300c00709055960700c100e464029403c800035141c2c070042c0c0c00020b0741d03c00c0c05502d00c541d0300a01480e20b4240548490810400d083c00400d0056080d000c1c14085440e180f0000c640e042c81c0c40c44c1000d0410f000e146811003000303890b401c1702c2c803040d80441c0420001510300e40c41440d40c00d100d241e1240c2507500400c8603071411401403001c010111507030711a081411a9040c205c2d005050071580c810011695400c0042c1404442c0c1c050116081c05a82014112400100c0310020a819280c4281c0d40090039904c8821000c05421036540854400894088218041070000300141c070411b1145045c0100b9169503081c8404100100d4001d800540c1d8034006000a1602d24002c0032494990300850f914151687c8440e5400c141c408100300104180e00c404001d000203a14100d0440c82c210502e003542190b4440120b500e070312 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 629304190 1250 629302940 629302963
    0x20304090c02010f180309060c031b06091506060201060803120103080f071e03080f060d060509120c0a030206010602060705040b0706090818040b0402180f03010608060403080a1a0102 80
    0xa07114200844414801d5129200d90804144240460b07400149540c41c0d052407208164000b8044584c0818454040c10281c51211742c160765080300b0807030020440c80c082c400304804039400f9440e140c0314004a60f51690f80b0281c2c6030510b10001d5940c1c50140040e086031040e50060304590000d120312004003151a0181e81102c2e0081030940d07541d40c1d1181d80069921440d003005140e0360644081104052200c1950007003144603440e0b1300003e8032a041c0c0303001c1002c01140d8150740322511000301400160140c02c5190452035180c11540d0f9002c40140b0301020b90003c800241555101725807050515504001090051a850000d4495800c00500c024842c0c4100c2c0126140c0c1c2d4400545101000000c0d41329001c1c4d180c00442c0e603a100c06410f0405070101c0342c6004002d10071801e021711100c0034600f43c421128665030a04220641c259140180903041c0710b261241c13a410355852400082d000782c2484400e201c0e40c400d6407204e1807454010500001c41d8a500c86d07542c40d500c7c010f00c041400f644c0024500d00e00d003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 629305440 1250 629304190 629304209
    0x30306040c0e031204030b250c060f0608030d051e011e0e190b0109061d0406031e0317010303140c1006080d12050f071107050604120b090d020304 64
    0x104003030755050b28440040c20030543c1501c200e0162000e2000410058019284102000c2c682130711007042146800710500b00580c1c600c01c4c2d820404500c28002c92448030158443c9402040b017000720350301802210302a90000407580c00001d200e0801804501c00e05d68040e50702c0140a880b2400388695044115050007108a140070f07112092201d18030007400c20b070081000045110300e919140108840c100b40000f40340c0c008a040c01101c4c2c505602482d150000d0b213041da902c80c0e1b507940c0c00c0c00040c00140100e4514540059030342001002107407101190700344007080d00492842d15131a80c035006015040e00c0345071203d004000001071000035130001700c012602d0700007030700319850303040742c11110781058954004140d24520304480051202404140ba014501d026142c042ca8100f2009025080d19800c4440e0040341904100203104540101052400c400082d070841c4c80042d26072020031030f664031581201c0d00d2800240d9400d0300704010308003455030084095014100c081b0190741c000e96640110300640081 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 629306690 1250 629305440 629305451
    0x10030c0b030a1812020c030606032d0a0804050306010b0306090406050a0e0f1b040e100c0915030204090f090f06020306061303120f21150806071d0a030503030604 71
    0x20100d250700000d60a9001c020903800e40c00480ca821041800c80040071340c098015911020390a00e00450450710481001e00685003003028140049141100b0035801c41c00000d2000254600d55801c0242d19442c52090103500d03605ca040000301032502105900c001d0421204004004403a1251501c00b900b243c0e000e1000b01741da031600703804140130704021250701c0c1d0544101d035100c02c031440e000960001008071101d5130400d003018890500060b5903c140506c02d03280d200b100c40d07030302c420003c0d40004581c85030741c9000c044264584220380154a0204c035424000f03900454148921242e910840404807000303001049a00b40715a01c00384914407011014003850f03030100014815031200401c0f61b1074010401411500c1645a14102421240c0407c10200048a1000607014103006100301c01c2e84c1818800f13038188a00d442083d80e4082d03e014080c01d14115050040020100c03c2001664000e0015031204000880d500c0e84045c824540300740102c0c4212809842000426000b1084075001002a0340c0841d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 629307940 1250 629306690 629306701
    0x23010e100e250c1407090605192d080105090105060d0f02040506060d0e030d0c08012610050c07021801050a0306050603030f16140a0209190b0303130e10030c0b03 71
    0x2608541c0d154060100b5140c00c1d103440c900d203c040340342c4055401c1c0c640d00b000030507291021707c27115010400710820b02480550040c4848810444c0d0900d0940548140b550000028408000c0828140e481401306030744580501c61002021701500768000030907030300078922840984404234010002c92010740100d540d44040b0340381780c54200840300300001070b8106120240b49090000c2e500e0748058440b807081c61511b50000f045a120350800c9040341e010303400303103203150303442c49800c0d54036055114045145200b03059030341607500c841c0c1c0581072092013042c012503103c2101c0d00500800700f0f1a0242c0380a910b14040c018491a0f8070f403070403001503035041000015645e0360f0390b0100317180d4490720b025070203d11001b241d454501e05891a03000c40f018442c0a020f60300c0030b510b5000303a40e1440354150080d402603101c400240300c0715008807484001816070f5800b00e59200f000000c80c0c10341d84191480c00d00724102e00c0060144014202c08a13802c00e00e0280110400d91560700c8600060709980070704c404681c0300002040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 629309190 1250 629307940 629307947
    0x51f031b0803360a031e02180f100e18010b040f0b12010c0816171510080c07170403080d02071e03080a23010e100e25 52
    0x20094020301c02107907981c141485404480070f20842a0300006a881d04110407400c10141e10103a0140020344a80c40450640e560b8080c42c0101043c1d8002010780b40b4003000c09070703031345511000d0148210080000300d414030a10780c080407100100804a0081c480c8000c0082003152480241e02081d81202089841c5604c04481d01400b40da2031481c1d0b100b410540c400c400540d0780e40c009512450211546160610031402803400d898079040c000012462200000ba5040e8407081d44501c000500d1812031582122100c000300548070945a000b16415042502e40890901d0890b64440603004d08000000b894620f1000b8094412030700004d095400280c0c814045400040644000d5580941195122042e090385a0001e400c0403800f80c88840c0004120860b00090b03000b200c042d21340541d5405680d50701ea4903684003600d509542c8600140c0705c065078940c408400399146001c2c00c1955903003845030510559042003d82c081e0025a040da500c4402e001070390000343c2c2008040000b000290b25802c0c000c28056 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 629310440 1250 629309190 629309243
    0x10051509040b0f010501090609030f0614191d0c0f030102190e0102122511030d030b0a0e010e04171e0904050a1a130b060c060901051f03 60
    0x98201040300c0c180000c0103541d0361103030b1240c80c440304126101daa80b60011205502180306d040301140c44800244040342403182c00501c401d0103076001040c058140d820300703413141c402200c0340f03541013400d003c000701e0010090144400034190124044040c110324400a6154540c05462510501c1a6007040d54030b500c0a4060360429961107413075401803402345101800101340c08407514014041c05605030407001c68101641d107080b0145405e140140e05c9081c0d110b1030808200b10070b81d894010b41c042d41e205541d04211010690b00981c0d404603200040e18144501429141c00001c006c0702d5110040c441e002c17016040d650b1080d00411a9469110a2800e20449100c2d0408548000a4801c050308649003000700901c0030400c16a41084113582d40c010000440d12280e440322000035281042e481646003200c10403c11007001c0d040054050740c40000900315611218121205030000e00410080207001c1c0300d0194031481410411402e074035410400502a0a00c4c0402000d10702e00451810792102482d652 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 629311690 1250 629310440 629310481
    0xb180c1c09020405090a0b0703060b09060a0e04060b0a0905090103030c0807060b0405010e24130b01020c040207140f010605150c0a05060109061e290f030112060c111005 74
    0x201300a00b0221450b40e02c030846410300340c1c0d0b040da800c408581228402e1090f10212a480003000742080440e20170002168890107200c420000e28043e0701300b444d0f4031880380c0c0c0000d0494000540e550f120000028ac0054026400203110f202e818004101194000c0d0005a540d0b6110f0000d5a443c100da00c3d045d0002c0c0306244446802514040000c03940c800310039003050042c001c5015168501d00819000c2078103240c543c4040380c200f8100380b8160095000c580040101c8101401a82c0c00141010b01213000c0360041d90023561084845d0000c1c4020900c240306503100c0ca20b01c0b0000f0703c4254104404940c0e1440ca82c030501e084114006186800030b0414000c900b1035a40c464281c9010b56980d200401c05010107004509031413419010500710b0301d889404039401c8070450307000007240c507480200b004805001700141851144c020040c407915042807100071400303040c1700c1c42c8403480a00c83d0b0400303a00702c0b510501507405200504c11002003291002441c0d51081d0001540400d466403105c1d00c0c020202200e410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 629312940 1250 629311690 629311699
    0x70c09050f0609090f070501080a06031e0c08060114060306040609020a0305091b090402090a020903060103031e0801031a09120c01020316020321070e0d060b180c1c0902 74
    0x90003504a031000e00c142c028042100c58811a40341e03801c5442d1200b881c560010180c0d404182c3c100090350140034250342c491034090700015540e070f0b29150400081e040c4048010a9400301c800d150412010590320b40250800e03200620842d130504007480d69000081030818841c0d1f03000300008409584580141e4040c1c01c50b00c50a64a03112046800703400b91405580004c018040c40058017088002c0b900c1d00804600020702030304540e2981c1d000e00460207130150000903030316000c0203400c81985040094a000f18442d50703440e64412a9084500c190348203d12940e410811134000400105510101c8900616104090380b000c54480f05541458854160780c044022070011510808100040d405103100d10280700441c3c030b00111011080f0b0300da114500c10000710b05180b00710b41440300c0c051005035601c5150f5007482c0180c0102030000516840c1990000c50340b4580300c0030b54410504081103e0034901ea49494008074900380700500002c103014184c1641060360441c903640d42c0e2101180c10440f41c041c0c0150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 629314190 1250 629312940 629312951
    0x603051c2a1e03090515091e0a03140d03021305060a09050312120610020a0b090c0316080f1c0c030201020d021801020d021504021c0203011505040c0c0b01050105070c09 74
    0x1400340202a05802070300420b4100100007014148034440c240300c0c03100000000d07d044080020010090841055110381031003910380e40515441d8200000007440c00b409444403400005050b4500d03002881c0c0c0c0400c1090300512420141c1102d0400d85d00039520102c400b1611840040c1c412110085980d010310b80c50f10845070420702c482c180c60003c100e0042980410354090750707040700f489444025440c0110042e4000d042540c00719820301d070317129001007414080d600d0b0003075140c0009e890070903d540565054400680304101c058010403030038003075800c02c00c06030201881d00c107103814200d90b00e01d0314401070203d10035806040601c03c3d0304940e068107034000c04640750168021008103811111810310302600c07840841c0000c00c0e000144510311111445003a01c0c1a0752282d003400348442c00c51908030594030703032000c581c001642c081c010740191020700f4003429041b626110810003515882c4800c0403d02104085180200d0f031410310440c1540c40c02c4c21304a5503408207203080511201c0562012840c80d1504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 629315440 1250 629314190 629314223
    0x30c060307180609081614090408041502030d0c08070c1202010e06090a17040f05040f020f0c151b0d05060109150c060c030b0303030402010e01210603051c2a 69
    0x1901000a40d40725004640040c010106c01c1740c40410240201150051f403401840d00c0e17490010180b90348103104501d20741c20030f950b5480c403687c5c21017203c0f0b405000d81c1012407045500000c81c416140181b840f0710700102c080c100b2003c0940003d02d4120060402c00162801d000500d000f500120601e04140049440510340380710b00340d4803851508001c0792820180c49000400000030420759060300d407402080a2111714181c1080010a031082440c1c0d411602400507003840b496100180015400420244c0311524620481041603000246007540507401c2001c0c004400120f24182c508400300f04400103110b80710000141c8a0f08169800540001711160424522560043c03078400c0c041d00c40d4500380301c020780040081d400d40e04c0b00001c00b1b40507402800010090340c0701e610703030740340da281c0604040c40604032241020501f414055401c03507000351100010410803104004810801d80064200358001e07207649001840c000e20b8220042084504010b102c00740000420b50101c0315511080c80300b41001d51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 629316546 1106 629315440 629315447
    0x160815150a0909061e090210020f0a03030f15030f050d0c11041e0f0b1804080a080417210702010e032b06090b130b030c0603071806 58
    0x15414140c0081e05165012a20220121000315141c00140140542c0124008042d23003158400300790300300b40660100e88890401e41c1440c0c0410071000100300803020f40303105102d41d60002030400d0f00004010095800400291143c000d1b50038003100120300b51040e980400000d0b1901c103c0901e0084941751a41c0911400c0c0f040e0229005101d40002c50034049800c00311744580e1940d503688010303405141c600d0040d001c0c88143c03032641401d032030166540e0480e40030707129500090021680116042050300110f80070a0180700c0101d13911905400183c1c080322903070202401548802c0b10200b4502481030003220750040c20280190f1610501509695401d051a20309181480b05c3d071410541e505c582e801140000c18500402082c058031100c200031000115820407a1030a107016104003481d100480d04405004013211840c1c0c0325a00d200d401d44101300201d14131050f07008500c002086107900b = true := by decide +kernel

theorem cover : BRFrame.Cov 629136690 629316546 := by
  have h0 := BRFrame.cov_init 629136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 629136690 ≤ n) (h2 : n < 629316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
