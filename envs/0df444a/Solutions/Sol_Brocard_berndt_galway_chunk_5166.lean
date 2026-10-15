-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:57:41.459442+00:00
-- url     : https://prove2.me/submissions/dfae89a9-0571-4550-9e13-2aa209057eda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 928956834 ≤ n < 929136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 928958084 1250 928956834 928956851
    0x2030d110c09060f030703120315062a051c0e0402071208071106011511010c05030a0209030102070f0f0c060306030201090e07110f1c02070b1608190909 67
    0x380446010355000e41009001ca1207000c030400450b41405086250007062402801c0310a460900840024601a1400a5415514080050454a00803002055481e1024090103990f6214001a4444000b400403c1e45031440700800c100b0010048070080c224410310030441b0300300c64440b006105040c0103444217a840946c400900041e442070140c018900c0d43c1c151051141c140c0500d11007500190076241c22402050400305440c40c6c0350702a0815440644102070001e41c90303500c00a90b02076105120028000e240180304098283c1c0000703040c00340c1054000c0b5100040f91000d40c15181c03102d80024005030608a00c2c2000c28014440143c203445105c404400400c0c400c2c02405503104485d4180e64a418441c64900806952080600400c040043da1241c000780e0354020041104282c0010010700002824242c3c0a00c480b01000342c2d11084d900500b40c20001184100103071b0f40e00016400302c01c0511407880c60101d040d4811030181c1c9a20300c440e00a4030b280d45510140000c1940e0707003840c00f080000c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 928959334 1250 928958084 928958087
    0xf0109050610060509030a0311120c0a141b090a0902030a08041403190803040213051005010915050714070e01062105331302030f01050402210402010e0406080a02030d 73
    0x81749152a5416900c40302030b0a0010b0700c00c009184482c0740324015198010410403041140d13900880032124207070300c550384c13003410321603c142d0001140010000800c01240d030030511004102003085410b204903081400190402c6483e0031503c01c0b01c3d40102655881800c2c3d140142180d0018001c0004855003609660345600780000c0c10703803880d1981c440c804210b80c46541d401a0baa40010f03c12038000c0304030406d01e5610080d50207028000c80301d15043c40e40c040c1c24000010f0041c02039a0107682901c6106400c240c1850300402152403145c0c0003c0041c21a41407212407a2030403c5aa10181c2003c1040e00005045940f10510315022080d040c0c40102070307242c4030443e0303007991010b84d1002c043e407511103458080000032150070b9456080d003400a541610000c1c00140a0340210800601400d4002040007045540034105901600c41280c085042404808069000c00044034a02104405013800b29065a004101c51000868000c00a010050321001e515440f5480843e040340a489401e0042d82c515 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 928960584 1250 928959334 928959337
    0x18060e1003030c06020d0b3118020108040f052b02010207030e06090a05100c15050702150a020405030d090801140402061603110d0206041a010e07030b01020f01090506100605 76
    0x41c0d8155480072480002515a14003d41c400c9030700c400c0d500c0d034410b000c2000d41c440b0410100c602c8941100031000801c1044d5608103010b1a1320709200081c501714840c01d1001c0c8207074402002c80c4d020310340001d513030380d440c50580400e90038004040c0c400c1c410081b1f00c14403000c5e440110a403d1400324951580301c2c070740d0f15090b401d0340205500100400c000e501d4203d403506100000e0010420020700740c2600c03560b81d4001c60303283e400030104140091040004042482004420006200e00b006d000304141d25059000039224010035400030703600d4504d01c0100d0106070154064901806005080da410b428181c5030160125074a40b00c0c404d469401d121142c4503180c4041410341c842d0f80c019103500c0ca060210305080302140c40fa06411018480c2640105950342c4040004821103403254000b031106080a0502c0d81ca460300717030505691503601c2070300103000180700e101020760000850b09002ca6240c005000507424051001c00001c0e166103085507150034030000151141c0610000040f0f844966190701c03049499 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 928961834 1250 928960584 928960589
    0x140c0304090905010b2d031b01030e03130f030b01140a03020f030102071b0302040608120901200604030207140409021c08040f0308030103110d0b0a110418060e10 71
    0x1160418403042104030000c1d082008190b00c61400040c1103584440000c4000c1a00d040898a9807054074505002120000410840d85801ca009042d03400b80700400313103604104949100d0425844d80f261000781c140c10000c0d9010440c03d000303442d0703459884500b0070085206074441960f413007114000009011507503c0c60340c170385000003602c21880242150203104420405d40003440c4c140d0750800c00c0002058000224603140b014540c0700c10005499401000117481441d0060803680d081600c9007000798215208030780c0e2500007800d00d98400015088040507400058a42ca0807a011700c0f0100410140c5c0801e40c03c098031000300c203c0380030749503c0e0107120848500d804000c0d04540b42010508403100b030710100f03c141a101d50403603407070203446032040c2d0078000b0b00768403c8a440b500030005104000c81502c0e543c214000030b0301c0317015070890182c03504a0000009003800c04c2c0c88e540d0b001c2c0f03e121041c104c4200e4015103c03031092004213419270705a400082005200340848000403002041105c58003004c840b04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 928963084 1250 928961834 928961857
    0x2104150c030338063a020301080a03110a0c06030e07080c031908041502032706030402060703090e15010801050906090708070c0510060e07140f0702061c0c14 69
    0x880300c8403c0b0802c0519400910f0090748000d042c0821100c00e2940b545c98404e51444003e840000700160a40910482c0440289172040d401400184200380b0f000603c2100300d40c0501d40300f0010ba818100003800d000811101801b43c4007680380c003244c01038058010305400004002164082652004401d07103404843c2e4103107926802a10180d0b5001c80004e0074504001e015524007407602d5a560030b448550000d241002d400b581003c035841c41520020040020314800d200c400200345110701000030154031006000078800c1001003080002c1c136201d54854006840d0750400c82c00b280c01d04007444481920385403036007030014000c01e00200d003604040c14440c0c001c440141c4129040d850b001400c0c1c0e0300000c001e18500030400300314864004210100080d624002d403e00300090090300b440701d11003000c18000c2c641d03014028008008a0707094081011612496003525899403103000d1480010b02074494044400106d03521103c0c00301940b000b070340c070000c4140742603200c16041c0b81103902240c03154001c81c0d00088 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 928964334 1250 928963084 928963151
    0x50f06011e0e060a021006141002010506010c030f05161103010b010309080a08070c050a151404020d0b07091208032d04120c12020601050a06030e2104150c0303 70
    0x20118100840500b5040c052401541c03481c0f00c1b0034918000300da0003540a181d072508264502561f50521b21440c80d005401480280700d103281c8a0700280140f00c4450f40141084000d651b440e60191082c000c2d100500010710020000007032605018144d2076032140414425464980c14242039806441400e00d420340c8008098104282640c050715041c500500306800d00149145040008009104219110703100d004144888400d01c2041011140440d0820b010780b00d01205210150355042e640e00c036620b501c120100c0059441c00c10071140c0c4840ea9000360090045c0a064504000319071014502c80c1030105200d048002c041000520700d0b0460301048400141c034900820045030391010211074510711824100c5030a04550b8501e86581031092006005030000d60050165183c17405408000707142502c0d0501520804070b034103e80700e000b40700742401c1d1445082c4038440d03098011400c0d0707002814408185112902c07102000b804500ca021001c600082c0340181000c0c002c0d800a40c60310b912800e5081c843d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 928965584 1250 928964334 928964357
    0xc090109050618160207272a020307020f011b061a060f030a0b0a060909021b030c0607020610030c05010c020f030105130b0a060303050906160204050f06011e 69
    0x801800302030442c82d040941e203801c1c100c8a000320254079018801c60842c10706140c410050007070070590150001c0b6a0159802080200c40c400c501088910500d5103000286100d924000a403204200c2d064041c507000f0201000c02c01182c0120180030003600945032150310100d4500111201440c60b00c0980810703100d040c840f0045201540710400d060001440511001e000f54002000d90f000682d500b21280c0d800002c000030100c40340a0188a4031301030302c9084845040c00000b40c284040c5000c0d4030202c682c0401c41041c2c007881c1c608100b21000c900c0d0190b07907903400429038850319200102d4108000d4030a07440070a5102c08080744020460ba0010440c9a14900301001160004141c5c14143e034014400a22032980d55000e118541c05103200b0100c5101d104641e1400710342026001f000c2c601c40518144040000c04e81107011242c001c001210343c1640c41d1b80703504405103105014000650030901d082d003003003a40800c140300140180000d881d641d0300c0d450480328144290703131507542c0c00c0000794000584 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 928966834 1250 928965584 928965599
    0x20310151206151b06060b031512010501030b132924060f0c2506020f03090d02042c01140a1802040213091503030e03030a1d181303020f0c0901 63
    0xb444481d4404e880c0802c0587d6144401201e6400540e0050110b40c50018281058640144007a40b02c0080400a100641c599181d03655000e00003025950708210a14250701046500d4215005909081ca01802070202144850440840c100d4140081242030608040d003030401c1e0034840800c1c640100041c2c541010b5451204c0d441c2c200a0200c609881803041501100c2180f4a0011924242c03030480c405480c90710000070300e015002c84e0551007603001000362085d207882c2d2110000c0070302d40540740411a100781c1c01e55103e00700c1d81e00b07140ca00c0c520050b14042c0890f0106400200000202010100007911102c0300142102c401018840c480201050b0420040c20260058144501c0d0400a000c0e107d0390f90040d101540c08000b02c1480902548209008060300f012445220030300607801541001c07010240604141034860340807550a07000b01c0d001149640f030541c0e080e46a01c804150b04103e00b070080b01d503800760051880c02c50142c00345105100d8981ea00080d000308000008082c3c00969103041d0340c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 928968084 1250 928966834 928966877
    0x524040f021603020f10060f0b0a02151305211e04180603060c0801050603010b1e0a080712111812010501031a0c0306090a02031015120615 61
    0x8208203409010841e400b0901c440c1c00e078150741c0680c004c2c00c3c420524080c12410a1040e08a58884a207070042c140420021003030081c0503582400d90540c2d17101481c7e1000c0c0c5c039100e5403a00589103403920104000025411a001800d600c1c0300d90121181c010019464010307600b90060b448100203024401d81052881448807036030024980c0314280d00d41600ca20024800c80a45000014038039141c003400c0080240b01c3c45410600e41061406032955414100003410510040c4108081c2c2c840c0481c1d003400c45c000383d001000105d88101501551a0089103020b0544081143d00202141c1c941d064000304c1c4001d4042c03036400910810300700d49003a100c2e491b510b503c0540c0d6000c16030070510700441071400c4038003445924003860181100345a110f03000d100082c0c2c0c006008042d0b40c8a54801e1003800b4003600c580c006280c000140803c0176071280c2d01d0b1042900080200d520460700b02a00214101d81160450001240b00d00c0b511000d2026548551505a0201401300d64a000681120501c1c08104090742c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 928969334 1250 928968084 928968101
    0x30d02033c0a050a1b090e010b07030e0d15020304210815041d0f0606030f07030203060708040602130e07020c0f0d030c0c091406040b01020109050d1b0515040501052404 74
    0x11300004280411000c003680d415680e0070850040382c51a0000c0c80480f204511150040c4114039540b40b42845540d07000344005000380d010b034003650041c0c0400d410403866440f01400403a0340c0d034045440e8902405c260740c1c0b42e03d00e021440488440041000c2d4103511511034240305446409403c421004108103100043c00d04114508813001030f2500402800424401c1412142380310004000908101c01050300b044079005021007581d103d03050410040c0c5000c501540d102c0c1e01400c0840030f654690070030b00c029206001d003401008001001c007194050b52910f206009031402da0803200800350345014840c1c0e01802c0c00907280e014840000080000340300700302c42c0103007620440c1040030050b981e1013042d090302d00d0405d03940b520701212420400581813510402c600c408092000f40700c01d40307440d00d900f038a401034075952000b0020180384c4104d05800701600c1408040c0c2c00070071100405426811005000780950781100c055081001152038961128082c4980f0980074150004070700c040c4003044020032501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 928970584 1250 928969334 928969351
    0xa0c080a0509040515030708030c0d031d1c021b030307080706140a050f0c0415030903051308070e130b0f090c21010e01111b030d02033c0a05 62
    0x41001c10310360f45581c001c06001e0605004070409a02109003014184096604503e036030f540309004600000500042840d20100356080004800700000701d0040001800140d0b45018800d40406403000515084907181410b8158240c0307200f40c205480c1036105050040c2200c0d40b45d48180000d07804100c60200803d0f41921421002454002100280e100c9a2044566259050351001040300300c1440000f440d81c04104160464501410311007504c80c3e0310780c5400c200301015603400b0300c44101409401142c031200c029404080d541c560b40e5100d0303642e0b207259009601d0f1008540c2d0108074071404500300c81e640340358421100c0c1c2203a511200c4c00202c5000c01405001e540c401c03c1e0b140000c5032143c41c40e00d10515500c0e03221201112020030003074203640600c107245610740e1400702c2c0304c5d50040300312051b244c6491081205c034401041c420701e0b0510314020301c3c4600c4412807000003444030070501d042076684451403030500d0f14503005804120191420200030f1181301e0301d048000044107481c060f404142c1c0289070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 928971834 1250 928970584 928970587
    0x7050403031d0d14060702060402100305042303090102010f0b0d080d061505031e0403020606130e03041205160e06091306062c04170a2a15020a0c080a05 67
    0x42e00010f0300c030315038940251071522020080801030a41031001c6640110300d800204524102035010698020444004c8020544d550000c902040350003401441300042c100d10070443d8801400c0308a8480c0d2000082502541c0b0f0207418107602400c0d4010740942e0200204a40d400342050b13210603000303030b1045c0c80c550826542c1d82c4010910424030000001c43c400c86540c0e8648034501414191100c0c450f288200c1008a9200c0c104000645d00054440c0d01841c1941c00035a00100700300d4110241910302c90b0501d8900010a011030010600081c0784407181c003680c100c90303081038400d41c40c50911100340508840c1c80302c0580001d4041c100050400c0d046042c0c09807000c288065030315020200c0358103070000c1d0202c04081c887c80c4d0541207a41c1a01c000b00c5080c85605025003070643e17030700880c0c09100815070040400802d403105480c0c040c20313034540507126000d28841a4260250f0071010540c444c0310450300c40001340f0802c400c2420328425500300300450385030000003018036251044250450342946013007000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 928973084 1250 928971834 928971887
    0x60e060a030c14040b1309020306090703110c0304033801210803070906030f0e03090405041e05071509080a1716030c020f0301020a140c1905060a0f02030705040303 72
    0x42c10780108010010746403000e8071882604482c6a803e61b0b2640550402401481840169510303031a8031034101d481820006110904030441008600403012481c00600010800000b48482070a18124060400071030803040b10752640124880e44c1311038103101c040301d041c2e001808100180f085004041214004103005401a070b41c58224640c01141e240300015800c100401c83d907078040c051406580b81182090000d0301d41c00c000070342c0c1c074001c0307030303861480782da100c402040c01d02c01c0040701c220342e04c07694000c06075582c446810b050b66680c1244c030030240b51003e003540fa045054450f40e01c03201550458809400303003000c2030700c4828851407200340040c8441410402c000d910102601c05c0d20f41ea44c46500c03a421070708002d004000030000110300050003a40100301d8902140d81c41041c0812040c1103d030020b464040841941d450f240c0b500c0d85580024108440f80020b101000030308511030b000e03e480600444414409802c168002960260045601407100b44002030203030740d5a041c0403074200c14003060401e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 928974334 1250 928973084 928973117
    0xa0c1e0506030a0b030c100c1509080c0a121806080702100626010b06091306080625090b030105211c0f080609010302040e0f0f0115060e060a030c 64
    0x80c01a10031106059481c4e40c02186401d060120074148442122158510508102c1c09400c0d440110401045210031500322100c034041c903845403075107507086194661512940c482d03403940c85103400001e840c8811686500c1a000344a000501c40c2d454a40c00c104a00302e00d07003041641d070b002000e009041507000c4d810030840c0300c11091290780002d10b074210001c000404061186140358140e0b07000340308a41d04054850f80252110000caa022072400d5968241d0141401860700c002e040a0b0009603460042c601400603001e0003040c0a505030b030f424041d910481842081c1618449550300c40d020140406100420030744c6007203641510020b22a1401142d05184040d03c2414241068400b110240742d1041611280358081454080034080d42000600d80c10710700c0018100740300510009100d51340b1100c0d00345103400c043c0240801c151514048611200d4183c4109001e4164003105c003000198400d40010051700c80c01085501d2200a08424644001d080f011000740095141000074465000341d07014070300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 928975584 1250 928974334 928974337
    0x2102100e040903031a03010212063c041a010206070e0328030320033c160f0c020402070c08030d0e0d110d0305100b04030605090105090a0c1e0506 64
    0x5840f07607038002019100260807488007020010309a000e40e105201d0364609000145005400401c1219007500104030000c0f1840a8803211400c8180d0003401d8080c002c14100c0a0b10b0360303219102c100d42c1405880740208299005807005c40029006911000c0400c076001c3c002c01040d01c10308d40150548005a002c0480141c001078543d01d40c0201200c0d2003501000c0c03640c1486044640c00c1000150710010500000b4030f00c640c000030300031440700601082c40704032864081c0081d41d07007250782a60603480500746140d4070000490447d1001c40203840e082d01403110920034031582602c4110360315452046110741c0c09100c0250014031045039110120340303002c645c48104101515040c06c1d12840811140107000c1507505001301d00905106000070b460b600c055511000c564468003600603d00010155150341c449103101c00503510442503070800040202c14400c0a810281c410281030009101d55120100070715610920311101406100e00711034280079103103294000c000c0e0380031f0395402c000d040c0c1d45030000910786 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 928976834 1250 928975584 928975601
    0x50c2e05030f060105120f09100e011505040507020a1e02061909150504152106031b03020a1a0d1b02011b02100c021617072102100e04 59
    0x200c0e2000c010418050491007501d94008801c0ca840703814461040c0341800a88006881301c0c8100703100c140011074201d810440c85072003d0100d002030090f04840341000c1e0080c030b6842d4043c00a41c5c1c0c0c180000c0744a0801e405020b001e1103031a8010320480d40207444000d2008140202c04d402c4030b000e15814005641c4910260044001c4810070408106015001070013a0724298001c0320f40794050350319205003a8001c0296021100105801500300000c201c04640084642200e603048001c400615500c40845a121905582c82850401c1d18010b0500d907000da06101e82c4002503021002d03020500040c14002c540f1050f1011503407165050500036800081034442110744200c803003505000c00000c50b5424002e248a102101c1c4405401411400d030080d19403005031140c0002c00c1d00ca5030704117030a901c00c1021b05c403a61041c2d50290540c070746840d00041c80080c80000c1c2c2400b4131031070f0303800b18112041850030f42856030000d030004000c0b00e403582400110400c242455060100c80141c40c1540d48079405003061 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 928978084 1250 928976834 928976837
    0x9041401060f080a060807120f0f050610081b0f0121020d0c1d01031a150307021227060403140d09061701141f0306060305010b07050c2e 60
    0x282d03524501c20081c81100700500003400e450034040c0401407039001044080c05d40b0b125141c1131885444a052101907040c54150061003000030000b41380070320001003003050040210742c0c0c0c0c40e00c050380c4d20014540d40340c100400202c141e02c10514882c050380392a4602c4100314006050207000c0d80c0f100c0c9400c81d0078480382d2201080d266000280c1c4440303040c13180701e030024030442c906010b8010326480754a150217685c0c11580030b05059890341d062004080c4070240703981e900d2000f0203d00d04401c3d405426032190300196440000b604c11051a440da28040b03c0a4034500240a0b62a000544c401050148001c841d00c1c02d6542140d004c210201c040791000c06040000c06d010030040c80400d0b1200b1000700a060942e01000c2004024100c1c81c01c24418490098115241088252a148001800190000c0c451000c2000030303504000b8008a40740c05801c0001118100d88081249a81e5142890306600c24603000900681084900000034945142a4429002003404c0c4000d410000381c03480301c04a8401c4103000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 928979334 1250 928978084 928978097
    0x90b0d2004030515010b0d0506130e0309090714220510050901020c06090112020903010b0616120509010504030305031003291e0402011202090d0c05130e03030604020904140106 77
    0x14003a0421000301c8001d42d01c031511031a50300d0002816013a000d1030304647c03001603d034408202c60759240403094910040d029000c116050343c450160303590f40e10211906014801000004050328001c1c4146106074009204103464602c03442c0304040d00e40304508402c00048200c01003c101038035402c1c83d42c80da518064880319a134807460300019140801c400800c500c20301040280c1c00d00c0f0b03603001c4805000c480c000040540c5810b2400002409803503610710990700000c0101e0b03003410710030301024800449030050909403040302c0720300002c484030b00c606201c0341c0c04650100010400244103500556101e0380040464000e80e44130340d641c043c451403030640d110003828008024004000c1502000360050b00c000a00c02c2003000c52131200c4021580144042d040c8040d03000c940d4410442070b0110b07200d10200034600840003d06160100e4901034034040d180c0101c02c0ea00d43c0703061a2460f8820b45600401400007141599031f09410000a90301c000505070300300e5100c0d0418031501d86142141d0380a8460343e00c80c032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 928980584 1250 928979334 928979339
    0x703060606080103230c0d020f041419060308030408030403030e0601030629030a12200a140606010c121205010e072c040b012606100906090b0d2004 65
    0x403026800c5849504a005c1501c0702c540c290749001508001451042e1107045041240e400010f00d0040c0d00408250005e0500344940525800208124826501c1030024004412a485898100c40d810300004080c14020001306011071034120155a10034440d10380807a00c1d101c000c3c100d46c284003080c3c3c81240c0464486501c0758010412912000c0e5088110307001e000c04002d1240080d40d14203060030f0113402d05904001480025115500303143c559403000743d82170101144011480ea44141c0104103840346101001c0c180f110080105165010f0101651401d00584c03840d2500d5482c5450840b09100340f010132120810280c3c40d600030640200025540c0050601d401400586012410f000d0100615010304044164145151001c4ca4005060307400041c1c401400b00141c5445451040100c41030084a44c646446145481e245205000c02e4801544d40000c4444c20b695a000c02e00a8001080d0700820610074419101c0242000701840c900c00b00c0c0c002900c0e082d0321903e4140b604c10401184000509 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 928981834 1250 928980584 928980593
    0x3110d021e040b12060a15050d050f010f050402010c0209150d030305090c01020304050604350c040c080c0d091a0103030f0f0221180310020904050604020910110703060606080103 78
    0x3c1c410b00d07003400d4031343d61140c0240e840001e1300c40c0c45c000c00340c20300107980c0c0300107880c07510070900c0ca10701408d4042c00c080e00c4025142070603551840214a181050342c01e03c2d135400c076640c215004840c010751f03041e141c8002caa4502d038200200c5800040410f2044141c1080c09041503540004421805010b52030000300c50074000c0301a41002e0f1010350040c15507104000402054942c60100c80c11185c80580d1001e10003a0802d90603445807240641f1500348110b203080d245614408920722642c0c3c00122000c010008103102c059815000407620014600b00178000c400b404035003030b002054032502c0703035841801601c8074108041d400082138005030009500e54810180041c1c1041070340322001002e00040012807644114050746c5d1041e020910b00214001c20324000391801e10390b810381c50800080680340e0869000401600035013002141c9481581403e0108045040910032501c180d00c0c090020010f81d15640426140c000070102c200807103100e101000404125113100f440c000e409156500d000a5145051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 928983084 1250 928981834 928981841
    0xb0403050106050d0b04080307141b0c0a06270b13050a09050c0d090813080c1509030304030813090e03030a11090a0509130c15170103080403110d021e04 67
    0x206600540203283d904c4082a44003203510351240e4020030441e80c0f0b03903614008403440d0070704855000c2a07403c0803075990041c00c016006000000d032070b4402c54416400c2030080251a40c964401c800c0420500c0785000f401c640c020b000b101200021801d4102d03119035404081c4080d50150f4041c540960300705405010390f29181e4030302e10040050600521890800c4451400c0700c0c421701c81568007842c0c1c0d4002407801c000c044019206900c001c8202107884a40c0c5090090322800e18000444c410109224444482d107201c00690707a0310000940110b0815003555250001d551040321201851501c20304002004048e42c01131030004030f10314000d10744a003802c0740340c841a9103041c001c50300004020711900486443d9400b1b040e084550881c0c45e490741d030301c40c6054200d40e0307003038040b010304800c90110001c80c1c44058040c40c400d100340c00e55640d070f2051048100d80201640700380402400d03260100030800109500340102524800300a003104903001300b07540041c03c441d6003581966002d0300a100c03205514a031901c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 928984334 1250 928983084 928983089
    0x21c0902090f0708130311060901050f130c090b0d0f0303060806070504030b070e0f0a2405120f0a1104080a030e040e100504060608120705060c1303060e01150b0403050106 75
    0x420300c00281c1040c85018095120007409103000c0c03903501d0301710310902d482a0340712803e503005801615410708000740820301070801250011603d54950000c65583c40300c14004000c141c3c1c020001000103820300b05c0c08406400c00300c8031140d00c645018220004203092030321a03000d2034802d44000503401c0c908a4150f0400200070142d41c14050180700c100042204180061341c00200c92902d040c05204030b0340028030750310700041d00a4201000401c0401c144e00303400140040110808425142900a618200c40d1792103039406030101c24510101080d07450390090389054000185040c080b60341d201200340054643c2042d0b00c0142a90b102114440505421140900700940d0554090008030381b4240455a500089010184500d50701e00006081c080140e0040c8050580202960f2000901001108441d0400502a1618040c41011802100085040b6000b580c0c403402400009851034803500c00811101c40001043c3d52a81c1803010b8800688244201914418015a40b100d0950034400e084031302c9034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928985584 1250 928984334 928984351
    0x12130b1303170403051c060b030c091f0f0810080616081602031815040b090111030310050607030302120708160e0303030109021308010c1d0d030e01030c03021c090209 73
    0x2083c080402c3e4010202c0b8030708041d54100c007003446d07600035520700289400d6000901c071403000700030f02101c18018001041c3c40717a4221400c3d0071280d4890b16406c42640409a6400031443d0a01051a03550045400d154094000e200410440303689031402c5007005011035485441201c2545144070081d0011841c03170300600324245a40942000366000795492003a0391101001100040500c0c09a40d514201000721000c00001d10b0307140c03607485d0003415407500143d007200d000c40e80700c11591888140c0003080c2ca01c03502041c0316120f4075500e01001d101d01580300da241a803c05408009a0880700c21704100c00d8018062544c030020b140c50002588004410680e01c09001c01c4144440c1d007106a9002064030f055a055100041ea03aa1003228024240b20301039002e00b00550800900d4460340360040c0410f00b41e0070010300241c040304284d40c10001004102040207001c108a075941c840c295109070310410780c052083c10014500300d500700b131101003180d0214401c0000c03a200d004040444c109a66603a4004004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 928986834 1250 928985584 928985627
    0x20d021207020c1e04020904150603110c0a0605130b10030507080706050904020a110a03020c0420120402010e191502060702030a0c150f151a12130b1303 67
    0x84006090011113144503102c4401e1507241000e01c0c0e59550480b415054014001c00001502040282a5518030f20070080860300d81002c42d001c4120300700031600304902080217040501c1199403950002c000103090f0703142c1940c90b1100400080c4103844480d011f0280c140d86009094614134206140800c69005010680c011000400440750403405450315603104503009030716448021411a0700707004003200c610039071043c00d002605040e00410341c07110146099038280004030074907101900030801080035050201081021046039201102d03c950402d00c1450803604124484002415201c41c1c2c2e1003c0c00c030190f9051081200a039000c000da1a450b10318000780401d454030321400394803030280100c4141031041c100e00c087c0411400412242c0d1038080c2c0704003003043e43c16940060f802442d02250440c85408110341c080f401c106180c111a9041408268080c540b16000f084280341c407002404a03010a591000b0140c00200e41906c01881002d2820800c2d201d0566030400030100c3c0030740490081140035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 928988084 1250 928986834 928986853
    0x1e090909032a1002070b01090b100906031d03030c250201020706080405120d061518170a080d0212150612220c140118210501020d02120702 61
    0x800094020100d840d42e00c071403400c0c042502d0500e0401a004001004061000410742c04000c400c480380e074161644c6070300401c0740030001018454082c1b220031812010900b4204100b2035544a40c20043c803c520f03601801c900c46c2070340260145140c0041c4c40109044101082034030707419504034200004041c013400c801e000000c550700080c0d1615514042c030030800c90658001410f2200811108e90041107074200259190352004421000301214014214402c404078003038051940b062800181c0d00c810401f803194582c2c0f420009500041d110b42c8401954000e42c450880402c510b040074000840480b1009030766490300035410940e100000b011440c1d5032841e00c0c1941c01544401d0141ca0702c6c051003ca00880a40383d080c20f0200e05400c842002c182a0039062501041056378000c00085440c8a08001c0304694070130010754900c2c0781c0c00c40da03110203a041c801c10400031142c05210310b049000152030310000c40941d02d031142a41e000303521104041e500081c400010380005003090781c4c08400762024080c4080d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 928989334 1250 928988084 928988107
    0xc0515040b030a0e1c0e0a170d1b021206010e06100f030507111c09090b0312180a0b070c090603020d0b060418061e061a030c1e09090903 60
    0x900764000140d1342d0302520843c01010800c030a000003d202d0350041800900800505c001c04d880d00041c000c207058100003c240084d001e0b200280034500f00608540144100103d0720389100318a46c58506460650400158864201c1c01d01c80360307180c00241109604042d604400c5900191016001c0d01501040c41c203299800004109080780501e00401d1640382c12004446003494001f115465010300b041d044d140d0080005603080884032034607031500403580d8088180484001500c1140c06030404c1580b448100c003808000c0504c2c54007001800d0010920002007030035003278550081c0055040001d0344600740051502c05a0042070540800d00c80b6500f90703404581017004a8100400790310140010445aaa698200f84164031740e0703c04840400307c49040c42c0f8043e041d8070511841c039480408035812521010b00440003592103180c1c2000018500b00300510481e1b20080c03c403164408140039041003840704a440750741404560075030356103a6540340d0030070400d00c001411185640d4030400c050071650 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 928990584 1250 928989334 928989337
    0x302061515040e07180501020d0c050102041a030a24050d060f020307031d010903140c0c060d020403020310061a0901021c05070b0f0103080304111306030c0515040b 72
    0x80040c0081045469a08011415540d091160504244008100401c0c04003c0c160340a200f05900d07030f01d00d00d41110a07943c054106542c0d0040390b0041c0c20060018154038020040043c00174814ac00040c9402e641f15010340c1c2030803100c418065046000030500401143d9070003507521a40281e0500441d0b121501a25580c18002d482694010603c0050305024440c6580c000b244a10481106554900d4005002001000c11003042c196800c840701700c0d410b0a03d81441a014450f915480d03522282c0b0715010b10102c1504611001841c61092500083c0d42e51981d20140008400c403860158983d07085104050504a240b481e04400c3c600c1d0203401c1201c034940e1a48000501411070140350b43d2020758004031306064200d055102102d0400d081e070407030039520500600009018410340d0005458800c2008040078003840b001d8402001400490045040d142c8200740c1004002c1c841481c0c001416044010744290307500986454400f488204140e041200d074004078100613504043c94282800c000c0c0003035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 928991834 1250 928990584 928990591
    0x1205090607030903020c030d090f080c060904241526150d0204110304050d081501030b011b030807030c020307050a11040b0d11031506090f0403050f070c0e13030206 72
    0x1c0640f40c00b950410306009016584004034080d003620a51540740c4005045650903208240d00e0904941d030000d074220021801a409100c0280a140344c480401d0403c00a0b14454114242d40050083e07000c0d420761112801800414202c516800c010010020282c40946210310050603090601c0c50021100700c60310302030307601c510018101e0905030401c10103e0f1031160741400003500300e8a001c103260075528060300510f1141c1d1140c02103410507140306008482440040d1805981840030082c031f140342e903009410800e8103100614203450104180c4606040704240d0313400a501003003c5070280070589600d8010600d80080500047d850a002590307104da868a54100282080d0245040d80c0d10540d41c2c1d42009100030030040000c40141c505091001d60400f00e111130030700c6403082030400c0040c10480030003544921401415084940e8503c9250300082c48010002c40402200b0840301003000321040240000b030340103119642c1c940e4180320203640c9000340035000c0104e000101c18a040001d500248840d403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 928993084 1250 928991834 928991837
    0x6041202090a150e15120a080c160312020607030b10050319060b12060a0b0f090102010609020c03091206010f0b180312031603061a0901170103060c1205090607 70
    0xc050b0b0301c040c050707402042e00010810045032026800290310101c60702d054000c2c0100d100e2148110369040030003000d4860103824110a400c24080500400c07151800703882003040c9003095030b0000c1c1d040b280406d410921600110307070703003014021980803007581003080c182d200000341410405c040075080000c03045000b60342403100704500000050780c503031080c0700c2c5940c0d60402c0311018401543c4441440320203800c00548150f240c0d2054000800910b0192101d000300d8000d0a00c0901d05044942c21500d10340c800a40641559203407000011646001e00c01842028456000b0316202c951080800c030380c0c039811030210506540250014400604401c502c1806c07104500794460f904d17020b00304948011007a500d0344540c03500840d28070b0003020b07a8550085200c0c011406c98000c044110b0361007682180c509000f030140b805009084071117814101001070401107070505003040c003203004404a02c01c0c0c01c4260000c40d038058960b24090354260300000900b51064090b10180610f18002da481030b41e03510010708410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 928994334 1250 928993084 928993099
    0x70b0f0706060e0f041403030f01091107020d060203091501180902120a06060f060f02210706090f020306060607120e0607060f05070207050a0807030f0804081e060606041202 76
    0x1800c006059106400510090004070f140f490060311114801000300d0b0160b46440c0080da850558a0011044910414200100181507424150290018581c0014080203020200308180160381c4142001440503c00d038000759682c580a4a0241801400062202c2200d00c1c500144525180e529003402c1b0765201c0c070740c00205074100340001141000c0d00700200e03250303004407505501881481d40004080e2005482d41e041250780e0f84c40201c1d1034100c001c2031000180c204058001407042d0106030103210301c41c180940360030300f101505e90500b280d103c000d013220200d0400c0a03040440c00e041c05040d83c00f040441d0b005042c00f0503502ca480600b4481e001540c1007000038504c0503440c0e640c5e5015181130365084030f820800d64000d118000014242035810030f000d44240100003843c2d141c22400501503030b00102c00f0300b4038146580d403000e99030141780804803a41a000d010204110101b00100d105a09101c9916030f01801c40103060b03828a00e0142c285801407030100002e0210510142041c1c8a956040d10203c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 928995584 1250 928994334 928994347
    0x110c03030702150702221b021c0917030c010c050405060304080703050d240b04270615020610060503040b01031e1b06080c0c15040c09111803070b0f 65
    0x142041c85074a000075800240140f1a00d41d00c030100b40401c0306c0b003450f044200404116400da407001c892012160500582c440440c407090f5047c0e01c4c100301c0496000e030030a251082e40329002e9944c10400303080c4072a226800030035000091003090240d202c400c4075034102946460b0412002c00c6d494800148003500c0d10300009100f000309032242c01110703412010340f081081141800e007945282032855003011a40181c002c1804101d00340038000711000c690313507090481150100070901c44441e02c2402c4042c0c042c00d03031b10000040d0000d11800c940e030780d9a080d50301034044c47c6005c00100948600a8010408102c414010040003c06142d606815a40c103c250514000301c1511003100307407041003100405028031903100c4240f840c01c0c0c0c4046429513045444c0c25680e583e508003001d0080c05a10030b07040f050350228103003a030100d50440c0a5130b0001e0069003244002c0c0d0b282c004000a454000c0001503400074000340c140100d00c50b4403202c0c41070305c41c11005013401526105000107680204440902c0d402000900c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 928996834 1250 928995584 928995619
    0x70c081303150e010c090503061f05090a0204060801080c01020a0308090102070c0b0a0f020f0604031b0503030f01050a09020a0e190905090c150a02060f0612010219110c03030702 78
    0x990011944400c20b89410b0740640508005003040100440c40796007000d2040c00014003071603070b00b015104090010866a9120b043e4800c064041001000340c08202002c049150b40b10300d88641e100344108803016a4551a211300240700f200140e008007003a800c41a9507030016039021408000ca00d4151070b00c0400354454649560080c421404000c0021044400005000742c82c100544909083c0d510349021400c0f01480a0362a00e030b1030800ca10702600244002400240030303c22010102080d00b0031072a1403041580c6851a56000b030341c40480d140d44c041e004004504c0e05000c40b2001c0c1004002c154140703001c01e4405800900d024036a80c0c41584c0e404100007640da00303114880002e080c0c402c81070000f8203101000a40f601105800700d4011404004905400341e00b40003107850202450b801811241e40381d100310703884000081e000c1d0742e00c44054200c0b030380e091000f400944070f5081c1084140a03055031428015001d8810200c2c08429504400c801650907503000c41500d100b9901541c0c200d0784d50b60b00c40324 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 928998084 1250 928996834 928996867
    0x228021905190f080d08040620030a0501140609130509010e011d0601050d080d020f090d11101817030c16030312090f0201200f0a0303050a0203070c08 66
    0x540140340b0140c41e600c0400041801c0040342d4401000d0079006450b913200549403991004404045800e10005c20f00144217030f48028049480010201e80c420b4036080000440c0d44241c178802190358a0318018011405800c00c0e0201040d01101c8491924440070041084111940c802d6111242c1d280c0010f50449029041229440d44c1c00c8001c000c0140e45480401d001862034800c100740d0b1186000100e664200304082c450944c6e0230146103810010410810740280d4007000d0400041c0074203018064441c2c44144007000c0b80351150035002c100601c90018010f10194800d0b000003000724040c2c2d912050056050940d003030702c0308410005c2207018040e4085185119100020080d88952840c000150510340c0c04242030b24800d65038150049d811020000540d0541d100c00b40944040700700c030200640c05003a914000c01d5081c0c01650980b00136281507810203082e0326100c0403d4124601034000c066241c0b00709540851160b90850079424148402070806101000c0202645400204a10114110300c0e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 928999334 1250 928998084 928998089
    0x30c0c0302120d090b0a0905092a0a0f17011203020304080706020607020f0c010e0d02010c0c09020319140c0702060c060c040303030e0c03060403210207050105060102280219 76
    0x10000700850008440082e030f100c107100301040c0042c001c020041102e0810030100d90040c010303a81c0f048a010308000c104401e554024240510990900da44461001d981481c00709a00003107102054441d100c3c031401600d8500c0c18204401041414881c1c488040e84040c0e0703e41c191510450441820702081c50b050b807542c46140c01404070361007241c000161603980012030340e100326200d500f0b5500c0c1c401c000c6241551540307600d4a041c0031820003040302c0120704122840110741e42c0140f5144840c8101926080419031030350f000040120b03000000c104d01d002c1d02e512030035a9424845400c0003540300a4411510441340508902c400c24030001e60b520655880c03100391840d130504031090311014245050301064580c40f40c13004a0100b824480700103c15000070807154241140600545083d95965908843d003000c034038041142c542400404542e221203d10141a03190b00c500c000007403d05012002918007600952511540f04408050209200c179200300ca440140e8103a500e51001c451a102d0031500c040c1a8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 929000584 1250 928999334 928999339
    0x1d040b0c0403150605271f0302040c020703030813230a0209070206150d050c04050621061509060a0605160204180b070f02070302150409140a27030c0c0302 68
    0x10b0095201c042d08503848441241c1c411141d01007480100d503080d0040c1d0305040c98103510056814002151f00c80c40b16070034100c00402e80b61840500d41c4903030005086529800d007000c010b900900c800e104054000410340d070044130104a00310b01d801103aa0b22001d0a450000d9002c42c00060140000101c00400c940401c5607401000302c443c910301088001c1d917a0104440036480004001340812241c14269111101c598200015040d070300e0017042171002a100c00740565420195643c2d5000d40821030803001d480b80c05000d006800d0500705101d4a008003900200d4462040410070309118441c0da81e5405841180d86a0400a80b0340c1052920403902e11070624001e5007150070450110990210714000030026881404940002e44a488040b601075416151000258ac4580030038070261902e60652007068030800160340c5815107032100741d42900c03a5180d01680c510342c0801480224641c0d405140c9072080d511242c881d42200c1c0710740f8180d03005c4852401509000e049203020050109100d403920255070007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 929001834 1250 929000584 929000603
    0x302150c0703120f0e06090d1404050d05100e030d111204121403010909021e150c010f06090b18040804060e1306081c091202120f07030c0603061d040b0c0403 69
    0x314000d413500d4203001c440c410524021002306250a6001e04410b468005468281a050600b49010f01046042160007501c49101d111800444092a4050703d80c00107040401742d0385425002d04003078181c0d0101400b020001d107041c0030326034070110403820303e56001e60000034030b0320031070703c103d03816501080b00705180c080e40000000040790b580e01c590490301c1030324401d66840d03202d8114a00d56602848007490310390741c0409803d8081c1e41e4105140f000e8550a039007800001003544c12039003544100d4080707503c4500810340b51480c0d00744500d0a4540c01482122000350880c003450b155035840e0107442140240c900780100000c4e03072100c1c0d0319400011100181c5c0d51a0400c143c1380c490800c03580d5208456455018124a02140c504081c4100303004400c0751540c42e0766001201c840d500708466100c038030042c8000e0303114140c5e043c10240b4040045030000c0d4098491614130341e0910700000c0c2900c101d074202490702080c551640c2641c40c001104c01c1e031710640226106945844403140d442035032040781d1001d8106680e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 929003084 1250 929001834 929001851
    0x515090d052e02090d0b15040906051501020303150907110604030804020406090903050d02071a0c07020103111801140432030109031d01031d0a0302150c0703120f 71
    0x5070944144141d03407000d04020600603005011005a1089541c3d01e41c1103d407114174903001501000b0110341001150007801c01001041020030300b103644015064414544960500c61520f1081000c028040320030310285242d0314003d4000c9004004052030140a00108000140f543e845003255514110408041e00c4171401d00b0b080041401d581610164442c0340751000001d5500280d00c5500c95050381a210541030000b10b10380c107002500f204809490402192001c40c0d0600303800c5a82a00c01c0700500803c5854a80e14000101260345039510092503d2003004560038800d600024a41c84c2e0a0034a008058081d0b219980d01080c012a4445c50170f03825001e0b0450501103052010352480d40c00d001c01104008025000c0609a440040e00600410030000c0328041074000c1c031030b480042c0712040c140400d821070f100714a01c001000c45e44c43d0112036005140c0c01c41c10594107201640c1c0c0002c05940030b182a081c1003001122510640c0c4004051064100c620100141c9641003030307035040150f41c400c01c844807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 929004334 1250 929003084 929003113
    0x120406020105090c1905130b1909050906071413031b030614130b0a11040611010e0a0804090f06080a0f26031501030905060901021e040515090d05 64
    0x3800e0321070840e5409041130300041800c003a2440e0300f0511101200910140c0b90200b0b00ca030300c07865a0141c0c001c0d03503291105030009468004011600c09a84144603401601e0201c4150032184090500b07034058101900340a900c56000c038081200820a4262075a100c150402804000409900082c03948400c400d00240c989410910384d4104d9014007004e10901d500e4404180c4c0ea60700840305c00440d448040f844e000805e180c1d560580d4000503042002403019081d803144110354003d075101c5000146804401440c0d60002c1c02030341100300c2e85500802c00c2032180c0d921700c002409207004a0304d00035aa810407d6500c1d40d990040d00040c02070b50155007030002581016815014401c00a1750303000c0105618140410061600034111080c56850f42c0c21500c6210104201c1651201124105602d8516a4003c60400d000c0319025044550006a03601e03030700da001d076140d0003035128800f0b810030b4107210410494075282340e410345d4100c0f1484400d07070704d6035100b000809480c1007107005013851141504444098 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 929005584 1250 929004334 929004341
    0x50c0a12030c0906080426071506060e090402090424060311091b16020103020f270f01020604060203091609050901050c0f16080d021c06050906211204060201 69
    0x400740b955921111940703c0b0800c3d81e00380c0c000d81d80140403000f4180b00c030b183e4059010011025080400700d2901d81600340d00d901104001b901c01840180d5900d00d0100030301034101107104509941070340c641a00c0e1901d41c000580c5080b00400150440785140001c5403000c400301c558440e1003000c2c0504110140c2c6074105400d5005180e0a02c5001d85100da01040d00c4000c0c403402c14040d00f2104401c5803414000001d040e0b9400c64180c0100e041c181c0920424102d81050303006029803003c044d043c1003050809408610300f030352a0a0310382c0c0c02440240680e21003640d010829a0703019400c02c00250303403a161914210301d0010003001c04405182c41c1540030a411891390003041c0580f107050000d1100340c80708035827084203105d481e82111401d0070800c08900e4440000d50700125144c051240242440013101c00102603912104104421503441002d0350b54050a6204001c00780c1000e54500c0e4041c83c04d00041507080c244028510504500811041040c0c02d0820401410094194419440360341d1800080d02a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 929006834 1250 929005584 929005601
    0x902040e1b09060402090306040f03030f0614100504050102070b03100302031207032601120606090f0617160b1804140105120a05120c030c0321130209010501050c0a1203 74
    0x110008000304030246000e00a444506031b0080250505417526030701c040604424400890034542c80f0b1a0200c1440d41610441000300300c00302c117540c0c000d049041040442c0b00d501c0030101c1031060920041c07160341d90000c0c804007903501203143c5a9903521003405920348459280d02c029818070507008110a46242c2c42d010384521403003510b030b010365083c81c1e002c504c10300c2c1c4580c48040c140100000040110b07400c0340d580d001040d1b01404000515035103c00c560825180002034250007561035000812803010540071100801c42030b0320140150001c4120308c60390801d660311846000c2100813500a0304c0403007020800029000051003000340005201c1d048580c101c003440384901c94021111503910444e408030308804183d50040142000c10310070115400550041001004148400d001c0e03001c0d107881c108002c254800f610340310300c1d50f1709600014400d84500014400c1030106042e654030001038035582c2400d0b0540e102420015241d01d24074034042e1802d1450780e0042c00150341e0221590a147d00743c3c0c800e091 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 929008084 1250 929006834 929006839
    0x9040f240e092d06010806091005010b04090c05040902070609061415010807090509040525080c09040f08031003060c0c0309170304030b0f060906040e100902040e1b 72
    0x100565501003814090800322201480d682180728404421900d03540420400d0107510346030202c0400f225180e500c1c042090b0844581030b0f000305c052006101d01041202d0001d1032944050001d0342c105006242c40740241d10481d24103a440e0880725000c980542c090b20042d102c2001e045450b180c1c1410a00c02502034001c055400d185858005140f103c444403600e40b04914480510342054041c500444075000010080c2c010403034507000109050381c40350103c5020b50b0003040206215001841843c841084540185500204a810800090b07501040a00040000f2588500180ea89041c03c14000212640c010101800001082454840c41407004156801313140304001c0c0c0c0c0c80c07421007134a074081103800285c04038181c0d45003088010b400b41c00b103010190821054905181e07595880d0303002540203a4500390680c03044410440b080c20710324549a40310720704417414401c1480440368141c0b034000d98040070032540d890b520b4500a41d11540c0100c88018081011900b115810030040d5000a807092451403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 929009334 1250 929008084 929008151
    0x3d14091c2c0301060b0a020a0c060816030507030209042a05040f0905090109120903110102030306060711040e0d031406090930130509100f0b09040f 65
    0x80c030500340c0e280150180c070704080401042204401000110820140e419900c500010404c143c6500182c4400707007a40c2c0003003c8066161a02c8001020130707404c80c000700580703481004130410030f170004201041418240007034151100001240031b8407a441c05076800c01c0c2802500c2800e402d64010f89000b40380c800d030f0041a0820803407400c4a0901c241e1041c0c584a80d24007401b8804001560b0003960065174582c00001c40c00d50641c0c42c04c607148600388015010a41305041001031001c42000d0801c001803d00c0a5803862400e1000540d10b8000c1c0e16001c0c00701c8a050021034082d84075035000903425061142200d41074224240024046d001c1040483e02c01d0103c5400300d01c260030700420090052402d1000342c1001c6800d244d040480c1c6c44e01d6400c162500780c3c4911119a50580080144007030204807440f0240e0908000502081800c050700203a680c210b1000104142084c080480e01070301c11f90004250740300d0b00500094050705003d4480c1010a02d46640941c4100c80c41d40a448500510760108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 929010584 1250 929009334 929009383
    0x1180212010b060a031a36090a0602071b0312170405030901081f090b0907080702070311210d0311040b030c0d18030e033d1409 56
    0x1542030b54032034003200340c01500501520070b100d03000340c000060262840e039102c01c01045a0000800c0261030100319855489541c111090083c440e14403181c60b007002d000d280f0018101442405e90701c0058141c040e0110740d0100d00324041052180d034007060b1404030302500800581324282008860341c54245600420010032400300c4000c3d82444051003a50844041d5043c0300030180155109600200401101480210490f100380e4001c83c1c00c0020b40101000018000c843c03000740704015001030005030500c4070007010861265030005450b025a03500404c1c080d946046200171551f05400c01e8210002681c0c00d130300607001c40d44002a030541d0075100355014454000b44904600390f910460040243d000410800540541e0301c1400400c48180048400920f8448440f0210940c46054004500040105030000e0f4149404c1100751384085003038151890380000b240c04054801d400c080881d16841841000c0c2c0c45a0456a1010204500c0c02c0300f000180d103003102030252101692000150807030704207500c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 929011834 1250 929010584 929010619
    0x1080705010f020d120209060d0b0f0103060b070f1e0609051501051c050c04090b0a060b0a0c111309060506010f0908031209031b07380c100c031a040902011403090a05011802 76
    0x590302200c06013f001c503c0d00e1282d071100111540c00c2c000036950580c038250803102c1c052a402401c0b0485000b0000051244a00d18046050461001c080d02240c000c0300f00501ca10307910080c03171020860011050140700384013403400d641004411100c0300d51161034142d103001031003038818046100d51849041041813948403078003000070380244680e0710002075018203080000703010340c0c00040034014002e14501104065800144c1696580c003401c440d45070729501803001e0781d600403201c031048500608011403034904040e10503070f83e4000e18031000713134620340000851207408040c0215001048050450f41d80d68a40640c02540c03880c4030322880744841c014190354a00740402c44050810b1000c5a802810402620400b500e4990007c01c00c0051078020221030714210202da03c117030181d1324081d0300d000c140c03100804103000444103900350a038007450070702c420540103030382c030092850a0000010815480e629030382002032606d5540c00c4004e20542c40c1840b2415041c00f600411402d80f4404c83d1078a200c81b007103030b28 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 929013084 1250 929011834 929011841
    0x9050717090114040c030605060f030c0d060624020f0303090307020d02280602010b04060312230d0b10260601170f01080705010f020d120209060d0b0f0103 68
    0x120000016000c1540000c1211620303511600031980200200e051542e0406183d140f400c141c80440e880700c80b802007082041035034007545a201508072080d03074040c002e02c004203488008002805214440045942c0c1c1009a2940b0943c0900601d0711103a24450700d61034000c0039400c2802c085409407040c0c001e4501d0f80c56000080b240320340101e501850800d41e0903400e0000c050003500003268400200c124070320241c0302200300700382e20310400c3c60000c540a240c45400b9003110000c441e0103000f21304001c024008507055a2903240c807042c462a16440120381c0b00c03880c12400c1c0202e0385200320120b000484020a81042e00400d0100c00201e03000c0220030340100c2c003510320040c42085001c040e02e65422a40d08030002c00d0b40160700007018108101d0303030308000f000d00315084402c07102d16404c10300c480014010751108000b444081d10382801c1c90449800c0010780030796603058542203c010028026000008045185c058440644019101d640c4400a80001c0d0000d000002c40c403138065240e80d442d40100d07600c20700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 929014334 1250 929013084 929013091
    0xc1c200a050d020a140705010902091602120a09150203030906100e0615090d0b011e0608011517040b04020103050f071b0c17030408160b030619150c0c0905 68
    0x301c41c1403410300761202c0c070000307500645803800c203100034a0004000c2c2e20803507000b4602c00f80f2a60000070700701818410043c106c0b02c0540354051000400721100c5c0c2c0c071a0001510501824030401c01071b1100d4002404848040d0300d0b03040b0303070807503221070704500c3c68140c00001540c000d2107400151340e82c85e61180000e5040c0100c500c510142a5214130102e003860419142da803548402d03e0a040d403906907144003260000144010882e4241d4120004001045441c0340d801e5407400401507828103185012002045804180038541d07001c503140f6840f58020b4001c084507001303204150b41c1000c0928183c180008600d1045400b030b40400c0c2000c00150090703580c0c49942d48604001d8a0302c450342040050040c4011507080403c6a08402c00000440e00383e45481d600716908503604001d50340c4505100525060007100405c0303541482c8080e00910034481520180c943c00704060328100d020a1845241c60003406046d03200040010400611051450344001c191518901842643c0c0c42c2941d9110200d04540049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 929015584 1250 929014334 929014337
    0x1031e0804050609040b09180f01020928241b02030d0c14010504051e0a0b0105090a09140c03160e040209190c03020901080f07170c1c200a 61
    0x3080107200c2ca2500c00050b2110036030141000070b0940c0c0c20004a20641c0702a1400248191124002002d0305020404014030424a000175820714005c4001f01d89910f541c40f88040c00d0307043d000340034402000c904100743c0042034490150b4505010b0403c24030311981d441c03100c030b5000810426503038242804103494a4034165004d0002c4c110072010080c115440b032031140080b40e60070304807020000c03485424080c1c00d01590240c800b03001030a0341000f01e0404503118030750319503440e00021681404502c4440700c075411258241c071090b1466680c03501d04801002003420040c112401881c2402c0300000c00200413405207801e900700d0300c03200c154062903441c0001d43d100740c0c0682c010b070000060050a1220a080d0840d00c1c0901c0c0b80c517500340007a012030070f441d01000d1940000303501082214440d030380620403d401100441e16051f250a0002c4001c001071010300d501c8016112200104081542c2282191050300c1d2041d40c840c0800c45608840c800780c85807400350300101402c0b500f0044001c4281c400c07115684890f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 929016834 1250 929015584 929015587
    0x9030e090403090b0a2f0c0a0e061e060310030308070914190b040902181503070f090503191515170106030605072001050c0f070f0f030801031e08 64
    0x5007040d120391580001d85c0d45042000701d112448944142e400e800810366829644104a0702d41040720754a010b08003100503106007144a0100040456421340300d80020003544d14021003485001280e20750001032590300c0d0070807400810070202c05460038200301928400d03501c501441e1120b603022a961506800381e200c030440c030001d091010b07242c04a00002c0344d0212400c2410340710340d100034410310b0303400039880581420f80010329015100f202c0c0d041005440c0d000c8a1441c040903d2068241081c00002c1001081c4100d04496112150160b6904001010000e048550210103c010300d001060903c034211540f0000008588100c1440d0245040104140401c49600c5282004010680f9055080804a9540e82c080131021070950b0082503c1001a0744034007005220f686070301c00e036494481c0c0c1805c29a074074110600000e036191508480103501014412500c1d40300504204095a0280d00024400c104810003d4101030300141007c1c12030f40140700401c0541c1d6461002c1c03901045156004200748030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 929018084 1250 929016834 929016839
    0x501020703031a28050d030207180216020f010309082a01140615040306110c0c0a0f060e040f02040905180706051b010b10020f160506090418060207030309030e09040309 74
    0x9103898500141302d0046106681c10354541c00f0990100ca0014141d0041c0c006031401d02145008489004015007040ea0442ca0810904088070318100781060003807182e056030203800ba081c2c0c46070308551059504a40c4050b944e5460140c80e40d4152640322a242e1900d11800e1040710b402410311a41010030842e8181c04035650b2200100110380d00d580030180010f600500001c0301140807440340d80e1810524160103540d4040c4448614608150a100c1601c503d2400c81c0511008481e02215812220a410003440c032055803c0041d01170b0281d8a0a410701c148003240001d00d50a0326008103001e040c1c00c142d0b0f40c0e82c16840507400f5441d80c040d801081c010450400c140f0203910b440d4110f100064400100009160b90700900080500c1c0d403894081006a20210312400c022005002115030108182203034803100340382c88085440b41c06408800c0340b04540e280300c0d52402041e2480a1500031b68403900c02c542e0342c0342d5880c015008155450f401d90010310650300c0c40d001030130004401d600071505500d030f4074481403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 929019334 1250 929018084 929018119
    0xf060504111605280209010b0712050a020f0109080904050907060507152c010e0313031205131d0a020a080a0b030f03040902041d010605340501020703031a 68
    0xa4000d0111024450005000410030a848520300000e1010b03921689451017801045103000041e040940b1700e960400c0f0010010314980140d9100000600700b5035112450004240d080094543d100c110341d500b0102100c0c20820780d00014090888129010005512034000240e0f9400460280001141e010060000450007081c1c2c41d43c80200d003007502141c0c4503010000480c0001c201c80d02443c90005182100000382c1003801707000d1040b064400118284098030070746031005086440064041048441c042d0041c51140d0304907001000000d201500ca641e4aa500e081207a05120030507100301d1480c00401c40549081c0210342070702c042580c500c251a180d004041c0002e05540354030b0340d4580f00d402c0c0c0700340c4844400e1000e800280380a000050716540303428140e0f403a084400c80c42405a21000e4014011190064281d840d035505400da034800d140c0e205e0700030030504d400c4c0c14030040c0d030303907018000f20010454150010078104d44240d80900940c0d80f0040c0c40c90400c48441449944800010036981c40c81 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 929020584 1250 929019334 929019367
    0x40519080903100603021c3210200310030812071803201206011e050f240d0630031d03100f090b1b0d0c11010e010f06050411 55
    0x10350040c04010749090400b51110703c45041c9541e02449000d000848c03a09008007403005001c007100c1d0450921194200c47e01c0d84010040111011004500100124410b447e450826101444d4030010b480d40e80c1144141c400540d80044a0f07150008010560f4141c40c94a03411612040301d52200550140c5404817000e00d034010341881d40c20f600406400140004250100000c900911011448081d812211003a0021000247d041103016100c085400c02d290340b00c1c3c066100c00ca41c0b440501c9003080030450b40f030041e18070075400001102418000049800246d1800d4102141e10211000200292130700c0d00480340804da41c0090f000c0b41840034001c0100034044101d14104400806a0307401c43d0140c43c0d8174086503070303180070414019a00e018090030090080005a002104603071510040035000704030282911641180c9130240c3e4440c030300d101e60b1500984d181880228030368000d01540030300d0006207000307107082004070a80c41d04008001072281018130a007640082042c40803864440d0300c2001c01c801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 929021834 1250 929020584 929020639
    0x1b05030607180911070203121804020f04050111211b150103030f0215011728110f1017070f1706030c060304211403040b04051908090310060302 63
    0xe0008110308401a5000c0c40840b8142003003001a2752200c42c038107242803c1c00c0310b5690341030103140304010405503203242c1010b440c2142d80919200503800e41001c05241003035a01180d0301001a02001c020030451203032400f601214000f103243d50304901c0708500c000e50b22800301b00040d81041d800f030700500100e80304501c0c0250310034803401100d206000080c40580b851101360711112200c410400049c02d1a4010701a60000c2100c202400100b000507000350a07421012210080c43d0341d04480c41031038961038000fa2000c8481000304030301c4681450b40c00180001d550b4458440340801500b001900f000c1c0526038100d002c40050383d8000c0c00c24400d416641e411a8080c0816070326104a0303085441613950384004620030f074445d50b10881440e42004984603052810b889032400d10100c03202e400407144000c42a81c1c5d00c944c0080503208aa10b0307508081341001c0c003a000d511110191040c401043c80300b002d0003000c542105804480e0824401c103901b00c03c0f962030707010007075000900110030b181c82c4c45070101e03080c02c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 929023084 1250 929021834 929021861
    0x23070e0a031a1b1b0c040b060318120c0c01080106030e100f020c19050c0102030721090b0307030b01090503070f03031215030309031a040209071202071b050306071809 73
    0xa60140c582d90140c1d98000320004040c44d03400c4aa040562501031000011120b41600d00303014120035000000e500f4040205801106100d019145d50f8a0b0010800951441704003c1843c0e80c0300120080c50343c85240c1315240034081501c02e400000c40b54401d20403400840701e0035014001103200110080081c000c1c1c0c041c01c1001d941c0034440b19024000c148050803001c0d400c001d900440300a10315000d0b0a00b00b0342c00c821819500144582400700c2c08000392201d2840d0492040d01654070300000a4030400410303040440c2c3e40714088104010302d0f0b003545c050018000e090301c44941080d514410180c0d247c11038001c0c102241d10b2604100002401055900e01c1080510740110350a2650442c00d400e00719160b0003900010b10313a050400500100c1e40141040e05030000400c1c0c010b02d030035004034a1845c00a4048001c02070301c000c45107540c80d000d6046ea4131140d40704400c40c081321036a4582d06100c100902405100c2e01628020440b40d034010031714001c811644140c0f4040041c0b0b0052154010100a610000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 929024334 1250 929023084 929023111
    0x50d2616182d1a03041b080c100c060c031d03030915071e020715030216080a0207050a0806070305010501020d0912080c0124090b0307051323070e0a031a 67
    0x70314083c00c54000f031100341d141e6003098403850030f0300b040c050100340c5903010740e000b912404040c002e501f0046440c03d05040c040e80d40d4600540740582c02c81e40240c0314900a04028a400b9241744000d0f49a0030884081100ca510180708040000c2d026440b48000d03505550346a000005202288030701c002902d9104c007050a083c038400b00489606000e40881c1c0c3c100c40b00503004808140900e100311000824449400d03c2d00710f051584080750a0004d2090b51009041200b011401c510780c87d04c20048480640700140c154403169607900380701035a8100a8a4000c0032a042c2000810203510029180103c03003490750740c06400e1450241d003408041c1300c495040c1d5500c80d0400c01c00c008100240100314460341c155503407940001e4034001e07070460208035411040308a4240004a241d0382c0d000074800c002d5034002c5501c448080b9410510307500510500c119014141e450f21250032040d1018400184120599210b00181d408a8010401054071741c5c00000c01803650b21120001c00401e00303001e00d41c031905240313008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 929025584 1250 929024334 929024339
    0x6040204030507080f06070305130f050708191a04080706050c0d020a020a03030e0f071a0705010e0703110a050607030c03170108010b0307050d050d2616182d 69
    0x95081ca0f403160000c503142c3d8042c4400c2440c29400b041a076600030000e00c1d04010b0f0b42071003d9084c19000280714060102a510500c1d00140981808940b0042205004030390003285810f201000c4098410f00664104000090b000390f1f296085815a2040741c2c054000340c80c11882e552124024100a07256a800310300a021100c1c084e25544010609010941c00401d4880b065140090950b0101c011400b440d8001c0c4019003600d2500098000c1035a60180c1880c401c2d8003480184072a6004e144005821903003040700000c2a4100420403000352401a007042c90352041d11414007505e50413a100703032900110304100c0040071030b01c01c3c8114482d0b24424030340018071045400e411007400000b0f0304440d200b81d540e51a02c07461341ca0100082030003071a0076585182007804949441d44c1700c0620214001c24400010300051404d0b80340704900462020310b582038140d0381094507111075409114681c0d440410380707002418895010b206002d81c112201a01056206d0000984d50003107003c11000880140c80400d002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 929026834 1250 929025584 929025593
    0x2203020301090606050f0d200d020603040303020a021005010f0e0c0715060801180807030c05250f050303130603020f04050307090507021e06010326030f0601020c0a050906090604020403 81
    0x1d8041e0b5a010386008650300742000100711b030030030501072160312600400c5405400113118805400d00c2803506010542201c00ea00c1c007107100c4a8641d080250310500c00406c1008046c1c2544c05002c3c2c184480d421a02a030070807102d035004445081c000d81d5552640032034100200409117084c0341d80155254116420281c20f6605c031007900040401608400303480b82424010b118017441541025081d510b00398a00c0d1041d5280d001440c840e0321809403c0100100ca08410b00c40c0801030100b07685000107c04440c81241960200d105056001c0c05e070711309011000025443c074000064400b40d980b0800c8808405103044019070003540003180e10030902c2000c3c8000145590144640c2c4010018a2000702d10b41c60300700300c002e00b0a0411310010007140320b01d1485500d0b130440001c042d41903a5202c45403140640c1c0c940001017001c08071048143c28130030004100968646548141d502a1400380c0881712104040020000c4c000454003645401550510014443e0301e04501c081d908103030040c000501c1c064898a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 929028084 1250 929026834 929026841
    0x1060f092a050f032509090c0c020f100e0607030309020312360301020708042133090302160609060f120605060c0a170a120c17070917010506062203020301 68
    0x1710040f4220712000c005810307860145441d06640c514004403203c04590004d00f090500188882c01001007007903106040d8052140202c03091b6000b0041501d400b07003841c000b806441410000c90081c019014419a10010030040e80c0c20b10380c0c40300c90880e4a5640c80c4400907000e01c500c01184c6104099080062182c0b028401060318034052580e40741e0721030420506d4842c0804200c15030010000e21034a000c0440c0c9594501d8594400c0010300e004103564045010f49190f0660180c07956562904080c03008054000a250f0100700a54500d401001d580341d006482080241c813032030f004600e0840414407031920030006070217000304451300060b0542d00c5101080721030300090f1094221b42d201c0c2060300280300e02000c0090005241c015054504200c00c1c100030080022141348000c6c25480301c245c080442d004101802c8010240b120101491804000040040e0318910a52032001103540c00402150b01c18040c00d0710a500181c030040c038180f00c804502129a420055002102440e08070200051f5020300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 929029334 1250 929028084 929028151
    0xc060301090911030610030b041b09020903010b01020d08060d02030f10060614190c061b03021c02090d0230031b060601020a110301060f092a050f03 65
    0x5041455243c0032070142c49100503188244d001c141003000710071901112406403503000300980041d440d0380c5451210345080f006200c00f201180c55001c034149116034041d00d140c034003c0340248070101e0b1250040e61990101c1c1d5a100029007404002081c1d8203200320380100b0248007030219000740e4038000000d400e00b030400c480c0b80500390b02c2e800d042004030303070029030039540c0b410083c103039480c04c1e10510356002c0b4400c05000c0340c1c05200c1140091403c1c04074942c06280ca0160070f03846104c20604da2034008000f50f0141c1e5400e010f05201e15822240c14800f44242c0d9a0400c01400711003444d6040d4003041641050415010990340304518844003400c44441000c80c441c2c0c01000641d15194540d02112040e241818500c81c01d0340020100111030303a00060003240c00d84c00a40c0d90810034054000700c5d01403c407a1b00702c40c9901e1a801400100d6a819603c442c0c0d140d8411880380c401010a01c000e0042c10020350206030000d0401c0c0300f0015641c203400000c6070489224504202c480301c0102510b0100d0240e01d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 929030584 1250 929029334 929029349
    0x613210614090105091609200d1e020c2a03030c0706080105101b060621140307080406081e1603150609091121042913050c060301 57
    0x80038000000024010242c0004017640508540c025040071846001128821882d4098070f444080f045881003407108480da41d07034044019542c5088820060280c82e4a1141804942c201c18944646007682d1003034034020301814002d400c00e902600d40706429a207003a0b0180011288515587d800ca0353300300024115411000094007020f85800005450030105a200a01407180c4d13003801007103640e11003d50116007011004260b085045400d28800810007500070328120124915280b0b501030038002ca9210f9103100e2005031009560b00c64080c0d4407401034100003018000148028412036014105481c0d10407070f4245803da041c1115402c80703070320140a030348000d020703100180b031001140c1d8940115185c3d81d40c2c00344105001482c00b20001d0918502c1d1040ea081955284e4801c401c212146048070792404051120420000c4c14030360741c1a07040000d6400b01c40344176100c5e440c00b60b400480c001c0c641450014980300182551820b951103071002001c0422a42c44c06140c542e09416550500550301030400c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 929031834 1250 929030584 929030621
    0x27010e0901050c030c0409150302150d05180d0807030f05070f1805090621100c020d03090201050306012703030e010e0108010b310803090a0506132106 66
    0x24031002400c44102506281010104000300300c400180b035401c44d402c48502900010300c80d64400c0032010524960b0300000e510001039602c0980c0c0d00354020242c0800e00c0b10010070800c0381c4031921700510036503007021080c417603401003103c40d21014002c1c12440c1d0700921904001c07c102c6000612039044900854200e0086a040c2d606c854015a02c0701c680550b008a482030038040a05140000d00281c42c003c18491007500c01400914080004d514074401c0d000d05581258200d40202d0112009040c000c4d4045005210b14644074000503c680108844160180c403418610388607100110b80180424030890902182c480e401c08400030000341101c0114066514922100c403d140014100d204480740103041049034030042c80064050f0044403031101d0380b41c0200d04101186080d260b45c650480d2052184040300d100700162040c004801004001c0342180c104120544031020420140144500c1196800da018410700244c9002090480d041c240201100d2194500e59541001d0318151910341414400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 929033084 1250 929031834 929031841
    0xb030f03160b06180a1d0f010c0e060403081e040b0c1b030102071106070201020f1509010f140a0902030709060609050a0b040305060415061701090c050307050105040527010e 76
    0x10940b54109100301c030540005480f00d00d007070100c14806041e4803441da94640c030300100e500044211800d40701d071000580301c407900804c1c0c3d000d0013807160410b004082216003020380e01c289403000403581030b203a2200d003860408034031550f880d2034400b04024600151104100102c0d400000c0ca0141c41c1c00d448020060200d01038001c10401d041100a04036406a8014070201c2d00040800c240d00e5009030b01943c420341c9132046400100d10f45414500c4550440c01070400d030500d11002c51510a01c2814560020302c0022828580182142c501c00d020012480074040030501d42d00607600001801c0d8002002c8072189522500141c040319200c0e8804401b26440312004c00c13141c144401c40c03400410842c51024180380c507548449481d07440003003005102c0c500d00103401107141100e500103000307001d4020207010210203e040c2280200381c4a4400d49031000c3d80300002405150004295050340c1043c0e486504142ca002c06008030840d0b03045030a04e04100f4035510a014490205400d8024206d80305911024107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 929034334 1250 929033084 929033093
    0x3160905060f280504030818060406020303010608060603061819020a03060906090e0c01050c07030501093009060309030509030a1a0c0708040e04060921110c10030b030f0316 76
    0x120792040c0f45070881c454280012860b07401c00256412640c11402156550003103401c0e00300c28100384d1840d2680301e480414041403003540000618141e87c55511149119103850702040001d020031035100740d0045801440d40a070901910466800c403082007071607a52a00344c40c030008142e801040512002aa840c50200588272203030181c0001071090b6a020400742c2c030b000c2e44240e250b00024440704c2c1803020001300704504c800b00304003032001150884000c0040340490b18080a101c038003a040f02c8204170b0009400d0050000320308500d4000e040c6501c82403000d52812a098001c3e0411f10010b5007402014071071248503881c10f1044202140c13043c18840c80c0c0106181d00d60a5403136010b0b1042412110038030088001a03000300c100d806541800306040702581c0c03541350140c040c01500c00300034400c2d0000484502c1d44c4101002002d8558020b84a00d00c1c44400c10710b4060b500c1d40400c00c0b081d03000d1509035840c1031945c000d0f801400d194401a0603101a10350040b2003a28550004425804030813035a1058024070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 929035584 1250 929034334 929034367
    0x50c0118060e1e03030f04150606030911100c1b091121071b020a0819140f0a02090a0902191a18130f1d060f060603160905060f 56
    0x8292288030704190031010000c41d83d00d005c000c0c1b5180140d40c4100204003840760354101d00d604046910400d0048a464100017030282c0214281210b904814003400140c51038013644031034030b030181c0795240300481e883c03a240c2841d10407160794204503910348040003051000047c0508060020b0700210195030311200d0100c07031588510103205204409020301800b8505a1100d0710170140d250360b05030000c0aa21900000e207075a41981d12210240c491079040010341800400b82c100028028044584803e1509544507110984440d0220380c42d0000740c0940014030340183d034140c11041c071050000d020980384e8040b804c01d210112843d25141c0d11203108000c07002c4040700b1043c044040c1c061040c10b02075801d865070383c0f009400358103501ca0740000503501c084881c40d900c01407040c00084005c0c00701c00b4003080c1d0202ca6145405c0c806900340280400507905558444065002c2e22010b48500d1031981c0703646c000c801c003030105507101041180480c000a403503030311440038082c4452a030401a82d900504d45088100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 929036834 1250 929035584 929035603
    0xc030e13050105280611120301060e0102010c2f0f031210150c0605043e0307120b13060c05032403031c090206070605160c050a03050c0118060e 63
    0x1542605903801081081303d944070088800d94203050000e5480700c030855041002d000d000f0b1003c01c501100001d4556440303450100084800c0c0c00030010200a00821114800c0c81401d8901c0d02080c41c2c10041030303070507150400301449080416252049120003e090856000540b03407000d10390048107100c010804a0340d40c0004000c2000c1c2c040c0030600c02d9001410160b99050b0181001e40d84200080501c4080c44111011079a502d5038509003040892410386951203440c5c07040e01003c0803000f011074030700340025031000380c03aa460040f1420205d15520740b5140300780208070202d510680074400c0300040c1c880c040da010f212141e44501c0c0c6c4030300c0d01b428480b0807944010b40500203022094162a002d440103c216008211316900401170200354003194009460100780c025040301c80043e405c001d000c01030b0f0001d40140712445040c80c126003504c1003211440380420010b40075401030907415000a0189005000142c9910000f25020502d0700d450301280880d072000307803003c07600d41c1285e03103c401052156488 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 929038084 1250 929036834 929036869
    0x221090a060806090f09060a0209040e010908040f080c0f061e130e1320010306050310021905041a07030c0204050a09050d0201020a021b0a030203060a0b090a020a0806010c030e13050105 81
    0x10a891b000c0e100940d110009411810540d074001554500c9444642101c08242c4201000740200020f91070220026400b40c492501d5000211502003040b080110781c01c20003420040c600700b50001414104101c55122106040740c042100c000c0c03502c1001003c001e0702c00c1a9110a080c3c030b2280c60700ba00b0b03058500008102805051000314664009641541001102506c08030055201106140107030000c0900e508015810b01c1010300202c48410540c00401d850048455242c0c0b400703040341c009955034040c5001d01c030011003003e41c54418801c4860081c142c014040d02c4d00c0380404d21690003060403920b00740c0364000f056884110440600204000d407841180c0e06200031898002c8400d0001d4441c2014a45000c809094041b140c40640c0d0700c040e400c3c0a1078004080c0c900b24108000030710002d00010406e1402142800c00103a11416680300351030030803940361105481940c031403004407150312081600305d060004030605a800c1e511003000414081010000000306541804104890402004001003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 929039334 1250 929038084 929038111
    0xc0e01090b07060509070911190306060f08070201060b0a02031e041d0603010912051909150f0201060f090e010614030a080304112d030106060221090a06080609 70
    0xa55000380040326900354010b600000c65807140c0d86210304004040c1e001482580c2084040801040f0000082c0b0300718403107540f04c09c060000340d2000c0d01940c04038031801011601042c0c00f00d5104d801004203039131003580c42c40002510703500c0c1e00e6506055089060340400580c07020800040200c0c4030384004a240d20300c3d440c00303420300c0e280090030310900359404907441844042c03e001c00c190f601c0940081942c2c590103001d901c4000140b0000402c3d0fa004560004041c5c14404040c03c40320740115000b409465440304a468802075aa005403044015410200f0842d0358481e0001010101d01c0c4150014010345031003c00c802d281702d004203081d9076007500003003400351a20450f0125941c0000700000317015844a00c058480ea540d04103119168090541a90030461000060b41d5500c02105550f140b65480b01d101c0b08a01005070900d82201d00c98021000903910040c02c05082c0b200c410004e0f4826071900240b1440e1a0280e004203242c5040390b48000c0100c0c244e003044c003071a8501555030a50000c41e08a861 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 929040584 1250 929039334 929039339
    0x309030209070e090a0e0601060e01093c030807030c05160303020d030b032a01051204051014070f140408030d0f110a02100b0109030b040309151112090d0b0a0c0e0109 73
    0x20307481f0201807064a05022600312462303a02d900604000b0000c104144d41209098007040d405400b03041080700700360400d01c001102100000343c3e184500103880e08189004d04046143d602550400050902600c440c421500d203645003450f01e00c22000074610030b0b13000e85480f402800c000382c1035802e582c66043c401d4101160100f0b0003d4180000681000c0d05501028030200f0040140d84134400e0a0036520540303035000410080c0600001c440c0c0c0c1c60780e1005c40c1084264540c001081511070141d4020002030850402461247d10031341d11a810b40040c400801c1c50282d841e1151740c51644070310300000d0f80540301d07610f40b8102c2189101d1040d00000008140d881e082c2c1c9030300c00a48850a103d03070900e00c19527600c440441d9034490100385010f16403190b145800c038105820090281d0314144a89083c0b607003500e040c0d0000c80d20038050b04078060306160052228907180c20f40f5400b036401c14450290003440a9410703402082c0040101c50003046084000107055004000044c04054580d61440c10701c040400c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 929041834 1250 929040584 929040611
    0x5010b0a060c02090f07140309161401050d11090d150c090506030106030c120c0305040b010b090d14030c0115030311010501140f01120e0c09090105010803160309030209070e090a 78
    0x1045c2d070060030342e0200d4100340d03540c1d48141c2d8040d540d040d0600907188084100640c00600140781511451521400c02c40c2d82d07510180f41c6407030340c07140c01038078001103090000303c040c04480d4000d241d60700c84c41d030101400c004170031010507840c3c12442c400791642a881d07140100e6410707003031040b00003d039402d192598a050600307000c03075013901c0107200300d204056464049140180c0b00740521104000601004d01128450f00c00c020003410068506445502c200000080c0c0c0740725907000c446400602420301e400015241c0c030780c034030b19480f9490130b10441e0104011142c1503880038850301c0400c2d110411450092400c0d410300400403e070b8030843c00b285038034002c018401c6128540740b440980c441140c000b21070722801c600407a5900c80000780d111314035040510004d00b1100208080c24912400e84031130225a681c9400e050030780d0f00030b11841c6400e4008110b04041201041c00900400c5d009041c100780d0b45583e5400b04040020881da52800540c3c00090f1843e98648208402c1d045030100d241440310000c030310074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 929043084 1250 929041834 929041849
    0xe010507030c062d0b030307260313211409031204030b010617071205060f041104151b030c02011e200f06012c2d040510052205010b0a060c02 62
    0x1005072400200c0f50441040029501014009d904540750f40c541700e0a240304180300c90001c00104480304030280364585010b2520201c11090400729544005090031850008082d60f40041d141903018091140424558074a4100502c0290702c242107103026036141c84030040c140149140441100005081403040040d48001c00c0090000d2010002450741c0340d000000764201040c08500303420505025008103017010071009403045403507a00c0560340c01019420700b01c48000054885510b0003c1101d06a400b1901c00c40c08030705103c3c810b05101c3c40c400141000c4140310800401da00340010100c2d1a101e080303804840400003444440401041140140e01c1e0035030b241c100501610003501d040c240ba040f8401c81d0705442c00256142e0611030f0085003001c0f00c451010380c01c50240c2a00700c1c2c00420000d0214020428245d114903004001f0700382d6052540e80f200701400c0007804803426903007581540407000c007c1c00c1a1456140c4954000210314052a050152803200d5030301080c14440c1c400442c8016865006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 929044334 1250 929043084 929043097
    0x102061306020a091d0402010917070b090d080f04090b01080411040f15030501060e090d1202030408071a1f0b07060209041512150501060e010507030c062d0b0303 71
    0x400980ca03040f83d600112001d02a9910441400c10f64038044c04040345c070752582c0d5005038000e07601e202040d500e40c000c182c1201c00031403240d4240c0c2d0144000300005001e52001d0505814010000e5107802a25240c100054202038050201460000307420049102c491140c858102c0b000e08054032580350540b14004040311009000f80650b49511550000d41c0859002d0f0580e0035103c0030036285181c0fa4206640201004d014000e00300c1501004200b241c100010000401c40041d60351490200c040410700e0044c0d00003400881e1a1301051194100061140742c504030841d001104241c070510304800040c2103100014101c0844407540e2006011074002d0f4421124101d4000340302581d1480c410011900030282085551a50f120b041400b02c2c001c50581c00b0280018000d040d4000405040e1240c101251001e02c150000314600480c07110b0b01d54003410203811040e0090038105292a450303120340c0191070400c0481c038030360040c11468441004a00f5520590aa46003400304040301c80074010075030b42d1084c01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 929045584 1250 929044334 929044343
    0xa08070b0d2d0c1809020d2004060f05072019030203030a1803150b130209010e01110a0b010b2115090c041a1c05090a1b080303012301020613 62
    0x41558003900f5004020000044508080d01049699140d181000940010080d9061941048041103020030320440048149020020711841c1928140e000d4800501d125030341c006100060040030041b41c11000200c4c0f105185400240341d401800040007107520004c0c50240c8004003082c410300c007585000080e6018010a41010441e00381c40207084840f58459520050500d4900801e203580703c10150480c8180881c256a80901b512492031620300360b014150000b4001140c14690600c0d0358420801410750307a0046064405040310f45d110341c14031242c260801c203c4040000f40e010824214004125480b0000680c80d582d142804200b0036140280000441d206004200205007419828002c607002441c144003082c42001c0400c00383e85160700061092400040040340050200e00d01307005017841241550007424084c0d00540e640100401c00e041101c014003c800e43c040b0b101141040254060450204403500c1e041408502c10200304d0b20503d142d046412030424401c14010303401c55603070342c141d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 929046834 1250 929045584 929045591
    0x1103071205070c0f050705032b0e1824030d1709031204050c130908091216060903300507020d02040204030b0f0a020c19020a08070b0d2d 60
    0x782c1c04100d502000c0803402602c000180200715080010000d031142c01c440081d0143c1d159003d0411030400da404090905a2002c1c1804410f850130921440c8113002010008144100c410000801c990b1040f5086940711000c0c081c280d031305080c4094526a1100c0e101d07040b0300a200b044090740d0b008220004d11000c00c000c1d5031503900032a520060030300984130101c4603291004120b117440e051155450b801e070309485006103101c1c0800d0028009030700902951540102e40580b07013403161400d001902d481003414101e10f01480b080d050f440304403864107800829550b59104584c9007075052050b40d50080841032340c896541c540364030090502d04090714601d10541e080c49511224240041202e9501c0607100940c00b900c009408010012185003080c05a444e031041c84015070380b0b10414000700d110360644040681d00203021050220542c9858903061031000d448028010356403a1214588007140d044552441e0012a0220041410f4420b1150030001000f550141da0200402203200b2502150f8401c0071684 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 929048084 1250 929046834 929046841
    0x801020c072903040309140301020f18041b030c030e03090d0305070f12050c0c09060102070902091c030e030d08061f17100920090603060d1b06031103071205 69
    0x80068800019000c1c8100300e542c84c40c0c94680108000384a0058090301c801031039000e409070a051094904100301c9041591400d00e0800e01c07100d200018080850303120b903e0300d0300141e112031078085104c202180c0d84c07130101c0c050103041c0002d030a8400c60035184140b42e00034130001d180c41d070b580b03400c0c285650703090709150303507540981d013013030280842100d002802d00e00d46100c001080d940c1c01802000d0aa880c030701911004810f0604000300d040c0c0c140c039150700503803102405000c5107140c1d078010325500700d00a001902040000d642003008071100302d026804140c62403409809414140480c1044624915012019240130310010f0300050210341000644210124004e5a15000d960501d2190b80303015071440749440c000c00850a1003170280610340f12141051000d20034020140040000449481c000301d04022804091000d280c0008050643c4840743d480c0d1700012680c0c410f550940b18103004507501c4c40d00d0624001a00781c41c0c0c06d04400b50889000c0080100703a44d803245240c00ba4100c1044003099545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 929049334 1250 929048084 929048129
    0x1903020115091116051c0c031b05060c09060904050408220305030412060209030f0d1211070204020a030603171e0702060a0e01111009050d020106030f0f0501090f06150801020c07 78
    0x441040c80152681076103000c8815403900b0030307100007e5510a603030700d903403210184000c1250000c1c508802072143c0c1c820000310300c1c0092508094a000200940054201181c4800050940d40265000d0f141601d0004000c124100b80004201a040080501c02090380c510b9480c00e980e0301c20340c850750000215500c2d40c00704000090701100c0340c4660090481cae0ba0b081100c00000c5c3c070344415510a50100300001000302c1c0291130b5008640340a6008100107003400e0b0300b0340a001c060351103000f5090403d03540d4140030002450280c0120120b5846903021503c0340c3c5151032400100700ba0303000180e944442842400010782d10a0215410a94181340000d500b50340240141d42e11321a4100c0a0108d025072400000c02d115940e00c903105150107030044031041c00901c01d0507401c803041400701505c05986000c0a034007056406001034040341c8600c00004191a4030b88558801c014001001c80e203d6413100400d204151310500a0006407040000840c07a02d6000e01c0096a120032078802d114102d00d10136000d00800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 929050584 1250 929049334 929049343
    0x2030f1303081609051003050a0b091b090d120503011d010b07150b04020301060e0a1a19120603060e060a05070815030c04050f010302030d090323190302011509111605 73
    0x103140280144040f50724a20000d00a0f00d02119409c45a80c5051a1038076545400300410340241300440401d040769100d1000c3c1006079110080c9a07400c1603601c0b200c400042e0500d503040f003001403151398031501c03941480100101050b26203000645030f02c50400601c000d810000859600640c407501c0b524038002c7e01d04400007e800d160402d95400b40c0b0203c00080c1c031607080401c0107803054003114121215501c800f000c100f100860030780350240e601c0a02c4140c0c08906c54000340711807483c3d1824861405803000703c4040941d002c50f00202c401c5030319001509da21001c100300340b58110840510502043c5082e880c010b24606004045415541280913130349440c4c0c074148884450801d02420034030003031424154000190000307102c02c174020310035084104101071091040c2003d980d48003007540340c48030202101400d00081030001862500030956400580451403005045941c8a500082240c074088005006594003503484100d030035040026200c01c420b0404101c422084540c8844626410b4a042c0503281 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 929051834 1250 929050584 929050589
    0x121e12080a180b2e0e09030c300c0a03030b06130905060f01050309060a150b030703150b0a090e0405070b04121205070b06090c160602030f1303081609 66
    0x500e845140700106004a81c0c2d1000c3c854181402d00c510b8604c1d02d60383d07419000c1201c20300c0507030081c041c00c0706021126000400a4028501074112420304900150460901c440c1c501c40c041d1006c3c0010a005800401740c00e484000c8010f1040c850402d1089006541c98446012009041683c1e07040559140d54401090301d686002900c00d4046081c0c68818500c0200000d461440c451003404096000c10b41c8140c040300c1c0701d10031000150406498400d02d000240c4a0100e9445421550303a0001c0307076592080000c2d41c0704854030313a00820502e01c030001c84100d5040c3c5806c450072002e0304200a940742504000050b080b80c082c03070540c6d151959142015828102c3d542c00c100342000d40020f0005481e9076130b000310b00e045030140070b4580c0c074010320140c02d58043c0309000004140c440d000c40002c0f1a0719044402e160300241400c4880d14105482501401c40000710408440f02d5901005100c000728995100740d500828240360301e06014405d4034050140720009006030301d00e0f28004404a185481609207000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 929053084 1250 929051834 929051861
    0x4060807060203041805040309120501140a0915110418060b040305030406090501021f180602030c0a18030302060c030714071505071e0e03010213121e12080a 69
    0x10054071020001e4496000b40b01d91043e000c440141e64400c0740443c0700d07850190ba4540c81b440001458001c1829007800402000d951075581d030000c1c081511402007070b4034860382e00c401c00001d52540d289024030500098003a80c26010345810134100100c0300700c1c07080383c0035119a00b507480c004080d01100381028100c07035041003c28500110b000030130844000060000d0754415210020500c1d140c0004a9440c20f4403031829801c104018100030022005a000342e1455501d0040007954030310546840c016070740f0070749030503080260004407400c41e540d001001c0c414850407081851649461070710001d40e00c080141c58012103480c00400b05044a01400c00800c241c5403003046c042d2200c90354200402400d0b906108500a00c2c2841c00003003441c6e11411001050390290030600320304907006e00003124200c07659103a10b03405641c204020700204040311903c5004041c1100c0c00b204a09103840c2236070440e1248115402c00f648080402800180b00e1284030b01007400f689040b2030280d0f10300d00090f0148c0132500c404403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 929054334 1250 929053084 929053093
    0x13050d0c020d02040c0c0c23131b08090d03050c0306091806011508070219060b0301090c0f0f061409010810230a05010f080402040c03110c0703120e1e040608 69
    0x4401741c3e0410036481a540c00f41c0104880f06545a41450a4000301d9020b02c89040a81d1800c03040e61030901220101d503a06c2560000d1200800000c3d0360142e0400504100850941d100f00442c03250108500d00f29000300c2e00c0c0910640c00c1c020072018403400050300c0584a80e21901c00a9020000e101d11000c0e0075006a04803011565140e09189800300c0102483e8009441c040002d441d0741e0001511102c10b400094030b24040e0012a01c544000f0014281000c2d4035548840085010407020b0f000b1001a22010350380d00c1c40d0b0343c82e0a51100c0b2a020a0b0310020900c0381e40701c115140c040c1c0300d50694440d201d0a003406417840d5558200b030504844150400d0206c80c0c2480c145520031500e219044102460176528a035405849074010346d211101494100009a2140002070044c205500003149041c401e04021690115101110102c0d4004130380300011a0321122003042408005048500358003140d0400e200071448075404144405100c0c80d82d407255240d90083c20742c03643c981358843c0f0700510450083e903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 929055584 1250 929054334 929054351
    0x3111801090c0305060a0e190f290108250306090207060c1d0a060516081902070e040807020904051015180e0d0f05090910060813050d0c020d0204 64
    0x8000500c0410b200c440040c2c0342400041041c200140c80700203030b603010a12103c031036076400c0442101c5020070002084880d210087c04030750008502620780e41c864807040f02d100c00740107104180114800309207039504000c58681030009034a92003070341000b85a03845661031030f0b84070303220000d902601560384004001c81c0300182400600203154800c1160100b940c1d2030800955551400c1c43e40800f881c0f82c003c0c0d2000e64200d081041034000c1004006410b03020520650480c42e64490201940001c0c034000510381c40035118400403035045c00f01c2c00140070045091006820192106002c1d0b000d1104024019403c1c6c1003c1020b0090810880c41031411562040c4222401903051082d541540d101d00f544120b0034150100a00d2000c1c01656080204070000302441c14022400f1250281100b1021050003400c00c86c1041c16110740003420700c90303429585c0f400491840c158004081030401846549114000e10f00074001603004690076011002c58a008440215180006148410307400d00c0258001d16107402d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 929056834 1250 929055584 929055599
    0x14071d090a060302090f0f06010c1b06020f07080f1c0216080f0f191e060e061605131e081609110304170d020f0c07091b05030103111801 60
    0x404160707482070b180a5000c0e140c4840000b91b00c02c040d5981c040300740f40b0000003001940305005c21a0114000e81307003500d078890048004040490f0581013200103800002604000071000c010240040c41d008004048504124011036100e100d92013101d0148562800303200b09c8280b00708200700c0002c9445441c80142d56648403425565543c1d01007030301c464010400340400142020941c1d07108101c11120141c0c10b614280c1e940e8811580d00c03803000352901199213418001c18241d119180f01c2036410700c000c00650500c035461a84c0303284600082010403104000000c140051880110704540c1804800440c0c0f2028442041321401e00d50000546481011009205004155100c100f120b5a01e0340c200943c0012030034a101e1880200c80180401113030f8403680201507240c0000b0914550030003001420003410403292680c6500001070b0445540c00000c044c000c4001354461f02c152a26068080204c0032090b040180c201c1c0014403018200082c92050700e521070310b8400304810ba50140006401039503849425 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 929058084 1250 929056834 929056841
    0x270c1e3c0d0605130c0912030806090c19050304020103150b0a030c0203040b0c011505041515120c020d0e0603010620160b0a08060f1e0415080304170114071d090a 71
    0x1001c0c000500001b40002d10400354415401c06c0c50305a038960280e66150018000c0c2040d0180c5081444001001010103080e1950024054202250340711030b524105400010182c0d10410220300c4400c0000e03030304003c0741c020b40c0219400301007141004584481103203010707420b6000e168441072000d900016000c43d041011b5002882c0b403c1d550003038210b500c3c0c483d0280070807550440c2100001038000070041c4046481d494001e0118030313144c40c10094004102c1c405406446182c044000075034009140300450540000d0100c050600c15504039086624298000301500b90f903091a10000d148000c040120b0340c8284428111008000c521107015584e40300c44a1080d48110b030321000081c0f44c1d00215110b03152045511040030300040603608022014000b03816007207510a9070302d0f845940d03485800c0782c4900d030250180050003050051a01c403803500040c40715040c624011940c82d6490044d00f0b403500c0c07444c18101c940108051522899106104074412800c0a04001c80c1c0d600060210400005203402d80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 929059334 1250 929058084 929058101
    0x340c08030406170c27061204030201050a05070f030c0c05011401080607090b040510031503030509131b08060a0b04090504060b270c1e3c0d060513 64
    0xa68000d41caa4816400f60030014040d10b0903442c42e20100b19a0403000d00d0124242041441c4001d00300c0070110580c0004d1003540825010403000902c0c800300710515130280304550740b200300c510043c030403442c010a004024081c110340b84024141e444c0807211445126151002d850380e4814000c000796003428001c1840d42c0c10922030504903105544c00540000e01c02d0403a07a0845030044086401d003800c003420070500f0008103005208243d0b0300c1c10311240a045100e841c81c0114025103402d5580d842060034480e41d10041900064140d08101e0320525558109900c8540c0318041d141410a54407000002801e03040c20340c1c441c2500100210f00881c1a004c5584928000c4e07120f541d0400444651a0030302003004c1d6031400040a0914011240340607030a0054115801014404440d19010942124885450040000d030608110101d071400c20a00e407182d4000c03103134250000c04805560039000441c1d40c034000180c42d5190020101d1011031103030346500542c01400c00244000320b80c64101c9001c200401100c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 929060584 1250 929059334 929059337
    0x40f02071a0f100b0307050a0509040f0b0306150315090118050105062d1905031b120102091302220825050307170703230d05340c08030406 61
    0xb020a40701c8904540c24012100c50b83d641ca4103594075108103649036004190a0000d01c10b040180d010756a44912402ca04081440e80001e08032000c4801d00d031800340014800c101e001050001c81540340d400007088801d0a031121402212030756610310f00f50140000d42000c0c8800204007908404011042d040035104203000d890300840c440005200d1000042d50312015204043c0b500c20b51060782c10002130600c540724422114408155075100404d103803900750f108211000210004034415442c080c000c41c050813052a00035418104a6000640c0d025111800c200c3c289a00160008022403036030454a4804101064034814950300e60002c1d031071300c94680e03210304034034010081203c41142c034104c000145c03a0054000c0107607500300f0402d600c50b0f4031804000707141807203042c1000000840f06100154001000b070b41c0a94440300c40c0c142e2915150080342d1000500030b040c8130b159062030700c40b000740541e2500e240060322150402a941d0b010075110180240900d00d010001041840d8004000c0040b26460f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 929061834 1250 929060584 929060611
    0x15030103061103060d060e0f1002090108010b1207120902130906050a060f060e060d0c090503070e0106020a06110d0614010e010305040b010306110f07061e150302040f02071a 76
    0x261001d82c428441124603581c442008111103011806580c007090508039030700300f207403041c805c0191001c4c0f41441627048901e4075900013420170034079648400b800e40142000802d0f0f42c14082ca00100d1500548014501801c06c010000c0108180c5800c0e00155030964010b416541c0701c4451060100c003510180b90181d88075401c010108220211034841c15003117900a0a00350072040c1130000c210390340701185c907241d42c0c460024040041301281701d00c104185a251621070080e42403500045c10b0404804d548040303880f02c0d1440040002c02e80201e51780800c4d5030700c90310005501e441100025242d0090041c0702c41c40d54a4020007181e000c1e07020400c83c0c00c102c1c00b62600316000540900444c1695401c950051040141d1001000002c0f0b0640051000181c40c01150341448021a0741c1e5955400c02c02081e1074160326442c82448105511944102066100d00244845015803900803007028040c072000740103907030b01e000100003090f403541643e416951040500000c2424905005020380d020340305070001401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 929063084 1250 929061834 929061851
    0x180f050c09010b091f030f051302090106050705030f1b1f060b27030124060921140f070f050405010b030108100209030705060307021b04020a0e0d111503010306 70
    0xa482138444115005080b00000811482407680c5980078492501c181502d42c04003004000460140302d10960002c00a446003100d80d00404c0b1035008180e010500348041044120b011410100c00ca400950401a00907940c1e00440d007105044c1442c0d0298903424024100c070f1040380ca45040c1d01038100075406c801400000e031078810030500c601c2051400e600403c51f000750311910900d541000900f0100c028000240d00f42000c82c3d00d00303825005082000715031200c0805104e126080000c2402900c0c0d0040007103800f4212003224894010f0842d0050118511903034980f180303003410400a42d0003071005003501c8045642d010000341d0100d0500404d485242450004502c1d6401a01079904131740d030410042c91260440c1155030700945c0b00322005605030164090100d49a00c5860045020703400550082141049810695a681c2030420250388218010018002010b03413150581c101c01100300c6500341690707014508454010105465203800168101c142020508001c02a5040303c0c01341c5801d005404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 929064334 1250 929063084 929063099
    0x70807030c02030a03111905070302160614030402310605090c0915090612160c02010203040626090f0f0a080706020a0e0d1217011503180f050c0901 65
    0x8201d00341c6480140e000344940c44501d0f1007600700070200c0b030501d480c192506042c5980c0360034400b00d03404480003280f00051100209981009691084050b01030f44800050400364000d0001809210302d810107a404008501550ba4400c16948010f1300d240c2000581000d000c00000a44101c55601e01d40e146001400103171800c014007214461116909001c0c41e100a1108001c03074501c001d030030391100c00b0040c040f64860b602c0e5403001f404651200070030b00c442480d180060640c65030081c4032560401c04807200d4400140d8001040c0c40070788103103040414810081490042c03080606030703041103949440d031061102042c00804c040c4071000c040c006580744001000c941541d00c10807108014000b010400c4020003090255001e0500040c2500d040605210a40001601c00d000d0440c1640d402002c81481c2d00003070740007140981714800170340001080d5032506882c020300a105030300c100b0070325071154524145003850710350481769503a00100300400300065081661365400e11019290180b40424008144003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 929065584 1250 929064334 929064341
    0x10807120b06090915040609020405010b0910051809010f03140d0918090203100f0501050a05130b010212070b0109061215111c14130206030703050c0d020309030307080703 75
    0x100d40001c004401a1030b00010300030390800040464990380550402005409100810070340214024100490108444d0042104070340b010790200386031030303010000e90100d5116010540000da6140c01c0483d203400a81c2410001e82900c00348a03a0322483c1840003041c001c5805070494240c0e0702540c0c41225149074401a95500c00801600c1c0c1c011400c000d070304110844021111030250844230f4000708525485034042480d10011380c4007140c070707580c51b031180c510503000901c00c45004080444a00010760b140030007046580c0c8a039442d00e4a03540e214520710307090764003c1107030cc40a0360649403180d03514201400e0502c03c0c51000c2c05081c00c5141030000000d00c11042c3c86400140d203030007001c00b50441030440c0c0c0c050002c0001a0303400c021407500b0312415001c818406c07482210280c2c031003400310701c8207071a100e10020108010030100c51984241c19020142e102c40382a01d0340718415050000f07040d00d41c0b420702d2056010308196131440c00e00003c01c1280a81000c0040e5014030310070f484849640e11100c10076402d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 929066834 1250 929065584 929065619
    0x80f150c0307020a060e1b0108060f01110127140105010302060a110705060c0d03050603060106050910030204050409120e0d0b0a020a120204031101180f03030804030203120f010807 79
    0x2842000325080100510003140c0006181c012078103036070400d50318a01601e60780110420150007005480840348103d07545090b0808003464070313002c0d51a212000a040350380301081641009203d80f58a02035140950040c200b000c9004980c0d08203e00c10800c040c0040c0070b00904541040075619070203e0290305003d4503058070380c001e000c1418074500e1b0784100c800c812804490305007841001c40028990302e4407001048003550140c003400340003c0d040e2015060f120041c1c0103e0080c1d000c1c4004100240d404026141700500807115100c1010030100110042e02031600003071b5000c2e1400502c3e400300240280c46800d10071094560102482c42c1c103041040c20b1030340000c013610800740200003610f01c2540364018660b00080c0c0c104080c40e41d0050316203000300d0300980c00454043c00c0c6c03094440101d60b0800c400048800d49504c90f009070f142402124800910a03100060601034a000410200b50080c425144200c0902285520f9032900c1684584444428460035116020b03010b404248810092260580c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 929068084 1250 929066834 929066863
    0x70e010b041a1305060d0f050106020303012d05101403010626040506070f090816031106030c1e07060203041124040311032a13090222020c03070309080f 67
    0x3400d42c13401060101c1d5030300c200700c0c0d00516a41c1d2400841c1560142c03085601800709a0f0065480c0d6041040e113100040100721655128540101c200d00c10107103c02120003641c0c07042d0740091018640d0340c8159007020040e45400d40d040300c08030000c40ea170f6a210148030302000c0c0c2a076801f850844c03290000d000d03c070130966000d041da810000004030018082c4201817400d40d15445c04244a5903115102810a022400010154203510001b001031114100c2d8001814070202c941500d1400c0101ca40d480c60b1003070703049100500200c01c0b8041c0200d17901c4c80c00c1d034140da90400c0c0305640c1c0e841d0901c0e140401c3c0c41d28202e5203118201401c5202d002d05002904000c8803003c0e90509850603003142c43d54201c03044c00c1d080c940d501d8410720b02c41455451406004654810b009a40700d01d8800d5007608000c070004c00c008620450302c0c90704035102d000d42e860044901c02100100d6240c81c0c1c0116144010020f40314904e001583c911001a03401d04040e4010003607001c940039482035034024146001390b1502c550411030400c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 929069334 1250 929068084 929068117
    0x9140603040b10051e0f030d0f1d090c09040e06060a17010b031f06240503250e0301060b120c0d0905340305061305070e010b041a 57
    0x2030000707070202e440903089030b40081d80c0340714941d0382d1000034071a21030088008200004980001407a04000708008024002280640641501190000c11858583c0348003410002281103001100056091a101d258006400580076280c078840c11107039a03001481c000e01691600311200c1d520200410414090007004000016031132920001980780400f00c481050203559480070300c0001e0f5001c0000c1c0a002c800c0e4150442200300503a40700045075025031242c260b407a81858104038201860030420821242c0f4100705840380c450740e50410100440340c040c40300044000c906144081e40040d481079481c1d104800901605445150340d600c903006488c0f44c806c8002001e00403640400c2000003500301e101c2c0b0180001040341c00741d00c8207450320b1452802c0c000c01e214074583c04503040d690000214000c4001007414030741240b6541d1065a1041c00a02c4c4000c83c4016040c5c00080150038024a0024602c0088542c0c05507124001d1f40e0b9039500512a207030000d0011040041115800810703922026a445207a8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 929070584 1250 929069334 929069341
    0x60509030f0d02190606050603040f1203050c030a1a0a0b030a0e01091203020a02160f0302040c03020306091b04031406010906150203030f10050402070605010603050a09021f030212090d09140603 85
    0x440110030303c00c80c00c070341c00c46e12100082040c3e201c8401035441140a05c0018240301202e080681110807040303010f900300350500007041000110b40ac202c0713412a003c1e903800620500f2041070942c2d0154030300d09030bd500c99648540042c00410640107580900c00740e58080000e0302101042c142211000007004180d04003a03056038140500940c05005819050700603280241d61080c00c0d0082c0c00d0107a0850071200101c0002030007503080510030848004502c2c2003c5141d4203104000440081c002408182e5644040600f030200c00c0e00101a2402150302c0341002e03540d5002441c0c110344841e424050740a80d58500880040c3c060403051301c1c01e10b14015500590700e0b41d107403404070b0019104000d008000b009040070001a440c0c403184002c101e06401030000081c15410810000d0503120007070039203400c1ca070410114101583d51030301c0121204901d0011070540f11030035103080e0041d015003008100b21105a40400030380e106d0125844180070059510312405940790700111004c500e544070415001541807001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 929071834 1250 929070584 929070613
    0x5060a11060603010e073012080f06180c0d0905060412090b1e28020d08010b0a031a040c11101b030b0a0321090807030f0f0c0f060509030f0d02 63
    0x102c0044d00445141c040c0908004043d104061b001d0394000c880c000048d188800c4402d42c4690030b95040307881710140b00440d06008001616000004514030024180640480c60313102013201116003107540c44206000e4074805003012501c54004a400783c0b80c500b01ea00316108810700c2858044140e030640c1c04498240b16418090342c0c4800940900a0785891003000403a420100c001d5095400c40036003501501d441903400402424540d10800b10800d00c0744401c0103000c00300c162070503140300803114680080d03100303021100b5a00250307650002c1ca030040d2900006201031680800c01c42c20404281e8100c4030621520101d0380b04946401c1501000103640ea214060014031903040604110b80c0206031444180c0c0725210400d8500380107500314048a4928030702d607216500007180710010110340c1c000e800350900d16150f106d105012040000c0c20030344810203080401a40301d540760041c100e40301c464803846844a1002d0860b0380702e607509511910500c07044120855001401510000c1c00307501502c0c0000e0940c0c030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 929073084 1250 929071834 929071859
    0x603191b260103120516020d0c0305010c0905060a2307060912020303090706080730060f0b0a051b03030f0403201506060f030903031f0608040305030a020405060a11060603010e07 78
    0x2d00e03060f6a0074404030580542d988e003900300c1001c0d00410107110024554640142100c42d82c610580034441c10050811442c1e49400030707a03800140a045c4100b552000d80c0b200f98804142010315520703c1e1010503440140300182d40201c0c0381501c120880c80655808460985c1c1d02d000440d400442540009024041188552080d0713401c0714580c01c001c8098160141e4a01c801010a40382d10003c8062584901c10300c01c07a800f5510040c842c5400c4000c1d19400d00e10a800b0602c83c0c4030020090090001c4e40701c10b81525001c0400118501e1010740780c41c5d09040982c442c44030f10558042d00007440d045c0311150a04203100c00751703034000350110080055441c0300c88880c5540e07000804459102100b03002d0a04103012070001184958420f50180d683d074501946107072038201d04c2c1484180003035058241803140d00e4000302070f0ba401940504046440e0740d50421010064452500155009580400c100303035102c0e000342d141d130f111040e0103050380d400b070740d513442894221080c40300b002c52103510801080001e800101ca = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 929074334 1250 929073084 929073097
    0x22d1201140d0b0414061605030a0c0e060a18050603150d060e0f0a1209031502030402030c040e060f1f090b0a0906081e0c0603191b2601031205 63
    0x70032405180b106030301c42915000c001c66060f224224005d14804909a040c402e05074044009941010800e890040052044c003000784821081c0d40e450b01003044841c003840841c006036200402c11907480010a0005080c069004401102140703261004507041c0b80420580c1d10400800024510b0710780c40354108505c4040340b203015503009540d140141c50b551001d10040400725150002080000040e1425500c032021100e00a030401c00d84038000d000240c842c034011503901a8403072000d40c40740c855000003410003a840d203125601a03d06550302d020103001041c01c0307105040c0701c2c0c1c0d04025640c40b0030441409a61340143d507812285814824012642542e20919419074080e00b4041c0454850340030b20112001034120030056441551502101143c00c4040c5c5400000c200145c00590b2059000c6003040c00701401680d62018900d61204030b00c9143c0c4c0c81040000c10f500e00301350004112620140c240d20540c80242c54403800c030100c000858800d0306070941200e40c8444803d81c0b4540e10402190740d9003220 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 929075584 1250 929074334 929074339
    0xa09021f090b0f0a02240403180509040c05010f1d131d01050103120e030c0906040f060e0601020c0f0a030b0603030d0911130b031e0c04022d120114 65
    0x8903001ca12515100060a02400120f00e81c503610320306154042e180c101e10000001006043d40c900b400c0d0108006021074020341d15090031003145491419040c4907641c150000ca030000c10100402c41409800d480c6070b003c803142a21f0360721600400f5042151111100e2541d007803201b00710812030580d82040103003c40131040044000500304140d00042c3c45a207040014100c50741c0d120703001401400003007080e00280700e03000e081c810702c0071001c1004281c071402e0403a0403910500d1607500242c0c803174885800030900c20744541810820f40340c841003188985c0f0f5007035501038014841c00303c06913100d0a005084150700b03040180130b513110a244d66140844800d0003021641c141c0018415a445811a40581500f40d441240590114050501840f05003280e503001040818200350407603296031404035004981041c0030001404610030710210514010a060807590441e1000504c244c6441d4408003038654110a944801d0041d402a01c08884500a260007092405540801001400c4609040030300c000f002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 929076834 1250 929075584 929075597
    0x309350f010e070914010f09020304061e1b03020c100c050c0f0c042703080606040521060c03010f060c050709020409021201050306090a02040e280b0a09021f 69
    0x2103014903800e640d0b041d140c0ca456503100c100c060000b5030407400364409803151012690325540c0b42001c3c90502103681c0c420444510340c004041000e2021580004c2c501000164141c51003c4600444c600104148405d0405459000d00e40710005131080c0211120607210700e0061201041e03181c1c40d01c00400380541181d041c003000300185451610203000012143c035050000e040105e03c3d40040c4004e483c0341481ca05501c520401c164209001c0000580b511a5007515050015543d01d1020808034451508510f46c0001ca47d543c0403003e004298010b50081280f80503100e1070348510130580b005003c02e01410ac0d03001da0350030040c400e09200d40e400c01105401001102c2c8496941c400c0b08089920980241061640005007041080d00d010306d890300511060740100302a1504c85d10720342d15000f5040c0d00131310460b00e580401000002c108041e003c411014410200b001c1c100020b000d190544002084561454407000120039549903c50942c2040d0051320030000c0b410b842143d0202d00760799085030428002c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 929078084 1250 929076834 929076853
    0x7051504080604030801080601080114010b03070905090c0a1404050a0e07050403170405030d02070506160f05060f04150c05071202030c0111130f05060d0b03030c10020403030935 78
    0x4040120500613800303902c03a42d070782c0d50503c013003a4100141600282a640e050850800484030030f44840f5045030a500041500c0c3c4e2a00c080803140e41c6c0f0720354022a4440704c003100744261041101c4c010300e04200750b9101c0c46200807901c4550345581c083ca00c1807d5004a9090003081805080021554480a80d14101d403805440740e4944205030000c42c03a9100080703020030140300c24141089151485070b2280003d000213840d10000a980703205100100ea940c1d1040c03c83c040812500914400c80d10781e000c01513403140e2601820011008008075410740d01c00c1c01c03008150310640440d10902400f501d442d40d40360328012482e2a00041c030f040315000801140f204101d080d40340d2200303101e240880710b200c040081d036850b90807051920b1030100d40c20a49a1108590703041105950744011100c46c22000c0401080e4a07032039000080c10b40c091710028000e14001c4149032503000070b0541c001c10607a4801c0e00d0f501d081c1782d00e072103404090054a098400c10b0003805105442d5a80c400e0f00d44000d52010301d01103408602d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 929079334 1250 929078084 929078099
    0x10c1706031203073b03031c0e210d1103100b03040f0b090a030807050909040219120309050a06091401082a19030e1b0d02040e160b0c07051504 63
    0x1e504020100c03d140001e131940d88862000070760317100c1010100c0081d400d1000401245092010400d26030383c5040d511608070300c0a0300188400c5042203040c1c01d9115100103402c141100651010024a00241c503001158003040c0b202c00a5a0140e0000029500000c0c10710445401d50791014005992420740340009900007407064141a103d0310425000e0038800c0c1840c03402078440d4401074502018884c05000d11046511680300e1030b507000350104c4021072071081c501d0420090440c1604810240300c6c00607485410705420003540404c841080c0c466280842da1168200d540004034000c0420f4407848a003045c90a41c4601c0d84035400119041b031001920240e81040385182c003081450008109010441580302c1e034403800000c4501c50941418880080311560003030310f0707a0100c1001ca20004540c800303105280c44021100511545c00340003007044900a96040b988d991381140c40540103080414041220480c0f0002d4400c4030100314020f0030280d041070100b1054035a41107548060031404d000024a65 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 929080584 1250 929079334 929079377
    0x11030408070f0c080a0b250e27040c08071203030b130204090905071d163f1a060904180f201e01120c02010c170603120307 54
    0x5081840c000c0a400d0550b2800b075045001c0140028484140322100310b400c0d81d50144c1e0162107442900d401e41c0100c0d81140000c007160a150316040301c9c5d044004a41030540b400c1d01c26107024600034000e2004e19981d80b0078855560003d4000c446007031180e0030700000000e00a801c869580c05000704407004212140e240441207801541c4003040340c0341c541c8988030900c4418400480600b0b8109a43c18148481400030000b60b00d0160000c4c00351301d40790b85200000d5204184003030389116903004007080104000d120102591403074001841c000102c2ca42c0102d0118144240024040281901055109007004100007600801e010705d0300161228a21040210307c419002101c601c42c1c01d44112030011418a42c20340d144040f034008401400c0a0a516542e90b00c0000da40c0784403419411045264500e40100e841d2022074072070a0615007400c2c00700e0310742a01900644108045a0b035804d5030360484107038410140005170fa8903034042d0403995175254000c410303c0081d64842c00609007084e00082d0b01700d464220 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 929081834 1250 929080584 929080589
    0x302030915070f140a05010501080705010f030b0a140307090f05040b0708250e1903051c090e09070f03050a0c0927170409020301090f11030408070f0c 66
    0x16040091150389610345540407070030a010303241c04503007003103465592010088098040035000c45000c003c46100c91008200d62410590701c00e001f0b2180f540d40b90b800f55a02e002600500740841e0700304120500c464420b126441e00c03a07000509180300300b480c06242e801600544460113805010340200400c0103003290040d040f000b80d0700c080014441c5001d0805e00075848001c0d112000b081412401c1c40101400c100d0403a030240396688408451551004090759901ca06c580e03002e40042032150300341d581164400c8080c0850b40030303100381e410314410720000298460400340008013280ca004014005100610081940801d4407002c648a094880129002410300ca500813100c03903000800c241d04100c014252a001803041141c2407060040e070340c0c0303464080005480060340810300c02d0241d01c18031800b03100d141c1a400300b15001030764890301c0d000f0500103540240034205c1d03014204040030342c0d4051944100784950310380f4061a0309548850751502c03015401100709840116158080340042500325150000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 929083084 1250 929081834 929081837
    0x82a100224100506120c0309100e030304030e04060501050409090503090301020415090e0f0109022d0711060909070810031b0824010515160524070e01140c01050403 72
    0x481d450860445040041c0c542c2040b802600c060042d000141e064480c8560414024056152656190b69980745421403890103603250700d050101c0112603007408002540110300aa50b0700403060018028001074a0321841020300251041108000c40403280c0d008900c003d11071000c1e00d141c482a480042c2c207a030000d030410300c03114454203040090542c0080d00b5170700400390084510300601d445103108007a9081449074014058000941d018070400c0140080134030000c0384504032014003580a214401d400043c400c450303000035245c10211a02e03003d002d40e103460800510200c00d66aa119007140e0105c0003500c200c81d0035214001c04000035280b4121025014040103601e448503141c03405071440d020482500b0301c428890015101c0a04030843c0c00305040d504140c9041050040049074000c0d940306050010000b61b043c5c0050904103e000b24110701c510460314000206110030103080b1580c17940603030380d80b40451a084500c0c0a107500844d00c090070b5141c0070b00e081c0e00308104126031a094030302c111003c80 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 929084334 1250 929083084 929083153
    0x912110309031c0810080c010e1906031a0105030c190212070303091a15040b010c140a020108070f021009080403050a03020d23070f0c0807030c082a1002 67
    0x40c01a405182203901064003103017900c140c0d1518000a40380e0b0a00c0c00c0407410490007503c0b203240742c0c46030301844984d241c4200c84044c4003035030b41100900505200d40140c04d100342c070b0407412402d584a403003920300036003481024500c1c1c00301700802d00007610000042d60080d80501508603100b41c11440142c000d0342d002e81ca01042803041d0340360000c12010442000111a4201e1301805507020401c1e080c25880b480035600040c120090a006854148461200402085445109102d4804041135403840d09200703880f03500d501c1e12030860549061490070401001640001c0c0304235000380d180d40101405a010b1411140f8240e00e81e02d6460400000c03c1c400ea0240e4440c220068005070700c26081400f90f000c0120400264400c8908404244105403001e0a83c403070510300902403110005001d00282240c904030f0311940e68134070740089820520302c0b0300031007400380c12180c1d5890184074108403072407032503603124403c3c01c45094200185500b40d80c0e4801e0440c4100070558030000407051200e250041c101d62600c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 929085584 1250 929084334 929084383
    0x803030a0c0e04140a0e0f010f020c06070c08031501030216111801060f0809100207030c03020601061827051512030c0607120902060a0801140301091211030903 70
    0x14001c04034501c90180034518201011801881345080680c00244400020481c6070b00a8410b901d0488590900e00c01035190086822102c0f082e54014800031180800b581c40b9599508000da0b551078207000e01821b16901040003c40040480b0956441d00505050040c10311224a1039081042031050080300d9159550802018074034064114062060740c820300d00c0f44130740c18018000c02c1c1c000c56144010501c11001c000c5210010148007224140e0a181004c54a400b442c0c01d000740f81c1c40100e40140c0160040000201c3e40c244034887c0039a03003000e403410590080e8030f0b107070600c40b214030500401d403401c1025044544509a1070301030036005105010701c5210a4079640b003004180301490286100a60080055103010074001c22120390241d07081c01d12007040c0f175260080602400182c0c0001754040800914241c000f6044200681a01c045840120002aa82040c9400c03034483c0305001e841c0e07030021000a1480c61041d010242c180e04072805881c10452a80c011a00c1c110100101150404104006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 929086834 1250 929085584 929085587
    0x20c1207081501170706021903020118080301060f0503010f170a020d06060f0e10090506010c0c0e01170a0c091d0105040c05010e06190e04022109101103010504020d060803030a0c 78
    0x2500c1000308130094049149041406999140300d45071040119040c40510307c1030600070b610040042c4540c0c2c0314072040300094509035001e903009009060125501c040003000917841202501e050398032140400c010b260620110301c420060841e2540c6c40d91081c02d8031280181c90354076101450500c40c400204845c3d003004000c028aa40030f81100160030031100401c00f154003404221012109480c0f00002d4680750600100e4281c071468002400b43d4000300c0c2c0005411001001c428101e0302000126080c1420a01c4500e840d21018400500319400c5c640c0305001d492000c0d409a0240d0203183c600f003414003502d402650039680101c900380c075030b42650203081150f075801c0300284d521010100c8036140380201d641001480015911174038020000c4148464616883d540d044480d0f40c009040d0055071042c0c8001c0d14400042c0c1110102e505009106070034200b40e0762400786a032036005d4035403203504503030806090000079080f00c005500c0c81d50300d072400080c1508081c0001d5009030302000000c5140f0413038a10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 929088084 1250 929086834 929086859
    0x2190f02060106050a1715060c0a120c030c1401060f09060806061f03050601030f050405060403111b0105070218041506150906030203070915020a020a15020c1207081501 74
    0x15002d00c113042204c1d0034000d41c0701403200c0d05154902c988034001c0d1034015081d9110711401101c0b6400401c009980141888005985255540304011f144104211004200c41c0c500c2c4d4150010003003420136000c7d40000c0d2500780495440305400700001b03600796440c0401c54400a043d84820421562001d062002a200380400341d40940166001916401e41586100740780d00c1320400d0008060341c60003c01c280b0380c0b194100c001200840740040c0064149410440d032200416282200460201031391301c1070b540000315042081c0c85407120001c2c2e03c8010b400040d07600d0703404410101e81c0043e001100c400e20812506566000d00d0003816a0f080000d08a42c0c3c50040310b00581040c1d0000c85140744100103e03a0010401c820b90709540340c00342c4c81c2d480340101174500308000d8100303d80c51044030907400c42d00c903800202900941c0c0200d0b410a884d5070342d00341c0085090a4151000c006030007851702080305041441d90300c0d5244a09034122004a95075a003164100f80815103901c103021112401082500c01c500c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 929089334 1250 929088084 929088089
    0x22b2c0f07050109151404030c170607081302030a0b0403020102090a1205030406030b01031805031905190f11060a02190e0901090533011707021f02190f020601 70
    0x30000d008041c1804006050440b240c0b007660003540c105840001c00c144910301098032001c10010980e1516141e02e42408908000d01500c049020440c2d03201003004400140680299a03d40390300202c0e4486d1141000b541d0180b01003a40c15200c0c4814680c000b460461442d44030f82d002c0c0e0b00068403002c0302070400c0070303c0030298804030750300c034460344068080340000c0300322001c607010340c2000180252508010b9010300000140c81002e0700007a5074004c2841008030080c2030380c52002079210246080c400d0262500d000e0854881100c02848800075190b6000f00103000f0602003d0400308404905e00c03482c2464040112803e0700c8a9401003100b000540e10841014106900b50602c0700300c0d820038401007008041e0521401640d940c451001c503241078054521854928022102c2c400c20030001c02115614400c42405031b03000503c17148941700c02c03000c61004d40380a03201c04e0740900020240140000004003180d2055102e07140e0070040308135091156118030b5040350f003c2e12044000400d81c100030b414000140d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 929090584 1250 929089334 929089363
    0x1022a060f070f030209010e030d0809010b060c07030b04140d0201140f07021902011b030c0b011a0301030809010516050a020301060f1208070525140301022b2c 70
    0x7005011240b50000901c800c00035007031400507112440c1e4001203030040201c040c5c541e01070060b41140c41c40603134000c1400d885080103078009c3c000002030b001807202901c12582c0b280c000d80c1002d503041c000a12001d00c02c42c2c010b4012044810070014110f011402c2c807120015270009030f1354800c2c01e074000060294650743c0c0800840c071614450301d07011a0182d19003051040302c403200601844a2821603014140c3c820060038000d01c201000b07034640c03402501500d6074030707401d96242c140000001071480000140c590004460800c0e14216442e554402440fa0841c440351814090248280041d1100001040c440f0354080e2005100a982c1c40c0181400c4551903007104c04c4400c0002401d0084042c4111a015056403000b00d080e41c540c014201036040c85818110703241c1482d18806801c9100c1d035248000300907120302c1590542e0b046460740c1050300300e200740c5100703816408055030404680112000c1406600380c85500126410b1650701510540005c800c4a80c2080f82031401e10003a00341040100c24540b1603103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 929091834 1250 929090584 929090611
    0x102071a070c0b1006020c240d09050109061a03070302030d1103070b10032306070c050f06180709090804052202030705070311240901022a06 62
    0x45032a00c2606a0001640c031001950100200c0c0125100e000c48859050b0428501405070070700ca400c400f9456082d20410700140300b00481e41c817040c5081d950f403c900303a00c070b120245034402c0404000c0b0389079004102000d07a01c6980e9942c8001042c801c4c010322a1081c4500340000e5804e04095003e0040005492024082d41c80ba0005000517100010040d481118508045000c01c451002e03070ba1851082180080c03510081000380418000c0710383d000400e0b00d12407040709242030340740c00550600c5000c40c6280c5440354015408600400e005031200d180c16400794058610242500e01002c1c60000180c40d803070710318030181c5690440c1d02ca003071084a0103020b842a052180d1085c90301c40481501030350040c2e521900b00060203800c0312090000d5480255414034055481e4500040d011b0195040084150f021a528211507900401c0110302d040c2c1035a03000d1074100c4445450b8043c0071400b140103148400c0356508000c2c01c46c049107500d015946500048441c0d814024601c000c05080c014090200340c0d041d000e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 929093084 1250 929091834 929091847
    0x30c03030f1112091504090c090b12280e070e01050d020f1306050d1a0f090d0f0504081501080d0206071409041103071206050a210c050a080604050c030102 68
    0x10042243d19000f0b03106003034180c40384038800c0011500c1240d200b15210b818000640094107102d640c0106001c440580c4441c03201c00c2d61030781303000c0c180e2003083c54038580d0800c0e400004034800307098403030528031400c013040b142c841003903100041048568214802e009903000c0c4070200710404032240482c1c0500341c01d45281a082e078981d8040f42100c06012a80c03441142100c0091902000c1c85c1d01190003400010104200801c15041c110180940c0c0c3c50f15010b1b0235010400111110441345185000d4081c0400070100103c0c0780d441158024440ca52040803c001040000f030360b000c040103503e4003140c40090310006540746c484207074034141d14a401107040d0b401050410103969041182d4104501034107001c2981ca9140c440050000c05460403107051003074000c0180401d407940115164200c800d0510204486c0d030312401000101d60307041c07103071560003030324086103100104051300d0903002c60303225909583c4115103400c00a000485990002082c40d4040010001030110410800d40e10b5501600218078102c17 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 929094334 1250 929093084 929093117
    0x190c0e0a0510141e031602010b06090915150f180d020d02130f231311010c06150b0c07121a090a2003010c02070f090b1207030c03030f 59
    0x1180014110078843c00403030f441ca00d114604644131640c0f00d440440755039a28107040f402c65600c000010788001586081069003a504019003201c1140100800340400d80d5100220013082810040303e864000030403080d04049191010090504074030300040c40d585070486103802c0507120740d84108040c400d40581c0b08500140c1c072120303c84030307103560140e580e601c0c0101603501040240100e04100c800107447e02d00e40d45010001c0036109400d44540d145c0300c21700c3c4c0c3c032540d000b080035262990000d0124032540038191015030003440c510b80024410800821001058816421645825405821a0300b00000d0000d14a5418441e000280c0915581c01080c10002e4070307100840048544c0c50141c49103103d0100300445402c000c81007505034130144c14080c40360009485240d0b031105503c000d00a6003003110500a4500100b14082502d000301c1200070445e25140303240c4090001c986031f040e00a0542c03240f10860100a001c1d0002031806000b21040d190b10b10f10300100388800c1282400100301c0d1903007504900c0d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 929095584 1250 929094334 929094347
    0x60102010f0e010540020a0e07030204030309050d1703090708060c2d0904020d0f1a0a050a0608060d06060f121106180d0206041701060e0f0f040b190c0e0a0510 70
    0x40c064200740c14170100d52407020071038000c0e8680200308400d140004012502e40d05400510a9910a0792000c130019660824040d00300b000e850000d14240202511701e1800c80b000024583c002e81c0e01c1c08a0384220754031581079050050580d202c0c5170180c80001c3d204200d190615078481855241c2d500c40e1800c04030400c920300c2500071410303240d210b280c00086410100031941c024101a0340c085004000780032051103c0c200381c074032862000d802241c164000040d82e1501d240100111000d607198005076640b80c0c0c00f08540b81038102c20445116581e0f00c000b00e00080380317610000141120001d83c02d64944113050540ca00100b1205a6114440800c44404200c080c1c020500e1002010b803007680c2e0f9400c1500c00100a030090f60803880c1c0d40c0e104c12018014840d01500004102c2d6440383d025403840d12808440c00301c0f071030304540031000d8541071b4002c103000690503c069030f4088020a0100340b08440154010181e654458000700002d4200082d5486464003a4600300140707812101a00002e002580c0036015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 929096834 1250 929095584 929095681
    0x903120310031202160603022a0a03050c07210b060307031104020307021002030907050109051c020607321c021c030e0304030c1e080312060102010f0e0105 68
    0xc5041c007051016060b13000300002504000c203440342a50042d19405c0050003900702c028a880000f02c6085409200101040b4030030000504d040079008286c016282600d40754800c40a00c041440340352000203110b042c1d40608800412001303402d581c00916814003401c07400c005014035101c0c0e049803070b041000034990501e600c1d0300001505d01603142d039200d643c141e041502c2e80300d002c0c045030700000412046803008644082550300c00d803166514030361a0710601c4120380c45100c00100b42a4003081c440c0c0986002006000030341d2040442143e1a900c407002c0d0885e072070002c0c1c5248000c00e480b0401034041c403801c0c0030545410760034511107440c2f4141d420000350f4840180046070b1089801c020101035207842604071b1451145260f003240c1e0346540e645080d4000405e14030404000150403a500b00c0156002c0901c00c0031615400d0046050945284680041d80b0016110303505541d80d80c40c1d54650920580034219100c101040002141d1401126000f00c0c800c0350440501c0001880400c8560100180d140741da4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 929098084 1250 929096834 929096843
    0xa18090b10110c04110405030106081c0e060f04030b06130b0907050307090305070b030907080f0705040b01050d0911010f0203070b1311090f09070b040b1225020102090312031003 78
    0xd40c001110b0140341061001036545401c2810b08401e584990400001803085401c00d030000c1000e542d41c1e0840607117501030a24064484032206440c2071130329205012410100c040148090b10745400454100d909521682c8201c420360110b03405c01540785400300e4a0300c035800e030700c090510420340a4000106606002400031042c05804004201070f07a2090fa2000c024640c082d0032214001d8580310b180742640c004550841ca00d2041d03210102d1030320004140d0042c032100c841c005151003800c00c401c01001d001a111075604000303090001000d407170102c0c004c41030312500680640741001c104800062060611411050555008001510020702c1c1c4149031030388402181c90394039400d49107207000440220040c0c52258066884403e1040280003401000d000d0804002200c91840d95503e210005001d130b8854074050b118184200000d0f003403190641c903032104c920151203200ca4103c200c1c60000100540359130005079400708400e055400c1c104480d0107a4042d0300c2c2c4041c107629110784400007880c0c641c04000d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 929099334 1250 929098084 929098097
    0x30e0f0f07061b200a1806081612060f1d07062610171b090f0f06031608030405090c12010b0a02160e090d030516110c060a18090b10 58
    0x218405450080081343d4400030602e070303640d83c0d8a1070728000100780240034007116443c10400280e042c40c002840c180d0030680c1c6110606641c500b070500110015603503006c0e107080e5110030048810540c940315001c00320b02c010000d03440304580a640e02e881c0140d69001402404000e080710001c054034001200c1002071594500395496a4a01da0110b003000d05600c180190700152501c01c0f440b54010035501c1121145c181c4501d90102900100f1616500907200050340c229808042400c1d007145c0025142e21460140807100321143e080d40e240c10061107031780710b041d050300042030900a6140c5045c9554002109e0f500550a0400c1179200c03415a841c18425140700c00070024014291900a01128000844201e140c0341c0055807060101e1621404032007074542802a1841d0b88801400f034440c5500480f01b41000072902d511458050351984014003900820b8800d103101901c1c29a609001080030092581c0e03100301e0381d00030072114581802550030041c903c0d800e09030015041c2d150400f034215405060316010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 929100584 1250 929099334 929099363
    0xf15060a09030c0b0418060e180a0507230a0312030213030b04150f0e0607082206240308070204050a14040c0e06010f1e030e0f0f07061b 60
    0x15202540c80340c2c00203020aa42800000354111400054011a421180e401c41648500c00e280c00031264107014014081d040e40300821415150698440000c503001412140c1554050729001c0c40e00007150b100301000ca5a501c09433001d0426101c0c1c1c1e1448200c1681c14102d1a4203560758488040901c0c40c2c5001016800b0510540b100c0d200f051000007140c20088005482c1400e0500c04822a003803856804003500704044071a051289102e219030b0f02d801032004e4134060302c81110440f070760388010713041000502e154613500034a14041d00e10f8442c103c1c0300b21800201c1c2c221301075400308400c00c01d400c1200e51095203402040410341e1101180c1c0e24540c1100d00040301c2c0c2c0c1c0d840d04000141605041a82e1100d00e240400041007002003004c000d4600c0e03030035081c00c16a90b0072300440e1010388046210b00091406041000500a160500c2003000c0480c200400c007001d000f00300ca0f00c0c104c503001402810b41c1c413401260450f0354003840503002414071442c00b1150003494840f40c02007805880d8000386144a0b06085 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 929101834 1250 929100584 929100587
    0x7140109090c09150e15070f17090301291203030718170a03082d09030f070326041a25031517070512030702040c05040603050f15060a 59
    0x55005001115034070b00904c0c40a40c80140782007890b901041c01382c041046107084070132140c5c01340d9189980c0011360207446240c81c1e88401c003031040403264182407401403180035081d54081c0561070510110441903900c115030401c94018003100390000c0ca005140d4041e0398000702001104030f0f9804081c500b081e0240800c112000102620240e01228550041c00407401c1990300201d8413900041c0640d1b500c407410341390140260aa840e4560b980030254444040c81d45141001c55041035011020f03070300b42e81c00d1147c00d8504260f161b0100000318002854001c0d04030301603101039142145c8510701e000b803040d00d00e41503039091034841d0079403400c0e00f84030480d10004242e20313803010540a000d01a00c810070340e505180340380500908850b07640c0311429811420040f07200301049258021100030240103108440c40c00040c803182c540000c154001c0b0f80402c001d0f440140e11540a92032000701223940720380c4d84500c0d01d07800a0460f40c0242130300b2100d040b07004c01d01080c0451401d0b0b40a0080701104d4069032035808032030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 929103084 1250 929101834 929101847
    0x120e03160c0e220f08030c1c271509050c010801060c0209150f030f01201806070c08030712080703051611030c0105010e1522021e03130507140109090c 66
    0x80017402803030000304028028070701c4c2010f003003a00c56620043d40311140803081d50741a250341c000200c10305c040108108030101c5c810300c2c5041389140188110b60904140306400e100781c84640340b0688455010f043c0744006d40d603111a94070b00400182c80c00f0090b10100c1e9000845040c0064071140c22014101c4004505682d0380a206840c101c00408642404604105650180c08074481000500c0700c4107411034100301000c1c0c205d0342e0f04400c04d2000100303e10303018108100c60300002c2c02070713603103030383c800030200cada244e020401840800e0007005120102c00b0500b000500e6a6402030500c02010700342801d0021105121882804110250502c1d1400702c1c1c1d01c5c0005880c1d8010360b50204890b41c00c0c0000041e502a5000c2d400d401044921012107240070128107100700a500004c2d40c0083d48d00c90305416071040c1e4158050a2068100c69070582030005400d10882c451f00107444502e40700803406060400c0000030080e41c001400c9040c0707824682c20780c442c00601410813503c120b424081e112174050482c14490b80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 929104334 1250 929103084 929103113
    0x1d0402030c0919030212070b030f090a0c0e090105010914070f0e030703140f0304030302070902030a0f06181b211d24010e040201120e03160c0e22 64
    0xb48210f10208205082810756005440141c0c0100f280c3c07982d002d00d40034082101000d90390b0342c100b400c0c0386485007000700b049481c00030004111750062414610000c3d41640281c00109040d1014641506240140c2421200e040c0d00c40316030780745007611040400044207a00ca502c1f0803d17080440e85800d101c4015038230440141d110700d0345801030306000b10403c48030072907045a0210050440303c459030044880c40d900c2c46240006130160380480010424900750360002c5601084803070780030400c80c112103450000c0e600d01e0340081c0d01488030507442d0583c0410610614903004032565020415851858015140520342c0c0b83e101050807030329000702c54102c0581c01c007044149000c420004501c101d600c0c2c513030321421044440c0307806540107070301041c10f90704268100303051b01c03003021200e200380c0c881d540191190301c0d4820341500c4e030340c2c2c40700d0305841c5842c81400507000c0071007007582d8807009242c0c43c500701c440411150814081e10640b031081c44402c0b041d804e11682c6000d2641040c01803480d150619411440c02c21303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 929105584 1250 929104334 929104339
    0x4030f081602041803090b0c030405100e2706240f040302030307050312090106060822141006061b140316060225050c010f090b0c010605010e011d0402030c09 69
    0x55550841140d100c2e44c16440d90080d0769010000c1e8880d00020300030f1007a007005042982c018881072045140400e020804502603042030504a060000401c600b10012151440c0703000401400100500c03c44d142d15038805003c55074401800c04901904640303074000204180d142d14007003004603280801d0005c45000d50f400801702da03120160b510f0140c0c0e69a2102c0188903c589412000c26203002050107500107880c1142c4810303056030f8800c1c0e182d5807104800c0d5000000d2642615824002c80d9900140c00d1001000c000500000100c9038107100c140c4816034421000c00095641101c0d034966541040004640e10601225814640b110800d00e1401805030700080c0500d65001c000401c03c043e4018142c4031a0315000d01703020850301c49110800502c7c482b02178a2a000507101074055803095030b605440340910b04041c1849501d5100016894010082c0705c00329a5464106200035a044aa814601c0b1800d280048112140422a04038100300892080c0034607000f1020444625244007030310013200c800b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 929106834 1250 929105584 929105591
    0x709150210090f0c05120606091308192c0f01180e150a053d020303061201050601051e0f120402090906090a0f060603020a260304030f08160204 63
    0x6070400361070005880c40201c4124a0550001075241000003544580c110108041d0809075a08c00c2880325a010041c002115540202d0000c1c1c0000e1001018010452089051203901c1018407009080b0080e0220b4215030340303c2040130803040110b0f11b00d060b90b4151050781c00103100802040180ca20a04600c3e0301035048502080c045400d105600e0028400c0c801004403030716040010040c4500e04155000e019040b0391008107085010400d6841c080c52002d50301d441d491400c00096156030302c503403007854010060b0000804c1c03010385d29020080c0790761a01032000800c0075040003000a4400d00c41c8680e000d4040c040701c694041030945160645071481c01404403555a104d1910071036040203c00c031f030100d02c1105250040f81c10003500066180c0706200340c10082200c85402d44a03614091050f034403c646242d11058044010f89441c0c2c4024000c000001700f44a000780c01209040010300e440300106c4050b802030100308041880081506007158028000c6a40d400136061000e803410382882d0017941203400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 929108084 1250 929106834 929106851
    0x3191b170d08010605130308090f0a0603020d0b030118020909010f020a0806011707050f130f030305120906073524010509060f090d0b09060f0f0709150210 68
    0x2800301c0c0040c6840315503650320a0301d07070701d42d0010b8030076005d01c0620100003070b01a541400041d29281c000c00a0420081140c00c40702c42c03d400040c189803030b54004000098021038200c4001800307008030b407114582140240311820320340c400c2054071100f55401a00c039040c0d0300b0105103801400e40c031641c41000300060075962a003880308050b080300d0090b600c0900250030b1700142d00030141480c3d040380c0076010641d202894150041031008854104a600f1a200c1001200005140807c460030000452094480c580c80d80c03600c000c0e05030071800c002c10b034007402d0704903c003007240c6150700c07003c00d2129020b1042c404e03071081110a4089842d03c0140600210400100244540100c031a240c03e60f070704d003002c51718080300c03440e9100441e800d02038031221a8020000744141d40c29000080064000e46801410083e50010251107030346500c0000d079a080c06175081070051116000c08410744e60351180d0740340f000020764181040014554801d5120b21440c1c010742d402e040391900e00c00e0141d03542a800c48103051003810b6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 929109334 1250 929108084 929108129
    0x80a050a0507050109060b100c170c030d050f10170303040f110301050907030b070905090a180b0109151715090115090e0d080903040e060d080f090f03191b 68
    0x752001d905108404104e222a4017600c1403c030005016400303007000011100c1015441c043d2f401c41113004040e0b0009000c40e15103282207101d107501c618400b00c0c0d40103881c14401c001500c030320895000301c9084644c5031021601c805000088941107984203848501800c203e0511000202c41008240e60650a220a10111000018145003924040e0000d1800c6032203442c2e040d200100c1c140f00c1c140d0440d02141c009a508052940300302e580c140c100d0905102c0400d40c1c1e880c01030165007604000d82e80c0c0d0f030303c05418840c3d201d0080c600015004003000e07201104482140c40303546500503090240e0054504002a03000c1000303410400c2103105080241035003e444241c0840900440c0000d00c002c3e124000c4200f01051040e03242c0381c09500010055840e1a0030000003817012800180820f400c42a030003494400030b034850b801850000000e24247e0344502620081211055000b20014841d921000d0740300b02c16540b00301011600781c2e10649c1034020042c2c00458107419a070fa9030242e04100381058150b241c85 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 929110584 1250 929109334 929109341
    0x2070c0b030717060a06051b060c0408120f030133050c160e01150314042f01050409020a09180c20030a0503151e100309080a050a050705010906 63
    0x20701c1c2e00d8840c80d1030846003003111800d0700e400b21049580416000010041d50303008070300401c21194110706076452050296606440d0600a54450942e01030004080100c42c500f4803c02d5003504100340e041e0f00d0551811145100d03400180560052159482c80700303d8890407417202050341152014012420785c03c80d1501514a421419030880c007030080c001150311080280c0c1303641c42591031003d00042aa42803441b10351141a8450341d44080c955244070160104640340100c40c8160300c604014250360038070301818464018800d0820190146140380d801160b0b800c0001e59003514108400180c030f602c1440300c02c0747c43e40341d558026006d445094481502650141d000a26003801544410070030455150040e0015040a6030800303c0d60020f01011072000d20903402150070581c0d20b0402c0306510b1000000485000400c03c1c0034459510007a80c528039400d00d80c100142d408000d0400300012070064640401c50301c20340010b0b404100c03000560510f8140984196a84190080e008001c424918603155004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 929111834 1250 929110584 929110591
    0x8030708070c39050a0603020a111507111902130f060f08061e0406090f020316060315120204090f170a08060d020607170d14060f0d0309140402070c0b03 67
    0x3c8207002d01c0040c42001c40301c04089840140603000c01a2030071a04400941080c9110020087d1030076218414003800c0020062003090a2150392440c240881c01801d581d4400762451840c0e0444015001c940c118241902c440707503010f4130400091003540381840018180712500d0026541761000102c4e400498400c4034043d940700c40100c500a40300c0c0c1c80580d01c00c4400a2002c90107405080001d400182d03503411000c42c0a111701606240c8827860380c0080e0903e1080459443c4203041400c5c2006503550500400400902c0b010b40da15903d421b121390341480c5021280c3c0a4020ba03110040d0300200b0400c5140c941042d0b4014a00c031720101048004000198802d06094001031049804108140707003006400140710380c02456645440035942e500042541036220560070041c080c44060b542c0784075401501452030300441440c10510708071041005000c0380360b0225026410564000e80040e8001c090720003512480100d185040c000c02c00080d01a10480c14001d040b4144403400040e005444000b4501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 929113084 1250 929111834 929111903
    0x1f060c0c06080c160f060e0312010608070e010c17040f0f050105040b07061508190c350a0c060c020108070e090c0d090206030106020703031101020708030708070c 71
    0x540e0380e071100215501d110540307075820103074800c01a08a10180c80c141403000b0b14440c810255100f02a6201d00040350b0554240200c0b43d013002440402c0702880148180c0074090a0401600504040c40000c100f15807280e2030905111518012006000d41c00003490303030210700440e600c0e5495440c3c00b414240c1d07520500c00c00582d090303d914007080c2580102c041d6410380d401d8480039810300300103807696005001c00121300342e1070301c2814401141202d401c1c004000f9640801507002c141103514a019000c91500303910004802d40c01c0c044080906200b54200c4208900000e84185c090507030240319424500d44000050006044280c00244540c00000b400e1925000b42c0310014203503507064040d81c501c00401c000070381c4840008000345031100080301418180c80302d5240080d01071490b60114186a00c01e03005030300560b1017120304204040e406000314807603990340b038002d42c246040f80e9102801400090004d8003401501000a125284144080e128050300601010b11216440401400d072828103521080e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 929114334 1250 929113084 929113103
    0x5101710060c06110705060403030b13050f062707090e1621020f0f1b1207020d02011b060c08090304031a100f06120b010807171f060c 59
    0xe0444040e03580345000c480664442038211011507076414000c18407105404441342c4c060200c8404203004001c4e031403145c2c3c4291400990002500100301a0382c0e00306408064031030902c806c11091085214015421207001c0c6d8804100401d0283c0001c1c820b04400c0800310071005030010040034590120b0072400f12010321000d10b50688a80c40001d91424400c4980760104100850842c01b80031140326a0500341c104400050500d00a410007041a504c5131680c000900c0012650151403444000079801c1c4804060040003241030b015104403840c003490b00c02a00c6044000e0120f019640194401c03021401c04030f0b400c110040c2c051810600408090102e2400150300400003542204000304440c184c0f03410130112804140302c40328604507000021f182d00b14a0369850000200c80d180351000e840608029128600c41d0349040c3c5202085139069a8886d0420a01005120581c0e42007914001c0b041c0399943c0e0f09042c2e5072681540381d00c41d4800000e1a01440040c01c000078030a9000319500d05080c85200100c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 929115584 1250 929114334 929114341
    0x6070f060c030902010215070e10360b09030c060d0504050c0303040f0306020d2007031202120106030c1826010207111912080d050a061a13051017 64
    0x450441e00710703c00081c0541d0140e0300b04100d106d42d440c04035a2100c440e290004090101c1c030042502d0030b0480d0b40d01000301d80b110b01c218000400381f420050014a12013096040c6a00d00e1070311112a403094491154140c10020b1a030748151402c0c0002d003083c64028140b144e13142c02400700c2d280140021101500c0c1806200d1301c800760f031726000c022542124440c94142c500345003191101030080d400507018600c2c61b551910f080010315800320115100c2084180c82640b281001d04001d0100c00000e055540d0080c41004a031100040881c1c00a054520754a07000540000b850303c241c0d060722800311031802100f11210006219551100080e0350b050040c100d501c4001e15290b1406d09030b000b00c40c0014081d00f4056000c800c00d0510b02d01103200305030310340c204405041d60b400e80ba07001003205040680e0f22200014000101d980c2c10b01030b451700b043c08031404100c103515180c03e0414840f69080021000c0100150b1400400c99104089003d01801400f600b610074001801034090400c8120504907205240e001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 929116834 1250 929115584 929115587
    0x1060c140a030822050f0715051c0203150901090219080c0702010e0117010e152719020c0102030901180f0b3607270b060906070f060c 59
    0x80310100c9900d40c5904101e0303169510400001c213030354a60180708203600c0781424045101000105060310f00c14003c1c00103582091024400720340c0d0702c100711003404010000c210008440c0000500c50140f0650016141c0d203565507841c107500c450f030b18010360018541001007402c80d401d5001340724500f0301039800e82d10b5030010602039504d44006c5910807035264050040c02c026501070001d0300f5030ba107814501101d413040800d0544c0f00390030782a00001043c090030001c1254500504c00384c0c84041c00115407016865807041044151131424181d030701c501c403880b540811145208043e00c10040d0f004c01d0340564a0300d12554406000750401c5070ba42c6401e40c02c1841440700070780049401c0103a5900000b0b0128220000d460744280b0720406441c240c1440010949040303030742c0409081042580c41d88059102c108040880c980c582420740e0000455034014a210049901041c1000815245031500c0840d440803040b0003d58507018900c00180c22500000d0094100000120380382d100d10b01c034010401002044800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 929118084 1250 929116834 929116843
    0x9080a060b13090b01090e031608030601023f0c1005041a0105030d0302070813090b19080304120204020c010606081b09010933201504021309050601060c14 68
    0xc1c0900002c0d003c2c0010300289486e50042c10b41190000116454401a0040003240748004e079070541d1081004424402030b90f1b0f050054103800c08690781c0030030300300da0319040c00c60031313020010400424000c4034050b00c44104402c8068410b1481c41000b40d5107510450440c11020b000c08030350072540d0f001400c03020140380d10781503c0503041e140f000d402481c03082c4201905034001d600031481a2403c85040c480783c1d4244030b01101070006045540004103202d9568824001c0940341d5103154801c02d100844d09210075500001031b10202e8038400284cc2c501c8010b400410000e2041d04d108513420350034560041811500f0070012400f031081c005039801440107070745500305d09001c1caa001c1400514819010403c1c0110f14006011207902d0040400d11420074050042d8a00c160070280b50104d190380b2032050743c41e404000d02d0a00d5114100107440005403840000d018886c00500003440b03090070702c0100a040781580c0c0080c0d0300d135506c10101e03200317561103123405001844540c40454840032211103003040d2401c0800c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 929119334 1250 929118084 929118101
    0xd06150b0c01110a020d141c09140606010203031f050303070303020405010f051c0504031106070806010e060705060c0313050115210308040206092b020f01020a0b0f040309080a060b13 80
    0x2405050003c0c1b000c5811603000b8241d8404141075401442078280e2250007481032514000107800003c1c9091040c640310580001c90134165040c1d0b0050381c100107032a40c0100c02c691380900c04000e507400100c801d07460420300a40350342041d0f0f007600c0080f038113900301a0568010b0007580d409032a843c404100743d1400702c5481c89a040d14429004a41504000145440d00290740081c401c0c1040703401e07480707071030100c501d4040d00300e40100014080e18244622560462001800064241c070b855251003c0ba4440c1c56603000083c1200c0c3c100400000020b40c04807100a0003401190302a000340149901c1c01c0c0301e00d00741540c038040c1030386c807041290001b58003600c0d0404000742d0a901d901d03182e206070368070303020001990010449560086800800315407080e00310b80b03800c03e60550101014030301c0300b15070040c000c1d11044145880c0c195440342c00c1d48030100307104001c80340d801100014110080e03501c1d440c0443e2000515032114000d0700c6105503600030085650003000304180305444104400301090b03220130544845c80e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 929120584 1250 929119334 929119337
    0x1d0d0e15120c0c16050109050a0503060c070f051603121d09060105040b12150418140a061404140c0109050f1219060b0105180d06150b0c01110a 63
    0x30032070616404a4421441d070700c00d000e05038550074001d80f07944107800d24091002240300c0c0030164105005c550b801060407805401c09440500d40941003101181d503e1001a0041c0b05a10011030814100320812300907d0000307a000c6e040e266007991076400c41c00c001ca4580004c8a041940b141616100e5101d01c200240e5030f186540b030b80403400d40c11024000c6a40c800b40106041210400012034000640e030700400503000c418540780283d103490b4a84000d0440b0b12902d41d44910700b0050200030b520000c0b0542c8214a0300071925519007031044e0141031510104c01d42c001e10740c90030540a5244141c216114900c582c0c01040c00701da00c04840c9415a0b12600000c80c0140450031900e001d02150418030404880504082c101c480c00308009581185803c01e00144c131a185228185910f040040c64001e115042c80e007806c1039820031212800750041202100e260074002c1d0b1101c40f0301014402a500801901d54580340800c4140e078480c0020121640000340c000065803e08606251a08000e021640b0120b100d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 929121834 1250 929120584 929120587
    0x90503060705030708060d1202071e03081e0d060f0302090a0c080114180a09020102070e040c050111151f060e09060909100f0b040e01020a09030212011d0d0e15 70
    0x13190b100b69030080b4094400354010891135201b100280c3ca41311030000004950f00104407651a1003401e143d001c80780003002e00850003400041000900603001c0e688e146500e0700f00d000d1001d03401161208580183c00c600842c0605140c0c000691452000054064078026540c0d0416035840d031a00d00c0c01e9581c40101d610001d145040100041c03c40d0b03009504100d600200b1024030341c01442c226080600041e1070044a06030f8178800d0004568042100c100100b806000000807840e2940b240307142403407284220f9040c01600c0c0317648500d840050003007100360003240e80122510305000d0025010061a00040034840da00c4041c04102d840c004c000c41e200300c440c02031100318103550b803400b40080d14130040c10260680c07190116000d007008881c090312246c003800d140001613292400041000307855042503050042d9104000343c208860340181074070103880d01a039880900066000055005181d00441d003440b40203100180c441d01200070458201460b8241e68044178031110504000003d00c084001c182000340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 929123084 1250 929121834 929121841
    0x904270605180609010e15010b041e080d0e1e09040f020d050a122c040e03090a030b01030506060a300210030c11030906070f060b0d05030a09050306070503 68
    0xc550403a642c0102c000350080c00c0800d24008036490880162030442e620b0f511500310600210b0100403840d05080d0101242160354584092100103200724029480300002546c85048045010340079070303000b401303084200c0750052006d181c0140749a510b40c0c0640d204070000382512450808140c80003850320300043c00c1800e01d4440d230b0f4401c0c244001501c0200d8200d8055a00d201c04554240320a10741140942c4d04442e240480c44d00c0140114100c4075065206240c500000f2061001c1c0d44d180d504010054400007101251039000321728501810038941c5d800200c0031008820014081c0d006812a4400c1040b600c042d19184204a1640131a004100c0c40d07110241d0b050440a6541c000207417104810029603242d0710030350b008686040b41c462141c40c0869240c8030113a40301940140850030041a6202135403c2044101c0020317024030070700c10003924100300110035000b40030003640b2151240b03500400007004240d5919000b5240d800c020f0428012880070030000850342400b240c01441140b2030380c0c4041c81c595 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 929124334 1250 929123084 929123093
    0xe10050702150a0f030e19020d06060e0702030a0216140d0f050303042a0305030a031e020c0a030f03270501020910051801020705130c2102090427 64
    0x2000040207a92040c50045010030085188004107078900c41580c2d1210945041040507054428100c1e40f481917130720100b4800c4d18080c548406590032a41190000220b030300e503045c100060020382e00301c1140280900144581a60000014001c01101c2c0e001d071100190b51007008807444103180705051003d03c0308811a03c0a1400e140328140280c0b040c22410040086611013900e940c00c03c45040f10344081100c0e18802c03d02e581078407140c0c00d80c410030480d100c0c282159295503c82c080c0292180074161500d524a00c4413402d02e81400b03a00240c00300442d2900d0b20300e0400c81c2d0343d0b450107409a0125101c100c11104a501c02e014140c0c00030001c44242100d910600217142c080150400140c90555080c1700b400c1c0380e03582e41c60f50300340403c3c62551505d032185141c40344182d039916031640303d90556100c3c1a01f000b00b91104950107815003065407002441000d0104140c80b84a1403c096011454084468841210865003d080000010b503000c01682c2c03200d803210310b855038400116a01c0034030341d86480c40025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 929125584 1250 929124334 929124337
    0xf151003090b070810090524062503110a031e090e0c03040b160e1302160605010503100b010c0605060a080a0305041e03050c1003020f070b0a0507081003140c0a08010209040c0e1005 79
    0xc8030040c1c07809d8500301103d0300c8513101154034940701600e80d03c0110840245540300c010003005141e000054034181d11b17142c0d805046c8a2154a44814040002208100c194000c0c005203000b01044010382056241c02401d0301240e1384200d800b1155145070382c0100701081000c648543c0201c806448001004403a0b40c200f00030309624906c401d9040f5002c108041c0c69610903c44648158800c00340400c03d541480d0416050851044400d000e42d0b1500800450036a80000c40e10b4040e6000500043c5d2515080d011801c07008850300884910f1003900c980303004165100001f0401c0f2894a011215202000c440c1e100f0760550610015045903c8503010415034504000020380c1140c880c10300500d0080d90146000003604038860035202400c07a2405c101700007134103028080d071000c420b1604c0e021a140000030500c15547c02c0c00045c1040303500c0211110403070802c0014051200009012000c0513135101c509038040d60202d0040c502883c00e08400d60590780c0510804414810010810f0344111001501103409 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 929126834 1250 929125584 929125651
    0x80a0b060301110f0c0c031b0f0604030606150f03053d060908010506030d08161115090c0f130c020709020705010209090f151003090b0708100905 64
    0x55540e5031020095928010b0007032508450140549071034050100603181000b1800240e10701070340180c4600c08001d24030238600c485909049400d0203150302c0d0100442ca040c000c80d000205200d18240002c5003140c04005040c12043e032543d141442ea21940304128203075442550007943e00490f06004880350703c203410600000c1d400380703044560308900881c50403894480d0b031390048001c109811818040080b0138040d4a61000d4140d0041525200d09034000304100340040c03800700c94012060900c80c20510a408420751030341c94100b1164501c0b84071814441c01101558802c2c0144101401d1241500303000489440d0000020700c0c0362000041c881e41800a403450652a0b0110300588802107100300c1544050044140640c0c001600c1c1d0008409028410308041c200c000307003061050030001900182003040d000e042098a8440000e40c2d10b44054000c0c003c1848000c04024060041081180d40405114800c0040f6200644000d42e42c20140040316030030313198400452182b0a000c0d23680545030145000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 929128084 1250 929126834 929126839
    0x60732030a0903020a0f030e13020c060606070311010911040e010c020c0f0d050313090b030a05030f180603160f0c081608070507080105070e060f0a0e0a090c081f080a0b06 75
    0x240d14000d6038803540d2046180d01b0403800300d1041e19503d5101c0c14400820601c07050341d501c0842c0383c458107c1c0c074507079100e000800b0b0034030860000810304100b62141c90170303e503c110100000d1000d115949010810b06911988041c010f52602c14003a07110a8140100b0782403031780d00d0b0048c040c5450705800340f12180c0000c048907900a0090203007000010f40800040c0f00d04031841c00586111424183d60030140c481e000d841034482d500400c01d10001c82d4010084801c000c0046d2240b5581781066003000d4182100764030051351040d0040204400070004440600c02c0c0707035040d640c2540b01030000005880a5165040181030307410140014180c43c204400c1540358180a00c0381241419590f030368103461301750707590010295070351280c0c00d01c40090b40050001420340c0c42110000d0510309403011625403405000003034800c1042120030b4002c2601ea1804081c0500310400e400d20909002000150002d01e0503940004445031802001c030510f4400c04a4005841071540909400b41d0305440b0040c1242c4051714003603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 929129334 1250 929128084 929128093
    0xc0b160318321e0f09190519060303020109020a0905010f0306020313060c0f020c01020c010503041e06060816051f4b091404020f0903060732030a090302 67
    0x420968801c0f10320740004020240c3c01c109070310840c05111602a181007141d0181001d001402148143d21402410030918014001031641d107004d203040121f0348111215100610300b0700040181541074015640490080d1084121240d5800300c0b00c0c200c0304240328441000340c1c050303c00e1000402c42e03001150000580d05980e4204c0d0401e407204011980311001500c04941d21121070b82e90760781c0500c034140a6850900252440041410000c0c00d03621008200504002c030010000d1080082801541c0e01c06411a00400155849010300341d5190f40c0c1d00300300d50032401e240c040004c1a26102c85404e850710001c50b80002c00d60194801594141e003e042c4507100110310301141c0381c040c0078046407100b8402d17508026803038403c81e1403000d00820b01c02c88800820811104402e2001801125006a50700000d50740140c1d9240c0080d094281401840b1655905010f504140a20301d54005414039031800848660b04c050040c45a4500003800e1140c22080d4401c801d10000e101c41c81075a002d8110300d40240141c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 929130584 1250 929129334 929129429
    0x1f050f0f04110d060f08011b120e060c0406140408031b030f0c070e01051f0e0a0509040614070f0206040303020304020a051305070813031b0c0b160318 66
    0x502c0641040c4410b55103a60ba900081000300c041819200041821030020400a400c0446000c40c2203050804002842201e40b5542c0b913081c420790110b03801101c80402d5a400307040c1400030960a074806d00c030749000644658461030010300c105d81101d0482e4003ca00541ca00b401030003048140540440c1d038400c0310b020511580b1b4500b241e02c0001c15401c68140c000d00703821800c0c0300300402c01c0c1d14180c2081c2d001c4c04041c481501d00504800d50448004441e040c03480488101900042c14020b054114940120703000d42030104000301608200400c000c0d4610f081040e540703002084a9500007071a801c4010b91061001c60f010030b000743d00840d042800035000400c5c03940c9403c0072072110b689481c40203c13503690f0b40e000c020304158403603041a0030801c8031041d020601d0340c0e03440c000c04c1c0e00301c0c01d43c0c98081b05810070301400410040d00b00d42c01c018250428190b480d448145110268101000c0003a03010a10b0030203949c3e040300902c4c00c10f1047c0d400303204000d0350040c000c2c50400d52004000326540601300c0f805d1103d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 929131834 1250 929130584 929130611
    0x18030b04081c020405040f050c0702130b1003062102090c0c072103021213140409050115140105210a060905130611030106140c241f050f0f04 62
    0x1000c1c0070b4580344009a07032a40303000248402c441240e20091665490002800b100d00e401c1000c4070b50882d01100d080034829040529800100801402c06038001d40d00b4094071083d54046e0484401c0307541c1d5200c1c2ca50780001c6005c6101507060490f800960169040001039200b60315580941000743e0210101c6051a45170090051591540b071103c507a4503280d4903e107010181d0410811090b0084001c616041000804c0008059259401030189626100320503003843c1d2200c2e800b420075660000c0090104001c1481e421749140c06034041e10403d02c3c941158003845501490803162000788141507050b2800c00155268078480c000b600c3c00101c00d845000016000f05140034030360140b2a9034240b00e84030106454410120f402080044441c14014030040041d107070443e04030501e0034000d011070b9580720b07030003180142045900d4030001070310429000e9000400113040c004510400b80101c025184414201000030441490311481d54410365100b404012410029900180e1513406803011a0300400000f9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 929133084 1250 929131834 929131867
    0xc1202070b21070207030c0b070510240b090a0302041d120d06091416052206030c050315060c011d01020306011b030f1b150e0d18030b0408 61
    0xa1101040351000800c4600340042c07072001e81c0240680c002400360a03d146e40b48440c805aa11840380900004200300c414011306200c2720000d0321124204014040103c050401410343c5a00072040068541c80302017407440403003044404c2050018a40c1424901c0e650803c00034086454005194641a11017000198010040e214480d68a10041920f030a40040d11800701c600070341c0411400d600f0301d0240345030341410302c281c20742102d2100840d8805090418040c1d4007072040c100c0c1d0480740c00d04442c14503517003244410f01c00c2c20346031941d50038840242581400c0b5014003080d600780f015501080710540309403801134010144c80c004180082544051302c8243e0302d00721402540036155940000c200499580e01032000d185420a00c010f1140d45800b5071402452005000d4400e070a100755019802c1e6561141e0340680501640084200700000800e50414054401c6030817441c824803c8034261180c09014000445403049100c0a01c0d10881c55603d580d000180c0140017510401001c200c22446c4030000c04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 929134334 1250 929133084 929133097
    0x1d0606030a0b13030e1306030212120403170f120702070f080c0409061d060412050f0d0213030602030103060902040f110f0304082107080903190c05010e012903030702010c1202070b 79
    0x4c0005900c508d103005000709031a0b84c950a040540004561800ea0180c8406460a80c0d03046020008081501007107002a48181074175161410b401040a0103903541d852140742c428542c40d170903605401c2c0d4031040e0440d480003d000e14038413500100d0710702c469401c1c16480709048501541003c40d202c441e1440500c032200c80400903052940181c0b00b00800d011000e0f0450710a080c3c84c0c81e01d07a103044510090001706e03004002d421100e06800098040c09504414003050286411200c11996541d4a1030050010038107194220f00030b5040801c5a5100070003403059000081485080e180382c610f5090400034168001172007156011301c1440402c0404000d907601c04071404502d00c0d2142710b405c0a86c405000c042004085040d00c0d4020008248010944000e03007460340d40303500745440324454a241c01409882000c1c05801d02e03621380628003410f91400311075829002e0042e008030300b03400d03400c07001d050b200e1082c0300d00070b80494a800781000000f28484c8203801e40b81c0c1a8415148510b48941810b422a880a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 929135584 1250 929134334 929134369
    0x30c02250509060d0206030106360905060a05090106050a1806020c030f011a06030403021f0b0f041107080304080c07061808010e060a0e010f1d0606030a0b13030e 71
    0x861051003103081446420f03070030410882c2c03005084406039000500e184414050001041261780621803420805582407041742801c22215010040380c03440b40c000000f040c403c1000700c50400b8003244460a1011300401610707005421603d0580c00c00d00b0a031141e03400082050b041250100282101e684080400c1020342165030140c86d80c10f41160415103400c80410a521103a498005d1448091844014040380c0c580180d420359243d035180c0c03c050b8140400c1c03c458400300301140b400d00c0c00781405940310840000046a42c03012038503600701401b0444040b5010010302000030031007640442c01840c003566000c1d1060340480d00e485a140b03181824079842e548201e01240c025070348080050910440b580150550310000c2095441e51804c00f5500e41c4040d2140b00e8042c0c0da401248010302080d00036035030002c0301d030100740046464a155152a00f00c0500c52201501a885c041303911440c01040c51249182c104c4030b20003054840c905030303000700b000283c4200d003031014900450035a901d44200001904207075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 929136690 1106 929135584 929135653
    0x408120325050d02070b1b120a0e03071b050114032202030f010c0206040b1e071b020405130203150903180301200418090f03030c02 58
    0x26581030740c4046000241e03510520061b0800e03c0c0c02144d42060880901000000f2201c807030140c0900140a19001000b25241c1922900820420f803078a109591801c1d00c0f40d070784d203425200c03542c150300c3d041d0303130382c5d6a08222540e0420030404802040303400350340c41d51074250904940420856283d2000c0301c024131010055460400c810021140c24038003c000300400305002960722501154102c84940403c0c001922105040041201c9445861000d1965440380203007076a0502d00000c94200100ca056840b5005d0790307482c00b6040c02040000640300100c5842d0040c1414075211410200c44050315106001380c4801c0002243d5011501154492440306c2e40c40010b805001e54260040c180d8160801c400400c0e4141d000510490b50702101110040300c5006010b801c0d107103c03041c083c0c5510f40014118011034007940003c2e04a424610544e814803c85580e0481d0451014201c800034040 = true := by decide +kernel

theorem cover : BRFrame.Cov 928956834 929136690 := by
  have h0 := BRFrame.cov_init 928956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 928956834 ≤ n) (h2 : n < 929136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
