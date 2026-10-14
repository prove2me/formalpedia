-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0755
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:36:14.560987+00:00
-- url     : https://prove2.me/submissions/da4b6a29-9e20-4c4b-a4d2-b86fbb0c6e4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 135611510 ≤ n < 135791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 135612760 1250 135611510 135611513
    0xd08040e01030506011d0405060606092b14070807030305130519090e03040b071101020a05120703030b060711040b010905151b0c0102030d0504030c08030412030b01031109041d01090b04 81
    0x40f070506001c6c1c841100d030740782078031f084d54810740c40d4030740640600e009007000b0401107003075a20001c03030b60940d40b0940110104483c0114118600350900c4d1402d0f550141009061043c0c0c010100706082999140001054010b28603a4201c690368454054508001406040070401c0e944505500c1000400c0fa901e0120450070004c41e00203c07952413108486a030304c01c103c200b1110244038161025a900801525094084040145d0a119120000904c0340c0590701c1c07030320241d005501c082e01d11240207550070041004081c080c41043d210b07011018068100030013540e01945495045140e90342018901000c03034684d0b41c0c010a41c0b50403072071410b03807680d0404144030580c011a07001c0301c010104d00000030b2405409440c00030303441e0320481640c5000941c44030000780505014202046002c0d0b030022206a1700c0ca401d0405040c0c1c0d51862114200282c10729042005661290140301c1041908807002072504610404210060121a0f0140c61391340f030100c1089240700080c4134040342540070b0a000c01c1c061806 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 135614010 1250 135612760 135612779
    0xc1c0e100e030405010e060d020f031815060108010b0c1c0302071106040b070b0408070203060c03010e13050607050a0c0203030f0c06010b07170711091503070f03110d08040e0103050601 81
    0x2042403032101c41d0320034030042115a074880c4021076080d4064442c5030741d400241102c4000380c0726042c96082d68580000c140644001100d441101506101e010380c0c101d10000040703444802002c1e01d4490010b0310800050020441f60b00091a030f01c0b40000c01c0302c200341315041205a40c01d04e500024400701e5808220601800119103455600c240100c4034145014200f00c04404240503048018003074460404c006010040e02800302e56460790001d0031691b181c60241e041d0b04066100b4003074010000000c0001c5040041000103000c007103503115014200c03075034600074116a1a003040c1481000c210303080c010500540c03014401081c01c6590407059a40d1130280c001078601c0c006040e0311111481c3c1c0100b10400100d8400300b9803240e280e400a41141c0d4803509130820740d41d9490140041603100b0041c07810700c8004084040c000354611019000d496820b640d80707400314410b060300c4c8800307051ba4020a095000c1c628108040103021440751445505003a190f103002d541b0b280091304119590b500c04001400b49220703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 135615260 1250 135614010 135614021
    0x7021206060307090203060a0915030615030204060608061518090108100501080d0c030c03032403140d05090f19090e011514010e0120030405130c02060c1c0e10 70
    0x2100506619501f0a0004a00f0359045480743c1041196aa202d4580b181c41d0000708000564002c03c0501502e904100810741e009900c0c442244100d141010005850b0300030406184510402403494415102200c420200c0391711120850121a0701a0b6200c0075076590302c00d61174040e01498004001110340c6140704001c6075410b811440d007a5010311040002c0603031020603503a445505180084000c02203107419809001c40050603c1c0d209114122490484034050280b005c5a005500c1080c490101c2c0d880551196503000828000500030041c2d200c060909030f038441403800c806001e481d6010a5050800c582d243c0356000540b4458540700000e1030b660302409814036500ca2407031681ea03481d281031098a05244c9100105051000c8001101010781c010710540c00f101c40c9007010910000042400c0c69145c3d4010f001d04ca10501603030244070360f52318031403117550741400c150780050040391202000655590465244082c0314000c134a50780020121a00070061b00c102c0c038100030100d143e02010214190741 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 135616510 1250 135615260 135615269
    0x10608010e0709020a030b0928020a0c021c0501050f01030b060a06050a030c03110c160906050303070320030a0806090f0c0d0b181611010608100f0207021206060307 72
    0x303040141c425a074400c0400c00200300c40500c0e80040c0c0c0c3e8400f00c10250003410382d404c00c0d83d510091b080208100d01565695800f401c10785680001e00c51b6030580b94a9040380596048400052404c91024005003000d400c2015200d6240c541c0c0c5010300c4050741e410342980c604490103240c03000c07080010401c1154840e40960003000480c0c0c4030300110306202000340300d8028081c0020415441e2a1240302c500d001e03500c000840044540b00300c6d501c8c09160021a542d8001c0240c00c0c4241480e8100054035400e50700c10035040c2c50f0020007662a2007550f480031103000c41c02180c451080c07503038a00301c403a4800c81040148000e01c1f49403074004c03da151a408019a501c001410300d205140b0380030402002c030080c6c0040b03c60b40f0f400d2442c00a0400d215102140c140f054020210700740035005400e102c603440041c45404c3d5003040d00c4d83d40c0c10740002c0400703501c3e00740c80c1144100c41103030340190403484d00d40e049074004a080e54201d140040c102071147e00000c0c41505a00b00350592034110105121460400b40302c0e010242 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 135617760 1250 135616510 135616513
    0xa020712080919060e04020d18050106080c010e0f101403040501090209090a05070303110a050f01060e06010c1203201219091a360d0c030e240403080903010608 70
    0x80e1130b0444c064055039055002601c942c2d800500004010074541c4402540c04185010202c602d900780742c958024156406001800c0c851035289000725031180c003481c280401d0103450440b45095040c00c0c40381c1c185c84c4a064405004806505000108801019501c280c0c00f500020940000c18014021201f2003d041c40c3c510350828003003a00441c01c0000d2080469600d440c0020129039043c015600301044803000a1a40c00b40804150403d041500718100b070b0b81184003448142c0c1c9600c401528180110200144880da41c1404c15515901030340c41508524600100c05d607200c1030f41711840b0169070040c000400d07000d41000c18009141858802d009100c50029020448052a0b1b04d074007000da6171042401c0b030100d40107400101100466070b140e1401c03002c201101490080a400e64440c1c1c01c20702040513603207200b01342040840910542c1e9000c90190507403948400840c409050000075980d910030340e0101114065031003100205800280021070190410750740b98070112040609481d0b40d0313480503145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 135619010 1250 135617760 135617809
    0x50406060c0b09120a1101060b0304030207060e010e1f0f1409041d0102030103050d0f0c0314030417030903271f09050406060f1205010b0406050a0207120809 69
    0x4181c0000c0c803014803603003100e40d0703103502d540b200b0240d4079210381400b09a0444001040840b45260000000c24500704c205c0c0003484030945038164912302d13020888020b00146c1c0101003c0061600514000b844014107150001c6540c402e500490002c9500d103000c2d040e20b00c1180c40d0311092640c4184200d80910251401c1078114080500d1080e050051030b05003441940d0728204110141101c3c1c0000000070f124200a40d100d60350303414a243c4841f07142d103051000c52402d00c0d2a00101341318000c550000fa03416242e015001c04904410000343d08020320843e00c5400f810b24514001d08900040d5100340d01c480011079441c030000d00c4c5002040d03c1406010b00c024618500c40f01c4030f594403000081c400c1402201d4219442506030212080d00e080d80c401904145070480c00300301c00e54003151800d40f02c00c0d1602d800b0360030040400c41004440c1e0911400d255143c0c14481482401d100d0f40042080305003a02c1101c42e980e403580068982c60420180890791090b00043c110399905096500c1c4a211000e03501c501035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 135620260 1250 135619010 135619019
    0xa0e0706120f0902041b02120f0a03090807060905070f0b0c1c1209050a03080c12070e0406031a0a1103010308030a18050d1805030a0c030f080408190606050406 70
    0x88151050400d03403864442c910604a660075034040d04503650010802d0100005000249000e0740224a1030001405085040084800c2080403210385444031116035103001c0c1e25180490050028040845006a00304035442c00304481e0b004d00048a405007002d401364621707041c4241520043c41e030140b0300b100700c10b0007120300601000ca4080c580d40708908100819880d58503084401d17510030000300c0d89940c03034600250140240019880d4809200740c68400303098450000d4103201e409028411002e621140d0005105103102d1000040d80c10005040441c0164690343c2e080ca0100b000e8040482d0140e00d181003000c030101c113014003495010000041071455055440d1101c0501c13000b8041d100041e1134603060022a240941c66900d404d4100040d40c40840d0001c0d40108540c400c20110001418100e5022800386804596018070551203070002c051949140e98848001c070f1141c100781c1d440d250510000801d0b100502c11401c1001c42e0004403450400c0625144040b41ca103600a01e0050703290001c10300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 135621510 1250 135620260 135620267
    0x21c0c020a0b0103060e0307120306031a19110f04080a0c240807051902030304030e0901080c04110405100503010e070305070801061101060503010f0621050c010f11060f0a0e0706 78
    0x60641760801d4001c18820303100c04099146205c1d40600400c0d1040150500d007482d42e1642c8010243c1e44a21144e044545909950100303082090b114200344030011410740f451015142c0c80701a4169501c200c031400c100b0780e090403a510350010342c048030140d044164001d0030024200764980141620b010404241d03600101840b080200e0482184144400c1c400480d40c0b041c09101596003203c0c44600e0704800b00d0720f1080c000c1d200d4000791070840116205646050f02881c2c0309542c01d060361903050051014942801c2008050441c040001801c0c0c1401c00010443e0384031400b0069a0200300d4071400da913949040c0401d0240350300200901c00b01440d12043c400e02540c4540c459045616610304000394080700d5082c2801084998400c940c19817900d11ba824400c40307903410500448010310800c026030034030b0111071740b02003000d000f0081c001d410100c0100c000e90300440341c0f40300c11b01c01450550384140001c01740300d207001400c4d24035400302c42c503c0e0200200c0c0081400b84a650818034805842d42601c0d140d40034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 135622760 1250 135621510 135621533
    0xa050106090e1c1101050c0a0806030f190303020f030708040210030b01020601030b040228060e04060308121f060c060501060c0309051003020f030a02130803120a0203100306021c0c020a 81
    0x203100940b4284403521285128690901341d500042c03001b04001d080c860030811345684410040c00100340307001c0009800c0e00d070200341c2d160059103075409401281402d0744080304010b116030b001c4080c59400c3c441c8070f001808c0034001d941309403455100d41a0b04e04041c0100803202c40f1a0a4900400d803d04941c0c040d2a41d001c141139044a91240d20072903039451320b10004800c01d03411307252803041c40f030a1f585180d039140308016103d04a5080740c0f90100c045056800307003c00c0d81e595010103042842e040004030b0f80303641072488940e44804085d901034401c4160b44504680d241c055400b4070001034101d941c4400f0711440e80f04050041080d030510031010395650740c000d02500d41c4d6119440c40742310700a13000441c0358040c1d0100d40c001d03220035401030303035a10b02211000000d42150003e10729608030b000011500060000440308014081c802415407079403070320312038000380d80300900040343c501d686500040017900c58000b90840305c98031000f416140c120051180b003140c60345400442158480c030000c07004540c500000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 135624010 1250 135622760 135622783
    0x10e040503042102060d0b01110102180609040908070605060a090501060e010c0507080a0506040b070302161704090212150901121103070e0f0f060301050408040e04050c0603090a050106090e 83
    0xa00020150030f402c0b1010551450019400200025a41c60020745a80c44501940004d80352a201d1403580f4030714034204d005000031900d030303e10701c804403e01e41d1030300e60054140320740000d2001c508001a82d907000c40b00e400c2002c2c116400794980c018071007581341454000c0c01900b1210010800c139071420400400f51005403560a060003400100c02007072007010b01c0900040c141c182e007110340c242d02c2441c000b941c41108490940741c5110f00d0021a48041c07190084450107414a590494510401d48852082000a4040050454040200050b440a84c0c0041c0020200381c00c2c03400030320f191000e48170074100c6410356401d110b81070178030050281200c5a055181025049035007102e2007500c0d400860f00e0001a034001c801050307006810444c4415908481c1c074482d1429030400c070f00070340300c00080c075003a40c0003607800408004c070506c000c0c042042040401588280031700101c070102c400510200d000340e801a241c10b281368020014400034010240035502c0180704000d010460000e8400d002034440d10703505032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 135625260 1250 135624010 135624029
    0xf06010e0114010c06021605030a020309180f0402060307110706090302010f0e011d030a0b0103050a051014040209190501060201020c2109150c010203092b09030305030709030804090212010e04050304 87
    0x7d2440100c020350308601c10040d80306003102da4031061703400040e580b9007244030450310070440703c81025644080000c182c2d005c2c0400c21400701d0503441d030790308011960f00010420350030803000c444041c0310031800f000b0000040181d03444003480c0500711b00005202051449000043c01501c2191281d280d9001c10340c01404108c2e41c00080d10803e600c400a410881111130142101d41e03010004414040040748400595109208840803201c000302110144e42c44009607170b1078880c1c5000000c0141c00c00c6c414140e48424940350101181c0c030107040640807144282c0064006070750201d10082001000c02031129880703191401546107447c0c20201a404d8418509181d01680075201c01d8400713102140165001d440704840255142e203040c003513017030b610203444018010001085966003075000040700100044480b031381d11003405905540703060701c840d0b002078505010840300100c00408507104034040c00c040d10b0750f07003009030341c5a0320070381d0958000d14180c000c40c002c1c3c2c1d902c40511000074000021641110340810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 135626510 1250 135625260 135625267
    0x7030801090f0b0301050a022d030a020a091e0816050307090c0c02090a140c09090711070f030b010e06060a0207030312060f1401080f0712110c0f06010e0114010c0602 73
    0x203074890054003100c3c944071341644c00c01041c050704003604c5d00030309400147c0c46007681c41064110700081403800e90362181d9031300f0309040000c0307120790740702d41c009190017000e03030a04120a0340d4844800c00035508041c054106680e01d0b040074030040d90b0a119181002e550b8a030000c441c40d0508000a46890b030f40c0c810050b40d9940c480d0010135280c01100321410554004280726001d1818450135030142c0b540d00c650346c41a20114000441c0300d03038010196884800040c0600d9a60b5956040c19100c403c940002e211082c0702d0650f001a40001a003540c002541c420074121006501d03264040c0740003003010381082d104150910135110815400100175085a41600d0142c955044240182e4020000e54028812050540c0700200c1d1100140b46020701e400002e90b80d0840a6841103503298000300c041d10858001032114022810724111600140d881e0185d0480d01807402c0c0c4603c041034036080030041c055915800c002c0c01045a8140820300c1401410003048000990018000082116610100040200f80d020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 135627760 1250 135626510 135626531
    0x80c010804150c08071803030c03180803040b120a1413060216060219020d0e0402180315010807080a0201050a0f021906020d0f09020a05010c03110102030f040b07050703080109 77
    0x114030325114034140c900c04000070000c1e0007000b4a40038040740d42030041b541c1e8081c0782c003203081da1251140840b90540d0b1980c80f0a01c281d42c0c100c0f89801d03001401040a5030001000c04d0064041c001000181003600c0780550350201c1001e400c081d07120041494000501e0b000e6142c0103e04d980c001c80b40d2013081002c8100d80c3c00c083d482c0000007801106865810070ba501c0d65603108000031503000301005100d52003a24001040844101c0e45e4902c0c9030311f0b560004030200410740040c10b00f600605039092050407050800e4070746002007840c0185881c5441d410080c0e200040080480a002103805001940042c0140b5101d41e000a0807500c45c08000b803040003a141442819a4820b01c03420485070440010751012500c542001000b80d0800e646a031b000c1854204000d40300030140c4101c20003568043c0c6103902070b500e01001590704600c0c10000341d041c006900c25004c1458000e1000390720580741a1042c86036800c103800c02002960008002c8028084100003090220341c010414504481d094100462905000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 135629010 1250 135627760 135627773
    0x403030b1f08010e3304020409090b01090617060601200a0c03050606120c090c130f06080c0909040b0c040902040f080d0c0305070602030a090c081b04020301080c010804 74
    0xc411144094007001d100950701603900240c1c180c1240d01e01c6140003565200d070b00b600c2c400b07402c0e0f84071720b401c0301d80a904c0045040740e071a80706074080303000060006090507078483d044801c1d54100e8004842c01d021441c014000180c26110305c02c05451003140b00004542141d41040d5a1580070382070a050218040e109201211406005070074a10360b501618542c44661521140c0282580011203145c00744000003103813400d0805c429150019000d0081c510f12041e00d0074440709200203080c1c02201042088018141c03443c07003521900801418020355071261403c040240714501c040e19024071210304000d003481903035a00d0b11040d0410b81101c400302c81611070840490062086502c0201001d0001c10300040000d101c222035411030f041c01c1e045c1d40031054241c004446441004c400100070540603c00390010503c0c5a001d16400a444c47c80002c0420082d220b1800e03c01c6207912403005070b40310f110700000314070070301c800c0c8803440c0307001cad2019419035040c808516264004d00c44024100b15641c0b0004050004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 135630260 1250 135629010 135629029
    0x6080102070204180b0106050717120907050f0307060c051c110d020316061d060c180a08030a140c03070c08010b010804020f1002010f0f0b090f040819050909070302180306040203060403030b 83
    0x5903a4242e55135800140d5000030482f17402c440c0f101c5240508400080d580c14549407130b02071258014003030603800303040010a41d0a10a41e2509175010310602e00b401112200491a1515030807035900c8614503080c2ca100228034101810714020115042402002c5a184000011075030341a40890b02207000100126400b4602090011190860bc02c01060019012214009142c2c901040d810410000620400d112858403070f4820b1003c55441004102641030cc5098006946568484401d2a01989a801c0d5155400094051301c03002c0c02d40c04100042142407140540c180d800b07003000c06071403801d5000a0540004103100c0b900404454510a00891003940442d10b00600307050108460b1032418a40c6000708540c48041d4010911607020401c142c1444441070310484c3c1c0600f5051510448150071341c1c090450b80d4040041c04018401500c0d56606d03002900c0c80f568060764011b8446d078103540b010042d4180ea0750240e0003900288140130240e2004540c2c81e034069054203020138901d8010703011880099 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 135631510 1250 135630260 135630293
    0xc0f0e06071a0105031e0a02040b01020703170307030c0c020d0b0601090302040609050406050c0c1b0109050909011a0607170a090506040308040501080a1802010f0306080106080102070204180b01060507 88
    0x112401c2c0c500c4032002d420384905a810039000c4a071044800840d4103008800312001000301e600c58002200145010380000000343e0041c415038072240c0e6a035540034414414682000440c44003c0100070300d0691520441001001c5840d00d4401560301c0d801003440f5030940040503002e2410000003d44c81e0340940b80358001103070b0142042203250f0b542d09440b0b005107402e650860f4210b041070b0105003943c002900360703401e00400c030000d80010a543d0b00c1c1c0c007a02c0d00440c6c02c09410700948080008040e40d03110411441041d40b14008075000440003941125074142074071081c0f18150605c4003002181507540f250005071691814580d9801c00ca400540380c00c61135a2001d0742c00301001a02204003c21503002e00200c803402e8030354038020f0f105d41c421002a03503241003400e4807507030b12060f00700059072042c60b600c1c0d491310560600044103034503590300c01c1c02d481590300004120307900022910110b091a00c11aa400d440800c5010081000c2ea44c40c0b01c0000010300c50401040340104440040c012040700400070038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 135632760 1250 135631510 135631523
    0xc0d030210050705040e1918030507020406081f0b0402090a08070e070503010308070303020919090c080f01031101050c100507120b0301152105010c08190c0f0e0607 72
    0x4491500a41c0d0301d111040740c110040c02e08021891103030080c000d0301d041d101074000c1101142e5070311091404005d9424040311059031948901c18803a41c0200301d104406009035100c1c0c2d540d6881d8010300054a141da030140349142e03c2a42d25080192020302412b80c98480540085002024100001c0290081707207811548524202400602c1403000500e4400310380b401001b40e4038a0307035905001e036040e01091001515881c02002000b0000c2e10039401000382705030040c01d000c1e01c2240d2811204140010f9005415600d540d80c1d0040c5190340c00c2a0a15402000406000840c0d07041d0b42d105559001c03001c40690500c0b1000c0740c1344440c10000e115240e0345145000040140303151a1400401d0645269110030170716152400380d00c02401c041c00340c66071000c20146072240440c54040800340c1c0800c40c81811035041605880c00001030b00a0159007800390440e51460703040c3c18031b0800d9034105420b00c041c82c200070386803070400301265400c0703451220070720000e09084c131540d40c01a000c612544255130307004005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 135634010 1250 135632760 135632779
    0x810020d0902120a120806010e060a02010207061d15191104090e03180616030f050906030415050907060903080a03060b0c0a0c0603020f04030204050901020408030a050a0f1d0d050c 79
    0x405000280407004a402100c60085c1c14070100360580341602c094072101e00103040b035646120a807c0000040010080344d1000500d800c0031a10340d20201c03203420b68400300e0000d9140600314034007001c00400c05400030020480420703040001c1c2d4169403018441c1ca502c1507603290800744107440c1d640800c2e1001800300c1d40c41400741c00124002940c0b01e41c4002c51000e0200c03000c0300000920f00303224095507130040c0e8641c1142200c201c244c0303099803114001440c1c901000010841a005030711800c010311300580c403450300c66114502c90300c141e4080d110010240c00082e80a40410045030354004401422a80c1114103540d4a4918440c203d010300b02c50b03009029900d00006404c00b800200064000d2030340c1c01000303c08905900c881d0210141e00c40d8038460202d40806010038000b528180d0311554200c1d1003000018685640c8412142c00d6400050390400030400104181202941003078980f002803005142001400306411442001c000d0900c1c109809504110074480c10003c081150302c452071b60081c0711039035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 135635260 1250 135634010 135634039
    0x4050c041d010e010608040b0a0e0705031006080705150a030c0e09041a09030c07061d0325080a020901030816020901140a0b0307051603033803070810020d0902 70
    0x407903142807090706203d01420b0000154507100750001d60080c6e03071140d80542c2d6525115160b0700648005100b400950242210000312076408000307103d003055001901040c0f042c6040401400c15560354081ca004c2e10041d402d041000711000201c825500e15030030001750000c00118216020740c0d0f210162a00074542c181400207100d8002010460f58174107400d010035950b540039666440340503400c1118100c1c0e10480c03090020754000c03c091840380400701e0081c128410f074840024500f4450541c25070040c40c180032181c00a000c20000100508541c0d0010001c070310590740031030840001440043c5c251200419510b20301005d00c510701a04a800920040c01548c403000e0b480340008036a40c41a200e40e141e0180020320503a1036040c5ca114a0494842030b042c071aa40c020034003002083c1600b1420981c0d24191005040300802c1d4500620a101c1e205d4410030390200800151400840c441c144290b00045c0100200a400035646038000c903084800743c0c0351446041c02901826071010025800100241c0c40071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 135636510 1250 135635260 135635309
    0x1002030a050f061005041415030f16050408070e040f020907032403110d14010608031801020312070513050301090602090103050615041e0e0910050105010201061404050c04 75
    0x82c000c422040c02c0056586849003004640340f80c40c40001d01284080c8030800039002046540364446070040c190111940c1039801085481d442100c00360ba03101d00e103c040c400c060003000d6200401c2c1c15103082c0b00c0d1405007005000d556a02280c4601c501001d030381d0000804000d01307000301511455001c6c1031180d03d81030405010300600011170803401c801020302100c0c0154101c140300c03a811070360040440c0c1d95a40c180300910054440000c41070340c00031041c041c6d10750031000c241305d484010020702d4080d54486a101d4a818201c811440f01740b0b046500510803100054103a40c856900000b4500344181d07580b0401c14100d0204031541c1c04103134036501c1c2103640d80500c80c45800511001c03909aa0030821950740d0020000079000e4400680c1030018280801e002d003907082c03095898640076800240f940c1540c0d8003210314948004803140c4d890340d0009007000700201350034003401d400f41809000074050300c7d040100000c4c006280c19055842692154085107880172484c0072240903003601d80141c1c1c0400c10b41e0b842076 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 135637760 1250 135636510 135636521
    0xc050f0601060219020d1e0b010906150815010f030b030d03150e09070909030203160f0201080c0f070201121116050f0606090403030c031410061106070915021002030a 73
    0x700058015000300710812196500c1c920021356004001d142c040e02203440f0085c052150b4400107121b07000340707500000415188150342d40206541c0038081080ba04201d11040c00011840184007800a010140545c1c15502908011000020302e071100d036401e442001240038100c007558468050040a007001903903507164100070041c01007400010030301683c82c45010944141100c41031401e401640b403d1151108a0f0484542e144c042d20440307003801d10b0010096040302180c1c1c8100c895000d8040380303c0c1103582059500303900403404030b25181030107819a06000740d4421110000d0400c0346800e500c0d031021016900155044400465a6403144040e07040300040640c0b82c00c0a4541d0311071856045035484c40001d20780d02c1004040d00411180d1a15503040d0003070410400d032030301816120200455090301105050f0b1060107001048443d851419601400c0740c20011590303c0780d904031600304040302d030b00402d410040723411206214010b02000c802c1203042400902d1042841c07030000043c010309544a4000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 135639010 1250 135637760 135637769
    0x1a0a090e0105010b0a08041b2303061e01050d0311070605030415090c0e0618070509180f010e04031107031101030b060a1d1c0503030421120c0c050f0601 67
    0x8101d82d903280c4d060a0000d010b03e64090000410306000580010001782100c0302089007025500d044644034080e480003108101c0340b28040c12284600c0541070701c2c040080d241c010842500c0c1031303000007518004103441581409100c0c050402e410444040500c038048645141300c814069825107500c84a00400591080d40d06441c41007004540400c0d0b000144254061a50301c80780344441070345405403034805802c0090407503600504081008200300d04410446201d07802640e41e0a6840b0b0f05d407030800165130f841724078808038081003004025000102202082c10350710f0071100702e48995103601c0c00711001f09124003108680c0c02201e07400403c02c1200391551244800c241ca003400080c0d401d0017030210b03a0003600c0c40c610004d01c4d9003034040c1381806001c1d6203040c10303000070b0019001c0d02c95141c001c006d41d11122004503401d500010400041c0114044031000d0340d41d560f400340440c403540c40401000d40381d508240c00c01c415500c0400c080541e00851030031188940c8401501c52079848008801d0f1525000d114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 135640260 1250 135639010 135639013
    0xd0606060e031501151202030f0106090f060c060b03070f140a0e060108160201270b06040603020d060203060d0f081309060609090509030d110415180302041a0a090e 72
    0x1146286030210702c060f01c5040001034240c6a0b8600111a6921010805807209201c2200b003124411000380c00210701c20100d5032040391565240280041020301540d001900c90101da1105100082d4000444030190f50406404078000c4000c034002400c0849035406000e0494641c1b50005401010a4040068030421074070070502c26a180f80ea1290907008813412400110701c48001504002034140316804181c1d68400042d2024a00081e0084803410307852030281000d02d95042d100f08120320303001c9030740080207650500900780303160702080c840d5040c0840106980e401000280040c0c4440000300a039980240d074624001800d42416402e60b0b0080c07040d031012010308a00072503800400c0c0240c41c21940b280d038520016a1030141d280c1d000300400341640015001c204880c21241d0200c3c05003100008189040d03a540314a40084003e17030120500e202e005010b03889205420740304880d28507030300b1640c0654002c20509507400c0d10f01407929154000960206501101060782c0e8038660040f00520306110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 135641510 1250 135640260 135640277
    0x70509042a03051c0e0918030f070611040302010f111204090b090f0103050304230909150906070806040e01021b010507021234080c100507030b0d0b0705090d060606 72
    0xc500384d4004c00c150780444046004000e00c86486d08146d00b1156001d48107100b466060070303040107690704583c0b20080707100100102050000601c94544100b403c2000340c0c145007403034989160b002821300c0e0a281000003d02c80c039540710350700602061044a4402e401c58110980e656107800715100100103500c044d6008254640c0001c80c0040d0b162801416613070001d0042d4140740c60328080345110540c2e8600c1d030b0740c5e1309000340c111344068548008040c020700080001d0071100100d041035404000c80200307552115403241d401d0101d46508038000301c1c0c02c60410707103000c0b4003a0181100d60f40640308050403211f6070000000c07104041c0006510480c0142d50541c20745800d00b0058007036003070324005c80440b07000c88030703507035002003401d000100c040600c0d100881015a615002512035554940000c21280e40719000b1404c06410560382e07202e520707482202424100401400280458017030189501c005200711185004a09503901072400c0c1c403160803008051030f50348143c0740741020241c0b80a10070a00030400d500f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 135642760 1250 135641510 135641533
    0x303031a0d020f031516081612020d020408060406060f0602010e03030c0a0c020613030605061509090910110d060905130b040c0b1206010206060a08070509042a0305 72
    0x150121203400800624181e440881034003001100440442e0702030381441501264250409805500340c403d14294010002e500300c001e1020349110001405907060151030320b00e21034030a4001c06020100e4205040040e15a1649614000248650340010113036110b182c042000700038840d04000d050b40e10101179081c00c10350b5400160b0030f031121050a0a2140c00502c006142003900320083d0864404601c1c240d409201e20f078000c0303807840c0d02c480d400021941c05c2c11024024080b0600644c2e030031840550355007804565240e0314580340c1c0128a0f00314884c40a10005c074500c0701b410001800110040a81005000181000f0541c9a40f0100200080c1070800d0400111140913209180c8a032071181a1000e0381403940c1e4070402c0c1e1000041c8210b403030201c051004120809510302400d4408a101d061400340c1c01c0150002e0b02d030000040a0303c0c481c4500a000303000503c0082054800c030340e410783d50f40441d0744981c5028001030100c038091401d480c1c02c402280420344401e1130703940304903800f80301605d1003002d41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 135644010 1250 135642760 135642791
    0xb06030601020d0804021f080a1b0503070f121104050109050402130509042a050414012907050d02010501061209020a12030216060f11030c071e0e0f01030303 69
    0x854a907400750300710403a0304209a0040d4140c5511520042c40400c0343d9042c88585141e101100f80c000300050b880c0010000009a5440b5000301c04001d034a410603020340c42c503002041c510004040b10100281e8100c003092050261441000c02ea1070b0300014000b01c121110701004c29041442030900260703840300e0029040c24548211403500c1d2006a15840050902c1d09111603024090821a813540e0500703a1010402e43c56001900c032444030f21100c1d44068941030820041e100e0b00c5c40d8003910326000800400040712802c11100300041d42d489101804076621031100c006025000000c0d105014091501689680c10f600c054113881c0242c940711b108074003928101e81103800c000d1009400001d00c2009200c0c0000a0204031081442481106c03186144c0035042c01421207182d01c41000f02c2c410140c95000e01d6040b50b00103101080e0000210700704619800e44c41c2d0340345120310a81003036420040d00a160500b425101c4805800c00151800040c1000079007410b00ba4003d120642c006403411050100d580c0700b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 135645260 1250 135644010 135644017
    0x2010b0916030609020f0403060207031e0309020a14030c0405070c0c0f030b2802030a02040513090b0109150317040b0307020f0601050d0302150c0d1a0f01020a0506180102040e090a060b06 82
    0x2044401b150a0900f160355550007548a1441601032001204110071240d9490074a94002c1280d5500030500f20302038410302c441540c2c0c81c0c0004010030942d13800320409450000300428000c00440c0c01180c15251400c003030303500122601001e40165a11030700443c05c580d0980d81d81041380e120780700d41081544c1c0c000d10801b13042e02e02d990003040c180f29001c1001c0c40381519000755410034030000c00107280c03699440002d04241c920138104801d06840d2450b0406001002c2030590040016a1092204020b18400d14a081040e404020816808080024080100c41040c0c802904800003140c0c2d036400c0941011f03655040c005507406062056000210b803604141c5400d03030000b03926400030801d03400c489030a003161490083c6585404d50040c0440c041c0c1c2c0d1094002c40764550f0069401041c070f409041c052001c4102500041819544088510700005900040655211480410041c500000d05104501902c150341c03001c012142c03d4024400300d003a0106400000c2481142d0810203001d0070414000ca901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 135646510 1250 135645260 135645277
    0x90f090319051b0f06160905090903040905041a060d030f0818010f0b01080a0b09060d031b031e08010f120f060609020909010b07020306040f0302010b091603060902 72
    0x400c103114180350700d16044003540204500d4185a41082480c4007824440048007030014040e5201200d81c00b102c03d01400305070342218440b1000c0184090300c08020742401107a02c40c50b4042c0400c00700056010200b442914040c00728104280000d003000e0070005c00d00024000c2d1406030380090008600c1500d0030244601281c3c1e415207811158621201003a10010001401218449114030544000f5202885a002c05140882c00000c0480a41d00010328400c401400000c0640c40c1040342c2c20142c1d20120704c0b981c042c2b400c41c0c074581454070b1380c0f800701e030f50751070003000c1e42d0321801c003120240205500018942c041a01e812022100d154481100b02c1d4031400031300c584494003a80700003d104448281500c202602e003e551244250015980c440044421076070111500c03c2d130205240d0114640252064010018942260308008054001946510003d4801002803a03154609001c040c007c3d009200c1c900d100400018407450301d5508880380c1d40a5370428000a89000c3c004a0304c9441c134400d4801a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 135647760 1250 135646510 135646513
    0xf030108390103090221011401120b0c07080c07030b06010305191802030703060606080c040f06050304060b030a11030c0d031b08070506240405011203031d0a050c090f09 74
    0x40e0a20300e0040108003038808200c2c1056203d107041d102584840407100702600070401600304000c1c4512406085941d8500440010821400100030390070300403240b45280c540203089402d9944581c006050944508140107080303810118005411090104445c4122801030300d04080554689004608546048072200f544101da640504042e00301c40c1d1021103140704030075084602c2c0704140c0002e0b1618030580e00444100742c41d01802e00c68254050485500141010085828203061128001803010580154802c01101200140c240300c215080301d050f04c10302905541d940142e9090440c0c41c01d9202001c00c2c080e1041c41c80b03140362030415451210f0b2907505551485c0c00084003010100242c046402e007607920384014003001000c80d40078060355001d030003250361551007010070340c408210148903a00312351311035407422004120040e0b01c450040700301541361500080c01a1440741e2100700c120807442005c1c003481030341d032070004106e40054203104603e001c403031b4041c0d40d55500e001c0f41d0508100b161115100e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 135649010 1250 135647760 135647833
    0x60b040e040f03020c150c1905033103031d060c0304060c06020c030307111002040b220e130b090304061b0f0b070804031d1c0809060f030108 62
    0x45a9051001050b01d80300b403050307407000791005002610300f050b440394000e002c00c0c0001c1c0301417100808201c80d20320000b42c001c0c460701d007522680f50141c6a00401c0303140780b6040e0000c1c0902107041403210f460440400c803030f40c4020b500c50b140d00b001030070700c01ca003004a000c1c0045906194041d00e0120f05a540700000036005618050038580308507110300300c4070780032946683c0034082c400c5010b03014000303940f02e100c203695151046161003004528203002494000b403503503c1000701f17014859112040350b00e01c1c0c1180c200048403115241032040c203070080e5448924100040c006111411541d0110480d000e8000c5141c13040e5600e07855105616031140e0320482008c90039890055111519840d422280e16006192403801c04071151150010200c00300c540c5000580514108001c058020365591144800090b40855502c13880000c00c0412208411640242d402e20309210100310a6008640f401c50014001c10f4450203841c6d039201250b0802c0c081c1c103086010b0302007440ca207041f0340003100c5040040329154940 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 135650260 1250 135649010 135649013
    0x50a0206102603090409120f030e03030106032a080702010f02040e1317071110030c0206040b090f16030c05010c0b04021509370308030115180b0c01060b040e04 70
    0x18403486141c584842c002400a044c59594500c101e004031400f81861202d20481c0c024001d04c400f000d8440036040c5854071402c0e0401880000640c2d06580f43c0d824006058000c0c1841c0e80403039085422020b410001039410700040c6036000742914006d103440d400900458250008110a07401507019100e00e485c0310724001110001450441d040c6d96004001031150200d0384030758200f041d406400c09880010303000716001001e0829843c0144000c4440c6020410b0124a4100035200d04002c0c0c0058030400002d80030074440801442407140b28140030303085036550010480100001005884142d07031514034468001103039401044030401d4258040754030201a540e80d800c20403214111046202d081c00705002200240d240d0707084803a0042301800040064041040d0b5141c4080082d200900b2082c2c050f840800014001c442901d040d19002200f144600400840841d00500c0314684401d8502082c040041c40c0741c0240d00070002094080000c0c81482e03100d400090861041e441070703504040b103401c0040c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 135651510 1250 135650260 135650309
    0xa0b1302030a110a08030a050405030705010908060a0902040216030e0f04060f0603051005060711040b030f1b1f0809010609060b090f03070e15090f130f030e060307050a020610 77
    0xc41401000342151002071700c850005295403c1044810041200060f0601007450304100f1000244001d1900000c0541483c44281e2a880301a000c2c2c1480c54131040a0021950f40e9015545d0003a0030300019600d107039490400500403818002d04030b0182c0941090043c50341414000c02d820307500071050b510907061510324200c0c001c20005002032010706d07040320701242d26646d0780700800005002d40703441084003047e40c08200407141d031003240a00c00c0e0f01c035145082c61004003084505010203404bc00e200c1603408600840c242080100c0d41090f410b0f514044c8404103a0440780e018042c584030002007004540310300400080322a02d009111a2100c103000c095000d103450031283e416007c029098070951580c490009179208410b580203c1a40c101e5142458070f4140003059550081903030090080d01d040621060740c142c56011000f5260001078110384041c0740c0074403598501c8620103030641e40d8134a080030009210b81c001321164401406402d000c90045002c070b1052105540c02c9241030501c95540e669404c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 135652760 1250 135651510 135651533
    0xf09160504030605010b0c1c02060105010e010309020a082104290c070603061403030304020f01050f120f0f090c030c120f060103050106030c0807121203090605090a0b1302030a 77
    0x21410000208000b00004a040c0143d90080940c90b03a07450711a400f1180c0c0310304020b1407050203031110b41e07a0008494110b60015038a4111002804e00c0c0a81201c1035004070094651014080d4000c110f2120018420500240400032030103410a03214650000c814000c070948182d00c035103501c4905c0c0c90140b030b401415813910342c90190900004e00e481e00c0c140c00300c601c0c10000d0503401480840d0f540e060801902c15030401e4000740c004100c02860bd507107010760004000d07400c40c051450410801051024883c00c03124120345140c0f0524040705001e2030140d00300c00d42000111352403a0024000303404a102c0e240001903070f6290740002000b402003044488203000703460b440d8480d42843c611902e03204c03040340c12003480014042c2d4090340c00451b00c10300750300f0072801c2e00c0003d901c03031940c42e403001c070040100203010b10b074651019074005940341c450044840e0032000340c0030021001c0c02003403400303090003e541c0c400070720030b620180320312130710321181d560606040c2052074611400394250f045441401c0c006100207800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 135654010 1250 135652760 135652801
    0x160525050913050a03080f06030d120f0b120610050a031e08040f24051c240b12060307060f051b1203040c14220603021203070605060f09 60
    0x782d0000c845580c032514a4400003280640100701d0741401d200030001000300c0c155001205030001c00c0e601e02034800003400e907600950a110001c0ea6442440702d60000c0b50051450040020102e02c0200844000980c6803c025140000c80030784000300040c0c54144a141c05080300c0d04105c003690707541da04400c004e000515500c0126040141080045801c51607000c5000c007800b451220900e45084a9546240ea05d800a04880a200c002d0004101c000c0e00c26008010510000c0c00204121506081c00c000108518507040c40a00f111000840c03284100009401c40e400b07103032482c0c0c02a484c4c0005040d107680d010700503000002c8800303c00303025040c042c0004015001c08101e4800c1c1000412071100e0030a8510290000321500020511003071003200300100c0050710200d401540312410f040000b400303a4070524050b036817440c01c450b140d0503100c850b41d000500458001e40050203c81243c10450b84944c0003600440f043ea161001017092401c00c485030580f00c0b940907141e00402e80710341d90346e40c0294401c41d01c6c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 135655260 1250 135654010 135654031
    0x3010519091509050a0209030703140307080a03051504110a030b060d1109010908010b030a030309061e0b0102100b060403062a030b0103060803090307031202030d021605250509 77
    0x600007040d00040c81000c1c203002034480100041c5040a46480660340d001d00600c01840c01400180400d5030081030010403294011400e01010400c521103c0c02c41c0604034000e002440c001c078061320350607055005107101d02100060010810320030010481102c43e150340c3c0003100001804420001d90082c1d00c07242e041d0000610301400c000c01100c10f80165500b1005010300c0c260040788a5000394ac004050002910b2458020b2041080040110399200d105100280c01c164489001501388000c2d03a202885c0120320540b041d483d0400d210355a009000c01a139050f0051040e0381c00d00c1e145026030703c40c5a50a410041089107040d10716200d0701c0192401c03c0c1c5c000c4404100b00300400b280350035000e01c02c0e011036203610302180c510003402c0054102c48180d8001000e6030000c200a24407507801090340c1c000d0320780c04807424030901e0a80504034510302480200c941300328400a8801140400c03071980f0014144640c0448040d015040140c0c6040203950200b042c620304412000e03c45460090080c5600c68036108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 135656510 1250 135655260 135655309
    0x100807110f0f010902180c18010c0f0b190c1b14060403030f05060901060c200303070b09010b0109080712151103040c090e030901140403060207150e010908030105 71
    0x480a04080600c2e9218078260355405200045052109080080a00c0c10441c0025072511030303002422031040401011246806040322882607000700b40c80a944c5070807885245510041d840d0015115105480700c810491465625007980c403080c2c01210804420342c1e0311400282d01c06451300030340103043c0004940b010320400030032008a404228041c072490080c0c0d80844e09025081c003504c11180090584c034018064031005200d2507400c0800e01c401e1a0388102030400d8583d03850185841c400c02001030b00d80c9400300050f10414026a00a0307039024940034402006940040001500c04d11070310f2003002001c3e0007900d401c120042605203c0b0142c24052080482c001c001a40700d541115030ba80e03141e2100110200902c0144131702c0315229405001d242c00100112130b60280d80300d5580c096000b01e2410440341d00381148480d26a80b064070300450340b100c820f546070001454107284030100b44d20750300b0505290040c04203c0c0901402400c2100b60801c0d03041c1c3c40c603420003041c0085031004000640c40c0c0040030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 135657760 1250 135656510 135656533
    0xf050f0c01020f03040c06090509040f02030f060a1406100c020108070e04021621080c0703020c0d05070302150306090a11091003020306042d020901180603060e0610080711 75
    0xc2c0020500c440594101c655207141600e40a000340109411210400c05088401d0005454440d0229041504072121b400e9440542c40000c0c500340003040c6c0400a4050a0140300c5100d80d00d4200459000e42c1c0c00c030310b00302565024144680008401d10007030004514084800165000740101c80d040b03141c1d46000a02c9084802c08179041e03034000c642c1c4c0402120414142420300c1411541004da0010241c841c00c86003e602400800e000e402414101c07242800180b2541014000c01581300ca18034068640032038140c85041250311a4800d01c01640280440114002400ea07000200c0c0c2c85004003c011f981d0a480700109800103141c1007210031003085007004450301a555400c1c1c0c5c02001c12950b5809aa42d10b0040140300c00c0c0c8100790942c3c4000f81464000048001801162200000d02e14500607101d0f40b0190048036100d800280180340c2000f030f00c8000c100c0c40c2c0c4c0341c4c200c0410354840122a10094a0350b8003400ba21130b0041701003078005500c0c08081070185108190540103911110200c0380d03113004c038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 135659010 1250 135657760 135657763
    0xa110409050a0b01030c090501080f100209030a05062a070b04152d0e0c03120a0513090f060608060303030a05040c051206060a06030e030a0c032c1504060f050f0c 71
    0x303170000c1c2c0e405280c80c60100030b5a54507006440c00745c0400000760042d906000391042e80c2d49020401c0c5114680c001c91120302c00d032000c200b045035240c0c03c403088800ca81008031000c4841007090301d10001985080c041c801158a260040300e240d07139400b00043c003040c2c0d525286c0c0d5807140d00941d407214100d0b4407014040c05004100c020b81240300317031210f02c1030142800710020030200c0f00d5007500100c1d05d0300b040346c00201554010420724000d1441c6113109961760180a0212224403c8006d1854500364980e0045001c42c522307842007210b51404581040400d850300c50030742d140003045940d564540d1003000050303030f208002e40003190018820b52811155075100c100142c00c01c80341040040c243d070300c4601000f1042c41c104c04100000d021074181082141c0c00e0130314541d205d1040202e460148090441e01c002090b10031030488015414800d10f1680002c40c0040216688c00d008800602c9022806001030074581320904075000c4038440e407507540022403083c500741c606821102c0110100303002030000030800c030b10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 135660260 1250 135659010 135659033
    0x3061c081206040f061d0a0b03070603020304060e010227090613090201120f0e07150807200307060f0b01030e19140703030c03090b040602280c0b031005030a110409050a 74
    0x549140d040d40c200c4d102d0382c0c501c401c40d000130180a107c90519901e0300316034801140820075200343d854050794075078032400c245c805082100c40320b0107650320000d880d1010009031960b801c1040002542c111115203040c0411000c0c107415104036521001e2900794035000300440d8010381050b8410b0400135400e450100e1803104a50307440194242d40c9441d0071041c0000c49051100e50050040b000c0044066006058001c0185200818003000c0c0315580d0700a01d42c0171220602c4460740c1444104907640c0782c1d103920b000406086005444030b03c20303041c042e14078031960084c010300385c94404030340041c17410685c80d80b846009031228200556100084114001c03a0713110034040b00000e9802519481494a142c0c50001c0c420041ca82c000c190281c0240400c0c0000340d408034081c54080007080c00c01c6030f80000804480d01e000450803000341050180b60b000500c005080001c0c51040e003825000c83c140c155070704103042c2c84920340f2200910380900090703580018a410342c00030075181e011708103c8503d0b0740140d45921a00c803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 135661510 1250 135660260 135660269
    0x3180609150605010201020f191b0302030403060c020615240403120e030610060819140603070f06080c0a0903020a0306020306090c07110904151103061c081206040f06 73
    0x1070118054100c0e42a950242c2002444203200031440c0000d01d6560310b005001d403034141e0000304200e2107142d0013907118143d0344200c101c0c982603c0c9480d078014940070b503413035005e80f008941d5142040d610000c0c240c0040f80c010302c06c0c3c62204c0c0f0303942521042c0e001c0100150f450500084503103840345a9103c50318910001c0d0000e544542c40000c290080c07080080e260b50384400c00140300e0341c048020000c1710341014035100221000c500f4100095104c0c1c8183c1d543c03401c40415407003860f900c1d2034082009c01c6400c29006002c0c203030650503210b1168a035000c4101d035034428000c5002050740b400100c0c0014107520b00504060350719103030000d5401d440f60300094010740a684107950f840d0300402070082c14603107034402d0b03500b1074050038085140c03a45030341d1411048426400030340e00c503800b00e400003024048002200407404420703560800542400d1010f00c05690003c0d110940691a00900032050001d2400e0b2402d086400c603154506054410800d0b0400315401000150081c2c1c9801d1004e00c0880980500d80180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 135662760 1250 135661510 135661523
    0x50d0c05040e0903030420010210050a020a0306060809030403171e03010806070801050a1211060313030818061303110105071d040c050301140d0506040b04020a081c03180609 76
    0x403440c140d45106640300240404a2076042002480000380308510b58542844c0b12241038400210b5683c0141d040214041032b16803180e040c0401c00045090350350040c0190a8503850800c070030f0303450b108102ea10160443e0300300030552040000f407011803640c0c41030f0044800303241354082c94107100064101e03000441e030220801c00e403400310042c01401024054958040450720f032601d01c66240100241051020340300d5000c1041628100700144031176141e2000910102815840e52030602010007541e03405110420b07400590303044081810310306030240c2a02c00c00754107802440180c48102500f00003000c1d6107011030038403503042003c0d8100b550038010359204580e940c440143c6e212691010750090450120282c7c402c51400c0695640c072a0428150790544224000c1501d150300d5a0011034008441184084c1c02e9100d0002008100310b541c6400c0d5100750701c02e0f00d0700b861050b91108886d6a0310323044010300600c200c1d940300b43c0c40303054420b500c05014556541031030041c41a6940702c0304101c0308004000d0310320 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 135664010 1250 135662760 135662767
    0x10e0f19081c020d0c0201030c0201141521030706230708060a1401080a150306021201050102010e1603110a031406060a050f0901090b0d020a0b03090d03050103120f050d0c05 76
    0x700b40c0724a10100c00d103201d5002802030900c142c1c00c01400782d061508001d060540d45c1811412040c801d41c0060025501d84820444500f805c00a0740c24081250071501d01c211122018120302e00c900f051250041518032000f981441d641d650380300054030f030700b20044445842c0508080e0901e11001031a500402680c3c171081c00d2410411706200c03404800d900601c62408158090f000e03241da122601c2d41d404008103100146c903040c00040d0032603e002c55032002e40313400c1c000b00e40107150100950490781251000d8008000002031500034a032148554808495500e82c04c0340c00b000411045480e041d8603c1c0c00400601c00c43d5125a254408821145010200c56003e08101700c02c130b040001200c000791004403007000040400c100040c40e08101405003091031900d03454030300003a0300c800707a00c04052940242640150340e2a18041d002c540c20840b03260711030344646954144030600a200712410380340c0040d0841021103510200341c40c51459080c0c03030b80422600b0007424003c1510341c480c17081036200603652103a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 135665260 1250 135664010 135664033
    0x3060a0614090c0304030f02010213030605011409011508060102010b10020c0108063003070602040806040c090204030f1b170a140f03191106100306050a0605010e0f1908 74
    0x500d140c0c0501090044030b200080c00420480f03c0e0550754010303854074100f09024003040c01240640100c0b003a01251005280002c801c002590704101d040e64800888103850401100411800c0d00080c41036401851080500c07020b214460b1041540c400300600010601030400c1001c103159400c40c60b01d07000160424021081c00350782c413a07092508050115481c0c00700c5548440c90418040f2699180300c8010b14446403560309400c00c2c030556131580e4001c9421911543e5511a01c1c3d00d403441258115200316610401082d283c40d40e02c01e50781a42d8000c4200102c203c926a0ba1041c9100c062003602d0704420f00307140001c2c0300a6094228200c2c1d10401000e41004052441c005000c0c4d00405864a0250131108205015020010907201e00c4800300020022040500c2c20036140c0640c8421f0b1012540070b500c0804c1801d00790b602d4210101da1255408012550f40d00495030100c03086406014001500d1503401c00340740c80d0160300440c0b90760f0000e04e0318401c200714a003034490302c6090303520008003074100054070903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 135666510 1250 135665260 135665279
    0xa0905010512060708011e08060c0405130614010c060b03060103060209010e0a450516020610090e010209061204020a1a090d06020f07030e100201150905040f0203060a06 74
    0xb0128102d4000c01e03203402c244034090b00362901409045900c0b500280910422a500200c19004050a405072407041c01c04100c1e00c0c4840d405401940e008a42c0340c625100305030344034030843d0300b00c40b441c0f11007034448040b80004584182c98100d082d5096610781051600641d030522026000394416a0300627507034041080007400c211104190544142520b00e03041140444a14003003807002c0f240c030700c4207241180000392111f00c000c20703d011543c0015141e85a071207100742076000300c0c090b80c0c41c5420411898100d041c12a0744000c101c84801c0c004e4143d030010000e80b40c10307030851400011050000760408200d000842ca86420000700402241d95a005000075070902845420240c1504041c00803050383c649095401849500c003003d01a42c0d50388c044609002c0582d040d11202040341d040140d5500720345c20024003031005611042d10503006003001d400841d0052040100888544d034550b034116190060040061030000c109031041c0000074880720040e6000c0c003150303200d50407035840043d00c14100541034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 135667760 1250 135666510 135666529
    0x14060910020f09090402031e010605010206010504230720030301210c0e070309060e0c03011a0109120213090305030f010803040b1605070506030a09060e01060f0b0a0e0a09050105 78
    0x19010744100580e02e0103103440d00c1200c544180603501c0580907160362000c00e103003880013580742d01c1880c03030480e403ca00e484041d0407540c101c900982c04c844c210390701c4030100800c5640e0441800100d0500c2140130702c512003102d120550000c401c0c01d0822003640c0310003410351a06aa04401c005980000005100030024941c2d202d2031900c15528100701201c3e1a03640100800090242070080c4070f03120002810b02e4401e07004900e680d43d0044052160798600b030381080e03896154000441c80b80d402e11078450445082c0c65481d0f805054142d560408035403a0181180c03030907484070300030b0b60058081c03520603140701c0e110300174510040e1180e03840031342d43d240c9070702d50b081d001074181c1100845800800040041c42c8070002681c0b008074500c280444010081e00d40a803500c507850744516040400402009940d0070540c3c040d0f941a8010742090180b9003114000c0d07400ca0700745000b08201c1a404200a00c95030b818000a4260180c007401c100341030030342040000310a14415804401801d03241c00040c0040d06184615 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 135669010 1250 135667760 135667783
    0x30414090901020c031e040f0905190b031209060706110c0706090b0a08060f03010608010218010c0f03030c11030301030f1401051308030606041703040e010b070b0109050c07140609 79
    0x214100030000b09442d88034800c261b402c50107004030301010a400e4030004102c1d80284400404804502d548180101c06030404a41c21184078843c0d402c07a608006860052807401d03031006015001c2c00c482620000a43c0d0069445283c015400340148000103030144161414009001c90b159100c84c094240c540c6049100d4121204110001a0400c0710740d4688042c0c80308082203040642a41c0e40d0365010481504400008992641c20814005402c076010340c001e1030391208448015030038103000801075036441c440c0d030fa000b84500009482180441e01c654400c40b9000d80c10324280010160303a4070180d2842d0003c3e001922500e2440c0e6503c0e00b0003864080c54030544020720001d020914200303880041200c04103d015000c20f8000000031410794500c011100680310104020808131140042c0c25903d8115003d051103103c4d181002007050302d40081606c0c0001c1c0c0c06034074580968240361100024140c05010440120700030f018000000c0d01070440c41008682e030000030079052402c00710251505030300202c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 135670260 1250 135669010 135669013
    0x9010305010b030d1d04050403030b04090605060f030d120e212205010c060b040b06040e010e010605040812130b19020717070909020d14100b0306100302041d0304140909 74
    0x1c0703140b017849184100d40d0340900494001071160346c1c0c0c0c00e0a40150880216099106d4507240d100400c0040c0c692103240907410a0798610b8044800c20180b540c1e03030b039200c981a80420000e480540c9600d585810091880b81001d0035544001403030000d60703245c005080740d0350f601c9640104000f0034121b45681254040301005001503031062a00c2d00280c14108140d0028107a69101d0003501400d4499401404900c1c02c050000742c0e81310742c0d50b543c420890348280221031000c3d00c1c0500009200307200380f080da03003540c000303001030502c01c1e28603c0d01006c5940248880c0082011079140043c80150700c0f00540040350314000c030844669900c0304024144503480d00303c003180c0c49500d59034039a4202d000404c00e06540c0c2c2c80c000080d403c64035000150081511402c002c1000003d04c01514842c1e1011070130480d04c0030004410b02402800404258480004032a58020601e03490410009803030550030407032106041006600b4900164448181968441d07040140100d007100c440c4005030800100c1254070292140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 135671510 1250 135670260 135670277
    0xa03050a0314070806090403090305060705040302040e0c03031b010908040306020307120e0715050c032b0c05071101050c010f051b0f0703050f31060c0f02100e09010305010b030d 78
    0x40f800b0b4420f1501910480c00340068400082c01c02d8003902030320340507581213021260207103850900140300c7e80c0540005c82c0107a050042201e89424001a503048008000b80a582012006a10002140305003800240991f4803001c40401040454008101542c0100001350340e80c6440c00c00074205a0762060f20004661030844040c18060000c01c5202c2139075191001500c440316903100488090003241140210350000203034074000003001c2d9a00303070043c66044421522a246039030300b42040399a02800803000c184100300300d0000071107a14200c0c0d62010141481803e00154001d404d0071640c2c5d100703602110a030345038107003c0c1c19105480d80342101e01c5a009c9142c6070030f03482e0745100b6280c01103240040500801203400b20040a4020550320003030720b0004507035290f4070100003541001e40c40c2082e082809c1c40856000c1100d510400710700d40d249801c013020a140b8003071a801c3c4888039462051270405c000d0760342d011481c00d50300c6000ca030340214000c1c0008100c40d054507003003505051540c0406c01c140071201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 135672760 1250 135671510 135671521
    0x1050306040209040848070602060c09040207050d031e0b01020c06030601020c100f0e0409110d0201031e0515010e2b1218050a1d060f030a03050a0314 66
    0x10f28154444d83c012800c9403101c0803451101c5a0080600300e4450300a111070021030702c00e60104024620300c405034204c803981d800700c180c0a512810540502c200682100300041c5207001e03091300030809a00050001807500f00c6039110b0074140074840041400080d00c64080b10011510241d15a8100d500d800080000c1d01c04840040c0d62012034142c2070703001c1c903804000507003644c2c000e220199941d0b0020b0800780008000d64001801400307c0018200031031f843c60241000d9051910610380c100350b000035540018080c030f4040003900c4501c00400c0b070405071140512b81d040001441180c142030119480480c40d414418201b050306000310815504000040b1100c542c07680c0c0d00d41c0d9070901000324010705004051110345900f00703813100355009020b4502d0401504103160780a0504403280c004209400b0103d911902000141c449074481c04814061030007140d5400010940b040e0340001d0300400c4c44504102200110303091a1282c0700503800711307601040c03007600681c2600588810030f014254681091502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 135674010 1250 135672760 135672769
    0x20f0309120f0d080405010e0a0b040b0a0e100c020712030e06070c050402030c0712080603100f0213090b010f05070b0a0e1f05090c01090e070f050f0a05030609010503060402 76
    0x509010910800307030861100008030050100500b1021000250f50000300520000703491064140c4003154150701e000c0159460701d030040f4990071207613408050100c1c25112a1186071441e40080d01081185903500d003429407007002007000c40c40200c100d500c00709140b01600310207414040340b03900c03000e102c1882e4070344c410029902c540d107282c18102c22941c6540700d00e8141482c158503101500150342142c40041400400c5110300040c1a01500c900207031400f032000d070704048481c002c040c1c2c2c0300307078059000c00006a00034030b458016080f011b03910300c2c0044c10007108140e21b100094083e800b110300295280070507041542d1010035a05218503600b0010700e440d19543c0c8480c00741d540200544482640c643c07403c02618014004186910000b9000441a034a048501e900600050b20140e40c14400c1108100c07ca5001e000c1e2501107071010011280740e5903c4403c203031a02c0d01401c00f0b070020810100214145040c0c01d40c0900381c500384035520030352289005010310200c1101a004148268400001c01006944 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 135675260 1250 135674010 135674017
    0x50708011103010e180304080304060503100803070f1e05061006020d0507030504090203040213150503011b02101d060408040f0512030724060605090301110702030a110102030d1a01030606020f03 85
    0x10010058260351009045c5095020b1a000307400d2a0100050014805600c5402b840c003405041094030040c644e0f81071419940e12038408010a040d68803124840400c2d1591800116602102002d0111184964807241048001c49985081405510051042d658100034003441e500150525501c0c1a8043d14003030001c1c003551068140c40c5400000150454441e8404602900340428061107a024201041142c15800340070799401b0307600e004c002e0300160b0781403000800d55002c01c1d0041c2554010000b07091001d40012001c68064442ea503110a040180c2000214407680c003400e02661190306002d8a42221004c5600c000e1042010048912405402204594507507902c525240c15241e034910702a8155440079110100a600d0850b0010782150404010808400c084001304a50101c030402c0b2250ba02810002940640c4807030482d0700011401102d003001c030031050044906000d466400201aa5110880d10904103041104030040e940c01d4001d0a0142180c0e002030082c0403102400c00e0b0b500d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 135676510 1250 135675260 135675271
    0x3091104052509120f020301050901060b0706051e07110c01020c090c0c0109152309071814040c080c09190b0103060504020a02010501030b100806010605070519050708011103010e 78
    0x402500d0b2004840c00383e03001100510030f10301c074003401081c03509125000c10400c8000381c1c0a54209800900100018400c2d2401d40388810320340e07810807546448141c000c200051502c080180c3d0030b2108088c50414038486407158113140ea0340400b05220010140c10450b107541e07440d05641c458146807400b942c030801ca040d0700c00c3c0c4083d144e81e121181b151a01c0c0c0503003000c1c00040c3c4110b0514034004420340f050b8010100c4074010b00e40c09036905a500900c0005140c0440711802c0c550042082880385039800004c20b031150000070340118440303036040c45a03100c400c030694044075003002d100030410248005000360f00c040c032012603408107245042490350341c161800c0c0042e460742940d54007504001da0300946c0144041c141c06481152120320031440039000b41b80a000954280b49801c001640200419900a0503a04e510f000b9140b41d902e807000c181d444d80c2000310221824040d0580040309010241d4203403c1c4a8081c00c01480100c4c070b00001310382124a40041c518403018104018450741e511561810b0f00f04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 135677760 1250 135676510 135676561
    0x20910080c0315030c092d01080312042607020a0909050a0611070506040b150a1404020703050909040f0308061e0f0307030b09011a09040b180102190309110405 70
    0x120450f100090800a4a0110940c07040c4904207200e0480740440b00b4640110200914a403144071219504420020901c250b0341c1c540d1007040084036160000c282960464030503080c13030414030030000d0500c00441003540e000d2072400c40856a00e0a40c0341801914004040e0480704001441064503100d88440555401900340c584a8000f050f40d28010340880d00c0c4550400c00780c40c101c1c103080c80c00c4914081e081c3e0b1130103030514404118031101d14164240c0300c01c0f9041ea05100d060101d11034144400b13074200c2c1c4815024050305002d04d04890301c1d5482c2c813901c114882d01c840d0b60400c0c4940b0300684500c1000d095a401481c041c428400b21403182c130b0304580003840071940c414680003000300007440c248a9802c003e200c0d00b4200d0074088000015003000002c489980c00304400300c604501401141c010854010b8502d03d000808940b00070315070006030300e0500112002516004032000311401c500c0304464401c0c0003c2c1e903440d1400622019041040390350034101c40610142c1004201d0b108492900107945508 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 135679010 1250 135677760 135677791
    0x2040b030309060a0c02090c0301050904140705060703080906100803072a060801060206070f09050409020d02063103080403030f021504140f1204171906020910080c03 73
    0x940e40c08109a03070711218000c10082d0ba440e40103070014201c1307107500c40480c015034009000c9000c2001c1703901aa8180c507000b030301900040d40c950700e0300c0c4214064014000500d0017005404070300d50f1104170040440b03a01948402031755007040800d451402e0001000c0b0b18020407170300414402c001780070044403003240e04803400c00e502c0b528459021100d41a030003c1c0e01001c901c07840c0700040190f0407c8409049078029000d40301603580d40c45081c3c4446072200005400207241ca0000e0056142507440501d8072400070b0400d07403450605074082039460784400051200307154004442000a2426441e422014001715940c00e0014619540c000c010701481c0001414001034060614010f84200400b030300700c03008000459440e00340f900380303002503a0300d001051416000da5466507000010016a000c011194400760a10302894002c0ca420190300c080c0110340640113100d004010003c074101d0482c200c1c0c2c001c0500594650180e0104490322025200c0305013481100700402c1007031941d82e01540c2d801381240300c90111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 135680260 1250 135679010 135679031
    0xf1a06060d0f0605120d121104090507050d09080d06050307030503160807050105070306090c03020309060c0901021e0706020d0c05070b030a0f021801030e07080309040906020412050c040606090e040204 88
    0x90103664000603004031441741803a4400f0f40005404409004685441d8080708171406007000741c4040f16610380044208003c108030200c400c0e80540d47c080654a05139040c005804145410b031000500107940284002c078a0310104800c81c070826000701011001454110704c0c5596644c0c907030040300050307034100fa12111050144400030049500702680711000b003109190103030000d00180380700e01420301540e140124003000300740a0710840f8081c64800b002412942d88120b94840641d20050700306046000e903803102c1982c0c41400b11a021440101e03406040c1e01800c0400081ca40042401172000300001018440c0100c2c6000c170b459800d45000c650043d030f1302e6070780c134800c84c016210500442c86501e1000840c28030004020404080710300090741e0902c03015450321162039803030a141c01411240d4004104855051070300390300902c03000d0310030ba00160500356030310402d0448901001c810385081d08a0790b4102c02d94035291182c00c015000074240452a1424030031801007105c8000c10023030041d0f03540c00b1a0031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 135681510 1250 135680260 135680291
    0x6041e060e06010503150d02011101020c061801090309060f02070b0a030f0b0a180f1d0f010608072d0302041a0a0b040303020d1b0f0f1a06060d 63
    0x1160062904220000820004540040403540310707040490308528082681e6610480459004905046410810184103420040c000203043c00c100d040c82604684040c201b07a0a00107041081c0c0075802901091034400c80c0c1d000c8000400016240c0f03a403600d2040382c0000c0c3c0090416041e1801803612010041d0f1086050346046241d0304000308004001c6284114942d058100541403032421000f4002d0300484010f010406081e401079605d10307800c23400c980c6070800c4036600c0440482c84601010031081c1400010a400c01d21038109500940c000c441c001030340d11401d02402000b001a080240089450b12288454840360300100340a0442483c0120380d400c0302804410f4090354004004102c060b031f001ea6099211140305108074041d0b010350400107200c0e154581620205c0e034241e00605448402e590b41103541c400054050555030700b0f811907001c04200e515910490841c454900602c0c4000107007000390302d003034003120480280d40d5008100f113030780d4880c0c90a41e828544e44038004a20764881d0354201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 135682760 1250 135681510 135681521
    0x210702100204091a0a03120f0e0904030309140a0201080403140d14090d0504030b040602070203070e0f191a060c1009050109020406062d030e030c06070e01090509010e0604 75
    0x4824000b180c0810301981590002d01100800303080d021810348680103000b0710210610024000c25500680055014050705010b5071a1046280290415010a0010390188401d0f9402e0b00000e94400aa03801c020680160110f207a02503002400002041c0c0e0008004c9030008000404220a04000442c440d03880410344216060591040c0079241c0000402c40ca07800007101e41c3c41491164100c5464101c0c0108129030680740c10142598066440d41c032100081d41c0601412070305441407850010b02d1800ea075400f24003071034650003a0300940c10f008083d03030449035141298913036013031400f0031083d603c203800030318a031003004241c03907103620b0b0692800028100070082001e1040c060420014a003004010340c0030b1075103075100319003c00903192500c50450300e1b80300f5400b544a0b0070580020741c142580440340b07514900c05841c50045864400c004100e41990031501002d11140d21090920010356008250356510b003000b841c18008072890000018003859040c8502d05a5811000128000740c445800a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 135684010 1250 135682760 135682783
    0x1030f0207150c0e0d150e0304033305070516020a2705010e0f1503010603080f1905090d0605040f02060a02060f010b03070905010e0a051504030b010506210702 70
    0x446801042003040c501c043c004492030f890005201d418a80054507000c2c1c21038882d56000351b040e0310040b0103104810700a1483c04250301c0d5920092000000042d2a020300100f03141d00f50001548840704824094040130544204444c02c03070a25040050072030340030342600c1100407040078a003540581d50002c0b27841c4200070307080341401400f5001c3c140c1003502600c94000b407540d01a10100714903070b80c5040d030130f0200d81d0a558400000850101207541d80b41c90030002a0702d03001c01000050f0071582d0390760b2400c25a00108600040e8180401c800340114590401c240c0b0076800c5007401d40c80d00325450005015440340002c000c090503640d001190501085914403040300d40c0c054003c1d591610059006540c0d4401141d0450709485444004100e65240c03c058a000307465548441440d00d0820b001500da07a554061401d07040403004400045598900b03d1040007194a80501030340e0b00c0c25070070f006180b1841600030324010b1130108803000844d60301e0241c924004815031010401030b02c0c1c845080741400f018181 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 135685260 1250 135684010 135684023
    0x3080a090b0108010209090a0b0d0f0c0b0315040f0501080606060f0c03041706010909020619022d0f2407090e0a231905070c0507080a02030c0108040b0601030f0207 72
    0x40f6082d1015801040d84c0c1070b04a40c5446195034545524040d18440c140f5035402044c207581e10000154900d42000c100c42c400c0b44884400c0c1c0d112500078206801c115580c200350725074031043c1406400c1c68440c0c0c940c4611141001e025640c10509141c4e581c0e0005810a80036050019141040c8064035080d51095003107038040d00e580d10764500e29091481c807406a1f05a032400780f8000051010818822851610381c040e040c1403d204240711041c5003901104400c0095000f50440c02003181c902922082c00c410071001c04206043c1240c0d03545141604030901942c2c141d005010802d072442410780380e24400c3e0000c1c8441e03903156460040480301c01804d603105101d14084242400310802240d040300c07038003e101c0c0310400005e098051001643c9030003502e00444031350000e2108084002150000c96000e0894207011036840c6081d921245800a1035214a03116081039090100314982800307038040008013449c0408840c00c0030788800d14210700c0a0002414140d03030304c0410519007001d4050b900e800c3d40144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 135686510 1250 135685260 135685283
    0x616050c120703110607091e15080106080702150c07110d0602030405010b0a030803130201030b0a06080a060603051b03040309030606030f05060609160809031219061203080403080a09 80
    0x440070058012501c1200802c0400b0440840d2180000300d107072140240350f4920907040c1c5445042c1c0e070b4138404055045a074040020001c03a4540c0324052060f05462142c1c0d6080c040d62600340c0091103050041c0110301190001c06560300d280844000d0036420120400902d0364071840c1d451700c075000408001e18503404c00e051080c08000c0c01000c0d4059846030703000d0304c028008008030700c007000316903070042c080103103160024008140c0301e6883d01c070542401841814002050f030202c8001904803549030740401c001503155030402040c011640106002000e06040900c003038240614a40c0340303660021440841e111001c0005004d042c4600f0810005503008541000120340764140001e19146105080d0b8030782c45404c0108115060801001e0f1044041107000c69250140d4881142c00ca14040e088848030710040c0440488221441035080c000c400b2062084214541c152001043e183d80b0b5011041d80005c1428100c0400e82000101d584243d25152164190b600e107019500200b4040501030003030424031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 135687760 1250 135686510 135686533
    0xa0204170f0706030209100305041a240f150d06150c11090106050405040924050f25030203130f060f060504021612021e0a02130c020616050c 62
    0x124540700344084200980780d00b551119002e8060344111000140c01440f16913015072490300c03070740c4038507006403150140c2c00c500307030300d118003c86550002d0301d00100c6010041d030303018040c00b007001606d107822005503410301180d41004001601400050180300d01c82500040d0f841202c801540520080d1402280340705010072420f00043c2014030401e0300300c03041d03603001c1100c064501e0451b0900741240c40d00e5440a1601e81000f0600002e00803140f01200ca000c0700161000c0090351480c1d806003d036810410002e19031500382207075035400001900010040e000b010344940148980d030b030740c4c00040240717050160343e03030b100d0100c0404090005c1d1800382050001b5480442040f01d00d800c0b502c0008200d02080c025981c441c41088100d01c80e16103244010106400040300041c14591000714103509030041e5000001a1180300340840d4441c6144203154200c03a52030343c21803900401c070144803042c140c010081c03003486001c06580c401d00074280002402015410712035840c460030884040328640010b4610544a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 135689010 1250 135687760 135687763
    0x30418091203020c21040906080c030a020103020a0203070b0c070507170c06030403260906010b0a05160c03020901090203010509070e010c031d041d0d0201020f030c03040201090506040b0d0e0c0a0b030a020417 91
    0x41c2c0510748510381000c800007464403000ac0d00a01e40388004015160440707660740150001d41c8140042c0c402d42c00107100c032502241210405500c0b691540c018a41e907503180c2d107070160503c00b07141c008401072103542d0010005003000140702c1e122100d00391000c3d0340d281c032039090a40b0603030000b082000e041c185850707899000340384115401e07003d225003100302c031102c0c0d032114150700c10b900070000c4001c00580240042c00c150480345482c007800d18015024409159260b4001c030703100c03a0b401d070401c1c90820b13000401000710742000040c03654170010743d16296004006020001745040071080c0301400300941110202c65001c0104078035260300800802c1084400c4221007100c80080e100c4020740028025005840301685c010300031a40d0508140340c206145a6441c3e02c4000303030b41c20140c0140c3c100001c4e0400421320352a2440140050000081c44645448408611405552010380720071459000a10980c040e80c94000d44541900d60b8440c01d01d890343d45203540d0038002c0c002c95002040d04000c00460900c030700d80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 135690260 1250 135689010 135689017
    0x4051b0d060308041203020d02010b240c03070c030b0603160b07050c0907020d14030105010f050a02030f0d0929010b09030319180e0103050613020105070b040302030418091203020c21 80
    0x40f0340c094800c0208043d23400c1e8202d070210f0f4403ca4100e0328950302030032180300012940384059048000d81d824a0042c0345468030f1904071000032038214120b82c60138002d0166511115601900440003020a2400300c0c1c1800306c1080c4904c074001e0b0300c5101045c44410050144282c80c00400041c2c1186460320304004003e42e5000c2000c0b011b00460000b108400d0b140a00c0004c490507104107851340c8441083c01c03442102e40c1e5101c550b21804501091012040c501c170f40800520b1980c554a4012074083c9840c108000d400d04241407481c1c808000008010404230984211070454071002401c40e1a4080c00011038118403441550000061481d2004105a6040452010803c07007041036620220f03103030a2885070152080c00090401d50001d000203072641c6500c0c0010903403c0c07040c501181400070950320080350a10940b4101c0240e08041401d11490050303204c0700010354150348043c001e00020f03440700440400c40d030550000301030b0002450400315078204401c80e1031280c101c401d1050200a034a00795841c3c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 135691510 1250 135690260 135690263
    0xf0504030306051c020315090a12020a030e0409020d020402090d060f0c0908060405100903090e0a0e011a090a0b010903050a080909060a081e070b0a020a02030c04051b0d0603080412 79
    0x11601c1c410598804a4180138050164058002d110b846103c0c1440f8801620041180c0001d1207070400000015101d503002145c004041d80060134419210701c2c025050240c000000e078040c91601005c0c00159485c6078003c0f140540551340142d0f10000395010803049405c90380c0150506050500d4000e82080300da100a00c9401c095a45a401949480c105500d60302c00307890141030b070360080385451141111a404450007500c00c0c02c04202c000d40e240600760350790400702d6900b602203035180d250b00d40e144030030702130206a10071220040f00400c01480c001100a50060182d030500c03075460030000c0703050b40110001e5000c0c0d07800004440400c083e6142c0490254085040f450082102001050311401d003044c001054903c241c0180500c5000b200044111a562200079042440b510400041640028004003090100ca030b003d4807030300b105070051602e030103204000369004070702e05810007222510030790504482400c2542081e5485001a211130301408480e0000741c08241c002800247c3d903103283c105400b030107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 135692760 1250 135691510 135691519
    0x2e06080c13060501081906050d030203030619080318060403050a05160e0c070b070309080c0f0c09040305120a020c070f170a020a060c1b060f021209030316060f050403030605 76
    0x580703807420041a551070b4801c960110301010045550380700805402c50081b440e140001071f1181d0384600082d40002e0701082500503800002c02c8c4205030500c16400c0a142400c9050005d40c00d00d03040c1415542d00c50101d40c11940d08403049040425502c200c1124015500b00d0101c5100c4092410704e00d841e50000440c14007426045a0005031440f00004002c0c0725248001c6040d09041081e1542841000d006044800b01666820b00f180007802d503501425403072503400001c00b050825403445501e000703000e910580c0310f10100340c200030000f980700040300e0241e43c4a0070440c0081d22482c0d5604007900a00300c81284a004040b404039040268503204030850f4090070f055940c6c440031181107511802440030203500288134100501c10b050148040c1014140b0844580d0f8110480004404805005412000000d6441800f8070b2210740e04220428030360040440882c03411140c080000d90320711a480c01c1344100680104d41100384807069020000940e03440d181030090389400c2c41c00400030200c0c0d0207441d104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 135694010 1250 135692760 135692779
    0x19060e09070e0124050a0c2406090b060a031d01050f06010e100c0305031b040f0e060a150e01170a06170c09040f0609050318010f0305092e06080c 64
    0x100300303a014408420f2480c2c0b050842d20a01021669a07020f0503000050201d40c01030740f4001230903c1503003a80b082054207140314a28103d031501e02965156030040940310305002c01204e643d500c400803190b0303c055500740090a500d500040c108000120080c40c0255480c5c00100005406211038083c440c4101361380d541c10504040c3e040103c507100d50b100813030001d8640c0c4001030010707000d41e00031034012800d13501d005ca05141402c1800620790041d00715a21800101404008030703104d484d01d0a4000c84100c5100104600300400c40d641c00c155a11500100010b06c030342c1d504541d020703504400b100b900e9484021094640b4064401c05048540300d1004c07003d45e0b283c42d5101d62040401c101d8080f000c0100f12072a00e03103481d00d9588680c90110015108103035121500ea00154040000f094801c01e040705a505500405002401c086041c00800013818103003400c0001c858000f181c030540d041007940d0303500b070010090084907101c0ca00d10014102400d2601c180416190000200e100f080c010031540e1040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 135695260 1250 135694010 135694019
    0x40b1006091805070e04020d06081002030f0a0f0f060e04030801090c1409030f01051f051009030219050907050714010209010c0f06091a06040f0603080319060e09070e01 74
    0x810803880d10514968045508016000103410f4110b290444040c0c0740001c04500f68400050403a0321092a41044a40d40c850810031031030184034050b10010716280850951410820b4141c00e040300401e140310b555580c0c141e0f0b240982c4285e00c10320340c041303c0c1e410403c4020b84640b0030110b01441a5002d80126850400019076200f0a001c0d036184480300740d4403003a511108511712100c0360080003031640d01d0300031004655400c020034880e0a204c2c0c0342190100b040216030004c0924001d03510740100d405004040e24914085800c41c4441d8102c95042e10640034807207030b000300b1001003942500700303550200c40d203000d00c9420356000000c3d0401a008100003404043c220500c41d00300e00c030b038803401404140100d0124010494221500d00124000c14002c540c0d241e05650b4003001481c001509118050805c1c2400403e04091088007500611440200075803401c0d900c0d1680301d800010100d02401411a003500e04000c0c0e41c1d001710000304080d80170320348141841c1004513121303d25070042d0281101d51100000303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 135696510 1250 135695260 135695267
    0x20a0606090b090a15060e0d0203100203061309020d0b0a140411010f020c09041713090218030c180603010605041425140d1103150102010f090201090b1b0303040b1006 73
    0xd241c420302020001200d40740c0701b02500d2241814039010303404207143e0542c001603102484184129041c0210060f5a0300c1d0403001c00181c5016010101c65403807070244010010788441000350710312074100381207880642d941030444000c0e106c2c8110641c1f070440501c0522081040001d6410007901c003d89034400c44bd02c800201720303a00c040da414469031000100c4041008030310440198040b0b15801100546060380424001c0c1800c08907030300000b1102e500290071201d0400344107003444101800c901810042c4c001d080094562007039142c2da80c00074074a10b004070303201750790950140d001003401510602003000752004012114100710340c11000d200010f200c45915503e28a0700000a44d00d035200c12401400304103440c02103802211001011691b503040140003201b008004e18807a40b1200404420118150b000a09459940150105032400c08448400503078103c1601800c3d20320410800d504c8104c0410404561101c0401c550101e0000106000c2030269506200d4880c80502ea03203800c41560316901103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 135697760 1250 135696510 135696521
    0x9060e060a150b070f08070c0501021c08070315051e090a0209060703030b04090b040b06010906020304140d0c05100504030b01060503011206020915030115030501050f060702010f020a0606090b090a 86
    0x82d8100d0300051414040c058280c000740440f50b0041707040301550462951015503542c4403001c19901940e403407408015035070313042041441c2615020119211688402005002041c0240c0910306241d2036440f40b4207107035032540c1041c0c001c100c000c0c160000510710303411505580c910070344002e0080c040040001c10400d840d00072500d08020252465103030060320b8400314000c050600d05182e2003a101c0d041400458010220a070081c0e0041e0b103000e2031428040005411084994081d80564009100410940c00c81d02c8400b40000e0050780c81c07a80d4000302e85001750320b0f480c03207400132540070b8096103006030071179441005441a217101e1103640c401c41e601c0e03841c1500c0501003446424404155079420300c0001d0841d801801428802418880c0c01403001c1440d004079400980001d080c05086580c84003d240c0d06001e51401003a082d10310680c43c0601001250765482048d4020741800403506101081620802000b00a44d400c044c0070030140f41c442e40084081c0042000c03039072140840ca400b03e405140755101c1c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 135699010 1250 135697760 135697781
    0xf040513140106050a1b0b090f0a021c0305070503030901020304020307140306011a0c0f1b091b030c0408010504050102070606061809181a01060207060212040608061309060e060a 78
    0x703040d06a860f2000c00c8503107070312140f5400308120182d1706d40043c1d100802080084584151807143c4240751001c4100d00d44025401c11603500d500001e58540036031941c0100004081d02141288089034541c282514241303e020f80062031403000008000103154198080e41c0100d10840640e4a0107a8482e6240b41e1900c1600c0c180707515400c0030004120310381410f54860451044094141c1c02c0074410a0b00318203103100015001d050307800c100b2403940c030940700214512041c0012100480b00d030610f004200c0600301480303000e03081c0103000400705260f054010f09440082c01c4e42e100a010a180a20b4124041e4020b1901124143d04058010662a010310040020000c0b141c00301c1c0c0711185816400740241071400740c0d540340c0045850b0070340042042e405008a0407503c484000c4025403414030001d00d0701000d44c0c440310840d0850000a0721825002d07003240c1c07c9031840c2c81c000480f80c40c1e04001031902070382c0000607407100e45401c0212041121541010b12003554000035154140d03186020203007541c41d075445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 135700260 1250 135699010 135699041
    0x60609010e070f180510020c041d0a0b040f0f050d2006060436051b06030c0309070b030a0516090b0703050706020403080301170c041e0915020f040513 66
    0x81c10030341a880b83c4513100d40d2119400c0d03803808440d610320119081c2c1c1a05002440141c11000c040c00f01030806004d008000307446c0c43d804402041002101382d8139010302c01e80c0200500c1520010400b0300c1540e101c440001d9400020301092a1382519015948480c89610034001c42c54034040c80c0702c80c0c40e002c001894140740c50005010103980b00e00c101b1009040118044a9008403c5000f0607003000c00446880391400c600000b81202806040203494030b45a010861880d200f2108a40c4464a07001c041d2500190320560140e160784680300d001c3c0c02c0080d103030000d1104a4011041001c4100590000b07401412070203181d1340d919201171700c00c445d905811301400c4524041007004074000780c0f041d030040401034014000181016129500e021041e4002c2e0300c40800d101c800c10302c00c5600e150501c48060704072001c48040042d190240e104c2c1d01c000007610b508046003955400c0b02000d110055001d14000c07034002008565a0702039146000d907a130051b018035402a00c258421040050251107806000020b9a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 135701510 1250 135700260 135700277
    0xf03180604110909010905010c050a090e010f05130f09150e010506010816020705090106020a021c150504031e0809010605091e101707050f010503130b06010c02060408060609010e07 79
    0x7000e11203d580054508005503596179801004580d00380b140ca80d480352540d5419980b1485084014031080c281d8100540f00b8105c0401004221440761911040303607001d9a490440440c2c2d13544810081920103241d2804038140107010040155110013000c1c06055400b0401c180030700807515908a501c1114141e002c100c410000c03d00203000c0383c10001d0324181500c1101c41c2c590320380c80801c100358801e900440140c1d00c48080b48046285c204502d001e08000607050401040072a12060a600100c00d540f038001540ca401080501d03101d4400d0034410094090f981448187e1110f004180c50030403070b240c4185d9440e000c4003042a103045440140036802d0b4400154048040d5512451418400780215034045100c140c00508541442c0310908800860005080c0d0546071600b8030540f22140d000f19410000208104894010010700d41c452150300200040110b5403003030016607007003040c0030003e5800000400c00062502d000903000f4829101580d944c91981d0b41c401030009841790954008010902d00c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 135702760 1250 135701510 135701543
    0x105070503010330030e030408010603151b0c0f020a05180402030118020312090109031208040c0e04050312091e1605010f020d03110d0e03030a0606021603080702150f03180604 77
    0x3030300210300a180c103105480c2380c1030303990b26120f084071070540c001c41d24481c4100390000c801c1003600c2280c248041d0b10003044145504414004c090504030400200040c441c1c400d58415521a0182c900281001401f40035009041c1412513069010840b401c030721941c20b02030310100c00541174609020550f406802440070b007048204600c6d1035000090340c641040780c107600000c0800d00041d0181c524001540703c000070303428142403041c3c80a11540050300c2ca08640000c2c040024000412546568400c00e0030306c0003a1214103116060800001183d060030301d1019201c80800c0c000b11310303800940c0310f10003044101684c4000543e001c001600452003d41c0008000070003160181d0404852222a010914a05440e0b001d1200c100c4131440e03070840c0c590744048201b00d0300c85e055101c2c800252000c0c0c0001d0000d0510312500030103c0e43d40b800020103a03500828810211340301c513401c0309030703600e0110b2203a5104d0001e810160a02e4004491248880902c0b09190210910103d600340c000d43d000a85045004100c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 135704010 1250 135702760 135702767
    0x120b100e0d0602090d030c0c050a03020607080a090f080d020c09100e0702070305150402010e190605090402070618050610051302030601180f0501020f070e160c050105070503010330 79
    0x18110030356042d6020444140c2c180e444205802903280709071100300540e003136030514400d41401a04014050310484200307001507600c00f003c0e180c82961050245680b070b2004801101c142c1a546c2c030800f411281400c0c04903060708003240200340c0789480d038202c5d20f6820061040024000d0300307492105011040041c188031540100341503550000490040316901070f980e42c0e07010b00e010651014a0303001c044c802c0c103110440da8040e43c91040c81c0e4084480100c0b4a010003040d48041e00907104860602000040801207900da5806881c41660491400c2000303503044040204558260203003101c95000f400001000e040e8181d42a9040d1a40648080079036104142428001d60004d0802c070306000009a545419964400184024040d01030b140003029207084001b91504c20880be5850b1160014242030000d940703004105507100000a5010240d40640c5c84155404491103101400da54200401c21a03c05d80000003981200d06c540d1000c510884200e820000c1e80481c84c882c01d01000c0080100b0b280d0030721 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 135705260 1250 135704010 135704029
    0x9040e01060f05010c1b09021305010309050c010305070309020d0b010806060a1518091508063d1205010608061303020303070f0509060d091205070c0314120a120b100e 73
    0x1103860304809443d0b100381030000306c0c05140c2c00043c81c1a00020f440c000940441c040c0c2e40140310070309080c030241c0200d586031038039901260b6140c0d0405a9510001301e92500c2a00480d44040d0007801003243d0354550b08013410100024006c445142c814400481c1c800e003400c00b408402ca41010a40e01c4901c08091800c4403c01c802c1551a0010710004c40007007001c0e03140d0300c21040c0e0f08403000c00c203c80ca117140c141c80c241010030062100d06c90589564040e04086401c031030110700800410007440856031914065100492190840c007590001d01d07152504207c015484281036070302c05021200700c1d9603252140d100700310413004020010380050000c5a680c1d0f0060360034000e07084403810320908203500640426071503005008441d11461316002004107018426000c0e4503c0d1209140c502d25000c19520ba04030000200e110061040e464049502c00102c0180081c0030181821030400d40c1d52480034100a0101344503803480b20205142c10007150703141c40d05842102212100d80c0742c42000140010400000c42c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 135706510 1250 135705260 135705263
    0x1c0518061612020d020414150f0405090a02160c170304030320010b060c030d051b04051c06090f030f1809090501020706230a0606020307020d060902041109040e01060f05010c 76
    0x2a0207208180ba0304c426400900301900d100305850030582940e031304000720325180c5100480703084400c01101072050304d01401c4406851040e00c80c6030355920b51400c100002e1040c10780b100d640000c4581d0f440304001d4060b6100003203a140c1244104400c600c2c000e1039440c2e00c41d510002300460401280141403007200320207250029540300001852807446804214968440b2030791800c02d80001031b40c185010040e01c10790b500700d0002c3c084142046881050003c5e90301c501c2c002c0503c0b80540306107424000d1003202c2c0003904a6030181d418401039907a40f629081052521108502140b00d003442c00800f94410900008461801a030031816a407603d41604018a0000402d40c0c0355502007104001048403401180780140705000c2581d030360b150380007070400745078405810f032490207007410000c124065001013655030341e03034040310030549c8010107143c48001080c88480013074205007000c40044007202c4490240400f400207031002c0c002c1010400f105404c907801ca00406c038107800711000500155105500e01008d8a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 135707760 1250 135706510 135706547
    0x1060f0e010c1a07030c110303010f050f13090c060e0924010203040306020705030301060305090d08060603060a0312030b0306060321070c03080315040b0f06030403141c05180616 78
    0x9080d24020365482880859108001c01e444103c0319080552001c0c100e80c0220798040598115414810461020b2f4028490584903800701905042695030f0750030000107200c5000010030690402e4a080b0041400c5841000c02040c4016002d804034100000a90712500c1c06540c0a1256914110006940d0604c490441c1c11880300b40b001000007200703480140102806007005685940c5000d100070700303582004100c040c4a4100e00c0058248640103c9003c0d0444004c84000b40c81b0350303808010071040c0341e0302e03400036290b040544000c0301d4151309944240f00c900d0040d800d44140342d5600c03081c07641d40d80307202c0b920010b03944980885441c05289180600a424071800b0f0000055540f501c614029810640c3c9410390045080c080c0081490280b14502c00c0c02c0c800c0d5078140ca01010500010014000200040d00340084c00700c2280d03400c036015003110250260003600c10710203251074a0007c010b0508480d0349003180914004200300c0d14000480300c1c415000c109581c55284140380c822112003080c0d920a0268 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 135709010 1250 135707760 135707783
    0x100b0d150b0705060f0606040b0304030e01230a02061b0d0504051c020d0807021203010506070201090314030403110f060403150213060806041b120b0604030c0306050f01060f0e010c 79
    0x40100e001c0060144074082c80080ca41350600340c1e420214854003a200ca48600c9040004000e40086101540c0d4407070341500b03109032000030604c01030b5410490261500c0a01d201e50b004046101103d20103840100156801c03540c840da11621100213409900c400c1a41e244801e206040801c01580c00640e400b0b40326000b40d481e50340d410400140400e860902500250b04500070b212843c0c1d500410301c55020005100610114820080880c6c8a1006028607401090002400d0040d64003c47d2030030010b544c80359840f040e8189003600b594813071b041400101d030780700039002c0301e03415600d4000f401d004c0555000305101d00c2d0900d9551030b040400c04100b40c54203503680900145c0007440b01045070f60020012038441c00c4040c602801040f007210100b0400326900d19038003008100003940710392811036a640d6404000b42070110007002a1440c040c65000400125410f4404810032909801040c000d500a0180c486070346d88610003500c041107a24061400201c15428185041d8421040c040c000d5020740116444c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 135710260 1250 135709010 135709019
    0x100c1205180f010506010e0904290a0606170a15351b09090a0c120210090303080a020708070206031302010f0c08032a070c0509100b0d15 60
    0x16240304603401d003807401040d912014040070038811142640340d00d4000b0400ca02e01400060113140110602d18040c0040200280400a40d81c2c0d15902404409034001c0f0005030f0b0a0611130b84410440e2041011400c1c5800018024042d0960b080ca1507034000544803283c1c1c40c0f09040300100740c10040804123102e00800060306002e0b0910341c41c000042c000390310007000f010207640d00340b0395010307032498001794071002c10749100c2c525401007481d035401c040765039000e20b841c2d10100358600300180f4005060050041000145a1195421189092320a450105560380e182c017065806450038400500454103400c0000c904a6071a401003071440d00c5a90320310b0074682c00e43c001ca0351940045440c40c102034141c0e104032080d503821002c6002c80b9a040d1800301b103050384681c0d0380742e118080584900f03000205804036070031002100c0700e1804001c1000d4880354403141e81b402c02d840c000c110340c170a0602590309140480d00c64042040100195885000a0740c40c05010070783c030b800205005002800200d400c8100842c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 135711510 1250 135710260 135710297
    0x20c011e050601081810050702010e0d0c02030c240f0d060602100e010204060909020304021c030807120501150509010e0411040e0603150c0d1803050a030b040b03100c 73
    0xc03000490450001030340d140842c0050320310300003d4941d41d500d8a401c60a0128018002518a001e1003c0c0d00042a1a168203e00ba4094021074000115030b0080d540c03110481c43d8803840554509000310104c0300300010720002d00940c224520758100031410382e50176501a031440c0714001d01c20418800d54962504082d0f1104000b101c4d401d802c14001604940000d61551d0b40314002c14848548290085103000d28101000d00510f40c54400d0b4140d95402100090a6584041180002000010039000e03000114a401030400e80111007500c0442d40c030359290700304941c041c0710f000d0580b00c04801e01400c5142c81d042c00d1707900d500000b80e00343c100043d45c0e5040110707807210701450860032a40c10303400c1d07181c0703080820800c181c10004064902907802200340401600d50003403e2500042001034066031502044425005002402c00119100320003019040816074008010001d0280c03654042008842410412054540c98030701181d0507800600003c4615255501150769902e6909020145001107400c50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 135712760 1250 135711510 135711551
    0xe1f030605040905150702070f1409160813110909010603032706050c010f060e0a0f0506030309011b050f0a0b06010309020d0b09010e060a0f06060503010e0c0706060b1209121606020c01 81
    0x140314036000340c407220840c2041101e550b049141040700f140cc40403505402010307620024a5046008088000e0400f88908100d6408200d10050841035035494240507440c042c0400d8482140000c80d80d60317035142c2480031052046081c500c0310b05a030310703040d143c2501220160000800c000140d5a1500e441031131302194403526000702a03030285019146044c2115500b246e5503020304000c0c440c2018100038032607038003204543c00c0b01001d007000443c200c0b02040d000d00303010340e10038010030b244070342d0125800e85e00c00014080c0700c20344182c02d00c147c540e40d141c0045058a400c140e00a40040c0402040d0001a004c900000d6200014500000b80020f103008110314161040d1011012035a60300c1c0c0b01291440d00e809000081c00d46410309918551502601400c2010010030611a081c1d0100300305042000076000301d0028401c0603501501c510312004903a8080200352058811031161080d6054007a010100f40d9511b00c8940e0071b041c0d2180c54a4803401c003e0340c41003552a820703561b03600d885004000b501350342d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 135714010 1250 135712760 135712769
    0x6020f0712090801020c030306060d0204080f0313050406060804020111030d060321030c090b07020609210d0207080a02010815060301031a0f040f120e1f030605040905150702070f 78
    0xc81c00103801c0800c0540707182c1c0d0380e810443c0c03d07900420040083c2680002169004001540d0fa20307564a16038089200a0080b0340112259000c0d00d90f04080c041800005080100522609424495980c004000442d001441040b001c02c0c95507001801660161131941c07006a0058241c0e85441c5000321000c08036046500200d540086844218245203001940c005600c200c81c102000031010b440b80141c990b07000b920902e126405c002031408119256030040c2c0341040000b4142c440d00510702020594404260003009059110303002082041c10310000b4003808441c0e1041c0600103111322a00112207004009050800d002c80c558103500540c1caa03140158002d50064105c01c1014681c115007202c1c00300043c2a0203103040d083c0083c800400c00c60a070400100381e1202d5020f03514a5011025654240312105d0036501030ba41204485000c50040c0100000c18540d5804001d0141c0760401c000407290b900344080c0c01c990042541c4031007010421072864221600b80100c40c070950b03484032401c0043c482a0030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 135715260 1250 135714010 135714023
    0x2a210f1e05060f070e09090708070906150e01140c0c030d0e18100b1b060106050409060504090b01140a1814010b0712050f07150c020d11030307080406020f07 69
    0x400c1000e00c0000d010b2142c210740d4201c200140b03030410fa0001008044a140039600c91207484003c81c0d443c8504000940007010382001340c8028660700e00340340006211a00c25000007428028000044522451810111f10416152031804100c1034a111905820081408056100c4e292030500300d503800700600580c3c91801c1d914800d220b442d010901403504082d82413080640c0603c1c041c00003104062000105441c0e50b440007548501800d5a4a50301403460b5401c001c032401400008507003141d1010050068400c40c5005100d03c95882050000f155040640640308400540041c0201d2070610ad11a289610041500a005880e242d90308420010155a024295900c00c40c018092100382500c034014040402002d05182c80790701c9001d011ba401c414920f04002001034440b4403100c0f00b0007038071005501308644004074080c00b48810700400800600d0805071156020030702136144142e044201c01fa039598017840c00c0d600c61b440180d40b003500290046616a070240110300d5054803440181800364010724 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 135716510 1250 135715260 135715313
    0x90901020717121b070204050702070e07052706130f050f1e0103200c06180a020102031909090f050a0b040b0303070f051005042a210f 59
    0x291041100400e0071403191504014000710300f0a108810409500041600d44540740014001103424248500d49000b036119180c0024885a01c3e80041d0f9203055403041d00e5007000c0c1d0f4407860001d4405020740e0300d15031048031103446031445445000c10003442808029041d2820a41d8410540c44d4094260b0880700032101802c400b00000d16150b85e17107402540d0140c0d03041c94071039842c850205043c4440c00300a414151102c012030314206061503042404881103178100e072a0f0340112009900ea010554840c0c00f0300c40c040c8020340c8901c0011a00f1081d0540c140c00841c60b103251100700c121401e042d4010788091009030540010504210f0017646050b130350b2604005a01e190480314101112100a000b07030050340703407441c060401c0e14008126507c0c19008022100440d010303207004d42c505041d04000303280d668205400c2c00100400c0301d00d910a207a110078192059440000310a08280d9041e01c00c500002881e00850000d641c1003642d28030145000d003060740444001ea844018003040c1d0759001c082c2c040e2240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 135717760 1250 135716510 135716513
    0x1e030c121209030803070c020a1725050303030f0901020d05010303030914061911070501090614070c030c061a030703050304090609060803070b0601020f0105010e100509091b0402090909010207 84
    0x400c2900d1000750380e0400448075070564944500e030340401070648003400100c1c0001c0040d540c4041d410401401c08159a41030800c009800b240c550100a81c46c0020354400e403000030081014050000036a007001d8011411903071140c803508480309015280c0001c6542c20003a0b40c054800340e00078580614001d40b0040b80039103075841c0520f04600c50f50321031002d0782c000d4014000381841d040e40084002041030700100344181843e0ba081c01d140328003000200380758605606001042403c0e00204241c10f4401c100440a07522a803066906006014009000a1500c281c420004e001c5a11440d01d00c2c42d85801d4028051403100824a44805508141c80c2c0d644040b030b081202e00e1442c0101c01c003030109031509100302480c100700720707680c0e028640e40103000b04507000000b125a4801c1040b50580501003009000c6075940d20400349450358107482841401007101008241406e00b095a03e000d0601d8400400d02104d00445003010a2030f8104400d600c03540030040c454042d030710403501c0743c007a0284100050750365019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 135719010 1250 135717760 135717773
    0x50727050901081603151e090b0105060a05030a0515031009060e03090102101a0a0f060201060501050702090601140913020d051608040809010e0d050f12131e030c12 72
    0x50f8040c5400e03612283e0541c05401400003a002101c2d0700401e08160103004001641c09402c240303e00e82055203000d60181c5600c015038100c15101c83c019003500f180c60b601d480c14003150344500880c04000c201f080001c20310301581d030b0b448103510402e001c1c3c1ea001d81e500f0320b000003130800c45041d1410394550344466a040900c64a407085085501000006500d0220310700d0010b0f480d140ea0b039014a09141d43e401007402c07801031a510b407090801d0300034040f00a80b40c036604081e40e10b002900400f801586881d50100c0e50354007450460700b401c0e4001f040c0014540e0395100460380c408440911031541c240500c43c850140e00c420a2504d031b4200d25010150700d9412205007417084403401003442240b08940b802854005400c4a032440d001a003000344144c0c2d0310101c00060700c0034185141482d41000c00480f071a030607c1000709102e50054040c1044e01d10100c070724207c000141c000c0e166412904000e80400700b24820401c02880c07000c08440300320038810342c1d40791107007e18a034565010002c2d1008070700301141000803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 135720260 1250 135719010 135719029
    0x1020304020907030b030c4b030303060f04200f0c0606030601150807030605030313060f0306080709180b071710080d03050603011407020d030e010e06060405072705 72
    0x3882c9010000d80098900290317440c07c2c201c2e0a14000c540c0c00419410780e16a200031008840d03800e101401541e1140e40811421101c0d002903e650074164000301c68041c90040100d034050034005024140361151141007100509843c0b40042446180c468941150a222005090520210001c894540301c8071442542008401841248660030503001807003c1c0d216060b051600404a14104140d0350324080198010202c030340050758144000300d8a070b040342ca079503403051041e10400d580304030441d80d01d200e042d0b007505c010b40030b80300c0d0a0300000d40034082d40302c07580e01082503e13181002a400305800307a11043d481c0507060b1040700000e90004600e070b6400c1441c03010540c1050000c070b0b03080c0c6083d00c1c0214a40d00d500f000e010f0501059100c00219102e0b82c0c094110110449101c010f907442814003100181da42d02840b00c071200420b04103450724400d040184074030410342d1400780242000350364440401008001c024400c0c424070401d146000d910f59460001c40f038500301d600607001110750a080401500b0074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 135721510 1250 135720260 135720271
    0xc0e0f040504050d0c02220903110109050a1103030f0d0903030b1804020411040b030f0708061e09060604260c04050105030a030c051e030d06080607020604030c170c010203040209 78
    0x10304050070b1100099002645040007801031608100d508420300c00903442c0700d504035a070119110400000200b0b003240d5880b4490252180d00c410348100c40e01e1096500f610750942002e81940c0100700150045000989502c07141040101070ba8644113811132035000f250041106141d085585003061400c00d901803061684910b0215200c14284d94856444c008141c802013009000e81d0b22a07185071100c01814060320040d007400c00072541c50745400c1241c0510410100c131031000080196010400600700b00b840100f10907400301040800da0920010300c441088090052034200700200800181040108958824a0f0003040613000060070321140d24a000140c1c082103124a1800c1c004000c0d981d400180d48001c982d00d820160600b130102d0038281d040920701c4108ae41501e10610300d41010950200081c605402140c104010658030758a029650b0042102e925016a0200000c031340401e0180003100c001a204a02e101240017401c042e451240d040036a0402c5a41e4020040c001149800b40c6000d5108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 135722760 1250 135721510 135721519
    0x4141207030518031612031e050c0106050f0102030d15050a1502010c0e060a08060f040203010609030c0801020301140105030901020c01020d020909090d0e01050c01092109150807050a0c02040c0e0f 86
    0x4141e03c0031103c82c0d08400d03104140110f0900320010082501600400100d4941011860420700800700027074080d0740b0030804000203510f810f80200d120314008100b60302c1c541c0d06074002c508040780c2c171030414010204104882d081d4445207400213401c0d80c50411185c0034009070182d251005410400203400e403601201d100d0284039024203d24001d0701c1e540196400402c0521b0309001988610740407400d10100c10080642041c0001300200e40641c0040c03104044912486050300815a00c1440c5800c0b40420700910711040c00100c0e00c58580e40c07151021b1038015000c50001480d0401c010002ca00b240e102e00340b403c2c3d030150041030202c43e510f800049650711015402c041c2034001e0316802c00424200518460030b06000e0081601c010092095104403140b680c41801c00d4082c40e03081c000d031844002c2c41d0302c0d080c00003000c051001ca134204400036812800d240316107903004940c440c60415542900f111084170200000b0000c02c0000d81e039140140c0c2d00c0351500752201240c0c07840c0c074010300004221142e0081d008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 135724010 1250 135722760 135722773
    0x160608090f0309130b0d1415040f0204051801020301060e01030e031309021b0f03040306180317070c1a0709090e03090d0f15020a091203080414120703051803 69
    0x11000c0c040100c0d02c01c0b80c0200c4a00102a2140c94144c00030b19004882c2e40d0403822800c0001c00f00464440d240761140812421039481e4421040d10519040d4111401003505001c40b00c00c60050034650803054122100c1460182c1c5c6031240b20907242260002d81c403a070000341e40890070f0303034940d60988034020301d1a808002440c40c24075244040d036141e04840c03198031200e80d4005501501145600e618402c1c0c42d41c440107451004031011a2180d8030341107800282c4400d8940010380c0d84400c5210103450070329078143c940990010340d0301010018480010501420f2001d4036240740001f0305a1004501c100c81820b1300286241040b070720090421006030400300e00c0c249048040b011618000041c5c80c010b40b000c41d84c04080001da0301d8650000680580000c1042c0303c40f00c502c032641c12541e00502080ca11998440d12866620003412440303184c840009404104c0c0c000200d17000c566401c90340c0107200410812500900d0002d01e60306615030084070103070001031003c00d40c134040d00080d41e4040b00054084009011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 135725260 1250 135724010 135724033
    0x10906060f051807050904020a050306193002090702011a190909050a06140a0f1a190e0709030201020f060708070c0c08031305040f0e1e0c0316060809 66
    0x42c080d28a842e50101202e01c20f00160307409118400310707600650003610039510742605c500c000d411600103940f00c40c400d00c1030b045044007110490490320304440c0d0188800c8008410646c138000f84413000485840c404807202010000350304d42000440c014403aa900000b83c0c030341c441c01c213400f02100380c40d48240318035051030b110020074a41d2041030040d81c0000c41b00203101c221038541075107002d105c404010505420f0a64007801c3c0109803068501c40c4070b1100040c05081c0b0015a600211105109440000e40315240020f940f8200040c14001c84508070800203503d580714801c0001a490403213003400011080c0d00140b00b196414003054400811f1140100240d0500e5900500444002803080042200c0004100d040c0481d03070003130307400422144080d6a03036070801c00007000d085401c134018980100e06248030f801503460113225801e40c031104007000c0c21050725412200349130001c0f443d94506561240015035a00ba5405100c40b210b84116401c004480382d29006020306040d034000c00c1d030300d603680144e5881039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 135726510 1250 135725260 135725269
    0xb0304060b092406090405071e03020c030301060c020d02030a0c06030f020915090d0b1614071a0604020705060c09010906081009050c160303360209060409080a02010906060f05 77
    0x22903001c07115a2014004450360007189445c0108107080360300170305000900c20840d03040303002d03009a43d42d80c0801e44c116000c0150250241d01ca1440c96502a0780708000402c540c0340304121540c02a80b0083c0700041d145040d400091400c80c00d02c80c2a600754800d0501000416018031444001c1c112000b003c0d4201801180020f040540001400010034400600740110340e40b42259010310315400907240e81e03141081509000b103510300544510210303e4109046424030066810b83c0d04c102c1d071054401c0b40750f4580d2402c0c1e0f080c190700944403c0c2c025030203020020005009008461290a01c50510743e150039824000504205142d4024818020020f0074000802c1c070201d50602a039112030004155070b220000c81242622508052001d0013840c515500101981078201101da88107100d02242000da40042c207541510340c00700303c000d039800f50540140060414a032502d5010800600009100e141511140c0840d48184a9a0010307517507103503081c040084510410f00a003a021100e000e90605100104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 135727760 1250 135726510 135726541
    0x50709030c030f0303020c0d030b030d0503150f1f0e04060e0c040e10030c060503061003020310090e010b1504090e0606150306030f070f060801080105070207030314130b0304060b09 79
    0xd082e00c140f0800a40900d4000d130110b480e01a98002210305404141400030010550541e04034403a0050f06c4482d0310651040c0d05803409481403020102c0907108030401c20403c1c024401460f82c00174003008400c0b0036583c911b4908220b01c2400e031240c440c109014001c1004031241d9800808004c842182806400340d004425201035602c0b0310040c0e42107842d1003101c50001d40807580001c00045001c2808190700d5400310245004440a403102084030000d988150241c0c041124041010140c48004100d5411282c00095019078080d0001640c9440c0344003154007550f18a0490707100102c006010030038a04240300d280d041e809680301418007170800500161002d04400e03042801203e002c8041591640c0c113000407a03604101c1c8044620495403050a45a85011b0b4400c00001c20240c2c000007559280c10b01400d440b400e510b5024141e82411550252040030958482028158080c00701e452400e00b600700200150440d009100d440340b60906c0c10700213903800101118002c1000100303110240142d841318 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 135729010 1250 135727760 135727763
    0x70807030b0c07120f02010f0623040e010c0903030906030c021e2a12070b070b041b06030603020a050409020a0504051803070c0806090f070b09120f010f050709030c03 73
    0x441038036110b40498a03414060500007508110004190880703180d00000581d0762900e032500280303c0c0c0c055179408070044078201c0c443e03400b02c0c2120b400c0b04451000c0741c4000075501074008000107440740790030302141d0840741e00d031121901080c6892428414141c02c4401800103004600c2c050221a22607040203403a00d2101c2d40041384440003489201c900d0b6820302140f41c2c41c240c141c41058429204414042d42d10140c20403250146401442d9884507400208100341580c11880c0d4492604200e942da07030541c12001882031fa80c00381104c4010800a1001c0c451500500c41a540800d184c0d065004120706200d80794000c1c2e108074600743d03141c0c0040c0c50300c1421000b120300849000505031f949042130302010647ca1503848003030000142000800c05100d51010545510324125100c44d0303100c0c01c1142d0b41c1c1c1d91300c52a0b003407a5800035804000b0190709000611844c0409071aa80349111200300d51440c0c10301c0a43c0402040c1d4441c1041c0e20400300074881d06d5445013462070018212031841e01c8002e24200d46000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 135730260 1250 135729010 135729023
    0xd0507090e22030903061b1b05030306120307051608060c18011805042a03060515070f0804080a031416030804020a050d0c06020601090506061207110102030c0a1107080703 75
    0x80b0701c03d06008402d420011074201c8001c0c4880c0040d6808154000814080307000490308a0311209032140303004a100b03c0e13840d40031008500d140c98610030409036007120503005031684820490400050404d10488025841c07c924242545007040c14040c202013005010850095003400b41131210400d0042e411a5644203003455007845845042d0320b9520842c9801080c0c12a04104ca400ca186231180008068401d941100c1507071841034120840c1914214403a15600a03c0d000308420102107007002044001d10400004c078079040c09a5034800180c20960140b425508800201000d01d034103c0400c458a281d9643c42d28504000940600070310348450b5005000c01c04244006400c40d200c004050018100c003d003140104e0a40e0301d0144040700190107a0710060140381e000080b070361020701440e07026410060242d41010f40704180240c00c030308000c0c40442086428544615039a900784011030103020071034403995489810705405000311288103031425107503010280800c018480420200152a403165 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 135731510 1250 135730260 135730321
    0x1404020f0109030b1f050d230307061d010f09230106170c13090b06040207110d111c050303010b0a050d1b0801050d052d030d0507090e 59
    0x1401281e01080d1a04000c00d002c03003442c240030310713940c103c03022004c2405d80d4640e0180382503e070014070030403c1c1200c84c000d0166442e07a6007007201c40c0280041d9501d401c8010222414001c0301d4440c0002e481e000104d2a004502082045144101c00c0c000d40b034a081105000344440c0601c3d41d00e1850861700101d20f80c00c0b5000350300140100f26402c0d04918001e0005003041f152130b03c00421065254513200724043d2050542c0c8080d1a00000350b1301076281c81c1504040129840e503180f1041c04042d5002c1030302101c00c20300444940c40303156038820391011030a0144200c56904a44d1005214182030301c0411032407006410700b0348500081c40041100c0c151901400100d4682c49000070030799036405002c460010b0982480e05c03903110403004e00300102d00c124059482c454180da0380d03000e100e40303405140b6014100340c01c8a031101c040581010803503543c0340b01c45410244540100014181190092201012119110030500c20100d5004601c000a800c0603e100101418a0091600c1103207082c6807015a00350b046 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 135732760 1250 135731510 135731539
    0x303200a12031a03070803040603052413020d050f060901082113051203030f07030203190e031605010617010203071d0a030204050117010c0908070b0f1b0601031104140402 75
    0xc3c08044031280c0140c21521071130b4480345802d4494005000d4034000900e0f01001403003440320710300c0019a00344030250404070030340241c0c20b110030f24180552610b003454007005001c6c43c4d12140c1c03162600c50303807121041c0c0e0890f040106c03c01a450070b0691100490360701200c0102c0310035150f03082d0400040c044480e096a00c51400c0d01d083c1c000d40311756000315488001e549014540c40004801540301d41d0b500c80f480c0c25259596003087d401ca00080e50020300d0f14162003040c80d480480380d031180c181c0000360b004880c2450001c0d004201d14110383c030780440306079454103400c2021120700610748070440705841c025810361806100013070444104244443d504100c10103001c0c42c5071030b084070102c080c40e00600148041c0da141c8001b020510107641d4810195846e00e29a004020310404414094a000d400600b0f10507180414584c019027007002c4e80120351301c04101001d1102000c03403808201c1501d400140c0510741c07440c20300d12110f200000d42c1038010350800740c98001c0511184c444e5980190f0440d0003002c1c00010f03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 135734010 1250 135732760 135732791
    0x90225020a0305010203091006050a150c03020c0411070b06030105060904230a060c1b0b0a0b0301020c0f07030b010b030621011d011b020f0c011b0c0303200a1203 71
    0x50b94000342c103d510010034040b820388041108090320f28260000d00455070b99800b442410703c80da100c0c084000c0360588910841d18130440206404500078030440380c030f000000c00050101d80041c00415141080041c40720100300301c022400394070041c110000c115514026002c507e02000c0104028814018000402002c5051a15051980c07039403004564440c00703189002d80040c60141100c10100344030030300400d015000f001c1030b40000d0307501c0407007a02140c44041814000c1c21803070b0b0300554955020b20050004100821220701079009120083c01d6440c0703141031114a01c141030b0007013100420200b042001c15200c00843e5280408140c5d035030101041664005801404407a990381030300d1403d0000c8500210b07054000e0440741ca0858032075081c1c1500e070070302640d550700d5003804804107400c4590741007840c2d80907001d00c1c0c00d9207141a14a01132071980c1d59a0f03030051807007600100c0c01b00d031002c441d040c000c41e40e803004040c8800444c4004d00360b0180c2030b12503440354080c240c21002010b494000342d0441001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 135735260 1250 135734010 135734029
    0x702040c09080d05040e06040b010c08030703060803070b1b0a020a0f060209130b15160f02030c03070303020114010b04030503091e04020703050301030611070b070807140a0c0302010609022502 84
    0x801081d650103d203500390040c110b9019201c5e0050844124010800078946442400100c18050712225412181f80d59140260740000341150141503541800298201040c0000c04049100b05100700441c50300340d0301a4442070520a40050010f4140003010606400040f004c1c811500084038210340c00191a00d540640b1480752141d0300080500101c1c812020070790800c10101008851000f0880c44840460840307018109003424040406448a40401c4c055016166000d00240655a03001c0301b10380401e103020056841100140c0d0b46644280c402a041d210781d6014065001170945002c0c9180c964550741e000d445401486400d803070030310290419100812940800c400741c019900d4010504000e01990400d110030358669007050316007600080710004450341664400341860003a1280078007141e0b045030041c01402449405011404001c246002601c080c02041d6586010904c40d483e000342916481d500c400821030041c00940803e0805d02910703103c1c0014086450340707100d054000546e0035036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 135736510 1250 135735260 135735269
    0x703050a0225050c100c080c0111160506010e0402010f0302090d02030d030b0f040203280b04020d06080c100905040b0607020a09091b0501050a08041a0903040602010c11030702040c09 80
    0x220004140c0d44524250380102d0182e029000340d4500306111418400c041d6040303441d003030000c1c0c0c0c100040000503c040d000b52034441007800c00061060305503583d02859030310801c017505007070300302c1d42170002044401c01c0403601400b404044820907003090340c0045d104da12890045c006041e0046003881480d05d030f05481c50a050307002000c803200e0381d08001000d001041d1150ba400d0041000c600c510700281014021640200082c0c80d51008841c0c485408520035204000b03a4003066495000040007540c560014206241c007001d40002c00b02d29051203a0703d00402c510306140208000b85194803d07070340007030a98040300c4095901040f40c41c100d000140d003030f20566100943c00320a612012800c2e640e141d01c03071000140f142d441c1d1100c0303c1d1600c422500c9504207124090000784100064240d1510403e12540c12521901050054002c40101b0076179425040340e10360384a900c00319003003000c0341e424000c140b210402810000241c18840807000d03181c0c401c950000c0d0140e5224811014690f100e02000c00042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 135737760 1250 135736510 135736537
    0xd020d0905071e060305190c200309100806090a0b0f040608070906060203040b0304030f030f0c020d0f030603020f090c040b0309010f0c11060406050606090a1701060614030703050a02 80
    0x101d444080e042c3c0740c10200c101800c901d16a8500c0824801e000f0311689000d40121070301d2010603c105244500030b00f070701418803000c100c400c0035114403034400d900242c1403c03d0780001030342c3c451050b081841600d00a078140380b003c0080380b5007802001d072a58941c5a8201c1d840d0100405d00310001000f0607113100031541c4070f07900103140903c0003030a910049000d00035a945c008040c40020740c0c408041b60b4a000d0740c0110000f003401040460000782c010118049030114a05001c1054030281948904a0307003013584180150b0030111001e01c40a80c0b048800c00700e001c4600f01082801c0c2142c01003400351807090009400b0b45c20010100d440a00d60106507002084035000b61039a07454400d85080c083d2502c104141c640d50f082c50711a206450140b00705000c000020302c028140e682c0c407030311207001605001d4070142d0418010820120240c0303d219840c0f0280c4008039900c805402501c10107401c4840795807100040040780629081383c0d00107201201d0704240075180100325622000a81402841643c14900c06e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 135739010 1250 135737760 135737773
    0xc031b11130b040b03070815092b180803040320030118110d150c170108010b0a14060304030c0312060e07080708280b0a1e060e03030d020d0905 63
    0x3001510303004058015003d541c144050103210003495500c480340c0c0140c1119030840e08041528601d41e03180e06034402d810b5001c40f02d01032403070f45000307540003100109042c42e40341081c0028102504148a10151010310404030781003450100c40644900032804000d0014ad5694800210400c444401980b45200117000300918815510484a60212210112541d0f890660350000b41d2030705d60380c5080f0081d0070196030380c10501421600b800411884080c007051241d04892541c1c1e2640c0c0e100224080c041201c00000c8101410081107540f5415502032084006c00c00d0200743d03107485603000d40ea0004d5050514210b41d240502c2d00741c1d05a00305254401c3e82502e000000140044034103049401040b16480d46281d503103c1e02d40845a048040b900040314003a2a03441c90040f0245c014101070500c0c402d1000960802c0c044c00060000e00340e940b1059841c07048807030300048140c1d00d504000041c0b1050602d0a108102003003c6500d9000302402500c21642c00300b004042d10065801015929038014143d408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 135740260 1250 135739010 135739039
    0x309080301140909030f1209030d09060c02010b22090201050c030307020105010e16080402120a0b0c0c011104120f060e0d020a050601050114040302100516081206010c031b11 76
    0x2404000c205218494040a401301d000c59402000b02c661b0312075210075840c501503902c0340c1042000c0c005003400c10300340300400102c0c510410313600c2000134041c403c41c4040740c0d001480c98000d080d1811001d10610440300498070058060340ca0508600000b0b04100104403410a40010b031443e01440d9060019404008100414140d0650000341629950001c4503520303100d11811080d80d42c001004800031131580c0003c50058a048018500b2950003030b8102d40c03e40d007081e600c81030070100030b0b200d0204809012401c2104c101080c042c4821043c0d012281e5410030380f904c0f44500c00444e5405020f4641020101c488041c80215001201c03966100b00c201c4800d00e8100c0d5009549001c015400d80c1c0c903020b200008550b6601c120210740040e4940107240d0f080c00d0454082141002c4000c06080a22504001da070803140c1484840882c824041c0710080e444500c6040d25140000005080c0782c10003102140f0040000d0b045000c601c2094010089400036000398900b910030816000c5c9802d9204000c1c204070341c3e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 135741510 1250 135740260 135740279
    0xa080102031e0405150a020904020403030c14010e060f06010c0f0503120f070504031707050f07080d031104090b180a06031a0408030c1303020d03050a080708011a0a0309080301 77
    0x500410005031011004420886003a54900e0b060b1401095504031000003a003e0b200325180c0d13a0000303616040145008980c0001600300d81c400e138401c8020402d40c0c0009820b00c0500c00707500c0709508801c80280060022040d031942c465500415070b101c65000c420114074540d1043c84801c541d03644c080e18024a002041c1045a56904000c2d150541c0e000782e8400541c0100120000d14010369154031444c0c10907007199030707610000c1074151450024041c1801100003195080100341080c000c2140513004590408542508144250b04020181414080d13001140c248210403074003107601500000440d503a4403400950b50507200010742031114140028090800481e07030040044a1207000000005610f04400d00012402280c018012500910000380d4580c3d4550007028004401c2203031008060f01da03400901c0c185109241607001580101d000034055411451094100f1000d042c41c0080350700d049000307040c0500c00010000002c00c0821808200c5010307402c00c00886030b00c0715149469685070103140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 135742760 1250 135741510 135741517
    0x5090d060e06062b170a09050915030a24061509140f040902060705010906380103020a03140108010c09060921030c0501050a0b0906060f0301150e0a080102 68
    0x11464001c403004100e80d031604030001510090980e44000d869000540a0041e41010305000d4030720f174a071400b10001540e0010002d020220b4a40c5030149168100307800c0c401c0d00305004004031804602014003802a503000201500e1a0f64800b00c00324041340c400c5043e0700448a490784500155080510100d900f21195400501280940d59601103480c0c3ea1f41480d035401c9140c4100f150004410059080c1d50701305a00b05000702400900224a400310907915039003160640c24042e24007943e5114441900c43c0040c0d000d001d00c01400c682c0e9a4003c2d002d210440659059003000b40c189503000900408550084d00100130784603031111110742942e55101058042c0200380f40500c0054924403001c20041d00034001c2134243c903d600d010000d02c1a48911414001010407000d40078414044610400107100b4018288620445c0a02081d41b8004105114852401400640c032841003400030807154000f01e0203490441e8020100c1c150300584011054621100310300800350000780d2101c0101311503005400a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 135744010 1250 135742760 135742781
    0xf06090904050c1314010e07020304050303030a05071407120305070909140103061d030d0b150d090501050606030603101d0303010312080105060f040b07060b12010c03110a0e010c0305090d06 83
    0x70340d4131300c0103048030501100c0c0402038841c000300445006000b8042010f0080758400110b004491030a40c44500081c51500101c1d00040003940302d80800c25690780c04819180110802030400381420701d55a101c90040c01d0400d06001016076400007d200070f407007072030394030018042030b50b0421000c18030002890b5606801d010503186141454100c80d0102c2c506004242d02404240c041d50401d001c030141c0d00d024200d840d100c207034441c081c1c4500c00008038004000307051110780e030070700000c01078403074a050b50135120300528541c030800c000e20821030356450111f02201c0000d03066400013054001240c81e54038004118860440a2101000100420840040d000101c20190704d4004240e80d8502c00c108092203a401c010a00740c00030b0000b0031541600300d004c0c0400714880d100200d01d6820794400308014035420342c1c4410850b0344404c0b0801c0c00340d402d0701c034005c042c10102140c64601050010080d060054904e000c50400c8106054141414822000c2da0b80c51880104100c059030420300744003024001d40c001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 135745260 1250 135744010 135744019
    0x20a020c010329090a09080a121a0108130c0b0712080a091101030f0b1306060e010905060f0705120c0102031605070b04170408100f060b0301030c03020f06090904050c 73
    0x1105090025007100300040c00300d075141007440c43c20140c014083e50000182151959548540351100010440c2e03000d0181015070307940300803010011038244800c2d0b95514481d00d02d406040d14800b251030b42e00a0704c9903845803103a03e41008007006441e01300c01301030241d48080000c19000c50032034104440c2e1030801022800c6560340401c243c94001c0310004032400c420000b0041d003e80c5c450f40d801c40d40070341c11100b01c400c160640061440480c00200344a0400e004030700c2d4400395520000c0c84000c1e040701d00c00241e00000c0c40c0000d600760610002c00d04030b20440704444000080416000708000c0100050254101401d082c076403500e07034506200d4040c1d041965038111030300c25840b0440c10300384660113a80386075410409040c07040d151600c4800003078008811080c1041030030030005c078245604200203103510002007000201c052610207510100c80468200210b41c0c50100010030221300b02c0c9104c0c1080d00d404950900004c2c0906002805500c5121b15694102c2650000c000a0200c08100b0b40c007003103070658 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135746510 1250 135745260 135745271
    0xb04050109050909070303031e0515040c031107060b1c030c05070b0f03072a08030f01060c030f0f0905040513020f0906060403260301030503030907061d06160204020a020c0103 77
    0x20204250f0720001c40b1580e801e548204401c00219210750005d41e00350303240a00b068000340401a60100b07445c02118000e68841a1003c164000d0a00e441102032100e0207240030003880c0d103d0512a9128491007001a02c0c8640ba94110689596944440651442040040d4552035507078078018000c05c0404800351b0303890007030321000a1401109400c4401c0b842c1e01c581028a103968002e4240c960641080600e02401c403812003c1c88074200405241d600395000c7c911340e507100d14149030039070341d500d1058014404110307000b02c07250b0000b40c019044c8202d0b0460790502c14030328201c880c012035400c159940711685c85420070086c05030180315007400050fa280241d07505111009547c081c0050710506507034458021008000400110740c0984662000c00c01080c04801c4964980d49900f185820a030030a0b541e50300300209004102204000c000b00804450078105100200c2007546504427104000d4203000d42c0300010006040c072106c0f0020400e86500410031500c03500c8900001750b0b0b9800c0e550301280400e02e4034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 135747760 1250 135746510 135746519
    0x703050c010203070206030703020c01090c0603020d0b03010b0d030c030e100c05010f051012060f05070807091205030414040b0d0b07020d05040f030215070b0f0f060607170319060b04050109 83
    0x4004c035107000c1d40150296207151640141240291701c1107180703260035566202881c0000f04404100e8000301880c1d0b0b40541c4924180034281c2c11107801141140c4030360700d080142c42d61603c034040010034031501401d018982484604094460510042c072850340f09070700c07200000300e090300622820a0180501d000f08400a014503074007044945c21740c0d0110346903518100400c00c90341c0c515000e60109219600c0850004c0c0110b040500b030b65004d9031410040740301101041070996100302140028028000c51006805007502d8064a912030340c001c50034400c01c0c0300480d010759112504400344400340507000240e1540141000311540800b030710300c91f0040c01010b00c1034007000d104006950584d1a18603010520902e540d00b00801d205140c40002210030044c0040d901081e45501d0541c800d100000c580030413840d02501c1031710311980041465124840c24400c40002c0343c10200c3da2030100e050990050759a40b5000a10310311101148407a0001b80e007030034004200d008200b8068801c840d000c2c0c07100c6003000e842c2d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 135749010 1250 135747760 135747763
    0x90618010f2303061f0e01030f060c02060c030a180203100f0b040603020619020c0604080a060b0108071b080904061409060102013c020d09050c03012d0f020c0703050c0102 75
    0x92030b0465060744000c0110318060011105015801c0325000084e180c150380307401c10b00744003a0990080e40c0359980055003000b40300683c003a80c808030704148003400f258a48030146060a0101a0200b00e0141c1d44610000308041803016500750150010219040d41d483d58481c2c030090402c244081024509100c8148003030b00b0180243c0003500d5000b49901c0c140f244403248a26101c000c010100110f11900c00c48103c9a11650010000303046807001600840c105402c10205441d4081180c5041100500400400b5a44148100407118407200c4060744d01d4028189020305000f010300711540285803010000d2882c026003000c40081005072110002e540e04c51006900b21038007107211220503d0741c0e00c004071192803404100d070280301c1038520b05054084d10b010100d04076007144041c516002c0e034035140380c0c0a1020030031500c25402c2044009001d0700d45072828020740c007200100b50061180c001c080700324101455806c404840748080c1400c5403104400c68000f03a45104074032054806010700445000107510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 135750260 1250 135749010 135749069
    0xa030e010b0d0219210c0b03010609140121020a0305090a050d050f041805040b1014060c0102070501090b06011b030504140d06050108160e1302090618010f 68
    0x1401046180b462885400340012003640b020708000c034003203003000401c002c100000501007000000a50303030f508850301e1400310011079554101900c000c0c01030004004407a8020000000d80d605500c000d00708542c0100141c0d081e5030212402e440b0b031702d040d0140000b0300c0090b5000e040907503000d80c3c082c81151198025607440c0c0c40b1242c1d001c0c7c940e81005441200441c051360007490ba02000d206c0b600d242580e81c0c031151041d10511003011032160380f220140030900110500c615040f00251998908823481c2c019284000c5080082031401490082840c1c07000820030f42c10f440407a07411000a00509040f440c0000c1c0d001401c41e2a24041400e07407241c602c049400c50050304440f42c0c10384030540350034104103060301c0701e112600b101540009168680c200240c0107000b03490081040c074000b4203008244a6511902c10521740201c0414150201041242d21030808580e24213501031700d0340c1200d500c660001c18240c0d02c81c2061002010303a0750300002030942c41904410112056203900081d40c103210000303518040b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 135751510 1250 135750260 135750281
    0xa050d120b011b030305060a080328030e1c091a0a0816090905220b06010306080a0314030417040e1603090203210c070b03180303091009021309080a030e01 68
    0x10201042c3d8001a009034840e6030080307401040c0701c013039a039580041441c40c0e0054202e0030114030940807410900350b14428240b43c080f00e0303042c244022041c284c10559103000a00108041e800b02c1112500018013681545001e810440498071401d040b22403501305e42e40c0a64042000254401e000a402400c00d242003010b92050380c1d2030800f2945800030240180034060600300040c400a0f40a500d4007540c202c2c50320206104400150092070f04d1000501110f0301503000501071380162a40d131000940c0445491030440350051010b46a888500b03104606814900049012410000700450348540c00840d40d84260100e032225148805030f064110700ba5034141a000350076601c02e124140e140c140030280e41106400240c2c6050500c6924188285403024a50100062086c0002448080704010315200180d042035002035155082c00c0d10740c00c0c0c4d1070b00b180a2909041e0b035035080c1e81d021983d410700740c04604215000705001007006410204072540c004c4010310082860b004d5a4510030906004011019 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 135752760 1250 135751510 135751547
    0x30d08010308040b071a0a0510170d05160609050a0606060306140d0f02030d0e1903050309090712090b0106080a06050f01050901050c010501031a07020303010b030a020703020a050d120b01 82
    0x10b04c1c0580d413000c0d80d00018070403901d00b480700244010303010002c07840601c54041190082150304100d180b841c0d440003260000c6940d581c0b840b054105003000018400280c104a01c1d01c01c1c0c1c1d07443c000d40f03250880042d000d001406c4a040c1002d05051000001d8801c5040e80106410490705948601c107400710b6074280304119402c841d8881c12a01d500c3d020240c02e484a02814403c0c0d114003103540041d00340510000290041212518485042d003009020300c29403140981c2000748040c10341c2c42e019600e0103008042031061106000141036030380b00e00c04041040c09000e4092150444515000c900080c00740208400643e034140010328001d5a4083d120490301d025040c00d5100e42c108004403140e0b4402c60401c0d040c04030801540da080d581c00d1003a24020350150a009010b03890b08840c141c14a10041c1070f03071045510a00042c05041d500320300302c80e0451152100160303118034900d42641802070110020b04103000d61030421140c0b40e0480c154208075000110100b01a80d0032038010f403000e002c104c0d2540701c40d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 135754010 1250 135752760 135752767
    0x6070507110f0d020d0c1a0708030a05040201050c0a03031a0301021305010302090a0302030a050a02011b0512071703100f0501050703090e06030307080d0b0f040c02060a051005060414030d08010308 86
    0x1d4248010800010040548030304122000707900410800483c0e180115100402d401c0208a6829a0025011070030036174401c1d1071401085440710300c07403404040c00311820641c1d1400400e046a020300210781d00d1054840c140c440569041c1005802449400c101c1550a00b200c0003000380c2d4541131084070040d1000c01c400b00c20a50034107004400075001980c03a56007060407001d010004d40c0e400c0001c140e40c1c5204070300030040e804092000612451040c080c200d0121407041071100002c02c04902100c13400090865035403a01d0650401d2510316130704161303005120100005000601541c03c0095065a111030b0000071880d960700011101c511500001400040d4144018001203540389665500300b200101200e0512805440c0c50758194001c0c040b0314412030756020310031901d0401c0d0302c0440003200300b01c2c2c0400014041d180080e46405005006c03540295964002907000c0d6039146251001e03000c01b42400e80c0300c2351209040c812405145c3c6034588a403040c0c03201c03408418420b4000f14140c980c000d900030704 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 135755260 1250 135754010 135754043
    0x60804030f0908070b03010305100e0a060b0102010f020703020c21151302100f08010504050f04110109080601080f070b0c07030201110106090507051206010f02120d1d0f06070507 78
    0x8901c0c510345581002c000c0c0010700091507400400045020f4020806025503079491032900601d0200c00c0c41c0715455444c104407104102001c0425003d818542040c4045040c0341c20900403801403403603042c0802d603148041141000d06900103034070030102100340c03484c000904204110000039031442c401110594400380c082c0d850750045110343c6401140c0704443c41c030200c696a000810190300d000326280014140804181c500f54000362203070040800352400c100e2410884040c1d03200140c020000303840202d440d201d0b0b10650f4490194200206100c038185c42442d6110503400b80c80300320300a07410070345d80b00d045000f19081c90300724112000761031349200400351140785500642c0c400112013a8584a0355861100086100241c0150344c4950410342e1002e540b03103080e400f440b4420002400c480d042024218810100b240c00049444000c4074078081291200103100082000d0424280c080c140d9200000424440031000940092603120000c241c400c2c5546003641200c048c0500f0038090b1209032003402c40301c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 135756510 1250 135755260 135755267
    0xb070e030d030e120a0302130f0f0308030c070204050411030d0801050307060806190806040311012d0f09060911010807141e0a09170111070605090118080403030e01080106080403 78
    0x10380265650f040c0e030885558180032450380d0300301d00070304408290002842e401d800d805008501c05890702003000400c89040860581502c0308902008046d6000000842c0c403030350207a0143d64480e9802072091020786807914010b182c11581012182c003070b01c900f4100380c29060182e24854141c2d20003070020002c0e140f600c0c1c812030390010007801990700b2035249040d012205000000d01c00280140000800e810f04042c9802045492500c044054691510080348a000c00f468120a0721401d00c110142c2e02c4628000044002c081c2c2c00c04a84801e49050948010488036400100807640181903480000b030b00d800041d100c0c600200c030410000750302190104030205508002d40041114507a4103d2040003400030340c00680d200101380c202003070702c0a6041000903600e200c1d81d41407604140082c00004010040d8011601139000c1c0142800d4403840029081d80c1c00358032100324000301e000880e01305009410712003035a912074041500001c1c0c3c0441c1d020244e500411425049541c6541d80f5012540c0311b45044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 135757760 1250 135756510 135756521
    0x21302091c0302010506090606030f0a0f1b0e180c040902031504110c0124050d11100801030b070903020f01120b0907021623120a0b10030b070e030d03 66
    0x90758420081c959038220a1502000000e103248a41c00000e82d90a11070108003030038600600081c4260b42c20420001c4003d4070a4034543c00030b01e40c40001c01c0d441078092000700074205041d808201400009201000c0c1e41e800f89002c03c0303000c410303035400780045c5064500180340c907000c482800780b0001c108020060905250f00450b484803806c0f82501140640a000a0a540c0505101c0c0414100490704640300d0303e0a2041080f8080160343d040d41541c560100c401d01d1690600c6654840c0a01070391442c10700012048100d00c181e0b0040c511060b0145001c0c0c0982030380d03000c2c00159100401d01000079a1140280203407010749400802184d11691074100441d40c0210314600704520a4071902d49200782c1d112010341600440f15034001d4100001c0c40005d03d40d0b01f051135405070200903c210188150490b0000141041200c10307100c019108030f25048051502c141d02d080102003206c17450402108400700e4903401c090301d10544141a980e203900308100c1d4041d9401143e6603050b000b801200c400c541c001e6000c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 135759010 1250 135757760 135757777
    0x304080a121a0f010306030b010512030f030a0c0207090207230a0204050403050315030111030711150406020a1d22061805011706090a060506010c020310091b03021302 73
    0x40200101285031220030366110359407044071003a124502c40e0796403a000301d80150588080c41e08020783d500d1034482d080c454406107d290300070700041e504c64511542c00d004840c5010000c3d900280d903401c000001000514400c518800140190b00703002c076165086000b207070a90750708040c460480c2451610410802c407819107242c03145200c0c2d281c14600580b11341c041d0700e100f01e020b0b071030300d075100d24261031160701902c01c80e00b0b0b03280b1991400e46483c0e2000c88030b50580b60410814901050300c0507555150130700c0c0004c15040a100c0814030b104000030090640c001b04a407111a07a00c400b0602c2800c842041034078102008107910411070266000c1000c1440901008c00c0c4c0800c601080704ea94883c0450410716502c40b0084800e512a801803004096041c04020901030180090130703140781c580c16603521002c1d4600001d10f2135488901082040e0b1080301c106c21800d400406940a010900790a0001004030082c2152504e2826031448a05003d0b40c1c0b00b081100d4003d80009014088440c8500082d48003004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 135760260 1250 135759010 135759017
    0x90103020c0105090105010e0a06080703060203060f03064011030115030303020d0501060c030f080403140c011e02030712050a411005010c330b030102040305030304080a 74
    0x10011081c40900580340500b000500019495052050301410f140d801020f642469041080400c14508005580c0d030890703030090801600e81e1140e078006810841888210340e8548114814080385815039604803021245400d801942d00240c4003da442d41520005202c0c0c199014030707560300100d00c544950b0030719080c0c028000204208484e40410318840650002c1c0c00081d80864031a59414161141c14098244c5041c4110104c00541c1c00400310034200303100b02c0401c10703900081010035020701c3e43c1d143d081414816454495507600865030003009400b503901c030a80d80c03004410001d2500d03803007140d0103a02ca9030380340881c02c5441c500c0000501400340984405c035076158420070702030310850710842a80590034017058088050b2443e6040c80e500d4801050f0511821030306004d500e503e121003d1049490a00f41151405103d080080c0d40200d44039285082444002045d40c00114142244048402102c810000ca451a4051600701c0c00742c0e0000510942c4100f02003001701c1d100d9005002c0020113882e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 135761510 1250 135760260 135760267
    0x717130507090603140307111e060313120e0f0d1a04030207030b0a06050a12081608031e041203180501060e07030b01111e0c06070b04020910030b0c09010302 69
    0x58480e80303852026400304015983d2514140704010700400c00e0944104124000c2d03050442645170884a13135078005a0510440d510707007443c0d1617412400724030401007400601190f221300c0e01001c00d201c89100010115405541c0021b110001801141c015101c18800351003002d014800c4801e20206084584050301d80c0c41144d2220051102c50b4a401d600c00e510a034003030010685913183c001c3c10218090020300c500d0341007100500031900d403a12500111070814400c48410a0f16003003a004620079801d41e40079410700f2300c90040c01c7c88541801540600030f40910154900d4008039035041c0c45038259401040202c40c0030b44016514031a40048018640800340e85103c0820781d51241d0840b4001e0303120031100a185400c024416400d8400c0001040c0282040c0031440c41c3e108246481c1c8040c61501c080741c03149411450a0524200010341300c10340080c011a541e2640c0d41483c415140040380c080f8800d0a514000840301d51100284804803580448901d0700382c2c84203e015085038000b410b14504056091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 135762760 1250 135761510 135761513
    0x7030c0203040302040612030f050c100c1b11150c0a260406020a050c0105090609010309080d1401090e01090209010e070c0b04080a02010501060203041a090a08070602060906060306071713 82
    0x51080c1ba0082c900c420405c00e040850f40703070103003200184941a106019080c080214138000204060480c140451000192080380e20b00a50f00314000c018014200b2003840406c03410040b582220b00714403d001c0300c0794140c22900b8840d2042c0d071311070a181c2c400e0a400c1109410005407108616202100400300300380e024920380703000c1c01c1840e003050b172090300143d01404250061007824040d05032202020301c1d04901d000181e0010808902c20003c500f410181d9540b620024440950262194920003540621240596540700049540280100b00c00d0340c0c40c02101c41d5102c0f00511805d00300d681d01034030f11901a840d04240c2000300038020040300901401c1d1b03081e1350000d4220101180b0071880703000d00c1611401440000ad0858034141c00136000e540c000c0106200d600340d1052480140501d20a0190b51f1340d00090216001203201d521030025449200c1000c608140c001c41c460b84246050f00840c0c081355500001c06da5250000c0d1480004600048050b0034507040400a0326032005c4c1e5112003010032a1076 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 135764010 1250 135762760 135762769
    0x3030e030d09200a030b0f090f0303010906060905190b030403030209030d0503011d0105010923030d051215061602010c141e01060305030d051f060302040609050603090607030c0203040302 82
    0x14042d08448007103010320200c2a40800307142c0c1408215003690742c3c0ba501030450b0340e903c410010103402420f0240300c403000a418030204000090480380c161341036035140c0d603480c0c401d40040c02071400703a80c010a480340b1001c2070304e0800d1401c05942100c208000420180b600719004001d6102070001d50803d6000c00c03003118552003c01c51c1c1048181c01da80e03002c0e540d40c9080030341b1f2040403454170000070514840d0010040380e03034003250745000d946001f292945988404202400c912040c1900c590309401101b001c060841e8000d801740201c3e0341420301d03c03151031340c6240520500302015030810b60302000602c025140d2803040003100d0022407040c140710340d40b11030f55103c802104200d011400404d60025100c03190702c550b80e40d4880103030314425000344901c50450703640c44d07180e000300d030500040740303640f400003440c5002d0b003600003102614240c444024103915200028060361040c041ea0000c1aa181070000700d50a2903801c480c4904d68000c00303042d0544480404402901d611451001144420321010001da504c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 135765260 1250 135764010 135764021
    0x4032a0309051002010c0c03080a0e1c0f0503100303080a020f1c23060d2105091c0b061e060a02010b03010507020102190c03021e0604050c0901060c03030e030d 70
    0x1e03190514160b1800007089514051a4a40360071a4100780b04811503580111541c100d41d94103040450300c1390384020701003004100d01030451f2114400c00798281e070014040042d00e4104d100701c0c3d4400c00903c402c42c1040c1e50900c0140c903903005281c945d00041000c644100c81c040e07005028100301524001824000b0080c60700006520a2107041e13036140495084036510030040d810130320110b80c5101421304800606011402400b41d8000e080580a05d01080000440c800c10038140c1c0301c2e040742c00c020366103004102d0b8100504d158007503003911250f0308140c0c601c070a551079680d038401000061039a41c1c1d02402000002c48c18500001244402c1015550342c84d41c01415803030031103900015605004000709802e40720302408001c25640f0401c008443c030002c00b8413030514104241001010030825280c12440d109181c07001c09485d0440c1e200c0300c0c1d4690000b0540a0040e4001c02c00c03074038203115610410000090a03c6602d01141c03400400e240040c4c00b0390042c4c14440c0150080d64141806070402505465 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 135766510 1250 135765260 135765263
    0x1b0801020903010605040501060509060c010e01020c0601060207140d0816061107031b0b0403050c03070b13030206180601050d031b0f0b090601050a09020313140c010f02031204032a 79
    0x25000301c1e28010300c0c1002d100e1040108800c803402c1c030183d403500d400a0201e21605c005103014000000309040041c1013500000040035410008550b40c509041c0040d031141c00a000300c10040c01046000a8000074000364402c1310f0300b00814105030a80743d565500d000d54040010340c2440310f03a00702e0700c0d0040b8090340f25101d80c10030310a003c1640c415003458010800c40c803514000925201001e03131b09011520254a0075031080e4142099542c80c07441081040c5076015440005002c01d1500c010807820346150924110464402c2d000c407041c6891301041420103b0611420311000d07800040100072500e041c00000c81b5403402401c010305c9010160300250403000140e00242c07614810310b032004042200030202191321140c1076000d8540c0f941401d0000b14011094814800b031550003102243d821a2a8000351000303e5002800d4020140c14144407a26500f0f00c90205021070888545082c049001000b2205004e089041042490750789c2d95003910803060010410044825842c040005810800c2c0c0940703005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 135767760 1250 135766510 135766513
    0x1407060906022109040902061b1f14070e0a0902070602040503160b04060c0201110d02061501090302030a080a050c0328031404111203070b0925121b08 66
    0xd504100c8060301e0f000f0f41c030b020007111800904500c0b002d0714221003640c0c02c02c001194080380504240c00020700c24050304554448514075101c41101e084c01c00204184401d075801c18003543c88110010000880c1d94090f151444420071000003081a8400c00d006405044003c107080c40c0316441c4c1d04007030100c5c1c00004040364401c1d4006000e01040c40c04000e9011846446120304000701c1c102a1115128080c40c820a020b0201a1004004583c0100505404040980c048600c0c0514801000b59202c1d016200d64001040003c01d4051a5104601d01d4050326000b0340180702200d02503440c0038003680b251240ca81001400d22101d62040e2041c4014100f140c1c241c000c07810040324481c0052701c10030ba4054241e05152034512402e4035810002c28041d80701e90408440d5000b114044041415040010041010f40c00001501801c02900c1460103002311005030803180e480050741d0840702000c00103a460a61300b40182c0c810045c500208201111481c42a0883c3c1400400f030914a525491385800000d00c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 135769010 1250 135767760 135767777
    0xb061605010902190803120907170105071202030c04030f02130204120c060201050403140a020c04020a050a0e06070c03080309160e041b05010906050a0203041206050415090b070c140706 81
    0x2545000540e0642140c0060001e000c84c0d03140808969491003519108014100d00800050a41d8806c2c802200101203040c2e918404c400035090b018001c190480d140e20100341c0305030318904c1c00c0c401c034425a40b08050542c159440d260858131080c0b05480000c078226882a2800e1110340000d00034009040249500d491844000e411403600b5818000d40303070841e5085a01d08001c20010941c0212030700f8003a2031040501d681c44003904012801d0010404500e50400d000040401000f81c1c00402890040419522288000d80503070802c1080e00c50140007400c400e030034190034008114184002c54101004e02c0c120354560440c0313000d50414400c20340c0240c0c0c0a100410400c0240640e07a01092880c4040d11210380e001d9051000203445182a4001c0c0d1007004000f2a2000c4094000c00407a80588210311858100010501d030150242201b00e40860f40c00001016030050b44526005503a440e55029043c40503036030b64194200e8a018bc0300d2403c0e10a40d4005c50b0380d407511401030100f0000b900785a5550401d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 135770260 1250 135769010 135769013
    0x1e05060c060f070309020901030b0c1909090e0304030507090507090e04050601150201020a08070f03020705010509060a0c050f04060c080403060e0604050f0705060702040e12030a0209040c08190b0616050109 90
    0x200c03010020b08810031305003400400401683e500522605581c1d010742010302580b41d4100c217042c00e0060107400114002c0040c10580003540050300c402c02c9519038078080c080203400420035a200c1c007a503c401442940651000d01441170950407840c1d11110500d0817034030881d5501d01584001c0000c0c2d070261542d0b0001c00060001e18003a00505541d840c00b400258038005250000a02810005220700104826801c0010850b8401c1d01103a0150790072000a03c143d0034610941a194603040e2018203011346070030000b4a015020301c0070f807205169020300c0ca6062501d003a500360340c3c0840c20142222060f40421020000404510400401c8a10000203023003600e042d10780140381c00d044c420340103810b80c0304200800003aa1480d04440900e0f0b4140e44c0400d9124014001501d00805501642d2030410080204120207140785d01501e50074008aa090055503400c80d000d8407024025112904440e0140b01b0a0314000c456410014080c200540580e142c00514100350800c00841401159280d440300d04200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 135771510 1250 135770260 135770281
    0x110f03030a0e13110306010e0319032a1a0907030606180518120913060e161b03030c020a021003020d0b060306181509010308030702100b01091e05060c06 67
    0x20265216a0420130740a95106a60260100034101410400f20b9080031206032424044440070001011848654107054a4040d0000401a481103100c021b400c07005140c00c0c1c80c00b45d101480e641c100350300400550508106280c03cad0700041c02c5048521892800000190040c0300e40340007462221808000882c200500000b907030b001038030084000c4140034100d03000310740218541425003c01c20710b481d650280103001c40c80e074501724048286002d2820304001042000030740c4c594403440e180d080e403143c1600816000e84500480305946070304007190881d4100000c0c001d0340a1646141c0d2401200d00c050a50350002d622400c10144c004000b0390089401c0314000c0840c045c3c501d0070803088072610300714542000801e0400054560100f0503111a0000c5203a140021800c4034000c00c000c0c08a0483e50307100e04100b5015030040e147ca00040c0310740880d0941e000c800d17100303140d500c1005940b03800441e444c040b00f200c40300003014285203060410120005d07680e03075010f0051842d90422000380c20185000030426 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 135772760 1250 135771510 135771529
    0x504050102010b0a0e0a1d0115150813030509061315171308031305030d020712020105071413050409050a03081303080f0a0b090a0e060105030712110f03030a0e 70
    0x113001d0704e15a80d06000750140901d10310382c4800c1141c00000c45c4040c001e010314940c02c05410700c04a55280c00e03c240341c5004682e039000250707240d080d411140181c542504660820080b144201c105422880a0000a00c43c20003001012002400103040107000341040d40750280319809041d003441d07901104d220482d044844c038400c0b9a0545181030103032034241d05920810459010042c003041c000000103006804085000c4403160704482120346445170295008001c2d40072000555404003500d82140c100e44c41402902e10074081c0380c0d19103003070f1000060a000d0300c6d00002c03082e00c41403c6407100412652540d01c01c0030045801030f0024a50030209050141541801920303c151843c500e800c200c01103034201c4880ea40141c5c0000c0ba8245907551010200010300304e20424581c41303803141d1b080c0f1071046243d402401005180fa81030b00c0c41e61741e171340c01090b58880c82d40c404c3c80c03008583c85400c01c01049008281c5249900c001e45894160f204001c0040c0c11a0701407031100010540754500820301d4201000c12 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 135774010 1250 135772760 135772781
    0x6080a02040e1317160c0f031a04110d0f1b0e071209020411120108010b0310090c050607052103010b181302192a0f0c15050405010201 59
    0x8500d040d0811401d000d400c2c0e8000c01e80754461070316410203010000b00b00480e100103184004801d490710042a4108051300c014401984d600c01081d402007820301c1c1d074038009003c40354090003018905140b50800e01099000610940315140e8040c04820661a808907111040b031084000441e07104041c034112410b0980701042c0c20700c0c1c1450100c148480d5007011340caa40c04c003541d070410002038a01840440043c0410905c000d403c24146070b00d140c2181c1d801806800711540408a01d011680c0300c0c0701e03507800c0700e0b80f40c1708040d403680c801081c000300c44019501580e001401111030224a9440b4004958154030528040314164000c0c01031104255044907a1082c200084407550b10b95450800321402c2c501401201d14480741c2d510341503480c0c55a4007803c0030f50f0b400c0352030700554403a1040354048580c021405500340100e01c1ba244601101c0b0390b0701d507121449468640300c00101d030321140c8035202100f168000c104e40c864030701c00f00072070134030a04055107803540c416035102540c0b141060300080c0cc0d503203034096 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 135775260 1250 135774010 135774031
    0x12150c03040c0302210304060f030b030f030d02070203030910050901020d0f390c0611010b090a020c0a170405010e0d020904060c02010f06030803010f17030904020313050d090608 78
    0x14400000c0c02c0341042d600b00c980484103121003001d10001500f90002044000150b4400054001a0190071030300044514216440c00c2143c5074000d410303d900d4003148074015039250400c0003554040c2582d079000c0e11072140013800b2241000c2c500c078045003445c0064076021021440c0400c000041e903a0422008012442910b0b0190801008240c00f5001c06c20f03980810640703900c5820305208210000c8440d824445001040620001042c01c050341034040c0c601600c40020f91150303014098038014001c4600c813010141c02400c0d207540301c08030400290410050214180280364102001c910000a4001d8411914811907030300e503d000000f50180840b035100304c0c083c1e41c00d407548402507500c1221107940030f60807240119500150040807401005502c0c0b02d42c640511b40384010041c085014081c0d0305840944202c00345054559121189805020300c07900341d50741c020030080c0c003030781802e80246070055602e4145080d0380c2d0705581c486050114440003030000850114040044981c403900740380d080854482c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 135776510 1250 135775260 135775267
    0x1308031206100806040c050d051003030801090608060c09060f2704060b1b0106080a06050f0f0910020708131805061504060e0315160f090e01060e010c0212150c 70
    0xb440503191040042085215a90350841e055100c5d00602c11a04908400e103c100503d03c0c1c02011801c0300f0805000550004400800108440d01180b244100752100d442c0200166951070786c1d18043c3e40c1c449141705030000c01c20f0102c25526150f0402500000c003130700c03c00342c3da01d4a0224100d01009071800d0000e102e42e080280400c01c404682d812115203030035410700142c01003500e40400d0f026100c180e01c880f24901c9000450f405000e02980b200b805014050100d00403034842d40e07074602e50b0720400c1c0c030700d802607412500c0092060000d41c1e00400e1401d10070481941417520811110048090a034010b10443d00c210902e80c68040c1c2074441c403a07112030100e40c5d034400c000283d4000c50080c000c0f4010201844400e481c25a4542d030108440d844101c00301462a0b100d01c1c0c605030002422007103108400c0403030042c0e00c032140032078014a2170005840c00400c070048260301c0e108003285c83c0c0d00e5040100e8103020b111841c65000d0f80340c00d08900d044d28140c1c00203006494400c10020703034810004000000700041071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 135777760 1250 135776510 135776539
    0x330501080a0b0d0c06030b04050a05070509060703030e011812020109080d02130306020a020a1205090102061b13060905010e04050c091002030c030301081f0203190f021308031206 78
    0x202103541c1003503180100050b14048440492040d2020390b8001e0030900020000007003095150b007000010020030f03071b001d12503600d40381c1c6104203540702030340c8600110b0414400032296040280c080c1c20301c0d5001c1e15020828640e103a01813821664007240550800d071000000303905001c0b5500c0c00003a903a10311310081040540304c6e00e40c4485070140396002c240701600014940c20998040c40c0b039802650b0052030840d51211040340183d80c4200a0004071500305040c5511000103000d60159822100180c000e041150b4500c052440d4101545d043c0e400c40e00390500442c2151011030f005100030f03003001c0d115200180d042500242102c407030141c10318410342c2820b00f002114500a42a921402420366000014403d104801e9045000e503d080920381e12000c400005e4070000007400e840740c0900b4480d020300c000e8210b2043e005a10044800040446042600065402c00b90f481000c0e951342e203510040c1001c02c1c440400140d4006a03000109640c00880c0450001c1c404041c904d13044582240c2c3c43e82c525004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 135779010 1250 135777760 135777767
    0x901080d0e04020a0e030111041d28110a08040510020f0d181a0106200318030c0d030e030601080109020d0605060112050103030309050f070f0e0604020706330501 71
    0x244090140150380101e070090707104d80216250034099070010001c0c03140071280d04000300e05401034421020040d800c440b04a207101c400e40038103406541c101310100c2c81c407110001c00d240e41d120020100e44100340d0701d078080c1c0b00ca0304400307010f014400d106680b040f48900300750a0203440c0c80700304001440c1d00d0348100028071078420220100c420400c0c0d42000401e074035114400c04001c00b52002800b42c90080030100030b5180b030003800c44090580f11291910401e01034a0800c0c0b00ca0343c403541d6a9000f06601c20409985d610b00c211003480c9101000804444416503071401250440c0b011650071030104104038420940b51406201580c00346c880c0c0b030000c11a411454001440030104460080c184030b6654012444592142e9043d0032041d040c0e85003032140756502d1400030000c0074031242c03d440314050321030143c1a007000450224222107034114503609450820400340450f00f400352110b94055030070082000064018021004400c1c4140c480c0224032080f002950700c103901d20380d00765034110301342d80d01071009030380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 135780260 1250 135779010 135779027
    0x70f0813150608010e030706060602031c0e0703120201090209090a0206040608070e0307030305041d01180b031609060315050c0415210606030612020d030f1b050c0901080d 75
    0x8116406000700e02501e030018006011940004815500f804000034401500000070b102080c480c0c002001004e55681080340c59010b54800850716825151407a11a440ea5070800c80070118a4000d54141c903a4039541c1e1403246c00716414540160351580c9074082545800480580e12882400240659074401d03800204c00c0e108a0140c202442022000704005601c03500700c58105080240843c4c900d2a180e09026100740c002c7d214076003007200a550182c1d03a00c41c0d1198a5030484102281d44102d03034080c514a80301820441c641d1542512400140c00320702e5420030312003001002c0504d00090f0060a5042c50354190354030b0800c00c01200d00303207014030078003280300011a0101c800e8603080142c501042d000403102a0503440900b06400b0800354140751200140e40000100e4400340c400f00a1540c0d24040c011095801202c043d40c00441c121440010900a903c0817540e16810f00e4050f10050840440c4000400f901105480581c01a12000a2818040c2031180074086160003040c40b00d00304a070061030b406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 135781510 1250 135780260 135780263
    0x6170c0f060304030c0c0e040302010203220c06050c0307020d0809120604030207050f0d05010e0d0908150c0708070506070c050115080c22060b0d1b02060f04020604090603050303070f0813 82
    0x17900040e100140000154014080c0103125105080340c182030500a011b034200762502c220a118090215103400851003145002c5642702c401c11250510300002074805030450802501c4900041145a005030f03a030002c401200c80c42101d403907850390000b0091160560000354104125070081045c4400300b07130000b43c40d00840e0000c40c0c0300c202103910900030403450640400014032960a09a02007015100031448004134049035503904501a238444400d6900d0003d121080003070b52070380000c0385a00b02010018040c080c000e920252070304041e503541500e03041c030469100740062040710440d0100542801225510400c1d000c80020060134110020348a0031081c81a5209404c200c403101d450300c03901024070b00d4030110a041084001e68401e4407004651003104c1c8202c14031710b0040404440c4184d0703802d0b401500860780c024109a51024032002c0400405081a83c2c850002c0c000001c00c50803600608014500c104081c0d03842e03090a0801829008c036900425041c841e10404204022068040f0041c03500d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 135782760 1250 135781510 135781517
    0x20109030f0606051005071106090a0b0f070519170f04090c2a0203061b03010506070c0812040501110601050102030906090a0f03081c020a02031801050d06170c0f06030403 75
    0x71190352030b0280050110781d1100350001c5410120b80700d000c0d0410041c0c80c10502511444a858803c0420015284100107520340d01000141050101102c00d8010700803502588c00a2031038007985440d600c1c68412018200e81004070490244000c104042c442e042101010303042450812000b40c02e045198041c0b40201d542e200c0e0b0340c4c05000322017881074500d8402c0740510032100094004a2021090100600b041030303019200304404141d070000400000d004c12806070b14010b044da4200700820115510101c03040d07901040d00500884e501d030003809a2420b1070303c048407940d030319482d010001d800c40017241003040294010000400c40360342c010044030155001100d10b25515071417040001c0b0b990b07106410154403403043d00404001c12400000800c1588104100782e40c0c441c04130003440c0c0592007100890b10050701f00b84560002882440740080d020b5405050181c1001c0d5168050411540c20350f0041c0b45440d80d81c044001180d501b0701c9010741c2c03003500f03403034103016152102d0100301540b1002c2d10013000c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 135784010 1250 135782760 135782783
    0x71e0335160b0108010515060c19030c05161a070201020a030f110f061b1305010503101e060e060a0203030c0c01091a0708060d15050403030b060a031401050102070302010903 76
    0x610002640c800030741603006508a400396101d80700b40d4002c3c441200d0142c281e003180c03650b4000610740b51082d00d0103910414018180c00d14040350b05421156125021403c0c0308000c2d4204001034030070700c1241d401000c10540c00b030405103404114003040e00c10361000000388804101c010050b0b40e020590440315500350a02805003411154120b548400c540c03a120158000c044c007259620b030001c60300e140140840c41d2500219245404059003030b11402c2641c00424404040410195003e20090b550180011001e00411941c40083d07101411210b4034207500354840040601031645c01c40d04a11200b40d06554881c06c0180c800000b03552407101408881d02800c01140c1c901c4c01a070250011619548d0104d81e4800d06111500b082c1c000260039030300c4c0404202e603c0000740c031900b4a005003011170350304460070480340103c00440742c000700005041a003c0544034900c600300c07a250540109004202580d00248203921441001401392043e04184d04541060404201503a805402d100c1034a4001024100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 135785260 1250 135784010 135784027
    0x80603100608031c05090a030f0e100e0a06180501030e03040329091c050309010902120a05160e3409031a010305060c0a02071e0335 58
    0x64a0014042400e00c01e08203080401d00306000f0024010101c03609910280c0103c0d140c0780401500c0003202c180442e9400600102c011030b22403a240300c1d881d0f2807401e2085400c9000c40110b036040a04042980100c0c0051058000d541001410080140b8903891301c40a840085202d0500b98545841102d04040c0c49038900d000420b004e0003210000e607030202c2804500103211181030352a182c060503158080c001ca03000100e40320070203e0341c41d060a0894a090180e800c000303c0903119030b0800b400c440c40343d40d40d525900b4016158070707548143c2000d640009040841251900c546011400d640c00f12005c07856240c00c0100302c8032810f509410481c414243c440a0f540e0030070102c084400c140070440740c0048001c21007a19078119110700c01b564003c014448442000000c031386c801090a101c01001a440720001a24a8400308064290884544148d401c400d694803d030081d849003528021034004400c1404000b0402010880f0746840022021900c0030f10a90300a002d500b00400d90380305a1800c001894071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 135786510 1250 135785260 135785263
    0x9090507080102120106090803090609041a03010501080c04110705120304080706111e1801210603050610060f0503070315080a050a12180504151206020702030616020d080603 76
    0x2800782886000854a0380c60540b000f5828040070301c1140c0106200c02c0001c0f520060100c110713040c5c130b0b0000d072200d4030704911901032000a18250070421142051005a1000f40e86c1c20700036a0300a05568000f0050030f2210800c00c0300719880340031020310780f10007002000300060000c98410051200f50303d800d0344964031403c004245102c0c007040204203a10700300c801c3d04d01503084000780c609241d007134a0410700c03155104502c200c0c03885101d41205405a40d00c054114540c8035983d10340c2c0910f0460000c208900661705036030242d40c0d603030b00203c4494000ea400c20090036068000385009000d6403521303140303180019001030031511015000001705a140d1910700d0800300007450700302c02440040100e91203e8054101181c440c0d849400450324290903050254070340c0d11898482650941140b422011945070100700001040a84500d40e0102000b0b0400690101d1041c46405101d02481300961745d502180b040504040004049043c18000c007940059810f90020f0354800f14900e1f407d12851a440300c40000c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 135787760 1250 135786510 135786523
    0x412241a10020a020307060816080702061302010e2d03060f07030b03011409030d110f090126040317010b0f1903150815011514030a24051003090c090905 67
    0x1035018414410000f070031f1944034000714403070315464008501031142c5c0b010441d801030003504c1c43c1006a003c03002088042c1c0960032002ca200e03205042007071140b502e21003c00c2d020303c0c109c2e21075441030f41001c101c6044071001845c5d0602000f002c6014018510b800309003841050405000142016500e030296887c586003513000c18001103072841c55101e10b1a24103181681d0303610445c000c10590b410410102c1400b0b00040584e00d01440c00707008982014850b000448000304417a4142d012520381110300f0141e840c0108159004a00940c1c2d0340007440800c400d20200060184e0060088050801000749140b1200083c0c07041c00740c03104d4a0b04100701001900310003502c501e0102d10b00b4cc1030714610000c4c407181c000481c002c0550601048416503a03a516141c0c0e60780c0c900b0501c003004200001e0b000140001c540c03000b10b81c0080040c00c00650780700404134000609584400c0d60002c405040028040d0703241003007840d42904401e00d0300380203001e01a61005c01c0c080152280e20390141d00c83c04c101e0100a000e0011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 135789010 1250 135787760 135787763
    0x3071d04060e0403030b0a0806010b0a03150902190c0c05010518040609050a15050918070902040b0904060b2107170a050a060e070507080f0412241a10020a 68
    0xd2041d00c1d1a40001e5000b4071080d60124046407800b84441014103141c0c0c1140125044236000e40b85580c6060000040759103e08a11402c26648280094100858074005009000d266000503100d1071244501101c00b40c9110f03c000510881816500002d1031070200a02a07400030303c1e003035450782c4041da00e6114409078102c459500a050141c0803500d40f5417940f0031840b6614580082c0000200c80310008404c18041c0180380d0000f59041c0016440b0000c1c101c3c3d100e2424940c0b0482e5822580c031002202241c2080c0c101551664000841d58100e1800d4001c0030003900c8001403103403510241164882c200300e01040304562907803000e000110024051a4407524011104119282529040d0001c10082404a460104181c98814081341d900d011440d5148039a00c40d031909487e045594640e4256604104c4000c10410020000404c0e00b40070790990304400d9205800162203c0c0c4041c591801442008441c1c00d6078070301d8224052500b00b0444110781d841c040980e00b402c2c414451b008201e080100440c1c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 135790260 1250 135789010 135789019
    0x2040204170607080604140406090c0503070e07090e01240203090303070602090a15021e0109120203030912090a120203011508150a02070b013503040e130803071d 71
    0x811181c102804038000744210541e5403480b03400c0e55140100821602c81c4900b500a000704500040d000850692006c861180524850040c071581d07000041c0c600700207504171507440081032081c841c01540040400006c1c180c0110074808560406c00e904440c002104003290303d130b00f40c910150498600078000c46039409001360549aa0b8510380c04c3c884060350011103101d0227041540e20001e0651039148821074580b0759075000c2c000c410b641340010f143c04074031070300380c1c580310355803002403000040c0c080c0f40707610400447c1e4000e5a224509a00818140403045110a02c0744a00700070351203880c1d640c01e955070203481240d8071301e05c2081c4290000c6401006c030b61090002810700c07010082001d14002810100c0c81c1002104209699241c000f10b5099004081000b02400c840c1c00050000d0400c240d628505549540804800c0c2d000b1165402c0301c1d4900c00444440350b42000909001c141942e0200325400384100204040124056464060a20008160354100540d604050340b207600311088510b4103040080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 135791366 1106 135790260 135790289
    0x1022401061206051e210c01030917040f1e03150b0f03010f020409060f180e0f030a0513051f080603031204290c0a0c02040204 56
    0x188a01c4450351904400300b10307505e4501a42404052012541902e1201d100511146049000c82d085800d8400540c074003c0450025545400320303000e18000a00940300e09203004a0100580345000c40c000002d000105001420508419604401c0882000b040b58030172104e4618202c1c40010000070710510300c1e04283d221540855000200980300015030001d1100080c00c5803540105042100c2c0e0104080c4120045440b41c200603110042d000480c01e41481c81200c102410309c8504040140c8607001e09a01c0401401094030000209045948034100a030002d02250008841d01e680701384030034800113061401101d5009001001540d42c00f8400301800c04491b120b10041030035403d0311081140107480d0958080d205c0c0715070f00400040c0c000700e88400c20000403018040c000071102c2c0b000001d002c0741741212000c60b2564074030f0307040c1400d500d0303030500c0814040d0040e54465001d0b0960302 = true := by decide +kernel

theorem cover : BRFrame.Cov 135611510 135791366 := by
  have h0 := BRFrame.cov_init 135611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 135611510 ≤ n) (h2 : n < 135791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
