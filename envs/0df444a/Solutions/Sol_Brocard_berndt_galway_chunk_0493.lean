-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0493
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:05:35.724998+00:00
-- url     : https://prove2.me/submissions/1d1eddbe-51df-4daf-a3d7-780ae39903b5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 88489209 ≤ n < 88669065 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 88490459 1250 88489209 88489253
    0x50d0b1f0303021c0f05090f030c03011103010e0603030f07060906200c01060f0501052212030c0b060108070e040f200409110304020f1201020f0d020a020615011d030a 73
    0x140780b250346001411011912481c010103031a1800d00f01500c2441f525070390030301491840c05403105a4400b08050388003410081c000304000b800d000e13035840c400e810030700805409949043c0071807054903000041ea140310080035645440c0055558903e0001c28903458202c410a40304c48880c0b100e03810030085001c0c051510032043d40e942c0704212400d400c41325190411f031601c401c8401e0905c1586d83c42015034460129241c1800010400c4880f92014985154040070ba070050700704808007016803205c2c805002a12a060300c90b015100c020041d030303030f00500315100d05c00141c0103041c0308064a40340e0421966408102d03000a200ca84000524a011491040888038070000240821441d20240f00fa5030300b50303d0240d50141982401d80c0040e140420030101c0c0307481910707003440ca5010000d0a504985410f14460f00042d80c502c214a404d2005c1e41040000f2000740c000c0707500144038072545054406049905a55054203c7e4420291a017008821481103070544500204800040c1d0b80c4000708600b001180c034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 88491709 1250 88490459 88490473
    0x40305040305060a0501080c130f06090204060914030604060f0e06090606010e090f040204050414010c0909050a0c200c061308060c070f081b15061504050d0b1f030302 73
    0xb40140780c0180581461981e40ca0680100401e00020501e00040c040c100d9108643c62a101128001b4252914815400c2c82ca4a100050480b1280d80100101c80781600d503c021941e4840144100005440d00079070140c00c020000380009003240c3c00020700003018900081d01140c80d0040c21325052048034650820b40c0b1100c14080b566801c50905a821441100c40724030b02d140208249260000150000340220f8135040441c0c10083c2905082c1a040c108500030090b105c02031034014010f1500744107141c005481d00b0042140d4a0b082c0c00341342c888030a2600e51013810a12098030040d090f80701100b0640740e0081075100071040e0b03034540040c082411005151440d0f0f07030410941d01d00700440a0708002d031648080101d01c001520345500d60301c0ea141c114a007a40c0361644004c1d040c900340301610b4a0a65030041030070041242d040901d1080c0103100c10348205554011080b81c000306481a40650b6511441c2c810b0510700007500f0385211503102d08603d060f00008802e164040c284a0b0031504104c1c0980c02c000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 88492959 1250 88491709 88491713
    0x150b15120c07151a12010204061b030306080a080304030839040807062007063207080703090f2105031303080a080f190b150406021e0109020315100b030403050403 71
    0x940c103c840c2d14485d0021841c00f4076011000d081d0005088040504009038486942414080d5014000130100d40094403580110341c80d2070b0980c1d070300c02c950803404908001e01180f01d5061034030704440b450402c2c888a00d003075505d90200040d5405089860304401c0b10801000c1003c103000e202ca04000d124a07104c00c004071040b81001c000d0b14884402c000030316805500e0810542d03502c0303030307200c000d9040d0513075400a42e90383c40004d104021104041441394000c0055241d0802044a0007448154001d5580300300c5540c495604100d0501c00d88140c510130402840110031511130f14031002c00306841071040368070308000d003551114402c94561050b2041c40780410b4035000e140d00144010351111a10048800038a8800304203040181c1041040c049a07907030f1a60001d1a0300c51058160706e03268002c098a0326180c0c0c5401c001d680f1060041450700307032130800741c2d004201c22050083e240781d168014042c0109199100001140660081010020107008e000c0002d48211100046008a00964030540d6031f074214 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 88494209 1250 88492959 88492969
    0x201060303020106140d080d060b070f03020c01080c0d0c090503010c03140a021606020702040906110a090605040f0b03220305031608100902030a09150b15120c07151a 73
    0x2a03400514142181c030503a042641c1c50705110050658001c110649945800100400a140c92b811529a20b540000c031001400b090031980403106120344d08985e100e07480d15004541c513040560380d041020109002000e511422a00700032010500361802d1408203984000003401e6501d0b41010001017503403075000c948200c001c03800c0a53701c074520240030f6190030000041c04c6284011014007421850303000c40c0100440d901c980000035050f420203810b11100c1540c0b198100140d00000441d000f08064031000602c13640204250350448100d440050102440c11154026a03400103040c401034000404264044a01c3c0c80b210a45503402507551035207030700c0c01c840881d80369000284550140711180c010400c42c01c0000c3d03079010a03901e48034000350706c81d11001040400b0b04101c0000401c00d102c040d150151603a00d03540501035001d000c0707848170a44025040118010301c9080c40c1d800c0c1621911f0002400305250000916071131b4494504001c918040b1060318007100c907010100050044040003c40b128904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 88495459 1250 88494209 88494221
    0x10311030a02281502060a09030504230406080a080f030406060b040803070b0f130303090c120605060906040c20030f030f09010b011b060f06050a0e040501110405010c020906030a1202010603030201 86
    0x2455a0680340303184c4100c00707541c400d0b0080c10303044142c1d20f40001c0010036101c0c0042c3c900400086032400c05040102400c011014140350719940110314200c00015401d10026105031041d4002c03075003031b141481d454083e11491380700800950780551141400600704801c0001440109004000385841e450700e032034089419080074104280002c0e00744240b00700c1d68a490041d4071300d50381c1801c00040b0154503280544031740510364040c00302080071070050700502946420051041004450781c2c1c0310755aa000410007101c541c2e20030900025040e00710b40000004070510b003d040c0d14042c08036405c003084502d1810f4a58002c6800c505540100c60602003080c0b0240505c504401b02420700d0401440b004040602c5c803619210f000c0c1070300c3e0322102201c81864203644400042c0c1009480310b549d803900c4040d4442030301304c2504e08940310362030174841c0340419524030305480c160307041651940144611a02003100c2d880d8040d06242d41801103000d400300140c2424030010511a064001003507183c13a608001c1d0842e17034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 88496709 1250 88495459 88495469
    0x8070c0e190504030314070306091b1407030905041a03010e0c03100c0306031205030916050a060f03020d0504110316080d081b0f040306051806010311030a0228 70
    0x451000788060000303001c0c20124440d10180c0c0c000341594a500f0120041c0100c0010b0190348411001409100341d4540c01900035202030010a028502094441c24510001c0c040b58034006141c00080e0110500c40d140180011070281c50321144281c0c44174002000c4a030055082149405c03840c0c0e5125645c2020302464090000c0c0b0006031040c0758050001ca900d601030040c940005c280d8400c04051924040d5121901454201100303401519071000081c3c4075074410760300240148100030b113602c44e0036a81c0800c8410350b0405400704500514101094400b10b001c900e141040c142c080c811401864036611802d0303c42c50062410910b180040c00c181401c4c1541140c807440011140d0205009004002a031300c405000b1600d00320f50565500314208694040030a58001c540c81300045224002a410f000303802a2030140500300000c0d11170812100141244401c40c0d01300307030420070041020a58110b070105107010040d00340c98451131a0b0707002a01030580401000034104d403481d00c0d4094100d0381e03103240d0b02400f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 88497959 1250 88496709 88496729
    0xe040b0906030606121e0d170408070303020304031b050d0e040903020705210a050606030d030905190204020d0c030e011107030221120a0902030c03010b1c110a0308070c 74
    0x41880000b00b07480d00002040c036400f4291203138020501400070041300803007240c04513804000094001c00c550715000100c000c200019000c0001c0020381d80003400c0c1c2c6018590001e44076141c851a95002d501a401c02082901030040b40f039a464400040c500c0d07108030b207a124402070181144580700140c43c440810780d40900640c038044d00c2500007500000e61f207042d039000700ca100b960002c04040c214116540c0d101810154001e40c503240f01085800079420380950f400301c080e205040a40c0000304c04aa11b00200541344d41c1c171000300c2c102d00d4600c00441c410b030180050300c09850030b00c0003d251025210b5152403140000c1c0c0d03d141c81405940d00380325080c6048004583c0c54584a03540d01e00968881c11099108100f010b1265281100104c0000300c170021b513003401483c821468800210002012801002d90181c050351180e511146810312502455400003010403400340c0010344241303c182c060403000c40c1c46151802d218006a901c0130400b100035841054415503030100780c903115001020f10380c402c0c1c01c52 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 88499209 1250 88497959 88497961
    0x10b09010e150f120f0a060513080a030e070302060a050a0905090c03040326010f050f010f050a0e040b0307030b0403140901080c0730090602030c0304090e0f06070e040b09 75
    0xc0b0050210311010520120340c20710018441c0310018902d1500401c00c0c00702c601c252500150900004500c07410076034018242008281e489601600c0c140c00440d000501d0b03400100584440d1a000b0741c0001001c103651822501c071192a640450f00030390040d52402d0100d040400e5050360349030710017440005000d06944c11a198140804190010b0001078402403c1c0110008800c0f6003804107000080a030320301c08054181540c1d500c0544140388458002c05020794004c0f0440d80940d4021031040307900d02495542d0b2483c2c0744035881c00b2070b41d9036078401c11140e00c180c039410f85c124155403c02640c0003540c00b8011030344660504d454041c0c2003000906614040240c1800750010b00d070b0308018040c0e0301010b02c1980c1c6c0d03030318003451038001030507001291030000080801240072280080d2982001c460130554540717a40668803943c1c10b0b030b41c80c0220b0242090036442040b0601244e131003508444c490703c03c5041110500e0b25500c0500d42007640c11031f800340c009201e220303a03018140750034041e21541c0c1d842038a000402d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 88500459 1250 88499209 88499221
    0x90d0e06090f030a0606030c03150b09010e0709120803090f0d05030105090604090f0f0201080603030705060c070c0b040603090303060b040803032802120412080601020604060509120c010b09010e 85
    0x349005a546041c810b81151041d205240c6003408a1001c40350300c40700800c5499100c0c40c0a40929080e0b000a8414045240d8104144000d03071141044400c1700038107919981c0e180115032048458014040001c1044680001600b1100350002081091185075240d449103060f1141e40e14207002e050051181e81c0c0041011043c0f160014212070644000341c1d0f081c07100741d070b500740414080d000c12040100340455a0380c00805205c288550a03415034801daa9004180c0c03101420140e030f0740034104010f48681c0008010a202075241801050740300e00c10f101041c0d0303007a03846400301d046030400e5006a0100e42c50f1300c545400c05605120b6640036040483c8428105411302160030355a00008008130811031106030b0304085540c0c0300c01c80c610948115a4107540d1030006042c081441182940d00b1205086c0c50070113210414043d003001440b030b03201039000f884180d0352919014003601c1c0150840c03645020300c2000d104942c4055000381546003008002099444100d01072200c1900142c2c4032441100f10311042c020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 88501709 1250 88500459 88500469
    0x10b130f05150d0b09160303050a080601180e04050a060e0f070b030103110d060e1207020a05060a0503040308100f0b030f0a0501050109090905030d15051c020904060507031404030305090d0e 83
    0x3c60340381c00003200c0410365144010545403030f428031120300750024250400400c055010300144a00c006036501c1d0b10081d00c41c1401034a0030070003403a5020180355000b0051010074040c105e032940c00b5000d4030031a5103002c03464a82600300c41c592410440282c100c4100001c032030318104000e07070082400203081031540d850354681c40c00030f440103e20305108600d0241c2c00301c1440847d410440302c802242d4245c03122038502c00c01e024815401144200d000b0310090400007128a0918240c55480d403c0e5190146503650b0303a035044402d0034001f000e0380c1d14282c2c142e102045602d400035510001c1c20403211420b5882c00c040f0992141c6000c014008030101c1d0500b8014041a40e000d000d0508846c0507041c0807901030034030f10701107045018402926249038540f402c00410740d00000d440d481114025076051a0303800d8900e03284003c1080d845c4001c1c2d049036516000c5070004e207466000e00d0384a4005d203800180c013404008900103181c0d01f5501a000a9110000d0100301c101c140414050b03d02c2c213040103050741d00d03075034007043d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 88502959 1250 88501709 88501729
    0x909262d03070c020d020a08030a0f0302040308040302010e0112020c07090506040b0a0513021b1c0206010e06130e2b0f020604060507050906130f05010f0804020f03010b130f0515 78
    0x1000c12021400e07200454540c14160170b40968020311348000d1a803240c2015540c1d8000010300300c0040c018040086e40b26010703100310f80a03030f604424078900c0d0034256001074400e03800420320306040204c078020010303411640b84083c0008004450103001c21030320305110b200680e0f40c0904040d2181d460055900660b0359044500c6045460a80d6002c01210140c15144028040c024100c1100d0151290b4162000c40114502c00503e04018000f42c1551000314126951402401903c009044401c045109840c100c1540450b0b0842c4840204002219029a50070800d128040002e040f001c072208503d00d0a0840d010b40c2e101220b0b140c901421070403544001c2d681c000c0076201610503540c92000c0782b80e03e0b05c5281110710707801002c0d00c1555142881c80380700c00d25400f14822042480d04d802d40c0481c0f2903210341c0c0c0380c0d900046c1540e24840390341c95a400700806400c50300c0d1425815940d1b90086111500c86800741144040011000034008000102d81c805880c00100002000c00c0c1d010b0f2189000e030340f005491 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 88504209 1250 88502959 88502971
    0xd0c0305060c09100f02031b0a0506010608010317180a3c060509030a0506010305070911030f1602010b0a12170703020a0b0a060509040605041203090206040909262d03 73
    0x14519012480c0f1700341c0c210302c03c41035112540d00c0025044001c0b5440098030a1a180c4a0b5080b109103030384c0e0329011a56010280070041140d50035485150b40c842a5a000d04a5060464240641c1e103521a00040c14103040e80d11504640c02c10310855160090155160840c0381c007201813105680c47d0720036000e81b1300d810314000d0b8001e00c04007041103080c40e10200541c025043e40001220642d5851341001c0d696002c0c5489084c0c0c00c54141001c1d0001000640146c034050130f00b840368220680c550052045032510280756400c1190350310504252607540f500020801400540c40d0040b1000041c1084a0740103400c0f4562031480804202880c0061342c0021440c05171078014500c48902d849030862007024120a5110f158803852a0090106020081d03000c10b02440c400c55060b0144902d0003416015242a00c501940c84030052008000f0a00503802c056566031092500c2e403600442c00590b0000e01d003580d2800b210506c00400c000514410800d40a40300b84d40c000c5840030340c0701d40b400f40700003076100003404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 88505459 1250 88504209 88504217
    0xc030203040b0a110307030536010f050c100506030d0207210206070609031206120b04033006030b01080a11041a1825020303240d0c0305060c0910 64
    0x441c40c0c0241c4160031304400d20009a00303403036403141036050040980e00030780c60f000c12010107810001a400c0320304a40450304994010b040c20624412001591401628003035201030040c1006070051000040c4503590f1903440c80035000030b05042103428145084c29811514055502c41e82041c440308000c22403900c0850304403d48071541c060184081b803007074051100000c2000d410186102e0030950000c4074100d41c2c80c1044010415680c0c2c401003000e5084529030050a030040c48804200480e00c60f501c0051540e802d600300115038918468201c4c4e501401035a104001540e03898248100802140d0090040000200814080c10a81c440c01c035104028100c140c8178a9440c1c00300311048140d410400da880358001d014120030510714401109507802200c207e41000701d02202005860f4200ca406480d031003460303000714199901ca020015002400c050210000c0300286038150440d62210900b0850350310842840b4aa00d10b14a4900c0c5002405070a44200300002d1040100540303601c440b20000f01600c0c50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 88506709 1250 88505459 88505467
    0x6010f06020a08030c0a0e0d0c09140411090703021b15070801050a1203020c040f050405010608060c0a0806030c06190f1e03052a0c10050f0f04080c0303040308060f010c030203040b 79
    0x105480b10f84a03410f1f5690407545c1d4514100911100300c034050304607404002d060040492008000404050449008128080310210000c207410285c4400b41e00c0001070030010714080c0e48000c0d11004826040c0c25118030361045500c2c800c0014558805500001d0340d0609030300c035506001c0050180391039800b46404c8101030700d10440034075208108484081c600980100070880c002a858805040100c0b03094030f4660810000041020000840602c03520448a065051002c0000100e4204001520813545441200030080d1182d42e4003004100c812141192550f820612840182441c6200e000103424046100c0c0c0301d101504014804103000e40192400062350f59801044405201c0c0c9030101c0410b2090500020300140d403000300509500740c0074001c4800318100030701c0ca00b050301c200f19000c0c0c1e020421440401c00d079859110078030781c002d807058500500b00080b282d015131440d0000c9a00741c1c0050001814060141090148551124402e10b0800d00c00c0b004e58401964a1040c3d00c01c548001c40009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 88507959 1250 88506709 88506727
    0x100e01051c0c0e01020f0a03090b0c010e07091d070b09101107081f02040f091805120301061b1a0603010b0a0e070201320c0906030906010f06020a08030c 67
    0x5140c10256024210420000d142c00724010440f004000129000d48180000301615190008400c90f4181e85603540721011410300440c051190081000981590f40f240d00843c010042441014080c00d800c400000d8078009006018149113060200d200343e0340c1008101f4440321004004031446684d042c2c0b074181ca81c0018200840307020094102e101c030036010380b100c00b0600c010040754164482c10440000305d000050045240101e202d64450602c07000d11146d1b0030450310000e80c1066004803043c4003687c00b1404c1940350340e81403643c600700380b400c00c0030000010700c901070b04104200b036010b0b0111502040c1181980d10505d0038a00c400d0088404c10105000841d0b42d502504100f030419000740c00d100481e41e8484500000d404140d8541025508008445031a0403605c403c81007120380c00640d61203c001003010400c2003200c041c1c100080c1170810000f00200e40c0b1010020f5000b40591002840d0075032400c200c3c40000d450a030020011500030304801004242c40101740c03a004a8244480c0740d49591403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 88509209 1250 88507959 88507987
    0x310060f0c050a11011218060b030f03040306050103022125051804060c020d170403031116020103060b180405100801090c060219030f0f09170c040b100e0105 69
    0x209001000c610800c00d4070000c0100000e040e9440d5a82070300d0b0519051b00d002c03808029185001c04032040140c0c1320344134901240352600200d9080d079016041e02c075045007032100c65007594443d070000d41e1811345030001001181072140304078a049031082e400075101c07965805600c0c0c850b03400010308007041d00c049008603001e10032050304000802e002070400842c107900c0500c006807000c045a040d11060f2a04095482e401c0c00801e400c070054000d2340c3e999680140e03003c40b403120110098400d5040540e903c0c1c007802c40c1c824080061440101c0d90544200b24021b62000601366005500013040d100000c1c003492014026203010a9840d0a0490f80442e031949c070401300d44071807885603001c034890b5030030f02400300148026074080d80306a4400b43d00f0307200502042440b034002810408402400100046d18991619101d11030341402c44400703107400b204460f42c804420196136103100c2d070446541c0054169059501e4280f046481508055134200c2d4034900141c0c2c0a45149e0003089154180034002913010007003d44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 88510459 1250 88509209 88509227
    0x30606121a12010903030b0405061011010e010c09030501050702151303110a0827010504180b03010f020d060608060303040302010e2107150503330d0503090103050c0310060f 76
    0x90408640390b08031400c094064081c07607800b035001c2840c1c10090350003800d060003240c0c03080c0c00c06061a13103104510b00044036a040300261001c0c0c595a1100b04000c00c1100b03010310301302d0a415943c5d40c00858214145142192805420315003594403903070a8080c01d6070018004c0303902c84d1000f03403811003400090809030340d00048600c420401e400340020b03840c01c120038040501104110f10103d42806101840108442038101001f81e0108809104c2008903110500b41c0368081c283c0284003062072605a000b00e0700352040c03ca285610603402203031200f1603a03c10302c10a00141410718107140d441c00c00001185c1c43e4801d6000c042e0401201541030765060310f4081803120b400358040004d0306032400f0405201d48410b068005e560518917104040c0129502c0344c82500d0140c0300f4402c52511021650200c0080103010f0b14801a000d41c04074083d0701c140d52640100200c003401117018564a600e0a000142181c000a0528030010700600030b1200306840c1400320401c2d00c189051000b0380c140302d9034007070f00e000007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 88511709 1250 88510459 88510511
    0x1050f0705060103060207060506090108100f180c090e0102040506190203040f0305030a020c0103050c0a180503030c0105160c1502090117040302030d0e01021608071505010806090c0103060612 84
    0x80b4400000081000c42d03401081228020743c410803040d1111002c0054003440bc1c410040c00350f01c801202d4000301d00c2a440801071684103d030000e00000700304001c0aa4102002c02510003c00301b0004200070613103405071031110240350008516280c01d01c0d0010f03246004500c1d00051018208401080b058000c0080b10082c5c2010ba5540c41051303034918281d5640c6d8040c400000050240c0749182a455002e40030f0341d40500411041c01d400c00d00d2a4008644400c034101d8000344181690b0741c0020aa1400d1004014040b078600000c0356034034007040f60a00b40c106040c041002c1002e4022050040f0340668012400e02d82d07802c40240e5120820401219038012a018401e50503450350103020070141c00000404d0160f0700d0032001e0000e01d0840301414201e018401030300304039490100c076100010b14103000415005208901c21085201c03c190b040c001c44d04240c00c440b40720790100d02480184402004500c00e400e0003460b052042905107040148110108a06840e540f0b40388c41c4886c0c0704c20030714040006400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 88512959 1250 88511709 88511713
    0x15030d140d090f06060905060d08130b0c0c010905090402060304080a0302040f0b03041e170f0c03070b010509090714060a0519031505031603030c03091e0317160201050f0705 76
    0x2c00c05040c20121110107400031134030030703241060002d285032803402100c1c450180106500314489032911040540c3d4440f58000003d0750155802164101c840005890790451070030080c501c0d0807100002401c2d0b2129070300040d125000c22b00421006035280300499034455840410342e9180c440e4010260080d0103280c02c5501d80e030710090008525603e0360300c095403089010320f000c6828060348211031070340c0000000024081d801c051103100a40480301c001806041080c00040f03241007a003c860341d040da00244811038641c6c405000401c0186008048640c02ca0a440d0107403220034503180303101411030030706100207019080c007117010070f21180030b03c05a604604d841510b034000568074810042c02131080313000f5805051810800803c1505000881c0104800344d0180e824500b82981c17000d540807400f0020450800021070f00106140d202c0359482d408845c5118503032a00380d4210710303040044002104844900e00400d0061150464004140b420700d1602800c00ca80d403091a107145480303d100d404c07005481d40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 88514209 1250 88512959 88512971
    0x10c05120606160b0c21100e0601140408010902150a0f0815040c09051906022503052a010e01020c0d210207081203060904062d0b040515030d140d 64
    0x100400c4005c1c074802d00400400d0780b82e16140030328450301140079a201000d4946405c410b002310494078101c1600f240c0c050400c00d0b041101c908080ba070f258002d802502060b5108d84003203045051001c0c00f810642c3d00c40726000d04105010b0720041a0405070701460701007028007004228201c51000482d01420400340091000d00042c180240c954940ca1140901450152040400d0001d0401c400ca0a807241503000c1d1001c110100d20007844209100740300308422803807000000000c2c200708403002c2d403a00403104020841785140f01171007481c3c40d010411030510100214058a43e039000c100050400c01c1100da0098403100b6050018065424850458068119148201c08150000b400c40100d484120440d0b41020b407070340c0f5441c0c07180003d82c0c0301078000101a010600007421038101c034060002046090540487c10528a0b2081c4080458203621079a5034440342c1c154140360003615407160354851002c0070040c0004c00700340d849032135a00300700420440e171805030301300050392040344e4604602150a11030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 88515459 1250 88514209 88514221
    0x1204020d12020a02090f071215120f15061d130804090b0a08010e12030702011103010609031406042001090503010c02070806070908030f160c030311010c05120606160b 73
    0x3403200700b00c0f000c3c2c0c81742c4070600000c2c01088041c0009071062030103030349400c0030f010700c1e400c501c2c040c050002a030035105d40f0500c00880c04036001d8501c4d104980c0103d604070300141c0301e41003021110406000c40b003041824a101441003a03d0300142a0281c0c0c1c203100f0448207a501c82134a02a01d000140307008003204000900040d200c0d281c1c0d00b15504c82e0380c00721a5400c9280c0d42c1d007410703801c1328006000c1c40a250403c1185400f0827401d0405513a005229000100e0600584a42c041407a40300760000d00204842e0303d030500900c408080044a810f0100004201d1030800b500d41a07607602080c0c80da4148030042210010907648600000001040003400910194204c40c07400f135110500c901484845101e0b00340042c01c0640b15020302001c07200c650001c2c500c1c1003100d445400283c0c1c031901140e02d103420b03a51042d00000300d0a003402d4000b0350281d0b84040741a641c0d00c0c0e41d2170030343e02844415420401c0c24004600480801c1403ca0b80054044511641c0e0b0034100908a10f6411424006840001e0072010840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 88516709 1250 88515459 88515463
    0x402160507080c01050909011a04030606090212090d080c0a03020f1927060c02010302070515150406140603061503040f0b070813020111030912030702040506040506061204020d1202 79
    0x5071003094003583c0900700514011981401112040c4e40c0c00300b042001000000340c2400c00c81000169001c0240c41c244d20794942009507085540126107003940000c46203a54000d03201403d4101c441030000d080100b0001d10002c240c0280502441542c00000400b2046240a40c0c1169400075100c0d076996104e040c041107803443c0408544c8410042140660480d1000c8860320a640d400d4050300802100f0700d05141044980c0760b0741c1343c02241807507800c0203180d0203c0d01c10001c0c034003820411802d0580c217203003e503620300b03850030395032401c2d401035042c80402e0115070440107800f0618441a074a040e26561303000b0014030b00c10b4103060b10810848000007400103009001680405050007031190812030344494604880f010f038105d1707241c046000a55000340c010340c425035907a5801010700c000c49082484600001c0c19445815003100c41950002558000310b00b02406099170043c8221401c004520300f91000c208584201c05238641600c1070400020215a1180c80d8852516001828610014070b05d0a0281d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 88517959 1250 88516709 88516723
    0x20903070f0e070f021212070f03020f0904090204060b030403050301140306010605030a09030201090611090415050f0d050106080102070804030b06101d0a05100305100b0c0a0f0204021605 82
    0x5019028800001c107500342410014011140800300045050b9180307001151440c840a00300c0c0d003140201051004412100b0000c0d01c005c084a251108042c1001000500903013550443c0400b03041c0107004110650034040c0645803400c00070703500881c90301b0462000400a0041d9045040d00700c070084103000c24190301c03101840c10382e5400d400003840030007004105562041c4c24070810000440c2000080c400d9102900044002c52090001158092041d603420b0203490403807803120022640414482d1b003900d407501813071040158540740c1e88041d03800c0c0b50104500000d00706c00d090244201866050801c14254030210040988a00854858403245400030507584248800c1e01d10b5880c07807003c15501d15041e900f8180603810341d210103060100c800001c10109041032005d0fa0b200300380c01c0c400540c40c0c0b50f9180302840901d1580d000290303880d100d0014003c10300960400c40403000309202c901d0300c0a000080012525400c41510100d1315158400107019200d1540c0c00341c0c465030490101400c0180006e010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 88519209 1250 88517959 88517977
    0x3020309031207110402090607061103070f1b030c0525050f0618010e06090a080309090106091401030203180d0903150c0804080a03061d0a060b0a0c03030b01031b0302 73
    0x350b84111052000301205000f030180182412150701ca808455107401d9000b0000c0c442c0103400a0b081c00020341302c1004844500301000f9564100104015455500051012412025003842c0c900c1c0c2e102c010301000d44600d4040002d0a00c140220407000780030040150140d60564526006030b65190100403070746012117445290701440c85104000d103e840d0800540c0c0012650590015842c400d6800444006041032010b40d0041000c03c481203c03504c8070910381340940b0700a40219692010041400b4592505900040c10001382940601c4111440500500d242c102441c000d61aa1501103516691050b80345800600d0f00c1054140071515400c1181c000c1128002c0300b110020854034029101602c40c400c20542c00200d154001a002400140141070780755142d1400042c00754591210004c2c1003688038040300440880410400701003624007900001e000c6c051052810041a118090510070041100900f819110b800990080c0d200340e000c602c601d000c60308001d4410b00c010074050000e5100041c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 88520459 1250 88519209 88519213
    0xa0c05160317071a0c0d0911090a02070b0a02030a1b020a0303060f05130e0a0b07090e01050301020909041e05121b0601080a170d060e180f0601060f0212070302030903 73
    0x40620b10141d040036030301150740050340188641071030607101c180080010642202420280300c5a401101030b4800c94807135622a016804103500544100800d00b400108160b450318010001407001540341160941c0280f4158409616034844c03080050123084041c07034601c0d14071403060882130000d500041c20700c00f80e8060740b000c02041b030302c8484003044103200e0301415400c075802c500c19282000d029400219148911002d031540400b9940c1d41710092401903c40b4000101c2000703090200c0400c0e000c2090047c44200d0085217485640404030780d210f20024800750450340364800100000000034004003225510070305440181d100c048409480d0b030403482c0c85180c4803c0c0da20300c0c04000400041c1c03090517200c09030000d0610310469074800a90036030031200c540c101c003001c0c850707030304850007501890024100388911007003d40740a00080c5080704c1030480300c000540c048181c0c3d96031a100898901d06490035441e0080400c2c40784001a46040b4018110f1494144002024001c1c5503002c80a440d1010303040701 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 88521709 1250 88520459 88520483
    0x2a03040204150501080c0903011415010f05031314010b03010e06090f0109020a03080304151802130203101e0803030414070b04080d12110c011a01050705070b0a0c051603 74
    0x1000b50380040394003456000c2001c14000c145120f034110b0240240f00790080010510003c241c00b103282030b000a460002031422103500100702c40da0004109110145c140c80c00c10305504e00304203030038840703503207100e0150054002040780104d14600390080242c001000d0024002c0138000070700c0950321003040302c0b00c41c02d038062002d0f00040d4900600071440140d40003130401d1200d90840d05d500c940c40c0d20180c002c8bd0040c010680300440702145004125420f11003c030382040d030340c3c01c2e0300500860a450040c40801a4410010000b901943e01d80e8041a13070560030400080700e05050243e1290810b9410400244c400441004200814403c07070f20040312540c01901e29040da0f400e0754400500890051b0020341c0c11411322441c0f507070704ca4042303009403100f1090301003040024499003a0030340d030100001220694682c80380f40f00b2860503164211084000b8038140b4980b049585540e5110f002d14012a00390b00c60000e07001e03918504c03400404a102e80c000040c0c0d054010810400100c1d9902ca100445025000c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 88522959 1250 88521709 88521731
    0x260601140a02072c040605090c10050301060206010b0a08070e040f020706090c0e0403020d0e0a0e1305060c041d060d02120303010806160e100c0b010801020a09080d020a0206032a03040204 82
    0x40c240001d2a00704030044c85141c40d01d56802014001c000d060032010310a502d050400e965030880998050714080c0c44141d900d50606c1e80003070602005820520304100d08100e144402940325071400e07801a554a031a0303002900300c80000e80070f0f041c2d1440c230009140c0007040c06010f0021651050113024030645030341c0d800903560000150501d43c11980540940c200d280c0d5540740d14011019022030b600000c1502c3c0c50652a00d0051040c000203035100710407010204046010040c0401c1120b800c01c62103c006030030a490b004083d01001c01d042c0c80b501a44010f4004201e882c0c8070301e00c09480075980105000312921500b0003d03035803a003092003140403d1041c6400300782582e04040c001c18160501e41d80c0c030000040f07104103120305442840200c2c410000c080d0485c13800b1801c0c66041c2d5019240302000980d40c0c2032503d200504201e91604a00e0f21900301b194141d01c4242c00041c0401070641c180c0e0050703213a036250740c4854082181d80e00070005085040e088042c09007443d900071403240d8821941041032078440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 88524209 1250 88522959 88523009
    0xc120706080606130503010618050a050c04120c0801020712080f010b0414130e010e0f07120303180c060306091d070314010905031201050f01260601140a0207 69
    0xd100c0d28000c80c490102240782810802d005100701318070303041c40a00da503a031000420b0840703210741d10541c4c03281c0000c2d107140e5035564140078040e001140e145041c00f02d41440300080002d0310661055419149400c0103442c200601c1c901d1000041400c80004c644500e901d06144404800000d480340024030703040c001801c1d0700303036091000303041e20b40c010030703d07803c10b03041c00c8980e0441640308030304c580e103c2d0445d5040014064039010725110300718031000100d8449000b1180700e160041c45040e03040700e034110307000520048032201031020907140c243c9008030303920400d50403181403a075000c0c0e4040d10000b4549800300c1d109415800660807074144100030800c0480d4030441d6140f0303e920504c03680d285e0f0840401000480d8401030108071241007000009240e00321655905d25503808404641c4059907000010451454003410380c2e4482402803d06801d03002075055907550001880c1c44840340c070058030011580c0341e44a00b04454400036949045035a840c5d0481e00655100054480d031082d550100403080b140c00e0350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 88525459 1250 88524209 88524223
    0x30b0111061e1027020f070309080c040b0108060f0d08030c0a020d080103030230041806080a050316030905040903021b03031306050d0f092604060f110a06020c0c12 72
    0x903141036121404e0030240d002c0380c25403441800900b041d0240000107041000c0c1d1b005010807440f81c1c5078400c0e69890700c110b0134184a0202111841a0300e850344088150340c2014101da0f102c40300311040d0310940303050400152505002400904200408020008101884c030014451021240c080b20460b801e0000200c54181c0240030040c0181c00140388007141144840c121381074207401400c5502c1070b861030f8082c2003241c1c1090388644040d00b46074042d143ca01c08940b2070741e0003500d1007030301400000e05280c5489a607407190000c3c2c1d041942c0c804080e2010302d485041c04c8405803200400034000c5c2500f0307040c000c0d500c01c2110140250000c1903002c0140501d800000c0b0341d41c004a04803903034245860070701d09a030550010100c00007a192a0580043c154801e0b22a14151511603c1d004489102c0c20000c0c11603920380a50038030481608101c01d001441d0005100e400302c18052412841c180244c0264508040000900a00c2c0701c0c00030611400e16040402c04032030f0750409032000000c1900034a01c0035540e00d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 88526709 1250 88525459 88525469
    0x14010c1704050f0f0c0406140a0b0a051911060603071503110405040f02030702150f010e0402030c030a120f090e0612070e04030201090201030b120607030b0111061e10 73
    0x1040d00d012a00d51410129455000e0301500a81d0b080e101d8140c42c82d0304020130b081c60f03070310745400100821500d45841d100e00c6c0060a0482188078294000380042500ca0607140503012400d0b90218034070601a20500c00c4a0f070405074074141b03d003c00a1090050900510040854254060000060403130f0400103010021103917401e13642030958001607000e500030700242841c84610302007000042080d03110f902548110200f5a180142c0d03e140c0ba44e0001d04184a4042060745244004203200c000e1b01d40503100d03415101c0d1507981c65450703241c42c400680f038900c1c0400080d40601880c41311000384015104141c0103804251240b640c50301d88940212030301d072254044c014410002c1400706419051010b00f80e030448003800210340c0e21544903c2005010f010803113007140144e456000210455901d0b00038502600c9051341e071390498071100012140c035040300414807030230142c0e07031103007503225a10505041d0140c125400c25a81a070a0221541030500c0400c01e0103002c0080810201e205d9504450985080354 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 88527959 1250 88526709 88526717
    0x1050712020a030b1903170304030e04020d02070219030b0601030902060706180503031f06090506270d06020717090306070e0a0b1b0c010e0102100906090c0e0414010c 73
    0x490300d528810001d400030903566040668980100d9682d4a0300d02881da0115200305400321000e1441c07922145c400d08116100850701424000d220001e500800300721255542114013584800e00401040e00070b006260002c0d6104803800c07445121100a00e0301002036a018440307040c02a55200015004d49490101c025003107101080b110b4049804c030ba01c402d000e00500d200c0c540300000c01b41c80c2e1b645136400c10303106c00003652100d98601c3c05212024601c400140100e05050803814034010005980380640101120902e0155400250103030344143c01c0c540552004201042045042c140706000350882c01c81200e903003041104880d8030003142c1c41581e80408009000b07203001d54805c401181c00f805951138064200f0010b02c0f003c0b5460101c1d83c05006000143c950849a0b641401e0046140c8614a00060b0500c40e14010083c03451368085115200000031000c007049628140ca40328008002010000e04215650304012521811b04280303140600e000e485110071221088010900700c3c0c0101c01d11034081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 88529209 1250 88527959 88527977
    0x10f0c06050c041a1b0705060d02031305030c031201050a08030316050d090b071b0809010e0d0203010f09150b18070314010f0503011d0606120a060c080a050603010507 73
    0x10101d421141c1e00c5800750102500307041c1d03900c0403d800269030342900141050040307030032441e88101440980a01154000400c42e1514280100b2003922620401424042c1c0000000e0204036145291854003507100f02102c0c0d4901150300502d480c0d81101d103140502036809400011140740100e911030544042c000514610745424485101088480300c0c50030a0000510501d50451028828181c8460103041aa49a480c00000c0181444002c16801da404101c800c2c005000c1a4048141d8000d50f0003800c1c01c032a8880001c00262076000403010080d4150700b820901000390496400c00c0020031b1141c600805c0d01c0300c0686c500025940c2c14900f803038106900c3c1842070f40032280d801e4920781083c0c2038200001ea03020900b20154121703000341c000070401003102038200314a007024422684100741e0154001062245645650707100d07400074100a2013083c60014036156050148940300b8020f50003c4100b103030201004010317129140845004914a182100203240c505040c010103205400c0366030395403c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 88530459 1250 88529209 88529213
    0x9081b0a1e090525110a0308090705090a020d0b0303070f030c020d0813030302100204050108040b2502010b040b04051501030e210711040e030d0e10020d0b010e010f0c 73
    0x85809224650541201ca4940002c40c100302e48505402400741e042e4605092a6128048003420000c0040e08100072036040040e1750070001007203e0540d20340c07524001d03a164554501d15454035550750042940424004280a80c203011680102800c003544001449401c02030020181c49000e01d01c406480e1000c1070300032000083c46406428041e42c402441d00840c03030a5900c440420307170003800c5220700d540b0700c01c48103100f07060301000a00001d0840c440c0551405040000082c00101d01803c0100040088008a59100c00c4240540c0f0050131038692076039001031320040240600100760f60382c1d0240f03140c20034541180c1068011103220f01c42002d00004288120001100101090030300c8441e580200d043e048010000b083c40c685c83e807210f40741819111422030070110044c0076005c158600c2540382c514440c410800100c00d4401102d20b2200000715240642009424103007801d0b070862140340300180302c1e0040045948059000760081c1c1c0e0b09440d01078000015281b4204407005400891000b49841c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 88531709 1250 88530459 88530479
    0xe0d0305060a0f181113060521060607030305040515042406150c1a091b09090c1201020904140703050a1a06130b0706020403050f060c0f0705160609081b0a 68
    0x21744510b103942c1c464a8418075081401508080b9005940014000141b04403070055a0348000210816441d044820f070a00e01c0004e0080d20821400606141c0c540c0009400e1000c240302030030740d038444226003028901d070038a0009099280b0148031003c008041c00142814010382c4100801c2d0342c040c08280511f811035805c155284c1c14001e500300c0348115001c0001100700d0920740c24900034400c20380104180000c0900054804040f4441d140c0a411000100551807030009034480c4844802d541c0d01002c0d092440e401c90191048100301600315042003000054080c52640b407a05c01c40b55560100220780b5500001420380748503a5854040e5031900b400001a071030580d000384048018101180c0f0000e0f940d80c0d0a56180d041113100303940c03055003c5001c0040c0305d030911000f4104d01041002c6c006a240a03400d44440d0700130300e1181c2c0c00d4440041000002c00000b00982483c01240c0c121800780706554900060140c0030700e0040c068a4000d42239005024896201501804580100465817540c20000000703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 88532959 1250 88531709 88531721
    0x3030807020606100c02060d0908030a0608030c03040302190b0f12090d0e010513081002031e0f0109090204020d0509010c020f01090c050d0302011401090b090609010b03040b06040e0d0305060a0f18 86
    0x2c2c2c0c0c0550104123008103004544a4590380d1841101c42030745038038010070840101d90a5078030007400368000308070100d1045004003c0350185da50498065240b007000ca0702496501c00150000b2000e52400a0069030781c1d4101005020f02c1114524000207a03a03a55110760f84030b06450a214012500004a00c2807540c021405443d1b003480d16515030403a690f82e10111840c0210390012262110340c0001030200d0b186154000c07850360086036462035039074100740c0950340404105215848403941c0e1222000110b42d2240c0499140802c0c031001440b0703138248401043d00801c5500d8651016108405074800782d0340040c0925607039941c010b13803110741d15850300092010b00d88040804030115583c51128440240c3c4901905010706a000000070714408044144134510101800031842504030100410850280700f0840368071941c40b41c044103883d00c0d10408980601f449103030356100d9000d000000000c590b41640f10764811078040710981c0b00a691080ca080303030040785d80514880c90414020001e03810010360000c17 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 88534209 1250 88532959 88532963
    0x12030c02030309030a06091211030a183c0b1209010e0132060a090b01020f06130203060c1612110a0b09010c02010e07051e0d0c03030807020606100c 65
    0x28918205402002a003820011741003290044d60744da00c01020f1043c2c142079150480b8480c1001c60152552040a5503240949905181080750120340b01c03181c0c40340c2400d0400203000c08101d080310514024402400d5691100c241c0d17980540100c1c00030740000c0c40c0c0c0c400c10111041d070150309281c900040101c20840000400000701c030340d25070500c400555024407400c00b030380500035400078110750342c040004000c6142040f01c44985c050442403007440d13074901210100310f440c102d0700080c905645c840180e080507440949040360340902403c21011050a111040c4040d00c220300743c6420350b80d01e03244c2008038020307403182c9162411250107030310010b0340c04004a64080305600f007040500d05003080712441c00e04410fa08035441c21640060000c00582402000184c44040c0000c0c0001e44044e242e040d0750315428401c051240c69250342c603202006c8101030340031541001810300c1c900c41c210790403c0301040e5040c0c801100010001d00000d04443d1000c0b413030034042c2c0030080410f001040c400101b2a1307110408601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 88535459 1250 88534209 88534213
    0xc0616020105070b07052502010801151814010f020604120806030307240c020a0b070f0905040f020c0708060c160602090d0605010e090304051f02070506040f050906060412030c0203 79
    0x2c84000c138039180c00103440740a107940c446035124848420340401042c1c2c64040b01a42d0020700148005030b82044800b419501d80e003c0c881120842c0000484201102c5801880422600c0c0d0001c2111880409402c9568400780ca641d4440134242c8412a0744807411900580030040400c0c00b46009031084006581240d40141240d081c0a26600c07500140740200c406ea0b0189141c03485c01c4d6000841a000d8117013144031030300140440160907154821100f1000b00400b007005001010008014040c000503c003903e03002d001000407146010800d0025442811000304511902100140e5500c000800c0c1d84201e11559015050003a240c81c0300c5400b8078500001c03a900794003403140d10055201c021b1012541c0780580d4010440d9498803a002c202c02c0c4002e401c0c20303501d0b0010081408642c841c140e84014500c076506006440c0300300b4200403810440c041c0c005a600a500050014030518514980740a461013100d0340305031515941c00304440351042c2e00c60440660b03540598440480c0c050701d100e10341c250001c1c1c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 88536709 1250 88535459 88535467
    0x1170606100203040509070f030b0d030804030804020a090603050c0a0b0903070303050904060306020d0b130e0d180e0403170105010c020a12020118080d090801020906090d0c03150e010e0c0616020105 87
    0x2000c4c41b00031a49480000c0300c400300800d4040e818020800403c20540303a0340c0a114050b00e00400c504030090014061200441c0410704544501001d100200740e0185e041040715101d11b0f0141d1585501525248101c846240c0032984400301c0c0200c61340840000e00819542e03186a81c241d500390030010425a1060f9078402c0040480c1050000341200c0d5441b16000404a859104100700403c0280c43d50b58100e19000c0b1800490304001150082c0f421107040000003120112403101002116410410003468500141300800d85c00804e0b8511451000d44442c0c84c50ba210f400441d2250030b8150065840022204108044031112190891241c0189030510720b09007501a00c03111441960701141c5140c0c0b02008904039035602110030360140554100940c9000b44d6800000c601d802400724543c0700b4820259031004104541c0c09100c02954400e80019200d07408140440052035052058503c40d4241003480200303110118028040c0d450080003941445c0100352130701d03080b62400204034184a4100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 88537959 1250 88536709 88536719
    0xf0a03170d050c091f052508070501090201022407030c030f05042303031905091e03090a14090a0507030e010f060302030c060f0304170912070302090117060610020304 73
    0x4000c0b940302c1e06180c040c2c240d441a000d03052000a070840328140c29099800e8102040f284e03448411102a4440300042400b0072042d011184103c50146000a0034888000350180c00c01c10103400c4a58140e00036020303942c1c840301074020049039071504198082c041d41d0b0b1b07200003071406010b075015602d810580d140c00101e950341c0303601480031500c0c10744040e2002005902501e0954200420f198400000a0b006d1805d40c144240078481c4480340e1918190038584480004044039404c2006500350074200c080d4900481020400640340d40c482c07101a40154030100c0040f0b003074114000c10818410300a0b0105c822682d038408000d00a1001910100406413150384100b00d80301c090103462000c2c2c040c0b601c0000c10500d075104143c941044401c4050040405024421114822209495025070071412103001c2e21450610082c1c1846914001d550141c00c1c1d40000d01c59030800201542903d02c00e440148150362100c0d107062401140d0718400a0aa00c001d00058581c1850040000d02c4070540c01168200790b151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 88539209 1250 88537959 88537961
    0xc0e04031e0804060c02071202040c030b100c05010c0801050f01030e0c181e090a03080a020708032404020c0a06110f030928080702010305060d170a030b0f0a03170d 72
    0x42104a000030344010b05220500806100e050b12484450001b02041032400b2001b0f0b0a05031140d8000e4821755a138849034142070b01079041b5551804004190594104100c00c02400b03520300c62200391415881c2c034000d0120140541c44480c1a10340c0100203880d184134901c01180079004003200f0328003600a0701c0072108951108403c041e01042d40900084040c58031003180b8001801c091102c444e07100b5801c003030040d044404124030828039010b01d40707500701c0d42d14145800c2c080e21404500a0042c171001080040c00b00802e003041e03c3d00c55146a141507070b44400c408100a0307008084c82041e403504516490800290190b00c01d81d07402c001e240103d8103081e0802e203001040c0d04202e5071807a281d08800e01010002130f00207074896024012820483d80000c035a100d4034481c0c003810750028181640d4001281c0d030395580000024000c5d07401a07001d4840b40140301341c1d115039040301c2021000b0034102081074035a8a04038245422900d0082c1c1018012482c54807130920b00000c40c4400c1c010382204001814000f005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 88540459 1250 88539209 88539257
    0x717040b0a02100606050708031e01090f0c030b09180c0d031707020d0c11030a0f0309211a0c0705010e07030b0a02070b0105040b040209030303040506220c0e0403 71
    0x24054032140c603200c21034400ba04001208114180903890703c94140030701d6400206881a1035041043c0c1c0b9100d69421040000140e00a00508000f412000001900e03485540182c016078461480500c681140d144080e07080e95400c16109620402040c00a40821803241c617410208000c04203e8800014000203e141001c645e1019400540c140010360000c181da0340c00f85801958510081581c42c140c880c0041c654000544010903081c1d40b01044841603a003004113280640d004812281200610b14011780402140e10804407104841e158200b00d54040c00307219150f082e0007851a070000080742e2a810000c080081c003e640394503040c0044c03000708401b4440d2251582c0b105c2c004050890850600070f035240d40040400400707a004000d00000200c014502904590064070046003500c2088001801382c0541c00403190076110100410090280001c0c00e2801602180071a2090a4140701815920a101207000e48401c5050000b007190314104000190b1041c001d180c4210904154401c807024280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 88541709 1250 88540459 88540469
    0x5040b041103040b060907140702010e010c0503270102010b1f0207170d03050f060d020d020319080d0e0708030a050901050d090b0a110a02120705010f150305010b0d0309050402071704 80
    0x400f600401602d8180709222540000060900b008230b510910300f580414400c4080082c10450f4692085500780d000d8078a03440040d03880701c2683d44413000b58000504034807a883c06881030400d5800d0310605540107101d290f54414015000c000c041c0a03588011090b01141496942184112280020076480465280b50400f9032400a400800140360005065600251010061801d80000d1008070b941c1c0f608040c80c89681910046c000710385900019081448203110303044903800c8011490204442c903402003014800c1000e04000340c01c1d5901d04250744010700d016242540d40100b000f4100140120080d1443d1801450880d1911607002a000305491800320201c4034905203505200e54000c50b8050703400c4105600410074200b440c0c01600035510280b4030701585001d000091402c0500c03001303400c031084446c41c03194140030054040100040009107844140d840c2d501e41080c0b0540e41c5040d80c11664080d405a5450000905150401c802940864402c0310880901d0340c5048450504c24040d00040c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 88542959 1250 88541709 88541723
    0x607110a0206210907150305060d0b04030915050a08090609151003120c2006040603020c030d050412080901050412050a02150a1a0a08070311060d0e06040c080c030705040b04110304 79
    0x16251040c01d000c151b1041002805050a04c002c1003159203407927a02006d65900248200110345807810161824005508901003051401c401102d4842d0400001c02059140e9a43c020f5140d81c2c5800c0107490f91400d9900c901c41da084240c4850991020786032681d04512141c0d025506c15a0302ea17590300310241244000300100b010700a007041803240070980075503503a200d84154504c0f01100400218203220702c0c0200301c14954049060880b00d1802c00507a060b01c3c10740441005203040504003039400f0b10b00c0c2501c000004540e03000080403604180242400b035070344894002c000d01030707270307c001c2d0364076001080c0f0801180705e0054039540309528684114020005c100d00040c101482d0001d0740c5580324450b2415005040d601020444448001004d00449030400400075403680024005003140c4140000100428201030056140d1540459124047d03031141d04505c04685d0f4600394a074840403111005a0703d0340002070104041c0c10309405c07080505000900010b42d81d01501410b24040d00140d400303a41c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 88544209 1250 88542959 88542973
    0x1407030f0c080c0a0b0a0302130801020c0105010b0a050304031b15050601140a090306020304060b0904120807090e192007021e0a03060e010b0a03060e0607110a02062109 74
    0x122a804070a4030192981002800c40340710b826001c0b8560404134411048020b40000300160b00f40c0c8a9410340d80002040c1c0301110314141d0301c0e03041c94040c3d00029a048025460301e4000200340010f8000c681100c0c10607100c0f1402d56456031001e407501100711942100152f8250303035010000300001441d9118013220b13000060541070400006101e207040c20300405007803404010315428540c03c8103804040300c1e03009202590703e50311450007002034a440e040c2580c01007000c400303100c100f02c0c0d00c86101a0000d00340c1d0b544a0300c0d503070b912400c0751110302500ca0300080724445004240402012144d05030302c01000e02d400300746070301d41c0700540c0e600580d154550160120301007100411840d00513110000c144400310103007402c491a00000fa0500b503207210007884259102c0c2d0020340c0060a42149068000081490340421303034a04144020340520506074a450140700c00148455020b105420b441c0c8011000030135182c5502d45c24001c169005050010051050101c00d02002c604011400c0c41590304102030100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 88545459 1250 88544209 88544213
    0xb031e0a05060903030601051c0f090302060f060d0f0303090f05030a09061103030708010b0309070b070c14090c09040b1201060b041d0c09010c02010302090a0609051c020f0405041407030f 82
    0xc1c40b0b8054030302c00c4160020402d010b01d582e40241515010034842e5662480d400c880348a00c0020320341c140e001d00c1202d0401011f07100f070580125111384501400c071010301179990740794204408150b45000040808480d41c0400001c02c0c0300c3d601c0600c0c007a11442d245800d884035030300c036030b469504103400d4030300011000340042c050141d010100b0240450035800460860030302007802750801005008000d0000004000543c0c100f0040000c040140310a5403500c0d0b0760320050502c075000c80340074001d070b00280c030110301d551403103061280140e8499100028180e007060504e90402c40036007980e40110751b00003070062000c41030320000e108010080814a40c0b140d034452074803510503481804804c0c0700840030001400c1221000440086961108003480c110414003460b10045e0001e00803946500d401543c40a8045100d81d001a000750540d502110444941c0310a101480d032101480c020082d049070350401d45110034200350700419005442807104540116003220b16a2400840d90302c250352004000142c001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 88546709 1250 88545459 88545463
    0x92b05190c0204060b0d24030f0201020a080f0301050901170d120b09090a03020c0d05060103020603070c1509061506050f030a0b100c12030501050d020907030f1a18040201120b031e0a05 81
    0x7d079019008071b11101c040040e078547c40034045220280040c051500380204580c1300780300023038a1552000305192540324170311055600d9002400340d2400303007a104c0d001041e10681e005030040449a00c3c4001c0c940304119a804480b410100c40f0801c0c10303561218101c11040d650007207210720400c140c6008101a00e5103040091512a40c4540070740616070703c10042c2c0100d030000c11110305480c0c0544805940740c40304001282c0a201078a8080c1129458080e9039100c4000d035001035041500903881404180c01c03191b21420840b02c148a540c001c140200050b65020000c00051580240d60010018944031420701040c005656490084002002500c1a801f0045034851145142100d8078081105604040214001b00388041010380300c0c511440000304000d10a404c0100d0900000b05d09001c00b0f10082d1075400301c0b9484040b802e11506040800850750442018400c0c800c0340c059444402d030302d02c0680560000d0074503803c125050b0285081d0428074142e000f41c2c5515a400c13007001001107424a050440c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 88547959 1250 88546709 88546721
    0x60509031204050d03050307050d0614190f12060204030f0f140106030b01170a02121011090108060d061112060f01030e030a26092b05190c0204060b0d 66
    0x9120301c0c000d020030b1069450350040307816003d900d070a0541e0b40303494130304090f02c01d4003840c2c154440850800c030b4082221151000c1e035003040c0000369016030200850100c0b0884c1103009000d684261141c0030020401074401d2285051440e000b070000615040e00d0b500e8007161070803009019a1140303000c00740f8000700441204c08120680c01b00000704003850440c0e880c00c41e05501845000180010b003404001071120900400c00060b0340100300052020003c0c3c00c15445244040c20114560f05c0e00101340c56180400b022200340820581d200030305070340d032441001888580b0709420f80d009641c800d50480300f60b48000041c01028602a0350030140c0c40c1400c100090340c4001c00e40c00c3d04160425220008400c400001d880c0c0d50701850070800d498100e401720800707007891806015407409006400340007242402240f0400488125022032000d5030101090f00a0304d0150f4940c14006001004102c9030a030941c0e44050130780000d4905919020401d80001d01500c14503007000307252290000f08284d001400f807180f2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 88549209 1250 88547959 88547983
    0x5090a0b0d0213021318180c030f050f060a0b15120705090301020c0102031e070212030a0c030b220606030c080a1805031206030615031e1606050903 65
    0x144480c16500000c541c44145040009025060341040c2c140000c030f807070b0180c841000204080365482d076071300c2c40341101906d546107885116618101004003a00c0001008070505500511622021851a541c0c504040301c07140b002d440c0b03401001c50001d1f0030017081c02658050704a0280206080d95414108030113000c00c40d249441c2000c0801204501900c00350740d0903480825802d20940701c10441c00424060300c110581080554800410400c189088100c1c0803440405074540c05203903983c0107003d998601c152040a40060380c1400051400303005500099048030341850046208a40c0c1808500c0c041810804807001c40820550b0301c000110030700c1307030fa0000c0005103014400c00842c83c0c8060415180030300400c10540e210300b0400c26404072032040e84041c03907000080341d6603500710400c07003a01c0710015610f8520a014090125042c44c0c04212035206c01a80200a4100c0403910079601059107518102060180034582030507400d00000d141c210000c0125456040c1e691308044105400d0601c05800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 88550459 1250 88549209 88549211
    0x12041524080c12101a040f1a04020406140c010f05010b120912040308091206190615080a0207020f03030c0d03062c0a110f0c2116020d05011505090a 65
    0x28001902e01c009a13600d0900407000c40051041083c8160541070200205d074903800c5400c006110034880d201c1c0d8009014925948200d2004600d4001000140e1080d84550030000311540c0303c01840c40c00c090001d0450300d24a00000801034088581e10044c0c42099010b56050000444c2e032000304800000b83c15480000c00c2d0241c00e845101c4040100a0f02841c0405032803914003181c2c0d001503845032620b00201c0458a401c8425600e04410020710054205110b42480e41c141500090700c08482e840340301340f451154498400d5956503c081c04000c7d00450b4059074818002c1d820500507881c18001491b9841840018003000e140d00c240203000e480c010383c0011031450000300c510b1940060461940b049481c44500d01e42c09898804403000a4048080040c6030100b0010b500c03036103400e004009280c2e01c4686000e442c1e126040320500191000032080b003600c656801c009034010320b0020741c40702d42814802002c521b150050364841c3d50859a2103980e42003101c5081400388a54900704a03181e9110184001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 88551709 1250 88550459 88550479
    0xc02040906090b0f013b010f0611030304051506060d05090607090806100501081008030c0d2703080c0a17030402010e030a150f020409020a03061a12041524080c 70
    0x1540c40d0003000c00b403800c6002c2c200c100a01c1b080e02c2184000f1101c80b0148812903502d5840d102c0542d10f40b0400d22076540419804450010003100200a03207101d2a044406400d038540103031b84080380c402c0c00821055008000700000440c0d0b140601c40c4500032104000100564941128054640c10140d0031030000c95200d00308001e20040051101000d8038420705e440c1c4c07042d844840d2542c05200a9030007100f21404049405480324000182c5d01d0904181951171074411000100c80c0d8a100b4800b054490402c4000c8800707001086055004006403900d0b441210406071054494642a041c1d0401c03520642e040001880107541e482107107922204822800f40c061650243c1d600c050503d6000e25606900ea25140203880510b00c03641510024540001c0039503480700c003164014020100c90048101c2241e601c010f03d02d0840000054800c1c041c170f02c45075480583c13a142c07200d602c5006602e9204007900c1d22140c0d001b40a03680b02d03224014560070b4048500545040c141a80c1c24200344900060090b0700d102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 88552959 1250 88551709 88551719
    0xc03110a050a0f05030c07030506040209101214160f08070b0a080f0a060b0307030504060f1a0108090109021504030b061525020306090d080105060f09010f0c02040906090b0f01 77
    0x400e0111405a0203c4200ca100c000381c50f08900f0f502404802d040d860240c01c10000500c0707008601284201e01c00c0b00c0c10140ca5680c0b940d00304a42000b405021907110000041c200040c400540c5038465030744200444042185d40e0818900f8401c0c150810603c040030702200308822001001600090712071321406608003440644000d040b80d40080529924403940d00c04070781d50031a5a8802c40140500c1c1c02c6240c0c0d00d1510503c0a00908020b0780c0441c2c000e13240035129204e5000d20322400c81c0f038814428a0314010710024004440300c1101030b0419640c3d540e41c041000c0113903a440d001940084660f6421038981d031039401d0a03010610024a01409401c1e211880d1103014055011580e410002039003a040c1003100026000c0003002e41e050080d058440c032024880758810000742c0e2104040c4a50b03919003d6030b04d81060040a020390b440c04048400300f842990041c3d0b026483d14280e0f900e0390b1520080c0c0d00c07116000201540c12000303080c0d0719a60b0f03840101c402e00039135209207507100c0c104403003c140c65407601e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 88554209 1250 88552959 88552963
    0xc0307080d090605010b07110108070504170309060307020c181003060905012904180f0b1807030308060a05040902090a1806020d0506010908071415190c03110a05 71
    0x8200248112400142030950010355401540b059400002c100055a180c0c00b00310742d01c1d48000c030203517a00404022002034543c42001c00c1e13485001c0550303a0505052070117003000c6120a6004103031a05000c00c0c0803408181e1a6000654428845940208080c0d06c0040034401000d0f03540d1021a05010130404120740174500020801c116580321400080311440303420301c0390040c82c00c800c504158000080f07440f07100709050400019142c000b12403c1140c040401d0b00e1601c2d040182800902c43c0000410300380200c0e05400b040d962000000356480d40c1114903200e1642860103940040f40441d50640a200e12070810015803409080290742c10010035a8a400140500390000d0465004540300e10032401300b5038155440096850b0701140c29911900070b00d0b51180501400c0781e0040c0041c40352040080c400b1000503030203081310041c00c0d905180e50b12200c01d00c9100c1500e0103104070081400c110a441e1183c1581c03950400140da59151441c05441c1e14004200c0e0300ca49100b0302c09640140c030040082400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 88555459 1250 88554209 88554217
    0x3020a0b160f02010c02060313060e0c150c011803030203010311060309100906110c03091c03080714040b04090b0102102003130b010602030409050a061202060319020307030609110c03 80
    0x1c09905844482c15100403240c001d044400250400804001d200300613100b05035102e00f0611401060058000344035500b540c405403001800e07800408100d0f074240081b1440d008004005480e0008216461320890080140c0c04074041200004d900000410a010446c11803030300b004000c45165286040644855a95002e0100c1402c07074656503034040b90030030005174009042c40d011170030110b0311112003081c45520781d00000c4445008504071800130700c541032104010700507103525480d03208103911894412580c03076510700c0260040070010030000c078280c01c80300c024000802c040310011a01644010009060140362464120a030381460303030070032248030f2003441d1140e158406101240c49507203500c2e845106140c2d002d0084d10b10745602001264140d0f000c8010000c1c1d41c01c072081030040c7e4803074003558400c072071140c03242458000159214400514100c001141c110b41c075071842c0ca5a0034611303100e0408a0b40159041c9000c00c1ea614810807040b00203001d04200f0305140a42a4240000d0914982d01c0e403007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 88556709 1250 88555459 88555463
    0x18041509020a09050306010b04050a0803090105190302070203030f04060f0c0b0106030e07090608070303080c04030b1b09040e0c0a09050c0f07030c0f03090608060306072118050703020a0b16 83
    0x41c02050803030350765101e42c03070000092500808a410f996541e203203806190303000e80109401401c0307403107000c1100c1d00c0c00401c071284050180d440c1740c03400b140c02c0c5829a01e192803259460425800b04180405a60100041c003d400113064403640c0e101c0c0740000c0030300700900400d0500180203035401e0303110200c1c0441c0301c5641100da007402c0128108280041c040d04000e01c6401459619180140c0494888000281041541e105c2d031a010550b840e0401d03c400e0f1405144001070100400c03000084101c1c0421484240201d0f515459505141070350000400740c4038403800d000b919030b100e620380483c2441e000354481e00406040800b0066410040c400b00ca045c80340c1e01c1060150a800507181041620420070f102c0c40940103007621405401030701d402082c1c5c80c0c5500c15400016802d0010508074900410044c1c080d00194480710056264106000c00d102209984030109a55602e500062810b08080200e0154415800b6040c11401c5204220f00120315810030310744081c05005040c034440c5107820900e0526 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 88557959 1250 88556709 88556711
    0x2010f0305150d05160506040f03110d060e0a150b09040609020a08070b04080705040b0906090406020c010c2102030906011820090a082a210318041509 66
    0x1640e161848452140c200001d183c01c03004000c031807004c0c481e01140b000c0e56903c8505080c804140c0c2d03030701007100c540113a00414088803a441010800209803403404811074402404d864052034103921200100c841c01134a05583e138000030f14140c100061507040358200c00c20b80700c041115500703000206040f404000c00041c030203695440c040c1c0c15940c03001d54101c0104106c0c800c4404d4291290407542c40c0f41c015109481442c13048100110345c41c03505000b5100c5140c80a0719924065681908000b00c140004d030003075442c16801c10241c0401c11080c0900340621126440d03107614202210451201c400d4180c070021840391050040c890440800701e1540d04490048105600c840c001196810080c10801141c000c0c0f901a041106070000c8910f0281c5210b0100301c2d40140640c0d81d401506484088444102c00780350103813903000d101f010040c003640000c02c4010340702d02241007400f001c540f4250351f940c0076038446a1011680d10810410701c3c0c40540d4000c010b03902031224010002d01590210114080d40b0041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 88559209 1250 88557959 88557961
    0x406090b0c070e090f0c0102061b0904150618050d02100f1403010e0402030d11060105010f0302070209010b04031e150c0203090d2103050c18010507050d03050114010c02010f0305 78
    0x20300040207258054603000e03c5410031824440c141d5603440402c601002d000d4040d08250348095070000c1826813040c407950106940003032059a03984459802150b107664069520302c1e4103081d020249411501400807906c0d0004e11000140040940030216032210303118800312035032500182c60b42032541c8851582401d140d00d1007088078105488004d5503a49103e410800032000142c1c14040368501c43c011b600a44c11380f42034202c0c0e1102156144c1c20084a10b16a40c02000100641d501ca80060150641c5030319005083c00b51a900055003030b030084e44070200c5078130042424070612000f081000507071a030389000404440002c0e695505003c0403c002000c2c0707940c0e40c54590f081c450081c011101410001051107152035058074203010380c941d50000c200814072445103828803140c080d00c11117010301388410030301d41418070315502420000450446039041000a0000900245003048402071203846500c02141542c140b109915112103118074030350400100c1005900982d80112041c14840c42c145008a42c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 88560459 1250 88559209 88559227
    0x318080f0a24021204021807020622061104060806010f140703050d05160e01020a0201090b07030c140105041109010e04020f030111070515010519181805030702090a020406090b 77
    0x1d0007200c50402c490703a40002500041e03096003030070b40d41c80380b4803c6070800b4443e80c0b01640300e00d031480b04403000405070b030245001c21201c000403d01c1d91540c0d20040b1006500050310b42e500c1d0151881c0769002e000c18500400d00f448115000004207510035001e203428035200f4030304103004143c021052a00e40c1c012400241d8102810b2280040341c4600700c0c0d1000130300180c24200c03e0a841d110700140028001990740314900741360f6101080003075540c0e405030b66000003203051208402e40d50307000034412414030071210340c5070380001d8039420102000f00d409e8000003010f00e860305043c142245504803c9108a494078014070056003074042e115001601a030341000c9100084000c240140701580140b0348400010901808011001034051400c80340c1038907411b0940d03601d00610084038115010807100c982d00c07203010f100101448a18070100c43c8e03074020105128002c000369440318104004141c45541001500c0750a50402d00d01850b0042c02c068801c51070913240482c01410525240100840b0318400104040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 88561709 1250 88560459 88560503
    0x30c0d05070207030f03020a1505060f090a02070c060c0302070609260703080f090a090911010c0f0b010b0903060f10090b0d0203010f0506090c040b191701030318080f0a 74
    0xf002e1035010012400e542d07802c0c10b020b943c84003c008115254400d00d00e20041e40c880346c0c095140600c0c0701401e00d030600c02c018001c103c51040000c054034500b5900b0f01c50000854100e240901c0100a16204e6406109071810700a00341905a0064414004010070030800c05569601c2a810030315146001e10008039003444081c1012010f90000c1c044840100f07916905101c104020f2021103c00c545803000d1a5890f0720240035203032005406045405201043c0c24503500542c805070000384940424044c140c080d0307803110b035541e00a0300502c100a002040c03c003c141020000303c0e4003e081c026004081e85405089420081c145001c0d010701240c450751031841075110620f4004203e54010000d0085003004c0040e81c004040460b1034134032640c240303c080707503020284100701e0b01541d140000035071501d00e2800340038002c1d4010715081d0b41004010b02018a00700003140c1510302840c0f083d5150b0308091440c803c42541c5c001590460203294021360500302a29200007601c0b4440c0d0361060050085045000c00f481c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 88562959 1250 88561709 88561723
    0x904060b030a060c02030c01060801060e040303050601050f1303030e0105030405060c0913051f0501080c040302062b0b01110f060a230928150b040e0a0309090c05030c0d050702 77
    0x404144c01c007103400600b0394021000d07003e41d1100d14000c12886946501e50380c00d954462240ba40d0502d0000d002c01c0c0880e03c01d800056000d04103052803841c10b010380c3e480c000164000480e050b50f981c020300f01031040562101e02115103d03004d01e8983e083d8181500c2c0c003600d9120150514881c00700c0007503045069114901050b2246290070402c20142c030303002400182c0142200c1303520a42c2c04000740c001c5180e60060650301e0051181c100c920b410a0f0441e0300b48841c40d486442e081307140074050306440c66001d40390310607a681120980400b00f084842c000002d0940340c104540105240c100001c0c01d05488000141710b07522000c1360002040707659801243d074221305074183c1c15014988013042000354215001402102481d12143e4410358090030346a180485481250010580480558507800c00300300c0b900211843d0100603c0050340380550000765207000c04400040740030410784171040150700058880c0da6019101400e00502d0351401c0c2d40c104a891042c10100300e00503503140040f4420310f100304880 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 88564209 1250 88562959 88562963
    0xf0111010f0902030d020703080315011b0807020a050604050f0402070c090e0604030f0e0d24060f0e010503010204030803060d11061215030f030d0903021f02071a060904060b030a 78
    0x208140140207448501620344181c0a901078802e00c0703d112115440001c82c1c02c116a0003100a6003076444559428030300300390142d5403e042240741c10038518005041d4445811103031040c0d807a19502c0001d44144020184140d00081c0b080206210400c05502c801514014403a0f0840f0700603924452440c200c65000101c0c0c02551060b0700d130059508911000066042c043e80c0261596049030728699021a48801d86030304031500160001005000034401c81a00d00c41c1a00e40c40b5901d090010004004c41181c440ea803156248084200d0308100240f88004603a0141405a009506d840d0070341c1c40320f150621001d80450b000d1220082c44505010f901404c28419803c010026a5201a5624007680c3d00c4404e03100ca504005411864141c44e00e070004195000c7c8221001840c240121180103000402c00c80e841941540a07440141000700b001780c230071018110f03d0394401a1922141d040100340381610442040143c0242403d2111aa0b0f0744103035182d002d6400300f4081004000720010a0400d40031003c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 88565459 1250 88564209 88564211
    0x10f050d090c290c1c110d05030604111303032109060203060109080d080412050f0c0a03080610081501030209040203070314070f0c0b07090305030a020f0105010603020301030b060f011101 82
    0x224410024841e0382d4a030031940d4030f900c012540201c4a421152148045202480c2d200c8a5809042c81800804102c400f04604100904000d000070075828803540c40f94030400644000f0030007496191030701c260505008041c40395828084503002d4034003a0107940c007028081c00381e170451150805c083c2071506a003040c0c041500348885000f5143c82000f03034001f524002d02050045a0102c1c1c0c083e000030340d22841c40c01541c1c2ea20f48644690700c41c240202c1650003000104401040064002e040c950000d00324901c0c54802400400d00c0f42c00d00400040000c1d103464801da030a4071001c88801d0744803038050b4022061001d005041c00d010001030f002485010040c68100d03001100300800c60b80c0680c413004502000618042207941d4011044444614034119900440c0744004020049240d044a03542d000c145410301c846110307142d490b0b140c5507410102c4000011703400303407843d480c10040a01420340100100d080075802c4d5411a5150068580020401e07030040d00110310030209a0b1064070280062204100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 88566709 1250 88565459 88565483
    0x180612050a0912030501050f060304110f030f0a0804080f01020306031f0213030f02040c0203090d0b10030b0c071205040f06030b0102010b04180302071508070c051f050604150302010f050d09 83
    0x100138000e07020920403240304000308180c2d20303458102203048902c01c55102050540016030081045114601301c280039415100c0c00428105829003040740790505400fa952080c0c4944c9040c10952800064020200e1a0f900510070b00c05d464074009208420840603040c140c0f010f181c564aaa00203019404603041e6060301202c00101380200495540b038018001e1300c06200410b16403d090381d5034441d03a2142900200710020b10408101d100d4000d0b0b40280d4006420300c80c082e62511001d80d281c030706480405d00554000360300c1041115100314040c904103d0306009003040e14240811064074070600c110402d0603201c01160149078400e41c008031900300000d008129580c29281e03041152402da401c100c0140c4039500c40821070161013842860225020b9070b40e41e410b50751b48042116152421602104c161041c113003040365400840c41e0804072681400e40014075031400c0001c0100703840503030610f4080311a40400074800f60f68403024101c956511030400d80d584100d000151402040c01242c058402500c00b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 88567959 1250 88566709 88566743
    0xa08070804081e1c0c0509010e0a030f03020c0a060810050405041a190b04050c0912100903080f01060e0325080f0a030e01080f07140702030616180612050a09 69
    0x11010344045520612446948000c407005041218217100c0380001140091020f8034007584a403000041c02e000280c10902510740e40d0380c0d041041c1242d04401c40c0560803a40c0010410b05011100304020005031401c820341c3c0c2090b0300003902c100154000c1500441c0c81c1e40010301441908001d000c1400500000002c46151805007505c203941541c02121043d07082038583c031054a410700406008140150055140418480410440d0000d00c0c007240c105000c0c3d100c0c54500319641e4403035442d02c10700a89a514452500c601c0a42d01180d050308030070706105080f0240c08258400240c00079030800000390600c2940c10000002252861a9201180360320820150315480e1202046516400e40b080c0c540309444210f400054400b81022103204425504c214001103886201d506c107611001e10071032403503260208a4012a0810360102d40040d40690381142c0101d817268010329043d00184002804000c4e036060143c010034039000b01d010300f4811910394022602e00031950340800303004ca501c106091140c603100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 88569209 1250 88567959 88568017
    0x8040209061f0e09011520010608030703080a0b0109030305181f05040e0a090f080f0d090501021b030901020a110a08070f06080106090608040b07030e010203010b1e0a0807080408 78
    0x40c0c80f40b10b00511046000103054000000c81d003003008115110b00b49039145800380301c9440718035410564515901d0314000100528140005e10741640259600c00382c0346050b00341d82003500d1116003528104000c145040012940c46010341d8121100e502001c100200c0120000300b001c0510340c0c0b200c0c0320844400c2c02030440e1390028001e100322601d10480380c0031a62104400000c4680188000d040000044405d00c0010300b100010070b41d0aa5000140d0b0134242410400c03800c0b14040d21007103965a50003d003414a18680c2c21740c00e0340201158008510300000040000d444042c02a0003d0001071540f43ca4111036481c11170714405002c0000448030025a03e8400325210b00e01441440702003001c860010400e6841000003000b0342c0d50b19142d44c000b40c4c40340d030303100341c000c01005008404050380c841e42e00d038452030700307000850003407044a5070640c54a40580c1103440c00652141c1c00c200ca40303410800e48070400c2c0c0280c10300d0b520640c20b081c840e400350703502d00301082c0724031030304000c0d051100e201c3c0440140c01c051 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 88570459 1250 88569209 88569227
    0x108010213050d050c090a18030c021305010f05120c060309012301050108011a13080105011802030603060c0702010210141603020a0909020a050c0114060103180308040209061f 77
    0x1030000d107500360359641c4140072a400110308050559000b1100b40c0225041c40b1312142d0b000b006110001071006c1c0150341c1c0701d000d1921f8031000c80003d030707072268400309600c0c3c09001d0700c050101810040107594944840042559002d1003920300502e8505810711059a00740b15841020301c0c00380400e5079170300d0180c1840b4004c00202c441089083d25a99942050140c1024454181c62040e1140591a424882001f81d020009407544e00200300400108954418411510000b8003204d0008110b5504205c1c80980007040900031010080c8188100541543c0c0002c80035005209068140c0e921103007400100e081407050348000703006508250b00103040e4140003a40500c075a540d9500c50740034540c980d000310140d02c18105194001810f41c4400c0c09848008da00500d03c030074060600c0d900d40100302c092982910640c80d80ca00401104c20704202003541c16000e20740c0c1e086800305903880150781955028102410140010313025004140000d0116121201e000c84a2407081603c80e44da8070a2007801462211 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 88571709 1250 88570459 88570477
    0x180c0905100e01080c090a06050d0309090507021b0909121c05010905060123040807060503060f0301020c0d050f040e090606041401060e0f060403140a030e3007050901080102 76
    0x5007414000b605459801c5242d069078011000780a050341c041c0200110700401600d503005541d642e0800040707a0703030740812941501e4440d48a03001c000d807070f0030031402c12a880142440207540001d007144031f0100c104c954400400300100c0300c081d05500c540c0719692030843c28111804a050300050441140c90b0311030f0514504803404507043c070903a030b00e84102c1400d07168143c80003800b1450140c12004031241c61030016075200302c42d442403418645d030b072074125103000040d50011022403000800e2103968204000929040c1000741c000b035103080c7d0400341c071fa903503410404d83c2542000341c085400c4404003006422035000304010441d04180d03051003c00c01d03455038410790303107148102c2c034001c09a810303880060a06412105140c13141440042d9080c28010300d0603905501540c0032104200100000e41c038102c92524003101030004014220447c0344c064000d030003140e0254401d03000e03c00c00d11021074000c0c5a0020004200402d019600c0c0c035080358a103042c446400c0158014008000820f040d1815805070142d0340c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 88572959 1250 88571709 88571731
    0x70803070323040333021308070f060503271606031d120702011b0302150a0e0303070c020d0b04051f0e070506210903030708240103180c0905 62
    0xa00b034207041c42c1d441c4694130000b030a000c03542500c00d1814418100c06104d00e490f8110301000600302074220381c1242d05c189000908241802030500c41000c00b008114050700c0d40c03e0300d089034107080900291042c00010700c0700c1c2196901010403442c00407258803039030501e00b01c4000c40b8180c58400183c01940011809420000f03460800f04040350800c4900e14080207205201400c181076000081d402d1b107622a0b10b05034184504002c010801ea180d50000f00700440c040c2d0701030f0000c00c00c00c02c01013201d440d015000960301e038281030909081300380110031241c10038642d050401e190041c910204540980000c2d000d40b02d0180041040f05005020501c14900c9451000002a201c050021501190005607141c140342c0e000d42010300c0241860001850340d19810b8000000d074101c1c080025109210403188400070307030004011700c01c5840e002030003d508035141e01c0c44c140200d144120304400040e201603c0b1810191145212560035400e590412442a006100418100d45840002c2e0240c0015030f40755000d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 88574209 1250 88572959 88573007
    0x1027030303051f09020903011d010c080105030a0506160c05030a09150203132303030d06051503011d040305040f0e060a08060423030409020a030b01022e05090708030703 74
    0x6a038203c0c91070109035018070309481c82d08149808000703412040070b09400d50341c0c03541180d408202c0c070258014840000000411110300340a030003007142a043e400903000b50320102003800018030104440758800c1d49460202d8941c008441e04485079442c0181c003500c036000001d500300b000f541c00a0701c02c0544030403a4660200c0004841c01b2070740c034400d00010380c1c1d0014003144240f291522218281c2e6040300300c0c0c40c1c800304103649540084d00f10340c81890004500d943e1030900300401e0400398013448808408d80001e13419503140140921588183c604100140c1e031840b00080d0400d40a54152005800800c01c04003840c0e40320050580030880640f011440380060550000303100c4000030315144642ea00c040201003003c1c960b088520b4035846414445002e0000340404501c0f141c15101034000700003240d8010982131101c40002e802c0102810446034420014100502c4c0e44c5070118080c440a500d00c000020296201c4400c83d0804002d9000b0007582d0200041502c00c0c1507108201c10380d091325807003109104c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 88575459 1250 88574209 88574221
    0x507050d0806010207030b0604150e0a050c040506040501050a1116050a091515110d08060f09060306360c0a0f06020601050d08070203120414090402030309102703030305 74
    0x8004040b00c01500580c80f50310144005851030140580003800038002060800505000d4003105040c0c0c0c12281e1070407204000c201901c55580151030308541d07c022210b240501300310200c0c401c0e10480c000c003414000001100700400380b003001c0a110302101c0f01c0c02d513400103240d81c0700010008150b1007414810b46410b903012801150600c14401242d4074000e0381c1c1762541c58140d01c29940494110320805211003203102d145010000d0141d911058110781d5400700307514280e0304224000f6a041c1890380038400c0e0a013000042d403400203002d030f00b1010003900740380b03402c01c41c14a851018a0359841402121a0310840d20070a000004e89600410001c0b92540b000d85c6c2c0f104010250210703144680390040c2d214100401080c00e1140040d1100c5010395042480c20045170046440e0885443c0d40e100b8985000070308000281c203075402094290b00845001145003400c2e000695a8000c03a140c2601c100001c0403003000d11801070444403181031024104803140c5d0303407a04180c49400f505200a902080c244400100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 88576709 1250 88575459 88575467
    0x1c0c090e06030703020f15071518030c06020d0902060c0606011b0f02090402010c081303030905010c0804170304080604060b030115030f14030f040f050f0a030804030803250507050d 79
    0x842810701500500c0000c0ca9074003003050443c40170240e160449951180d1000341c511040003003409600604414001c42c5c2018404000c07141066400004202c2d00414030000070b52000c103071200c0642080001d82c840c0303114080c40c8020032080f100250f1120300040d0106003054003180451145000343c82e040703d003030f001c202e286e14007800218000b00030541a403009001447d00b001e80c503400900614142c21180401d513039590603030748944c1149025001c04d400130010141d1100690020f00801c2c41e1282801d24180d81d502014002d0b40207500c1d044030010011090100f081065900901c08081125158102410104010311058a0547c007070b500b0580800709030702c203048042c1e088035844804a05502407946551441042c038201241c054002045900349661200010380041c06003000314404592a12080088940d00505000c0c0102240c0350108081a8444240e90031030b40c002088a94030340d00d034032030001f11400d03141c1d90452068900104016465000002e44001403245e01151400041c241d0180c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88577959 1250 88576709 88576711
    0x40906061121070303050a1404051b0102030408030d1d03030c0a030501090c0503130201020106030b090f070e0606030105060703020a02030d03060810051603020a030b06040e0910050601020a06020f1c0c090e 90
    0x402d0b42820044440020321a5010585c40104030000040340a80c000d81142004002d807000e4170260b214081c41d40c041c0a04039080450071209000661900c0d14040c810381d200d0285400c078001c0160345010004446682048078180c2c81c00d00320607269245018240780301950040ca150100083ca86000425022540d01c1800c2c0c3c89900c3e0f489041c02c6a07111650001407210000049046540755000040014602d035034041c0103094840203000310404000c105440c010030b5a014040c100b81880c14006a604d4000c101c80c10343d070041c0d41840c0c4e2004a424181e00d4096150320094252042568864250303500d6800709054074101e400f6940d90501d00c43c810304c1920000d6030450b004a222307441a0032510f0081e4010302c2004402e0a01040070043c00e4006030054005034040100130791000700b0000908020f0103130140c0550f00480c10030041c141140000d40c1c803582114002e005980c001000c501d0510b11000b0344406a01040300902602c1189403090082d0075461000c1340450308480010660241d91600c04d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 88579209 1250 88577959 88578013
    0xc020307030b0a090b01080606030c030a020a0501050a050705120403021e0306060118030f1505070f08010b070c15020a06050c0405060f030a1803090303020c0604031a09030409060611 80
    0x500c006030940e140d03698004400b078403c400711a96070950400081588081c035000702980c00140015180400906043c0022024254465004003a40400507560310170b850702500c41c01e18010752541e1410000744c85510070700001902c28401c0480569a4541c850700410917603209452840c0e49400703011020070014041c94201d5416005000012020f52260002141c0c081100d800381184650b0398845410420400d402913461942d015400d0903c0c0c0c4903402100e410541d103140c0106028043c2800030440041030086000c0c0e080001081400c0c0440c42a164000d405040030a6028116040e406035807084540b070103c44450404000500b900495816101190006000185400320040c07881da002c0c0d0006180000160380d80c5084e40b04212202107001989210303480f464030f014210f003006441c18110750b2007035120300d000704014400180c04440384c00c0c4d00c0d01040800303100350301c40240260860195400401c1e04600d041d1000420396409440c140201c01c04c24182c0c0e1030000c80010400c005000c901c1340c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 88580459 1250 88579209 88579213
    0x6020c01080c030604150f031a090303010f0311010302120c0d060f050f010309211206150c080a02010603141b040c0f0c0503040504050406020405041a0f010c050c0603010e01150c0203 80
    0x821904040e0441c3c0c0030341e0000c805006c141e50b156102d602134409039800c15202071080c08407104104610749900e07604980312100070740c2590f240c090603184000703940c0402403182038400e007413122a034040d030140c51010008800f1a1614a031041500c1000e400100c01044071500304140001d10b01d00e12004941615006051400c900c0441c0d030054010304200e0104407018403c1c0e03e141c0c501482076414410500d001c40c1c2e5641c00410340c0081c00c0003925955000501594616007850480bc4c2c5c001e4078514010ba4850380c51500c40c00c00c0f04041e40105840d600140c54140340300490070082074046180c42040c00b855040ca8295400041800112241d82803944080b641220302e220701d80b030145a2002c416071050040b00d142945850120b41500c0080e00c044505036000b103401e020a03c0c141c02114600c1201f24403d50302203d00200040c2e1070410300e0303034050500010008681c01d20100b40b1500e4002440505440c0d42c030b5030744403440d00b581d600c04d11840031058440310040b40d5032489254032003892500100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 88581709 1250 88580459 88580461
    0x11206080613170c0703031707021b180c0901091403070b070c09022101090903170c0403020301050c04030203150c030403210c020a0201021e0a080f09030703050706020c01080c03 78
    0x180b0720300700024400094507041c89000f080c500003407680000301815802d200150001501d103280141150380d005904da041c0c0d400000400000550018038040d0000f005013500f802601c01d9004102c1106002146050020100d010040d01000d60002441c10450070381e10702c42c0342a5074011010410305802181c4c1d41c0754100040401000201c2409800502d004625402c4103d6071f030704824003240d1007a5062049c000140c041400006c00c070145642c01000100c0342402903950b690340c0204442c03540800d00160b503e02c2c0340482c0d01d21104e401540c0113150f003d80200007508013640040595001444100e00c40d00c5100e8201c03040300038452119005500e41c0c1d2020f0706585495605455408418031060b90400720b40a0381c100c414814003484200000e580c004d40100c0d81c0d940002801d084049a4030907211141038038444042c400000c8481d02180c000351855141c0c803111000352032a22800700410383c180304980010041c400045094801c555085d0200c0710485030600040d2065030080b50300000c0c2c104140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 88582959 1250 88581709 88581721
    0x1822050a0b04020613060207080d030b0d02040c14130f090c02030a0c020d1e110405010f0302091009060312111507110f01050a0c03180b13080d020a0c020112060806 72
    0x1a01c40d812520003131a071820035042a81c5100d6014081c2d20000040e4030441d01042404d4052040c40685200781c6070600060345140082644020b40010080c0102d581d03516604800b48034103804c00c000c081d0300c04002d50b1101981d401400205075070140c0d041d031300100400054400300501c40d50201810039000f40d820003400c007009036998542082d00303036006101d00c2900c1c1c1c00560340190445403c1a620075520340c3e50002e0825842e04081801d8443c09246860014400703e407000380c421040b40d50455215106079035003018681034608550000c01c00909017000802005440140c3c6c2c850341000703a640c0e980f4504048441e682e03400000d0b205004d0a0b404030049040c0e58404d403005658501e5100460304841190403134942100c204030f444250040d40c6500c0e01c15200d526000d0310480c1045003c2640401303020b9100d032034880700081c03c0031240c000e001e880841005040b1040d60b1840c10810340454489010b48009002c0c1400620101d001949501c924800745000d0f00c030321801c0d04c4c10700300104140d40d144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 88584209 1250 88582959 88582973
    0x17010f0308030c070524130312020a0e090c09100203070c031112060702010522052805030a030c030609090f03030c0201020c0703050a020f0a060f0507030c021822050a 73
    0x3e0190070104070100044004a00100841c50b2096040c02905901c2c9405c0c0e1400d0120910280a0000c800103e008080c0400e40c0601c1480940c20000401a640c1301911000c3d41c1350000d503050140c00501d1501000b2410103980d020700620a0250b07214540d510100c40200e17240c0c814824003e02641d12104244041031011004030b145000103015a1400c011f9459480d10705003040ba030103070040c0e44800811032807100b5020003602e85400002081500d400340d40d10192a40181c4c17843c141005039000c000d8400c61072070110025526081310540b0743c0c415820030010040c10208180c03130042401c1200004d1030218034032520300300680102503c0502d80091b582200609101034580c41150340902c022540e066040c45454011441200200345450440c4144607903d100030004911803141d0013420444680c10505040d100306007842d00310f079584000e00e0207850000003903102039004180900080c0d1a403008800d150701545046032030b06a00d6454a00d105000c10140320000c08a07000609014002054 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 88585459 1250 88584209 88584211
    0x411041a07060608060411040b040b0f060307031d100c0c11330304060f020c100b010507060606030e0105090c062a0a0f0303050705030f070810230117010f030803 71
    0x424400840c0c1140c1d01c21407203107817403415607042d5248054200000c45a241510600603480d00c152070a00401240c94009450010000c1c616806890000009000301d44242d00605083e42e05100c840e564081500701180d484e4a50240144c2d014900070481e09090b000d400d045400b241d00c50b02d500c86800d204020701100000030881e002c0c5407001c035095044080c82070aa1114003e160304c0702c65403207107030900304103040d81d02001d03114520601c1080b0320303a2001030115140000d481c40301400314009810f480125010301c00c20f24050525480d102020a00c2da40c560410811856600000d0006840d40301215444592a01100f54415010000c01c1034103580504400c01d00c1c114030000508c2070724809801410030240303503001c603200c0c0c0c408800041090b40512505070000d0092906504601d010a842150a20701030a010280403c2d40c0002c2c0a0711541d50841014050000e548034510030040341007001da6070b00003a058040f0720448800c840180c0d4420b40181212aa485030b103c006182d074507440e80310b40c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 88586709 1250 88585459 88585463
    0x70602150a0917070c0f061706040c09030f080706050f01030b06030d09060e0102120d0605190b090618040f060f170607050f07060501030506010f0902180f010c021e0411041a07 77
    0x2014060000300040700341b0480c0d0080c6000c5c1c8582c051864850304040740c1340f00c020a2a0b01c0b940c5003220011415500c04a401d00b41c9a0025070044122218180144180100d207001810356080c88200520140440c26841c1240e11501000b403e07500c4040405488120007160b100014101c1d00341000602d20a08080040000600565100c9990f00c5a0304896078802540702c2c181ca915a5020403c41c01c21070a52040031a0f40e070707030700030030141007058245162140c4c1c01c0103485200045032811420b11610700b002c2c0d0382c0d10002c1041151341c1c0c00520081c040c00c100d1041c84000111184006184890b000b085200c2c118200013030000307a6205203055910703400150b00c0f41200fa00a002145c0020705521485020311700510052a1715850150181c003517904503000f5086040c0144000045042c140701416030001040b01d06400c10306c0b191004840c10b20710080080e5020001045c1c0386558202c0c4042c0c03180c080300640b41070100060140d4240e08521940c841c24400420312521030284901c0c804c05014071134 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 88587959 1250 88586709 88586723
    0x250f030605030703060905060610050a03020307090b0706091104110421020316081209060717090d08040302121c110a080301080c0307140f01080612070602150a091707 73
    0x1500d5002283c035100690f00110780099441000e5001d010080140c1c0f03501000486000c0008030b641c40c402010f03070003200450407e040e00400070420050280384000081c1410b9490980c0700c1c0f0079802e080c0043c007a069020760b2031580d689400201400e1502604094400200c00c13a4641841d0059000400c0c2036074103245413098a13101071b5401a80c041c031484180208104021440341d00f0030502c3c5041c09400212111095805c10070b40c2919200c6c2e00039202c01c41d1b04100d000782d814000d40c0d00150180301d4946c040b44c0c015021000a81044107850107001078038000e54000c0c020084035094141d440d0040300a50401300400ca042407103007441050030078901d04000c0d080d1800149166144e07461a0403c4c3c0240455070004000035610781010850240101403032820040070b910b0200214110700c0b42d0700f0b01c4504011005001800ca5150205a141100c013a03804030381040740d030b60400a45030010070f4019800340c02e800000c240e50b000c00b8090421204d0300210902189046100c0c11819507004110485460b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 88589209 1250 88587959 88587971
    0x1090e1b0a08070e09040b0a1a21070e09030f0c25060e040507080705090a05331305130b040c0503010f06080c0405010c0302030f160b250f03 62
    0x10558000c0038002405007600c600c061400c3c9810080c015a402c407400901402d9000104404151b284203a030f5001004588000742000491703c241c1e100c0002241065004444103400752464241c1c200030402c0803145130300761640c0c1c548500480600c50415100380e40240e10a000a0082511982c010881e503064141121758001201d003501e05072491050340c401d2006003581d01000141d400c0f0613983c0d01100220307400c00c602e1408040127040c1c04005803210303082150202e0081004d446804420024041c02407421306102c0c3c3c0c11803c80580b14611340c004c01c0030781c4070820750584c3c4c0010605540702e42401c17060002e101c6040c07205000c2c0306101d007403445100f0b9440341c0d184020760300d0f14424020507443ca03a990981c1c070340c18820701007442c60285d8003900c2041116810000b82075540d6050750305840003480c02010017001410124618000c10491030507442d0002408400820303140207030507070184501000401030f03940007110420710050a0300c01052813031591801310304a1003030500c40342d9400c10782800201c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 88590459 1250 88589209 88589251
    0x90303070f060501030210031811030a1b150207060509060f120403080106030b06120613060e0c03010503070501030b010512090f030705010e1009080f0d0216030513080c01090e 77
    0x581c0e0045081079511665a500601c213604048600c4086042c16003400e0103106a124a21480b45004c900060000903c03203520303507041da4050100d980101e4100c541484a0284c41d0080000402c0500c91074aa42a01440021416001140351002c5580549035181020340d103109104d515889001c42200c404c6080003101140e40048e540c2a001e64000c0d0382d82c0f00558182000a0100c0740341e604031510501c0c1c1402002c80300600ca00e01d15504ca1016551035030f00303180800b0200e0241c022a000703001c004105004010704030022801560491b28120100d5002d29900c80040d0200c4540a211a000038070800c10000f4014002103c90f401141203022180c09c14070104030795056401000c030881d901e944403100caa1904104111a61214100c404200003024003030b60341c07001c1d0340301e20542c90003000b80110b081425a01c155054601011101c2800f501140180c50f009005602152110020114030f1a010401000c0000c0710200d500060311098216420700650400104c00203205a86801940a04c101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 88591709 1250 88590459 88590473
    0x70605042310030b010801060e060406120207050712050d081012050a0506010603290303030609040503070b070504150201050606040b070825050712020108062e05130f1a09030307 78
    0x310301d00c80f0380c0c00290750350032500010490702e01030303104c003080200d40707107125100740e0b40c848c1124110368490504100d054030320050715001e0b0140403400b4005002d00e07540000d400842e1509035200320b10a0741074415241c48150183da04080c1507480244034203070410203100a20854140f0345c1514007c20071654018207942d00c1070300e4400242c001600090b200e00020030030880182e14032085950b101d0400d0120f0380e820011941d81c3c000104590720451001d0041020322500b80b04039140c0940015070402c0500d0060005011075009115040946401c504444001c41c41803103030754020b1a000b00464602840c2001882d81030300314200c140c580c04000c028007071b20850003d01c0d0f0482164400007036542d4140a080860034440a503102901482403d03241c240182c5c0c1c426071903a030001c030071200000484038140003910740c0340c9500b4100c10b810303407c0c1c007200500c030381c202018280700403048c65050403058440c0001e62000c0c40601c50004059410300125182c410098080c00742100058202e0741007030001d0701c0f082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 88592959 1250 88591709 88591729
    0x140c0406060e01030e0c1804140a0303020a0813020108190f1b0201060e070909020f04080a0b061e1302070302150406020a0311070b0612100c0305090106080706050423 73
    0x1030205208094408480d60103000e80c5c141080c110003d0303c0c03643e1501002c03409181044c102480707845240b100282c10400e25040104800800004640e002d148a06e80540203501007514032010030701610014020b0f20300307000403141031a41a0358408c05a110300040461a400d403a9100344010703103594000d290b102c0c01d84511201c4045010701d024182c109030001030300b120155003081a580702410200450550000c248100715040c0c034900582e40d40c0792001140700380c0a0350308503180380d0050070000c0e01406040320041d4001d9104079031000d10700f03900c042d00c3c0c0a4801820919130704001c1180314080c003440c0540c0a0308000d03009005880203410b00b0f608031390394804111400c442c5c040e40407460085081d030500c40c1c80500c1452503509450204561100900260014480f600c900c0d09a41c014080610501c9820110206040c09100e028040e980240140104035040c113459031030301c3ea00040b010800211242145c80d280c85482c541410600c3e41191000780e51946900d040340c0380d0703844946407940c40c889 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 88594209 1250 88592959 88592969
    0x3120c010b0910060f05130b04060210060e160c0503070204060e04030f02030405061b01090b15030606060f120703091719020f03040b070501060518100b16140c0406 72
    0x50a21540c0082002a10001d8820b14201d20500c1060081c2500a070485c1c406403041e0034107540720b218038121a52200381c150040c40240388041000100c10f03400103400004261107000034480c40c0d0300c5a41e0005951001c4030041c03092707000888800c50550103940305030300c500d01500a403842c0c0a0b464002c541902d013154088a03220041c08208014158800b400307040d558500d102940ca014600300018050b0301801222004601c4640001550240251b100064960f0301c4840301307820780341c01409440c0c404441b4072038502a02814001a8031490302c00201c0c2c0440c0580c2055900b03001200e00801d240d00c0c40104450f0626556210800104080000300500d00719a00b42d441d585140070b18945040410780802401075500000c0341c0b030081580403095809803004000c440d626280f860401c1c40c09040c143d480690803058004040a41a00140e4024814880b58101080b500e540700383c002041d10a044c46c0c081080b451000000005407440300200c13408000c44126216283c002c3c00107800c8410310b03400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 88595459 1250 88594209 88594211
    0x1090603090c0e090a05100605010807080a1d07150302030f130804080601080a03091e0b0c032b0501050d03080f060a030803070908060105030d020714120f150f01150e03120c01 77
    0x9104200603007042030807d0703c040004244002441e10700080c04140c0060000010300644000040e800c800650001d0068038078410941c030b2010034030000ca0346601e40c1b1300603105400304c0f0a14803c5807a001e8021a805a00140c5024802e96a5912960540c0c801d6007001c60b21400c04100c00500448104001806088600050901d21165103400f0349580401c1e84525814407002c007992850001020709001298204200315035107031410025a81141700c0c90402d8420105645950815060f440034041512a1103c108008690301c4800700251008420402030000318030317900251008d49422038041e00444040e024008440c1c0340d996a10050300215070401c001b40c00c2400030414220704002160040c0301c00d401404080440c541d0003501c92800d401501403c1401c0420602c0a03113900c04400c1281d0751080990720440440c4101a840d000008054541130420601051441c200800c103181210390b002451000b40c07290b604141d50032200b208506a00d1300404c0c00740e0a80c030003844000d02e030684100c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 88596709 1250 88595459 88595473
    0x40302010614040608060415021e0918130813090501031401050a0c12021305060f0715020f04091e1802120105060f0d050f03130611010b01090603090c0e09 68
    0x10b00316820300d10214061065041c031908101380580464555002a00f106807690008140c2c1c0d50240a44201c0041100c005001e4058100341c105020140100240c101c644091b0801108808006014140d8070200e00034500582600010034090040808500107031080160700e80c1d0b0360500044440c264015148002c000c0c9503c0c801d0b002c2885900e82c000e08020b0100b1484840030001008405813003030310380489500181517000c1101c04030350000184001010349944106021505002e6041080b088404207201e030701080c040d00d014003e65203000c41d10704840741403500e0400c1d060050441c0791014940c001101117180c0c217180690003050140c1c0c5020361000409400c92042c00318240402c004400e413645048240180c65071040c040901403201195119402c20031030800500b0203035611615080d0f80301c002594603502c040c28101c4002c556880e01c1e40c0d481c1c8160030368400d00782d5110400e60790005d2503402c8188402da00a60010f0f510b28082c803003804209880390245182044281c80e0400c06a005a0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 88597959 1250 88596709 88596719
    0x70906020c0d0c050d06090602040303030c170105060901051c09030f020c041103060907050c0a030e040507051c020c0106050a090609050c0c060a110d021306020c0109031505040305040803030403020106 88
    0x28280007000300381d411048280498840c82542c0c4014000d0798440c0c804c06150f10144a06c0345c11075284150848401c6546965925029006188201407040428642143d8240d1003115881c030604030b034000303000300d0325092011004403804e5000007040020000500600e17410602d9910400c10010301c281c4a00d202602004400f81c41e0001e02e8005610a80c1090151404204c10308103490b08120113032090681034580c060155014000c40d010300e0341c54070840c803190302030540c4188640419201a1000c00c01921550001c0710f00b8403815091400d0b00141604081c0440e15503801498180340241c00054055110000141c02c4426030b400708540f1500d5610600110f0f5080c401d5a401c0011080c9051821b1600c0e6001921440020003600714141d0300c1d2240d640c0701464400b218900c0368991407c654980d40f24400400d40d890f140a0701c030040c801c22044101c9940290300903026240c120707081e5010300348492020405400018003ca08100c4140700014040d0310400c06540924840c1e00081202c80c144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 88599209 1250 88597959 88597963
    0x9051b1302090105040909030c02060d021201050a05030a020904030306080f06090709050402100804060b09040609150c2007030c03150b010c020f0108060411030a0c200d08040311010507090602 84
    0x2040040410510411042e80a6030700b000444045480544002c40c4407802ca040594607446001406504030a000401d4144035085070b00070701d0941c46207050310a89980f10f105120083d9054014140c165100c005030304050b18100c1c0700d1581c400d204c0d24010a415840754030341420515013582c03440311030340040c00780507005a05114400c00381c00341c1d04007003101c0c1c9040c4d0002141100c400a404061042c1c2e040801d09000032500315280146010b403c41d082c0e400c0c2031070a440144400c0d5000d6541c00f560a076408006003840c02a40740c3c3d408140c4d101c6043c2246d4205400651844400d65011032154103400000102d80e0140d080080d0301460902d0510980c01c200d400a5401c40c154240c100f041901c683c0c00140d80d40d90741002038000a10300f01d41e45541e0100030400400c00c07503d0181c0000e030080100030034008581c11402000142c0c1c2d4030401005010f01c0c90070807400b4100c2c03005d6880d41140103c0003e0341d11400354598003d000c0d140041c2d01141c0b0b150b0703150031144140d50100015a2031202404600d0301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 88600459 1250 88599209 88599229
    0xa08032a010504020105030f0703110310080d080606040504020a230a09080c01050315030c03010e0c13090b0c03130b04030e0a050108040309180e0303090c040e0f0a03080a09051b 78
    0xa80003440702c1d140940c0002d05c1c61200a10846085c400b21005c51240da00c240d1000782041c0c004c0078030680d28203200d00c90300c540c581c4510510416105182146101d14402c2c3c095500500018040a040600303202c02c00000e50481848601040340b110004840141941d2030b00700c0e01892510b45640d141c080c0d220050900c425a08480102d078403041c1c12904c1c2c0d0340e000e0101d030391001022502d80d041000002c000380c100021240d2072a407560031f2000d0011049030201d008803501ea01283c003618031603042101c1000b529a545005800c02d8115030004a485980400440d4001036813000716007070142e2643c4e01c1c0558103003030b42d0641c0005c211003800722039414402901809030400f420b150015181c65a4028844e411340d0241c0c03010b001c1c04580114442c00703683c112401808649099a44a01d001c2039842e41d2407009a601a1013542445140d00704048003080e8441d492404d4406403000c04650344040e2400d5a02500300311016560350003050204030b0900450741c00c0181c501d030b0101c0c3c44da4404108411100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 88601709 1250 88600459 88600537
    0xf1c050a0e06150613080a030201062301020703080a03020f130303020601091a0f010203040503030a0201020d110a02120a050d050a050a0b09062110020f22030206030103110a0803 78
    0x1000302c00380701d000b406040000c611a14201c40480c1d4481c078214042c0c2012409030300024140c0302d090002c10801d50190012000e55030b40e09050780c40d01107800780561400710b101c83c3c400e0168004a40600c0402c060703400900540c1401e0a02610701000030000c51840d921082140c1e038000502c0300140f080550620070103005141043c4184000721300090280060507041049900c0382c20f8008410003035900070f0040da0001e0500905032600c07141c000d84042d021391312103891400c081c1c0c5818050241c0c00d0143e0151038220f940ea600401d4200c03c0800c001115a1011000009024041c000e403240d03041d0601035584602c0ca100d030080780500f4000400d206441d90104d503e4030031b041d030310308104040d01c0703262205c08000c4042c40071102c10820011124201614075503502c03600781c00010004840070061001301840402d6140004a05a089240d80041444c0303000096220794200010000b04a01a00910702440c008202c200c4050b99107444a14590080004002c0000000404504400302d40c1000540d19 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 88602959 1250 88601709 88601713
    0xc0b0712230d0902030a050102130e0609090307031202070c06030c030506040614220f0e0609060114040c020f070807051201020c0703031103070b093901050f1c050a0e 73
    0x19040200806a004800240b009150f0720860142590340401040c400b41c0e4010000b15a12104402e01110070b01743c0780155180c04c0103050100d501420400c1d061445291a0f41c0a1030800285940071144100003240d000380194090080750041480615041c00502c1c00752400108500d61f80805030641d03000600082c400d03440c14900300000521034403649802c1d0f03011944518844120704c45501e40c94000710318600c4d0140f810382400e0400d00580e11450342c1080d008121134855403224041c50391080c090156180b0b1810001040e05181025080324654010398019540c6e010071656409140007840d503c04101c55210940070031050a0420315801d110076004c000354a016100400282e40d03041e6807000600b040400c9502d24078052003441540c103510361001d041c00c01d0742480b024055030b521205030406a801100181c4040220100b00c464041503900002418010342560055541c0e4000e803450044440301000305010b000c02a80543c1080c0604009c0010941001c0126008540006c0600d070025 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 88604209 1250 88602959 88603007
    0x20070302070504020f040e040c030b090a031b08040302040c02010b040507050412020d0813060906170f130203070f06051801020a020108040f0f08030103060207060b1e0603040c0b0712 80
    0x42a40815180c050301c20035540542e072404404d5005c00d40c0d104c0c40c1e1001e07500100c1c41e0244004c2020f03040ca01d00c200d9004030240c0101c8e4403419040c1c0d03112440f040005000c01c3e1110302c128281d46d1148882c1a400c4d01569010341019901d070041825980a4082400180d54550840c14186024400c19810460394a045402c1a05080482e44450a000c0010f48036152a608820800c2000000c96510544000da0204207a9890001604035652030140c000400d41103000e01c010301d42c030801080e1142100031031411994684040e8900f042200c0e4a0aa03050301502c0c0c4003244021468240400070402640c3c0c0c41c5e5120107120385145411880321001c1d0442d04031a4038500980e0780a44000d030803503000b5140940740c004614140340005501d11340101000da020000105106499018040140c001e040901260450000704400c800141c21508500e80307600f01c0b1009141071080c040c41d8810b2250b40403850b610345071040a199504043c40899540f8016070080528541c4289a2440781026050320703225 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 88605459 1250 88604209 88604213
    0x703020607050c101806030f060f0e0702060705030c0f0d11181c050d120e01060303030504110411040605090109080a0807140102030906010b0f090a060305090c0d0203280b0a2007 78
    0x840c140c9441b4a808040c1c0302d0b480fa00c05098503a100c0c00040480380e4082e0b291658401039120742032411540782001d03028101c0007d0500d8020030440b442098588002c502c2d000c14030b085401d4a801c1565040703000c81c0d84003c5ca51403002800300410544041c8102210b800041c9002c00241d1902884011660001441604001400026039401407483e904144100410012440d401800e0042000c0c0c0301d50f081c4030000003415003590100380102d0054031400f911621000c140421b60b84c1700c518803e10700c9010442080214403520140080c000c0514100240c2c7d03584002551034410000410f130389501c40042c1840400100090000580030010003d505520704003070000d4a809051045c12811040060400140c80d8501d04403451610000c066104440d1682001001003900b240d040c00c4c6485884164100c900d080000c0d0102d042d0300600800d0510f807819840703107184c2030801400075400c0ca4401c41d400001c4140d01c0031403244003040000540c03031b17885000c005003504608488008903d410015480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 88606709 1250 88605459 88605497
    0x5040b0315040f06021201050f03030a1d0a030206030103050c10020714062a0105150102010216060b0604171b180f0403110106181109010503040f050703020607050c10 73
    0xd5040004078510003a41e0725030402105001c403d03c00203014070300c0041c64100c048144505c050690f002540c020200f480040281903a0344961400407011940b042140003010b001110b08481196025105100c1241c0da507001c0f6100750021f8104407802d400500b4680c2c00c5003007402c0340800c002420b10003400c0c407524000d4030251038032503c0400c80c06a08009580309441c4034040c143c1035103299030031407441e08101f504446402400151610141481000c0c103882543d8414000d0b541c003540460402e80080c15141d45140c01400d40b48405600000141320004503043e0b111821118110088046c00064082e00d09512152000188103031041c0400c0d41100c503051003803c207080d80a40102280c034581d80b12410165028521032a08401c1982800382c00300d103101e806111401800203980083c130920b000401603010900601d200340e400590140000b074040380d20a00301c0b0f00c819005d84161910b454603600403500c40d81c00484150784035444844011030a0a103c690394050804900e400c5400c10010132103d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 88607959 1250 88606709 88606723
    0x6080a12090509071101090209010303020d0207052d0307030602040803120f16050304020f0a080a0203011103010b1c0e0304062d020303070f090503060103050f06010f080c040c050d0608011505040b03 87
    0x2c010010b40811710108003500358442c0d2020303600200300508940c0d603440d00a68410081c80054014042c243c00014135092418030001c6014512040d185c808241c2283c010b06402c500400a915104180000001c11000c3c030003003000e01440d2000d10b03503030b0a50003100d4072a440c0107015092480f00e26010045060304000480704040710515003075039a03480d40d000090042c55001e000603480510340c1e2000400c2c400014100136414401d8000340100d1409900c075002601003486a000c085404000340c40d2200880008503114001c480780004d200d0083c2d00714140f85800a4100e20080b408224403032080c0c01881c2c03c3d02004852a0200c2e203071404c4011002503c17400080c005900b80140025891200c82c0500354000180002800301d500540c0d60b8203025680e1900c0b611101014020348001007441501c800346032007500d03d543e00409a1100740d20030f210091031401150710800c2000e100314440000e0718001c0c2c00c000d000309000031076031101208400500021560225109900d440081c6e12141c5002c680d42c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 88609209 1250 88607959 88607971
    0xc0304090b060c070f0501170f0105090705070b07090302130b1023070609020f030601060e01050706020d050907031104090308060607030905030d05070b161d060d06080a12090509 78
    0x10803521412070100d440c90003505018502d90041c4500802c081441001700c03412140241c0c0c0f00310001c90309a910070300d50b040a07103000c50602144001031085040c100e554035001005464282c4c40d1103141e0711094100b50040e15042e0000e0015078040041d4070b0700b50b200b841412400030007000036030011000165024010400c1005021030800d084403040d40000180c0b603804001c07903901b60b80c0c1400d454248000c18018a00301c2c85060003424072851420000749441c10795015890381e0080001d10001568a5000840200d4440e9003c0200038100310980c001d660042000b600245550360541c40c03c0d0740315a200800030b40c012407030110700c00e0205e5800840d5541200c41611582d40e0b030389140c2821910b559254002e20b0f05803040d4250291030503408030007000b240340103554152007a12400c84070000400c07440300450000302205c4102c40c020b01000600200e81400030300380792900c100395424000b0b484141d07121592582080b4010000c1c0207440302c101c00c001205290540081d8200800070b0602c4202602c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 88610459 1250 88609209 88609211
    0x180806090d030608150a0f020c0307020a080303010303050d0e1c081b09060f090f150301030c0501080103230a02090c0c101104030b04030201091a06041802030d0e010c0b04051507050c030409 83
    0x1150005010b6440400000d1f200c010643d039039030020101f5680c0e40d003c803008a00403500c43c00001540900801070360705999140d41c929250086500d0098090000a9074002d054000c00c4a0000c400e0311111425a900042c0c0d2140c01541c0340040ca00d0302130a000c645000440c55003040043caa0369036400c100c030380c50b00d1810f0304181c4a00c00070010800c800f10103820190800001d0f000e04040c0c0040401460480c0e01c1180e00b100c1140e182c5004407030300380c000e100060031a42420105807203007001b009503100c0d540300a002c4803440029500001d410801c00d80351011032000004d6280040902840029042c44081000b4414100c40003141ca51a00c03481c800a4142d416440201d000c1500c02c0d0040b200306a00541203485216403062041034129060b030780180301b80d181c241e039001c113900030511217064986c0003005032010070f0003180300341d84000030307445200d0412010880320b00000d01038040250245e40203034020f0081440c20100d40071000e001030036660030311005016640c09144000119025105e0000f8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 88611709 1250 88610459 88610461
    0x60f010215010b160b0f0108100207050709020904020d0c030209010e04090b0a110c01020708120702010c170c040e0901020705120310061803080d05060a0f0305030f0703180806090d03060815 83
    0x14207000c1c03001400240007807007039014052003022101b203450594a41e01c09590070b4203103c4c05002c3c101c0c890540024000d8020f0681001801501d602900c0b0225001c1c0016140c180d569800604440348200340c4800701c0e9001c100c140b003550713019a11000da1101550304000c000300c19182e50307082c41002003001d0f42054540d111403080140120989000c84507500003952501040d10b41442950464001c4006803d420000900c0c2203105001d0310790288010307183d5402c600c15074003540b01140c400402501980d641000001a0365002261203071140c4403944c001610f54095160260400d5200c41542044c441c06105101418170009200303005c640040c20841c401407400c100c0144481582d40c0040c011690200d0100c9400d00350b504840d10032a421115402880c0d01c070400541e040c030340ca02029103c2c4e40180b0240ca07540021800500c0b076035002c0d00308541d4000c0c41c09001040f08069400076203464202c202486510a0100042c60082045040c24080581009482550741450300405804911040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 88612959 1250 88611709 88611727
    0x1180e12091c08090103110906030a0902060f070605100e060105030a0b0103060f0e0f0903191d040e03070623040b04110303040815011e15030b0301060e060f010215010b 74
    0x1030b000d600d1081c100d240c0803100e20790605200d01030742c000300c01c0301d0301007810140c101c0c4d50480c0100c111030f1030b008014100303400c45e01c40b00c070440000c003c410780403600410b08111584252000c10090501107200365030115040c82e000f5403206a210040e800114102038180c10300c8540c0c2e80160a40c1c0e40110b0300000000c545241a0049005c1c0c80942e22281c1a00780c0701001051802d04600c04a2040c01070005484450719001070256803071007020040b070003c4070000c0219241c41d120f00380b2850800341401c40c0640031590440083c0417280d0800b8480000d43c40004c0c0181042518011803600070340080324134140031400603641c01c60441c0108010104c0d580718000804006840385c0884450390301070120798555440701d80d5207649002455040c040031301e1200c000203108140c0501108001d001c40710221403245000500989412a038010341c003415207403640854562001d00c00d00c40200002400004c1034107004081c8008210340c8611030b4115042250300400c1c0030008105d890456203035501003540c0c0c005903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 88614209 1250 88612959 88612969
    0x130e0601050a05130b0304110103050f090c0d03030b06040602010204081c080a0e01020c0610080c120a0305090a031403030708060f031c0c0501020c06100602070f05130f1401180e1209 80
    0x4e600401200a008018007062069025103084003520a07201004981c03112030710b01d0b90040c030407110005182c2c84071140784482e0902c0307000541603911905000c07c20302c40150000b102078000e5001b07003005030b60200b03040169400802c840310002c840042c004170359024900f1300406040b00100020700498884117103e036030040941c100c5041c04031050944100b8100141c40302020015442400d030030784100b0007108802d10301001c1c10b00c64465102c00400825004c0c0d070703042c0c0d00c40c0c20a0081a90140d59110f00101003140c0040040e149039000028541d40d192a0f0700c060000b03240500098002e6007400b00c2d1501c151400a0084451030044000c00352260200c84115584a0250001855540085000e4002d040000b50180c01668182240a1180e407110b01c220780e1382e00b491044404611704034104000e42c0c2405030b2840b0301c02c28151404120411a8149034058034280340e00f2580594034000100b01070300c80c002c003009617031401e070b101881001c02c03400400360307688a0060f4240700751708001900c180139510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 88615459 1250 88614209 88614247
    0xc06100609090b130213030c080706080f1f1818021c080417030d0b010224060a0905240301110702011b06051915030f030807020a05030c03130e0601050a05 68
    0x16100c802c1d903907140b0424106c50640c1d083d200881d0701e4110320340046110400410314409a84550b61030b03d200e0341d901d80d0700501c0d9840140c48010040c400c0f000040800c1c1c960150040a00441d9901402585960340100110b900540000711009607000015005039208048201c0c44c06038205000003400700b5042140d19807080d5400400c0c0d02d8100409000c0358100400a490500e0543c40c0400481803802c005a880c0c03034003401444e01c0f08520000fa407645c64a0b25005075040782010707156002c65519840c0c0720084a4042c2c0d041505d003034401e52403074100c04051300080c040c41401d0780244940e840251451030340e4000d1640080c180002d2a804580207224030400f120701e49e410503802c1c001c5082c07081440f0070544003c040b201d002401e200300001000c03070305074601084030b9020100407075040881d2030444114a01400c00802c602580308a2000700e41d0800c060320352810036601441d911440d8142a8101d1806548400e10001c40b00c020409243e8110702500c583d02c0c45414100d07544d240c0341e0000054040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 88616709 1250 88615459 88615489
    0x81806010b03010329070201270206040b07140102130311150a0e0f06040e06100309020906060306030c04090b07110a08090103020f040801050408071109151201090501110c06100609090b 81
    0x16245c801c008000c0c2c2e05402c49420070f14561100b81410030140d2042c6400c801c0107501941009040004010f080300308001084914017622248401c1c0d101d41107110f003a41d03c00c0150034000f4160900500601940240d0050402c200720742504a40310b6a00500d103990280c200074200f070005a0062040649407001460703040780006020382e654548403966000001c10603a0014010005580744608444c001d00c20a0356103600209030f4202c6a03502e80422540754802001c0d00c1e0940620848103c1c961581e02840b001c0e20711815107070205243c4200000c01811840d40850000d901400e03998022800381d8040ba00124001c2c40c0140c0d0300c9201c50603a501901c1640d2010070a50710f40002c1006011101014090b03443c403c240824054020a040100c000400d0380c50000e48103a100c3e03900100d1030101109680204400000f0610340820f4490908468a0910f44550341c240040c03079544401040c0031083c0d000114450210b17a1a0a041008040032024080c2e503414a035982d40083e156a0307200080c0b01800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 88617959 1250 88616709 88616783
    0x6050303070b070f0c0807080706060306020721020d0806040911090705031f080303070c03030e010614030c060301060c0807020607060e0d0306050618040b0f0a06081806010b030103 79
    0x1440500d0402c4407000200e42c07150000340c2c00c14407080f07154407801c803000740a03030003c6810f4141412611003a50590001c4400c58149a54807030000018010b8009018194052080c4400032502031340d030b643c000306220503c0c00454120f03148405826401040c0b19800503c01e0314000b40d030059502d0103c50702c103641c07641c417603004590000308815994840008c520a406540b0291500000d120103d20403c80a000701803040e0418000166040c0c414500c542d0000e0103407070085203006002000c1400c4a20680000044030341d1103003c0f1035581001c000586803950b041e54818038542c07414000030121200c1203402408403900158030030a41d900e98080d030b0750a5802101c2003040c0341480005d02d544a118001c02e50100c1d003060310008040c6000c074169120f42c0c0701000b04400081606c0100001006440070259020301003c01c00a42c940310808490040c204503100c0700d80c2030401060000401c031042e108504075074020001488a40c00140c00c2c0d81c1180e50103402ca00f03a4100f0b80c4081e058032504005002009 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 88619209 1250 88617959 88617967
    0x114040803070905030724020c120a020f1903030f05130e01050907020616030e0307060510050a1e03081b060c130608090304050127090b040506040209030a060209030106050303 77
    0xc440500300442c0a51126114414480c0c1d84100b40b5403034540e64881c0b42180c0c000440165803071a41c03400c100201c05481e1040e41c80e140b40c40000075908281ca80b500507034562141440c9030840c10300503001002c0441c00c484000c5140784054001500d140f03d0f0000404114100070240c00403030040c03081e500e140010310411890705440d0700007403800f00c4003441350500c40e00b0a900803c04450021038203902030460031443d00815000310b00c041d0040e107404107802032644401c0200d800462020b01c40c40c1c1c022881c941c1c00c0d42e601403500041181440301c5402000c800d400da40e14030020000c0b00c1c0030710411641c0c0a1087e5880d0b45414891001414810780c961515002d60002c0241c00340e40c0200400070255400210040e50b44c03503000c1212103400031184155694800c0100744403e6000c3c0c400c2c0c0101703030ba4501c40e80b00d45081016080e254882c00d641701d18040da86902174001c2a203054058140d000300700b51011410b0482820003e59141c1084c20040c24140d030014100031940c500b900280054280a401c49543d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 88620459 1250 88619209 88619213
    0x402070305041a03070e010302030f010504050c0f0708030901061a04050409030309060515041a090114030319030506010f050a0f08041104060e0610090501120e030d0c030212091603060509011404 85
    0x501d6004a4200001a46d02a80c001c07480d800b92080d24080d002e5410000e909a00704414440104030182c8045110001442098103121511303008201d0544030f00340c00c540302d003010784407a401d4aa00741c10440e40b1118440300b81d100664013600b91411282d045802150048040c00d050b4002c012810000c1e100500740002c1008145801c0c01c41090040250307070401c43e82900c2011845115840c0b00c0359580990804010404850600140c24a240008040da854409811450400b000702101c1081c0800d454104120080d85c1105182015494600704946091142c94006181603d060716240034001e400012a0602c9050030701200d5601e80035004010943d202c1000108220040b030f5042d11030f440008985030401d20880980d02240d0041c2c46642d440300240c1c00d10005010040c0503c038561005200c046a091918000d1450f800303400c0d28016550121b40915043c2c4030707c0201011402d81c4503402000e0300c00b0401344400c00301c030b8000c0c0000039030b9143c0b61002c601501103c1c00c0d40001c11590014001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 88621709 1250 88620459 88620509
    0xf15060d0b0a050f0d0807060e0a0b070f0f0509091e0c090a050d0308010e040807050a0c0501031410060c050a020405010b03060915031518070305030d200702040207030504 75
    0x30900040742d40c001c107180d0399820403000780b149441e1a40c04c0801c060540000940080251080711300c00c8030081151881070700014601007192005481c80103e96042c8940c054000609480e225954944071142d442004c10251a038840c081116001d0001c3e40d0010b110200d5095807000c2130b040e05000c0b01c0e03913401d1a1007540e289810980119125070b03010080001e1a20f801001207509070360580b0b84030300c44d070300e042e2040084850003001030318000c40c2040b90030300150741072040807905031244060455a41c100300006044554018803119105500002d10000f82d21454a000c2220308030700c1d160b4012000362a00c80d04051903101d000f03400c02d04050010485040150241d0b2080d40b040d114680c1c03941d82e86503409039081d603900400e40c0507000300e0401c1d040520301c0d40b00c2650115070543d2243d204004503007540e14140c03c80d401540c9641010544000c24010340c040c030b08503500d80f4001e9941e040740c080b8448900d4801d0200003403066074001000303c10507000d20290b41c01000b00000500e03106a464500c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 88622959 1250 88621709 88621721
    0xe0408091e0a08030418050c0d020309032107080f060a03060e030c0c060301060e0f0604080d031b11030f031b0403050d020606060f0904150b0703180e0402090f15060d 73
    0x10784100b40700d22003c15220000000c1c0c50445001a07540c00e551010100c1000040602915071800120100b00031b41c7e48001500085004444940041d86d46040a4072413001c01c50342c41d42d603141072201d110300740202c46030b00c08201134001030b90f22004013468840000041c0058200d034802001c4500b4030700588070498001c4041e0407c800c40c0c8094a1525440d00e0401c115444240181000b20714085590711b5039050103482044c0c2d080015050741d280c1901d50080320726000c1c80007100c000103510f41480b07103142031031000f02c00743c84042d50404510303070503400c0d00c1c160303d034007581244012080c00840016011b001c40030329107a200c00200d10303840d80d8945a042098662604145030000f52141c00041101350030810300702c07907080c4a00c040050405100d4410040500340c00002040c1050b003c00f000304610341d0782c800400b03501e4460707207403405040d02080d614515280c0581c05085090310010400c00540c03144041c0640c0106a407010000e06d90303551850030000c500650041d600704102084010014606501003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 88624209 1250 88622959 88623019
    0x30a0b010e010e2404060b030f18030903070e040606210c060518010c1505070306030b100e04140109050703120806030a03020d111f14010902130e040809 67
    0x1d8036507070302c800c4010040001541c1c1d8220035050341444100000e03880014050703480c00244081980c80e83d4034000d10454005444042880e0002000e1000031001c1286103000441c007600030754149070b0850006520703030b081485100490314820000404016595018402a1001d1903c5140f01a840040a2000c0f0750380340044650040760b0202081c1075000c2c0055450007807025851030541d0180000464942c031402104441034024040564441c1400340580d0740301c2c060303d550000b2282d24500300341c401640090070014070544000307400d101d41c000c1c03071114603070141e00070303148200307015406c07080c2c60040c02182805070803405040700110400407030005145910780d1517030304da45581e141c0c5010907496082254000300035038401c19001d5074141c01400300e0000000408151443c0d400086000c6000d41603c3c62441c9120303650300003464180c0c17a40000c480c0074000c2e034071086007030411407401c1f0f40344487d0078013903e544000308000007010403500c0300480324203070390240a40354032014005000c030b148078442030740d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 88625459 1250 88624209 88624229
    0x3030603050607032a020319050d1a090402060309031605010c0801081603150b090c0c0d090b1e0405030f0d09150801090c090503030703050405030d050705030307120b030a0b01 77
    0x483c55040c802c1c00748221401400341d52890380c0200719280045041082100c10640c003060201d1007002544000c11039582043c0c1e2503c42e901d940313810300300044030071070042046400b1000742e0a039243d84440380c505601c20341c10780b400d0343d803611005449031a40c0510800d20a00e64600c0f41913400f0000190070034034045c04544c5800c1140e13601d54103131545407004010425810103400304200040740c02c2d4520408080061200042c1c3e217810240071031460070040f101c82d00c6040300080d40300d078190410003145c04030f070b4040c0c507100102608000900c03010b0720030740c000502e10a1681e2007071a03148bc00d4900312001400010105d032025640502039031703240c599880f40d441c00b040e142800080c840400800095421005d40d440103003603030030310b05094010580301e841002004480400443da0752070410041c0b00e404d0080d21915161441c100400d0314011802c0d100c141000b001b40f0100780014000000c3d66000179140c10038041400310103503810300500c0403010b81038ac14824000d5500034030262800d01030607526009a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 88626709 1250 88625459 88625461
    0xb0409060e0112020f01030c05091215010816120215070605040507080303011a0d090804031406091902101809020a0311030601020705120a021005091f05220b0304030306030506 77
    0x2c3d080845554614040e42110400c4020311391984243e0008180c140c1e00d08049081210003004100080b254082555203a80301a45102c0048003e2200c81c2c01429564014608102d891218441840e498410703261030107a8200d1280865559002d00740785004082c0200340c5a0501e41010741c043d0000381c070b0a503583d00440001140e106400300c2100d058400540c15001d050703071505590b00ca25802031032150000380c1d030f41c8000780002d110b0764002c100550094078046401c450220361035003416805406640070f40c2c410307030318841c000b10310000b403c0c08190103d469001d0350f00c02c200103982c03444103075031101d031403082e001d0b404202c0d44003550107841c4000041d503007081800d03990b40303003114680f10540347c0901690008a04011602c0c0000a03010003800c2002541d46030996540030808100e102903042c0081100400d203081e450a10b0414000c1c050f400c03030510061400305050140c4a4441c040038861001a40300d5044d40c40381c2103203402c0d0004c00111a01640c1e901d000d04008008054a000c21502405580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 88627959 1250 88626709 88626719
    0x10e040603080a0509030102131212020127140f0d0e0114180303070807030302040918021806030a051006030201090e0903040905040f02030604030e0102060c130504020304020a0b0409060e01 83
    0x803044000352540035540c64903001c3d4024041d611a000303030a105d60303d99020840343e00c40e0401002004000d002c000c00488601400c0e2500310031103000301a07840304581c901002201034080f03421000e00c0c20444907000c22240300c0241481c1c941002c03a580460502d10070342d800c170a140d51000070212281c000a9444000c00302c080001103800d00c000e140c1503842841c090001907a40c0c0852040c3c0d200c0e0f03520007001c885c0380c07404907526000c070340d00b1404055002c25400f0408201032031a5004071000140d62070301e5003c0d04510713903000681d4101041c000c3c004408100c000100d00c1e0b181007040c07d02c0b1540100803103d0f11559040c0034401340206000803400074041c0d910008070344005200300f40c010340d4664040c40c106800c0841d0b00c0000e1900a00540c0c20301c40701c5c1d08110140e1000d200090045010381d9640c40e6003000c00f400640f030604003a0000300000c0c010400c0c28201128440700300d05841c01250701513079907142c40c0000b8035414819004001c05002c0000e0002e0244c240382e101300c2c115950300e403582815aa841d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 88629209 1250 88627959 88627961
    0xe04030f0305180601140a030c0303050315090402010206070804020109180510140109030308040302030706050c1e0307020318150a110601060c0209010308090112020c01091a091c02010e120702010e04 87
    0x1c200380f158031030030040c0000c04040d82c04441405014000d80c219559039200c10307082c108550310503000708200005010f038000c6080a11208500d040d6420602810705e640005c0d40e50b00014242d408101004010504682c890807403c0003c1241e110f002032030044007116403004120540da404c54000341345a00045070880c40d4120417911005864040c081446c7d40c03000c1c0c40e48200140100c0440c0402c120190007d80d182c4902c90103041c4c2d00240a0300c403504040300704510001030058045480040c41000180350b4000b08a0340700c0c4e00d0b89112525040481e9000c1880e0b044090f01d2000d401c400801c2c00c6103a1a401180100c03011074007030454080b0307680c5900645500c0460702011350000032107001807000c41c41e070100801006206151089405040011400884e000b0051064559440325940000e000107010f184600c44041d1454003050308009131346a50b190528100103410414108400d813041d4000e40c0300121004030041030310b2100c030324a1110040c0d58042c0c0c074128040380d0042e007011298103003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 88630459 1250 88629209 88629241
    0xf092e02010506030a080304030c080d02070c03060509060103080910090510030c020d050a020a0303021b0f030309070e1005090c070c06020105040212030309070905061c08040302040b061204030804020a0e04030f0305 94
    0x81650b247c5907071604d803400c03035424403d40010b48040c0e40c00c0041c00c82e41b500358802840303140d001d40100d0000c50700b18586070b0182d0300d001d484a0803e600032001400803d07800d100f21b48008808643d02c00b5560f11404041d280820180c3c0413641c4490034070b00c00c80341c0c1a00343e0082410b803e9194207480c0301d82c641f14025a0300740926081840180d108140c05000240680c1c02040d159903019800111000800449850425400c601c001603820200501c4400c21041040303001510b410350121000c1c2c9485108003850045912646200f1000d4601041d0401c20b104100c40c5102e4001050614036a21890003038041e04007668101d014040304110201d10340030100989020325204400303041050b03c2d020030a03018240140c05c25030300142e40324280304001e0f4a0b0302d032400001d100350b8100340c0f40c620b103004100458088000c0c4030f0146c0310070448135003545281c0d0061035000780d05040c0014140c8980c00070920315139042d0010000c1192203824041030640040800d40806010b941c248200c0d92002c00d0f860400c40d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 88631709 1250 88630459 88630463
    0x111030411060d0e03033102030a0209270304060807080403020303071103090a060305010f050307030506010915030f03030504020f0303160b1306021c0e01060501050f092e02010506030a 81
    0x800c441c1160040c5000001059106107040300400d00ca8012038640303003158402c0e20b03801c4601c2d1580c101d030b0000401c0030406a8105c0030410a0f2540305840c0c0e00481c0d1a014030841c0244a42510720000d00740d00c5500e91010304040f1590000c000c8880d02c03111441ea031341e10038000c1b00003041609001036175407842103020310710459040d8081c41c110b4981c60700540c0d0413514268008100d00050056040315218440c0507070003812980d0740440c140d40341601140100e0a9500028020740000d032040c40403403c0056200e044802442000594490f0110750340000182500002d01120000c58001e00741541600003a000341c3c022900e000701071502c40c0403d99240f0034040320845500d10a9103040100d200032400c0c0b9800030182025444c0c945441c1d85040c100c4c5d00a00c0002c00d603c0344542804101c04140c407607071440401900080188c5401d120010703011307000d46030754284004800605c104c80d80e100e101003489002c0e202007001c05010304562200d0202200c84514400640c0703000006032251a001800c510103603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 88632959 1250 88631709 88631723
    0x20304020f040e0c041b1b030c0b090f0a0605071209021e0f0607060501032114030604020903070b04050418020607030e18040f06050c09090a0b0f030a0f020301110304 73
    0x141e90014000035221020500740c01d0701441203404070589841c0114120b0507504140e1281c603440341640a410701310755140c12222030305079030440300029400a04450003141c204e003d8003840c0d5100046d4500d4103154482901c140e00541000070104002c0390006401900e05840303801d445400b03682c0c244200d911001000e50320000f51070002d07a8107142100941d130710100c050811004910100045000c962000d00222030140c1e5030001041032020140c80103a0945006c4624810008042401402d994802c01c0c0c10140490000200c1c002d0703a12035048810071000981a035480c40e645142c513190542203403141900944c103001c004410002c2c041d1455030101e41c01000c050401050b520308440c400c001c650700d03d8214880440008480c2d01c0c1558940c8103500c0b0301c44c0214000d99614042040d1000602441e901500920a4080e190f83d442c91160b40045142e200003004091103001508000428000b035401d409250029810b03c0150300040140d140240d0092051341805015404144400c65018101ba = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 88634209 1250 88632959 88632979
    0xc080118060e0321060f060a0504051905091f0b1309020a030b03030d02040302010f110a02010804170a03060801060b07030804061107080412020f0901061403041e030f021002030402 79
    0x16910364842040e0014040440341044c0c41e1100c10801c40046200ca22481980c62007001000c0c0390005000b22001d906607417050411011b07610280c003502460240d03500ca40d80652600b500c8000c0001194000c0c440100700702d40e5810304d0030407505090a0341c1c5a8002507800d1081c04545500140308644000000d031009000980c070b001603c80007500040800e004250300c42004601958080025040c2001030f00801a0755514500c00900300f001d1040303c11042c060110f41d009600c000101b13102c600c03183c081c2005e4800340c0d0f0341d150000e070000f08035045c0c3c04841d60209043d802c0d41d51550194080d030300050000c210040d1501d03192085401000e40050001d07070107134001400500d90f504081caa0410003039890f1b06001a84e03461200c1d0340c0203074204801c100000411301e01545465400e042a00c042901c0080707040d41015402042e201040801c0a54039500002107410002c60301094641900103500c07120804074585402440104001d0b00c0303400603c160041200f107d521403003141d0149500820444c0c203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 88635459 1250 88634209 88634213
    0x10e0102120d090c06110c0f1804031404080a0b060a080607230301030809180f13050a1b03030f090e041103010f090605010503070b0412080903280c080118 68
    0x40e41c0502c0a2801040d280d400d8607001070418107825029006948642c00c5d1013400640141c03901b01c0c1108070038403074081c2048070b40c2984c13210200c01c40c1082c4500c200c42d4255449040c20b4a000c1c15048101d03080d202c0c00180003d03010004240317084403a21800051006484400800c02e0300889805029210340011011070000741c02a0251011012062812542a02407410020741c80c1c000360300c29200707140300203600b04451400b0b00b03012040541c001c09107030707203410300b0080c0d01d800000080001d80c042c20f52403201802d00c5002c21414034202d03881900c444140c0980c000c0d04000c0c101c01c0c4402c4000c6001446a50040b40c081c8000c2d000307884030751107080219038443e211f03255030504c4072090742e07055543c60094a2043d05c10340641c250243c0101404151135240c44203040c40c0003291782c080d80c0594400e2200b40001e54012381c0380d0700300c5500003446507280c1c020000000d040c011101c3e5500c4113424040e4644000a03404d829803a540e50040c02c2110325160f0f2810341e03e00780c5500c42d41004180b004a100040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 88636709 1250 88635459 88635493
    0xd0507120e0102070f06020c01080603210d060f03060905120705120d0603120207050a060912060f0605090108010f0c03090809010c080d420b030603150c09030705010e0102 75
    0x20071030005204035100141c0d0b5120031264000325412810043c1c11480b400315407541c110520ba0f80000d425002881036810040c60300c64004010504c034400c9a0340019424421183e07900824007400702003010001842e03a03490014001c01a4203803c90b440e0280048040e82c030030b601c038280d445c031b2508400541860030551420081035403000200c0034440e681c030040800800e09885031034407881e0f0642c00425800d03081200f003041c003200170b0748440100f102000c01440900300c50109405a036038000004940f00002c1605140a4a1150801504051103000001d04000c05400994840900040c00c216448110303104030180c445900b0050903038101004142102c1d446181a459280d0082c407a8034240092031000002b40d4006078003514134100760035103401c10791840340240c14040340300c0804031255060144080e40d10141070300c500b10301e80601000180b120388050207141da5003454030080c09020b2412303002c441102c0d007050310514040e00c81c104001ca004d5016861418800e40c3c140c000301881441e40e24801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 88637959 1250 88636709 88636727
    0xd0b040302011512050705060309100e010b0303190909050601140307091a1321031404090204030b010e070801180b010c050a060c080901180305030603160306020307020d050712 77
    0x24110341d03031103210840f042402039888010709100b011162803d00c45085c0240740031000d8200c280b145004205004072500c2c00165611100008a004074802803420070860041c00700b02e588903014000018214810740700600c00e034070150a1a216203509940395540c0744125201100c07400c0c08036154015003603005520402071603120b04540f07460824a07480b82c004444800c40c0315540216100089008183c26600c1004c500c040c0c16006810070764017000f8900c08144440140016081c860003d01e403002a00c20354080b18054600c00030190b55031a0b0324501001c500c48240714514000c0c10210200c0e40045c0318509482c101c49002401b800307084102d040c048002c1c010b410056041c4007a1002110000b142400303c61411400341d0800280558420720240c210b00303006080d40d003a43d143c40d091035807803149000d5034411a509890b140c0c0d141ea5980000c6403520710301807c1c059550001080000800c6048e0300190300c100c03195425100042d120440542d8140078205d80246204000d41d01c02d241c01e48180e00c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 88639209 1250 88637959 88637963
    0x20c0108060d05100203060f01020a02280305060106081006030506030606060c0a051f060f0b07060f020f07120311041a0903031c05010305010c050304030c03120605060c061509060d0b04 81
    0x2d03201c07a180980d42d2501d480c04240c002d0600c1500481000040d2610942002e9002c1080c00034041151050340095005505000340704001440341488003901060101448041c650182c01c0f18043c0d6150340b80a4030240003196044003004e501e03500850800c1c480e01440c0d01500001c1e00a10b65900e0b28405c001c0d490f04048a0034034140301b80361078000030400800c0120101d140d14405012607603c0703100c0f9902510480e800846d001540c0348000c000c40300429044902c40c2e40c00080c00602039008042580c040e106000381c0d20034200c000700d50344080c46900c0810281d00040d42d00c0070410100341201c1301c8964020352040000e4480741e07031480101c20210318020700c55800010141d82c0380003900c6583e0740c2040030310403039860700d0b540e90801841044402d1041400311840d50621505516081d07600410500400f040101006840b48064640c0707040e03500704e60040d000017400140c80d50705a40541d581c07404222039130b801d00c80030032084140034145590f1150161030003400060002c1082c1e2104a402d00c0c0140003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 88640459 1250 88639209 88639219
    0x120203071d2a041e05030a080304030c03050d0603230616120605060304080c0c010c12030b0406030b07390206030c120112050d0f051b0f03040801060609060906020c010806 75
    0xa4440c84800700010f02c05091020b2881c0e111540340b9541070300b48079039a002140650b200e0300180c408580f0940075030394415814030b0301000941491400f1140303030081a80308681c460400c0008000c00007810401000070360001d040030354980714540356554a80e010385550034150007000b1281d150902c1514400c44070b20302c0ca5408100c0583c0c850108480d81d00846003541c40c4000030a035503c0c6000240101614140c0910b4041014102521288807003005c1d10101000d141c1c3d03c2189018503140c40e0444801180c00c12050465450042c001618000d014000789806010511030386100c420412052050001c00c101d04144d00341b2543e0074071030603500180c04a10540c10900c000f80540701289949400f8180e2003103e144184140d10300a898894045001c3c400d04c03a00750b150b9420b055219040e660355028130307585154007288035441135051074100d10080744613000003d80880c00840540106e801c61381e050f500c8922403507440d80d08807805c000d94040e01006800003a008002580b1600803240c0044c40200303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 88641709 1250 88640459 88640521
    0x20c0108011a1e0703020709140105060c010b090a0c020c01030e0307030309031803050c0a090504170f0c0115170f0d05030712090308010302040b01110a06090813120203071d 76
    0x14210f0091164a00005a242800101c5108040c1e0511091000b8440e1844c1400800c0f41c21000c0c10843d0414040c03c3c2c0141c202203004c0c15844c00941211511400240c2419003d042201030394028007002e900310800b500c5118000d5a82d94441c0c0704035801c09034128003850030024035540c00c60241c04052026010000b04881c00000346c0381620b15103004510820041c560018181c05004444020354840c0004610b40410000420400d05007810082c000c100e84581e070791020906c0d020035000b400480c616661034480e1883c514a081d81a050584441040c41d2030b20001d50500d00d90303940111882140c09402c007205050445010703001540e008180c500f050180d40d5203500c00c15049404039001503000071f54002c010415400d103403207400340380b01c021310305184440c0c1e540310500d030b031004540c00007000e80e9920400142400002c1c025182812001041c000016907214800e030031052455406031710030300500c01d0010b5490748800c03907500040184400c007080c2d50f03240711015400c130010180e1541d402541c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 88642959 1250 88641709 88641727
    0x9060a050a15022e05071e1220070501060f03030507060b0a120b1602070609050d0c05060301030803010905090604020d120c1407170304080309100509060a0309060c020c0108011a 78
    0x604d541107a1021014011040c0305454000054a001400210a0100b011241080e0b170000d070041072800303646800c03e581054800300144c0700074020940780100c01840c082030340000c008480010072050f4001d00007482010744854554211f400680310041c0400c03010080000042c0b115082212400e9004104102140c2d07584600400f00042c10307400c4035001d6083d070030403041605401003d2083c8250788001d041050504034068454585030040e540b0a090165400082182c0408184003a00020745002e841e541e6078a40380301a90001c3c0950421303503082c440018804000010081d2140740c0061400170b000072962a1881c0e01e181854141c3d0400503164006c90200e0045150702411300d003420b0003413802c9071905c48541210550076000e941103400410080203011000001d035201d941040315103c152151142083c3c0d10351152081140d004000402d8902c100350b016803107015124010a0144070003440004120707142c05140c1d6403107021820000040c0032060a0800c5000081525203051b807504040f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 88644209 1250 88642959 88642993
    0x1509030616030e0c101809020403080a09120c050915030d110d050301030209070e060d09030c03200d03020c030c06151906020c010e0402070f03020601030209060a050a1502 75
    0x32a98040407032403144050540319814411400e003080d1100180a0904005001034849107240901008010303085160a01200001c0360760002440d6400c8219515a902e04e02070300107400921406000c20010000001c40d0050130740740300c2146600000c141c0c5110308240c00c01401201c046c207200c05561175494105400c2e20100702d5510308001540794000081c905a507906d250a00125101c0e08010b01440100700680390300302e5658104916041c140740c00200b90020034114080e81d03c00790704060a00700c106061542210200d090680241c1c1e51079900c0d1281000b84c43c2c3d11903901c025402990004c0c0e0694400f0b8400d601800f141c9031a40152468a040581100c0c0b5250b002d4680c241c02440488920748280341121065680315251002c4030f030b034a4949000a07403201402c504441c1441508400040345503102d50455501aa1060400e4402c0c84a070900954840090004030302840c2e80c80041603251500300740d914210343c0000d1040b4a0b050030402502a52401100204154890200080441020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 88645459 1250 88644209 88644211
    0x108120d0e031b010c03020405011209030c122105010302030c040f0b0402040f090606030c020a0b0402030307080d0506010809010b2b17121311060a09080102132409030215090306 78
    0x200c0303c06100e0506208031450841d10001c40c00c1c020b00d48104010022a43c10070310980c051381c0000b40008503a600e40c1010303201d15003880d500400b081d4003060107a1940340c0140281145a0b80c885522460710a96440344049440c203020280d4554010134802d019441d1540003248000081c00c0041180101c1c8404107050381c02ca50000c0720300711070118003449400b200e40f05e810020000c600e0203018100c141900a9211044041c003e00403601010008056441c10011a11000ea01c007468a0785d5600b0404001e000f4803054070a1800151800041000d081c81402000d910400c02071403a0f85e4074a689042c4551001c03840c0d14186c2800d8103c00c1d550106044808003480310341c0c90100d1959816000c40f9001030b0100013000c40c0004e4290500031004241c10038102000594192000c56660280c0041034421000310347c07102d0b80641c000102604002c400c1c1d90141d089921450071101c20206102c4150700c04021202c0b8040025456901000986425100c66840c03003040c42443e071601a54102003428020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 88646709 1250 88645459 88645477
    0xe0306090f06061e191d01050102010c090e010b16050a0305130e0103150203060111010504030f0e010306030b0a05180706080106080f04050c0405062b0201170108120d0e03 75
    0x21195001c1d04038042c801150b100700200e861000402c481c1d486000003c00e01018130380100914989811082c62040c0c100025008000042c002c002864882c1a260307a0240a498015403c1400d4101c200740107160a505644440c10703400c3d401c5e03082c80c500e00c05540050405195180c141380b103c0700402d10900503440c9a5000c0d540d811759820035145150f00302120b5034400c4560482290042000c562111440c80724144410001b6a40f5103403100106d030001c10b03600c44592154a0321050100f010741011000d00ca22000383c840900c4890101d0055080318031604c809003c00304018002107203c0032562255a00640c131850700b440c03064007000b15a01d040c045410941c0400c00a20040c81180d40001000398000880c504148031803070540c0d19a80c94a01d511f000b10300490701c810104070141d403030010341c10700c181420301e03066000c0f81103460144411903400300990200c1e0011481031308038040b01410314142c400003001000003901e207200800f929400700c6520443c055403452040c0f0180002c3c0000c002d200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 88647959 1250 88646709 88646713
    0x2101090903020610080705010806040914010c02010e030702090414190b070909020c0d030515030a03020309120102040e0114040f02030903132411010e0a0506041103070308190e030609 80
    0x22500e250280c03401c20061300700b40a0285594040000341c0d4006568015100286860041e43c0c680030085006055040f200801c038924a801d0040c6461b4151702043c031020b642c0d80280043c202c1c40d14615268811171001a401040520000700452100510408180343d40002c03035050442803554038a0124200c1070031111042018240404d165000b0244800780c04001e07408c503e001d0994101640d03030018080170703c0505441c1d40000e01205201d80c500c603100400941603407a40c00711483c00944031303404040d42c18450f43c5c4030459805000814426901941c9080c02c803000140d007403161602d01000d80e4490164030640f07d0110902c00007460014500520300e20008613110070128031702c10084034003a004808085030641c42000510625429070341c2e42c43c19820b10706090201403e40902400a01081c0042d600c21209420208071000482c148a1801080e80c8012021024209030b242e0103584401342a15000b40503114000441c0210a4541002030030a404100d030110701190910108079501b039402d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 88649209 1250 88647959 88647971
    0x5120907080f0d180b0403110a090219021204050a120510020a0e03060603060f0c070503041703040512060702120901030b03070e010501020f120d0903050d0504080d11070314210109 79
    0x11900031131000241e0020300c0f80e140c6410700f094182c010078000c9210190041e0312551007141c05448004440c0003400c4403040070742d501c0c1c40c84051101c920040c25200070042c0702d0705a401c3c619013114000d83e026200000d100152462030300c066071903600c2141c88203460398007503045c2d07040c01c1501c0c0342f00407c941c80c1320352500502d10250100f09400d100c0001e0000d070007900804200888059602c0c00b595001c1445890a80c1301c0f00181401c91550145070420340909000e1382d0b03000008080080500300300c0e00101c1d41304c9445540100019200c0200340c030442c0c051b80c4110640c403200410780018202410043c9400241c1800010009141c45400ea00103042d03612407000503c001e507810301c08000c1310700c543d0004200e500100d03040d141041c0b050314a01c40030140e88403000c0c400c0500c582c00700c2e10706025844080c40315003001c0c204100e05503c80324900c0c1a4910300710118103c101405c068464454045e140c6080441c0220002e801170b40c0042100404144550000c865600081d8562406008a82000604 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 88650459 1250 88649209 88649233
    0x309070b03090a030f0f0e10140c0102030105030d11150c120f091002070b0c070606030803010b0c0d0c05100b0604050d031806020606060a050d060509040f020a0902040605120907080f 80
    0x1e0505030441c05c3c003c002e21080c224000c41d400c1201c4211503442a00c250140139404d0100300c501480720280b8055201000035500c1104105402441c1602e2084041d60140040f0207001e40d100c03000c440e101e20300c0782c01c40031000403085003a1030030350340c41040303c03280b5032422540c0e03446c450074914120340c0c0920641251040c020203d03c1000407080c90040c110b03003145440035a449441241600030800c0e1440e0f840005c070b440030886150080c400465012240c0b6841c0d50f1907400711002030304503c82c600003a02c00d141282d03280302c0c0702d50b01c2c0080440d00b1002800501d284100c45002404840307a456400c800d00300030010707094465083c02011580030303070741c2c03900f800c2802c5200159070240d5900c084219030104003070180d180e07640c108456a0710807030304060342d0340c855440b5204041c045a910081d070005422040009000d94400801d03420f038821070f4808456521980700904902a40c001e10340014014440e14003a04a44c001045d0000f40000031502007542d2011803924188980c240c50070150008052441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 88651709 1250 88650459 88650467
    0x20a0603150911040b0705030f1201060f1d01030504050109020307090f0b0405100e0a090501230906010609061d0a09140a05010503030307030218090708090708010b030c01050309070b03090a03 84
    0x80580b080c07600610215882d4801060070303000c1d600030240380d1800000d00d4801c0101c10001c64482e4040405500c0e02d407000d03483c00d0002d0030300034800e0b01c0114000e001c60360802480380607120700d40d107410300450b045c40c1905d6004400420004104032410740d0782e490b000c80540c1c4c1c1002404000e081516001c504c1030a1816800140d0b006405450f002c2c604000c1402034401200005409039841c5440c40c900e25512112090081c15659602a08030351a0142403508003144142000c40020f0341510b00620340c40741f1400556444003480303600d001440030413062244601c030360710286030b1a82c58100408503075250000a540003810398007000c1104e6940654202e23011001500c00d91001c0c002d40104019890813002c26181e200050100081590020343c455480c0f03104201082141809000d8844031324008401800203002034819058603c2000c80000f10390310140590010200003130b01403d100c4025400540b0b06400c00f0b00b004c0802c9c02608004940280c4140156215002c03180080c01550a0343c00c3c003038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 88652959 1250 88651709 88651751
    0x1005030a050a02041e02040e010e070216030321050108071d0408030103020d08041d07080a110d1119180b120412050c0a0f170c0715020a020a0603 64
    0x140290020580d090220701c010503002d10094065401041040b195550040140002c2c42c42002180c404180494140781c1c5622041c140c84406800f001141c5070340c4002c1c1d94440480d10700c201c80701c0d400c4005200291050f03141c0442e948030201e50301a1b40c0700307002044080d41e43c260000c400a6100040401c5015400307c035014215440840040681c207240d20740700140d02c41400040d004140d4890000100070092049038018071580c40084102010740d011a80d25150580708000055204004074082d0f04582c070850784001800c1d43e4080c9020600100380015081000030410b12001c14011220401006400c542100300280c0c3c441942c0d89545001015080d215082035145180c00d102815035646c2001c8903903001600490100d80d05008000221840d00c101400c941c00c500901c0029000c228000e122102c0ca503201e10820301c104003000042c03902601401c0e0406085034884c1400300300b112101c07109941d2000c014816503110005580105101110759448500040d6031280c46000081038200c40d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 88654209 1250 88652959 88652969
    0xb03060105240c1c0e091f090b1c0507031a010e01122604091a1c03032a021009051b01030f150611150f04030e04110310 53
    0x74071000b1110380ba401002401c0e18840845140042d0303880301d01c034040001080118108514a444000102c8028141c2c40060042c5c2d0040d2a804081102501d183e4221003482680310442c4416074070700714500c4007078074800c80166000a240707190407071030314a40c503014514a0b010304010180149145486503844c401c50210783d8075a00940c0c018004010013110072411101c0750740c046410711256007049280c0c045c820807008580c0b000c014000031345c04003545c054411a808030600300142c2122044403001c1d000508100c80d40204030081c2c0c0c801040513056041c4141d40a40f03000249204140788900000c0010310403001000b60f11290540d610360704020400d02d0080b1940140b080b0242681c0341e0b65501490100700100c815440d4440045911035844250061813100c020b00c80b80442d0102c00b2070200660050030f0000d030488001496240000598407a002c070360074042112640c805d18918064100a0002c400b0015650307070448656403207004104028500008171552070400310000c26080000b6400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 88655459 1250 88654209 88654219
    0x304080a17071101111501060f0f081e041a0c03160c03020c060307030b0901030602040303080903040b070605060a05030d020f010516120222030302030901020c0105191d060a030b03060105 82
    0x1060000f400c482083c1001c0e08203081107840030312015a03860038004900740c03040d12004410000141c591740601640401045a01e45801c0c298100381c08440c4c0b50f074200e072039002403415603c00d850107041c0341c4d03201540903002c1d170041170356003038030144140c0c02242c1074581d0f0316060800b1080c8641510b0301912a4420000340c20000c50624044e503020b510395080c0449281b150a0110024001c5030098101005040005182400541e100d1030218001d40103030105500040c410400071320312400000480e400e4501c505420f500b0003500b80c0e500d00160a0041000b60482d42d0000d00103441d0302c00704031401a5442e160081c1034820044d580c0f0300d08441c0003d080d04100399900b00c01850070b940003140e14014440150025030f484208a08015011a41201d01090b5066100c000024594040060184c000d0264251600d40503440011503160050103c400d18807024040c034040c0c02070040310055070084c01411800411041c110005a40b40c100030712410120f40c0b50040400d240c42d051082034054001212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 88656709 1250 88655459 88655467
    0x3180201020607030c020f0a0305030108100209090a0f0609060e040b060f100e04091b0602120405010e0108090c060d0c030f0908121e0a0b01030c030618090804080304080a17 76
    0x790b0700c8078058424018140da880d20280358031700c00e10620611401100481d030b40b9071080e1800030150703031007407103547e002e409401451981070b00103008444038003000034140308841c1c0780c064803407009048104440c0306a560b41c0c02d000074420703c0c0b0b0041d04000c01c000c0668800510305030420314a00607008048031702c00c0c1c0c2440c040c1302c107680c4c030140941c5001003545003840c0424000c00118000b00400080540202c03001449207091031800d00081e41550555400e0b51a501064116503d0500660082074003051404420102c0b5500c21a14158041e10b003608407102e045040c80031495070ba000c812000c03c00341d124074000750b840d034260098944d1000b200c002000540da8a864002c014002d00320410803110074200413540d103501d0380d50f0040140321100010916814440c80e00801000702d1559070707000ca810194004100c070f001e0702c43c980443e0717100240d05c03410a011840100050150020450303141e40c00b4007010641d10000c00140000e00054402002c01c84601d06090310b002d0904200d401650788104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 88657959 1250 88656709 88656713
    0x81501060f03020913060b0714120306040e1c02030a02150c070204150810020306091303020706030209010203070503040b0901080f01080712032d0801150215060d020307030309060318 80
    0x9501d00d1503000303501d4010707225000040001c921115031139900c21500d050a01c042902c1d12004010008188a0f00f4664221003204012039203510004219001d000e50610000c0c0c142d041a801001d4280ca038002540e1b50b044402e0064070302002c1300071310035006038404a000400c55404020241070008444040301580c40c0c030a142e01b0351440b030319100034050351b1900700a0b2203440c48003c850001d070100c8070583e60b6040c0313041a4070000350021207615118019000210380e0020302400c001c0f008030340560150031014200740d0f0942c023035409034402504502c0108038100110b0000d00140c0090800c0f50b103a207944072105d90004021600c060700091061011800402000000090b0340d4100c44451000c01e40b520000d04003078172120400d600d904860642c6a1400180c038007a43c3c00400040d4054640c40b95903602ca161103014074103c0381c2c18101590105c0c41122408200c1400e50b0350008006151240815070303940800c5c20040b16910440115489140600009425000f0360380c0c400320075203c2c4468410f1079 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 88659209 1250 88657959 88657967
    0xc02070e0412030e0d0e041b02031611030d0305100e1e040204020d0203010b030601090e16080c0706060b0a090803070f0b15060a0e0f03010e0c010f0504090609050108150106 76
    0x241005024692110203540480d00903004103120030b640700300b40c50348480411710107040750010300346561003a890700202050110780c010808645400d20b9000310300340700340184940034204940400b44c8091070401d0300c00d43d2a0350100881a41039040359408510307400c007400c040003400c403190071456518681004000c00002044402c03403180c69803003c0c1d103455840d5030000c00c0081c0710b00c03080c0a5400d4000000883c101019400450243d0000c1e0303541c22290380d0700d21204111003002c2e03030400e1401c1403e01d1141a098822000d080d04248100100c80c0360140300d03900d080840d021a031141c517100a000c50403844040c1c0003040300d4002d102001c0503503d0915155038200200d611900018117550221010600041d60604405140000501300c642e90f80090000501885101852148200d00c14200403000782018060041c44042d8440280702c150084001074465175404800391003001400e108c0001e9094550291000a000d9081c0c00921035040c0350800c2d06000d00d01c1040045101c944004120321584 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 88660459 1250 88659209 88659211
    0x6090103112403040c0527060d06020c060f0714070503030f0705070501060f05041802060306060c0f06070f090602150f070302160c0608090a050312220309090c02070e 73
    0x10031038110280d500c003036074034031a8680300050440da100d401004104c20420081211019140e0844d040b5401082110b005901c44414000c8035001d1500c20002c00c0b818200890007000c114480c12015091002c0102c00c1883c1c01401c441c0100896144001c1c000103580007101d0032030b001039441c02d8500d08001a201d540d1b0702d2002902c039030070407407500e8001600c152241042d100140e81c460024018641e5426550160640e40e018a520803031030004103405203d01c1f03811080802d0b0303004d8261420b6a488104001d031603000614070b02001e0045441e190403080301072290920540f080d480340c00b904120f149008000600c00e812074802c0d5889000c07806d0040b40168040b551040b4002e040200a548201085000c0d0080d246020814450f0300e401d442002050050b440641d1003075034601442c1c0e69044107682ea10300e408100030b09550030400c1620025105c0180865200030400728808035180c00b0740c12116100d240f004150000b81c1558024040d0307a140e40243c1218901a10003403114500742200c031016000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 88661709 1250 88660459 88660493
    0x8040807080a0903051507120605180604060308031f05100c02120f010e072301080406050411060720190b070620030a1b051812010f0b03010506090103 66
    0x150100d51022240d206803c114080c6030f002041c0c0700800401c8242400310315007511104045110b02d44545100c02e03162040c0c008841c001000b51201107550356810250003800b8088980040e2a4140440400d2006000303600500d40c417280c2d60301c1400d0342482c0c1440041a500498820442c15001e000c07005e0b800320480149940483d03411060348400c013003181ca040c0720301e000701c507007175080904001e03a42002003516000ca03503800c480004c4070004031109582d01e05d90006103c1c003140941d03001c03c02081d0303590f215661042c440c2c80000c0c4003141000029071b60340c210703400c1210042c04010340150540798210700024450020b60f4540c00056100862840454550103019510400401d940c02400400c1d0403070305105222000391000011001040d4081d980201c88800029050040c0744445c1600c841c044040c000550381e8507810b2a801e0014121402c030441000c1781e0084480c20140c00008080c415020400807030307080001d031410300d20241070a590000f42068441c41842c2c0040022075481c0941c01034502d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 88662959 1250 88661709 88661723
    0x6060c080d020c0109021005070203070f1a030a09210219051009050c040f05040203071e0506030603010b041a0406050906150306010c060501080703140d0909020901020a02060d0906060608040807 85
    0x4000c5031601c4c0144032807180650f2101c07130381e80000c14507a04140200010b43c0280c09132140540c80d24420618504144205130b2540c81042e008a07101c050360000d95003007a82164045072042d8651120744054400d5141641d0444220347c14100558041240c0070b81c0c0c2580e00103080d00040140c44840d114000ca841c80401141c031480d140080100600030b000c0440c0d00108200295010305001c40004c00d0101d41c12402449149400f0950000800e4150b008101004030300e100181040207105182c1c00144c0315a03059901d96010300384655560140c0d0070081140d1604c0c03035100b2003c20412090781c140303600c0b00f8090310600c0c080c04082e0300c0d588010700200c501c180303c5035507940741d910040740e98a40c01d84019001514010002c25102c1000c1070700030480780250802e603122001da0a42648403514841140017140c1d03032840410140507541c001e400c01d640140103441c5440c40076000310320b099001815190655568151130781c104002407203a0070150802e03145c180802d01d419660a0740174498010040c0a00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 88664209 1250 88662959 88662967
    0x30c140c061909020f1e0618030607020a0503030423030706050604060b180d030c0b040809010201050a020a0c020907093302030f04060e06130b0a020105090607020d080c0912070906060c080d02 84
    0x6e4141110303856900400741c6002d0f510380000d0303403100001180c180751074400d025003404148003600c0001c00b00c1040d6003020103035103544c4507079032200d0031580a83c00c24012288040e80003800e031001400030b090414000c56001c079003450071800b0003080350141d80000383d001c1e0b03082c4582c80c0141e05411400e5103d40040e21910b141d892107060503a5503841031200209401c58030b00400c410000c0c05d1018000001c404e8000740100d494600d080c0c020303405000c1c014030015002050b88009490301d103000300d812158506114850644a4500380000b9410f0800341c0845580311001c01100803200c00c198059132254030142d428041c20144540c200d2069103c0e40702004201620200e955813111304980114508035003d19000780d0b902202d42c0182c0012051001651038880020145da40100b0040d2049202c0d601030400d8104480098a81400207004600102001d0100d0111929060301030460080404000e24110385411070000c15a1480e0300300364200710400300e40701c001400d41c0c4141e03040e000c6c0d1b5001c01342c0c032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 88665459 1250 88664209 88664239
    0x503060c1b0f030c030c060a11070807150e210403050601051306051e01030f0605090615160c0e07090b0304031b050a0c050a120f03030c140c061909020f 67
    0x3904186960101e0503001c0051122a84c3c40d001006003090100c0d45d05451a40d030702c2c1d055144c11a0198200d400340303403400304800b100094141c00100290344c0304204450130710030340c0180700d008c07920030400740c09040c0e0040c1d0030407003910624000c034090100d4500700d0510f041c1c1190f5580f0f855400611070203008941c080800841c2441c99040680070301409050021140300c440070f200701014546003120f01103840c0a084039101d641d50300070700c0b003a140040d01e030740350940700c803414041c800c800d0074200045090180200da4040c4440c40d80e564101d801061080000d0f0300304003480e100d0800c00b81c076140510419040c10072080361240162a8410b4040c1065540c6c00d0385080d10301020414aa0000c1443c000e00940000708540c80081d80141c40040d5400c10b011b64071a6003003005820b5000c0c1c05440e4205284400c0c000074441d0b0000d004141e42883d003214003400320f50020340280c00c0480880d802d0b401042c01c00c0351610200c0068080c160910f00b003400480803d801161403901c0b04400302d40107015407018807003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 88666709 1250 88665459 88665463
    0x30901030506180709060e010c02030c090c1209010b0f0901080d1b0b090703050c040903020709020c03070804090b030d08150415080d05070501150f0e0406140408130503060c1b 77
    0xf001c0c030001c601140245480131000b041d405884c050300c404901100c00c80300040d4820895842881c0c3e003d8000c2c00c00015040401004210090000011a60401241030410742002555003d01c0ba50b03400030a24641540800403004090a5031a024a400c00010050f5010000d0261000b03011402d019030032507071300354046119181046010700940203034000d02540071000204142283d01440030358462181c10b804110584003034550246c0140e00c280c00a03c101c0d140b950003440c0d0441c484007124500f800c03a59541c1c0d02c58009074000b0044990300d00d250345160074248000002024640744c200c0603440c040c00008105059107110b24000c5070b039041140c00b546124240342c000780c51018200c0b5156504420018480d50220300d0440300d5500f00030908003071803250801030380ad43d41c0b00a00041c0244c24a5042c03844008020015141d494031281c85001e80704510358641d0060b4082c0780c200d603403010111800300303038462982d20007400395001c9c0e000c101d10b05c05c1141c04d6891812088580c0c1d1465400307070413a94 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 88667959 1250 88666709 88666729
    0x60411040b04090506061302360901030f03030b0f01051204060b04110714060f01121104020315040c020a05060723190f0206010308041206021309020c1e030901030506 73
    0x940c02034a403603e06414840f001800303520a1000311840e600d00c240e0514144242c0c01000c140308448114000003000c2e481d610102400f6207007002038880d082120b80000141764a40a90040d6880036504002205042c0d05000f00003c2d50310a0354080c4408495a000a01612a800c440200740030000c0100d030805c21543c02c034a110400042c0180101c04021800d1500c60780b082c5802c40d035030b0029641101e128a0701140c03880c8203803076401d40303410240e03c1e159540c20140c0c60700341e0840d05c1c0e4110343c402082d59941c81c03000d940a04c0c410b0403980380c0c0c1f6a074075013840110740754031641d6001d65200070030407070010300c00003aa0b9901000500d4002d151100e081b01d81c40d0074040e40002c007040940d000c5400400341204560244c82c102c05a51005c0d114054100e01f0380e1070305401e02010f4a603c4c42008240000206401d10301909442003100611744501c4c051114000754041d0004040349400103241010107008102101d401e564404904155041510205550303100300d910343c6040c036440320001052030f5249800c0c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 88669065 1106 88667959 88667981
    0x1209020a050f13020c010b040b030f0601051c172a070b18040f09060605040c0903110604080a030801210206030403030f0e030705030c0106060503040506041104 70
    0x100040b03006040090350008010008055078030781a20080c041e096640c000010400c03100c4003004161480c001080344250b1090192030455000402c486c2e046540c110340e00000c0c0c52401254030038071505c41d000500090960490542d00f1800c0340b0040c0b0300a41100e0000c1825002e40c0d0a1500100e010010b4001c5940401c0d818030030f100320240284255142c141d01e5440030130201d400201a0b407056a000003456468000450401045014640c007800d0111030038402d48040340303c0141100d40511024040030741c40a034208040e15610126005403c400d02581c40c45400307410050301404080c801c241d101c00d00780843d4008100d040c1c1c80c401e07405034018640e07032a64031551001c0b4040e07c40004030b260344070b40d12081c00d40608003c01c0107051180c4108051911034407801160750856000d580b16109109080040100180b808a100c5ea030095110280318104000600402c0060243c0760b02 = true := by decide +kernel

theorem cover : BRFrame.Cov 88489209 88669065 := by
  have h0 := BRFrame.cov_init 88489209
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88489209 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 88489209 ≤ n) (h2 : n < 88669065) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
