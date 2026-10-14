-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2184
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:54:58.443851+00:00
-- url     : https://prove2.me/submissions/a9e40ddc-7727-4552-8066-f05eeb7762e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 392625899 ≤ n < 392805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 392627149 1250 392625899 392625913
    0xe091b0f041401170703150302040207030e0306060307060f03050c04051c0b011a07020d03031b030e0f03031303080c0903010204030803040203012a0e0303130e100f030c090b010509040e 81
    0x30020b80000c41d0401e9141001100005a8040004100c400d508450345281c04074541e2040a481071041d40705401c0070b58060f10007c1d59800f01604002074008040b800d03010750702d00760b5a1a0416455032020700c04ca40200f03040c070f02e5068496100c4c0d4421540700702c42140d42410709407281c011460800b907055183d551030b58400c02003802e100700c000792180188480074400401a803101103415583c050786400038060314000c0714003c1014080d80040c04c1c40030040702c3c10401c1c000c1a0600502900b2100203188040c012840b040c3d82e1182c0c0401260311803074031007030780011200c903541e812142e5510080036a180440e0074007800c402950280010b20055000340c00b69602c90401d4010542118030010128862110344141075610400104110701903540509114100d009040c003c01d0551180784660488402c007408013185064107210344900031890182040000354071a485011000c1103030202410388280d1000400c0742c8401500070202a94042c504141042c10010214040d200108042e8038035800540c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 392628399 1250 392627149 392627159
    0x80a05030c1606020d0f031e0f14040b16090e0109020d0b0303090f06030c070c0e010303030605011b061d01050901052a0f09010306080f0f1501060e091b0f04 69
    0x10030215012542c864000c1c0c1d1800e04045e43e503003040d40301c5505010b458250010010302a078043c0841c0d40d40036040004440c065414180144424500c0181c0d1310300e4002280711514201c02c0d40c1c1e03c00ca9008140300c09030785801c410151000340c111100c1081010f03c030780119041e00310b143c07591300a040303806000d80c03101e40341038040701070740d03c80388a0a02aa009000c00da01542e55024000d0520105540d2259652600014000c040c400d03108081e0101204400c0026540804d1004504980c088d9904002c5140c42d42e00441d001c014001c210340d502c803168035000d40890700a600080c2c21121040c00c403418031002450031030960b1000c07103644406940d688200714001600030000800703102c052a5010710304482450f0645903000d600c20541250b50007107a642050390196000101410400c0226400850a0b80105031741c0c07004509450f44a0045240c20220782d008011024160340c2d9648950f4205000c0d11f013448005000100701d500a055003002000300b02a130040141000032200321100d640358100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 392629649 1250 392628399 392628403
    0x1050c1b1c39030615090b0d0b0a060f06091805010b0301140105090d05060402041104080709020d06120b01060306061b02010f021516080609090d050307020c090c03041b030b130c080a05030c 83
    0x80e030006c06814145081c0800170358540308800f40c010b40c000511400e64490030007007001040642c01c03000a81e020030a000c070702c00790445188411180c01c51200b81c140c07410f1000a1003680c100384100d80203200244010300100e020401d1400e070172031062500724100003400e00015080c0c10300302d800340c500e50441c400b40b00c19420310b8001c0700200c20701461074514007450204456a14491440b60000c4d40d0390204107000c0400007500504028240a1080d0380409070031306144901e100c00780715410120b49801c80004006000c1d204848495240d90901c204902090300103460b81c451f400900c2085001d10748258001d050314035140d5000380084000c030003850141c040302912184000d003400348140c7c6448100300c000140016042c00d860302c41d140060b03d9884543c000ea15110003d50400da00850b007070200401d1442060266103e14003d52103051400b00e110340d40704e00b0410078000600f01c00b0707900340000c007805512000c0020007880341c400d00b1409580c40c480386080042d8030b50101d03403503040020056105001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 392630899 1250 392629649 392629691
    0x111030f0f010e130c03080d0e1501150f170411030c090f010303030b010903150506010f03020910140903010504140f0706021b01050c1b1c390306 64
    0x400c0c80c00c058550428540c2c8458000042034100c200e0480d40210080090342c88221700110f41c00381015407680345000900028001c40380703034046a07100f640401d0f45c05150070f00e0668103d4000240740918280e40c10030449113408180d103188107000324070500251084039260090300c501e015094000c0003440035010542044400c5401d00c1c1300b040c0c00c0d810b01c602600c0714070142d811254181030014010010000503903070061182c0c0041c2c485020155002c680540316009544136000c240d1350403500c1041d0040584c203d00034030400c44e422000031000d086c10540070ba9003a40c503c003100c0d56440d0408800800080c299002110212250f010a90803030100500800c0010f440d0842d160291040900300480207641781070142540c0d01d00030240c80380040d01e034055400c94000b0111b032030076070301c1e4801010900d6140c12120700c2d42a015200752104142d03e4810800000b002c644d0000260140812030701099808510030005242405c80601192011034000350b800300c0114810307c004071300310000c1d001c02424481 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 392632149 1250 392630899 392630911
    0x70903060b040b0f06181305100e0405031b010f0c0203070203010c05040b03040b063d0503010b1614030316030e010b06030c070c1e0504060b0a1b0f050111030f 70
    0x4102444201e4070b41e131310700c03000342002130544d1201c0d01d031030680d001c211002c43e07500c5502c0c0d003014031840d481d00c040c2c07159086984500d42c002c41031201d1580d901d203515020b08044401900304d41060000a50106c02c0c1c081081800c0d02110010070119140c44640703080f20304036801040564000180c05007142420b028481e112550b0f0300305207081916008401c4818400184000d107a00114000280340e40d803810200305904454040c02000410861100c208901c4040f40d04040448083c032000c030000d202d1001c9034181c3d4041c07120035092906c68a1b0b07a02180e0424902180d01fa042410207000b2100200047c510611483c2c40c61004d00c0c0801c034029080b510015000d05450b4145031900c0b0301c41d01d800045903040381a0b401825901c004c02d041421171030129401002c0300a4005e000389022200e100414810759004840801c601341d96000e1146a030300c01e080c0c459011038407000408150b5803024084111150199100000d40b000b203580341ca00710f890424911403041004018800840300084035141d2100b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 392633399 1250 392632149 392632151
    0x150b060a030e0c09060d1716080a0816051605030702030d0305011701020711060a0e030d0203270f061e0301270e0c12070306020c06091c121a09070903060b04 69
    0x1091a401003104400c1d81c00c0091f0600000c5440802c080484000315030b1010b0300040250401d142074a0850f04591102c2049400110180046551a56254038030385101c03080d45c550510b40902c007080092440e120403400d880707034002071280b0745c0540c40520079000201e0450740d0000303480d8100b00550000c5410303002240c0007a8414454070f80014030556038201011f00c00c0302c140d62213591286045070300e104d417810100c0d014010824480310345a0008050b000302070b054560100f2040d442002041030790b011108155005c02d10300315820075400e02500620859250308048000c0020640f0202441c0d402030340540001130b10524159080d10481c01103141c0400c0c2078506006009480f1400d5944008103c940c506c140d0b42c48110034005a000c102803401194461410b649448210303401030748846040b604071001d8055a0840c08940d00988100700d40501142c413603280c141c070300140800041c050803000000031039204203a000140d0f40d803501c0c5449140700c1d030786480d81d440c2503181500580b078070114024069 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 392634649 1250 392633399 392633401
    0x209090c0a052a100e10090b0a0c0c0807111c08030f060a0504090602120109020c030f0901020703140a060f0203060607020f0f04231012150b060a030e0c09 68
    0x7141e4007004480000411103d1003505816100c910081d0090201122103d0301c6070310002c4002050a400c850242e0034441c0c1039445222020f00ca09060381c8074003200400018504002540d082c00301d0f441082171b9505c1c1d1030024540c0d82140d40764009544140025039010902003580c03107040c0f801c180040c080c0c041822501c0c21102c0c503603a03000d07098000945007184044442c400901152298496980203080080c030600011105080c110002d601803020380606260030400070a04001034000c444c1c01e1a8180001c624241418040c3c4200b03070015002c80341140502e0100201040b09011260080d50900014066103c11850520b0071200c100300004080341c014410420907a403000f00351070005405985113131030b9956900000d12626071440700c5550007481d050740c2c0c8082c04e00c1c00350b00140d04501108052101c0d11032480d6a401c0e03100e20312035a81a52000704d00c0c2800030725204008210080000804100a0f0281c400100103410090312440042d990b140610b5040c0802c004054684509803881c01131 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 392635899 1250 392634649 392634667
    0x1605010e09130311010204090b030c18010315112b0902010207060507051e030310080303090307060b040b12010c020d0801080607050c030f03070504170c09040b071b05010209090c 78
    0x815100500030b104115801d210403091501a08200c000040528000c55071242c54020303240c02424904603441c0039114200c90482d160800b17030380d24070001030446d005030aa03a00e550b842810004000c502c044602d520340c0e800222400d43c000c05042003891604012291102010001d40f00c10610244440d0490030714031402d0250742c0205141c02541c03c203107401a0380c4c02150501a240000607074410b1500e40c1607240200c9607240100c013440c029140d070000160085d0f542d00b18160307240015039900489800c04c0200c2c5001502d071741c0c8606101c0001400c0030a0a981d5040052800701c541500c171441a51116254200d03140d06202e40c0a44c01d00744d0600e01000c1d418600b4603951504002d043d00c052107070003e007100301c60b4020000e5810038059070015598a1074682d8000b0100d40051041c80180a644811841e00010204074103070100c1c00517101d0440c90340c81e6110411400c8020b0448c40034007403c0c1062039a410941d26840c8480c2c1d009034009a80d40404205000002c0da00070501d19203500d0078080b40103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 392637149 1250 392635899 392635909
    0x604020306150d020c030c0d0e0303030114090711011506030522020f0619111507020a0201270603140a02040302130209032e0b040c02030409050c04171605010e 70
    0x351190b80c500116118a04038410760020b104d1a590b4080078800841d11240c0d481e8005800d8518502c80d5031502030f500f00030340c1030598a0100703029401014882d019142c5040c204001300300e1b40321805107414a031100035075400500b1104002070b00d10700b00030b001900f44001a0140610380d0070807144558010310304400202e540403017582c080001d2082ca4038402d240800d64406007a21030ba018810b20141155140b4900949803514980403c1003c1c0150001c40c1c01c3c8064074040b251203940b1540251450010baa4011030340900700050f400c81108515855441c111051206c03000500540d0b100021980041c50a68100c036000525a400c4507004010910050701c90701035041207022103032400f507299911030b00082d04100d043c0c0c40f0468404240c0700302e2000d4070b1001c5e440544031040e0078010441d64498409200984403251441d001503402040204a020f0f8141d0125038402d1014212a0400307413900794680c0400c04001080565605c0041c1c4003661418003840440106000d0070883c522a801f08049a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 392638399 1250 392637149 392637169
    0x1d12030c061b0d02030a0204091e1103010f0324060801022502101421040b1e06130b030604140601080c0901030609081c0606031802030709110c0102070c0e0604020306 73
    0x10f0801c0d80c000c004900302e507145405413005000c0740c12041c842d2203c400c0315110b0f007a011041a0181c2420070020702c034080f410a007180d05844002002c0400d1030b01b162500b15a0380c61104040409180c9905086980c1803a446800003511f00d950025130703030320880e91540b82c5200745c1100054410710358032101c00c01a44c0d404610503052001d800d020100ca504801c084100c0c0c003a804100051503001c0159070a003164840c6d10a128510425003100035444032090480362103000c0302098110b034803120200b6500d24252061210441c50b44401150070003808022038104081980d00f1030740340c8080c45520308252030a0020602404154005081d580000400039030060f01c180b00180074941e071040007406006401e000c8440b10b850495207004610351030415600145901e2182c480007034a404252045000c5405644140f150000c0060440d2810056103000802180d076080f144128200b00d03482e042d040038006058110700440605c55400c1c83c006441c45c0d201320042c44248220302c108100029070361203075451 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 392639649 1250 392638399 392638417
    0x6111e07170f03030709050a09140a021b0f06010e0708091b060408010212010812040501200114040b070207050405040302100b0f0406140a05060310061d12030c061b 72
    0x52a100d5641c00d1515040075400128801240400010000100e800030340480c115a001d9486030481035071170b40c0401c1160b40d4031259888180688007c6035020845401416600c1c5540080c1c004075981d811107a0320f440515003c19440e500000d00402c90031038555103a82c0e21407894100709881e0310b0040000350f1102a2101c58070044000c000300e00c14642c591000356000f80480030021580d910000c02c2c6014041000d00c02c154091090007914880802150107032030440348180c40e070350005100000301e60b200c8a00304000000035961400214401d854030f94640740201c0c008d90140c02c26080c0303203100904018558000381d00841c10706041c0320029500060700075507004a0310740055850b14420008020514000d00300c3d50207070a107100800c4180903008148005070741101e281101d29962400d2000354001142c030910b075440300f10401c10070030b4026900030442001030400580385200d14000610a03002c05520002140d0020500c0290b2150400030142c002d40c0c1030700c090791640c0c400c1c4107083d03a5114101039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 392640899 1250 392639649 392639669
    0x70506040b0405100204090b0f1234030803070305070903030801060507170c010b0406080714060a0207150e03010507020a08030a0c02070305070605070b31081306111e07 74
    0x2403c1c040240f00403014008132050a6644503985c1004c000a8090052028415103d4040884691800303003003540e0140600c0307014100c1805006c001c400030346621800384121010b01c1d01c8100d694041035807000050362007081407075100e0138842002022908002d20340c40600c2040002030000c030b40c11241c818110340292500d60703940c0301c1501d040c0d503004905006a11900401140104140006402c440362141e41980e0400c402d40d51480d009544d261244135403408003041c00c20741d000700d04001005112482c014011104920f90b10504024000945041040000c0c030030041d5a17002d01d400c2c0502c540041544c4001c2c0484071060701e4100951001404009040361788001c4c3c403c0041c000e0107000300564000c0d0503504001d6590720b02030b005600941c03041300c20741150310000d410303c0c03814002e100d1200307140100e030014185020004000f2540e555416209500240144903019a0508214000e803103030380c1d103507043c0c40c1d600c443d80c600c1c060340316800c4001001449400407000c200001c14408603406020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 392642149 1250 392640899 392640901
    0x6040b0313021e030d02070e13030c050712020a05030d140c0f030d0203090c010503282c0c03030f1204031707031506050a02060f04030e0a03031e05070506040b 70
    0x9854a2091507022000b5080300b4400a508000c00c24000015031641d820f4090365500c403040082203803940389030b00070004060400e074003003030a020054260b1940d840c428100300743d442c0100e880e260319014880d8091130303c40303072041600421802d08000c040e0080c00260300410060025280c050092480000b100e001041c1c0414a1400210104691004202c00c174080d240d84401d098580006948122a1a0070f03e1140034105030403944a10100d1b4411201040d1401403000b20095254081c060030154180181d02e95212011a9407031030120f144900620509420701c00c1d00d050103074200701c1e4202d0400d100c1d40051003a0741441b5059011160010210904203649079554981521015120700c14a03004000c9541000302442c0c050340b00704c0a4039455124250060381d1040c00325410700c104011900160400c4001ca5210b0030541400358005210303060440398001c8200105403620001c0d1310a80001d001c01e080440d18200d20003885500300030b00c2c5401c1e071a0403061346a80e0382c2c40c80b004d080280380011b40c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 392643399 1250 392642149 392642161
    0x102030702040f060b07050a02120c1f140a050c060603070614090a03050114041b03020604150c02040c0e04060b0c060c0714071401110f060a0209060d020a031e06030206040b03 77
    0x40e11850182100f041e051340c40d031b8420700b4040d40e2070410340070490061350032001100b1507100001c0c04040c1c600005190f5001a100306815500002544d010401031158201d5103c8114400001038908610719039102d03615811200b0000345020700c00340c000303070198000032024000f00d580004190704c0c0036244410700b640e800c00d0101060410f6030300c1d4400340095180400d0724000210001820780900c2c0208503550b05040c60311108210394126100003503205004200c200031a0280030740d02c1c14105039508010200c0281500031505407521090182c00083c052042c8404a01e898070500300503081a664150421102c50481c5d0b54070031000d4803540101030007017a00c108204801c00c1c040d600d0103000c01503030401a80c8405503078106607070818103404595403081c5810000d40c0014006c4003202d1060041019481c1c0001400003540600340050b0040020449403861070b090f80010241c19140d82c5e800590400d1802200c000313480088050034113035086c5070040015039100c201b60b078251424440c14079940d844003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 392644649 1250 392643399 392643401
    0x10f1e020f04030f0b0f0c0a170406150e100b181909020c0c150903060a0b06070605010e07090b070b0109050a020403061401140a210227040516050102030702040f 71
    0x241c0d10050420504c06014410010a00d41e507a0141d102031004034016115640f0308501802040002da0000d41510b04081000c1c40b60305a00e90018090f20000480c8900f180c070740c0c2002d80c05a0820143c0768203910501141c0018020b4840081a0741d5071410704200407044000125408080414880c400300c804052500082d440190018240102c04544c0da0301c42015036501c40b0711030328003580b00340a0940c02805072441181119102c580c0140038001a0b80c0c1c2901200080014054490b00120240034407400144603104450180458100381c600e249010744004000508542110722103080c00d0005c0e6000803400003d083c156004810702054036a900642c0400030b00503980054105800c11804071015119406400e0590395070170242d8008560380320034801d00d182c40744196540808482110b101040e001e0742c0c9a016144001e1040c0030340c10b1604184000315052900c10300300e102a030420300c0100314041140c04030440c114600f000c031782460030340041e44034000e407031010b40183d1f20f903880c0c800b0007010307 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 392645899 1250 392644649 392644657
    0x1608120703051b011e0204050f3a05190f15110409020702211902030a0501051006090504150501030903031d160803070203030307120209040c0e0102010f1e020f 70
    0x589a014481c2e03000c0882d125010301400c0c0d00700135080c0300c100c4100700d00300e217140215410f4500283c00c8084002c3d0000600400c1850f00c0664601c400070b83d40c2c0210100351440901d5140042c0030b0000c00e11030981c0c2005820042c2e02000034850710b51001310307100000d03042ea2002c41050b0b0803405001e48040043c2030b460142c0b03500e42d084901180001000300d4040038070ba02801da8140255501048000019110111194103030b40000c00b41d441019249002d41011030510b054a05c060103440c0d240f5141d0b9a20782c04d5560586484408c02c02c0260706200704ea6200b0000d10003407900320b405101c07144131181c1c8181c00d19200e000362410542c03074001c0a02818080d4000c0469807140407200c0d07101030412501c45803a01d880e040e007020b401f00c424600085880001090b584040c0d0000d0241d480d5440f00a82500c1000c40c181d09421000d03000c0c404164980d803035100d000e1401c66540c503025030011101000a084484800c01d0404892801890303002c106104007040c040109402801a581d0030310504079166402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 392647149 1250 392645899 392645917
    0x702121312080a0f02060108071701060b040e0f090a08120717010b0a11010905030f070c0b0703030b15120103020603060604090203101d090303040f02120604050d02160812070305 78
    0x1440745a410401040c41c0003008520050b56440841c00e00084080f80c660f8000e100f5440b0b503600c1000c043c01205202c0c111314148608950001800e10350360f01c0d100340c45030400d9100c03905100e000f408005e40148505021540031101d000a00b155103c5543c0700b0055025201ea094540c40021001941c1d2a0140d10000029520040401c0c065070351035801c81303810b03804415010001078207100c4481c1c0c0c0507014000c00a400364070034065030409640c4401a061604940c80548074602003040025640c0c44c00001000c0c451f0080c0d0740852140b200c4414000c618480382c0304e600b031448080004001c0c1c41603010519056035811601645c3e20380780c042c0021000c0c0140d4002c5202c0c0d51000007841102c000d6000c510044580400d1411800c02c5e01c0101711203540001c840f12849a0010000a400100ca54800c407040c40c0c03005000508000e0541f1001e440e11000300c60499155100c9035030400021340400400c0400c800f0180312882842c14030610a860f00d5011218099401d0b01041701802c00d4003a00a5640601d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 392648399 1250 392647149 392647169
    0xb040e04031b061d03090a150201230106080609060d12140a080411060408070603050702031e0a030b1918180f031202030114060a0201060906060c140607021213 70
    0x101030400d00c3c0103141d401103d83c2d192010b0620180d82c0c41c008010707240001001008503400034a0501594044440c1441da04215503807182c110007041c2e4640480c00703600b506003008560700e41c1814409840208007400051007080c1c08820003800d40e95001100e10115480b5030240055020500c041e2205c212031000c0c0c9080d02c50100f042c000d5654054240f610480c00346684000c1d002250342030049501c5580213a8600e03800070501400190300079009240c104031184100d030b140840d21301c410780343e001c105800c0001104000564100c529458000c1648403401102c10f4920059410f492480b2010320348034600f150b40c0c01c4000e0400300c00c00f41c0d1050f1b11138045442508591070040c43c0c140b60445a8180c00c6000c60b1003ea02c0d130000603428401e50303041c3c4095010707150403440c2e020b04210082e048542c5e907404564aa43c004070301c400381ca0085500800003515400c1d034000d1140f034006480044441582c480d03500c100204208580d00140c43c254000022411aa9a142074410b550a9200b242c0040b2210 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 392649649 1250 392648399 392648447
    0xc06090c0803120f0708042303030406020903100e06062404062303070e120a0c0f0918020a14030a05010204060c060506010305270304090515040e070b040e0403 70
    0x2000301c01446081c240000040b0f0598910030301048640c402c2c3d550200050421000a001907002d200b003a04030342d41100c1c0340a0315019030741014a16030080b1000c485190b000302d1092441c4c242007080200c00402c0b90424448001170003240d5541c0c1800800c2c00303204000100e248003d200c4408038444401c1e111a2160345e4880d01d500c0c2c080d000301f500c0e90520700c01000c01e03401000d04943c1007007a0780c0102d04d1941c40c40302d03011007070301044200c45881005008034003900c43c001000441e0030b2070140040c200d40c1d60301c0750040c1c9170120100885007842104020754003007021207001a5240284902602d40e820180d0740780042c150040303854520480c2d03004029600c00140450b40301e0b04134a00b10700d02449400c0921082d1703242d4004409890080d0307a400b421400304541081c16100d5006a5100201f4540c2128142942e8032413440948105446020091a800740121458249805003413442c246e100700500070b0525008803410f541c4900e12800d01c0000d9101e010408141c071a02144103242c2120201c5003031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 392650899 1250 392649649 392649659
    0x40305090d0206160b0606040e131e0c06021c050405120118050a0b0a0207050303070f121418070503100c030204230306070e100e03011515020f0a02060a0c06090c 71
    0x104060130b40107465071110140003c410386001c10450742903d6101810384800d4075030910050a9120700e0b0b1b400c5580d0304240401c0804010118902d100d5140904020b64030607203085400380c2000c0000034200c00071003081500f925281d4008089500300d0720140d40091083c481a01200d004003000c0b00d01034440840348280e20240000014880c04903809401c402c10a0703141e0301040c0c0c00b2441003a0b801482c5400c2400043c090754000c88801d0b00318109400d0041c107142049115504941650301180300c04401c000601800000c240242c014503140c410050440f2804d000c0002c0d40c4640f6a0f120f103c0c119240d40c00c540c5118800d4064400824a2103d01d00490b149809600716803110341c13160b41c0c01303403140c03600160350305125580c0c3c01c00ba404041c180700030b8051048012907000706007001403905076403282409414004031005a40007032408070303030060405c150450000e08000c1c4400103590710fa805106450701682c0d4030401c5800074481402c04c0f0441c05800e00d400c0001e80a2684090445d41510350000741c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 392652149 1250 392650899 392650927
    0x1030e032a01090b340e010c020909010e120a021203040c030519030e0102120a03020705070315052707060c061503050d020c060711060c030c0d030f06050d0b040305090d0206 76
    0x7000f0400341064403c510441d1140403031062200703030082505c20704141c02041d0207008140c000943c1c0410715001c50303103281d00d8010506000b002d0350034554681d0350300d08d04c1c2440c180c140040300b031b500d44201505140620b0483c00960344d054000480403840000030100d02003191032440c030002075030300030161040d590750042003a0100e2204003040d00810f4887c29180860341c804509003081d0456580540e04100b16841c084000b5040b51400f12140d00c50032070302002042d1401d82000c40094120b801207143c0c03500003a41000e02480340e075022901009090f92010201000c281c00b415504c5e05e1402136924101401e20707a02038010803802d020040000d40001c000c0c0607001ca00384a00340001c0d000c0324000c942400521010307104000000d885422039084c0ca0703d43d460071000a003684081d8200b102d0901d108250400e00b400700286100000c80d030760344001445090203000d054020001122a00c05207403450300c440c80c0300b441c01000181001800514414030365a040f42081c43d1a4018140588070030030685658 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 392653399 1250 392652149 392652151
    0x6091809010b0109151e020c040f09020f09090a12030b0904030c060c02030906030a0c0c02060406051c1404030c24090614010303051801020721060b01030e032a01090b 73
    0x5001444e000404101c00500b043e130003d018565550301810303480f40c861301240444500880508500034000803200c41c0c0e0b02c81c090800307000c6040c1c000040c50082031040000c106070b01035155000e0842c4d00100070104070042960010590454010300c00d6114402d001c60003081d0034019250b018115200740f0050507404005207161501c1004100203130102c0d00010380e83c0380160b107000c07a40400c0c10000142481956002104010424201503010002d1540000e4040d0803a8000c1c00c0052008502146011507800540d000708407070354403c00038016110000d10380000700810103410720880d04500001c101024410321a007801c41400c00040e603174500e088030082d240400c0b040c1c0d081d50403c50700d50b40e0640021141812240c3c1521001d1603c90380320340070b41c0c00aa5120782c1c0e60660044400c002050000c203500b2481c45400301e81d008440307614919190301200da80c0702600b4109442c0c0326510300300c61400421264840605280411541c81d000c80002114002c3d00000d005542800708442c02c00008202d81 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 392654649 1250 392653399 392653421
    0xf060d0b0109021222140f0d0221160f11100c02130c05121b031306200417030c1212011202060d051510110d030504050601050609180901 60
    0x8400d5031514a0300a034a4020840c120703000100c5c920500700024444140080442040700680300d4180090000b1820002880d000c4070150300582034411043c000c80350160004c803841002282003600800e020004003641e540014030f4141210004002c1c456000d881e407034543c43c003c001d200c1400e100c0d0710080008078200c1040f03010f1031011080000c820701c1030146038079080c52030f035501d03040100c00c03107403800c108002500110b02e224a800d08580c4144520005511600064040750440d1050380303024022202c076030a8014016050414000884800078202c404907010364a42c035102014420f961803c40c8540303501d082c0d0900c02c0c06044980307164000c0c0600443c04403901075400981c0d03590b10001c0c0c6c0c06000390000394800c500b0054021900312661003039821424180074030003907107000d00108226081a00420004c202c50a5000200c81800c001039030842c00c0504d4107002e90b0410359512582c0d080f06000b01c82c0301d12000304000030a911020305105054260310741401403070030b0183d20740340240aa61300f6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 392655899 1250 392654649 392654677
    0x30a090806060f150d05040b0709090e0a060e0709051302030105100e040b04061d0609010c020c1302030702160b030a0b0906010c0f0302070503100b030105070906080f060d0b010902 79
    0x10003a0000c28414410035000d0324551030000d4075020025041c1002114603d07180041c03110500b03020035032251070701c154407400900043c0d04044030041c254006580c001c20074507043c08405040c244020070b404101c29400200400e524010403640390900e1601e4004040d4a480c4c9010070040e000b80d0900c00e40a107000f90000c01440d02d43e003100c40054201c5004403000346040a012500007203040c0d4042ea4024000c101c00102400b424060f44403040d02c8100c0100154880010320070000310a2041c14040c8407240000c07c1c3c0030081c54041103800243c0c040d1101e074181d0100015188900900100c4040d0b1550355003141c0164555103880b01ca60400d41c1c0d5104618a0107003002614184124640d001d40e40584400240b6102d5a80b804000d07074440c2d108a00b18090950300044a031400c010744001072409034000704400108106060071500020902410080020410400b068104620b50340003001789843c140c86070b44100c0070464204125000509480c0700c00000581e50510754090620b24a08101e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 392657149 1250 392655899 392655917
    0x15062d04110f0406050708040509010311130501080a080d060801062c010e0406090201120c050406031401240302090a0b030a0f0b060906090118080a03110a03021c020f010509030a 78
    0x36415004180b010b000e44981044180700103030044000e084164407500c400791034542c80b0404140c18040070303482110811704440c0c45c11910302c1c090007030a4401040020410141d07240180043ea1968a1100a08600c0340060703010001851364108001174549900240041941d640308a108100e40c140b01502c2c9004140030b02c4001c900c800345660480e550400710001a80300c0d5203951004080c00c000072414400c0410381e0070000145401024134145042d10303080d4449161480c06415205100e01e0741c44034140711310061160749401810304c030210310740008c51180340030000320a900038400c02108980c049000e0000041c010a0000114031852400400788046201c070500101604c0d032445410ba44140c05004c4d40000d1300740503000d865034148c1454822080d181082440e070b44070748541c03c0203d00d500440101030a050f000300039002a4030a100081c44500c0054400944071041d0f031521142c0404a5100520502d10802c80300b079480340384500800140c1000852a030b40d9904c070310400004500c080c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 392658399 1250 392657149 392657171
    0xa0215010e01081c21150308040503071d070509030a0807060522030e0603060f09010e040308070212070201080c040302131a06070201090308310e06040504020315062d04 74
    0x7001c606001102520f501d443c402e15894101511483d42505c400c0d80740e5940b2010310301d80c4a04006000031801340c01400da581d0b003000d0606061152940290144094002c05403903603104540545078000c01d940303045900d4058207400203041550b03140000d0020b10300070070907205200031381e44a2801281c0009500f1401040300303620038480d5281070405004030704c41c0e000b001b0301800d240c00203507404107000303100040d59050131300040c03c0d001d803e8001c00854110142004105038100d02c950f9003003555400141040e44c048604040340303105a0030024108100003001c2903c1c401d200d01611f000e1680140501c020059444000f8011b10702501e0300d40e400003c02c2c0760541c0d241000d00456030042e030180d58040500d82503440e540b40e2640030406c0f091600703000c507880302d845840020a19104080781d4903000e02d1203181c286c45180144018064034031440c81c0000b800016900000d2106240205000714030740c0c1e41d6070b48001400a0025040305d6055100d040d03074261f414103143c0391601c00303c000711303070030000d014581c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 392659649 1250 392658399 392658433
    0x8060a020a09090e062404020a030603150504200303040e0403020c01080711070308030c0c01020406050c070f0e0a090f02090106180b0a090618050315190902010e060a0215010e0108 79
    0x1042d04c00307219005031021039168460f01d4042c04c16500500202080401110082012680f0084600d00000e0780d0b84014070030080001030742d11805c4800d1400313016030304140d1510480d0084101303c00c1040d008c1c1e004204020384080c410b072002071a861a80030124902400d0180d03d40c0701990701507000071400c01c00155401d0255010083d00c0c21400001e047c03090555031030040641c030217409940191014404840c01d048240010303c06003000360b43d5070b03860b45580d0106030300d012a07a802000902c1a440c0d02400300d0083c0c0c40c500c5501030070315070001c5080c02a0f4104007128940303403880603400c03250700000840c503075800c1865113078170018110980b20455076605405c8158052030860600140811004214440c0306442d004508030700104803001055407040003a00e48600494801815580d0b041000181c1c0ea0032401d0044100b500c0c10306008101c8a5400281040c48201d0010311480c400b0a060388668420441651825840881c0c0d11031355858005000881d1000d2242c001c0728405c0e5881d9280450320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 392660899 1250 392659649 392659661
    0x210a0504050c030f0303060f0f060c0322032d15021c09120818060411090105240a09050d0f02120304060207061b05060f0709050d080906031008060a020a0909 69
    0xc0304d001386003141c0320a01001100030b103004d00d00f5072201104086004d01d554090040189000c008025076445816800c892154454007607071540b4580618400c02c04280044140c5d4008184007510030b044624000c9601807290120710003514541c100e002c00384000009600805041140b000401401c101c6c140c02c003403d44040c00b400a0207201c2071004d091046018a10780c90f00410b00f5400d4000c1c4c422150703c11450718204860940d40c81c01c5012a181c4182440d403499805030000350741e018140c2000c0f80000f4188121108c0319840d805002502100f0390f81701c0c0c80c1c0312001d003100400202a031a0242001e120f0030b14800400c3e0310808015010485001c000401c0350100c441c65000f80c04c68901d81102601d802143c90710448103039640410140006005000ba5481840c540d40d050417207092010004000c1c510680100d03010b0303998200a080850706100907039074000c00458206540703030380e1b01580109a4444e41c0c400030940c0309600620642c03004039006002240030b103550b0410055914204a015515 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 392662149 1250 392660899 392660923
    0x50901080309130f112101050105040e1602010f09110310051303080903360154060305060414040605041a1006080108070509010b210a0504050c03 64
    0xc20142c161006a0b00e40c00c104d804001c9080c0c001070580d207154841d0b0880d408408455091503c0d1411112170802c1500341d140504000c0c6000341c00c0c03c2c1080c003040c070010b4001d401030169107a03203540c3c0003480f032017504030058004202605102000c110320381002600c2c6030200241c404d00a1182d4806d0f108214801d0a1207070f100c8680c91200c8541e80e4a055902540c00b600c0006203010030801501c0510030600c48100740708402210405000003492141c40c0303c13644e503495504004940203040041a0900d6181200240d40c0b4410640c07914071070440306079034410b400e1a11f0180020b100d101c02480c10a000003086400c592000d000c907965800400c011107031040f52041c1104da4940c0031401041c1103030b00059100e8810320424801a403600c011481c403880498590b243c910700180b042c000e003070f8420f104a006208860044c0116820800002c038510014083c20454841c0030600386a0725800b06060000079806090509850500c0025500074001c2180c05403034a1062048103802802c0010b4210f000320 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 392663399 1250 392662149 392662159
    0x9070312090635091015090c080c040510051306051c060303020a0b0a090506180d030203040f03050705030714030d06050609010207140f1807090608070e040f020d02070309050901080309 81
    0x25140380d400c05200c0000d807034002503214005c004080309903103109003010018420707135003402d141c0b42c00e0402d0240d07900d4004540400483e04c00b03110a84060b01c00b6070781900d201302e4402c41d020019a2088030980200d0032000503814024000040943d00300008013003100c03155802c20f00202d00400324105880382032000a005034030201540d004a412290f035180c000030750000100d510304650700d42d1407400c3d4040e140440078100e40b0400d00b1550008100020100c1c442c0d05055065145c00d4030380b03ca00481644015007805000955981008030600444840941c058040300e021f8a11600c4241c0d0380e0072402c0c1b60f0f43c0240c6858008101850500140c98145505a0090203950b0400c0950818410001c1c0c0850b04060740140b1010325030f030341c250780c801c0303071920814011410701e4a8500200705582da0b602503400e00c1555001e0150382c1c1e034004035610503003800fa5804108400403880e410001e125a518045103c1d1022850000301644402030504440c02110500359030f90700c40b05032940fa44983c0180f59400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 392664649 1250 392663399 392663477
    0x402031e091504171606061e080307121710030b18100b040b220f0204030309030b09070302090f18060105061e0c0303010f0f0905070f08090703120906 66
    0x14544c2076401c0c0307804500103690f801e00c0000e1040011412501c2011110b49031241010b001c000c0c1b042031815203040c0ca451400260a1411301440c1d241d2180f000b014103522140300d400c40900740140506220164440703401c9400e481e02414911401d19640801c0f902d01d00060041022140610b038059114448440604440b01d24910b8420040400c1e4031a69006601d07140359052030b03540e100b02103401b0301030a617080031071a2801c074502e41241c020704880e2001910510062011030360210344041520b031312020407401910b035901101c0c584400703640001d40c0180c400040010f0a05440b0005009030150214007400108400300c1e40d8840009004294120909000b104c40002c11030b070103804a4107140050a28000c80ca210322415940242c1102005803840702040110a5241050a0007014501e00400c114202a078004190820000308030040106d07050109400340400d0202c003000310780c0aa0000f60001c081403000d4080312181c032520020480e06400a41e40e80408403a040b189aa421546082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 392665899 1250 392664649 392664653
    0xb010e010f020a05100b03010e0106150c030302090a121a0403020c0d060f0f0903020f0309060a030504050c040608060a0e070317070c12060911010c0213050a0b0402031e091504 77
    0x700040c1d9403146801c610562100c0c4000c168180044140400840c00209030f90307803000305060075690115144a0247c0c0b41c84020415006000c040c3c040c000c907149054070441c021820114007a0191408403070b4040e50700d4034005002c15401c032280c0d1090b840390126850310b8000d502e81402c1080c1c101e4026000d0b0700160308201d400c0c60070010410942c1c0c4941000a0040b00200385101180c0600c0d0a40c444140d0700d8528000341901044a616800c14810007103150100c0f42c0f010034036034052480ca0505241d1a800801d041200600100d00c04120140040044503074550245a4401d400e0300c0840c40940351001c010a214400300d0700406030390300410f0305464107101c007039604801d500c810410380b291600c2400118803c048500302240283c064040030984001c030382130130b0680c079034010201414050800031120040c0c40d000208840134442210008079991505100390107800f01c0100303990310510000820000428000021000142c00e68401045a8032108140da03103148012070115891108000200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 392667149 1250 392665899 392665907
    0xc05120606030a23100524182d030c030604230d050706050f0123040e2401080a170706090b090a031202031003170f07140c03010b010e01 60
    0x60080b441100000d001c84c030b80500985448600c16144580030320120511206000510410014140481d080047e481c00084059100e0504008810b0440000f2849070306404240c0d81711040100003405902d0065480114021016940058260204440400180e16040c00501c580c54904090004c0c45c49495944500280c07404202d007151200b0715081444400702c009100d00001c036452a00c81a80310f40c0180740c81e8041d290001d0040700c24800e0078004020101615200b542a50244204980d4002c00705020601405554100000301d00c20a040010030302c0079070807207441202030b020104525907220605507440e42c031003074406840412040f1950600419072401454004c0c4264000100d44000356280d803600ca03412600880701d0f4200b28904c005040d003003400700e6a02e14625100318554505000a40011805030001500311540e00c0650030001005c00200c031803c0c0072003131045458010600d0200f22016410010b44114007840900203402d04050103a8090000143c40700d00d002410403004407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 392668399 1250 392667149 392667151
    0x6080c010e0409120503310b0a150807051201050c03060603130c2d0803030112080405060c03130603053114030c12091318050d020309040c0512060603 66
    0x10340c020343d0341e00c0310000981d40341c500e03070260907003600c0321601c0740f4002c0120f0307130140c96043e0401d40c407400300320340a580243c510902417503003903010302c41c0030160303e51001c8500106114015000c10300c3d074100003c61040800503e00b421203100b00d501c03114862000503007030700740c50782610151030540050010402c2480c0074001b941d4062102c0c0201c03d603514045d1a410120100c0358050b11440c1514142c4400248042068040e004403e0310003901061901010303960301d210522604148031290301d0f10f00104030601041f40c3c000d14000740201d440d541600310705501ca0b801141b05c030b05050800c50300007c115020b0700501d403240320b0742104806244d41001e904071502c00200168140e1045501291000603108045000c43c40c4000c0010f684901c0041c110f81d103041d5246500c8428240280701050786a500c02028200e05c0101e080c0c041600382890f040700c2d42643c90540010143c0c001d00c1000300003260b0000141025440441e801d0245688001054900c0e01c50000004608103e45c0c00041d500d0a1040c021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 392669649 1250 392668399 392668427
    0x60201110412140312040b0618010501030b0a1a2109030403030c02040f050a060302150705060c0a11032d0708070f03050d0f0203010e060913031b0210020c01110106080c01 75
    0x8010f121900e03180e07801c40c1e10480d00b40c42110264814031061081081d49260f01410585000c1003051000401081d00141440b40d103041517158909a029600c2e5030400800518851981030642d211040c4040b2454205a540d42030300790b40b81e400e0004c0c500c07107464624021a0711601551505082d034030300b00c50b001c402c88400d98010743c41345002805034207035116852080f11405000194607046d84104600601c5a05441c1c02e031b0601401000c001c220045030b4107030011086101c01e603481031100c00c2a104078000001101c424080802c2041c20300c1d00242c1c4c46d40b50190010b404412040c41326182800368011202d01410745e800a2280900040c4c00700082552140603082c01800d1a600e044104241c0d0350003154400d62170380120042060b8580d000305280c00190460310400385280500c072141241114802c05420013101d000c0b020444803100f0421120a034014001c00760391a02508080d564074018010f460000d0032204290610800602c11300041d0f1b01c500e405405091020001120350003201c0c115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 392670899 1250 392669649 392669663
    0x601050a211b0c05010608030f0f0304110603180c0a030f0f0309081b04060503010506010e0d0311060a0c081b0a0f03021b070501081308030703050a09140c0a060201110412 75
    0x1115142d0044038900e00c00c0003605580d0b00404051520742142510b02070f07400012590300610034686507010120684040b1911412002d880740e907141041d01520000c800b64540080001040c48038075900b000401c0580d0002404640310b0041803028804800110b200152219407048040e000040202c001406010700918060700c1c02500d486025007814008445405551841c440a5843e030030329004110080900310700070011843c0c24030000c1e000d401581c1402d8071803514150b4520806009011800c2c4c034042c5101151010b103001d00d5400010840c01c0840c5003c60503a40000d00200b03001e40b8030100640480302c03c541841ca40c4001542d1220701c9480c040302f03054090000000c580d403108081d604a070400c6009005441c80c1030009814038001500a40c1c0300c0f085606420080703030390a011203800c41e00318038001525613180304200c0020b01507110020f03d00c1201c081c410f0300e9000c0008006540010864a00c3e680c90f039136040607801c03101a607a10078400d49040c4003c000e11201c00b050254083d0281407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 392672149 1250 392670899 392670911
    0x30305060f1e18011401050724023a02092101091a07052d03131e0b0609100e0717070e011d0111030a080a050601050a21 53
    0x100080100502d405511940c5800c02d180903868030389981120550702c1200003425041d41030001e130701005840190528103210b8009001c0040010440c0c0042d90019940910346912241c04083e401a60084078500254292107042e681d8814048200000514812200c80104086d900000019420840800354414040d1003201c1220307a4174240c080c405048040009104001d03072501c503202c144401224894a036042c020001710903001802c50b100308900354501c00001c099010707000b40c4101000280c841c1400080180081d000d01c0300c440b10000d07882500e07803040b012003200c14440300318003180e8043d096a06400c082001420401851504480700345868480d0303d45601c01940c00074400e880380cc1c00038220060b104400d6030340803d181d03000000d03803520742888035070000020300030b0b41849803c0d8681c00e10100602d0241c0c0c00b90662084110100c0b0a0303c0d00c903021164090b00c4020102d0721301c54100d082200142c56584204d00721680d042207511140c0c08c0d854945205901b0000c1c0c0c81408141d41d685030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 392673399 1250 392672149 392672179
    0x307020909070b16020a08070815040501151d0901050c0f070809030d11060c090d11010e0a09090b011d04080a020a021305010302120115210c0801060e1003030203040303030506 77
    0x2001002000c200c08003031413511407144103001421003a40d11106080e00080001e111607000455510a00000b0400641d0240c0321403e05074010500310038048000d03000500f00068104505403100790214010002100c07030b40c2e40024803030030707143d00b104c4015001804020542460101101038000240a400396600b4000500301180c41d1251501e40b1001003100100c3c555a92141089529441a41c2030241030034a0074a40100d000c2e01040d204c010080c1148001c1540035910400c64800d201d180140000c02840e40c07002e01c50010409400207480f4178800000104042544a8010718003a04002002045e036446880340c0415821075240141103005220b417038000359440070040c00c6009184880000d9552452041000421800f031a18041d07905080f40d5203e12900229a6070807100b02810030754070512101c100c40900e00340310398000c1080c42030600100720004154017480668540c03100159250300c076880780d40e900800030321000300141d204105c1400041e00c25000399410040151034160000c03484 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 392674649 1250 392673399 392673419
    0x206270f0312180a0503030412030e07090c03060b030c09010c0f17040e161e020a05060a0204060311040e011211100201050a0f0204052b12081b040503030702090907 72
    0xb40541c030707050680c0c0300709000b0000c0328a40c0a02d203002d10728000340034019103a0b540540300c0c00002c10280031040e030b01c030035041c402d0f0207a040042a074210006031101070361155140001031a41c0380122001a140030b00114a81e1200c3c42200e0260b40102500c900300b0750004011618014403030021284c101c040728078040000c00402031000f002628164054841381408000c0030f100c42c000307040d4400c1d49080204a1900d41d046056407003090428800204800c414101c20313840e00c291420000c0081c440e1038100306418070207034041c0056503070780ea17024001003060302d07256a140d0182c0d00a0101c0c2048900c0104810309044120050143c82201c807128440070307c400044000c03c402c4003140260351500f040020131001881140900f2210200841c01c103070920b0003056100101c94074004246036510081c020001d50030890340d8020303a100b41c40c140da07050240402003509509a4109882c2c0c00200c0b0b00f0240305450401751010784001800641c104080fa0b002c011440c0409801241d0a0090940124000c600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 392675899 1250 392674649 392674657
    0x1e0c0304060f080708041a060f0d0609020f0a0e0f151309230a060222031b082107020d0804080c180103030e12030d06170d0206270f03 59
    0x519110180726607102c03038003d80100001000301042103048803c01000403070422a8040800300000e00520320380e500d0001c640345042c0381c11a1544641030688107020030206804c9518818805d841103130585441d00284000c0c0c40c0c0500a540860081c03800040210b039111039201c0e8405d140d101c4440b81c4410800101c0d1120540d0458401c07115151176080041c05904212080c404080d410710700c000440782c45401c1e03165110b40398000c080c11380000754101c0e47c2958410302c54080452a00911266a80c0d14040b06140d079a280c4c0820891010640003030b4864002c900c10380e07688604202084880122040303040558410003049a1020b414025200802c4164020f40b0240079010000c3c002606180c080102c490a000500028540c01c80010310010b640100c100c161108140c07a80c80004e0041c3d50390318158041d41d900b0926071480c00400140052900a46c100203001001c06c2d611560f04400701240c4400d411100c4500040310042d0400100791300d1110f85040c14540c800f5610324100d001046c5040da84 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 392677149 1250 392675899 392675909
    0x617042108070305060a14060703020a1502040303020709051303030b060c1c110a020607080306060f120103060f020c070302060a0306080f0307110108040c0308030604020702060c0a03020c0a0b1e0c0304 88
    0x2040c6410814060f07050302c00c0e660040000ca8241041c20300c1c3c42c403000349a01201006a000700030201e04101014005c2001d00d10b155403103042c51040400c0d5400000081d0050b00c800c2d001481419400030340104035202d03047c01082c10f41044600b9402d01d071016030291149015070344e0402ca04001d004113040090002024101c04030007080c4511603100d000a0103c0002c003000800c0750400340000e00141c3c2c8940c00ca500349075108142c146c4907511000081c94501985283d5400f1540004842007550121804a4144d81c8074040c1084102c8000388c940b0120b02030100030300e0042d07104510a0025180c201c0103802d1402c0c0030300c0c02007001c03511000035600344028440458410ba10200c0e0300742c100000e810160000b0607003883e021010b8074258482c040180f03158840070303015450000125082d91155011110419005842286e903950010903090340d450038803c0603001030150814440326072400c030000c0820ed404440e0304504120181544201203c071501e096056458100100004003a00340040c1c00201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 392678399 1250 392677149 392677157
    0xc09051e01020105090c06070b0a060b0d0c08010b030609040b150618100c0b1609030204090b0a0e1b010e0d060e15010b19030f060803030a060306110406170421 70
    0x40c1044006402e544003d028041d0a80001e00d04c03103415180d4030f040e107840381d8100c100000c00c0d0719808030040041c402034010000c1c40b44001911508912150040c4a081080e6544c00669a81c0c0d445503141601095400341d034017010b8000460085551420426005407070704103440040003002d030000b02c0c0740e80460040c40c032186400e140c500300c40c036190f12000c03031100003030424800c21003d03a03032040001c000007440051031503450f00d894000144a421f419001d950b01401c1041003080c20304251145040807aa08070010741031243c01042e255000c0748410102c1100030381d5044683c425001515903000c0741c0c00c00c030f80120603100510040b40d00c0e40960300d0700d10a400d02424a0b00f00c3e21003800d4403030105802441c3c0451701004048000c0c20061460006100c0c40d240004225070140400405480c0d81d9200c10700c188000b0050080342c072507683c040c508403403284508001d03210914981d01c089008502ca40300c04a2a40409031012005603030005610034032136500c40100b2070384154940014030a03944550006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 392679649 1250 392678399 392678449
    0x112209020429030c040203061807020f100b31090813060804051c1d0301091b0807060207030210080c0f0a05120105090f0a110c06040f0203160b07060c0905 68
    0xb5040c10701014a038580159015440d42c54a20301041d0798003905080d200e4a4111072002401c42482440402c07051910142507500c0d884070118204050103078017406620500c1c8508103d1039401e030b0400e0b20502d01c4c11002101c4040c81114550400034844103d0a40720036600b080054110000c42c409100a4405500c840c629800c0a041544c42c0c1b090b0300004010080b0402980118030743c010040040110b501e008410300072a0280200c3d014008481d0020400d03003090098800c01e40c407018640054480ca2407c80701620380d1000100e903038082e06c0c03001039007011601c0b103003408407031140b141250301c03410182c00b46140218130002c02926500c08107080e000500003040016900e03110b802c03114010402180c00c00918282104900d622060180c1000b90081da07640040000d6800385042d01e2001e144141543c0c8107203040e00b04080036244540e41203200e4011301c0010030821244407014002e40d1030010500782004841d03030340c800c010a0b00c01d0b40301c0103000032030740005145d41c0c50358a40501142114025194 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 392680899 1250 392679649 392679731
    0x1012060b0c03070605060904050a020405070e060d050405060901060e06090606041a0405010801090c020d0804021c0b01030512030c0415090b0301031505070509030a02010c0c0b0301060c1122090204 86
    0xb159001b81c1924451440c80c028000030400004200d40c40c070784c0456002502e521380040c01d6a1449013080d009403c1540410501300ea401140d22181c8030300e0003881500d940341d440014050072901eaa0060301540c0c640303400440d0083c10000b40c0d0b15486030f0050011840e141d00c4604045810740b008000d02c0c5c03162800101400300d5644030070040d00400c4030241c240962018410007a40304c0c04500620b40411504000080940d80e541501c83c0c62070081a2a14003010124105511841030901065426202341400721300300e04401d4080307900c5400030102150910b81004c040416030440d03100c6490070002d0002000c901420745400a6000f9441003a200a40601c841c0c94201500c000a2407882480301c14450140c0c40c1d200481e43c440c01c9942480d00564201d554074008039500740c0c81d003080310480350110004c208541c01154a02c0c2c001e000300300408441c21100100108650705100010940e01d070202500c151004a40203c1c50b0741d0b20080c0007203501d0f49485032125100403d404640f003175406020316510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 392682149 1250 392680899 392680901
    0x15030117010c0c0305070305090d08190311040609051c0b0a0b040e010c05090402130905070c140f0706111c120c09120b0402120609031e091012060b0c030706 69
    0x808012030f0a200400464584016007140595000034042c0400041c0d100056a1804455508a40d0180c00561110b0016030030041d9074644400300f40101b4070341751f89445c03088030400035903040750a941e56056206003050f0501082c00c0f10b107030b800c1c4115010406000000b45030403d032980f1404420340c0004607152400104410768141080c540c40692428048401059001044418003141907402582e10000400003030704d500401d038003a61a0601d405c040c8003290341d000520400460140c0d0850301081440c00c3d0b0141c0380e0250202101c450380c40b00804104050060700d4414800300c100040e03170340d107a002403043e0b0560300017004005d000800b00800c030440e0020b50703c160450541e0524000c0300e82801c200d0141c080d143c0c08000940810203160014084ad80c0d25505140141d00d1720060320f0282c24508642596900003003440c40309040c1c0d14109128088003103055032540c9100030b01001e00741c0c00e0004161001704d0405640c00b48903807650004180074141c000280b80105e03900e03000315a07402030750800c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 392683399 1250 392682149 392682161
    0x15020a0e090c0a080114031e0a060b060a05030109090606091d0607020102040e0c1b0d1106070c0503161b0f090e010b2115040b04050618070e061503011701 68
    0x4040302c0c0050001c10039440c0d003c410a030541d01d824808030720692104002901d40780d844070084820518103540c03503c920202041043c0e880f0320489003404941c5070b9004110b41030140d081d0030302c0014014401040640f200b900800e8180e401180f000031420380703031207049094903007241c07401e510103140b10030400186604100255000300c59100842c10942007405034030100d0806049548254030120344d0300c920b0940208250100c08075401260031f4030035580400f4004500c4d09079032885c140102c00006200038020018108969441009540382848a400c1760b40c10005200c5c098469030000740032a540b4403070301820340b4040c0c141c0c010f05d4032843d46001488130556090760782001040c3d042c402140308a403120400040c0f0313807901d0380000400e1150210001c0c9404403401e4003802c5142c0f45418041031104030101e444c012801801a0380b05030740c84103090004c541c2d01e01c81c26842644601003c12a05510340a195007114000b400460010000304031b0b6107098000303030000c17000001400d100c0043e888091250b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 392684649 1250 392683399 392683411
    0x70201030642021207061b09060905100813140d1706030c030309100201020d090606030302010b0405241224091203010e090a021009051908120715020a0e09 68
    0x440c0290002c020740324000c001c12045440000b154a10402149801c59022004020003c16070000f0030180103000fa4013a11409000c0340340180302060303504012001c00d05003921515442ca0325200c03050010b560741c003150b1040d110b0002102d4201400e44041c00440401c0019a0300c1c41d10500100c007880b1100c20010701010b2099000a00d40c80c81520044142c1c0c0001104540400c0304409440c01030780640308600c40d090106103003000f20350030480b1540c812400e50b40a90300030420601904d090004079041903c14a0984620b024940e029508500c4040400040500b495801d0700100e00c9061400582c880e0606401c4c8103075409401e801c080640240d40209030302d0080450b0302d80800000011f1006014214940003082d0020b40c40100030401911301c00e41c06003c0408212103500014000480e074003482e8801d01e008240140075004002d211030545543e070019150440140c641882107034081d41c000c881948000140c0e40f0207595520182108401a80b01c04c90340c0d820040400980c00c00040c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 392685899 1250 392684649 392684759
    0xa0908010608060105011404031205120106030506091518010b09030f12070308180d020f0c010c0c12020d0803010f0f0b0c0d03050405030f04060509040c020f0a0303020702010306 78
    0x4000720100003c2d010b044a400f0300b0928880440190695036038030807030304003800e03600313010305c070700d00c03215401001000f05400000f113868050340c0300d036411002d82e00d05a41c041d41c061014008a900201c0d41c031010391040c0d400801e11990f030090030740d500c44046026440030703803c8000402c0a41507814140300b140407030350548024203164440501058018002d00c20003408200b0b680000541a100340c0c40190b04404036901241c01d5803001c040000d540c0c0c0140740b00c849003030043e0041d5801c594040c1e811006016404040c10503030505103241c2d0070010349000c0050364061101401d07940400c404c00001e43c0030b0654000c229060a003456100c12400c20a64414043c0d1103080056640d45880407406034201c080500d4040350a0321582421482c4d4080d9500a480c8500002030019443d030700035000b00700c42d90043c4e134180301344400d88800781d031910b038030440090b43d41d0004c0000400003486540207008091050600041e000e4585144401c1035408111101048280d92030407a00c2c840c0780c039494010038a0030701d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 392687149 1250 392685899 392685911
    0x309020102070e0604060b041707050f0f0111030d020712080603030307050d0e071e03060b190324060b070209060d020a0b250506070f050c030f090102210a090801 71
    0x80001d40c0c2e06058411542c00c540760304007040c0c03256502e40040c401403090b40541074440b030b1200c85912000103204e8440c1000e00c5440c200040c182040700010604140082240101c034807071308010354a0450000c000c3c2c4141c0400c0150401c4011030703202414800d4000c05141d181c0f8550110040c100205c0544020311a41c42881044441523018080707034040c0c05c95050124851030001c0f0001d25202d5585c008000c0c20340c41f40302c4030700000194001b640480380200c070144a5901607030103000d220a411800814407880c3d82c0014030100c1c0700710851110403020001510900e00c2444071640860b0100d030403d48103000b00080c00c82c194500401c0064005200b21a2000406950380c0081c2d40c43d58140325224003100c0120f102c1c0c0c2c2559580c00b2008a000c8460a0f0340d80b9400245013440c0c80f61800c07180c55000c0381d100010000e0340e91055064890780b0680a004520341a000341e0188425044003450b04d0452090012440313542c04450003204104a49510481e02d54444190181030501160445401341c1c0c50701c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 392688399 1250 392687149 392687153
    0x50303060117010803090f0f1323010510200f01050a0507020606030a03080a060308130312020319031a0402130512121903060b07050a02040c050c0a0b0a020408190c060309 75
    0x3004031349001b4412240e5600309200310012440742c0341040c0c000c070340c4021040c44500f2412500e402181e007807500b40c84020044002070a40541c402400e0046d42d410000607642c01c2c21503806103541d5400c40720740a50780c8200454010000703240c00050311110400d65150024021040c04a0007442e4124925002410103450500c0101f035882a00200150422080320f01191600c090b540c040700203103400081e569501d40810b4400c0c0c60000d581c0c4012074820b407892500c0034a480c03010080d205506025100d0000000e42e03503400324007800c0c0c0c641c120500c0800c1201140e009940c1e40c0300400c141150020300759201843c141c204000b100c1401c0c0d10490b070760810000031901c06944011942e850311902e49010450044680840c014490b079000440b00e2400010714100703100e000500381076094400c607030a01c042c201c07210040307441c2c1c040c41e5030070401d40d88200e42c50300c001050700c41f08607400154030800608150341d9041032841c00c0c21480d1203a4489140c55031103018888105d070b8600c05080c140c01c041c01034003080d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 392689649 1250 392688399 392688403
    0x7020d1104180f1203020d0213030b0f100306090507150210052203210905070f0b040311010c1109010915120819050f271f27030503030601170108 64
    0x1400000c0010400203207085503203002c0e506a414400d1f114008544070401d000e29030789945202e01050b1054890341c0c001070500707002001032a00c50301410b400030761007515569a900107040c2d900422075440c080c03060081255021207080041c0c40801c0c0e4000c0070048824031070801181c9029203500b5480c2c0300c2e441f03078001003840110782c16159940341c0f4003102d035019140d040410300320742c02c0d444100e11802c0405030b00030b00000144040a4542c805820310246035103100341d145500ca1031100619101b49907030a0041507000d521500200ea000d03040c10b5aa400d15800001d0042c04240c00002540f035071215034540f0400e1105110000c1e01e40d400340200d0740b1f030850302c56000a000700c2c109440345e4140090001a40c51007001942c01c000c5480303190702e840c1e0b5400100c4040c655000c2d800251481b00380c0540500518000442d4901c2c0d070a4489150a140740750b0200f100d0074405074520f04c4182261454110301000007910309001140914003950701c0e42031103c0010458003904180000c0c011184006000040340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 392690899 1250 392689649 392689673
    0x24050702120c0c09040308070f03060f0b093c221e060305010209090c16020609060c0a0501061d01030b0708040c1707170102070308190207020d110418 66
    0x241c22042c1c1c840c0e5800140c0382c40c00c1580542c0a4025414070305100c209a0000c401d1405440703140c035000c508030318480080301280c00c030f4800c000d40b18070000e40811140c1c1a01c002459030160103001d1941345413400c2c0c042c0d090302e503803142c0c0a400450100c80d103024040081c00d150602c40d2048440c036034440100003100080920800d05801941d42d0f0301c0465040782c1170440785941c03a07010707040107000855890400038002c1d00000ea015004444150006074030400910448252340c0348105655a03180c181d80034001180c0246100300d030000d10401c20618060010840804464420700000c02c055040908804400c1c003400e942800e41000140148002900c0702d0240d0340c00300701c03450140040e64881c100050041956032050148510752100500e00780ca0205818041d254444101190340101030318003801c0344030300c1c0c2d00a40010019004226010021030f10f440b1543c8c8031501c013505041c01d940001e023404142c10000c65a007c843d08101d007050402c0d020780c0743c01d0010a040301030030160940311151882c017 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 392692149 1250 392690899 392690923
    0x411100512091c020a021302181903060506060901081f0f0f140d020a150c0803070f0e030303090c090618130606091406090a0e0607050705011506020a080a1b24050702 73
    0x500403c4a41e2701c1c101c1445d072440c5058004000003086441c0411012008185000a88615080c1380010b107540c207200088a5900c001a500d200c1d9071385c1d880c1c020401c1e608040d02c0341100c40e81e803080d00092804007280903034041d0420b04109415185064643c45041400200071800b4800d9002600c01582e00c0c180410102c440d200318101c0c0c6103490090484092000090003032140c04080288a02c0651041c48071084200c0d984032082c07240e031360001305a624082101d00340c030990b00c4041c2903015814071035a91a082000a0900e074030708a1140459017868a046401c07524208925481105020190041034014211150200440619088141101c03440180414000d042c290003140c40103c0c0d0354071400d111041c0c0400c0d01c080d070400b02d1006080d070740007071010303034480d801d003800b00c0da06080b10500c0344100c031601c1c0c00500c1180103e69990629030800303014941071100094018291002c1c00c0d859801040c4259140049001400f68140c40d0304d10b6076001c032182e1807400b0f08020b005600000c10f110110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 392693399 1250 392692149 392692151
    0x706020a0b0405011812031a130c0c05010207210c0b0720060103030302091e1f1e030204150806011d0d0c0311010905090411100512091c020a0213 64
    0x1680701e04145001d441c44114544100b045003250000f8881c100781c0b01c1d006c3c10250b540a11182090120503554003441807102640020850800764480b8013980c40580600c4490031b000444102648880e82285c1100d10195440412682c50a90102405039400c111034041c1c2046003208440d0f85941e154248014181000e0000c00350040c40c5400e2050072420000c0034100c1200c02540e16171600401035040061001e008500d4000c0d800500b10130070743d040d4000b01001e8420202d0031400061042a02d88024071441030000249100c48100d06080a014940c503840c0c4015a41e9031528071044140d080c415005810084c112081c085242c0e40440da5944424008030040307900d501480010304000c0c0e00c8000200302040140000080110000c61215080400d8031600207042d90f44c001e00080010442c1e00400c54281014240c0031882d241c041c1240e060715516045041c2424000200d0040e0070a85044890303621441c60544200102c0d003030f00035a00c0d55803026050a00381640860075031119454138074185 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 392694649 1250 392693399 392693401
    0x90705030f1003050d0903031b020303070f0222060513110d05041407062c0a090f02070f080d11040f0b0903031e0705070504020304030e040b030f2d0706020a0b 70
    0x1c51242c10010010315000303401e440c600028210003070304803101d82c8401c6000c110300e00880d10b02e8003e041440074034940c0141c051860081c2d144c0e06d1090300c070b41c2c1c20000c81c8d00980c60744505c0c80310a030900282c0501380802d80001019030610040003180c2c6a4944142819418821000036003841e040075a407585a42030b20100c0c0917292842c05442c1c5d14801c0c0d07a815054801c1e075200140e115404140010098400318000d07114024081e040c103182c0c803015251640148561a04100440280c2c3c00384111088a200040c00d01c2e03c1ca681d100b509a004130000d81d6441004140c2000442043c85260031054405d02103620300b07445c04e180c0f18880f5400740305547c0c5030728000c614000280c5081c0101c9840c2000c61401e20400090084103507002e0b0425007007600c42d03114000c00490181050710840703000342d400d170f03c1c0c48090600010400000d0032071088620f07014050440c00011942d002c120303d080c0e00d9242d03254a43e070311200c510702c160388060050000405612032902005026008187c040350184c0040b100b51003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 392695899 1250 392694649 392694661
    0xc010c0f0f0b1014030c031903122903010605010f0e01021002030f19020702010c02130212090607020c03120405090c1e12070201020306180910111206090705030f 71
    0x1951503880082c0c0320102c2007081000c580c1c04030305a04142c44201d41040541e9028000b07040e030b00c0d050440030b2501680401c00c01c01c180b00200b02e178210250f1180c40c00a0354640005240019a042408148003100e0600305800800c070922506880c50f9005500800001e80740500081c00440c949551405012441c4681611079209009081c01080302410641d0f403801c01a01440d03030940304a440701d84040c0071060140d1004498001c84a500340c0507541c4401600043e02088115000506044a10b583c200005450102c06030039040c85456940f0140c1510b03c0c0041c2c0103400e22403200c009034826005255408429400c1c01c00740c50035a802036071104516503914900c0c3e045031203024451071441481c82030600d01e06c1800070007805915101160501c103134540d48401e07800c0c0c1c00107a071010741c84115208400303007070448802d00f15488409441201c42203c140b66031402250f40e141082859104001400288040100085900082d0640700041c82d4540090300901da8000600700100301c174004804648 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 392697149 1250 392695899 392695913
    0x90108011212110a0b10212f0d030801061206030c0b030606130b0319050c180f19150f050f0d06031401150801021306051e07140f0c010c0f 61
    0x7405034000b517051224205100c9031032040c511031243d1700c1000740e5080d102e00342c6e884802411443c0c40e0320064045000074421030040000c0207008003101d411000f80e0003400b1f036980f080c600e00d844901035184c0320410350500034001d0078004100a07034145107040c90700402c001280d81c0c03404012100c0e051a81500c03900c0d00800203a292003900c48507003209402841c04500e0031070b040e00450085103001e0080c60f00b01081e440c11025550201c1d049c20700d01d1014010440800c4840303007144980030000b0210201400014006107500041480800c15100c2c0c0e40003c1c8007005241515000d0710003c0d04101200701500140108144104000342410346008603d80707102c00542e8100d04042c540c0040b0090340580104009030003032242403101645e00d42200f0b00003c50850610807202036103111034100484a08000b0f003a00c1c2d81c1c0c89603003540303140d0101143c90784400340e40c40050250148100c101c1d010b044003004107545488158030180360b20381c001d40001d2800740c0c2c0028504640d507a10801d020002c0c016030034890 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 392698399 1250 392697149 392697163
    0x2505030d1407080a020f1e130b0a260106050a11100606030e031206150d09080901030b0406050109121406012909011209060207060504140f070b032e090209010801121211 74
    0x5100314403481e408038014180c0300291200c034803140e0741d0061900300cbd162030401070301d8192100c02015840800502c04a8030900c001e124002081c10501d0449000f000000c1c07909000b41c40070700499507541c40c1884119418003645c0b244511210056041522010303218001a00280c03810348174071000a029120f4450324800e0354010002e902c010031071a8114141030301a94820f0449600091400001003017030724282c4264000e44030107035224061507040c8089075140c1d510041040c1e80c40c400b003c141460310344003000744501034455601501d912600004100d4060041642d9078002c0e80f400380103007110390341c0c01510320344140d090b00004265030645d030902d03000034880d94501400383c0341428204000d00c0100c68043e074100404038202e84540040d400380d107842d01514003a50042e0041000403130035240500c0b81864810710550b00014042e415840c0100d580b1045d03034061800140c010940c0a9950f070400710860040c0070500d540640503060307686d60461813111035540002e0201c10f1480300c0140b1400c210351 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 392699649 1250 392698399 392698417
    0x7110111070b07030f09050402130b0306040605090c040f150f0302160f0f050c03210901091206050a0b040209031c09091d060a022505030d1407080a020f1e 68
    0x10b181c0ea103d41e030034000d048411104e01203002c2141d00d0000101810148221150441c07500c3c0001c4046003081e0001b00d00f50700152880e031703000340c940b0700210320350750b6071442c2500903440341040c69500d6107045000c0100904642c0300c0c081e05076000c490701c2003094000865441101c103038034005076a4800e990401503102c00e40c02001d803616050726101c808000406074201d01050042c421034400315400f2003015661804540e101e0103508080d41004000c080c100064595440141460210344c0c1e2240e1840a01105100003500c0080c0c0b108107010040c4550f1054079200d550982c0c00358540000040481d580700c40c41841440003940c4d14520405161049490b2006000420000c0c80701c24070640800c081c9021040604038640140c1b0302284032800e680c400c81e02c118140d07010768620740c921344180c48481440b1070010f580c10301042045c01c1001d0503a114490b1612105030b00c01c02c4905081c000240601030082084031524030400c0450303081a000c405440c1c1190189101401041003060520480d00804041c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 392700899 1250 392699649 392699669
    0x16120807080d050916081b06040302041e0b030c010516150f0902032503020909070e0a1d070609090b15040306050405120f04090504030c02030706080702120711011107 73
    0x10040303640c0681c00440c0130b0b0f40c400040b18150b002c00c00740040318001320b20516800d5070103500d4100306a4500e81001d40220703c010501401d0960b00e40205040e01c0044da4a2004d00d064000280c00b002c600d4814180c102000350010301c0d103170302e10748000b800a00c80d0080d01c01c10250602d100c0005c00a4100c804111300d404614180000c040c0c202405014142c0f010017284a805100c0603b485905100f9810000400c9440519140d500d9070302400503111000d00402d5103402039080104d00440005d1046001d16039150b0000340c0c02d000400da0340360041c2d29084000d00d40d040400b040002e07030f601202450540e140c000780051941c10041c00200c0340386d50146420303800600440c00009109540c0d200500c1240120190b99181c140b401d048881d03032250051a014049045c4803c1c030402015034415a071142c0702c2d007055001d105141e00024038286180d032101d00018a90320400212580c188200d20100611104081c2050402da903008503059402002c18104a01603285000713140042200400825800741 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 392702149 1250 392700899 392700907
    0x100803120402040504111008062b11030a0b010b040e01090b370305010507030c0f050a121e0e0d020c0105180303220501080105010c02010c060504021f08010905091612080708 76
    0x50140841d0030444146100b0000f41c80f50311070a8a4070090741c01070070010107042081072b032159a0140088014040d1581521959040500280729440301c2800303800443c44043e1900d02d8610740c02850032050b00003403146801c2c0b0901103120b4a8040300303103c181400c1d1050b040c030140e0088100c40d0765031b100e01c5441291790104500200344981035000074001c442c207076000d0144c12080c210584908900108090005000308002d01c09640704290701d03864256100c0001c903a040c25094951b204025104207841c2003913480f42521041030381001036003200c13046070003c2d0040c001c4150028045e40a000120031450840140d6090240e80910482e0300004500a200d5031081000d900c005420f942400b9070750100380ba50001140b950b00402c41780c0d078000c3c1c0c141d4808290243c141c4e40c0300040c0c076014100300d07081400c49154800d00605283d080c51b04480700d5507081c81643c50020340d001a614050044d00e042c2e0041405041c1107040034070902c040d25011200308484074810b1070b15400ca445a000041d0003a00080303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 392703399 1250 392702149 392702179
    0xf111611150c06010e040503030c0304260a0806042f09100f02010b01230a121109030105014703100611071401030b040609020a03020310080312040204050411 69
    0x240a080301012070400c0303c0c5143c1c1c0392154812480016113000d441d56105000107a80807003800005c40c0c2c814460501c014492002c1d46203400c4140345c1c003900500c51000460303c140c406a0182c2e0050f40036900300d800748100440003400d641c00710300341200c280c03000f84112613400d500700502007111449000540911444421341c4801019120308900c8000154201040b68810f90311500191014602e04182c40c403124140420412441e80044da8483c01e00c44a2602d100010000307100c2d50a503d881e04080c00d03500c0070100c0415086841c140c1096110740c5814148401002c03580c004a451030910b10f40300e4004142200410790b00b0515014407508402001017001300072006420300c002140c1d180d88480306402c0c42c0c0713140380d515124a406001850002142e01340403542c4603401641808201810002c1e80645030014001641c2c07002d41808003080d000018049116010145680209070b804040c50071f040058a0f041c600703510140c8068030443d01c4001081c2807120545109804c10300085c94152003201117 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 392704649 1250 392703399 392703439
    0x80f100e011202030120090a08070b0a030923010c0909060f0e1f0305070905090c0d0b1b07050708061f0302010e13140718050d02060a1103030a0504060f111611 70
    0x1041c18a402004801030009182780c0015080c016510720441c02414201242e4084008100402c0184d0390356902950104900114070100e1559841450000c02e00300a40274001e4030321381260744040801031421404001c1803d14600300b406a90354000807501c00d0720388896660b0348216000085440840c00d50000041240000d0400220350012000b4000d555581120341d0301c1b20040501c04c0e40108034441c159001035242c10300d00e0342c4400d5480d44000704103101d4409101300e0700031813011103a40d8003902c410710940e0800c1182e25441280203031000006100c4000d4241840d03c6840024144600b040c07a40c0d01c41c0c3d890540c50020359100d007004114060b0000c10b1000c003540291001c80104004255620010022080075402c0c5c07100980701038202c5803164244022a80a0000302c02000507904003079602c00d4082c0021802080240f101043e542813505285c8200c030700c00014021450325081d070070300101c0a40c0040e505070250720003902c0f41080450500750740d01c405580600da44400441002c1141c0401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 392705899 1250 392704649 392704657
    0x601120b010506091309140a0803060a0503060610030203090a120e010f0e060a0503090307050631210c0b0c120606160210020c030d080f100e011202030120 68
    0x141060500d1666114103000c45031040e41885504426001e081d44444021a0803800d03045200d1003c280b010909262680d0604500030f0084513003880000c284441c2d0300d400940c04002d000c0071070190280d0b0a000002803407a507000750008040c1500440040c40c4144d007405100e207090381000c80c24601c407800c048000c1148a084100c0c074007254030400c01d40c08207403041c48061800780018001a01c3e1010314501540c0a07040141141800d11003044800000b44061222500540b034411500d08090800902c550b8680325082040c0412058070058002240003010800b17404120003001d803440003070500301103030307040c0082101410082c40303582482a6a0741e0303c802032401004040980040307071544010000c691181701d1400031800701a070b81410141c98042401190708105004481801e80007001081c00d005101080e035021415000405c14500325a00460340e02c141c540c10318429039418140d201303654001c18060590081d0040e54624110b45003540088100e1303e081043c001c8800e03900c0842140d81e40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 392707149 1250 392705899 392705903
    0xc0815010905130201050405060f04090603050115090506031b1207240201020c121c05040c031e0b0c0a11060f01090605010507080d0209040603021c0606080a05030405060f0408060112 80
    0x31600001454202c0c1c40311030b0514444d8140d694920340b40c60002044040c0e0040c0e150176030030310000c20000800ba80a0310944004501c21030001c1050089804030003150900366108090b007905204c00c202c500da1300469820500307003604156200440d00711001c2200700003d20542a4284a055404502030300c80c48400fa07050015815195442e110700b100c200e00340e004500150302143e01070005075894101107400f5003624804441c0701155009040300001c10713103209542c00d032010140600c0500910803900d000c0140c500103521505420f01a50340c0b10244280020a01144a040411800c0c41c00b8441d070a00c000342036a601c00c554603818004140908a41e081c41581b401e503282050005a0394014426155015080301e14203007050605066540a5030201110a074019690000440140d40d90804014228440384400160040b2442e1007000c4440c1500f00c10500c0d80070a01c03120000e94000102d5080da0400d5030700a4132290342c071070500c081d030045400c13141ca0747c0906400810044104214188128 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 392708399 1250 392707149 392707151
    0x4051e030c0303070317060d0c0303031413020609010f0e0a0801050f071115090a020a09050703050606090f010c020f09010312022b0e010207212303070f0c08150109 72
    0xd81e40001c041c0d49105140004011845004200c0c840611101040b40d0050b005003071410605520356a4800c8400160070840219a80e000c6602442034807515603a030050804d07440130900344182e000031b01715008580049042040881e0500161817064944106810000d0146018180c841d41942e000c0c241c00c85860a450b0494000250480c0c424440d02c0388004003800980f101c991410140c8901400c01404451a84500e044a40c0180c4034070b9140d000030000308600250714200040000c042d240050025407080c1001c2c0f040404903510000c5e070038107600f004d083c4240302c000c89101040820603009011603002d201600000280320f624403007640110340503400d80fa24003144042d240000401100342141c905080d03000088524080c0d1480c00004c48140115858a40e40c1c00201520107a503142c014090b1803d00300350410842aa28588510210340c099001d08040f2407480907540d025049000d0540c4a9400441c420301c03070815000c0001c0d284910995088220480e65600039120078405c1000c41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 392709649 1250 392708399 392708413
    0xc1515040b0910031b0305030d1e06060504060e1804050a030f020a120c0201050706050106030f0f050105060304030c0f080406020c0a0801050f010308030a111902010501050904080d1104051e03 84
    0x1d440c0410441d4031036070820f03d0701c0100c14115140d4480c0303650680101c000045c05e411010001c14800c00c0903001046a542c000301d0010001d03021100300c0c0c210004890542420408184010f0342c02409860550302c041c03502e2466442d2401c00961120201e211019590785080180014000040761001c090703406501e0310900c02c0400501242c1e18055290082e000c000c21203501c040e101e01c2102c68280c541e005140c420304228050f03d69400701c1d582070303001a01007551102e044d00045a0360141c0d9190050025080115624200c04184540b1000b04010100050342c42c120040148419540c00e0403a00f00718074540b80c0380c07501c40195844050124540c855030f4401c20004001d1030501a0500c12444d9550f100300d56443c1d591525030380c0d04090301c000e40c0c09464913514114183c448000d001050014441000c0500b049440a821039006820050190702d00314108404180400102c80000300c21407000204058508903c000e180036513041164001c02c0c58410544415503607491031383c0e100c800c070240c0e545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 392710899 1250 392709649 392709671
    0x20301051017061c02030316021309170c03070804030b100b0304110d02012c180702070b09040603150207051e0d0320040308040e06030714060c151504 66
    0x81c50207801108072641c0308100001c10344e08050201250340f00390000401588149a8002800c540240c0c041003c40c030010079140056142201c283c00c044015080c1c1000a0741a0b612034040441354440780858854000540001e01c00c0200200d6002a8028804c1030f1aaa120300d0280c140d40c0d41038440c480104100003001c0b40210300b00041720f001326801055011015104c03018000c0041e8002001e078103002e52074403a0741d0503600300c5040340d00030401d0643d603401071840d0404214007400744105c3c01804000c00c0b0204104160002500000d0366140060142c0b15400c0310300142c0a440c5540004143e1400d41e000020424078035005084058814000da480c49218030142c9142100404401203166211047c01040c00b40a5030140c1524410380004925a00d520344905040d580f2a9000b160040e800180800046e0100c031070321500300320704a01800303071140782c0005466030855918a241c0708910005014520000400009588098040d071002c4546485028070081210307100e8854012400c0840d4902 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 392712149 1250 392710899 392710907
    0x1b0e0109020a05090f0a050a0603090515060a0605070f120302040305012d090204060302060a020a05070f0e04031d12010c02240a0b0604030605040c05040c0c0f1b17010203010510 78
    0x8440c09072682c3e00d9040920000422402046060899070050205403000c90305469020140e005030005403808500800107140003460101c0c2d01e030b00441251003040602055540d9500244129101494550f0700e55000f401d2640e41c02c06030388001130411000a0941407866019005002102d000d58000c2240034807038040030a50410100000315440c1d150603a40000000c290701015004d8005800081e880380c481e40071070303040d5000c21384c41d80c00344e4404030402c802c000f01044440c01425140b001d4001c003610313005001015140180000b014000350100307200e000c00028170b214202e034100400003444030703480034180c0b802420070200c1400140102c030441441000d0f1100f440c81c603d607110306503140e59510300314010001c0c00622a0117a01c10020400000480c1450082da4000d50241048030f03829450482000300300d8030700030100018007a04e000c9a10119003400180c8030300981098000913001a201052520003056800528800542128111050005502540c1a540141c1e041030541c40d049109031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 392713399 1250 392712149 392712157
    0x5191503021c150e0a0213020403020a08031206041125030306080115230d0803090c0901180e010615031d0705130b030c1e010e091e0903071b0e010902 66
    0x41c00c3c0305040021408800c00c0360f4001010580b40d402600d860700041d900094000d914088048941a00842c1c10320035403a01800301c0c40100b41c410001c1d850104968607240f4405402800188100c0c4c1c0c4502c0c3d80c0c140c001e0041210b0f07a4140404140c440b50710710290311001d85098810a80000b86441d501040140341403282e4100c2c5170404600e8507100b49040c6405884181000c00345141034404802c500a5465010883c40c03a180b252043c19103030720740865030b90310380545429002e10071720f402c9004010942d00703c16480038010b413414011542000443ca07250142c50168003212041c0c0c0c2080e11384016541c150302070b80194581c400c030010343c2e140260460b550340f8000c0c040c542d88100307000c080a03008400c40c0e22010800102409075031001d10050001041d00e1082640060000d0541c0459100d0303603800110302c510603008884050036410009040250446449600c2c101c051001c808a501d045007001030f0344640d60f01090240040780072400780d4980d0a01c80c401d401018200718004652941140250303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 392714649 1250 392713399 392713403
    0x20d0902040f053903060307030813031e0201080c0706110d0902040f0c0206010b0d0b0a03060c02010c03090803010b07061d0309011b05060c0307030f0c050a0210020403110405191503021c 82
    0xc0d882d008202285904c0ca0b80c0080c20381030340b5218040d400000520214082d08100200380b40ea280c0840c5942400800748089240300001103000004040050b80c106003206e400080e5141d070a5220300c104d2a100004050f901c50540c5130f98004120301c0d448280700e410402d5402d10075a4144011080a21000f05a5850f412a0400b5801900c0180107000c1c0f000054411886040400f0074200030000100300c82c0c1c0055003055554544a40b8407210064090080c020400042e00d8100251801c64440402500040c01005e80001001843c10144400c07038014001d2049503035060001c400720380c9103e5589901210343c141c08100500440c1b000900c14200e65850a81c020001d030696076601075564a040d4801400321041c503555200c9583c104030540301340324a800345a1102551002a0800a8035040c1000024520140100011720001e801d5803180d02c0308480035100490583c541c190300001d6406003c110b103600b00c1c1b40032405440782418441e407000310f074000e9541140038903c420011944500301140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 392715899 1250 392714649 392714731
    0x304080307080403020a0f1a160c08090111120c0c01020601080a02060304172b0207030c060908220303081b030f0408090d05011a040209010909020d0902040f05 70
    0x1159030b0301682030150300c14420300c180c49050003a950781480341c40180700c0503503141400b01207207490f801840f20403e40251200100001402d0344000040c207034801c0100091103480e022070340c50b209901504401c801e1901c00000e83c0c2d04040440f06c01005a00140743c616132921518451070b2075135001040c0581640e0316400a0f00141d14140c00703011040e1310151084400c0700c40c00c018181900c3c0b51001400400c0030030001549040308014100c0c00785071801843d0680340d4410008040081d4202490112166110350045007140c01810a01d0403801000b241105803c80040306e40400014440c0b1001980d1090300c0d002d8980d102c11318a00715100315a01d002c03c130b0b1b45040021541804604008aa00900c180c1950386030140c004c01142d030300102d501e0100d03180c0c0e44501090002507030034000c90f203801505030780450805600c240000d000740d5030743c070800030a6540003540b41c0580d14613804c040c2c9401c3c0c0160060124440c0c2c00c01000c0100f000300c4100a11040020700b40508a03900042040c6182ca004d038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 392717149 1250 392715899 392715901
    0x405031e1306170702060c0720030f07031a060f0d0507090e072c0417090d0b09190b0c0f0d0606090f0b0415050918040507051503040803 60
    0x420310061208119030401000d4240702a04080051407115405000d55903a90000201104464014003030068090010342d0054070801194040c208280d40b00590850903110080010b20000d105805903480c2a40c0c040c0654030b055141481d0024421003200d116003008124003030101d0109501c7c2e44240d0384654080d180c041c2031041c510784181e40103085401103041c0c82e5982d603100d20b0641100c0c400d501403e0715421840f02000440103820141c8a2181c5091b4207200303142d05101001c003100301c01040101000c0c0d013500c00e0b61181303d101d004d60b140030b1000307884102c0f0380b44641070104000348212007445c058404e891080040c20f58a0300c001e000c00340d200410b1040c03a280d070b1200c882c0c5a08086c02e0940560018420300002110700d000705001030280303481e59210305003440110320140400fa041700c40720080030070080080844000a28180b002d4518126807034240e020f000440c041c0e0100c0c0c1b44010074603104248028044085904801c440c401c40f10101c80001030b118070a42400100c501a0940100380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 392718399 1250 392717149 392717167
    0x302060f09090109051b0c03190c08070c03120c0309060516060f091e030806040b0a05120606130603021f0309020d20040b240408010609020c070b03040503 68
    0x21025014440e111002981445925800300e603600301d09034414aa000c0e1580207120094203070146568404440b4840107180c0001c1e0741c0020b41d2445030508941500b0b00c440309001601c0d21420343c080b00c8651003c030050383c4042e6800c1c6500c0402a80c04291340080b454084125071900030003049001c180d0507101c0c01e6017140f0b4170000347e86980080d00e0051402040d5465400080c40900c60700c054040c001c0320000b543c03603460505440d010548910002e8400082c80c0c1a00406e0300300903d1903110030110b80116641104601140e016900c81d40700941058001038004100840400c900e4400e43e800c0e02c14001107850300f010324080e03650380e200103034020072010f000840c0400056003031001102c0360f06010901e8440b1754049004c2c0301010070151145011342d0109064a184580d100c0c88030101214184500c41c10400000c0c100c4600d02d40240e2031080035040c013040c2000c00f006880c010840c90000300201039039a07041c0c10183d031006040000e580900607011035020194829240501d4018005504066141d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 392719649 1250 392718399 392718409
    0xd20100c03020906040303120f15031101021914250b0903120a020604050705010e090604050603010e0d0e03060903070c05090a060305011104030311070303020303070e011107151404050102070302 85
    0x40119200700354081101010300d440391030050000350b1007561255591900c50440a04841c4046180c02425080000d0a04e800d2200740c80d81003a2038218a4a280e2000c0c8100182e250030b0515009180080c012403040e424000f017080300c1050082c0803800d56603081034000e84640c03800c004040381504070151003018014250300030060b00940e0300240441d640c981c500e4541ea6402e170804d955410040c0c1c0802e042000704041403005800074039080c200b08940000c101c00003807800384018001c90043d50b4a4000404c1a9400d412024410384001c09440d40e800d0109401032505104054407030081c031501d03011500c0c403580041180c0c0659000200c030700c40c0e0b50801d0104180d10f8030141c9028105903d50f180400894028891b40c1d103041040039100d0303940c0e491454040c211250050289400d60801081000440e0300841220350000141c0340030480c2444020040c2c84586407a90740d40311070702c500a8041405240d44080500141168484000c0d2414200313290304288078500a144c01600014010801400d203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 392720899 1250 392719649 392719661
    0x506130216050a0b071704020f01030e01230702150906070c0510020409060e16090308130905181603210c060509010b132f040f06020d2010 61
    0xc0e105000c05020182c0c540d1454181601000c1d80c91082003000d100e43d17150003541c1d60003c261710072001500c611b02030300002c00d04031290080e207061584490004551460030341c84a400c1d603080881c800c841d050b0481904910000854040c0c015120b038503070f004d000241d802c01503171140d440700c4000c21403541c03070801c11120000b900030100e03100d200e06000a5000b2160b800a000a44089800010b00c0c1d460b2414069500f10041d2400346034072005440b1b6402c45030701c010380b01c1c240c07074016201d60350320903402e03a0104902300c40758086081c042c6000280045201210035002d01000304000301c0f94802d402d0400d1100095140c0300081c642c080718941c0800c0b050301c881200b41b105415040540c8000c0d0140c44d01400d5172401c1b01c41031030595503040341140915000781c0d0f07003284000b614001c200c41c5501c0201038042d40b40045607985040076858040c420404204200c0e4060030381d401e080001582d80b004080e586520000c1c00c0c40200e00002e502c510948590480d040c420000a0001c00b816000083d404000f048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 392722149 1250 392720899 392720917
    0xa110d0f02030d032004050306040b09250f0501051912090618020306070f0e010c02060702040e0312010504021305010e030f0601060f030f02040e062704030509040f05061302 76
    0x100380282100581d0742441141840c640715100414141688a41101d064403440850500408140000d000e16100001c01035400796201c412158651615122903217840b10f008075054562580640024910602400240c1101d10100d42c0d03131403190700c0300c0065070203000382c412001c3c40c084940b20000704144a0003881038001c004100008040740e10340c580100b41c4901000c23240c400041c0c605448110b00301041019401030b058600034030440d00001c3d0041c070808104014a0401140701403410a40d40c6810480384500d50042040015004059180d40c4940161004010040c45070000040710305050084580c0d10410304603060000d0b0600c0c0041d205c2ca503036841c00b260188100e100404688004000080c00f030801511404660071384101e008058031403041c0352500ba640103010402c0000c01074100c081d0441c03002c5803281d4034020001f440071004d4500818030081441d04000340818142c0000003060140f106071000c0c401100f1541180c01a1341058aa050b005807080b08461401001d941c05046150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 392723399 1250 392722149 392722163
    0xa080a080307140d0605090f071b020a12031701060e090105090c0c0a0309080d02010204031703041401023007080f06120102040e2215020706020f0d0605010f020a110d 73
    0xc040b4140c4203400750410f04400b91350780e03a00d0500b0702661901600c40342d88000301d90305480c0145884803000b890000300c0398000301004440b800c040701310354030000d4880141010a84c0101007400908000b0070322081c511b071000c0c2047c0711000101c0c06510400000d40d07481400340004609901e01414402680d00041c24030010700401c1c003031095080011b02c2158000c900954441c4036103414810010700b81001c0803210070a42e84100800c0000034595004142c01000c01c6140c661255160706002c0b90445001c40c05c010b50394030002d140308040d0078580d61200307242141c1c03e40c080e00d82a450341046a2502c10342d030b400c1c0490004000070b0018024031944962101c80134003820004d90220301c0301426038110b030704a5500e10b48400200000101c0e2a0b504183c0d0b40105a0305120685464981c4050300c0c0282800081f401e40000ea04800c1c0a1990111400c8070401b1240c60354a0002280c61401071159000d446e0000b45031030142c131526031000a8200211341c0020031028801145c00030031000a9001904a03404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 392724649 1250 392723399 392723417
    0x1911010306150c060b041404020405060607080301030b15042715060b0315060702060d0b030a0c031104050a0608100e0109080a180e1501030507020a021002070807050a080a080307 78
    0x2c805800007452001503c1e583d45440b5a80740c40d1085d601240082e5008920705220f85040d030420380c2c4815005134060340c001031030351a0030002c1407007881015809001d141c0004000010407035407403e541c0c801c90108079425100d00701d132407c100907030b04181c030303907903455007607800030443e014400245891a60f109810030340360014402c0001e4240c4002ea070040707800100100030001c4041c0781603500455100111070030b918100c81c2e0360004020b80500e000360f01c0302c42d80d550ba440545840401c0749894140c2c00000d1081007564900c4c00c0300499070390810b0580035505100c08a03d042006000b080c0c1520f2603800942041000d03143c003017009003c0f80e8110300c190b41d2146404030100310b156004086800059807031102c8022404180a0302800300d510410250119030304100c0c4882d840c2c0c504000c0039009180128807601c40c0caa08a140079012a0040d40c42400903034159116a0001072050888100358240c070308450380c070420400700c410782e40700f031b40d0f0907401000ca0308000800301001180c2c4448542455260 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 392725899 1250 392724649 392724659
    0x30605090a021509040b040c1e0e03011d1516230409021e0901050714030c060903181c020d0302030d0e0309040b0d02010c060f110c01020a0305091911010306 69
    0x80ca010b0300181c203c00810004100780a42400c1c0108580e10707905641c184600a0304110007800d100820340000e04070780c00c2200501c000351181901043c032120090080c071030786404008464004001d480000e202d441064035010f06c19418249441c80780146040c00040c3c00c055602c00e46180301c00084a0030060141104103161807115000f0384050002c2c107400507140c07050121050a52002080c0701c918840e02403100ca111aa80705084440e503681c06020200c1108480404c1482c601603481c49903c1030007904200901e0700300010160503d07400c0b100707181d00e58807110410300040720b03084a20749180d02d6640c14100c0240c208030030b440c21107611a204803450180004003610803110740fa5001d1400e5040003480150364071f040d009403105d018084805101ea240141d0029113001c100d00d4006041e41d484404da04100117003948000f54803c400c0840f9a952501860800d0007503000c4141c3c6d20100380342401080c4201320005100020007911030f1141a481c0305501d0b4940c0c900881c070705090405844450200d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 392727149 1250 392725899 392725909
    0x1f0f090b0a18050a0f031709071202040b0303210c09010c0b060109030210120630030509030109240501030321060b040611010b030303130b0a090602030103051501090b0109030605090a02 81
    0xc8a81c005c06070340321141c0c00c524004207100020820b03c108a10400c00340b00080070b02080c000f007110100510720b1000340892011a01800c4022141d0341c2c14000403c1e021000054091003040d500103180d502502d40e039440411403011301030904c40b10b00240506070003100241007600482d0700824141412200d6036a00d90020b43c401102d804c054000070340340110380c1140c520601903000640442940002c610140c03604041201c1d444034000c0794080c4241c47c00b1018107000341d0446d04c03940e6018009001402d070714244842894165403207403814040140002000d00014841c107816030303a040e0745800c6c01201d540047c0c54070488212492000907178608000460310060300050000380203c2d00c89030301c0d140c007a080300303400c498210f4100c0340640c10800c208601042c0e10122036590720b0f8040003145164a400c1704503c0242031000f001000c0e1440000017000b4001e002544041c1d1344000c46000c095070b0707241c04c1a2000d641120110a01040306000140005800c40d0070495010484c43c0807164080140e8001030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 392728399 1250 392727149 392727163
    0x60103061422091a0906070f05031008011805070806090304180b0901030b151009060302071b0b040314070b0702060a020a0b0a0f1409060a0209121f0f090b0a1805 71
    0x407414080400e813042000b0f001e50055502c1007808002c2c0c0700e2441c0c0114094181f00d0481401420041c001000a07120131580300f58502500481000b0803a5464542c0450085160036105807181d21030f50780c0000742c0c40300000d861481078030b04c5809142020300e4041c02440d040b6640403201140313502c0d00550703101d54440a080500850190241d003507141000350750301d1052401c41a2142c0515021850044500e4110004004540062a0060b0b07500d0950403c255108242003c13074240640211001400e295035101810a80303010f480340406103000e02c15001c1e5107107224414031400e0b48052014801514012000e00100356035401aa68554840e603601c4c00c69410441d080c0403e95940c0050400c00019440f41c0000304134483c60070030300d40c2802e00c1c00607070f116070060038480455000a001440f90f00c50390303440ca8400e00c144007200c0e004e0b03007507000c40201013190f41c036100c0580c1d240c0036880301032a4030342c0194540f081d040303c06040f00b611072056440103458602c41e800740740c24081c5044000114104820 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 392729649 1250 392728399 392728403
    0x718180207140d021b06090f090c09030a08031602071203050906070b070c11060a1b1110020d0e0a0b09150f0d020903060a0902060a08040c090f0b0906010306142209 72
    0x44c1c01090407017010f001d4114601ca100c40d0041609208003100c0e52200350002c5000c60003140e01c1861903170307600c1c0e0040180c40340c540350340d80500451903070900f0005403201550182c0100b01007110071a02010302281e46050611035403005c84400102000400e0040004003414000071784002d190050980313603032070201d0054819a000036031981e044402e121741e80903003c0c0880f008640c01481c009a824000b801c032842c4114a01042c2c0d4001c40328002c2101c81c000c50b0343d04410283c175120100c0c203005000b07500c9488000d40708010415642c80e1803118646114004c3c142e1311540a5242024014418886c0e152480340040540c18801c00071a448200c10038084c00d032081440401503075500c884800c1c1030401c9070241019404e14200f9204000513640d1a060303841b03410007407400c100299590b041c0042c400c00e00781d12000105191140c400726160f510b4110001c4010156007803112500c4802c01182241d41e24030170304c1d00c00e040422002d1020301e04007074510440300c010100ba2400c00987c0908100f103440d48030003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 392730899 1250 392729649 392729653
    0xc011e0203043201020c0a06110a120c0c0602070302090c180306010b0c0c030303010b0f0f040e040309034202070213021e03040c03020d0203010e010e060718180207140d02 75
    0x1455514810356101ea18844000c2c405046040845400305e01c01f5880c0d4001c46003072001d1407203401c0e0304890802c0544103040e04036540e80349141761400040c10041d9010801d841600001c075000c51154000504030701103e60203064a0910380d0350383d80410300c54000c29000070030b80b000da01814200341d600304807044c040d010074074149540d04100612285000b22240640340281c2040c001041108500800d450141d980c121800341d8400140005c0c1040e031292342c011010000100c0300f40828141c1c0207543c481608d124040301580300c94200d0300c0c000c43c880f02e4002a004e803000c1d61588506400c01d071a25090510002101500344070540d8001025514501c8180c07030340300d501082a51410700c84030729814504880001151450500d500d07404845201030001034003490000401c7c0701191401d52109502c500036400030006c4001c01ca1461b5201c41007034449500141e1040b0078088030300d04c0c5160000c01c44460704d2904001d0000b40035503401030b400000013920000343c03480e6200c0d95008184590004902d460340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 392732149 1250 392730899 392730959
    0x17010905060c0c011b091d06030705240a0e09130b16030603050f03030a150803090f010c06021c0605011115040c0e070e01030507030209030a030c06022710020c011e020304 75
    0x7e0310103440d02e070702c2c5501203140322203824400503440100e02c01064410a50310340703051240a0305644a1100e40030005c0c42c41c124009071b14903500d90300c807a111b9010081247c00d2142d50712085544680620025405494604000c0203da8000084103511940c80064140070a425a0326118030b820a5250580c4000e503410000410034500003505c41d0015600b10110032092650500584598900501e4a43c034050494080a814a42e00554102503841d42c400d00640d9102140a03562529165a40030301d8030503410890b0101d85c56000d101d4031103442c00881d009110101e000361a402100b00b000d8402e80307101046100204a2140b1454070070320a50054a441465841c100c1c0010304840c0010680c100f01131040c840c4120941c0d0220300595040d03054688403071140c500303081510003403085c105050042c4c410103010741c10854040724060035038502103a441c204180035000583c2c60b5080707043d600340000c2d01054101703a170002e20b40041b82042051b00c11a0b0600345c07201219200740f040d0706119560008201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 392733399 1250 392732149 392732159
    0x507121508072402060403080106210204080f06060f0d0b04060902030109081209061b0a09080d09090b12150a230619080d0e031f0617010905060c0c011b09 68
    0x5800c0040c0020f00d10040c4540e1406440044c4425810300403603040000c20b150300444400052010310303410400754011035a407036541c0c0c078080d81d400003042c11216500030200001c10901d13100d01c1584941002810098944545503210041c819008000f1102941d582c102c40000da24241300f070500483c8590f02c0307955500c20b05240c0e03011100303004043c450350340c0c007071010800c03038105042c1c170540038136501b80b4003544070038a42c0d4068504442c1600945294418a07450301046070b0700c00702c1c00c011030300400c40400c8110701c041c060060110840011000c00d41c070002d0b28013a1750083d10384d42a800309811800207250f001003c2c440c00b49107041c0c0101045862690f0600c800d0346499100e070040c1c4c070b0a804100c1d074000d140840c01c83e00c0d50b100042e51001c0c8619051051081d031000d210400440c00d04603800790110580f404904000c0056016080341c94409040c0812000c17014421481aa41c00000400003503440c4c0420b40602d51001590030042d54035469140d03d455080300c1400c000050a03140c003a246428a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 392734649 1250 392733399 392733449
    0x10834031b0b0c19111504090e12071103100207060c030507020f1b1309081b070e010e04080405030f1f02250203161205010c03050712150807 62
    0x50304103607440369042000a900b60000100e9000980030700b07005070781343c80c86030070000203e1400d042c0b495000f00f0740c1d801090a80c0c1011000308151204d00000b041744007000c240641d920f0002d1003002c0c0c0201020841038001c241520b20030801c0302c0f0001c0407540781950760f20034142a60400b010484030a5100c5c24802c0646070140142c560184041c170060828000d0811303610b5507403030008049207412100c210103002d80d0f101e0740c1c521064a001c01c0d800380030b8454645040501c0e640311040d2074001203080c120300500c400020030810100c6031082c1c14540303113909040400710004c0b07000d807089031613400c104400209910280511a1440000d4000d07002d05d05000e005a90040d00609403113000d00c0c8100300300c1602c200310300da081c012100716a0a1009505084c400301c2d00d09990300c18606030f2090064070000d2802d00d0320445204c0e043c440c078004c1c4000c001484003a0103841e82a1100d10121302c0285000c1b6420425911011605114002c0013030200e03a10000303a410000560001600c461040588440b11881c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 392735899 1250 392734649 392734703
    0x19170c03061b12060a050402120a060f08120903030403060603080309070b03060d150b06032d100504050402040603080c07170a03080f04030c0c0e0610030501083403 72
    0x92150300d1520b4210044425960b11850a6a20b03c608054001c10364641301c0c0c0b009803000e801c0c0a0400c6540761150181c007614010111441c5003c0d50500030081100300350224800101c1d8580d80041c022100100d008100e035030005c103032050301480f00b4030001010409074010400114001d43c82103540303040c500d8400d82424a0b6400c03060902c401042486055110325402402c03450304480120ba24400312003124010386040c4409551000c00402400f03101d00b9001402a85803d009140b40a20340d45100403008030300c01120a2200c161544c1010002c0d81040c0d04619406440180000b070303055125560f401654020514a03800c40d440b00f20184000e0240061140300c0c0009440142100c16581c1e400420f4210024514030240f0000f0010404142c06004403001a44d40a335560b401103840c0e000c400c4400c0d80c00c4030700c544541c40041050081c940244580d5041e1600e03c07000c0e041d82c14071900101107244074412002d01c0d6282c0c09040ca4540303591580c0304806948904c0303120700144102c190000e800c2007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 392737149 1250 392735899 392735911
    0x1a01030c0914190c140301080114071d0405220602041e0b03071407140d080610080c090a170d02010b010215070c0204020412060902130c020c19170c0306 67
    0x62110500400c0081220758030034280c500c0f9004607055004003011600d0096640301c401d1600000b00010461107010741040c0f01215140318216115078908030116502800b0141061401c0d181282e9680303141002c1d0080e9074020034000e145003840e501494a0000c000c940c01095035044c1e03001c03a00303100500201180c9645164140074508840e42044d41814052001a010f40280024056850224090481580c200031b8000f8403640f80055140f804648031109000d4200001b5603000000b41c0c2441d002c0001265241c0c595210300741951001200b418582c400f140c030175400320f0b410400182c0c4c0c40e26a804410755003071400c05800d0409145d00040d096400c0b5208850640d04506e0080c120351403034804466000e202480c00700c11824407400840c0003403240d5089060480d020030785100520189801104540380f0a0721800c0340c981081c0c0d041401c0f40c03025400400141c004034414202880c2c502048500c001c2d4954200c8100c640d10303010030104083c6018501e865810025542060380b40034407140743d200e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 392738399 1250 392737149 392737181
    0x10030b0105121e1e0a031209050c01030914010f091e1218090f02032703040b03090705212401031e1b030203071d0402010503041a01030c09 61
    0x410829502c0342c0b5044200148801c0c01c1004018204248041221024a84245500c901d00302c1036994202d0f2610b0041c00c00340d000c24514180384a0a03200c0b881180c00d541d4020380078010400e488070044010b82001081554002c0d000d4248a40e102d00a2180e0313150008009030000c1c0b610704c0c03440d0048003880d01d64a440c0c03468441500102c04540010b080402a00b0240380250b0202d8034501940000301203a0070000c6000e142ca0504070962680d030b4000c40c0240721408003903440300030f80b1a0703040d403501041203c0e02c00da8005010802004100c2ca0103150018050810b440b90192507101047e07014614080c13040e1002c49040d1400c0030103070188080031024082d00940348010180480c0082e14000600c0028002c081003407284001484d00c0040e444201e510100103401860074038030800d41074049002c164428000c6c00e400048000c46420300b24986580c3d52128852035540c0e400648160b0001001655400740c02500c01603000f07600241c180c0654480c0320840c4a09041c0350344034080311020070b4007a03075803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 392739649 1250 392738399 392738419
    0xa081303020303040219030c0f080c0f010504090903030603080309010501031a040b040b0a0f0501170d020a020d023d030b09041104020307090513061403060f011e030b10030b0105 78
    0x800c0d070201c100d80d802601520850844001320b0602c0c200303200180e001400c02400d1001c0070885028034000c40c0300b2101004201d03641c00e400302d02000440150100f085001c90801c001c100041c4016410200d0103501904000030160b949840b40d010750340c0125840c90b6580d5540c0018001c00210800c07824441000800241291a007503950500c0756001410141000d110f9030002030b0028184d0700a0341242c4650b802c140142c0d40d4400b00700d86502d005450000a030700480c194540c20501c009180c0034000c2c2c00512a8600d00030603000d00c450300c025280e5240822000728128840d144184c0e18203c03070160700c54840d14032106941d03001411a04e504825a11403042c46003402f020401e410182c03c00450201c400580e41d4440f0541992501c0c4158407803500700000e1400d88182c0c00302c6a101600329201411300c0300045000e13608254480c1400c540c2d00001d0440320700140304071942c500d040302190300c0e5038140e10b60040c1c0302e4455000d4180704070341c1452106501001403040048027600340d40100401d075001c80311 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 392740899 1250 392739649 392739653
    0x60711090708190245010309050c04110405100504030605010e13061e060f1e290d0624050a0210241532030415020c030a0813 55
    0x1d064035034008065402150901032070031600400b0341c015000c40c0c1c0410780c1002960410b200c4c2d10b050b4500c0310601c459401c50344021b5000b8000c041e0039580c00700c05081d0030300d2003600304001006c0c1010450744040d02804045096103842542200d01429601c0740c6440341c0c50f51030040c099880580000710b44c1c0041405111406a034038000d159540d078404408128990a5024901900241242c1060148c109100000c42f001001106001e5480c1c240d0041340043c80380303007209003210300c502c03030740850031507680b404502c451065204035a0313004040c030f40d07604e400014907903c02a01c2d410b810200c140c081d0104c03601414200d04403080c80240340f908100c0c0c100000118081c2d100d203001690700700c0c0c0c1030f2645012036a02e0b002c10400c9501601d6220101455500d884486150b251010140c0c4013003000007140d4403907190745101462801c504040c1c1c1c03104009508160401540000d00100d03018440b0002e8100b0940f4140081c0c0300c1c19488100441d1200b00410008080c2078024103010001d010a403840e0300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 392742149 1250 392740899 392740921
    0x31b08010c08090d030209011b11060f0406181401121104090218010c0b0604020f04030c090e0d020601121217090c0f0406051e121b010905100f1d060711090708 70
    0x144400401501c2103601527942084641ea100300c4861a0b844040045c0c110b10f503211071800341c010b407185992010b40c0e07100c1c0600c0446040c000c1d401240720803140340400040c10f41c450760402e0051111000b010801a01c44402038045030801e4014444258011078011241c4080a01d410038200003441c0200183e49142c4840032031900150181c4d0055400150b00354404030b942040f00c00855009295543d09551607000500408001d03941031074502580c003200d00d03a11b00c0081e40e2030589008504511080c0141e642e1810240320800c0c01d40b0600c507200f80f101e42114070f2254114880d6102102400c101c0240b0003c105034101d01c1000c26125624022042c000ca440e200302c44500000d40c0c9440f84101c088036000500305205140718070141d4480ca01c11070620001c1c01e0b0501000c0002a00c0d14030406440f1401c00a2022100d162400001c40e00c00d1498242417142200c0c4885458028046951100d0b0402045165000c60b0095685217040036045030a410401e031040d80c4402d041c40d0038900c500384240164 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 392743399 1250 392742149 392742167
    0xb10020d0e04150e0408030601080c0a1205061f08040302060907081c03110f040504060b040503060a0902270f010609031a040c050a03050609010f020307020304031b08010c08090d03020901 82
    0x58000c40d41c0d2030340000d0040f2001e0303440019000d0410040007038506840c117100d6903801111414001a0341e0340119203042e5880003640d05045484c1c45010324110880743c20700003402d000308075580c8012403c40014000c004545000b1180c5001c0e503070b140f014503090030041d150079805494508550304c040300030000004082601e1030500f00514a8003944003d1943c100c018004130207900c0783e40703940029101c203c0c032140802042101c80079201408074507540d007043c40c0c05000d140305032a007503000240040c40c078500035031080601d140b00030321602d0030320090640042d0072408280c284411130014000e105105e1340710b0300040d00401d0107180c20354403d415542c0d440307440941c940840b82e4444c5034402140030401840c103010050700002d000b00031100d50346e04100e41d80d89020340e41804c182d441c2503000740b00542d9031f008491040c0c201c0e800135443d041c51503851141000e0320032300845004001c1c2e003003c95840710a01a2032640c0132969904407041c20640d0304079083c10300d038100302002e15104021030003060341c100e1700d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 392744649 1250 392743399 392743427
    0xc020c1503420301050c0d150b040b0702040e06090d05030c0f07080702040b0d0309051c1a01031a0601080c0c03091906030605060403080f0c1509010b10020d 69
    0x465182d07201c80e040d99450403001424441e00b588942c00030b403864801150416103011925a072074290024001c241400c0791000c0c0e403a41c0404104100700c140b20242034004100e082d0340c151103044a070f5075410b0341c4d049941060300720303450034800000c0341401d601e000c0c0504080d11250401400302801c111014a0307442040391401e900317202c40440010242d5020348241d981d0a4403451b9482e60720402442e1072403040e401000101d01c100d1400c1c00b40000c60600c0680d5071040c40d03240d01c441401c2030034a01002a5050003a003c10010b00e0003003424000152105841d05500c6101e0fa80d1424650651909801d07040040c3c0c0c2d00305280024404110b082d0ba482708400d0740107500b81010b540d440b181100028118829065040d0b00100c0c0c104140d07000320110510305c0210754042d5000c0114545501c00c0260710b21a0344000740c0026414031104000c8401d07800241900501c400494014810014105260f0b41003110b500039a030b55202d00071a1181080d0000b0072503000703d0710140180790074400c00508060100804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 392745899 1250 392744649 392744689
    0x1b030e19060b010c0516050a090b0109210c03081b1c05030a06031e0320071703130f0e0130150f0b0423010303050a05040f060e040c020c 60
    0x1078002c1990003100b0480a1940083c15110719103455200d41c06e0100301842010301070b80c5071180014030320070540b00340000030a05035903540f14245444000314140103e600400303100a01c07a190000000d50040382400194071030342180b0f485a9083c003d2004a400106104210350441148402e42100c0a810100e0352503850801c00d07125101c2c441000014840f50300003e2101c1e444c0301400070364038844018260a42d120b1382c3d400114900100103000b1801c1900c5051140fa8040d0a041c00880f030010604008541d40c0c4040782d05152110320000c05180030380d0301c020140300c54401d0910491041901e180d016240200400001074079458651103070b1400811612504003100049504001a07082c0d03211002c039040c001444000480142000203020714599540f2903450204042c0c00f043c7d402e0045610340810401c2c0c286030ba865603d0554050b40004513400801604000100700c2d40c640d090100d001d0000c50381c960342001c0c0312034103000031680c015130803405660040100b034107030382d807a030b0b00003040f1040d00e00d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 392747149 1250 392745899 392745911
    0x241e0206151903031b20030609070b0702060319150f050a030b190e01021803190b04080a0219060501081e101109030303011710020304050601060516061b030e1906 71
    0xc4601c17068800310342c004140200032100c008040d100d152801d20a514200c00395007450f150140099501c0e29a441003074441c02081c4400d00c0940342900c003450340490001083c1c5540544400100704450480107850382c40c071f148032401c0c4002c03112000000c0182005449502d00303641951920104500c008000c40f003084103008416000c045160061040e0b1001540290340f00e041c100c004108014040b5049130281c4035a920003a2100c1c000c3c0c1607000d4040d00500d07060b500d5103641c2c940c4011a0702840b031010a5208001c001c150410140350b641d00c102d4003907040001c643d418020300130b007000c24520791450240e040d000e00312a510340129400030001100480014402521008840340380500001a94580004000001c003524980d0070401c04965400c15280c41300e118004101c124001642c0c09003c80e404800103005a0f402400140b56401d0f210203800505106951000181c0b515030b241d80480b04280402101c190384c15002d12440f1000003400b03440b00c0480c103038522104201040d400303000191146 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 392748399 1250 392747149 392747177
    0x5060d060b0d020415080c01170f04050f06010f031101030b0102070e070918050a0c05030c0a08060111010504050d11070503150a14040308060f0406241e020615190303 73
    0x7002c00d0a0300390740903005000d119012000100c008015224485950003014900c2181c0e40c482c420341140c41403408180800c42c0c0f80c03000d42540d07403100107100b00c0301d40c400ca03400202203d2040001500904282e5500c0310103d0443c54000e11036050701114505150600c4880381481c0e0b0040344901c29a440042041070b2907940010850f14861141e010060000585404234240324040e0440c0340316040120317080c0301840c41d580e000c03074a0f480100c3c2c03004100401440180d214601c2030f00a40e80082051401c2a9003022960180b82111416201203030303140e010084001c001900103000070103040c8554040c0041c18038000100e600c9000d1152950948500c0e007001030000e01e5298040540390041001c41e4855190900e000340005400356400c40c410080700b141d0b800c89207000d014140a60300e802c064592010b40719070306000c051480030708910602040d15114a44840c00b05040c500c1080300b50300030002c0d418490241c0d40d103004400c01160180d00021010300130a0003600340740c3c048036414509656840411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 392749649 1250 392748399 392748409
    0x302192301021305030706050d02030601120e030a0f110325140304030309051e0915030f070303120905070605280504090510050f0f12010518070905060d060b 69
    0x300c0350a003905a244404011601056000d4180c4440c0c41c00c03684400307520f0f42c00b0940e40d00100d01c90700c400240d01700501d01c14452550081d580168040c10400384c9211a492a282a20603a01c2d001c440e40d4004140c1c90740d0b10f50b00c640c0a0000700c0041c205601e801c1000c007211501e03071040300d5484603000c1402d4052020001e15510031900123800c5881c080144a0075900310f0f8403988544419000a811a5004112450b040c041900b604e401c0a0a000c070300c020400901941a0004001601c001762004041142e0b407000d0007119000c46542c03000c0c0420034210320f0080c010004500c540c0240c6440e201c02c6100140e0009030210a8a02c2400c0194a404131025142254003007955000c0300200c1c03070400050600d8100b800f400c103035840c0641c00c2c0041d590b4030060040f050000c1c41020f40c0012503801818880c14501d9140c84c43d050302038070102c0610300e18480d450a68500b03880300a90000e0182c800d43c090007061010383c014100402c418403090412600062425202e1480034140c04d688070751580080d990 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 392750899 1250 392749649 392749673
    0xe100c02060a031b020f07140d020d060e010e0a081e0f0a0806040b0d05070501030c0513080a030f021504031b060e2a01050d050402060403080d1e0603030219 69
    0x40105072030340d078824004004000c1c142082c038141c2d1810f41c401c07400c1c0300e590022070400810180e000040941c64a003034001010080b950071b80c2c0e038200001c61003280c090388404c48598150390094101041000170400aa82124000c198580d480d402c0f0a2103900020680e070102d0300f54550802e1140c80302c000385101900103110f045001814600e001540882054000c040d0b148581000c035000c00198104405203c03054043d10401071031604024410b00c0150300039844050a5400e41ca4807034200070145800c204a0140c68004982940c080380b0b51004069100c10b0040301100d06201824183c0c510401035a60100050300080034050f0708d0312620105590b80340d040d0b500b0f0341c210005114a0064888050300e03070101c40c212408003194003102c816105410b001c1d40110002c180e46951502180c180c00c4002410090022a804801004004040360540001d0482500d07440300c001001e28200d030000010320604071030040e04904041e000c2012940206050784401020b076569185400c5c40d15141c0d0800d11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 392752149 1250 392750899 392750903
    0xa08040b0601030b12010621050a030809010b040c02150703020f1b011e0e06010501360b0304080a0905030c010903060504020f090705220f12030c17030411040c0e100c 73
    0x44145a00342042ca015000007040300d4088c4042080c0c40045030074250b044803148400703412944581d00c0d50000a00c00d148880c0d200c3c4a40d0000140c409040700014280c2d00044882d1005900030b403a00008103511140c1c190304281c19041c00c41c17424940e002800c0583c02514a0719964401100040640c02020b400c0080e0780c000b28006c580c0004441e80201c03009003e203200c070350200e20450f8004a16075020b60b00039084004c0010150001c40c140f5002c3c182000e04159034282c0b882aa044005008031001014600462050701c020707865a0302020010119406940a90301c2507100044005059802981041c00d40e0740281b0045655070f100d0000c213921401900e60315801c10340341f40410002d10742c40300c0038090b00d0980c581d02d01140c0048000200c84070303415000f80d0725400d100c907500700030f54041a06c00d00d0305544241085170301c202075900d0745d0300b501e8800080060740090000800c81044050742d40d85c603070020200c03000c000200300003d00074866103008088901132880c03224010402401801c20b011350035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 392753399 1250 392752149 392752159
    0x3120d1103061c031202040b040e1b0301170c0a031109070e01090e04030302090d2001090f06110f121c1b050d11030c0702100f0e01050d0b060d1d030a08040b0601030b 73
    0x15030350107510500e64810b1180d56160b0314400f012403d440140c200d142d4010b0740bc02c406909607401c025010311100703281d0006180c0f40c458240c02c05070b50707100d510001008500610038000d041ca600b40600c42d40e443e00030051010131220051074035040c2c0e081840c100c140c40b8600b403941030656662800350000d02c60280b0241d81f11540e900000c1c20400200b83e040f441c00203d40e280d20f03101c00c01c0001500c894076203028980440001042c09e0114a12500e0f00e454904050000c0700c0e04140d0412483d801c1000349070144a103800006407160804252a20f402d00c05100110200424000d1f10807480b10190040c00e40400c0010000d40413114030703a103401c500000341d440100c080e45c909020382121025030090380c0403809103100c4d04450b106503015901c0458038a02c03a4480124040c9c00b0001103c41c2e60207803610032240f070340c5e400e0078010b1611070360083c00c0d04007000d5100196203200750415000e8143c0c1118030010a07403040156051003580070715401e811682c0726903c10941d03202d070030041c0c0181c0320317aa420703913006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 392754649 1250 392753399 392753407
    0x70204090b010504200708070219060c020312121b04090c0e04050c030402030613020a030c03050a0b0c0f090120031201031103011a01080601020a0203120d1103061c031202 75
    0x1201501c84828100d4204032030030030141107004040b038460501504c8681e400d900910684010030001802014628801001c0400801100d8000240c20b01160000703000030301c000d03e4070004c60804205104024000b80c0c0c1d07040c01e00510b24038580500e03100421840300602c0030180c1002030174140059030f010304a4428140104807040000410060020007030303900c0746041201050141c00c0300011680101d4010300a803403e0341d00c075070401c48100391b503850803a0841020b080c0000071480c0203401c0b001951203000600b1406a0714101180841e2003d46240040b000030007084031a40e44003030445445c0c00e42806c2005000341c2c80c400c40d03007602c01c9900d41d40c1d140e4000000c0d40060014010f0b20a81070341d1003441c80351146100346003414201c0700c600392018a03075402d005040150750300482c1c0703403075005005204413281c8200543c0801d041c02152041c0c0344131070701701096000d5140c0060080300311104452902e0360035440e19000080340540c142c039011544802c42c217486414103102c1c0200c0e88400f80700c09000d640d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 392755899 1250 392754649 392754653
    0x5160e030709290d0201082a031e090c030706320712081902160f0b19051b0304030216120b0702031c0506030f0a06020406030e0303040c0b030c07020409 67
    0x20036802c004001c0c0070314800c4200c8010b52130190b41d00c603030741c84e01030355006140d950308620010b141440c00f41015501482440c2582c4062156004522540348460040408001e0024103840808040c0c4035117403503081000c4905080d100042d6040c12542a031400b0803205601c4484084900c5030303071040d01d620039010403880c40c0124120004007042031040782601c40714a000107084030405800d555400254040e2410041d07110415006002100900307403444031609510341c0c0706100200c55880485032580e094080001c004100780000243c843c00c1c0500380306c00e241c854282c1c17900c85400c881c1c0140c10040440441c090503c20000c100081c985911004ca081d0340310340c210241b01c402100d04490170b207a14030000318560301c04001da64582d88032454a902c0840081c0c100400b502c40240703895014800d89014182500040000c6041c0c54010305005940d1400c05500400b41c841001e04e05515900400600c00007038055001441203030358403100a912501d598609000c80e12903050060350103800d02c540e0100b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 392757149 1250 392755899 392755931
    0x1506070f0507060f050301060c081204060507030e010603030c02190f1205100e030306042d020301050a062d02120a050c280816020d0506180105160e030709 68
    0x108501a00488458680c0c3d10350880d02d00303140a0740b00300000c00038030040080341d0003102742d61480c900c90181141000d10882807014080da04682c19241d040d21034091014503501845242d524126003802032016a003151409803101d0b5801b00b00138050b50501c5160302a00203440748820191503003d0110307907082d5a031001041c51700020201519580240d01001c00c130300d400b502c203c01d0308240341000b843c2540d60300001c200c0101001c0d041101d0800004160451580d86003244c0d07802010480001600c0e54141014060b081c64103800407130910180000c0d10840c4aa00440103541182102d0105507203107020004038202000c2d841d4400400c440030a403800a283c210019000181d03503801260600480d91726880308190042d0001490a40000c001402151240c0004c110344900c0c240d2030240d000340b40d4045100014080c0050f034568001006000e80d6004417801070402d060a03900a02850400c46d420180c40e0b040392160070240565400380e04440d0710b088c82044000e08000c68100500942d01c0a064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 392758399 1250 392757149 392757173
    0x120f11060a05030f06030307030906120e030d02070309080a0c05130e07260706050a180f0f0302011103070804050d061d0d1b0b04110a0b0c03090a060c02130203150607 73
    0x1484c00160b13403002030002e003400000e46100e07603003554901005030b2901806a81b6041c0310305800079010b443d00700b1040300b210f0400080c10160488200141e440344079090080210406402c0400203030890220400864920141201690412140e80c1d0214060125100c02010540c1c1030342c0c11409117100c000707202c548001e01e45c006052612581c55000740703980001507c40000b8000e030000301e44244100902c0c0c0744200104e07901c1556113062a00c0c004d458a4240e207540b50280c1c461341955011401c00d00855900c10020b00c0c0184480e0025810b106441e0340c0d10059001d00d0080034000e221003041c441c00e203c0260406018901c0f43e103020001d0b05540070311941c072001c500030180007141c40740b004a000c2c40030440148410940002d000700c5140c0710f03592051901c030300120190f68030840c103c070042520104000100084607108004543d1505258144140b000083d0302100900c054101d1020140c0c48a0900c04440e00b10324a0050762942c60901895822054400b041d1b000318000c54803804000c03070340440c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 392759649 1250 392758399 392758411
    0x150a05010e0609070207060e01020102090a150f020714010f0c02090a0605030730053a1103070f050102040b04030506150402190e0a050603070e0415120f11060a0503 72
    0x300581e940c500041c054900e50540c0e41000680c001d800400c8150b200e42c01c040c00904051001519100c1c0300000900701010a80040b040807c54407101072049400c241c1c0040b852100307002811800e4640b0362858440301c0441c442c1e50510035112358801c003081c0700b85640e0041d5940140326030032505218803500b00401d51402882d01a02c11500c000c550081c078244480c050940d841c02c2d802c80c00c06600122100503d9501003220359210b80700b401d41d00c003d005040442d00c000c018080000e8820345000c0c40360340502e03c800c00300501048074100c1c0d0b039000001c41200d59094200540489004c0c4518004e802072140754011103901502240120400001251950090160b09500302c101501c0c5030410049110b00c1c0103e0201000000d4030941c02e0f4000d0541e43d48621009020301421586e03000894000d52044884600040c80a04030091514117441028592040c044829031000e082c02450389200d0141c80d805041541c09420040810400e0b031000d015001000d0300543c2c4510210788060301c030743c10990705 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 392760899 1250 392759649 392759669
    0x20d030e03011b020c10090522090b04031d01210911030f0106060201060905130b07140a05030601020114091b04110d0516030207022103190f170f06040b03150a0501 72
    0x46c20011a214043c04e01c142c0d40000d0941100d240c4001840f41500304944006844a40303031601c0c4c6000c0f0310700c001420721517806a140c41003840f481c0305a80818608100e42e060602c03500349840000030032031102d00c18801e0300384113000858074103a0426413812801007203025418801c2c0c0c0c00c40356861106400c05000c41e440b0760003e00066450342814405c0c1d07441280c068070000b00c45281040800c2c0100c9080344c03c84864100035030200c000c221310382d9041e4050132204000c05d40000038070141d0f50b4240310300403600c0750300d003c001a18181020000e0710350307124401000040480c5180300361300381d41f51381c01420502c0e8143c491560390042c10701020041c04c0110795030554002000c0868503c580280200c40c0441da0040a41c1c542070b582c0011000c1018404001c4d28051005003e080318482000c102d01051440d20345070060503e802c0d01004180c0c1941d09210808803145605000860030103400d076980040003110045a10245200800e160580006580c100f9201860a000101c40c855001905944105d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 392762149 1250 392760899 392760919
    0x1504241a01020f030c0a03050a051606140108030a02060f18030408070609050a0f060f092606070f12091119051c03020607140f070302071e03020d030e03011b020c 71
    0x30f030b15281c0c00f0b0322621081e950000a10140000c0c07154004042401203424168201118a6150503007400c17414402c0312019618605880071014000d203d50044c00100011450040d40c84002900c1d000050a01c540c1c00010720041000d1108221040290707580540c100c0e074641e0341d24140b03143d65030458400c86010580044000c02c140c1800030b610b1003982c005240c2c01c0f5101e440c00c1c00844d00c91401d18202e504001c91a140032528a007480e201070041032110902c020170920300788141c2d0800030058940070601800da603107941e009409c010b802003140e00003603001442504a0910100705036603150102c0e403111980280100d0004100d030f20788141c4038241e4140c1b0600052038600b2101c200d61072030245c09031380144000340000384200001403000340c2c40050541004d0300661800d106400c00c440407000b5030801101803020491070354540740b03020900030050a4051a5401040004101080203401c20030200003040e4151000d4100c02d00e400b100000b142249422800020345038042e0203002c51240305c80b02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 392763399 1250 392762149 392762173
    0x10c26010803030403121425031808070c1d07020115050604031101021c05090310020711010f05070807061a0a080607031503050f0a020901081504241a0102 68
    0x4525058585403001036180d030703c0380d440075990070003d0b810424295884002d0003001e44291141e8a006490407180b440d41940c84094138541403056081c050101440e0a0741f0152040e45a442c00030781640018845564601c03e081201c040c03e000d07008824000802c50740b260754030352480741551007540380741c1c000c00000c195441355000213070310b40c0b0409500440c00d000c140003007401da00c042c60300c041d0140101c902245500f441c00039411030424948bc081341010580007001d0406002944000c220807408600c0c1c00100e50700c080c080071103620030b1810005a0040410300502490807039007103c4d008039aa9848030010f250890240c188841e060181203000c5014a40718148a109070303041d101a000902010f54038000d0032001000345d0120848101e082c0800000414402c1c8416001820300001411007030a087c010300143c4003043c0e010140503480130980704203107080c21b0bc4403500558011852000c4104e40480307414010a04100a000d541c0740c400d0121080c00b034904505403120003a000d80f41c1c40c071289 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 392764649 1250 392763399 392763467
    0xc070f030203120a02160611191a0403020a0b01090911041a09060303090d150c02070308220e160e1008011203030e030d0203091504120809030903010c 66
    0x40c0300007901a8040010b080c010601240500b020032a40d104175a2600f404462400503122103130700003004a102d01c4031111040206000c0c00e0881e200494501c2110445540c9180603458807980d00c9007240d0001021604161003407103041c6810b07400203040c124a5840c0c040c03100c0100050642101d5486400c580782a60742414010141842e2100316014541350040051140d4a07100506095050108114031500c903078540342c07001c140d41d000b140501c26246031100900119840c4103d810150360044504000180007030044409480042c5802c00d0088200e4806155299103504542d052821041c05c001702101c1c0e607540e585890a00c0d0342d0f0340d41c0e1408220306102e5458404c01c0403400040400740144001000c03041f440c14100e01c41c1c44c0000b03420855214050842c2c0252100749800383c7c0000901850840c104060119441036244552060a1950b1444014080e2070400c1052103c03020024a650000b4000d880d081c2001038000c0c40940841c1d04000d0020203000c00801c120310041d00b201034442c0c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 392765899 1250 392764649 392764679
    0x4060c050c1f0c031a09040203071e080606010e030d0f0e0d0f0b0601050910030e0c0303030108070f0801060608060111120c030702040e01020406200a0204090f0b090c01050307030e01090f03050c07 86
    0x170103185006165502c03414080300d104014030a0b60140300d0407800099002220710001c1c20300748d4818506c0840c60510f0b0302c845c1840c82c042e14041c108001c1a41c0c1c000d03503940c00f0a51b038503030b4403d07803c00b090002da900800740d660107080c00d02e4030b600c81c180a100500b8403481040340318000344960200001c65446c0c000542c2c0d07500440c548a9000304840d403115540c580280d10040c0c05000d40700c02c80d814074040e000060318540c402d0700002c000340c1040000700f18442c0d9141104001d0940000240019820800014550080203051504002004481c400012014032505c54a07640c80800360f0364030307014904441e07074a6101080c100e015500d0226140701c10702041c800c0d502925116a02e651001c038215901411140300c010803aa818096410000010f80c0c0d20b1052044591081e10250840291401c04050340e44009000d03a4458005c4221522241e9103c0102c9074000c002d800c1c0091002e04144c7c1d140d0040402c40c400425524449190314180368220303000d000038220301000c81e1072040d1100c06035200c1c0a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 392767149 1250 392765899 392765921
    0x312071716120212010807030201090b1c18050a0605010f05041404020622270c1e0903140c04110f030103080f0c010207140606030f0604060c050c1f0c03 67
    0x1041e40000000070301c560640c0c02c0c01c1000c00809810040800c0d060004030300c2c02e82c000c84a583c0300d10b0701007085581104210000300000300c440e60030604d00c074414402d410342403444202616940c1d040b060f03890f407100f100313541c20640000843c0c4243c1c1079842d2100c0100001e01544070381c024800d00000f401e1809005824903903c01d440c0c059490703143c1d5400d0000980200000301c3c408240425a400140a100c060740000c00046940d1350003034114603004d0000311444151000ca1a0070100c83c2a00d2942008010111083c3d450f23030700783e141480c1c100444000300f543d00001c200300024a00076500c48000150683c4c402001c403010070001821085c3c00107540b007041840b00c4040e4045c40100042103402019082d1081d801b07020700e1a02000c5001c0c542288e0041004031080d20400e02a40c14482080000c22703840881070f0020402503200501217550340200410041000e40c49880060f00c40784500c0079250151064803c132508003040603503c0c0c00c140d072001807103408a031404d603452900c20321034011038600b19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 392768399 1250 392767149 392767171
    0x40506060a06021b04021c0203011404020414101806080f0a150e0c04090603050a0b061e12010204050a0e16090b04030f03090b0a0c050106050f01020c0607060e03120717 74
    0x1e803400761302c111307200c403c440d90b10581c03e1282c800010b08402c0c81481034045a074006a89604210600c032841d424100c100d4081c1e441804140700041c50520290308290342110200c0001c40307881811150450416030300140003000e620005945508406254003404100043d4402d55560300e00c2c0d03004030341550542618280200e1410071034411015219a00043c0004011340b41a440d80081c20960b04143d004541c5548683d0700182442141003040b40c0003c0f003299402002007001314003500e07010314648842d10440b1050042501d4240940c100d600a00e0050500b120040e6901c07200c3e500ca10040310f20125815200c1d00101e942c42c45580c1040c15114001442c5c2d00f400e0440c6c0350f00304542107485040341440806440440c0302d004100180c1a50710103130b030741e908160300103252860a650041d40a00c0c0501c80b02c0b241c8180d960f0300401c2d50f035803001069a01d56100d07803150908501521019204070090300000806940e8103800000d01445581141c803691421800c4401e000030a01b400c07a0815040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 392769649 1250 392768399 392768413
    0x807080306190f030c14030613030219031d040b150a0507120c031206030201020a030c0812151e0f0108190c0305060a0e06090105061305060d0c02070608040c0509040305190206040506060a0602 84
    0x82740f00e240d1420324a8000e204032000e14051040740103a00302080c0782600800c1d0b24a405550b050021102e0028140c1c003510705000c000b0000c0302103080c2c4103207900303255007454000c40c2c0400b40b14803403804d81340b009801034500f0314441c20020001d8440751100005030001448a1030301158503603030780610700880c5d83c1a802404080003648040b98441e020b10380441c0d028100f04080e01005814600031402001c0d01c0e600790940840070303c10825444800304003655201074241e104060340d80d40d40060b61141c0402c0c201000386a44124518050286012034448201e1500d01c0030044560715520061013800c0c1910214020780d1124200f07000514222a484e0344030441000520560400340c000d400c1040042e02c9003440691a0b1000503042e412003004c6622090362140030010b4035a0401081c4000c2202c3d01381100e05003025164808007888a004480c050012800403604040c4680112050400159020124507202c8503000b07482c1c0c2410b440545482c030602c00440c604d86001441602103c485030010810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 392770899 1250 392769649 392769661
    0xf0a0315080a08031302030a0b060a080706231908040b0c0c030d090302160b0d0f0c021e0c0a060c050615010507060504110d03081f030807080306190f030c140306 71
    0x440d40004c200c10f98a6482c0d03450817005031810000520300610038400b07940546409000e02182c000180c1c071000190340309680c1001119000340c0201c600b190140e60840c041c0c11030030384150b168400c48409c00b040c42c001c10b0002200a51052520340a40e01c9151525010749607003d9101c66402003000c2d000341600200403480c190303000c643c0000800380c801c4c0140c49411900303100d01d80507040c503a8411514030b40d001512036240341c401d2281001c1c0004e0741f20108180c0104c602c00a5555215a50180b100d8880100d00c20512604204034a9840c4004002900c040c2c2c40307032401044050002c00072142c51003010080f640300d40085000e80103007001039440794100822500c1d01e8010309800360041e110744c0304c02c8070303070500e00e0b1520402628801e01076195594103040403a2105c2881080020391031100c00c2c0400c0c1400001d103a9400c8540140e0404182c40e1030391a1200050719281103041d412440840c95080003c0c0a508010440e0440e4041c541c5952066a200c00407140d5105144506034142c00440000d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 392772149 1250 392770899 392770913
    0x1090305030708070c0507082104060e090c0f0d0902011e020c0114040306050103050a05190210030f0f06080708070608012402070b030906221a061201020f0a0315080a 73
    0x80c1c8948a850170404991035074940c0c5040c00d0450304800a180c002c055107000001e064084c41084040880c2c8141c1380074500314004165003100075080740304034104400310310345140306401d0700d6802d81510f9990707a513021640c407814002c1a050404a003c185075410850134100c5240040d1408013090f00034111200340080112148900508a0400340d9000e000c04804900680700e40b40c0070b14810001821583c4071410010320386100e90000b200b0b54584500b462005032200700c0ca10768540e0042c00c020960b28840790350b000c050907100b124410715a180400000b400400042e5080c00c03140e4442c00d6449054503001c041f01e01d03440902405220801e664848565040c0001880180514900c15030304410b4441030700708202ea200781c44594065015101303002d080208602e4032103050070000303400101183d90340d032041c00c101c4e01c00c00c00d581c0501c101800140280c40d41c14020000c918100000c55458207094440180d032307017081c041c00b00042d01c1d00800c212041650407642e826912028001c0605c407182e50765281d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 392773399 1250 392772149 392772151
    0x1021b010f02190615050901150e06161203050702010212150d0507120606050603280e030c0708070b0408070b0307050706110c060a0b010c170f120709060201090305030708 75
    0x451241881003c1c604840b0b80003000d140d48901800700b184150619800d071038030400d420035403042244070010000c040c40c0e40301549500c00340d800c0810b034055074140003072218015907410307119071f0b9904a002c4041004440e40518080301d5a01c0401ca00d4560200032402c031f0044039120411425000b021070302d0044075100b0040002401001c0180900300ae41d83d503800c1ca0308603400400c40906448890041020901802c0090041510105d055290541e54400481011040100c001c0d07030b40c0040c8151141950400c030482209081200c0c5c0e9000003c0c4200d5540c8942d114407200c1e4081c040c004943d04110408a800700e40000d070081100d18100100c001c101e9101074040400d0100401c80500042d1030741c016040344007038903c07034507448440c1c8600690810f41e0041100e4002441c1c80400c0c4590b07070700403a030340c40c0c000d0300000c01c0c0d5101007025914100511070003a144460004c0401c540f488076520340406031041c844e5a41c2d100140d0b603256016400e80c0c0a506000700410f0040c000112407501c10300c403036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 392774649 1250 392773399 392773427
    0x602120c27031c08090d03020f0412020a051f09080c1026190507030908030a0213030611040f080c090a11130e090c0105071101080402010c05100506010e01021b01 71
    0x140302d24001c0e4483ca55584521010b1450100d40510200038070410140300c0c54038240b1103420b0030b40c0303055580c002c02c480500c40d50043c43c0e08208500d061310700399264041000c000d1720000c0c0c1103403c0b020b000504100c4884000342408000382002c02c010502c0900032646419034900544903503510b050740141a1042c0400041602200000c4c010080100309281e0106000764459480d4000361403485810009903040201030344145818003c0e80340000b0400340807240c1c0281d4100340147c480d0391302104c50540c0b114581c0080d26480c180b08071103c4071203221004000300c942513901200c4260b91003001585806c07220008943c405e425600007108116a074201c4801c541d4000c082501c0c06090140d040720265040d0080508440603104100301200d0410100c0c1485409080c6681007101d540d540160303101406181504200d4164041401c590140e50700302880e0740d10106565140810818a42c020b00c411500b00b40000c0a60a5420b02135001148000303042d190702560000305900c480054403000d10002c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 392775899 1250 392774649 392774653
    0x29070201050912010c0c140303100314160f1d070806060702041407020f101a06090d0f05060f0105040b01020c010c23060118152d030602120c2703 64
    0x8030041c3c400207101d405820301250b145c2e00d5100301c0c40d052480780c03400050314081559008005120101c01070541d04000c032039001c9068210000a104100d041892030000e1595031600007402090f0402e00c41003000030b0b034424030303000b02d41038101845030a0030b0b00003660640c012400c0140410301500388100240206c0b800603101150788090100c2c50480f15078129a00ca0050300624994040d00006210b490301c00d8022490034807124088850f03039803c0b4001c0003402d502c81c104c0010862515114000403464250b0880c4401801c49103034185030361588e4080728041c085406040000c2082c0c03400d40720380c00d68210107a00614a10100c2401551219000da03000d43d0107007005144203c0340c1e129460321900e071520310805065103501d030051461016000741c1d8440c04c100c1c00c00715801c190415400b510012140441020043c603020074289100000e20407200000c2441513210220520546400030034010100006c403007802c3da074810f1028043d014181001c02040c00020340c4c110a03554988144100e80300c0201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 392777149 1250 392775899 392775919
    0xa081209121b071e060c15060b04031b0605120405010905101a06070b1b0c030a0903020316051c050c0405090a0212070e0f150901030507290702010509 66
    0x480c1035a01c0c0c004901030a51a4a600300400300302d04140f0410000788501c002001501803420024030100d1a18000e000c00c2000744011a014400c0704003800000740d25035030041113190b894089003407040c2c1c860b00040da84441488510740801c4c070310070b1000044851a603212030a002c40035010780300241028000b6912992655010340214005010b10180c1280032040003d00584032061140c440303034070003040342c4100310a1103840f012510a50360103510540440001c1d580c1d0040520260042c0118040309005201c0440e428110b5504001c40e442030301e000701c0458640c8e4411a20400703092145000d5182c009591500b00f0041300d1210310051200782c0304905444240302031001140c2103c800300c030740c059158010400030703013542440c140d014078884204000c0c00c4520308102000b818200050b0040d64410200b04c001408880c0d103078440550354400822000003941c0d2402e0055070b40046000d140902d00c0082916010500030f45080e105403800d1049141c10900075400540d0f40d5000466402d4100201817 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 392778399 1250 392777149 392777173
    0x91b19030204090e01050112021002070e13060b040921050d140423060106140903010e070f050117060402030414100c1e1b02011e02011a01020a081209 66
    0x14661011009503600141c846182541203015564000c01c02e0800e6450b250040c0140c142020082c01074a4040e1488940000b0542c0120304c0e0440075840541c0b5411403205000028505180c2c1074103030b5020320414800e01440d003080108680124000801c2400c1303821002c005030f00840c2501e61710b00f03401d04102c0c2c20200312142810960f80e010900307080355401001013004100c01055014020703202d03001040d5800c65110070065481d04180038480a010001203030710500820300c0c1c111240100042c009005c02a4803034261036840000e80988020031002e0700c00420390394455150307104400b071540e41450715600c1f00d0b07003404000c0d40007501c295803610000100c1a5542c0d800c02401d0f0301104800701c0014150240107005110b06801500035071120f00c2c0c061107008282e4052030700b14a001403000380380c02054881c130042e110040e9000a8417101c03600840720001058040d8054525882080380003c00d4041c0c0c2c1004980303d408020f001029584103014000010440c007141e41d0380401d4010449210072884 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 392779649 1250 392778399 392778427
    0x91202090901020c03040314060f040c03080c03090607061a1002030d0b0d1b140f0a0621061401020f01020708030c130f0b04061106040b07140405041d06010f05091b 72
    0x240c0c2007560161003400c0c8d00078880d5410001c0940c0081003400c1000e15050541c0d80400d00041440050081c030704c04030307100851031406d008889502d0402032200e9500c003050f00e0000d010b4540440d5a807a5010308962030b0146061164070072000d84640c0d4061458001c02140040c02040242c0705c09400400100784d6000088481e204040050441c006000c161803914058827114100f044d100e034001c113481c0100794219242c408940040d06c2640c20101d4590b0300984002c030302c00d803100d00190300c0035041800006012200800c158084182039090301c1102400c1402c0e24280c3c484e8040060100380200002100800700c0c40203007030b01c4d41c80b1160b020501640c61026542c41c9140e504420740102c80018200050380e00540114400110f140107812186030507210482c0d0342d03000504000a0142d05130360000c5d10040d05040310f002d8440140304002e0300015418600c50060210600e07681d0f40314250010448141100d041001c0b184024007050702c564030444184101c14261a54803044c29040c01006144044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 392780899 1250 392779649 392779657
    0x7020a241d031c0e0316050a020d060209010908010905030304021018060302040905090d1403060a0f03110f12060615040e13020f010e01020309091b0406020606040c091202090901020c03 81
    0x21403001161211000c0d403a81e1035281010b11242003241c6440032650416001106482844425000120011281f42003641c203004060200a5028000111440811400e507018050121003aa500c04d00e050720f0b01e100340d08803600101c0180c1507500601c00100186480000c41c0d001194500d403000c41c0e0302491f90644521145600984042500401c045c45820158805c0c0b83d402401c0500824010030001000b80054000f22030707880c111000000020002e4480c03421041c01858000c82080840d82d5900307001181c03000c400449841240301c07285129a41c90004101c10b244800b103c0607002c144c840c48104402c8100c0e4040303140700c1c520144070000300351001307041851013031254005080d00380040307104000c90924543c68281c1800842000c02c0c1059900005440d07990000b61001860703900c50790b0326429000a10480280300c1030000501054a03603011901c81e024020948060002517080b40040d204010b00c0e0142c80d4501807602c14581c090314000115031b41180d02200018a0140704200b11400d685c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 392782149 1250 392780899 392780951
    0xd020406052e051204151805010501090f0504050712020f04090b0708091209040207140109050a15020f1c0f0507090602120f07031115100e07020a24 65
    0x201c09200c4081d031010a500000d50300c1603d450b41c9840b151115015522101400250005156121514a0500e180d03c07904403024180742241d8509164078140c1e010b88401d004405085041041a0314046001d028082c000c1e070f4400c0c003410410f81090300300d01c440020040140e038010319604003282c0540751841407140da50700801c3c0d008a40c0c6004e42c00500400c002034840d070503a911464a80a01103210307801c0c0c91640604840143c0d1354030082c00c000f9198865000c44107170b03a519200c8200100071002440e0b00d03d8502c00c846189600c205180040120b0188002c2c0303004413030080141502c0496150100e0a2840c2c071040c002501c10f03c0c00c2c210310308440c000c1302d00c0404110400000d020b802c2d01007003005000c0586000c254684019079031200211300580ca002000e00045525004240800b8840312410aa080651100f80d1034030740d95500100c011741c4100344241110f000441c000034030209050b070444c0d400002d50040007402c480c1c80803400b12190b442100701995101030740700086d504c125035440c0b81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 392783399 1250 392782149 392782189
    0x20d06110f03061e03060a0b01020f030c06010e0c04060516020d1b08011d0c0d03050c1002090f01020f060711010207060501180c0207080607031d060403170907030209060d02040605 79
    0xb2800b0001d00c0411042581140e44c0109490040e01013980c0c002101540300c0040308001c04e00c3c0003418010703450605040c0a04a0a0001051150030f08600080d40c174101c030007210f4040b05a8544a602c0e100600c100c0c0203100002e101000b03a000070550200458180c24405013000f02030800300d459900191110402c604a01c2c4d002c1c1204204030b0509020b0701941c0c01c1c481c2c414028609455021580c0c4243c10200c05000e02c44400c0d416090500400542e40000e505005036980900c401c85070200952000c01c00c00d00c180c298654599982d44002910410031443d90010103c60700c4003d403d458141444901102d0741d0b4081050000056035400b44c14020140741c0540d64022020740390f21810307a002e80500104542c04004100040d00c000145503402c29102d040028034841070a0b40590030940a4946a07120302c0303161705100030135034030000800d003090412400614035200c0c441c0e00340c2c9509035848065070041c0a1404102e071441c2503406c48410034070081000404130340e40c03c04120030840410840940d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 392784649 1250 392783399 392783401
    0x512210f130e0c090a15050f04060306180501031223070602130b21060103021e072001020a030e0a0503150f0603060c0f030403021f0903090806010501020a020d06110f03 74
    0x22442c182c000c03504006407102203400c100ca440c0c0420001c0426209000020022a604a046a0082013107909201020303190070307502c64407840050090021885004140620b2902c070317032611001c074403402d816a80d2003039484428803040c10040700c00240e40000022680c48249a004543ea81c080043c00250721600e005a100c401c0105203070325200d140d611044e030151007004841c00889030880e0764048110042000e04d850f440305401200240203061075200c0004e291040044128200400340c161103100c0c0d012154009102c2c0c0d400012260000f81850250307000403031140000c0e006084541c01d080b806418000c0450b509c01c0003074680100003401611510350350052100201180c68901d5001c0c4080e4002e083d43d04143c003e070034082c8034034141c0c0c101c03d000100102d400c05109200310b050000c42c142071022148824440e44e80103100c03400c001c5003c41c842d07510009030114040354882c100e51058000c4e01e0509065001e00c6580c9142610480301079a07100710303169810541c500a00200d64106111340d4072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 392785899 1250 392784649 392784659
    0x212042d060f11070f0b1803070e15040902010915050c07060e100c0803010501110a020a03081309140604050417070c0302100201090c05040c0311030903130512210f13 73
    0xf0000c040a104594203c4401404a018115844e82c226038101120560f1900c0c410720070014031505984182e414022000d0000e14800c032405d005008502800c40e50f0682c10001d0104021140072800083c045400c0d20707010401201c020403864101021403c210740b80c00c0d0b90940250400c82180c0100b0086150b16003803250780c1c2489400071500d480d0f1820304100745080ca03107a02c01c0d81d00051003464104001c038903421001450500c0400c47d8260f014103241c2d040360300ca18028019801240f40f500e20100b20010000740c107542801a1240a81c12600c500503a4440c03405120240c440108165024146c1080c000703c0d209a0320010142c95006071418420281148100824641c00d01e075480d08580c1080d1103200842d04446455044134000c031030020f2410399401060340642010869100306207804400c01c50311140210080518050560741e50481c0c03510b8008200308031b0300041d4074400550010346803d0146140070503019400d000101000c1c24810700e540e91800c0d42c1d0112004035824107200f201085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 392787149 1250 392785899 392785907
    0x2606030c060d0e120c120706060b03070801031403160b0c0c070e06090a020a1b140703080403020315070c03081e0703020d050c0406050d150b04081501060212042d060f 73
    0x28066503101e141e207000d510704602581d41450b4031b860007030701200262800400c285c2d60311880c010a0140300e0f4503140d15080b04090322841003440300b03032040c20084000c0900304001004403100320420780060804540540c0314102c840000070070000c880e05003080514641882004a030b001000c8141d0001c041f4a01807050182403e0043d04610f2541d0050041018003074001000341c85290321189040403040c16030510101c00701a41d50003801500440d0f9022003070004c944001c10a80c2e00907000c84811041c01c40a01202400850340b85000890400e03a140c0024411640700e9001980015080b982d0300058403a0409264142c3d004000300742d0000c3ca81158103007901a0303e6002e081806d0250a013480c00c0001307820b901c914080c40105550300c503400150f0808a03e011405442c440c0d0307819840e03c0e2100c103c29034800307080d41c100c10300f070480100002d0340510020714040401c60500c40c090030246001c0380000e0b16040f40010019611101c2c83c2c4543e450240c540c0103004026950340c215150700c0155002d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 392788399 1250 392787149 392787163
    0xf03050d0201050f130203070905100314030a02210903030409051f08030a120e031b150408090609030a1b0609080303060a060509030a0c1202102606030c060d0e 70
    0x1401e5906000c1000181c40c89004203607440307200c4805040101189200013800c1605642100441c5850001800140c80d003580029042c0c0c1e10860110004290361202035640c0d00a49200d00c0c0180c2c0800d030904402000348074440a88501d11404604180c04000068290780181d00300e900107554400030080301d0022425080d14148000110440e010f042198545d2a480317406504e4050113113843c04cc1001030f8403540301c040c001030a030003500c1c1c460b1080021b0001517054903138284c0c8184100d00401d5001a424410280207641c031441c41c901e050312a86c00c1c030504c0d07049400001d516008111600e030110f40085816090301628030340c031110080c206a000303046000300e0b400c0307045140e00610800406444100c001410b580d12030801c161103052000000303140802e0074000070100031600030b0000d556855a142e1030003140c42103d104010025000302200c2c1740741c0002c00513100101c0360900b00500014413012580104028042e6030038142c5483c0032a034503a2001c0f50303a8015a5840d9401d200c662005d00c040c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 392789649 1250 392788399 392788423
    0x160f06050a09150203180a1416060804060b010c02041505130b09150d0503040906080714010c11010216080303040209060402031e1f08010c11010209031917040f0305 72
    0x4102e0041c1e00d8031480f400ea10141c42c01611581c2c00000300d03014980400c16080c040000c007085403030300501c81c5408135010a40c1d00d0a00c0c41446584c42d0890410350181e403408c16a2200d50340c1018a6907580c403510050300d19400c0550500c0f9150340d1200241e103450043c8614005061900d56181d45080140305400702d40e4016810010314107130b904a9540d1b06e0914954000041e4001654144205000540c4d038a00c0d9070b1008142c0e02c400a000109003081341c03c1101200e500c13000391444103680b0300841c03000c06645000ca80c00100d10800d490005540d0301c1c0074480c006410320440d0911412810305040c07040d5076411a80c035035071021080101310310380090700903032202040e9425402c50070000c00c83d00080303403404800941849400700051440c403044e2080851607020700d441618281d680d075031142c002c000008002c00004c120300c000c440546414002c540c04103402070004c284600742c25206200c100070b064002c580103116044103500302c0040c803010b40090488201040e641c185186820f920300711101010b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 392790899 1250 392789649 392789651
    0xa060537090c0806060a150e13020918071b0213200301170c0a05090c0c0a0b07030515030604122a03260903040303030b0f0a060206070f03060b040911160f06050a 71
    0x250101a540300354009900c8c4025901e1704d0184858401c09001b9016804000381c114500c100c0303844032a00a0800c0303900802c41038030354600c6030010800b0014000f80021029401282640c1c1a074605c0301280c0c445c4d500300d84004070079401d403c84100c0c00300301a4401e80c403889446643c00c000c0740388050144280d840e0148200c42070b80d000d901d01800310700110801081c01740401d1011841d8000600c090003948440c0b03902540c2c2c2078030f92810030b0001e001000151440d010603400a1101034040c01c0014410740034035000414500144501c19003103d1442c08146a400305101601c1003003030750b43c0e00818109009220381c482a540103103002d4104105c0120540608000c0f41d40000d11909060120869098941501e004184800c00b8000300d1402000d403250140c01070807484001845c980e000c01c1c00348c028140396950203c0024002d2007103064034880d015544903c08100000c2010150359400068030f4068040c01c64100313509584610544613078400140c9081003c82d0380b0b47d0801c01039100d041d41c07011803424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 392792149 1250 392790899 392790929
    0x12150503012a050c12070b040b0a09030c11030a08120a051b09060d0618050106030501060f0207050d020f03030c010c12020c060a09020109170a060537090c0806060a 72
    0x3401a06001a00326042c240440054615880001841001010012a091103030b0b117540e946400049004205d070243ca0401c04000440e4440905001c0d042c0d010f501a42c07551254146903c5000c0d107402000351256261044000c81000070702440e02074080c44e6800b2082040303903e0107002120503a140100321400d0300a0f2040700c5d040c486508000d990b03040c001600c1c01e039165005400000000c001c41e400040e00c05c40350170240741940b084d07600920f0580e000345d6800c0c00350340d0b60703250107841503611031082401503005010140000c0c180030f241c0428640c0001c20403038105414001080c00c50340100e44180d11651100c03d0000c1840d0000f4003001c2c021410b600841c41d142c2d488840c141c4980015204510f216240c0d50500d05682c8200c5408002c0c1c4102d0b000c0304500c0c0e50b100d41d400e0b41e580c06007504a45250030034001903043c000b2450001c1c102c18402c0c2c030a0384118811403d120080c501011181c0702c5959a01c1e40b6001f1480c1070100c00003821100e0010100c42c00c10404008500e4000d5011601c2e0b240c82c3c031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 392793399 1250 392792149 392792201
    0x101e0c09050a06050d0b1c030f090f031401090819020c0306061e030a05010e0102120604020412120203070b0a050f0a1a060729180d0e101215050301 65
    0x640b102c0440303000b440d159898070b02c6200510040c01d000c07684281d000200900c0c01d40d212008103c040a03440c4280c031440c042c552035800c1680c03003082c03074442d580400208860401c0450410400300c406c20b074000000003010101ca980e5110103401a2420102102c001a0120003142c0c0402180d245007100300c00401480c40c00100103140d075450342c500441c0071800c9010307401c1c0a4030100000c030340341607000009004002c6040d200d0381c001d40112605098054501c0301180c92403c040c0300325825190b490010880c003a00c0c980b2400004415041d2200440c0700801459010404013020f04d07001d1440c1d094003040c1411300442440e5480c030080c00c1c1e014040d1401801164024910314407441000e003d80c0c1721170311445a400d22044095500e440009246d8010540024115484901a02c07a800d4840b515130111209103d8592b5480c0000740c11010492200d0041d0b0b6520740794044064002d20780c6030403015450790759600c000740c4080380342c640c0c000c14900e5000c4c00145001e0088441484440d6204c0350801030345 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 392794649 1250 392793399 392793409
    0xe0f01150f08030c0a1104140109150b0c0d140d09080406030b0405060f150c030301330f0302090d051b040f02070209010e1b0f0903010b010903080d0e101e0c0905 71
    0x40c05c0c010003641d510b04800f1446d480300d4206104100515070910325541c1c0d51168040908000c1199000040700481c011586a944400b1758075900c0ba02d400034840451426410b41e110100004c10069480040c17283c2c2e1a480d54500071068113074400c910344d54849103041d00107405d80362481c800e5449181058100246500c8486607070b2150401154202a034a031032400400c964412047c10f000c0c0c9010000010482c94440c00e14602c0c000c2c1c1303500f0290050440c0c0600403180c2c213040300805002480e20083c0008452090700500007000009210032005000c03a0b03a0035140c82d8158082c80101a120b140e00d4020b0b00c2c10344035a54044039400f2040d071030030845da40020442c02d014003681d2035410203c0080790842c0c0c0c00c140d50703001c130349000d00a2075591010000540e403650450a01d0503c2580be0000c40310043d481500039004507680650041c3c1490003c45145000e024540304100c3c02d0300c98408500502c0515000c0d1410b4406886e8042804012080301c240680d406126250184015440c08001a80314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 392795899 1250 392794649 392794663
    0x9050607060f0605030f1c0e060f03070509060c0f070f081005040503070507030b18210a020109020411120c0a020d0804050106270f060e01090e0f01150f08030c 70
    0x80305500162074403111488030003c00041e04030301c3d00341c4a80c41d00c42d014960f0000e0600c04030080b99060714407403000c000c81141c8841040d548140c11000c280120803524403404003868100081742070803030500b1480c40c00714a0542181100802940c0b00c40a40d803070a00c0240301d5640600307032003051020142c0c18000003070f9840ca4880c0c201c1c1600c0342c1e500006400d008060080c1c0ea5510742c0041661201a92401c2c460901081990070540b0303c0c81c030702ea0442480300300207054401e42d02440030540034840c2491615499410845980701035548503001003005a456118620740c482c1050300c0c13140c5543c05914248403030b141c01407810400d00c20400c03021054540026035954503601914018010385d84501d00f01c0c0c00344c01254091100301d440542c03103140303940f400300c0b010701c48014400702081904600301080c025038032140324541403400d441e001800040705d03035040b020300c01807103000b00c0300120403100c0358500b103565400700d56010302d150720014000a2603d4540000070254a401503040c801a492102e2711402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 392797149 1250 392795899 392795903
    0x8090f0712020a050a030c0608071b0209090c0d0b010f091509110f04080a030e0315010b030604060315090c1d070302130b030411030708120412050705030706050c0d09050607 76
    0x403408001c085544141103500a04405013400512503a24a010003110460303004907070209001500040c1010b01ca820f000c00381c0c8890341c00c0034000244507000d2040900001e40910b80601403207511411f217803220561220914400d00c1071101c550b14001c140490385100c2e4004902d40c1341050184520488001508001e544d54400001680324804501c001d09104600015500303080118000454580200e800185a80680c503101842142d60b8105620b8218084140d2801c11984c4018404011180d0141d644401c002d8030006185450352101001e1501480b41d2422280d122010b0000300200d451489008291036a2400401c42070007000a0100c9001010742c0200355000c150802d9488245440c0c0005100889000ba5242030500f0200180d040e4111a00c1c0280700e211800100d1060009aa40e04a452003404505103400d02120100da120282815915445440d00101c1c0d50f9070180600340042c11646c403166039880e51102103e040c0780c0c0c820091001e2002184c4204150b4445c40c084800c419 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 392798399 1250 392797149 392797169
    0x9080d0e150901020f100606031109241b0c031509030a0c030e0907030203060111160308070224040608010b0414010509040f05010b0711030c060a1107150306030308090f07 75
    0x2c003081004070710702403c4480c241410b10a190131101c000760641d000c2c50031340d03441c1e641c1403007411030486650500c2d100303060013650041a0300465001c0540c8a544186a00e0401d250380c0b803524220792400f080c1c40402541c0d1121079000746455016625040102d0360501801ca00141c08511f40b17800016101e003c4c2030404e10a100c18070300048201441680380c02000000281a00d4090606c000000d0003500100d4440d40454642c64580c40802400a51048100010751903100c0403419613603048a10b030003002041f40c006100c1d4184402405180310a48030303552244003550f4a541c1b404000074521801a4070410122204210500140e0590032100240c11001e0a00a940303449031000304000b03040329070300c030307442a45490004142840d00100800d0b401d030160620700d0805101c80101a121140d1240096102800300076142029000340b000c00840c0d42c0450984010655036240310301200050080c0000203555600184101500851840c0d04103000310010040f100c43c0851599030350f202805241030030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 392799649 1250 392798399 392798407
    0xe090d120b0127030f031706011805061c05010909030f08011d07021516021e210f0412060e0a022101061707080111030708010306050c0f0a09080d0e15 66
    0x22003c0340c64004011944280c039410326000d075080007441424001c0c0e02d51000b82038080410f10a40c0700d200d00300b80409900215408680c905400c100150344103151242c2625480c002a00328102d4034407400b80204030b055008142c442c4141703802402a8926080030007801240001400004a980619040c108104000351090340311031200f60314114900c0e040c42c200c61425003c000347e041e14200802c0c00580d094085403103240f00f03407052000708042141004929405a0800c0030454149050201d21b280e9a102240c40c1443d0722441d000c45034440d4010780700401007005545c0c01c000191003503641e02105440034200200003540040c40c180795034900188000480344040c3c0381d50600394803a8005003810840315a08030551001161a01d065110308984c0f9407031324990300e600300c0d92401140d10039209595101581d0b0f0841d62904000d141c003406c0c50b41d0010042c4022146420620000e020361450f64440c0e803807640c501104649800b46c4010224100181c5003501318154a45c901c48048210300a42c83d00c8c0c407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 392800899 1250 392799649 392799707
    0xb0711091302030d031401050d080f0304111002010b090606040b07060509071707080106140102030a0f0302040306090b04020a0504110a08060325080c01050a0c030503100e090d120b01 80
    0x18481c9107003006540750280d03d0030301c08040d07059030104c0e15050300840384a02603a660410012071400e0010003402c44a01000f40071f010340d006c0d070000c650061003054441e8a070304092001c03c0061400312080c40140c2c7d5500c0008846140c41c1c0c0070541d1002013252401d1805c2e0410004000e94021088000c129a80310703c00b281111105010b094003030000100306203054540d0b000348a9072941144560340465180031070208100040784100160441c042c2c0046140c079410b00001c80c0c007640168100f5081650922000c40041d80b14020308003018095000d400641c140350040014111090348494450703442e016204c405803902206407203901a843c100142103554140200b0308000721039030f1030b420040070150001545000c074680c02054a1405040350100d034025001981c1d1445500e84000205503541015400a03116200850f40951071a088000403075594801c80d81101040d1030460f0300d500034800301001d44c0d9106040d03200c84500b4a10901c810240480080c1514582c0f0708078030508000f0a4013015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 392802149 1250 392800899 392800921
    0x20c030109021315090507020a0209060418020904061515110601060f1112040801050405060a0b030c04050702011506050d0c232802010204030c06020604120806040b15130b071109 78
    0x1d00c4440c1060115142051000752509042c9c03804a1042c621301000c00c2480c280303880380f2850f0b0f04400300c3c0610000710503002c0084412004008683e0300e5200d0b03500e100d21b607000140ca0002000c00c040c3c840403428000d2406040c1103e144142c1c9010340c4410010800e181e409418103645050504208005094610030710f410407030341c205100b0290000040001d0b8035081540960721450064081d034919894600d158020344001d107810320351650255102c000c0c289020341c0900d81040c180c0c000017410031000c43d01200c1681c03c1341c1c003c03400b003840840d0044c0d5a0220f402100402d41032450300305000501c1c18490b14146100f128401d84910f40410b0912101c2c802c1e0000d0b10580080c1c4041c0c00d0400442d102c020b0203580f09010440d0302d2070741c119000864078000141c1a0146500001c84007016064010456021200800c410340c004d40340d46d4092401d454580b42e03441c40b101203200b0346668802c1214000091542680650540d00d02000b55501042c48010100350725002120752280c0b43d01c038580140c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 392803399 1250 392802149 392802191
    0x108060310050c030a0e0f1b1206130c06030b090103060b150f130f051324060203040f150c06150e0a0203070806010e100309021519020c0301090213 65
    0x78015450a01441036002c01d55015600c654002d00042c4105003224402d591202c08480002c21140e0040c1519105141c064105011040300a080614910481404185490010b440710542540030000040501103110000d00182480303040a03c0241d510f4004529001c07014030025050f01d40e110300303d9529507500c01e0965040342ca07158905c1d0f141c08100104e18890760101115400d4800400c0c4002012540c00e010303035089910082098203504035195003c8003401d001403103030700114048080ba00b40d401c140740c00d89020348030f40d074000c54856040c08002d419240c4036402a40c0c40d2a6500e4481d0f0b0760503444243d0000040c1d1092000ca40c2541c0b071005910030419a4201e48a0f140b980000c201d90440f00c0e5025610034001941c3d07200942c0c90380c400644698114203811500700408441004203a4060780024803918400b0384010041500106541400d802c281001c0a48080171b0b880142601c0d810070a00c0b41c1c5140c12002003140c0c180e5503000401800914044802064a0f0070300c0080707609460a42c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 392804649 1250 392803399 392803423
    0x1020712050f03041707050a0f03020402030a0e1906060e01080c100203040f140910061d03031606020325120e3a090e130f05030a0314010e100501080603 67
    0x1207807515103544198030450071710120203409100e54040002d152900c030260000702c40c07900000502c0301d820364082c00065131008140850301c5403100b40301c400340c1d80100300050200c1c0746a02002042a103620380784081e284180c0c440c0041e0881800103008049000c90042003402c0100c1e409008400d6251003a8158025640f0403060042c501d800054402c544c3c3c550b4420707a010865000d151740d03a843d062020713280ba00c1c0c0690400113868180384464082d11104010042d0300040c2140d0514400b811030035000d00320407034101e402c0743e008004c1c85041d0075542e00f603040c2072003400503000c903600180900620002105c3c40480007180c075142480c24050041c4102c05400e205101030010320300000e240f0391181c43d26001200f4a40e070060b02d000c10194451400e190907aa088400b00801e9240c0306039202240780346400030784240540311000400118204020035240c0307820b03100400c2c41243d0403d00c08414074168890004643c1032020400b18022a1038003600755003003402c001a0b00d464000100b441c0c145203a0345 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 392805755 1106 392804649 392804653
    0xc06020d0e120c042f04030812040c150f0e061c0c051204060c12020705060a0e030d1d0105060f130b040b04090b0f060303040501020712050f 62
    0x10341074000145000b10f6030020349010004c1c0440d251010103215204040441c505080116480001d819004a0700182043d01d1134032202880c2c4205414201d00600b4800014100a0b1620001002d0210750301c00740c04a214400002d4201c500c0e03841c110b070118402607005500ca00c0c0c4001141c24030380c3e020012842887c2002d00810140980342031210074000700b1300841400c981d001e40c1d85072056000d182d02003080a480d0310060300f105510108511020300400552010540000d900e03504503640c0000010342a050780031150460041c1146107503d00e040c16807003541c04107079100036550034140034001c00c9162142401c0150810207001d42d00d401407006110700007074034803c4d0b00c040c000303c01c060000b00d00c00c03580303000140441e0545c080803106220320105015400010701100e5074801420350065103040c0c11700c030010f55100710501c11040005484481c40c01000700c1400080702000c90001 = true := by decide +kernel

theorem cover : BRFrame.Cov 392625899 392805755 := by
  have h0 := BRFrame.cov_init 392625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 392625899 ≤ n) (h2 : n < 392805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
