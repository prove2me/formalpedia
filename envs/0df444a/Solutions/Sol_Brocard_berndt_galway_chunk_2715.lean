-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2715
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:50.999849+00:00
-- url     : https://prove2.me/submissions/d151b62c-2463-4092-a8cf-72429a81bdcb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 488129496 ≤ n < 488309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 488130746 1250 488129496 488129501
    0x10203090304052d01030f0231050d0b07082e030215030402010806090a0f0203190b01050a0f12021902060f10050f040903030902090f01080c0d150504050106050a09 72
    0x42e5030f81661185200c8120f180c5060502809110702c0d03808044105240000d98800e81000c801c08144420140c10138668804402d8082d00a090010602a01e800c11080c4604990340520080904a880e0341464903562518009007800511071410042c20100041b000040325944200384a40b0610440040200303042845521145000507803042440d1690b207003501055108903031059606a5841d40c442e25540306000c0a01400340602c42c129031254050031000455101031441060150781c520305040f24070003010111903110101c40c2c100301081280101c407075006010300412a9161901c0310f0031040f0952000c0003806045501c0002d0820382d07000000141d0300150781405503c072009102401c1e00d440000c8500e031442131182c5034014200c0c10011101f86010b9001c045018000e060120b45034055500050b20007100300c881e000010811401444901010820030031501401c0e40d541034803045035240c4103000f0b801900443c19950701ca000290800000707402c01001080044e200d030303090b5515511800301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 488131996 1250 488130746 488130749
    0x2205070605072f0409020102030903030a0e04050105040920030115060c050f01050912032e090501140108012c070306080f0d140f040f1502011a100c020111010203090304 74
    0x4020000e0718a10010600c40308201103550205203c0030005185541031002800205200340d055000c28401d81843d41c078141b004000540700d0b0750710180c0c00400b1008001c200c43d41a045170303002e035140c182c00c440040c044000c04054088590003040300d00c80084006400b40600d01340200008a01c41800102c10381c200c400c0642c081c0c499000da411700c111340c5d91820708807001200c5854280c0d00a40d0a0300c00011581c00035500000c80c000b0f1845810308800a0300b110040740c1c40b28040b030106000d41001800d109116442c0901201d120210a603104840002d0203010103028840e40704038041034000d514518081c01501c070101c402110100d514180307002400604007449804454090b010005115020201d0034450000d0346072aa4004414a100f0710f004903040804a030889500420002c103005507804000070040c41100b464000c000c5013580c0090a44c6e49000481c0105100d44482450503907a01c00080756080c4246401e820a40c00c07070004a640d46074446001e100c5520020a00c41c441300041300500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 488133246 1250 488131996 488132003
    0x71b091a041406131d03120c0a17180109030f260408091c0b010303030b0904050c01140f0c0a0c080d080c0d090204050f070306170303220507060507 65
    0x149444000060100340d801d1600001840c5552900140f02031070122121140b04403411000030f800c1c5a0080007070002282c010061185038004902a008028071101c1e20340c0c00034030502c00c1030a01600c0107002d00b02c0b864880000e0741ca500b013800014440e051000c0010442c5180c0700007070040f20003500340034100030481c500250000c0c40d00804081c60100f0105480203e001541500240766195101c1000640201d00417a90015142c00c000780050417401800c094540258031280302d41d4507501d0f002c2d0440f604606e18a000c1e6107040100710201d5000300d6102d041d0003080c06c003400c00842c0c0c03c103800d120b07100b0300c0b4401042c03500114010b01c5002c000101080c0c12440b500102d011280c642840c29600c031181d6a5120000c0c2003400011070030100c20020388011410346201045c010a80d0f80041c040e100704a55102041015408101c00f507030303040c040c0307070300414840742003201f040b45c1201c0c03150710ba21004109410680c0003140315103624184410507688190070200b41e5030010788401c0d0041059122200a9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 488134496 1250 488133246 488133281
    0xc1119050c06040501140c0c0d0305040e0a0614040b041e090c06021204092406170a0c0507020613170706020606010e0a1418130201110105090a08071b09 67
    0x15041c038200101141c042c1d41c41612601804031001c01000001c0e84210314401e9a8002c2101001154580804003101710348a501d96944460801c100740d032220a0052004450600345a000c010715041c3d1900020314441c269008101080b010300490090304200750342d0388a0b451354080c8070600070002d50000241e14420000d900c5c186030354907422030383c07002103442010103407004102c100680041079221582c89240c240407801031101074410203207410000d034450310200d06a03c0002945d004101005580440d0040e41000306208920000345035009040000380903010014007040c00d0144c11340a20003c2441d600804042e545460b80e05031a440c403481264054410400810040d42c020795104240c00000380c0000c040d98038243e85031464841c540120358004405402c0e141010509440c020f11500448040183c180041e10004112002184000403942d01d1301c42031000c0c020005c50105035040d0002d0300151940c006091501c4040590410340164040341c01000500040300e400c04200814644400c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 488135746 1250 488134496 488134513
    0x120109090b1f0306020f070302060601090602100c021c05120f011a090f030f010c0e030127080f040f05011d0f010f030f060f05100203040b09040c111905 67
    0xa020648051800003040e01055000107802d0410030b07400c20700702c0d415040350490060303a6074454400300c1c0d01ca01c80300c01103064000344010905804014090f0420340030328004120074a4004000d441da0041624010406d480d030049504541c400c009003040440a00200300d50240e1814020788154004450008a4968040082c0d1400c52154000c1c0c12a413210304415940700184280401d203900440c401907100a0070b0492505640301080080341401e4500d00014501d900050302501c0e50911102452107681000307004c266a04c0c8041c5d490302038031080700383c0719550344003450034088902aa0444041c0300c40085030014108071490510000c8420030389403c0151600f802c001c03c00003000e80403c5d50000c0d11401c0d61042544190021250000a454001141d803a0481c81c82c00365131036603000e524100c0d0a04024030207442d06120003669410383e0b00007189447c1c0741a02c960b046001e0032103918030641d81c0301c1c60019454000c0707126005a40d06002039914000c0440498054000d00c4103088d070f42480f94400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 488136996 1250 488135746 488135759
    0x110f0a050d0804030c023604060b0d02030a020904050a0b0a1b0507030c03200f0303060f030d1b0c0e0a050405150c160807060c050a02160303080c030a0b151201 70
    0x25807400f840d010b941d0248410115006d00484801c2c010803400c1581c00307440040600007891340075a07070109440b4800f8030141040e0400a0998002c0841c841c480c004802c51040103071740024000c2210795040c1c0d0b983c050b5680f542800c500342584200c018087c003050000300802440d90741d1007610f010701500d6000800d1460244200c6940c00b4a15005012030800f50300040030a0003076205020180782522303030801110340942c1c40c0f8100900c0c070002e61490352021090200782c0c03800100c002800e002c103a008008100322020000c00421000d6072030f6000b841070417503000c14022804003050180805401d50045410424004e4005040c200c40903191401070031000e10807010b0002041d402240180d881e2802c0054104110031303103860020301241c50050030841500001c01c14018982390301410303261181c031803500b0400a82400e00710040190b0900b4030301d00520000b500404400d4100704070100c5151265034000101c0024001640100d51100c4102d60800203903406d90010804200c00183c0e9618a990303608 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 488138246 1250 488136996 488137007
    0x904140f090a02060d021305030d11070e150d031b111c08030610020a0210020a0209100b0412151103010501030c0e030c061c02041d2a0a110f0a050d 65
    0x10b40298411010810b906584007a50041c0c0010824900702600d80daa685000903e031580c69043c0c640400c3d4203103104581c803141408200300411109142c2d025602d0428211304046000e01341091255203618025000d0610440c01d40c3c0c40e1940180d00d20202c09036a04203100e0900c4200d00480c07003241c12003000c82d0740401c04140d54001c90340c081c0c40c0c0783c1103844071000c1018841001805208501c110052440540d513105420700b01044a500980110704282c014080700c06402000d4984802405508001291703080701128115810081d281d500c01e04146848540b0722250186031103030601380040082d00e070110400850485409032003c1110580f1190159803041c0c0004856905801407125640d883c140100209100e000d08241d1000340170940c4054022600940c200c107410b2014039082c102424013072203d458000d184000000013200d0078004241d121030112402100110000c1000080b1501034883c449040310303010705890088034088031090790342e80642c0c020b03140c1c0c0c410f4501c2401c40c01c0c01034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 488139496 1250 488138246 488138263
    0xc09040507031e0b01110106030602090f03030c070504090c0503010516031d2104080f0303061507050a020d11030a14010b040b011205091915050a110714030904140f09 73
    0xa140001d4219880303e501d000929295805074140b0002c2c222480c80a4000c0c4103000245100c1c800040c5c0324040031040c800300444c00e001c4203020b80d00801000076082d000260410807540f04440114442c1c2d03481c80d22140806035640219059820036052000c07201080c03e0501402010360307410800d5008904003051904113400315480c8a0708011010a88024034004043c40682c502170090f240c155604440b5140040340c2803100c0c3c142d000441402700c80c0c50300d030761628030142107800000e08084441d1941510340302c151780001d20460162a1000801000c0348c0403518610f0f004054a10780d040a0038400210381540481208039403038540e4140242c6868803803030400300d07010307034644155118a04281d80240809860007900d403141c0d0f10008901c0c030a1088652051380700e121400464180d500c0e05806135840984103610283c1008400d5442c05c1d100c0c0c066400954019140840100d05440c540307045200c1c21050a40183c24110105007600c41c58503036078020507400d0b401c91056615441c0e42510344ca0350 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 488140746 1250 488139496 488139521
    0x9020102101a040b15030f01030506060a03120509010c1205040504060b04080601060c030e03060c0406020d0e01082703040b070c090203040b15040b1008100e041101080910050c0904050703 82
    0x9240c02e26215042c1548100c1d108140a4440411602d107502a030f030454104035203401003c00c3c040e0050080100c20b0003181e41029040d60001d00c01410345e500c00c1403110702c0c420303140e041060102d402d1019a01c00d0030240d00e4107421a1103507140140e01400100306034458015903005034104680042c0101816048504039102c0401030001d43e42049822a08a200d140040d0200140d5440d801610f65080c0655400b030b0000c81340703640d521407a00c04041e06141ca022003580910481e21441c3d48542d800c1065194009c074000c0018640e03e8451815800b4401a0680c41e09188008103001c40c0e103201c000020250140a445240422aa1082804181c1c4000c6800400c8450440086001e50f111600300b103840650040c408241101d483c000f0070320030142000070f000001c5c015402c0c0004054901a000060310380c03005424642d01c1e16803115040900c42d041d003541040303004ca00084040c1000e00a040300359040030010710450500c82c200c540940c014080700b606c0343d40340c48080b98405020344200400c8110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 488141996 1250 488140746 488140781
    0x1b0c031218330221090306220602030c031e0405070e072001020c0f0610030b130803090a03090f0b1c0615020708010635070909080c0f161a09130902010210 68
    0x90380f040010640851280700702303c000302d2200f4100025144e0000d9442424100c5071180c8a2903d800d00810504010105502c1d24030740100788070200b40c0110b80b1000303407904c0e8140410385440b5035108441810101c010b00c411108407185c0c80310320b00e9040d00100300f503100d50400c6521841c1810500e40e152041603c649402c0c0c10031101c1000015001c000301c03640b0130b80d080d5800540910a032503122650340101c41d0a0115001051680704060300708a00c0005058031507100d0402d1818102030141a104a50880c0654051100d50904035001034028201416082402082c40e05180001964500c10743c020000c040d400c202021600d01040790a400402c1d0403d04200c02c1000c0792580e02d00c04046410b03100d40d0700d010780c9501260052142c0100403a003881041e020b0740d5072985051080c1001c60401341407406070006502400d46004140203031090300d10941c484040300144406071440c51090449880d040040b1204003450620160b01040425000380c0035100700703801120602c07080707079000c1000180004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 488143246 1250 488141996 488142001
    0x501030227011701110a080a0515060a030207060f06030c0609080c0f121204122009060108150d0b15010206010b0d09031b0c031218330221090306 64
    0xf244100038954440c10000441c80c4e40c200545070254004021800071884410901000b02d40a1107a264005402200010130121070b01c00284c00d80b04000c511030403d81c02003040c405000a50348403140e40d030458602000503035503a1400b40c80908981c45010301040740359030b0002d0f000c200454800320071400200800c882451072400c0144d4540d00100c8000244200e40072903014051240060000e021900c02c0d00301c016400e4940426a900008003882c0004003101d01c443c0c007a12404919900b04109080c0550182d4030070000801040521490756409000b09601c02d060242e0701c041c40f80a085901c2558661070140801a40d45010a00c14140640d1040010b10540c5643d03034000e11406109280c45c402490b40c2141c0d4440207201d041c03040e504144004c00c02c00400c660904030741c80303a02c4141498000c1440f4040446250300b0a84a200988041d1018038104410140d45440c0d00d0609803861000001e01c04500a50742d5082c4144400c20340c5940352840c410079800802e961788804020000c0c00b032903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 488144496 1250 488143246 488143259
    0x408010501031208130201021e03070b0a02040f08010e0304060302031e0703051012170c010e122508040e280501080f030c0601170a02030a060e010f0e032d0a03050103022701 76
    0x103001c409d04041d25000a0000000140a4924450003004200c4000d07858508111003401c40700c66590149180fa8035018503000b02e0007022003514201c40c0203080040c1c80381d81b03850f100d44120340700c01e8032000c040c0c0404040141c034a416912050107003210b01d0040c0c01c400c1c0c0342c40d0580c01d602d281a0001e0b200801c24030741422040c890314028400b400390f000011480741c181c00502407500c8580410074038207a40103d0102c4440c08a403008030340d1986840d9840020707140648902d0300c103100d0390040c401c410f202c800008043c3c0e0088071a240c4141d1a110f080e01b80203001001c01d0008081c28042c2070b1080c01954500d000600002080c1ea03034030f000c06800741c05141d1a141aa54102e5501c0c100f028481c00382d40da5a20140c8d400340054680940030300c10100341c455568000c00d08660018240d00401e903c0c2505408032601c00100360345060072980c64031031014501c1e04580c00041102240f41c201c003140001c0c241d88095050304998102d80c42503c0e0b640003c000c0e00341810241c144214001d104804840040120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 488145746 1250 488144496 488144533
    0x3080a0e060f1f080a05010c1404030f0503132d1503090c0f030804060228030e040902090109020c0105060d030c020907120207061a0a150f05040801050103120813020102 74
    0x44200340f804200d800a96007469003010a980c4e00c8055160003080d04881070003028007a0900c14601468a01c1c441e944070b401001d17160169001c0a0000c0d24100c3e103440801c002041107070204421003072031601050741c400000d10154540d10f070703031010024104840181080307150f81c1a02030314104002c441400841d1041100101020300096402c130304116000581e0381201e407100c0d0090340c01041040d0b91141040704c041cac5808440c0c0d003103e41c81d403400d07103076801f0071401c2c88a01e80c82194076190060b01581c0583c0094060f0250a0f00039600c42d61180001684290039802441e58900c9040203010550b590420020f0030240c407800a808240c415400c64014504022240d41c031403200c3c02d1400c20b207070584403020100e1b0812107080b20080d90364041c0c10440c498051510100d03c00840740644414100880c014818030169125410301003000340b400c03403a034090f6060b90b01401c5a400200059a5641004164201c0b8090001d01140e405008a890121a5a4012000364040e0010940c0080c81c8490064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 488146996 1250 488145746 488145751
    0xf0204150e100503150f090a0e0706020c01020705040f0e0115090b010c02150306060c1c0e100f03020d1d1b1c020904020d1e0507060309150c0509030d090303080a0e060f 74
    0x1e0000e01b001c03141c4800d40d039640e280c40c00b94405c2c600018800817418261450f00044d0380000c015540203800d10031151ba40010b44105070740040c0e4001c01c21600c003007a100090048802180300650034140810110140200c0480844039032040502c03070740f612000150b94900d5003c4011f50084400076a46005000e5540115040703540540907a1030b15a9984145003031200306030008031120341e080e040440e0564003c0008501c1102110000225001505d001e0038804005416900785500480c000044084551104054810504025509140715034802e6183e0805100c0c2540c030180041c107408460030202074800c40442c04ae08200d01c46841a02000b404180091003207a01041d4030465400040035440b11001c2c8080303d41020403480003520780f640c00c00600f508400d040510f03001c0c030341005c85c1503d41c1102008098000008101000100403176940c8113507034000d5003511900c000d4120403580320303070340701d045030301030f030350700041ca8448030000c1054031021038400182d980840080350100448500d89034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 488148246 1250 488146996 488146999
    0xa030201231501020c2e081603052a03040c090e07170a0f0803150f0d0b06060708030f250f030b010e09010f08010e0102030f040311010f0204150e10050315 68
    0x42d0191101000a50302c640e040340c0b01b0030018030480000044a00400708840182c05a0800c1c046524000d020350800020b440c5031a000c060300c41020408044001f104050b4009204042c4507105406c00c1d401141ca60060720200d45c11410341c00e000620981c0744c0704036154180b50001500c002c5190409250b07081c000e00c00c1e1002ca078001c03c1c05070350001c0c80b040740620500740320300607903912481d04040612290481132300385400b910720410108002d03a1520200b00c0c10661112802e0410303240c580124409020302e00004103401c800100740300c2840d10051200c0d102e010141501c0c0000440c00c1d44200320f5003041f02140000c540311000311003040e8040c1c0c2007140140018903100d580d001040e00002c44d242c90030707413020900030b201440030b1000321000c1c0103094101e40484000e51440c107055001c100c24510090000d0b0800880c081002107508087d0422039405260a1055449988a00307404650441c10b1402e18041100e0110307080710750901c84402c46542e109a241c0c5400c507603440300200031045101c2d00c00c0c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 488149496 1250 488148246 488148253
    0x5090c0c07060903050607020c09130f0f210c0503040e090a0f03030f141308090105130e01050f1906050d09020603010306020d050603120d0b0a170a03020123150102 72
    0x92050841000518010190b5a458510709407550906034144240030b1306110464100000c20304050b01e603403460641081884a80d4043d080702400c143c401c85004060040601f400031007183c0c2406817585021075480300d101c401c0f000e01ca80d401c4013610402c5c3c500341e00500c0c6070018031003003120516210b0307034940c49450041a12089011507403000b01d0030409000403001701c0d9484e24210300400b054407401d0902ca40d03109094074241412074441e01c0d0a48440ba00400f00d40000400c214180d11400903208680c6070142c640b08125102c014000200a09018107400f516141c8801000d915003140c0c0003d00240c100c0101048508140044405503c03100680c4c2c00b554640c80a80c00588a0344001c5009600804005032100c020340c0c00d0006440014000b14843c6d4040c20f403201c2c0f020041c0c8211038540e40740d1080010142c1400c0e000c542065004d40c0500a90700000e65218801d11001c5601003246209600030000b4000e13005001c041621080c04200384181c000c00061640112007441c00140300050049 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 488150746 1250 488149496 488149507
    0x92a0c0204060815240117070504051509040b0103090206091e030706110d0f0807081905090d110d0207031e05031603030b040603020d0b040c0510270f05090c 69
    0x151840c210001001d85030004140d02040500c4820500b04038428001094044175240005c0c0028040312003003100d039022030001c40110760400c0c01030080364010600900300100030030b2241d29544c56a00135842450145080005681c09036201e0302c6001402d940c0106840e040a9440742804070b40641001d51031428014113030030410030f5030f04210440081036107640e2804610010342c111401d00200d41d00c42400d101c1d240020180d00780d0415050350f0700526924064800307640d25940b007a000349041860003070451406082c4103031410081196100391044d505e5018200e00302c0d0240342c2c0d0b520300c0c0c2c0c0003200068015880900003c4c8918190746c0c003c6c505500a46003180058840c01d0441d403003030b0055900c100d8a203141c03804142d01406070329a010001c4804104a61454000c00e4880c40c48080040c52560290002010000c0c5c55418201426011348401c600400020000d800c1c0d10801000a03008041030080361041e6544420302c0c2c0a403410002d40c43d00f042e240c82d00344140c215004c0d00d05103030b00009004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 488151996 1250 488150746 488150759
    0xb0a0903200709060503060c031b0d1d061503070501030e010207020a060c021201060f09230c0406170103170c0f0109050304050a0e060a14010c0204021201092a0c020406 74
    0x9040e0503070035900a85010b0380360080690803202d480d13210070b001c0e400c80d8042045000d80d41d0282c0358090681040d520003400c2000b45104c030b520072200580070720b40c81e00504a031b15440481c58000c051058904984403620703000a229080451215043c0d03065124282c140401c0d403003600f00c0802c0d044803e001504003e4613a0025030807000541003c0001001a18810203500e03020304a00010090180204051810000c846420990a0150324401c52b01ca103586500031b0000f10382038854042d200e503c030074241081243c21901d584140f040b078002403415010448840c1111510604032503024203001200604495944940e8020740031001e041d010f000c46141400d0303028060660b0b80d9114501079aa550b040c04100900312030300c0d800510b0780c0c0d2014020030001d03895102d09031084d03d5851442c042c0a034104401260b406171040e400a4000380007180300a42c0480c050b030b0352816211340c6d000501c40484880003e5403c12040c0d01c0c0d6250102c1901c02101095000d21001c1703507500d0019001140554941d00b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 488153246 1250 488151996 488152037
    0x50403060f0903020706051224030105090705090106052106040204120309030201030f020c060402010c05030c03120103050c01050307090608091e0d02010605030606030703320304030b0a05040b0a0903 87
    0x10307514001c0d60726981054109075040c02000c0141c2030504145003045601540c0c01e100d00e10092034410400c2c490302e15548019982c140d4411601d600800074016864003031a42516081c080c0300e15800b515150707001103803090141e4140c6405000142c1c1c000208000d1440c2040d41d040081c0400d81c000f0342c20400802c64400305608070303c1c214000c4e01e0340c1c030b1424503610004040b81d00c96402c80c01c2c15481405101492030020031484e400c0b61702482c2c260045942c0d030400f14254400d510008415100009020130351920110900d41281d00410644003210b44042c0103407007501c0704588400000d2a015418005213018013603c503009400c4c11700700c3c3c6605c0b071100d8208100d085030b0030f201070455111603429185550309010714005401c0542c003400841c1000c40c0802c1d1b64072528007000341a40741040002580071404641000008110102d03c42c0d8040c01c0c0340c1c03a54607584940400e032580161000018090301d880d010f114000c03640050303000d45c241c1e1041920401409010f41c2201000b0841d0450344c840001503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 488154496 1250 488153246 488153261
    0x15212d071b0809060702012d1b1703040c030807080d150e07031109090f01030c0e07020a1403070b0f16020703050c04020a09080f060103060b0405042105040306 70
    0x1546442603030601010242003010084841182810103940d1000020721034815070314a042c05903085511201c0d01e1006031401e001c010340580020289001201c00034440b00f45020f4680000e455132181e45e03a5011440790081e0003510701030890340507030100301007142060009550050084407250400d584039520303102a648400b4050324108800716501030b00920b80d10442c158070054103240c0d05040d242480410380d01d90002c0c8507109042c1d8031458440501c10007001c541060100074840103207442c100d00d64445101080c001901c0c64846d01d5000705003c4a02040c184c0200d0298000300380900c0650303520000340c2d04007488150140018040340d0001019000b00900421040303002508524180d6010001e20301c000440c1d808640c403840c01003010032804104030407001410b036805a60382411540503244219a50310103a00c1344180d100c141e80054010495a05880c40780d1003d2102d02011820481076500550340906481c4140070260072503c280e65081010f250b260034040d0400382d403501e0b00380c2203170040b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 488155746 1250 488154496 488154571
    0xb1305240d0c090b0715020a050c011b11070e0c0702010915110f030a050702040e030f04030807120e06030f0703271b06080103110d0f050c1521 63
    0x200d60510040ca034101e080344001d4009282c8142c209241a1688404c04090704804a5407e900144660445200307030b0488040f0101d18000b8003501074518030500780041a17844540c00500400303c1d40fa1525400300d552812100c04801c40d900d5500e894070748442c540d0000408905000340304000280c8455441c42d1a003591a0549485500c4e900c1c003401c00b81088222003001c64550001c109100d04507400c0400d40340700e29019500010302010f2203036428510b1203000408960b0381c00201c1c1c00001c0045140080c96004d10402d9030710807403000c0d4002540c44014211640d0362169042c000038030183d0030b0880c1284c2c0443e4601d0301182045040160301480030000d01403800200c1a43c4506c41031001500707035404460040310984905900e0718100074820038040c0001005035400703140c4100190398000350b41011b60380004600301c2c4d0351164906036a0b104ca654440c2401362b5442015020a18110300507110701c078443c40c100340502d54017201c29120346072009292010489540c102b801d001c9006a40c921100e420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 488156996 1250 488155746 488155751
    0x1202010e0d03060f060305060607210314100320120706090b03011a0c0307020303030f0610030c0f030b010207150c0b0a09030c06020304060f050c090a0b1305240d 71
    0xc02019041c01e80011184050608000c01001800c008044003030481740b0340e140c0080e841c3c45a20001e4854402c000b405080100404404040c0c003c459211102e18046034a04101060082c00d0005110307908403141c1204128070001000883d100700034081880c3d440c514266105210400004c1c0303001034410b13a030080c6910103d4144202504011204090480320701243e00755031505d09030340940c900340d03440500890700c04910041c05482c2041500e04980d80142660b849180a044000307000c001114820b101e0680c42e8015a1100c1c084c1c40f03000541c401c181c0d0b44500c0c00b54118003d4001d0b04a6008483c1188a443c50001e4034035942e9030880e0385006c1a5a603114200000c0c20003206054014044031112031602c04003000081e0440c035404000b540c4040301584075695400d150004020b4400094422030410080150710a80200103100c81c0004440c80e58059486401c1c4040038003858148000c16100480c00380001c2c80c100100303c0100080100d4950032400e03900f440036140d000002071259280c2c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 488158246 1250 488156996 488157011
    0xc0b071d060c06010311030f0f013303110f06030a020904051f15030b09131403120c07290103210512060102011107150f02070506160c120201 62
    0x18440c405a2540c5108503403041c2010120b1007820b86a5406120080802100300000c024984003071101c014890b00d86000da03800b100c402292640a025107006c0600fa503d851141590991307004840e0f05a110000d4020704c07101401d640d14002007804180c415503002c629440c1c1e038070b0165602d8000750700c0348c001d50702c000d80c440440348207000585002a15401c00014075240500030366909031050001c4074205158580d6100d007911041c0d005010103030318030382c2292100c000c118038421710b85d0202070114451206c0344160074000e10805c0c0c4078040d10307808005550074000442d00500001000e844800c2c0035503441c4004605081c07602903072407000f80c00c00f07418a40042c0104240301011240301c1d504138001d02c20903003504914100070b10910a007a0244222510b0a0100c3c505903c00d51000b8401101c45aa8550318045818500c030031034848072080c1e14813400c180d0844008a168001d44851b01d610100529042d11500282100c50303800b0f446070402c10840001d400b010950b4900d100c040c1c920660000503440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 488159496 1250 488158246 488158277
    0x61d040f230603060106170c1207020606090c03060a26011509060602010203040803041b360c05040b07050c0a09060e09010b0a140307030c06020105091b090a0c0c0b07 73
    0x2040c005149500c29000a80101b00e01a08811040c91100f800d040e940d5070f0750390300611060349025405038a50180c040104000c3c081da000034049000fa03404441c4500b146d0341c0d0105d850f8003840111449604011000c10400529016045a04640c880f0b015054000fa040d90070680c2181d07070403064510340380c000364020041000c02e8416400035140c0c0d4030082d450b52800d9110b664103841702800080100b840d03111070b503071031001c08000e4901070f084000101c400d12845010441d1806c0704840c80c80d1010001c540f042c5001100c41c410400039080c00d40342d107030406140c10302004190f0440c15003901c0d01e0080c0e9902c0805030f6130780003548000d8603a00b040000c4141c101381082d44800d03c010030811181e8500311040c641c1e666000141d0702290f5200d00042451007030100800e0030144680d00040110800e0a40450096010340106101d0100c3c0c4046680307090390301034071440305c440e107040e056048003400011400b01582900f00a004040e00d0520b845a071505588107521201c08075040030020f041100001c105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 488160746 1250 488159496 488159561
    0x11401061e020303060d020d0212240907350d0306050402090a05090a180c030201020d0915081003050a05060109180206030c0c0a0510050702060a0204061d040f 70
    0x41d10207903005a480c807229920065640d102c091310a510511078050341c80d0440d0389040e05e850459a000c0d141c0c015280d0754011196a0f2045119282c031f10075010305039101d05078000b41490740314201d60401800b000d40303400340070880004131415800000018901d1004281074807a08041d016489c600140590f5402060040440c0c080350489882140101f0206199036110003c074810f54004450001c0c894a440d0810f50041202029040c00d203016002e5900a00a640700c060382220b000303800743c401243e0320701811030b0300d01114064103115603200107030346103120700c0380d500c0c2c80d4009418402d1a282d40c0c1c0303079141c141c0b6028a00a00b201c20f0381c0300c0380041c442c6205074000c590039036003c111020401c840503400200c44d40130050003e03260350030200e00c40c24882c1007002203101d61a0000c080da03d02e58a02140d41c400b42c1000c81354070000d84141d8012a42c094000d200321400c4900300e1350b800000895600500c042100c00b50311440e4843d44130a000d034200c80940c842c21185101031265402c0c525200c0396201007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 488161996 1250 488160746 488160767
    0x30a2a0f08070206040212030c0111040e0a0506090a0225060c0f03020306060702010507051018060b030a1509020a05060c0f010e0d14070314120109051305121b01140106 74
    0x104034100741032000003600000c2854029a04403003201c9183c11142030349283d07024102040d0959030030045070b1007958030720714010001e48d0811101840c0941c0c80d001c081007a030340241d503001c0e0881040d0f000240450403d501a026a4205050004070145606401c54903101070060980319280d070b600804171401d8003c165401c9100b0b441c02c0550562402d400000d20030f024040000e41404000940e5004202e0244004407203550441820441050030308413520001d414910100c90341481c0c0070b810111494005030041a140d401003403d2481040a000f142c0644070307100c0704a80000f0380300c10124484d5100009000020484001408404d100101d4503082d1030fa03504a005881c0c02c00410800039a510203109103006114905031a594040c03854202d079a4102400055013140d000309214200b200320b01c0c0e00904a0b0000134042c07019465070440e0440455018000030710941c0042d4016075044420000750031009214038005521020408099081d01c400c0c4814a0303035501d07503000621015410070607850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 488163246 1250 488161996 488162027
    0x30f06040507120303140412110303100302060918040303050a1121060102100e010203040330110702040f0b121204060503060d0204020c0a1e020303040506030a2a 71
    0xa5051903256251180520b008905001c002200710805040c00f940000c81e203d03000000c2500949020305154640e4120701c200540007404002c0680c1900400105880c09010b0300d0b00d00307420313452030369003041040c4d400059050b400c041441c0c006615001421000da1044d8085e07100441c1a05c2c0070104402101c960068003048100b00340f1003100c0722007100e04c081e40c900c071201c0c0410110307894040050380b824140d2030f114503405040c143c1010324104190069400355129860b03843c201d00c0e011505800b00003494980d4140c0c42240154110381c070805400090440214000103450405690081001d803a0b45103030040f05143c80e48c000c2c0c030f20780c00c00401d14804806190058800a1860030000c5164070941c49000100034006c004624a40c3d58101d00c0da41190380104115980c5591118494807014511025144040c1c08035068040c511301400e00c0c00c4095000b000b03949014142030400941c1d400c0609003030326241c3d0742d03030741d12a80c2802d00600b20080759840d031001c2c18040b002d040007005004883c0307206 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 488164496 1250 488163246 488163253
    0x806060a060512060d0206030406061a180f0f060c210c190203390301060f0e0a0902030d0207151e081b0a0e011e022806090809030f 58
    0x8000c156845015940071440c072030b83c0410300740c403150005203410034200300280d48254004184004c004589d4449421a842a00d010400e01d42d0195881c00a0003200d1042c4620500316a11180c1844e100145c01c0c80600010b11010607650700b94003180b8a42c0040741d0300b001c9540151202040400d200221042401055039154074145034040002e071907505004c5500c01d2803655030682400c555007840180940f20807100c040340001c0c980b030301c030085217108030690301c280b034805135a0041c0d01d00b818000c0030141c0c0d040c4048401d1080c60022040c503180001405004441e03aa00c450030010394062205580109456008200d440c1c200708245244043c140300c00414000d4001000000300c82c1080840d840c10703583d0811030001d41d9900485e80d00c066800a44907012039000030060402ca800c4a50080341d081e0070382e1050065a92004040704c840181c400e12400340e0b00520340412080801b00c3c00c81513a080329a0203216500050340e82c003042c2d03034401c8070031190b0b5800414044424201003042d004003c0082004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 488165746 1250 488164496 488164499
    0x30b1905010c080d020705030f03060907111e030409060b091021020c0a0204050a0509070911040e090f0601030602031801091505060a120b01090c020d020c041e0c090806060a 76
    0x190075641002e100500079403010400c0034403031850b541503c0d0080d41000640c1d40e1100c81108442071070703000b03c803814070665041001c03841721403207540302c68000a003c030024101002121002000d4000169071848980f204010100d9070403004e0107408c00a0135840c442940f2400090300704586a140c00500404200e45200c0010710281e600c1d01d1180c42002c00c120059880c1460b05400c1d0421034026006500141054103004172400c0541c030551207481150140d4501070780369001c000c2a1780204c048a405c0c00c10601042c003110259410494000030f000d0212411058a454810308041d0240c6c4180d601c41d034040200700101c40d81d503070345160240c0100003c014544071944e41038402c0c0307070741c2024a5001d503841c000112076803500f14003000642204103500d2903900d11840d000c40010400d0052030403050800c1c240c40ba105000258080c5841d075550080c1100c204000c0030b00c4010040140302c442402200100402e40e074066118007444000b03203680c0c8480c114145004240b80001c0900903501aa003007100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 488166996 1250 488165746 488165749
    0x510050910050415030b0f0907080a02011d2215050f0108070f031e0e12270102010f0e0a1a010807050105070c080105310c1701140106030b1905 63
    0x54207080c0e41d030845001a4124010426106030102a04024107105502d014481052102116036128405801c201d604158880b04050344815003500700030301040b110b606415194841254005a443d4085d200c042c5400c40030b00c081a100d0f44840c6103c600940c0c510100d4180c0d0b91201d20340010300001e540c075203111142400003c01c0558004c1020b000c00c41c0d094121800144a50048044160028806205905000009001000c02030000006481038040b4540107036a6041503445007103040508a007010010b1100c00043c00c401c0c510343d8115503a5402070f00c3d0208681c4650a00003141d9801046844260302e000102d40304070079240141c220b41140104100400000d000050301d200717180c1191298091f25011841d44800d403c43c6000b5402c001c1002581030b03241d1034601c401c0c00a140ca180c85003812203060f1100600201024140140302030041c0314909980c01c0101c021105000002010301304103c928800340800e810040c00662110050701a601d880e00780c000c004400a02034065080c42c2c0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 488168246 1250 488166996 488167021
    0x80403020120030711012009130504020d02010f0210230601032a02070314010c120605090402041d0a0803010501020d03111602030a0807060204090e010c0c150b060c0105100509 77
    0x10a61010001ca0200c0c1c0c214066081d00035800300d10321004407d07000f40d106402c070034140c2c00001e006e60150450341d5504482c2161409020b008036006885911039280e80c0e001100c404002d0b0044205600c03030841003205841c030500c920007600d01e0760312a02c28041202c0c503800c050a1006840e4a04150400c00c2c0700025010301554492640361550384c1e101c40002600d0207030309025180c0e1024050040007611440c1d5050190171082d4215015515680ea5078280b40140701141c2c00340c0107950700960303e44002401410646d000e034040c4484203034000150b40200c031245241ca10709000413210518088010451560100200305014010b1700f0240811900716042426074000d03c08180010150142d200080d500d042c41603a001c9500001c0300c680da4411403e000000c2d5001e8402d4512485c03401210180311541032003441e00341c0903ea82c81c150b20503071613295802030f103050a061003144d595800405071260303100f90040c0450300e02e880c0045050728120f070302400001202c0c0e100c5030180c081c11080218401281 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 488169496 1250 488168246 488168251
    0xb09040c170a0b090607110f060f071e09080c10021c050403080406020f0c040507170603070f030b0f0a0e06040311070b2101060516020904060902090708040302012003 73
    0x481c0c000703100a191600d040100304000e0010007104090189100b0049880341c81084241c480840b242d10b1498082d0703450000a60890147d00541c00ac122005007d013242c0c3e81203110b0307160140b160f219101d60402c1d4586802c1c081008034846440c1041400c000b0701c000300380d01204541401c0c5048856001035120761b1401c00c0321500c00b06c0c0c011200b51050050302900c003c0d43d0071802080d20fa03174440d0f0029550701c045200000441c4a000c05840640c030309070054500c602c032a031b910800345198170b80b01a04070701009007400341d1601568001080114110441c4030041d401404003074502c3c1410410480c200da07000e8840c101950608030b00083d110300000b0034540050340761808064003030783c08885506090f00380d0007400511200080c0c03042c01103a50100e1300e02000c001501800b03140d981d80d105a401c0d101c1c42034280d00c0c440307000c00000050b10700f00304560341c85802964003144d1381501e40d000504c0300c4012581c00780071440410074401856030920400708240c204a000b81142d14520340a5030302c0b030000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 488170746 1250 488169496 488169509
    0xc020103150515031308043305091002071802070606050402040f061103090a0f030b070e010807050721030e1209010e0906041b09090c081003031b140a03030b09040c 72
    0x1000c10710149811750300f41c135820381210903162500c0d121155800814605079000b40540940c407a107048503803400d40c05d480b94186a807940c529100110003400760007022071050201b940a154400100c9602c5029050704056070701c00010380d80e010610b000300c00c40c1c2044d040a805684140030030700a2a003d45185410b40f03100d03040c0300000c145000805031441c8150950590000040030380003900c58440711020040d00d11480700003901e075039124800c9030008072617140b41d400240c4c0d59005c42c0781e40340104014580345000c2d11254500686580100740020285a89080020341d5404111000031090001c21455149440c1c5c44e40b0b0a044500003d01803014038000f244145008800300b40c0c03550b59903114818101010103000300e1242039030005081200144241c541890805c52160700d13040c40f4032100d52103104065052910305003552411641c01d480d0140d0f0b100e99011496030540810101c0c19540310b0240d1b01c1c80104060101d900e80201a03400850416000f000702c00144800140044040f0003135910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 488171996 1250 488170746 488170789
    0x62304020306150703090312020606030c150f040e1e13030e0a0810090219030b2a04080a0c090903080a09020102100e0a0203060f0405030711040207020a060c0201031505 74
    0x5504001070b203e09000c1180109001000481d50201501b0074a498222030180e4a00d00321207e501d00140d803140710460707500b98540c003ca40079207000d00e807031009954070201c0da03001642060031280d203081c2e031607002c1d800c41c400542e18001080440c0d00b00401d074144100c14421241040d080c102519541c40b510200c000b028410020242e18140d185d64604100902001c400c4404120307034501c0d18401091401030580c0a095405103038000010350b41c0300481140d50207400e0441550320054a0356056410640740c14501401c406040520b50750071014002038514400606220715441c5440b21a03103004e03a10135100c00c4c1c1400d11200200790407054542c1d006000785008515038889100403403c06890440c0f42d82c05501c2c0228070341ca02c03400082d05000807031007030701242c03011788400744900e070701502c1220020a00c0d4002c1060b18000340e0202c05460700310900bd0009030074000036500103001ba0f0380c0c1c0d400c85800103102101000566926010304403041450ac84000c0c0700e40d0910001c24101258041c21290481 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 488173246 1250 488171996 488172001
    0x40c0813050307020904110111010e031204020409020907202d0708010507090e0a09120c0326161e14070803011e06110304061b02040507020f010623040203 68
    0x4400c2c000c03034201550042070300c0c6480c5818078040304201c007480ea51034000f40b0301e2080c120700c0e40c005100d442d91500c607410081d0305005011901400d8440000d00072a0000e03211480140140c079404802c1d03006545075112801c224417a8010070152002110308101c0a501031608510017610301c400807004200d0b5401c0c6440c07012174030740110345480520380c040a215032a1a082008440d401900342054480007044404140c580f18469020350320243d801030f100c0010461110103860017104a02c130301e18402d0410441c000c8940d01d9400300c01180f262260341c80c40f4a80d08026100701c01d03c0a0746000c84d05400c0100304221580200321000304031581c00360911074004401d0304d4040584040d6504a5408104941d403903841e105420300180340c0c030000c5d481c0c285103810041103590050314000b80d04517648000318145486d24030100c544502031945842503071912a0048056166400380502c100c4da030350014428181020301e21400c6460542c00303a080c0d00d49403403d42008080780d00488007214401c44002d626074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 488174496 1250 488173246 488173253
    0x1419050d0e1b0f0406051e1c030e0108070201050403090324020d020405090f010b090907050c03070b100b0c100509010b1306060201050a0501050609042004081b040c0813 74
    0x610010904110303a01c0b070000c40b4114020304060303880c52001c0c103503002081d900b01c000501050f1071341402040d07400440310f084444054045040540c0100c0000d00000b0000509581064400d0160f142980080d0848035444850f5804c4152560441045d200802c070918154500400e1040203010003090404418200c81c200d14114000480b40f841240c1e08542d00d11503541c540e0001e60140c07240500445060000810100240403541e048818101840e85400c00143c2000440c0780010304450034801c0c28030040241d00010009400d03285c0c0300d40b02c611998100b0b42e07c2c1c600302401076407100012078000c01820a040c00701240320b014203110f1b55001b0600d5203841c18003901504600600f20741010308103010341e82c61001604614220b550035002080715440f5600031000343c400c02d00485801040c2045450428206940300d14803010b180001e050b00000802c0311001c031036201e03034424180b0b580200b0011005010f40414440d1000040340e040085580001d0042d203c0c9800401070102034281c0f69412003070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 488175746 1250 488174496 488174501
    0x1109012106080111030f0c0c07030602160f06020d06051215040512030403090f0801110f0c0c06030a0c08180a030f0c0b0f01090c110606130b09090303071419050d 71
    0x20b0320340381c2c009101c00c494401d0401c40c0d1390011601c900348280358502044400504904851061403410098090b803030564a039000a98002030030341710510f49150500c004a030b042e17004404103d10804015170703205841040070381901e281d0b0b00306038421018140d640c414000001005e000c000c2c10451001030a640e103081c2a4240707034a044041c0c40c034280c00401c10080580c018000030541b001c008030261615259040300f8225034802190b83e2411008010f05540c1c860828050710900c0b407440100da0b22041e01c200800c40740d07001507134140003090707c1d04030707a0340c0058102600360342c0100600c400c18424008440001da580300312400103400e010310300140408240c800d0360b180c00b4507078120f0910703040f50a15000c3c501600d0350911aa9051030314180e920313040310344103011002d009510480241002d480d24801c0081031081100c0c00c2030403c0c1d6540c98002c0381d446280c107903031040308440b0107140c070791a041c0009040e41803200c2080300b501c5020008415440444003c0a200c54403034a044d6890b80b2034510490300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 488176996 1250 488175746 488175749
    0x1504030f0305090a0807060e040e0f010e010606020c0f06071e0807030203040905060111100b04060305160f05120a0f140102071407091103060f010203041502060a1109012106 76
    0x9100c0c80146044185504000200144071042c0e0341c4581c4c3d03c0c3d03a50301d01d944070109401030304001080e030401b00034180b0745500000303502440c902c1a00c0341d000d0b40e0480d050850f407201040020594580d481002082d80520580038076070b8042e2031442a45200d080018403501c00c6901c02007135020754825403240000c02c2c0841c2250154441009966030000d400c1c082d581c0e401070b04c11902000c0c1010005181035100d041c00207030341c840520041900404e441c44070405031841101c81c503080340c0da0780400404035034100804d01244a03603800400080707080810300200121540c101e6801485120714940041c80d000541c200000d401104078200304070140340c24640c1408180c03190507298004940c40e01070041d0318a00c000030089900881d1096030391448040281d946081800c0030940045c40040d210b03060101500400308414410b5914054031054a0640310000b02c0100c001030380650f040124035840c81c41021039510f5500c02c002e0610b02598002001c4104200034010025030040710410b242c02e00d0f800410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 488178246 1250 488176996 488177003
    0x507320f0f071104060e06091812040e010501020303090d030513080403050c0906011d1e060a110c150702131d03070201080f010503060c030915070306031407060e150403 74
    0x195241d40c0196920695000724a050342c9010b20260b011403a484d0501c600c1013114400d8030300c1d8869503245001c01c01d807040014400308443d80220402005180305010091a01080e0200c0e00e4503242049411400c104058210721f05643c030030000c1c420184400601e655914084d407402003100d984600305080707040e841c03c42c02012080f006c0303008020018041440a07108030309842c410039590f903400044400300c007110f0440101c201d01381e43ea094141810079103007038080008200c1510142042c00428126480132401c03000060601c440e40784088810305c40030940110490b4a5035500300658010012031040d120028400e00c464a00300d400450903412004c2000400c2d43c1041150802298460b00c950140380700301c0c00140f1002c00160b48491803ca41d0b03042c2d44028004103103941ea42c4158240d0751741b000d085441e841c441c04008402d07802c405070f030680c07040803035980c04117120b40385241c01010021000c0f81800356400c126410b1050640c02903206054010480d00700c2400345400040c1c103d00e101d40c2d08082c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 488179496 1250 488178246 488178277
    0x61e090509040c08010e070321090b0c0d08090303040209190e010606030213062102030c0706060303021c0804050d2a0b040c0807061d06190210050732 66
    0x1c24000941c4411007107400c50130081c05403001d03001d81143c0314285c50000400c0401908042c6003400c844d0150343d0a00440d0342482e6040d01e40381c000899051300180b48264080e0b00440d860001d082c2c0c001035690b00484200d005500b5420f0942c0020104c04006040314540d4402c0000c8501d040e0240c2c020b00041202c8100804c11180c070381d54010041e6200d065007010101d40740000103002c6201c0d0780302c1f600c15945a00240141421000100d01950000d800c1d80b107803420910070080420054421940118030a80050890a0400030030440301a80518240d0602c4a08401c1002041000c81c5056a0304003914207014003100ba02000d1086180c24441445d005c546a0401401c11030000c0200b80030364041ca0001039115550440565108001c0c003448000882e01c1c0c074207440e05025621003407003c0d00d0040440341004410601701c1c0400c0c04c5809003034011b074000e500f0808105101d1003403c0c1c1009161074001c2404288000d940003c6c1e04211400203c484a091051002c00010303050352170901200190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 488180746 1250 488179496 488179501
    0x1050a050307030f033903020c0a03030c0b2a0d0507140304060507210b030c040b011202090a09020f0901030c0e01091a040306020f0315040b0901030803060f040c03020c0c0a061e090509 81
    0x1c00c240c05d81b40c104105c000d8460840000381c503140c81c0f40343c0001c596255a502070192001d42d11060568800791402c1d10204080e02c2c40c0140441c0801c0000410004228550b192031460701f262051304c40c041e02100910001a90405000c05103008803940700741c00c01360226040e01d8800044542118085030348441c40c0030242c2c2d540284d00543c000c000030300c0b8120200c61608038a5070801c401c42d50f215036454041b80d000e01c1c1800b01002036401800e4031840040054064594403004031059130b02c0b19140d442010000100905030b0f42c0c042c490080044054908140300c840807400181100256000b94500300505019902c94659003008503030185502034001e54440d81903c5815100f6082034401060105c00c04400411504240c80fa801c18104010941101c503442c1d621000d5080d84003610907034125142c485a002961120700421100c122540da00581d85d00c20940c0d900d003000d03010841688154403241c03040041c3c951003aa8188900351001c085041d45000e09420342d0b41c640142c2c0580d4104409804 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 488181996 1250 488180746 488180837
    0xc301a090a0318051f030e0307060903082505072f09010e09030301060e01110d020d0905040b060306011107030c060c1403032802040f0e01050a050307030f03 69
    0x248805014429202d003010344103c1580d0110b00005402000d40140000d5040d00358a00041d0140886891504001881d03481400da00340c1582e209220a98130962900307104800c0542c0701d144240d10400c502e0318003208a0b9810703625188540c06a414808014000c40c003482803180d004030030400e603102543d04920404800d200742880d03510860120788a041c0a000000e00c040860301c807144213160764000386107160f0903ca002c0d03e0310300c1100e000d581041011850728013004010400d12281955a400500400c080400000c10100d040c1c1c1080c0d00544c200780114110342c4448042c0e0b90040c0c02400c100c03550750016005280340400603800501300008005d00018416000010b56801074014a015071069001200b0030f40d0b02d100c280c0c0c2101030b085203c0101c4103900691498101b41010f80f82c005850140c0c2d0b46403074602010310b0b402410f0801e14190041006250a030000c200400098014154041c030750f4854030086e4002d0711018040c401c06003400481e206103440042c800002c42003018210450288 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 488183246 1250 488181996 488182003
    0x60a03080c03040e0108011406120303070c11041a0405130206072018160c030e150418020c01060f0803040e042108060f040b0d020d05031b0a0c301a09 66
    0x218023904030f82250000c560142003510300c200c000030f0b503a4000c518648484104a8803820070940565500030b0801882c2d40e00c0d5500d01401c20303101240036502c811091000308120031200c0140c610381c00c40c0740900d40d035030043e111141621402504a980c499103000c41c5c507000c2100402c0b035400e0340da00182c5480c242072410640904903000300a0610b040800c144001300c241d540318000c12016010980c00b0840407070910b0180ca40c1031110075000b03001420540e44280c0c2c40038101c210318030100c40503004682500c20b01d01c00d1242a00074200d03c0c0c0c000c981103240103000c94480c807480c0110140300302c0c100d0001c0c0a020190320060b050301c000b4140d11091598400780149080e00c01d4810510842d40480c078160589418024000045ca0003807a00e00c25401950810a00441d21101107840307000034041c000005007500208540b440200c000347c24180c1181c030348480d00070001c0c1c001c190082612103c4000e082180c1c075a40c84070354040307143c0404180840c2042413035500101f00c00780d2504035203010032070f03030501c0403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 488184496 1250 488183246 488183261
    0x30f070b0408060f010f120311070f081c0806091015030b04050610020d03020c0a060e0304080607170117010906090c08070807031523040812090105060a03080c03040e010801 76
    0x60003924029290f412450135410000e03c1044405640c0390810700030019041460303003280b072090400d500d00008100c8100d04200c0d442c0e2041d810801755910401881c1e50a0008283d0120002550424811f0207000900645000342c0f004d07005401180c0003480340420710515101900130303410745404449007001d0040c081c0a44104480c051401e000225109060a000380440c050b05038000d4240c61031000d100318000d4100c80c0100300c1c1481281e40c4940400c009118034000100d02001840d621400c02005914100d00602200200810403044980080d4200046410340e410014074110320b116600309a0701400c890000500749500e040c102c1c1040003103880b40241100c003440c0554159966464805844003030602c009824039010004420704610180d0101500c0c408190700784110405001c1c05080f444812901211022400142078180e41100480e45a00011f258020304c5141b825001103403400c900c0e48001818200c0109944080c0c1c0c80c140300359000303000c440009100745e42c0c1d9642c03247c1c040e00f0103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 488185746 1250 488184496 488184509
    0x212060a1b02010c020703020114280342031a04030320180619030e0625081506210106020a0201200109060903120509071d06030f070b04 60
    0x8076000d02a07071401070040780182e100c0f03034000c3d102540c80d64005481100511308002e00548040100043e000e00700034040d0305803000c8903008480641d100c0d03000b030202c424100e8401000b66803000c0c41c59940400402d411503c04040c240c11000c8500c1c1c036824000e01e100794200828034204d80da0a25503d414450000e403085000303070b40a00521418403c0010130780d01040720800448030401181201d00c481b220303c1d09112034003400c50740c54012040329040004001038110000662a88880156600c040000540142440200d8500f0661100c000003268900b49a10700500c180400061101e46254842e5204030b580079003d6655400f100b8000f000b017507409058910a2464080040380740c610003d01c2d0700d02d40d85c4c10303180c1030014407654401c220340344054400c40703195640f913000c50303000186c3d607000d041506880b9444000c6822140031200003518070050a035503030303036000c0302d020001141c580d40c40b00c1c050300340003021809548451000c40c0c1031400c080f6260427244141a800599800c8240c001c0007200e08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 488186996 1250 488185746 488185781
    0x28080a0510050d080c01142517070306240206090c0604060c0f0609060906050a09032c0a06050301170d050405090a090f0503040f0803091c0212060a 65
    0x440008100403610180c4034211600803124040c4110b042c180d04001c400c03409103404034100003000d540035081d0b445a86c5982840c48004060045045200c2101201000c3d80401802100800c10000700280d03120700200e910302034104085081d0034000d51000e0081d0025a1209030026980140c0c10410200b03034105400521951b40003c140601c08944441d40b074600a00c242d203014a01030044408011010081c5c4000006079410000504144601c174509440750034040380000460501c1021540010700b03001c0310030f0401640c0c1e40001d50010071008403074160704ca2240782d00c5242d0600003400c1c201100068010310070320710121b84140c0240145040ba0640b02401e00085160203402c1e49640c0c43d0760800002c20018441071000d45050314006502c1446148002408000c540791b03174080002c11541600c80c1e4200042c03c1c0501c050101d551400340c0b01c9500110325089452000c51303030354000d08400418603245038a07440110f58610f05000440300e07241d000c0300d0141c1004900080104614001c0c4020803c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 488188246 1250 488186996 488187001
    0xf08160e0330031605130e10050103060509090606090c07050a05060a0b1008040803040809031c0801150903082d0c011401030807060b030c0604060201050906060d12142808 75
    0x340300c1281e02c84c4002c0300460400f0011098141c403990401e150440352103452400109091101c0c8282a22415241e585440d0852400c000541142c40580095000307440301c004022907000005811a0000410740741c0744d170542c0d6001c4691285002d4001d0007050f5000d0008018280540010844d0144451007000c010b43d03542c00303041000025841c000380000c41c0c14240002c000c20300d1080034641c01402000309a01c1c1009010000c0d00b4205081c0303555225012406041c010994000c00c414003500c8100e002c20007800c0800c0d00640b50409510000f8140900041e4840840d425045010003815018490003040c00203a41c5041140e001511061041e600e4204a0000380d02440744140c1260b03005901c81c1e250500980301d4501500c0f1030b180613505486070958603001c0380c4480d070091000304101d0b4000210340c101031503250b080100c00381c00940f10702658508140403503101070383e000300804542084d0310035100854904929002c3d0403200221600c1360314409150003ea100360489070f40d0659103007405603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 488189496 1250 488188246 488188333
    0x308030109110309060a050c0909010e07080901180609080d022803050717040606030203102309120a02010b0a0906090c17130f08030a15060f08160e03 66
    0x18001180d0311900c503401407020646c44081030788100e801c01142c0c582c580c98600343c080420748003002a0320180280c0e11385130401214580c0103d00b6030700b0440500c028001d079400e0b01622111881c030304030040c210356a2102140100b12040c411103640341d03201d403410b640b540b02010340c40d200155005d80d034603c40200649407403c0a80729209440c4207058a0b102c845d0080c01c07030700e66003010020042040762131540e114404409640e013040380311170a428900f00072403078020301e1080b2034084000801c802c0103030800009203c82c00401040c4e0030b2500850200d610703255101048102e025002188040c3d8100c2c914800206402c169500504269207a5190602081c1c010344001c588224030010202d1585000c0d00c0410804540780d00703640403030350181001111801039500c0e020910303442030302d8200e0707042e0303450360141d00c0e82040c0c5c40240000e01e60341c10300950301c078543d501c081c0000400518040c2d10161030b00c00612141d002c3c002208a120000e011a4480c1c000781110041d600b01c113401e003042040c82d540e0a000306 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 488190746 1250 488189496 488189531
    0x70c02010906020d0c11190e07020705010e03030405040c120c17060d02010801050402031e0915090a051f2a0e0402090d020d020f06031003150603030f0809160308030109 74
    0x1c1c00103035154541c503c101e03110030480070781b004000c941c00100700600308410b80000384644043c1040489206a03410040e4005c0e18140c1c1a80c482d038184210074500d01c20580e004002d40301181c00594012035006440c003801c550f0806441074405600d841c20f031182024681c85241e0340b640b2040400003940d01e88800d03080110100c1103140080c00503103002c0050045003880d4000d1074000da10101031840b000e445401e80140c0e22001c40e5071191960004120070b01280c0c89010103a048803908010700b0b190502911156100e05824034980086002d407002001c0905c225800703803404880c0301c0c0405084440e01c2c0c4060051b610030080110000751802100c9015142c1482141d440316401040401c005420f44e080c890f0404070004141d07401a038544804a161b01c841c80254802c1003060a00e50020f4110300c2c00e014980100c53f18803900c10b00d440340034000650030000c90042a022800e00783c2c1282c6c2e0304040c00780703041350030304030100500380c200c0c000020801075402440c107031442403009024a40d030080440c80d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 488191996 1250 488190746 488190763
    0x1d060a0e15131b0c110a0b0f070c0b0c0d030b1009030213090803040c18050412032a050405090a0c050405010507031b0f060f05040302280b070c0201090602 68
    0x140c04400d41a407009450103868454034800c1031000071800e607080f10b41c0c032110b0700c0c011100e85000c2440d010400e4100103401e460340036900f1048a8100c5a00e09012600e41d4a008010008400c03a0300000c4001c140202c0020070360043c00795111895071540d180e90b0807904e4845030350141001c40d040004002e014035014110518229580e43c9071203c1c0752450b000c0100c030744c0030a5100003006035103002d2240032900d000300031840340d806143c030002c0f10b526242d9410040442410038251442c41c000610001030814011039240400038500402d04405104041d074510901c40c0149564205c0e2130f0160040d650000068411981e0407a840642d45c0c0d1516028000c2d200840c520400241007000103101e5980141c3c0a001c2090103490100d00b00111403007541035080e9648404d40b42c1c2c143c400c1c81503082000a00500c04100c51091043c0010706255030301a40e5020741c03044d80d2a00c010b0714034420400320600a503142d01e80340c200000b518a410603002c0a000e4038486502a80086d64031710011a00500020b010791 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 488193246 1250 488191996 488192011
    0x1091b0c0503270a0f03050d0201020f1611120705040b0f060403060c02072c062707020c0303190f020a05060601050f040e0412030e070b221d060a0e 65
    0x41c0f5140d0031030144410030614030b9808118200140080900f42c5481d4124000fa210303444a502800f8110b052880c5402c610050704000c41e8010042d903041280040f060781c0010520745840c40c200b140519041c00c1003e0320072800d170340041d0a070401ca12041000103101003100d00a40d02081448150360900030450301304a002508071702e00304801c0000446c1e0f036000c440e8020702e42c41901c440545441c001e102180600070546030485040745200c0261b000c0103011504180c0c12502000b05a460b542019a0aa11040b20f40c0b00143c5480010f99100d000740b04081544000806a903951101064005100c01c5500081000140f00c3c070300e40e8000c64000200c0d441d106800000500c547c0c0d64150045402e617011000903224000d00340130008039014000701c0d040c0900e00c40c01c1c003419802c901c91130007001c85150055404107a0b018031001c00902054604980d0440342410220907074440200c4480d4207607000c0c3d4050403c01d4103d544e400303807542030904464010441100c03110500c036907958881c0f0783c0c02008c0d6800e9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 488194496 1250 488193246 488193253
    0x10512030a0e090a0b0d05031c0227060409110c060109050606071b0e01061125060e040e070605030711031801110a1e060608060c09060d06050901091b0c05 68
    0x4954030f0074141e80c680c409181c40d03001c03500312440380206030a400103600c1120fa070303400032541609000c44404c1d03012401c0041e4504500b0b0810488144107040300c000c1d0304c64503044d440b03002283c0b41d031143c83c1110080c000446090010140000042005900407000c10303429005031800031a2550041c082d1034054000105440e040c182d682d103c600d0007010520103100b60004401c80001c44520300508140208000d48510010002400030f81341008403103400035224410550034454203089860325041541e400e40341c240d100c2c00e29030000c203004020803d401c08140c410700100141c81c1c0d610030700840c89212250f0720046108541070005035203001d02c035280d41c00550781144541055204101c5a08801111400c44081003a280c40e400401c00c010343d000317500042408841070509c54680280c0c002408003e0040c1a5441d00c2c1000c4042401000800c51041030300194680381a52140c2003c405402e00400c82109540e54940300c1c0700510007034a0982c080300030302e141a030115000c1c0450261268004028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 488195746 1250 488194496 488194517
    0x4170a020f1c200703050a110405070206090d0311041208040f0b1c111308060912132903070f030e060708070305070c06090503130e010b07021e0301050f010512030a 72
    0xc042c6a142c00110045600c2003803c0000841c000b041311f200d00c180a410406d01c0c10b280304003800b0583c1d030000c240806651102051165100d00003903103800100e0303180740000b2005031484107c48188120362001d04e03150002d0098000780304507480100115003900800000030b81d518000d00119000d003c01c5105e4181c5101c1da40c030b00350300541e0000c44220507801b04091510484184110404005422032451984810100408214100139120140c10b10050043c104125078044000c40c90050184aa03a110f8400c03041b80c6140780340704c903160083c4680022986070f01c1d000320003e00c00741804c401980001e040c060030a034043c401107841030050700700c0d9507014525907a4080560241c00060141002c010b401a03408020403810f1240c0d00c3d00c90f11680c0a59a01d10411400d2050b9190a400c81742017107012200401a0301200021034041960690b0100c060200a000380d6040210b9010029050750070b000030040780e44001c01c1180d0596104480c1c515100341c0c100307001696030040ea44a400482c0803d0302 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 488196996 1250 488195746 488195777
    0x105011407020d081b010506031e25031a0a0c0f171b0f0d0c02030406020d121b03090302010c020c2206050d03020f1b06030a0504170a020f1c 62
    0xc0b0301c43c0b1500800c40740f0f00e0b11411810b0309040600c202d4100032540d54440a000191500f80203880784142c42e003200c0c20007903140c4454a40c030b88683c444904c0740b084442548500c00900e10aa01000f540c004849420a01a03000c1c800b2018034222903488203a840d0a929521143c0101100500c80b402980c030190403403c0360604400f8024003806000d07020f800e4800702101c005d16100144601d5040300030607074540c00310380d401009440c00d2400c80000e41d041408140045503000901c5c8004401d01d01c1c0c5844d031450b110115400610018100c80d45200c8640c00d10104a42c15800a0403528803a60003080700040b4100100e0301c0c2c45080b030029030f000e0b00755043c010354051404030034080a0315031400050100d0b5a00001500d80407814012809038214400b001070f607070004c0c00005a0415a541c0c0280ba008a410000720780384001041d40c1140d0b0341d07440c003040a0000301c0d000008820b03120b0390041e0741c41c200b00704041d42d107a99018a890051080c00540c000d21140f84880001c019002e0321000c00c4842c4211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 488198246 1250 488196996 488197009
    0x32010903231c02010207111c0b1e04140d02121902100501060306240806042310051005090d02010e37140906090a090c1d010501140702 59
    0x203107050482d00c903119801410b09000005010010071603000181d03103411524114101100002a00380701d410034407428041051600b00382000c00382d0000503510b2503a2405041d420340e40c00341c01c10745150542d01081008200800345449000c4881008544c604803400600b01d9175074511410303d61010800380020035072400c00c940c441602d0b10b101e0055071804001450440f04840099128200194540008000761041240240040d640c80d58150740803501c440b5011f08200d20262205009a03a2800030f0452240c504034800c25221403035910b018281400460103903030160a01402c4d21540040d402d001e20980150308031155508041c28004081001d60010b4608600500c0c0c89500300c51a002c05801d1400001c040900880e1f1143c1c07003c51440c800b48500390340103142e802010080c0103609000c4110740d21040140d40c1300c9400c83e0a840d0703643c0e0f44a540c3c0007401040c60010001801017802003202d2416003684180003200448002c1d19a0340d4200445204010f40d103044101c0500300040405801d081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 488199496 1250 488198246 488198303
    0x40f1a0f030309031c03050105030304060212090d0b04030f1209050a020d0302011103070f0906031806090206090d030809010e150109230903070512040b0d02070c32010903 75
    0x741038904101e8020301082c01d001903c12080c00b644042c0340c40d000c4182c1c051144c40e016040030b60043d401c03e414488080e550300c540c00b159491041c004038400b20556115032112008035440400d10409040510300a400b42c1c1d0650a00404218603a207500f031002d62510601214503003241c02000000255002d021a00003c54010340c00c5549a10004103402d80c070800543c003070700007962840840601c0304030040c00c000c07240d003080c0105420030490780c10003520b81601d03184154102200040c8620350380f002940f00c0c0f0860007801e41118018a1180601da0090500f074459000c5030020300ca1041e0090500740c85050005803400c00595180041c4960710312a8000c402116050b1410852001032228442d003100c41166074600369880001d09008100c0180100700c0008101d8141500381810709800c40d001380148510310354140d5000c43d040003841141480a002404060a4003d00680700b04600b10700c4034054001d40c110380d400c01c80541c110b512640341d000459030000c5e4003051401401c190f07400d25080300e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 488200746 1250 488199496 488199499
    0x304050618040507021b04090b06100c0512071a040c0b16060614040c02060c0a05180612240303030403051b0609071503110d0c120218040f1a0f 63
    0x20030003207501e901d840c4201400b0343e0031600100030540c8020340c031a17510954003603000d001c0e608081c20070f000140907142080d008482202d64100c078032016a4111120310500e0310207070a601c01c43e603003c4520f402d0b11008060250182074203840c00880b07420002188407084d24014000d962100d01000080030302e1b40645103810b08801d40081c0803000d511044280c0d14190403a8042e21150b0200b000645054401c81910800034009040203117005204424039018100b07c038010710074009000c02252a9251921550744002481c2d40d49514909088903481e010488400103031005070352103a010350b40b00045102d01301e800107008604d566110764044400d41c0090000c00183c4204c4902031011701400d2203040e1052030208000c0c0142490440601c010740e164000400600d864220b030491760700024800c0f110000540e1b100800c0660b4000004c90703c500003180360321003091000c600782003001c240d0903119461940442d0300380810807034001d03c181100e0860890940c6c004422100b0b03581402d0202c11100c90140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 488201996 1250 488200746 488200777
    0x90504060e04170f040b0909071706010e0d1e060e07030b010303050d180302060702060601210c0917010e07091a10091a030108070b0f030117031306030b10080903040506 74
    0x30841302c2200745811a1308808004c01010828403120b05000c1442a40400a4a03146941024035009118607900c0940f69604000707020a900c11103459141200d10240d5100000000c00009030044e503200b412490405c50310a4240346816a090b00c00041603826241c02580d000c8899103542e0b010741c0d030303980441441c3c0c4080d6103070141503803c00c1e0700344401403800c2d003e5000b500051500f501300a00700100100002d041c40070442c1c040d240d1005a90300039180c00591640012070480344030081e04e20603626400303141c05103003428403803804c1c60703044d0440d16079070a165007128035071600c4180d41c0d030075035040c0450311602080907560820203103407448214038111042d00305140e00302c0e20713029001e0404822070000441d244001004114120041120b04004c2a8403031110f402c11841c5010b9400c280310604c41c0300040120050100d1180070b0a0044525201403000e400b0701c0b00b565891701401030304103604c3d140c1c8a001880e400e0110301e8080e4040c0351194200901030752078542010304002050f0000b105000100c3c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 488203246 1250 488201996 488202007
    0x504020a050409200c0c1201110d0e0312040305070614070c06090f080307180e0705030c0304050708191b0501020d0f0203210912120609041104060b0307090504060e0417 74
    0x1200c920040205c0300c015030103000c3d40309240d4280300b4540201d4020180917032502ea44410510001c0d0f09a400010f01800041100601c02010a2940c09000440030303400001300284004c1503000f000529000c0d10880d824401c10800100418003020102c1d4208089540d01c60505d000a50039440b1000c1c01d0320a400400021503a5240d290742500200c484c0c001140c094200300c49a00105042c0100030308040300d03c0b208625090200411600028158402e1540f000c0081400c1060600034030b405803900c5411110481300c405610542c0200d1000c007a80ca2040c4114001c103580c0b0645c0d000070a45006070014016120520307030894504060314007000440c0418850050181c2c942c040d100c0803d542485100360340e00341032215506003c54159054078850b41040300d002d269503900304c60b80d03201b0001c8403408210b603902d04040e910b0803007014210340d0240c03401201180000315040994004c007003a9840c5a00e02e0b80701c8051000700d621a018103584200e04800003800290041861600036a65021350750604 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 488204496 1250 488203246 488203301
    0x1509180601110730080f090307031a0403030605030607210e010e03071209030c050402031008030304030f09080a2004090c14040506010e21030903070905010305070504020a050409 78
    0x1005810203184030011300781da07011000302c90031210046000e0f0296030104801564030443e16105004003032540c407602044200c080e43d824403604c4029034212000c04044214500842d050103422102140403e242c0315000c02c0905000074040c0c410380c210b03151182210070b0174a040703140180300d4907489807254513144a803203035100c20700070882c0c0c00030ac400c011031f02c611452900640050005803500f0401002681c00c0000c80c01c01c034085811164252001039498595085a91040301780380c01c01d0140b44400000d0008040d40010015940d4285d941d50780070b81138840d010300d61250540c94002d0010700b40d0740c40013030340d664042490340e24001340140000391410310b41c1d40d2204610b070f042d8007000202d88011402103541c1454050103a000c0e5007440c0135100c055001c000510106140005a542075902c0d03401c1d946400020822200741c408001c0440301f52540d69500340010f008240400c4a085c010348400040504003402500c100c00350644480342024200781e0258000e00014800c0d222605240c1001d0400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 488205746 1250 488204496 488204503
    0x10020d180b040f02040b040905061b0f0f1608121005030102030112033c0219081c06091a0103110f0a08091c1106100605190905030708070302150918060111 68
    0x400c0c4100040e0409142903030ba58140040362f9010510b04074000c00255030720a06010480b00c4464003802002e4603400040e00d9149001c4030910000d24441c0300098050802d0300f01c11100d48a685440040c103c50382c1ca50061500b81e01080c4664001c64400649010010740034009000031040802c0e01008c0301d0310145955116180201003400101c0d540011b50540140d040c00011407600c51194850421500ba80c1c1d20a250700c2540762401c03110380d0701000001c01c0c1c0b44942210000b0700d900042071202c2c004e0501c140080404101c80c1601003442c2c5100c011968010f001a50f280c408444407040c203205010f0825515420700610350071603409201d881e03820b00d0244444001d5240d2003541c92a91110902d40498600240505124940312001c84c04024450b400021642d01c645040f02107505800e06840984040c022500010f0741030080f81c82c0401c82e0000002c0f03000481c3d000b103c4186101801281844451142100305a00059924400319045104e00f00017500108180351002d0281e003a040400d09 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 488206996 1250 488205746 488205761
    0x106050d0209031509060108010513030c03170702030901030c170a021b0307050304150e0306010603020c030913150e040f030507110409061e02040602030409150810020d180b040f02040b04 82
    0x4158091300c2400b00010f400c100d0a0b000d001418000c00c2141480d031242051004030243c01020040302011030410548140070200000c12000d0340d621080c2403200001e9240e0300510b0b840b40c0001d20782403044507120310030041d100801040d4000f184c5641c940c0c0c101307080a5408070321046803540c40c0080f808000c0400300000c2c00000e00031000f843c1c485003000c1441a03c082040c0002080014007121255a40c0e008540541100c680b03043c0141c1d10340c103c1c02950701350b0048a07001d42c0e0100410103e000402025000044041c000701c5041d105541c80d11105000901c0581c1d0182c60449d040c0c005400190180b0000e142d403078010404031005119840015040d944214400c64106880f8040c00c0e0481201c0c4405095100c9506000c1d4142814007000035039900441c480c001040341c42d0075000f100480c8200e900000303483c2004c15a07510715a1058641d01a510660603071640916004d050b8003148c20140c00d0902c031551154004165840b1600d40504d00c00f12290103a900c140c2d60b0349c1d44007283d075a9111303c16 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 488208246 1250 488206996 488207023
    0x2040b0f09070909060504020f090d030201060518190c0518010c0b01031209061d19081203220b07050315031b0103050a090f1e080f0315030d080106050d020903 70
    0x3e859400c09109800303543c1c0550001d40103078014040d229203003a031441034075070090050310100c6020304a410100d01612541d0300c0150880403108255180e2903c0c00d940910440751440b40d80d6070034a41a0120084840070800d060000b6401d0260500d0f0003049601002803090515124206030b072142c940031a482820381c03003264201044190304d0305003904054410010a00ea0500090030f4800358110208159220050340c070803640d5440e4402d0f840740500d14134028106d520100c5000c854203640100807a8419118280b84001d40c0c0e10f00321413450300d134200750829544050344081d10b45511600760358a40010302250314000c564080800c42d52410080d150041c40000303585040068108000f408481019040d142000e050050350000b0903520400713181036a50008541c400e080282490300040d20200d0f2000340300d4000001c02000184948000c3e6014070b40e801d40200b1401030001c02c04d0341d5241075411a5003c034044000411981340198040c054000720050050b203407117108030002c3d04008140e8441c0303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 488209496 1250 488208246 488208257
    0x15090306010f05090609060a12031101050a140f04080711030120030a0b0111070303110a05060708012d0e1b0d0501030b06150304060209061207022a0d02040b0f0907 72
    0x80121380361441d6025004481503070b40182d681008004919060304502404a00344103840151003010703c241d03032481015510800070041c40c01e055000e0000b502d5520b481c3d207201c4e02e81780081800e4030000b54001c0c3c069540507840b113240c409a0340d42e034a852092000c869038113558959427000da402c40349240e40e17181c000c076501d002e07502c2c6090040f0404480000300050304025119043e020003000000764003080d645c25040c00c0249039030000d440342c03821400c0040146180121418044c51541100c02903050f11003070005076014841440550303114043c0c240b00309a0604403203404110780100b80c0300040d00164405868840d03400345103e400c40b65070001c044904540e90310340041041c48410307103c4030f40000040394044080103140c2c8611703546010243c8058032103540001d44090959078001103030083d254400882903a072400c64006900d80c4000c5a00040801030f5460048900e20b03000c40c500102c9078020402d03840102d02d902400000d220031b89106801c0410421500601e54030419860301c1401265031340c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 488210746 1250 488209496 488209499
    0x10903090602070302010e060f0f16051e19020111010c080a0b010203040509010905071806020102120708010812030603011103090d0207050d022b0206031504200915090306010f 77
    0x342240303a654810421500032200a100603079004042d10229030048552613264103180700e00030900d104903c411803402c000050f021040b54a4480d202a10a0281c0281c50310342062401c0d070402914201d158448a4014490001e10110354070306506441c0d0043c504008956200c40a40c0d084030200000400419042801c0240a1440d4001c0c42c02e1700b4428805503003001d1810300401c0083c4010700402d54040d407580001a0000c3c41052a40399540480151046032903403010003900035440007400303611003440a030016090030700842c18281241d640c040145002d410094240f149600007a0415500d5500c0303440c1d01a108140c4005503000362030040141101002c640c00184c81c00c00c00754030090240803e4501c902c0542d403031000b07003003201c124000442c50006051f1501c00c440c103a4518020752090002c01440ba2011281203100305401041c2e07810004440c14110140c00d1040c100d03181005108100690003480c1449070400441440c1101035a007003882040010f401d09500340c21401c16001c4e0002c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 488211996 1250 488210746 488210753
    0x402040501052d0f040f12030f231206031509060c0d021303030801060f020d08070c021c0615050406030b01150504030b010b03040611120703152607050312030a0c110f0109 75
    0x400c6c004041f44c2030504920b0801c1c0c1c3d009400104401c181c0d90520107003e500d40b107901c005680045c00c40c10041c40c22a0350f5001c4010145040310306441c090700034030075506501010824245420300403041c0307400a20442d038490b4000c0c00f45a02002c000c141c4d0326002e0004a844501c08a03110f4040c5200307480d131024035030610383e0087c00c1244040c00b01c021540300c00c1c40c40c82c0ca00c0d0450207490304600c00307107030810f056a164004503014004401e009014803010003c84400d1169580c05150480c0d84501b1034200b00e6034601c2007000342c4070305020180c0124000f00c01044400c0c01c401c05004094650f04009050560f6a00c465040c00c030300764061203488500104000030040540700305510600340b01003050600380c0c101903102048500800e51030500d07644400c4602002c150201c200d0003003d940310030a628a01c0c8007100d4005018140807865144038041010a1038a004034140055406650b502401d40d07403040707010406480c0c02c1c030402d001c6c0052041c050b488401c06000d40c0d42c03e41c000c84000301d04500b4528 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 488213246 1250 488211996 488212019
    0x3022d01021b040507050906031e060d0b0c30090c1c0b060402130602010f2304080f040f0e070e100c06050a060b0c1b0402040501052d0f04 61
    0x200114115000107155030281c0301c000d202c000e04450151000511551150010303a69482258802580702401000b0050b02001d40c240d04401e4007203400807480703580c460ba000d22650788800d04009001170000000210840c65000140112004e11800d225039240c078445a10305c1620190b042403968030141040140c0c81400304000000c600d07003031b241e81d003901c520345495002c13203c4d44000003421034060401050b5039960b2a0103965094041224512216607140c20103030080400603c10540729003410490f5010200c00c040d8076484030214040b8840035a1241d0b1081041d42c40580100c2d04c4c03040504c00440d108014840e42400303040c201040010a0420b2800a4040c049a401c0d25224800e1101c1c4041800d034000e640010082d032144002c1001c1e21240d5046020b0441e58108200103c80071595110380740000405203000d505840503460102a01028002070b441a809000c0c04108108112030704c2d0340381c480c00718200802445213055401c62541101c0340c41c1d0701c0408040301c148000b150a0106102c01c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 488214496 1250 488213246 488213329
    0xc030c06050405090a05041a0a0c080903030f06010f0507080a090611120406030b0315040f0308070e030304050d080d0f0b04060b0301050d121107080709050703090203071e0302 77
    0x41c10124102440e25000400718003000b4144190640c881002c10200b220001902c0d42210b550441d1042d94034201c0086401010b0041c60140012040c101054602001004603805009200070102e000d5407100015224403080c8a00311003003040030845c40001c5a0114003520000c100e50391604500340c60902e0082451035040c40075001508011a5203030019440d07411a07003280c440d4200451040322003030009042100300214944620681300801041001054400040610a455030002c64407545421141041013806540c2c140e80104001c4c0264649080b1585009200d0266249080e0360328402409036411000301c0020240c880380d80d001c180c5001d00802010700004022181150700d00703000940500081000500861032544000740094401e810a00e0705260f904102ca00c0d5a9844d004c503582c1d01905d200700c0c404236241202082806203e80168034885400030024004542403240350401d20740d600760321420100c0001e50000040e2240c00d01d1400c410000395469402d0589215442e40300b0701138 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 488215746 1250 488214496 488214509
    0xe010305090c1318050a0606080f1c08183c030409020f070c080f010510060806012a030509040507180b030403030b04020c0a03030608030405150d0b04090c030c 70
    0x1603500e00b11682c071688000f0802040c441c4000c02e000c01500f03560350003d6004e10019050b401801c13018402d1142a8003c002203810349000c964440305484050340d1071750440c0380030000c2c03c10207514141200d031103030000a4004030f58401c4200780c00201112181b400354900050103401061059040f001250508804c4d1131264800e500b1400d03078180c00c905900e0b0b01c500e0080303440d43c3e41d000c00c4103421900f03004191426141e1125040000c585c0f508501d41e5615401c444010b142d40c200340000e010742200301c807410200c1d00c582c0c0307810506882d81401580d0185100710400383c0790000c150903a4010003d129000501d60082d00e03044d940f1001e2205101c00e503030008140b40140103c15003c0518000115811021035500304281a144c1d00e4070b140c114080d1608180441c3d01c20b00210300c1007841c443c082001ca000b01d00c01d413030401626330f0720300c00544ca07030056200c2d00f070f4009080d14044400d110320b40d0081c03241d0f220460340050b1001d41c0c03400080448040110649500c01c0341e01d0180704101c807090070f000c0075251 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 488216996 1250 488215746 488215753
    0xd0b03070501110c1306031a04062004090c021507110111030121031e09080f0c0f120c030a08041502070803180315040602030a0b0f0a0e040507030c060e01030509 71
    0xf50749018541d104101c3c40c11034094070905400c264081c81d56880040076550113000218455000380045116080642d007d5403010310300b40c00c460728000403400c41c103071071707280346c05014245850b20101c0d0b8000d08070680888254041c11980007400c40c2540c21192207140145c403100080303030260441134210381c0181140032918608100601541e45109002010303400d544001c0d0100c000c1600d8202c44030410a01c040104142007210035034242e400c01980d8003030b110b0440494142d40f085040302640c42c1000c03000d00b500200341456203a03042c1000700c2150054070152080b903070312110f0000402d24000450714143c3d80c000c4007141c01e000504440c00702643d0030401e4401000700a0824111301c0e200e110f0001c450742001d0800514602d03640b020302061007680605120042c8524042c20190013950048400400c0140381c2007080180346002c440760303541350304042d048400c0282821124458254050b1081d1002d1107866000800203002c845114090581a0748400d808030350300c0005025500c1c0a080c0007070540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 488218246 1250 488216996 488217017
    0xa030b0306040b0112080d02032404050f040212010b031207031b03050418110a09090f021204020d080715020702090606120f07090902180918060f07140d0b03070501 72
    0x42c08650101d041d03c040d1040d501c07004d4846d00e40440b00b40b0a5400d8021400c1c008400c1065010440e40800b040c11501c180c000c03411156041008111a41100d04401d070440030004a005070074001d0800d1030103099400001011420076001038030741b4001d060031807078481c0000b60100826508c845a03074100c0d6114a1206007050b0b880c1d40180c0a40154010f180085488140d501d400c5100b0790808003c04a030207a026548a41000c40200700d410075008a1602d9401d1660450501d40c1c14422141d201850000300c0741c036520ba80d800c20001185140c400e50751300760140314040125102080001d41460003e01c01680c40600b0310500c442003100404a5124002c10310403210190540611190302004000c1340e44032595030901c00b9a0500000c0d0005e01600d4030225082c00c0d26201054074074401c11048030440134540c0c03180c01e500b10504052420311001d401107400718000c1c0342d1030710140d500041c103402c2c411514520a8121031291300201884500152210000d8105040074458203015180a01e402c0b134000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 488219496 1250 488218246 488218253
    0x1801060f0306050901090c0e0901060b0a02030f09031638030408340b01090209010e0105031306020f0a26060f0f030a06020c12070519060209040c050a030b030604 71
    0x500d5944030107000c0301d07101c40014401030400c1d0701036071075658450f241c280320360b4944d4521580204116038800e84c0e0b40c40c1c5400421000070f601d00780e45028483e40e00551626840503032268850704070310016600f61254250501c1c0d01c1144801d054081d10f00d450304600740d43c0402004600c6585465000b07602c9000c5103451511240301c0707408a0b517009401103a2a03507a003a02580f07081c20030180b48950b80c0b1541404603107180c400f00c590079400700f1a008015401142c2d8a07080814124032441c2e864a02264140c0c503103102e43e5004601455202c01c08103111b2001e400d80f9141c00c026a400140c40c0001041d001500c20300e103540003200c2c16580301c0c00444400500300a242c20740c079004c40160000c0d201e0f5a107080541042c2d5203440100810000c05002d40703051403000d00c1c0c148081d40105034203015900440306049940058070003a038103a1900030300103003d0002c0e500f4102520b0340380c40e42c0c15039400b5020002a915920b640c007440d1091a490303606c03160384403405035004080303851840005200c4d400c080c0508c07011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 488220746 1250 488219496 488219519
    0x131a0c0a050c19060c020c090609060d052b0305010816050906040e0a1209061803030f0309020301021204020102011116060b030f0703291909020f04060b03180106 71
    0x42100038108a0303602d0116201d0030340782c41600141c2241c043c142034200000c0200c1ea8000d80710710103150f002c07244c21802d08000c00010b00da0455a80790412429000a0807502c0d01d2000e01c0a440c2c06501600c60301c19074080b00c1034003111180e18110311103241c0141c0700540f03507061003124010904030010b408c2da107040031000d0034109010310909109100c1500070620741c5e51650700c00502a51746034200c0e03800c000b0610346060320b8103c851200e00441e074010302c0041c00c0d074081c038110b5030144640031100c0e50b101d05565080d5050560240c0d154109030303450800100680f001d100401c900341880440b08158a083c0c8002829201504c2e4040710411b030500c00301c2d18600f040f51030030000d154801408605140030702e0204c2d1a03d004105610712a2142c04000018071140c0c250b20305a0007807003407442980914024000e003503030b00d050b01c5e5130302c04200024240381a00c02d070354000d00e000742c401490b03c0c0d03140b004200020240c2e07016070842942000c00000307001d40c40d00d0300b112000300000e50038000d00c400c038945000c1620307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 488221996 1250 488220746 488220757
    0x3021006060e130e0a030315080a050d0309050c0d0b150a05030309090c13030f030906020102120106030e0c04050703020c0606040c0c150f0504080a261603060b03131a0c 74
    0xc0d03e030003030b081e10046129000f049010401008030b80d000b000f6402c0081c094100e02c2c03c1610003400c0741201043d040c50100b01c4690040c4c004000b014403401d000c8003100109030240b03040d600c501684403840398035900c00300d0300d2a4190007a10070011310305013003008070200310090300040d1060000103c20481510040151034044078200c90301c0101c1e07600c0841c1d0004a02c1681800c0b12280f48400010040040c16400311240d9800390f0384425001e84c5a41c0243e00300c1c8a06580c0c0401940c0150041201a00c01d801280a2448050031382d40d480200750013140613640c065800401098021030100700102c0204220350f8444004c031000c1c0f08001d82610081c0005600d00d80161140d51024030031242c003038694205410644040300e04012900d03103410f18488981011070081c000071702e0460401402d001102c1e4068080300c4c041c009400d10740717840f01250502452400280d00381034032002c0000b0302c880d0213005144500e4425098440c50403c40c9051451740c00940c0600002400c0042406001c00c00030b01650b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 488223246 1250 488221996 488221999
    0x60206070c05192d020604120602120405030d0b1f0e0d051009030f1701090209031207060501050906010f1d040227011d0d120306030203120703021006060e 68
    0xc0810703641482410303c5254002d110010301180640c800b007204460b40b408160116900c169403800c45401c0b0740304014035803070029601c29014001401184204105840d03600d120700b00c01480c0c01036500088002c042d040318191402e810224021702d80c06400d010788107010b501181d0750321107000b0317500360400c1960601841a0810034070482e001c0d842c0d101c807100c7c0c091081c1c021088812004480384403c0203009107800031000142260000c414142c05808214010300004050451702da0038034001400941046550541c148a00201c40c184101540e0041c400d0500400011800b5170404050180080c80038100754100b000b514503400d5803640c400f0701200b01c0d5401c0c0c00c0b1404107442090004001e401648001e0440060844c7c0c600400080f0714040003102c1002e823908a035601e001c10040c4d55000b40820300e581c02c807410510400008191300308500c0300c80d02c5801c0008020752a500171034038001094210b11400b010020b07400341415010459003074040d808640a02405083c8200102084005040c19 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 488224496 1250 488223246 488223257
    0x1305120304170301090207031d061b031c1506080c0a0305060a03020627010e0307050103020f0c0d020706080c040f03080a1e02160506070209011809060c0804110a06020607 75
    0x10200300e1412900c0c42280c2a600880f03449586507100f200007944000000c8002c140319001100e0084d541c150611401c450080485003081ca4076904120303a841010542c01d4035020400c0401034800074259044040860010001130221640d50703000c0024010b500820240100c007010000119502c0046910b6080246401300f000c0d2100004509107083e00c5d00020344c08100420720b440e612614521400d954000e00c80c07020107281c40e440c01502c0d5101c8100820341c040c0c0050100380080c1d40203400414820600340070719803034010880b94072420420030000360001030300080001c00109600030345258129130341c10149440c00e40352410011405081d48802041040085030f0a10b4040c01140c00035011800a10b6035401c0000494000b91074180d0140441560540017401090f0750500b101564031055010f00782d00c030355901307081a07889403800100008000396150b10f01c0a00003802805a1181040162582a040e080c58034080492118010110f8000c3c03440c003100700480b50340000d00c107030850482d0500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 488225746 1250 488224496 488224501
    0x12080304140a050d12050f10090216050f030a02150907120609021002061e0f13050709021617031533040801050108030a020304180219080108010513051203 68
    0x10036003041e02e411005801405000b50402c02c03d0741100003504003070300c100010401a940d0010180c014202507900c8116001e4840040c4032500d001d034002c000324880e002c400c00310301c40c4a640d11843c011030511001126000494160a4a40c04002c60510b800d0030440c040d50b185001c0c9030b1559204100d100d0b0404640103991558288141039010607015900a81400082151904040e40d1058140d89803070051101c413546402080500a20500401c04400c03d03071403c2d00e43c02a00f00c49800c0f8160103485c1da0159150005100d00d2a01c010481d02c40e0014400b002c0b50628103240707100c684006c01d01d40c40410200708001d2982407503552110b03401012515a64400c51113030309011014600508440500211182c80f5064500e83c0003502c00c032103501c1c4c0203000c40e82c0c0701c0800030749078010f014580740568014801402070106010500380c55240c0c0c10f40042c2044080810310450407682d5500c440864800801132221042c2801103607400841c0c0e04414440301c07003590352560390300c600c0d0301c0350103000c88003102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 488226996 1250 488225746 488225783
    0x30a0b0412090b2d090d0506190905102d0b01020610050303270a0803180301141b130b071511040b07110301091b0f0315020d1103090c010912080304 65
    0x3e8400005000e41814288869031507c81e40c0e0751420b5840328204482101c809002542500071006010b5024000d4000282216080b60103082d040401b03038102068070010300707082c0111406e20420b00105c00c00100704840a2400642002405000308528540c11902803080742c0f400003c407501d44600f00f10011107d01d000c1901006c5074620f01505503c4042c4100006040c00300001900d01d001086452603d150315000c1018200e1304265910300013140c4110014514640095201c603d43c50001e40241c500114062005c0032641c298018000b41200420344000b400303501c1211400d441803107041003000441d00b08003070380e181c0107505c202c0e1031000c0c00044100030040d42c0c0c0d030702428054005c0d000703009584007450314800c8451901200e0402c04c07420800021400c0740040700f03408998108000004600d40494028080e5000b4a01d10480c80e480d4440010340d0750400006510032448580078044100d0740e200010001e00b513691102c0c43c116400701810020441002c2100c0d08180e0100b02446034108550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 488228246 1250 488226996 488227087
    0x60d020a0e15041803020114060f090a0e0303042109080714030312100315020a0e060304020607020d0b18010209030d0309031202030c0403230615030a0b0412090b 71
    0x1402d50800c0c2804019400080703108400d081d1507210390001e10902d1043d024002000d88110350540e8400084415480c80703007030203940c0580000889a0104010043d403300740d140d50300c10b580403501c4690f00403000020100132040c42d002d100e5a881c08611042c540b055055035448507009054851000521100c10750f602042100c610b02c13803452440d072891410014001d074501d140e120558210005030903840d42c1c0502072007154000c444545031112134012200034000c41e074000401c00ca8019200f00f02580250703540020080085205000ca1724251404642907902181a4000034400340c6c01800042700550340070a8030360921002e4500000c0b01c00c1281021030340b00084072800001c00c0d100005014000d40103900800583c0e00901804c00d0510894140c9400c1d000380da07400d19080d401081c0850300e0302c00b29007004404080028115409c465080d1210020600142d40890b10000d4103640d040619812421107001031203000c05890618030143e02528071501c0c52449140d40e6244020000100031200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 488229496 1250 488228246 488228281
    0xa060804211808011b090e0f1503030d05040623040209060d0b010e010609050d03080f0c041d16030513060e0313120b0a05060f1201020c0d080f060d020a0e 68
    0x2c2e18400040750b40d819401d000341401880c688064020141c1446200d010718403020850f01e00141d0310203603650384154950b940e880601030740c00c900e10030461126140d07410409040d83e06005c1e840010745041c185007900c116000700031880400130207811140b0340ea0852549141c1d200350161103c00d031566425000603c1d500310060028259014034002048968803500c8a5068503c95203484002e15140c1040007484409021b0040026600300002072102c8548040c0039081803088081905240d243c0c88241511845c1e1048250184110000c200e08610b410310421580d9103035040410543c20003560000f0010b251400280c03070b80b40c4034030492201c880100308030f422a07824001601c0a803912561900031710300c5502d00c01e9034603641c5c0d01e0220f460440e01348140346c0a040010031a1104140100902c030301c0705900c1c070003070049550a2080080c8445c09100d160200c0c0c9080c1d81d400c4040c5061000808801c1000d002940104980e190820040e00d4501c100401c0e250410b40300310103541d07015003d68091110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 488230746 1250 488229496 488229527
    0xf06030a140709030b0a1e021303020616060f020705190f061b030507020105010f090b18040f0203160303120b0418050f1509190206071403090a06080421 67
    0x3a4010010032543c495078001c1624480c0c050003415480380041d41017980c00d5901c0c0c50100c02641d600e1180750700c1243d40101503030202c10b082e041025903240c00107400e0380c00042040341c58012520070042004020b01c0342c3d80300442d2100046040000769102c05685061440300004c00b10b032100c14500501000c6491403850641c030040620404404030840e030aa1014003408101080c20314021601003801805000c0c1a1072500c1541040304d458481000301416110040d1a041052449600c41d81d280c0c005070319100301e02030f2107450b0b15592148140342c500f0a00c01024240300c452075100303000080c0e001c42d28442d1004020030105003207440e000050001d20450810707074484a1511443e0f001c2140c00708480790064001401d03103050b1901c030a0071840b0045d04940820b00c0f9081200b0130f08500c0702e90581c002c1d4032070000d840542403054513600c5458a0001c1481e03881d003a4800b08a1810510708a40070102600030361401d8405412b1503550f180814018141841c45207180328000042244591401074000302d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 488231996 1250 488230746 488230781
    0xd02091302031e0a0b0d0201080a24210c050d060f020c0f30130b07030903020307270e0f1002090306010503070609060e04110a02010212060f0f06030a 66
    0x620503542442039182c0d150501c21800b2900c0050713152280d92113003003220072000d441c0e9504801251300440361100020002c0c44425521712140c0c1d044c80c4490040d1782c1c00c01c89003100d0380406003000c1082e04011500d5404102c00f680004143c4c00203203000c1c0e070840480703e0035100d60081503e14501580600504c144021900d032022800b4401c450300001d0034801a409407040d40d07001022005804040900c040420701c0c10501203425a034404c0c072a80089c404003400a05181c2070356140c12061149910180003500003900ca02c0742441075180030300c03104005120003104512020f504200c4644000b02c0c61040103c0f1944e0b4002d1820002400d00c21040d11a00c00d01c19030f408000c2e03006804e40213400c003010140c000d00c18480003003054140003480c8010b81c3c010352108041e20b0703d044c0049034203c581110860f0000c5e114608801d0890091016045010007500056142c07c0e040d00751186129000b0101441010740c2d40001d5400c0d15030728039164400400345d0302c10b9526500c9000d403401600e0107201c84d9180b440d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 488233246 1250 488231996 488232001
    0x103305030604060f0b180a17030307030606030c080106180509130c0f03020f2403010303080108010c021605010f0c170310060f1704050c0411040512120d0209130203 72
    0x5601000551140808890420189444d8a040480c40c42c60780114582c052040081040e07030452030f003408091701310062004010a44410030b80030480300c006464031541d0b001105003c00c41c0d4060042e0000381100f4580ac1100c13502c01c0b00002d02d9058107101c1d020070f000b10726500c011421045610b40e400742101514441036030801a521426070002e15209583c580144080032071034041c0b4499030411640c008094124034500e48080004040400c3d00061994a10320030000304030303039004081c41c001c60003030321143c00035850b080005080d82c4c81c072920f04007150414201c03640d601080301c14400c01c0e50000e28141088085403401901d900c44c19540103403c03010031205071001020b140000714481c0d146a2203440a0580e50b81060f210749010b010703041d0108050030001c50880c401c108a8a9006000300103c0b081f04c8072410103e002c8800c500301030702e1a410b00207414420b1f4140701c4042a03107080401c00403c07a000c80c0320203107443c2c3d0041006030102d590700050030441c1c960b28000f0381e2083d400c142c0d404642c0c0e030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 488234496 1250 488233246 488233349
    0x120105090a0b010c12021e0d0f0e0a0e0c0705070e07120b10030e0c03030d0b0f060304110409021f0207140604180b2206060f05070b0610020f25090510 66
    0x4503610052400001c3d0092003060783e03117110b485010058ac2d40945000091810440d046038120801800c03507182e05424440b100204a0406c00076000304214840c841d00ea0030006030040a500c0744004004595060552864280c5c42d0405002007a02207440c00140818040404508185010002d20b0f03051001040d08003074090707a94862041c148045034001d0b02d0010030400d0002500003268041d14000300c800d000501c074101078025083c05032005284c2d00c4040c101d103403000740180741e200500c8016030003001c06000da00d0072407103044012101210000e05061802e8007004804420a2004240549a0b450702d803c603280d0b101c06080100400d400720a02400410b1428010411840341c0c00c0080c0ca801c02c6001d181d4040c5088070b8000ea0081d190b001103660703080138020110143c800c408114403419050300b42800040c403c02c038072a10090340046c05e40440d0349480e0400b0825400c80c0001a14020038482d121100d84c1b1403034100c800c407100d400407218004402410079441740d105081410709000d80c0f90b048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 488235746 1250 488234496 488234503
    0xe06040f0305061006020115090207111314010b031501030b04141303120b10050702031609060305010b040506091b0c03030414100b030601050607080f120105090a0b010c12021e 77
    0x42c008a8104413038041e40c0d1201207003030f55131081e0080044003201c542401640d04a800400d5018040e030b41222004120b9000704041007032905001160541e2001000c212200c0b801c980c600400502c000e035811401c102e0640340c1c2c242000c03c6205d0526035500794004054441d90000860940c440803080c40301d2804a03842159450b00010031000517018440c0380400045511071540050406480c4540410004d0350603641648400411b9a0501c00c408003480381d02004c0607100042c15800c240400c140d45185041420f4030300407282280b15500345406c003e41c1d030329500d050681c071285c0c034001c2151400450303121507501e00c40c0c0c103d9011180000010072090200780b12823401202440822200501751030f80303208040b10000741480350b15030042d00040010b403034400301400c034050088000c941381945208c80d0700184d5110030925a0b403c46010010000d9241100303a059109011407002d020b0303c0c20300c0c0c0000300047c03070445c0001c1c401840b2a00920031148204030300d07400e040440c0c3c0300d400003907912980341d5078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 488236996 1250 488235746 488235751
    0x2070519030203071211010509030d0b010302040506070b180114010e0c03040203070e0709050406081b06070809040c05070203030705010914031e070f0506041518050303070e06040f030506 82
    0x4161150354294034a4141400400d8000d076015805107003802c5440da5a11120309558800764100100701204280c1c0b80b10a101e480e00035040c5400a40d551103c0c4005d00b81518040500281810700c140801c20090702e403a0221030720164231022845035940d0351951400d0003070b8241800000f5600e00001c880800c0140c28440b41610050701ca83d04c000d9442049424a5210840340250181c12404081052140d6a021607030008203504000c8a4a511a008282110b40c00d901074401030b03020059851701f146800070710341c240c9603050b1015880e040310343d00e8030000d9129151042e4001c540e21400481c18900c942d058400ea1980242039950f00c01c0d0604000d030117014035a105a46108024213882000c0000004403954844810a141d80301444180fa0b820503422010007607918240c0c00400cbd0000840602c4107a110b03030320419070582d01e0503912501000f01c81030141d6000c401821074102e1008611300000380c0e0340c420900d10b8808011441080868505d0082c0c3d4003004414400340c1011040240c04140c561 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 488238246 1250 488236996 488237003
    0x120602070b01090218010f0201060b0a0c110a061d0f0d050114250e1c08030703050601020307080d02070f0b09010e0114010e010506160812070f0201060b2d04030302010207 75
    0x55980b80c400d8141241700f148a0180440c040070311030080e030350107401d94030700300034081c0000645180d40b120980d0040c3c0c0000220070002c4c10407031f0150700b00070001c117454485c18400e44030080b22900b8468041c00400c03e966503a207180400b60981d8016a81d20040a0440d403006030a04007444014540f00e8040c0c002820400d1040c0101000115024540f1081000c505a00c4801050050340d114090f03412110603c441074000c02651b01203692900c1194082c103940e407050715810340d40d280000000b004c880d0b02130b14050441d00200706102c00f240c000425605213032001c101c016aa0295464071440401c82040c1c0100903e421604004083c8010b51244085030b00040081c085944210b40f254131360b407001d0048402c0c2844d88001030003582404005025000d40c040c5c3e0300c042c490882e1312800e10300c1c2c206500f0318103410715403806c0250281d4420b1100c111511075000a109040c200790064075507000b0003001512502540404800c1c1d40815190400140c4e030a181c40c554950700c1e410024040d51100c178058 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 488239496 1250 488238246 488238263
    0x4050a0f09140402130c03090b040c030c0609030c0b0c0a022805040501180c021e0604120302071106090d06093206070f0302071b0602060c1e07080412060207 69
    0x144114884040b6051056a00621010f291980550113000420040c9803500030103954582460000d0303200c078800f90042c0c0c098915000c0b903d00e9442c0841c8152240d0f0449010404040e8003080050001d00304401a40e804c600703610303181c20f00d032449030b0b00c0c1a030b2040c0003039800000055940c40071074600726880744c12680c04041c00b103541c2d19030b41031205946080c8245442c825a040b580c890204071a84001051061032050700d00b0700e440100d03142c241003030160031514160011070a010820130019014010301503181800c0d8200401c5d40ca03004a5604031302c1c0e040d0b0080400040c1040150b4130540f27003200c01c9500031410041424107041462030064030850031259444003c04c1400b06211401c2085600d02028008110561303d110040310f1011809440c03a00b4190240031383d00c0020191b1242914104a28119110080c0b401c54000d00d4040080c0001110304010406c66000111580c8a841c2e070602103c0c1a81d501d02c000d00d462211441660302500010000d0110042006550303002809858001d4090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 488240746 1250 488239496 488239511
    0x418030c06050108010b1302030705040b04082b1d13110d06050a0b0d09020103021c0b150414060705070305060c030709061715040e030412020a081506130204050a0f09 73
    0x410b003280c1056a08075400b80110246075501c2406070009d40e0f007c0010700d01030f410295640a1928160000d8120741c0703050b00818504840c001288411510300103d0002d1503400c01c642e4040035042c0306000c8416500941c1600743c034035241d1150310313083d02a0f000c03d160400601c15403c03580303030068110407400700101d801c1020014082c50500d490703500341c407400c1419a2500004494a800a00c2401400c9050603024424400400407007812568440c81d0010080f61540304030b0204810101c046406081c5020184001d000000480843e102100c0302651074682d245c000e4140742d8a0100b01d60308c02882442120300304207000b10448041d60080711140c45150b407664071140140c0d010a0040c6403500b02d295081300180c2600c07841da004a08102c000b41c000540202c4c0d042c072040c03c0d64403a401c84414440840c01000842c00c1c182004001044c9100103001c0500d40307051141000f183c00390142d4843d00b000748003102c14280c9071f81200c0080c40f00400b01d240c80ca944444540d6220071a110b2520741503e41860b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 488241996 1250 488240746 488240759
    0x2090105150418110a0e0f221a060a030c080711120d1d03180f06031602031b060106031b080a020c07120b0f0702030a0e09060418030c060501 62
    0x481c101103040150040c2c02c06040c01102c401458582c081d208103241c0350303022008203800300401000340700000e5594407072201d0010180b046504050718181e000312000c0d131b8000080042c0081c040c00300071820401159071805d48000c90031200800d01ca450b03002100103260a021601544580b241042a89480066548203c02071b41c1d40d1116054400b27858000381e4980c060b0b5501040108505c056100000807c3c0a130441d48000e154845406400194000a9000105a51845046a171400480c0c0c035502050b50000802c40501019080603901e00c000c00710b40903c103000f4001c2d29141c2c8001140d407500c521108100b103594010a100e4400420302d000b154600003c18070710051401005511480340a031540300c0c8900003544215076074240b6001c1c50700042103003948540103508882c010087c0505500700045000c8000b0340107131001003550301c2002008401c0c0d410401d280e0545508031843c0d2503580d6241d000c9406049041194400c0b0020303000480704250300201e28009a0303000f43e45c10000b0f0380c1c071803c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 488243246 1250 488241996 488242009
    0x5010306050d1523150405150609130204080f060a27170f0d020301180605010c0609021507080d050a0e07090f0f0509030c120a1d030c1003060302090105 67
    0xc81c06030440c0b00a5043c6605140180c202000c082a11142078400da15100400301c1e000e2000c0e5041005580c82d500710301600d18060103915088000e01c02424009201c3d0782c0010703050710070746850310301a008003041e010403400c181d819940105030040c1035859400341a42d80039100c02c01210094001031815036803e862100340034005811520032110b1840d0181c807034803900e1804e0030405401c0c10120041200070070950300b1801401d69610340000c00350b03c07941003003915255809407070303006101240740500422050780d00c003000010841c0c2142d0001243e000ca07001141000308049941100010001004d10810840e4001480c600c404150100100e4854140d20800d8610580c0c500010358482d800902c403203001507100003562145540c000484403400d501000980384119110643c640010400201c0c20109208054989001000c80e900e4031011210141108006104054600c1010550491561020071505140703400c010603500a01c003000030014041d0003640000ca004600386000012a403d050707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 488244496 1250 488243246 488243269
    0xd120f0c08030103060b040f180b0108030a080c03090313030807021f0e010e0409021c05070e010509070c0510050c04080d020309150307140408010f0b100c06020f090402130501030605 80
    0x88210b10316443c64031110b0162a0f010b0405a10590741c500c001e6030485648501509860f0010841003a21070500b40000c1a4005034885131842c2c01c20442c0920069100d0b4107140d101d400711010135180d80f20070020f0b62550252200402c4000410000030040c0321140c4007502d09284220790204403070686000e00112a5254810640403506603c4560005c0d80241c03e890449030000c1d1000132211050740004400c20103224000203c401030781080c400f800418090318026255015042c2020351508000c0780008000170f024804000c950700c6600d0400101303110109141390480000c0c000c1c1d04042441c45900d43c8148103000a030711610810b004814008003c1e244180340062045408140d51901d001da290700090100c420802580c1d640c850240d1124081e20182c00607000001e031280b504031100c82107030343c2c0040c04d51084458244c0155819444a404244036038411300140c2c455881501c07000c124022909426481800800c1100c280c42c200c1500b84112034090b81d062100c13564940500c03210030400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 488245746 1250 488244496 488244503
    0x10b0907140c030d05060f01111921090501090512030d0e0c100507030f09141e0a120203061003030c080a02120d050405060105030613030e030703020d120f0c 69
    0x460002500d00d0380562800318805a090280c245015941c03400e6508561141000300416640c3c0d10600025003032a41c0c0c00c07200481c007800d01802c00580001c45c56900c0212540c140c41c4805034600d07220801040900c5500b030001c851030319004840c519800134280c0707102401100e0020701c0d118400182803400004016825200c0005507160506140001001d040040d03030516643c891880d01c4c08860301c2d41d00c4140911071107587c0d40c5403a20b80d50b14004120301d5010424804000554900b4050880c0c8500e00c219408401c4541a8180707582008954004040201d0310303030b0054100d84002056040050240380ba0344c4220156442076840d032046041e209814040130f40003c0e0040e8216001410003402003c1d600680e00407a541415003200041060388030f141c40009294444080c0000c0000c100080b42c09806d007107000d400d5501e800141c80310b00f038200f101c0c0582080f6030106441100d44040c00340300055070300980406c080c60101e0400d07101d00001c500703420b0000b441c0f21141c480e10a20481704003400691 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 488246996 1250 488245746 488245759
    0x90303091505101a0f0427110f03100302091302041506020c12030408191e0512070615091d01110703452711040b03010f0504050702010b 60
    0x8000f40000103a009540034440e4082c108241c640005c0c481028000402a1940b00f80001506002c81140824200e031010407190501607407620340c03407500e41074403200401c0c200c206440b95501000a95404040d51010750010040c10a001203803400070700040e140383c001e40f000d018602d902d21249045036001d01c0b4a200580080300e00648504d0406507400300000342e00112410680c40384901410b2803201041401c0865920b00082c04004292506120700071078003034160895074a0340c45080d1140e05901c8100a2004005504d00401006610080346041e40108142c68113881e1990840204007011072207410340f001250030100204140200c40507000c814206c2801c00400d59404d8a0403640f09210300403591209604000100c2c100341e050f1400500d0001050030a000381a641111480c83d4011110910074554001001d200d001030070480308003400c10000d40c845a03114440726501590308407081e075440c008000114000c440143c1030039160111401c10151300c501d45c06a080307808025006070000d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 488248246 1250 488246996 488246999
    0xc08220b0c03040804080f01050105010e040e0615030109060905030a03062c0a0e06150901080c06040302091008030708030a0c0509010f030c0201060803040303090e1b03040b071209030309150510 85
    0x4070900069030f00107200d088850706050b21001250b0038a00007030b142e030030a6075442004100c25a4483c0001a0300f0b0002e0b00d0810560100306e40e0561200d80050121001c0e13604001034840c540c0342540050781c0c0e590440002c000910280c980103841e0745c0b10280c200e000034148174002c612101c08404503043c14100d09000c0741005651160036840d940001d040d20141c1e961400300845403002407100620441009205040b4507036040200070100f401a04008403030707031100074030800744e45506086409981c1c046680c400329943e40601d240d4074140c0b507000600180800700d400300c100400080914040d5004d00d0b4207100c0d8207007402c0225841c0c0128140c841c00500c19101d00d00802c2d001c0d901610359001144000710391661140a20703491607006038021000543d4451040000500d0300e52440e400c50381001042200c0406205035030410b01010f01301900c0b944005010074001800382000c4a6400341450080c4000c00c0d61341805401002001e00035240022402d000f42d24030051849102e1041649560610906 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 488249496 1250 488248246 488248261
    0xa0c090f0b12190c05120c0f07030c0c15020a0606080106050303180301240f08010c050928060c05070f030503120a060f0e01090e0624010c02090103051f1b030209010509040c08220b 79
    0x44be0f0000e0076900f491740f02d080460600048a0075000c0310420750003c0040c0341e194039104045075510340c4a4040c51345458001d0042c2e5901108490003003442c140d1a182180e101c400103130040030082c000301110728010f8203103240c0103800340e17441c000c541c10810185034440c2c0d501004c034242c8003c0381c000c10010f4001c1003205018908503503841e00d961110016050284200c502072104e41005802c0000428807442211081280800005000e029030350415100b0610b1503540994030b008051301d1001080502e000249418200d902803002855092003400d1029560580c0c5140d0700c0c02806035524560518030008866140002c03070600400f0305500504081c0420044070200541c2686000e04000c9480310100142e0341d9201103501a40c0214050f00310035040c80075a880100500302c003081e000b4140790802d42c0310711681c2518140086241000741c1d0b2a01030341e0040b1240d03c80c54100950080c030340680801c503968040d011310301c0780030200b8000b100408654020140e8034408400144629925400a41003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 488250746 1250 488249496 488249507
    0x9060206040b042d0305030907081603061112040f020103060b070b1602030909090c09061c15020409020d060515160204090f05060a0c090f0b12190c05120c0f0703 71
    0x1a4090b119000901d074421021603d41040c13421400d50000d40003105116200341c09203c8580207150901c0100f45030845104115401e10302840050240e60f5030b20031a010b5540d801c0c0c2101d00c103501030b0407240b003039140a241514580d00307150001e900180c948400460303c2134a81c01192400c6400c8500c00703840350784024007036442d000869900b60841c0810322850f04952640030b00c0c64014010764001d08034415080080c022040402412a40318070b140030500716108126400064003e0b4002c068003485128008030000680f2541d0700034004d0724400503140d048031456620040aa8800f00c0d80074004071b66070b01d40302003203010b852446011400714a17824401032906920281c2014801c98000d08811850388450303040034411260102d1147c1c69070a00840300b584070b10810090003114504c090344038101880c8007002c6c00342028141074954402d000c14000c412000c040d400c140325a04d814030100d120150014419005058010055040d45000c00c030300e40c90741d40545842c14031201d4140c4c10b0a140d910704982 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 488251996 1250 488250746 488250773
    0x504033e01120903090302150324010c1a0a0b0f18040609020d05030a0207050618010f120203070914030c01020a03180f092a0f112a0109060206040b04 66
    0x10700c10310046010a05005003d25000c580c00380e158940268a940103000d000d900120312038008100030020814410707221004660070728502c074102c010071035182005a90128500e00d02a280340c00c540b02c1790125100ca003c809115403200308042c000b00602406105851090344161980188d41040e40400c03400041d940c1030b40540031300404241100b07580c010030681d1919041c1174a032500000f450039512a0100014001050260f54032444d042c00403405040e503100b2640034a0404c0170501c031003007a651250030030700b200080d02c0070704541d05e0400880160842003903100d864840c100084004056140204242c9211001a000f47c072100e02103590403903040c0c240d4443d01030840300313107280860054031200030341000c1c0c0401c21000440980d80c4854884110180401d00080e52030b0b911403d4600b50300013400e042c1740020b81041540c40c15004405070078074038002610008000c03007d10341040b61074580d2848085017820780b81e200c032781503c1c0c1c07200720b803103107012140a406812500007050004000380380100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 488253246 1250 488251996 488251999
    0x19020a09090503041e290702040c120e0c0103061d01060f020a0807061406060c120c010b18011415040605030402041404050618030412080903030c07060504033e 70
    0x240382a0315844503040c034140000c190705004005c0f40080c001c0040310328414980c0207208480010614214010b54441d04c50068028015034941034081d103030b1806105514410003034140240100c21400c2022503071042d01d50710660000b0300700030f800642209245441c0499420305a01080700b40c0c20168141c919610380c0000d1021032081d007054002041c17003080034085440c071610010500e082d005d0340000d42c20b6009803103141328000070054400c071900005015105456841d0b00c064441d13129074800d0b4010081111016081402d0583e210240c826845075203041e80ea01021142a000101d424090705100c8844041031140042005200d6a8025001b565016200400205851401108590400805076800c44103584110f050100e018100b2803030ba444c4030b415400450810b46889a42201070207140e40c05090042e000600305100c0e20700f4012161005001d408441e0ba0079a036000080c07403680720713201c1a60040034160214038403030407410609944140c018802c40003664603a042110001010812704d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 488254496 1250 488253246 488253253
    0x2060f0603070b07060623010509010c030e040e1f02030606070b04110d030302090a081b0904060e07030c0801050703020403030c11031005130c08010209010917150c0c19020a090905 79
    0x8a0b18200f50091410703c0c8034100c0402c059142c100300c2c00c450b8611030034044403102c810081e41456607000c8107032450b844007480d14030f000d035200f810191a08006403031610341241c20038040260450002a2030654017540d090b265038403104040c1010201d02040ea52944d0140c420007085010820b00075445400034000d40c0716000341340d1200002201000340c10004c4021940118410106240c410000d0b001090a28050000c004140c407070b891652000c19911441445042c01081c24080c003a4020020f070186401210b0748507071641415410724281d0700c16140c141d800d00b0009140b181c0b190003034500300c0390f142e01c640030364419507510940d00d215080003813901403081146030b64000c000d50041e58000c14003001e07104105817181c1400103498906030080b600b1a8010440303001c00e80d0b8441d03146012107020240201e803503241c8007681d5040040c8c0641107111080b806051240f0340c038030400149604580602102c0d44a6410000032a80d96200c48010390b21a24448040102918039000407100310310031401c0d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 488255746 1250 488254496 488254499
    0x30b16050c06040b0603010e0601031518120306051c050a080a120903031b0203130b03190603030306260c0609130501030506040506090f0307030e0d1a061c020102060f060307 76
    0x1035407802c0c0b011201510540300007002d028150a080c8944008444a007010300419810342d216031420350440d02c05251610340d24801e0381d083d290030349407030543c881e84039005907040b1007a140b0040252200740106442001441008001304c03402d01804003407144d2050140000e8801e584480b00726800040411041c018240400031040f8024810020f10b94841d0700c000403040c0658012540f07840807040c404041d50310420660541d003071580a814100c525907605256691350355400012442c1590100d08003103070030081c1c00b00405815412500543e44074089085940842e204041c01464070311030401100c1d0815418100366041400080942c0c1801402a41740d2041092a080c00c89400741d0042e22503800c41401c0c0403c1000c10301c078013900480700070010700c1149a10383c01c082d16440b4000740102880b02120040020f901c4803504c0707041c1d05400454a188440b660b10301194890012030300715101b840c881c000c283c624446022035003900340d0183d004040e5035840060f504060007000e0401c1e0b44c0b51180e00c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 488256996 1250 488255746 488255767
    0x180b0612130b070f05160c030203100e0c0609280f12060c050a02060c0a1716020c03030f07020105070c0b0412060c080c071b08060907031a01030b1605 66
    0xd40d18099001c0d0625864000850304048440d03140c0544001c04000b0034422805115602506460b8078500706880640340710303514503100704002007a50000b50580515001c818440007036600040b207804034401074a15038141ca1007004518070030825000d0740702c50140503680054005410090348034030301ca421100c00f943c850141180342d0a40c0d074456034401a101c6140c000304030040c01848900926814407a09110602034060340358070000b402c003180c0560121707816482d6441100c20031040e201c00c400fa21803d0400004945145403a410300c0b03005440740324484440d504000040b00c9402c00201030803820210240e004580340d44c00b0302020340304141104400b0a40d810610018001005070710292603840f00107162010a65124180e80420b0107420810092000c1c82c136011178003032039032215003404520515000604444131541001c1d485200b00c0040180c1d00d40005514070549000d400307030840c481d130b4183d41e00e10802e00900000300500482d0002c55400c1100c1d10101d017100c1e0f02810b00701d0401c0034a20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488258246 1250 488256996 488257027
    0x3050f03090c21010f02121303020c043e0a180320090a140a05040218041101090b030114010c080705060408040f05030604120503090705090a05011e180b06 68
    0x102c040507185400f80301c4442c46000b440349494140407210305505101040e503260b41540d8009003d81c01030010301107114105842070042c1051648020300400200305e50604040c081501e00c00d0114403008045036500100d400e4078000303440480280d02240c0b5161181c041100c10b90801c04010f100b04260503c0800001d11089545007003c121107600b030100240441000480d003c0039007844665440d100c01496802c2110990716407011042c5404103280e01c45201190b0703104801560920540400c1084c001000041000a912008241c1e540b099498a0f00c2c40c10340c3c20720081c0710b41007240091003605a819400ba082001c010340c01580c10504007c0710b502c50390f080900881d411506220005014803540b0038004190b4040c000a070000e203601d1410f83c3e41c4403480d4000300558020701a01100007a1901401c00400b4003901c00034245580504201c51044042c0200b80070b22a01c0190010020905070f00320170021046901c10841c40654140d840820700080050740700e2543c00400130446512004a07d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 488259496 1250 488258246 488258269
    0x3022803080c010b060403030c02010c0305090d0b090c0307050a030b0903130e010303031103010e0403030b03030c0106060329180c120103050c04200d0b06120c040f050a0303050f03090c 81
    0x4440e202c0e65400510485421598060000382c4240350034001400825440f003420318030142d082c288011121414181641c507401a8107109a00600c408084000c000ea9802c40f940102c27404c0040300d1480481d0000c0540b00c3c1803500806810202d0080100301042a80000726000340742d49c019203142000d000c0080b694444d01c1d4010810b202070340c10042042641c14441c2d6080c0310b110340d03180340c1154189511036241c0d020240002d42015107882080d081a5000d100311420010000001c204503a40c0e00c0c00a0060219902e02e9044ca1400c4402050190420108600c1c00000100f08004e0194001100303100d551000e09100c81d8a0b000b4882210b075100e030b0601c1d40d4040e500610091490104903c100000d40308000592540350190141181e00e10100c907042d00d030460030a084c045103a1070300c480842c58030700600c0100c1c40c900d01e03d8400d000f001d80e0b562005109440300c581078000c281c2d0b2030b00300340325582c603c91000038000307101044407000c0c20034040003650300303e000d000940c1c01d0409481c0020704070b403d51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 488260746 1250 488259496 488259503
    0x3010207051e03071101030b030c0603091b030f06131e03080a0507090503030a05070f060603261e0a11060906012607090203040201090b04031104110c0703022803 71
    0x201041d044402021015007804180b2600840c94144555601c0c090000c004421a051548619107a6416607081c00049032034240131342500c1e1a8505410880e695040c0000c288100d0002d0660081007424085031004410034464001e046a84510031140d110030f010074000d403603e5500030340c109000c2c0039601c512500d190007070b0346180031801c0c1418002d00326800038040c001440130311401040700c4d81700401911b8550101342000e5490350f045040c8007a1100306040001c221034a8401d01004005408810f01d09034090100041d00e0150f003004140d0452107140204a075074074811241e001085c0185000304200d02151a00440c400c90000001c1d1410006956000c50340d0401c1d4018800d0310810000211410a59800440c00035100451b1980310b00680c01030350865500003000134191790040811400400d03070040052355a0341c2d241480c810012130500b405125904140c2d503282c1400319801070707960022804c0c0c00f804a551860782080000c4410840100c1c10450034102480f02840a03131001009500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 488261996 1250 488260746 488260753
    0x63d180b0a081e012610200408071413050f0708071704020d060b0306040501090201030605041e1d1b030d110607080c07210801090e0d080a0b0301020705 67
    0x345254040c02c5100014082ca000042146032907a903280d58180181c1121400c008100d1000d000c04035200598034000c0c41d9080d45d20441c0c201c90004132103688403000842005900282810700031031407001074407544c80388041643c01141d040c40f0301c60b0900e8541a5074180102a800c030201600e080c0015500102c0d44500b4404000042140d4a5006149a0383c089618a44404074402c40440284044800fa0020b0b00034003848542c03408100719944080100740c002821a0080c0ca802e01d801c50181080090407800030b41400c800003068140b40c01a00c07a03090700c0c44003291000840c011201c008003020641d00194800c001d60303560001e08144002070300811811b04460721481180285403804102015480402c8124400c07502d99907070104d80d0a0b045100740c0342c0307800c9076240d180181c040e50291b82c40c043e19441000c0807281d5a50411491940801a036840f441c01c243c3c6c0e2594460201c7c1d419401ca44072039009112000c10003403080340c085501c03d90003200040d2854114011a00320780150781c00f05c07615031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 488263246 1250 488261996 488262007
    0x3060203040605010b04120803090c091003050f0622060b0a06030b0f030631080d050108010507091404090201090f030f150902060d180204090b063d180b 67
    0x701d034012540501240584a07260520f810001d1f110100c40020103000c0c001c020002c145860400c0c440101240350007409050141042541a00882c040f480200d4243c4a13171940c9491082011425921032900d42811070942e81018006403001c4610034001c0300d42076694450800d465440361f17419070290403d0341e4006203c1d80030034180140c0074001c1c40380500c69030040081221400b8084003a041d902101099445040e080033640072040305840c50040828001080b000112a581c2c0d10450499040300002d0195840d605800d45d0700a0076805100090100440c80c4c240d43d0429800c9002c901c1c1c03042c501503102503904c003508000301031300e42c1088802100400000040c01174008401c1540440980100404070666002544610800c41052078080d1200640000000e8204401640d0390b0080c10031f00c0000300301c2c0f4092a10f40703030403110740c0d00c11806c1c15080300b010583c2c0d40f584042d2141c20b01c081c03028030006500d031084541c220072560080004c114003204402c111040301c0001405842103d42e12070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 488264496 1250 488263246 488263253
    0x14120114040b0604030b0402060c100e06160806090c18090a02310909020103060302030303090105010305070b04270623040507050c03070605090102190816050c1506060403020a0306020304 82
    0x48900e0b00e5142c0c442c0344240710500104081c0c1112981050741118000c0d641c095280038141402d54070001a20b11a20741250741c1984000410541d20640807031410304480100c03d43c0585044030280d50154010b610500003a99144250000b46007a030f212081001c0b408241340d0016501110844201d01400e4012074039200f075050340030040a60504090160300d800501000c041c07a03080d038038130990000c40d03142c4001d103007564026408a4061078001d0f0030799960380703010158030340070b03040c04c1c48111403903c15103600185024410742030364162151002c480701510071200a511081c8074541c0c141e03007ca5560305000554441920f600700100d800d0b08102c2010f48000c0041104985008050b401030083c104041913240e60044200c0d2615a8070003400101d94503808a010700901441c440321340602a458540e4076000e41083ca264415807010034108004991040c00311034500448005e0221603100b000560507600f140100c0310ba0108015117003504203583e94000815005d0b0030fa1003514003990000c148003c2c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 488265746 1250 488264496 488264501
    0xc050d09050105190309060501061805030f030a0302031f030f0b01060c1e1a0907090501090c02030703210912110109081608071a160206090c011412011404 68
    0x41441030400100091401001800314480c40620b0a01e601e031007110a03503e0f60080d84015286030300a54100819070310b502e0041d152542141012028400001c030004003460001000c42c01206030001540c280031029405030040d400c003a10f10105000841582d4a144d4641c0c554031008501039141c13012801014108504d000303030180c00c02020082901e4580002c101070544000702060720f4061a41c0354000390809250300c02e00000d140462400c1c20b0140005100d0004480e025101084403c000e1030760784000c04811100e4074240600507802c14028440402d003e00100800c406421214450402115403c20200c841a280c04c864103a070441151600c6a8040c4400000561540082100000c0e503192081c447c010308a5051000c0d06444813013003001f0300c241c1a201e900750702080900882d06595414002c52108035003982c018802c40650183d00352001440038007800440c00a0b106d510707003031001112010380d070f984403523642c1100704140b45020f406408003e00034200381c034850401030ba114007000203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 488266996 1250 488265746 488265763
    0x302120c12150403050d020c0a060f0605030c0a0e100b03040c15050309100e0a0204060e0f0c040b0a08072c0a0f1d04030c020a0e071b0b0f041506060c05 67
    0x10036601c07000321000c0d04030780b822640ea000f54250900c3d60710b420303202a01b40080e105024010801e03008404c100c00c10408150031940740b2084110080c00110384079024940c2c1d803041416490303031040e2800410000744540940041d0400d101c0c50203000034035200ca020f4803050740b040c0c60864400b0b04801041040341030290002c840c050881c0303090752841c00c10340c81b0503030f0b108400a00740c01165590501c0300000c240401c403810305a0780c090400e1100c0b5a84490607402d030a41140d0b15074100300034000042048d80071804540036103101c4c8402c1828030048820403102074a004203510300740406028166a03c000b0802c400c252140d40c40c00d2014500240014050080701540c010841b60000030f0041c0700440d000e680c542e01100814809500030750301c038102100c020f803010304060741010100c035002c14014a4840c0d034510600d0141c54511140001120544040c103800724060601d07071784180898080c0c4a105d100d50341042c019401c482000c40c0b26a1a0021501c5c1d680c007000200300728100d100c1c00c00505000c1843e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 488268246 1250 488266996 488267029
    0xb120108150402030c12010e0703051b0a1503020a030605060304060b041d0a020f06071a1f03030e0409060902040c03020417010204080c01050304082a150601020d05130302120c 77
    0x110382483d50119070b840ca2400440c91040b0a0703900452802a8258844e0400d070381841c00701c4e03d4032607482c144030703456600018003d15482c0c00d4014003c500d0924180030011500c5080442e0321344884044118025081207081e0400c0540301c010000b4155907040c042c5000d0b9002d030000055840b0310201304003c490004c584240e0300103805040d00300071140412804e840707680503160b0905215400000408900c036000c40202164802c010346400c40ea40c404e8a10f215068a00a20002d540805400c002c0003d8038840280050790503100401581042d030031000c800c52007900f01140b00502b0740e0001c0c0640305101d0b1624006903002c102005110744440e0520b41c98079512008529090070b21145544038201058920305004000001c04c080209130700c1102e6000c00240a050720200701c4032452100000c10078100c002d244500b00b11903400e0418440f400d409914140c0041a00703d081d0705003a2170070340240000e1848000c20303910010158444112020401980c07030060003980c00001c0030070441459032a80c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 488269496 1250 488268246 488268283
    0x506030c01090b0d0b0603040303050f091f020d020c01062309091902011403040506010315051509070207030503030f100f030f083009061501020c04150b120108 70
    0x50390590308000000e050720848038540390b0720044c40a03482c019000c0b8004d1950861800010001499450787c4000c0c040c5840d0054000c0755150580d680b42d88400045515401c1c0032030030340d4041c005549500801001402c000d0150401c049401000d003101c07072030f03841000b00b05110160308601060032400b40004000441c6c51130410300301390380c605640b400015082082541c000315160156170055030385032484070340d1070002552480d0901e0003540f240c0081c8030840340c6100c071078036808944009001d100e200d00220324540001034000d50401c0801c18002d0000c1c0b055000d41d0b00e0100c041203051006600c0345c00340740c3c2607142a00b4000441881158141d206006001010710280300242c0406540c80441b508817400c00d0300d0311807240000d4142082d0aa241c90314200404c500e60800d9040c41c115403240740e40005681c100d589034103e0540591034045d001d40180c000001d000803070310f0980e000b141401b0300c0e04c00d0300b80965142d03580c0340f9072607209140c032000415050004000d504000c00c0038811036140c031880c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 488270746 1250 488269496 488269513
    0xb0307030606120c050d020304021819050703020906031f09020d02130911040e0402010512010608060102010c08151309050105101e030b04021c05010606050909060d0f0320070b0d050603 81
    0x45c414060018a0b1401c00d40000106003595181d04080005440080c6a00c3c0c0a00b0300d142460400d012105c1c1e1010300504090000742040d01074130035915086806000c0601d10b541308015010103052402e810350701c142100c2ca01003200c2c01d051024022400710007800698540580c01404020400e0754000c0401d43d0514101c0c00c0b5600b9880107803811100044150700c1c25460b18070041c0e400d070180707040424407199140000181540d101404600425007a00200202c88041c5000c480c8180201c641c924029449944c400c3c640c1400c550000c0c100c42d2141000030095403a40c0c5250948000355110070b65104100020300c00e100d4100b22401030300c0000e0a4035005517255941c0c1d0f81058000800181c46401040c150451030651500c1c0160755581c4400200007040d25050054007a0700121180b80c0101810000104030b404c06d4440c00141c15000aa41400c0103019503080340e80c440051455044811018039010b10300a041000b10b02410007019450b480310000c00c6a44101c2c1d1004100700d200740d011500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 488271996 1250 488270746 488270771
    0x12180603013f0b040201030f0b0918120304030e030607321c0f0f0e0c0d02030304031208011703031611030403170912070305190c0b030703060612 64
    0x3505500480e2084981100c2828400b05840c60300c2d080e0003211071000d0361500351003080107034018240b00e02e100f600e040240c80c1101d00c9810403154404042030300700c40541c002c1043c20042c5004000c070390003e0702c1207440040c40c0c42e24504035900706540031000b260707502d01d64101d54030342440700581c0050245000306c099441c8250009284468081c01c60692592420000098080c001252541d280c07092104000031030318a01c804c02040081207008416103403c03458184d9954900403c1020010003000300480d001d804200120802c945008a03030502c4100000030014440784503046035000709449189981d803400d03030700b00302c00d0540e5003004000c0c0e0001c08c10028202008641c0344224943c0c0d00c0d142d00d2030307074212034010310f03610458001405608000f00084401200c0b50020162041c056820803540c001c10344425641d007a1901000f02160048558520040b40c030f450346440c42400341c001030b402956640f401d50010780c0f06407070440029490710401d101240e00b00510440c824031961040000c4c800540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 488273246 1250 488271996 488272019
    0x90209091606140c010e0c010305060409170d0b0d0507060806041b0f11030d0203060a0e04020a060509130905300a0c061b020f1501260f1218060301 65
    0x5610500c1003a0501e00f0781000b050040d0303070042c41414002c20041c181030311a296911900d22010b4002070400300000c6960502d405000015940310021003442c16400000d408590000200489103a03620f99500345a6a1480505c0942c035000b00058041c441c241100103085a4000340114007650a040c5ca8244090410031040040c02144c07512072004007000c1c50072281e83d01e80300c4401c1440d02c40880c0c001d914414590003503010b80d10485080300c07000d81d01e41c611403038200d0455019601c039196400402c034950080008004100c0c2c01031a482d038884c90713840024110b840e149820b44140c0d001c121882208803004c800c1c48a49108140b5050104003168038901076841200b025208001e40450b20070100126600b00c40d005903c428041284801036201c020b55505420f40400d4441c442e0403d0546018083c0e03298a0513034040b07da4010f0300c843c900d600030b1005104a0500405072281e44d1801d00b0190050080c000c2050011801300c1d07640f07041c440c811170070b04040c0e48203520a400810041140c1c0c40b400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 488274496 1250 488273246 488273249
    0x50105060306010809011e0b030609120316020f0d0c11090402100522030b060a060302040612020705030c1e162301141908360c12010902090916 63
    0xd2a10700b1842c0d0710000c0703a9024214524851f40c8420005080341c000b40103507048180b035420240d0446000356100c00500d541d80e001c540071890007010400104400340342c6040e131085104040e00440b180e040c2c08400003481e080303143d060301d400122825203840c10020f05021074040d480c0100c401800c00d0400e03030000754540034031940303410a21a001035208007810601c0c40526900014000c01880c0030f543c2d00b002a1241400c0360f0340c91268841c042e01007141402442a01c1c26600555920f1010b880d41c04441c50081d8801c02041c1d850784000d101e180161042001140c403020f080000c00102e000c080c9200720701e03000600d4403032076289540714000d00080c0380c0d80075130146010307079810980c5560307004a006952201c0300059218011000080f28252200480b41850000080b9500c50b50f132033392a0b058030040514014000c0000c540d440868441034001403049841c0c18440c00103a602000d6205c1c0007400c680020004031079a65101c4180e03801394a01303d0306040d40824540c000d0301055800146c50800c28001e03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 488275746 1250 488274496 488274499
    0xc060c03070c0507030803150a03030207051507080a090510020309130510030804030f03020c01110d0f211a040209090408300405010e030c030409050a0b19030b0109050105060306 78
    0x8000180d01d28815411100d071190490b040d5074000b81c0300d045c8010154011600e114a900c004072080f2203504044420000301ca81581c050304806080ca030802040d689414003645030720b601444090080340928000708003210941e118003064134905424402d007130f03046044800070364005004080d1681c0350a50010080c1d0605280018070703030384201c5c60140801c0f9a410103480c6c1840460044100200361076018029030180d000c8a044814030001140c0402c20000604220b400202c100c86c2d0715800384e150446006451b00b002031038800d41c020810818140000c0c0c1034680b98982c0040080001c0c0f420464088200c29a000d510f000c1030f14010130b60415001c2c0c8024031010740020070090320042181d0460890503204107000207030503481c05500030000c0c25101035801e946060b251600700304c800000c507560000080040e6081c14540000c0600030701d001800e004a01d6101c0200004550780c18000140c5400c1c8280400c00303035811401c3c1840d020344140c00007440b19252500600c101e03640c12041eaa40b1080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 488276996 1250 488275746 488275771
    0x10020316080f07142802030d15140105210903040e1f03020616080d05010521062a0c03070c06020a03051b010b1e310504030c0f050304090f020c06 64
    0x1170079a51250000101c1d04101405448205042010760100c01000049190071007846030019925092002c0c40007449540c0110050381c52042507075010b4806000421038420389450180c090540d405031510b01202c0070011604001000e00c0700a0081c0c409541094a000807001401c0c01c0e03003000c0c40e50300401c2c00041c1c070901000c24680c0d00d04554128500010354132540d259140e40c02c04031300c1c0d4040d0000b8000c0d140b2841e40c0703c141e43d01641035140104000c00e80350008000c5c680340c100f051901c803c5d0f04014554400c60b40d440146c2a402a0401090041e007000001c554880041c00d0075103601c0001d03040398045402100d44a40800d41c00001d9540403180c42802d400d06000c0b40141c54010000c40144640104101a078104051041c0380030381006e0304140c81e08030185510900c0c8a0700360981e461f000c68104000414101d000200e5445160b01a02c07034140480b914001e40c1b1110742100200d80c1c21501ca52001400340007031409030207104449040b0b48001d500f03250402000d607855250051107000e400e203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 488278246 1250 488276996 488277007
    0xa080f010c0201062d08010c020102030403110a1101110304051203130503070602060a0f0b09070f0f0e09010e0705090306040803010504180201051e1608031b041d04020310020316080f0714 82
    0x703645c8400c1d0f402414024002c1200c242c4152000c5d002c0c2d0011035040c1c010900d940d0003071400f00350200786400d01b268004030b4841031903c2a0b005407a410100000d82000340f00a02000c43d00303072241444106000215030046849220440e9080c0001d0713110340000b8040d4120f91010041c40b500018800d4202414050104841c116201d0700c9008150342600317594000d440300103111500f1340141c02034000d003400c1d50340c442580d840164252107100b40030b0411034000211400401c103242034109555041000d90ad00f131844c00c80303080d00103460903409680030384060314004010082440d1601c00c0d00150741d0a076002000710f1200d07400182c840e00910142080c1d5844141242e003c0d00c2841e02100c0e075030785000d42c44400b51000d074203024441d03400c100c940b0508103c40f025130840c01032403402503c040325100d0807580d060080340c56074050400c00103030081380c145c880c40601d60014100b50020318407604038900c5031103a010030b8280040022002804202c0000c1d4940d06201525601082e01e628844a4010342543c5c0c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 488279496 1250 488278246 488278319
    0x20030a0b041112071133012607180203040c030c06050a0314040c0506070c050429090403270308190807020c0901120305090a080f010c020106 62
    0xd00d00c003424180e001d46041e501400b000210006444240078400e41500c0d00e940d040342c01c0d603541001580244071540300468483c124091601c2405200b8000701104009800e001000260001c0030b800040000700107581c00c00d41c9030060345d801d02440ca0724800410307059113010300440c804d40d50030001030f8495400100060500907903046620085520140040d0410396841c002821604508481c10000c0e00301103e41d0509078400083c580619009411590f0b0f462070b200810807294094074044440c07000c169000501c03580c540c40703800441130060f40c42e4203107104100c4d172142c440c00c407600503144218590014040401e501c004031320181c0c040d0030b104600c00ca8080f0410301006405600040490000085903000c90011352044034070501c46441d00d1055803202101a40c95285000107582c00440c42c00c01000451203840080000c14000d0512030b141c0303070b0840c0201e030030080a50092802c0e82e11112000300c0d407032801d100c0d1504268251000300b01079424550540d4410500511840c0171444e09148002071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 488280746 1250 488279496 488279501
    0x61409040216150f05010b09010f14070326040b0a0c021f0c030b030a2609120106140103060e0103122c03071a0d050c0c01020a021f20030a 61
    0xb0340200040020100d03465150a910002845094408060826000c18281045801043d0507105480080e070700780b0659000440b24020800340b800c081149104034a180e00a10030020a41d150281e81d407102c100c40d0700000d0000c400c840c03400c0c0a151441003001c11010079100c3c03119541256681d44041800c010501e0100e1900c4034902e568059030f002c1e0740e07100402800715807069440e40f10b99101403000e910307124101621001c2840c1d0107444220889001c10020200022038810107074668851801d0a0494010400400b880143c0c040d50340e5440c1e8042c40081c54807000603c6900d0309180034040c607414160400d00d50308042c400140310642c0d851010001c50300605c8000c080d036160040394680854006000941c48101400c0d00f8003e01031000041091211a44a1410b29a00b6684d0618120484400302c00510008007260070030320083c40f602058240c00c0c00140895280c035801801400b5000011b4602007040d4070701c80e0300319460300c0d42c0342d0034a40c1c0b4819010752000c128000c440d00c1e55903000c00c5102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 488281996 1250 488280746 488280757
    0x81908191505060a09140105030412080a14040f1406100320091611030909041b030c090b01081807030b100e010902030708060a061b030207091802030d020303010614090402 75
    0x61281020421a00d040d074090091412241b01c0c015400d403111408005544030303c410b890203094409201094410140269142a0885120302d80015041010346044029010680f0100c40c09614a00000c0510402c03c007a0814030070b81c003000c2c1c5142c0c209016400902c158511004044d0f1502c44524002c0c81d82e88241500010009404102d0a241410600700024803580308180421140e0341c4084480e500001510200316024290311800c3d2255122004200000c1403694004140041c0102c0090042c0103400e005026a0001080440501c03002501d15400101082040a02c01c0c1c80101c0460b0300103921011641c0020300c0b0743d510b40b0769010890000400307410006215812400000d15046c2c26401544120000c1d52005000e48480e020030503421400e02c642c1c8000b84070048210008079060100c00e5100b4480e004a81e04281e0320440c520944154030a00800c0030142580ea00550509201a01411101f44050343c80c56041900c098401c0c0301c040255003048201151030440ca40701c81d8115103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 488283246 1250 488281996 488281999
    0xc020c01140d020301141003060b040b0702030a140d200703030f09120b06010e1801210b04140d05070302150705040e040b06040e01020a05030a0b01030216081908191505 74
    0x1950ba6071207440242c2e05c2421b000015010b88108003641c800c61b0310900c64030381507505600d0b03441d14081c50b014022419810411042e0f905006100c10000001c00450040c098014200c0103840b5002c0c0403800585a40d1030003482880e41548081d0900041c0c4012410310280c0e0707410704150b549000c80300001c5620400729000380c0500c070350420f0f501050012070300038a8031800c030903a50904522014400c3c000c1603500c2d521510341d507204100c0180a008112041046007854a0080318000180d03a1030352602c590742078a00b81c942000350140480401410300402c0c1e200d421f03604005240c100e0b030366802959103d094441007090340814000ca07003418031800441d0000c0c80c494040200504040c14800c1001d5016104c042c815403070000301031030000060003610203085007901c0391b0f81903540b00c5d45101c019040b1982e5a904150f0b00b0000240c42480f0000c403041c610780142105030302c545203041d400003a5000001103000b88404881045030610b4050140e0444e26034403000466500f089041000d0407040303981006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 488284496 1250 488283246 488283251
    0x907140301060207031716030f14041d0f190903050904020a020309040f0c0c0219050d08040e070c171c0222120201020c12210901120c020c01140d 64
    0x34901e41d000440740c1c2941c0c05030341380c020580103c00c22002288204001d5995000481c3c03101f4002c41c2c0141501c04030265a4101105822000a0180c006a106421905400b1246214841807003103c1114a6002c00050300c0060181051400d201901251440100380710b501d804600701010b00c1034054961620b4041e106540311858000c01a4a940046000b6401a454464a40382081c0c041c0100f01e00000e0075107030740b040380c1c90340c0c2c01303020a0040403c00182d6822000e04001aa5220b4561016155009450f099241c41c141000c490984030090411001c0280384080b010100d400000740d01c0c1500f441c404455a5038540f595800c2003c0c03189542601504e10200f08402540c0c0c80d4451101824900360407414995124060008140c04a00300640103900200d0901c5450410006040104840c20208e480200d03090ba40c0010102000307049850840004c555640b0301d5800ca810302c0810360003110180100c20801070000d42c1c1d1400e852201381000704046110300684c1d50001100d01c2d201d07907440207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 488285746 1250 488284496 488284499
    0x3090120040509060a0501050301091a03070807030c06080408040e1305060f060a0e01030c0909020307030507060e130e0d030506040209090405060105120607090b090f130f0c09080c0907140301 84
    0xc03100160464400c03107004600840c0082d6581c68607000507000d60704143c6030142140d0070300300c20400501d10602c00d81c601004c403110302c15055404020600c010802c8000a21809042d45041e4910304016449201400954024030002a0070a0160b0b0240c8800c65914401682ca82d8249400b1803901c00b400b510301d000e4982400700f4070b10a2660319100c2c0109903a90341c0c20390340d00d450700b580490003444003604900e4007000074003035011a904461060350008084a034480c0d04c07030b100c0d941032075041e030b2050700442e040d101d2288503810700c1d80d400c45030010034850030400c00695006590301c900000d0200303c20035540701b0015409980e20b60603641080703005010b44203a840c0c81d1030b03c26070341c0b0b4003801082d200d5001e152140d4a0901e0000740d280c418a00b983c2c6101e00980740c070301288002d401282e2015807200160f102003445403640d94a01042007150a030116541c00d0020140d000c6894001c0c101041180b0001c00b4818900300040d40342080c00151407e100513030b10a03800303c58004001940e0445107a00100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 488286996 1250 488285746 488285801
    0x80f040b030a1512020f04150e0903040f09020c030316050c070905180a0507031412030f0402010306080d140723030706060501180509090c04060f080c0402031506030901 74
    0x800341c03400100080700f00d000c1e00c4c2d540c40c9640d00c0283c08002e40c0318000d82910b43c03403804c0503085159507550034104052000d4982d4010300030316404031180700040d03002150811030088400040d10081880301021803900d6408000c081c0c807844010440c041500451807000940c92091003260300014500042d01c42040d10b40c800000031b8141a20000000340450b031f90a507240c240481c145004550110003001450b1856440440e04d0507440c1c00c610707140c047c000030380c0c01540f4844000c41c03040301e00c0c80c528209450503200240498800c1d400100e0070740d1044801804041c1c0166030355001640b0b10700d1842d25142c10703203010144201001c41c101c4c401324000b16001201c0c2c000101030811a0710500702405042d40724070044824246868494101190a2208002502300400b089800654610030354070300f5a518408a01500c205c3d80c0019610000648200b0007000184a10301507008101d80551940c2440710001e0303549600c8d080d116115030b2000001c15500c12095100680001e4004440a000c0000c41c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 488288246 1250 488286996 488287001
    0x501020a05040306060b280311040f15091401110a0212060403140307120b06070507060e040f0e0303161809050604180201020a03301a010203070c03080f040b030a 71
    0x103c110780c420f007007810100e41007001000b55070050a641d0080c000401d110300d804410b1202600203402419501c501d020b265201a4000308003074120103c02501080c5080f1044419884900c00320341084500b910511102c2d800c00b280c018841d00929010055aa203441d0003400c15401100c0254801e05800b4003828410010450034071440c003940341c0d940c02a444c0020141507101c11100c1070005080c1143c81d0b188003800d40d2002191880185c2030500b003002c6581d44601d020036030380040c008562070b20200b04071482c2601802c85100d80202040c415900071001880d5680009891040030980e240e1a2800b4039208000c0190301401903d500c114240c1d0f0341c0080b4004080c1940c0c491f000c1c80c20100030404000d400000a018158180d00a120211041d1070441c0d450400c0e440441d1404aa4041048402800c2c82001e1b1a151900c1000a4030305516131141c0d0404503041150307040d5002449040045244800d00e80d0446c0d401905290755030242c211003544e10f1046402c01e012070380010080c0600e500349903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 488289496 1250 488288246 488288249
    0x61209030806400b1e190302031b0429060a0201140c190c02090403111e01050a0b01020610030305071b0909021503060a09110906030910050c090607060b030a0501020a0504 75
    0x8281009404021410312034a00200301d8070242040310b12041c5c20301d600b00f080081d00c3e00c1d481c0d01140381c8a01e40380c0c0c0c0041d00303203a40c54414071000308640c288d010841c9000c1c800e4030285494269080c00e001114404d00004010b45080c440c402d040101300d50790014000e41250b0703040401180c0380c90300d41c40c4c01c0c01c6010441d004409075030384c201e00c1c807840b40c52000d0040b03680030704441c0c00500100d034030355569508444900c00103030101807a0140b0718082c26101d655912035640b001703a01c00045014031b41b10302c01800700c44070079020b079046521440503c0862178048100038252509840c280d580d0301842c0c10030000811210800d1100d01d400c604000071700f91030300d6001e104020705c00c5078500f8240d049020f207a90180000d83d412580010070724001c0140074100e621031916003140c3c04d00c890810042e4000101316800890307800784142c1149824043e000514030501c2c2c1d01800d20f0441608280c500c002107171140c002e07510014000f030340c1c1e4200b00460f65010850244050740c004000d665429450800400d035800c075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 488290746 1250 488289496 488289619
    0x40c0305100c05030c09010c0c0f18090c0e10050d0b190e03041e050a0e100b120c09040b0904120e03030304080d150e01030c061209030806 61
    0x4011810800034010b01407401c1d201070b2a83c40390b041d40c5468030120302030340c00040a94117000b03a28440400007081e4195110040c002c00d031004000303074600281c07c1e50240480660854440c50300900c040043e109040140507181e007036806114aa0710354002e010181410f41019174046003000001040200c00c940311441003200c4145041e01c413824003610b0382655961401d45d640b0750014441400781541000705600401043e00441c2c1c1c50507640c6001c214889210f81040d00c14040030002c00602c847c41c420400c000349056030b03202e85802840092190050400b904218000d4000903101565070b403140c010220f08000180080468206458074511034800b030701800700410303041d178526040307441e02000b507a104940100040c2c1c50144000e110b08004e0452644122a0012011021444108050b812070203584255448a1490b0500a01a04130061182000a45820141c000c00000d622038000d6800c21001d460b00d0120900001c0c0180a03640404074a00e0b4218041010320745403082c7c10350b2000070524 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 488291996 1250 488290746 488290753
    0x60103030e030d020604020105031b0d020c1504030e04020d0204090e0f0d090e04080a031104060f03060f2d0909030302030114030703031403060604170307050c221e05040c0305 77
    0x10400c0078142c5801c18030000f8005604070304001005540035400031a4003c0d41d400c608890341142248540d0140c002c0c0c00207826240c3c0c0404d030170445a0302042189036403280611613244919040e1b81c02000383c003c0d00c4c0d03914002c540116040380e9654254043d1806400c10300d1051050b80c0c2c0704a01c0c241e0741c00d040d500d280650f00c901804001003030300503216002902c80441c41d940c1d0650340c40d00c3d14a80c1c0d03401001044105030761080e54102d0000c1c440f01400140c1000e55035113034034011012006091783c0064003d4100c0c1d844075803040002d61150007201900c4440519050111503071401011500e08403035201080d01c0c0d050840480c201640341c1d0095040c1c49441c418070b11440140342c00e1594546041c000140400d40400d40c0d640941c0c955805540d001500038801403425440c3c10703000e00300419000c955100c5a001281c40b204000c028000d4846241d41911019240440c80341e100c0903900c02d85140302007250740e030400c000c0405080d104078a0320310b114150a1085080501e00f1822410083c841a1090301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 488293246 1250 488291996 488292017
    0x6040905061323040503040509090a0506010608070e100e3f030307050c01091209180908190c02040905281a0705090301090311160803041203090e010806010303 70
    0x110034803a480099021120a00d20f903961030140c0509440050300c01d850340c1c40103010009040c1d88030707041d661150301907a02805103501c0d246803203071502006030040028052008104070080e43e00040300015080c0845000000000c3c0002c155064805010907070b03044100d50194480d0fa200030034a00c042c40b07440c80c2140d4540313400f122a8180d030f201c0310403844c5410b400400100d084984502c018240945120000084c41485030b80c07034907c3e1940c000700c84004204007007001c21410b03240c0110300f4400503000310306004425803030340c402c00c01d8860540c1400440e200039800c0108507115688031003440707a0281042140030701c1c604041c0c1d50b4500010340520b9207486801d040c0da07113400d4a10900e04490f0b11026144002c4200c995030710400340010001c2d41006414081540550b40900404090600a4654000c9261022032785800c00c00280602490000c02c12000c0041c04030000443d03003243c4030801c1c6181c00810519003111000820790103c01c40d03000350300c004100044041003443c100c2c2c0c0b0a840d01c96118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 488294496 1250 488293246 488293279
    0x10c1b0b0301150311071103030d0212040b01080a0c050402031905010b121e010509060103180c0e07090503060a020f040503070f08150903180310061e0b070b011802090604090506 78
    0x41d4440083c1e45c03d00300040c0041d4000a9202c03c4c029440880201901d04101017903501c40704070b82001001801e0505488244020720202c0d0012501612110b00a407a4480403602c45001d609024032445000b103500000089080345241e5401000803241c490601540d6503a5450b901e55400c40c000841c0b0200140b40491030950460b014040050484e18215089070f00e080300300000c10038010101307030516840300e6445216060304194584205d100d145110000c50400c404e103034030403800400c01030501581150034000eaa60004002d40d000004a00c0540e179800c00071010021401160b110036014401d0070008681b100109007440c0036251303001c0850704c2d403881222540c9400c039410340e6a408550030401240590314100300c00d1b5084001c01804880c410ba400c2440b040071101c3c2d50780070308410011012502241003d030102c0a0050855400f000c2c2851015221003180302410312488240785480c031300c0034130168100d4060303c1010400a14554035070341da42e68000003400084503d42d126240b5058500001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 488295746 1250 488294496 488294501
    0xf0501050705090a090b0301110a0c1103030309100b0a030219080d0e01090e06450609070c030c0203030f0904050603070609061202040909050312070c050c010c1b0b03011503 76
    0x14500014a10403644d4a442c807841c3c01802d0401c9025015500c8500420515840da00200003160300c039074071462011094144498144c031030100941c030030340080090009041e4009040c0b901c80800e00800255460400b0020b094030825500c025005204403201074043e910a4000e0f0341240c040000780e940f100070641d03007101d10031980865240403d101100c18030185901c000c81a622500180180c400c031b100314002000015581d40080303450a19078030b240b440c00064829424840c001c0c0c503d40214a0920b00c2c0021040000140a0310800c4818041c842c20b052207810280780c1540c014050b21798805050030b8410740c56005c00b1045005504010100b40113080000c2c035502200c00c01c1c0c3d28404140d06010f0b080307503200b51100821420980902000c40c69000e0f51142c00c2d1401e00c22001540d48840c5040902c80c0c40e0300080500303051100c0347c00c40d207021490209014000d080d003441c041407440c0280c40c18095185e11040b45000c01c0801003402315401107800d00440c142c5038008002000c1c0320412904506 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 488296996 1250 488295746 488295757
    0x20c130b031203150a030507050a050102071d0714030405060f060619030c1115011d0c0406051e0d05040c0f0b12040609210e0603011d1801090f0501050705 68
    0x4050b401403802c05070300c11024000c0c1d500200e40c104400030009001e40021981c8210360010340e80783e003089104009034589214054010042030018244861a00c03040890002a01c2c16200782200188002880180b240420500b1810b1354071141c1d40340d0500d400d01c03d41da4202101c50928500441c00410041d02e004026941c14180204011001061051302100503103424007622050040c0c0c02a02502d001080c0203102c1c0925020b11a80181e40c5007600d80c0002520304221410008441420710100d00307102c0080b60f050340c145041c642d60703c089410491050400381014030300c8000b001304940da60411240c110074002c2e80500c0c180440f40e1345400c0705540400760b611480d20b4900080144c0c1881c1420300401d20340c001c0c0a0440010121415140d9110032410302c50021071b0040607100150410b030300560122550842a92580c1c1558144280034034404e0304002d54100b68445000000c0d07603070380080031a140100300712000b40040c010074503103075003500008032003101c030340d400c2c070300040d1480f4840d009684 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 488298246 1250 488296996 488296999
    0x80a06051f031509031e081e010b040b030606070c08010c02071509090e031b03120a0c08060d0f0c0602100b092203110d120c03050f150f0907020c130b 66
    0x600c860301003e071102c018003882c98120240710072009525040c071801556800c6039500741d104c8044034581040140c0e8061240d018000c02ca944040052001d03030344403000d44d020341310007a14065403a11098005040c034010400300500c0001100360116007940c0c1900070080c2c1d640203808840f080c50f240d0024200d40c001d48011000021002102002a5080d03504078541450811003601d103010703410180007041c1241000d00d40390729800066178503404000410055070000c03940400700800a0f05420007800710401a00d554401c649a8010209001c08035804840c1c543d03000f400d5049a5560b9407010751269080340b0240405481c00302420003d05000f03400c9449040c507980c03c10300000002040d581204000d40c010780812900c3c0d400103011160400c19180c00350301d10340b80d00032840c8000c6124015070302c43e140a03600301401c00b002d0000c88007290203039641141001c3d88003d40c800c402004945604804030059038848001418024295001b041c14066140c1c2a1511012030b03044824400603190803040d800d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 488299496 1250 488298246 488298263
    0xa020906040b040603150c020d09151101240906350f06041b080307050c060c010e01090807020f06070c0e04021c0b0609220f030306080a06051f03 64
    0x180355203041d901c85064010020800581307280c59490b014090b6460815003041c16030b03540f041020b00e60301004611030946041c0743c010102410511802c12003110402500c040c40100030b41c020302c0c06420341110700412a00e82d90413540c0c40d0640c05540c0d950002d442405519442c01102203484034890070304451024403d5005441440650f500c4a0000d4250001d61a40c2c006e0220203620a041800f003240a6801149045103804a83c1c004045104c0740d40d00c602c2c81c1e540708001400000d240810382c916452400c45403140c0b640c141c0b03c442400742c880000810000d5181100040c100041d840103401d03254000e540d103581c40c040b0710041c0100c40c4500c54001e490000703401d80405c10800080d070025805440500729010107895a1150100c41c804484101d482492881c100003003030034040e040542c0b2180307240080000103014174401910344000e01000c0d01c0700000a4046090500982144c2c0060038158115886180d042c10520001c0009079413150701c0c0340c0260b0700c030071160326540c1c98042900e40000c501d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 488300746 1250 488299496 488299501
    0x80a150e070e130f18020f2209140f152809080703021506010f0804170f04061106100605180603090102070c0e1608090118030c03110a0209 61
    0x15142428014405000c110381400310310802d48034120110f840c0801c0140102c0e22101440d00f550a44255144240c1e0300500b1409400151b6200759442d09030700380988007602c400c00401d661812032206039410303003517040c1045030b81c00420183c4001d603111048841c064419400009800944407007000c050403925803580004199001000815107681150070308404900d9040e0800520a41e280d01c2d07010380c4c20700d00101c2c42e4400d240d0184616007801c4020580000c031860900d0000c9c00303001c4101021002c20010100003002c000c51030306040c40c1d81c2c0140140948079910540200001c0c0d0043c064100098500300402c0d00b07540300011050300500813018440c0c0c0d65070030503404880030741162620104c034451492100d0a00c0e200c05000b1270154420700005030344c4100604100e01e2403400c1c3ea00030780104248204001c0201401980c000150015251514964817880e0b02c1902402c1e588504100e01c0e08118207001c20507410146620210b48a5210040b01da400d00403456140c80040601a4000300320400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 488301996 1250 488300746 488300759
    0x3040804031b030210030207030e0d0503180328050d02070e0f0c0904050403020d2a120908070b070c06020609300301090f1b020c13110d0507080a15 65
    0x10540ca4008440c00b03103007a2966a00043e1003011144405d40100b607000400d5001d1503488594000030441c16940220b120219030780d980e5980c880d240740d250510f040c0ca09107582a903014480d11a1903101d829480300c0e03040c2110200c07180c1c0058117404031094401d2034940005580049440000c490307802c0a00201a40c0b0003031548081c40004102c107458030001c0000c5500c583d501c0c0301c0c0d0360140740654000d005001e820200640780e14105030f0340e03100d2541c007500003484640542c00002d418640c001b00d0150074114403c410b603400c008030340001b4014001e4117000b141104150014201050082c0041003441b0380d10002661102c0058440700e00c1500911100745506242241c105082200c1e030900c94188080c2400340c4030740350000c0c0c1240d1651a102c000301e07050310000e030241034012840c42070140031581e1000c1c0041d40c0e603c0f2485c2c8590051440796100341d000c960b250b00200440f110082481d5484810982042c020802142c0036400700d002c42000c1804241d60784158540c1a440c0f06609008a00345103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 488303246 1250 488301996 488302013
    0x150903030c020109030501020307080601020c030703050307080f04050907020a0b06060313260a0c02030d050f070f06060b0d0f050a050c07080c2b08060d0309050f011106130c05060304080403 83
    0x10702030303062043e040c50000015000340700640c82007480d581e8039503460a00400080c2440940c45074507100f81d000c0003090022903004000c50300d400d9402480e60f41c1d81c0ca60710062050318080c80e480b0300c1d0b0002c02d00040240341a00400c1c504d1246204400e80302d0a40c0d281d0301000800e0000303840743c088050102c40494005000140750303075402c030218824003076003406030b20035a0f2041c1d00c070b4082c50000840985044045090401a045040340b132414950304011202c000510607018415000d05a6034254076018180401c641c880c070054201c550609035288800445c1001601c580c81032500202e03e4a0b0001c3d0050007a0310409026500360021185049450b481f402d0031504045040040c90094040401140960841a010b900003140d8a81c04048094070b0180180d540201858054161490b020b4006a480b14030182903c80c22135210346200d1140c0012290344c010028160103a120300d500344090364500d01840841030388030341c464001003510f440074014a800182c80040117003009100501c006042039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 488304496 1250 488303246 488303267
    0x12180e3105060609132004021308120703140a090b0d1406030c0913020f0406060e01090f06140a02190311010f0204081506191517040201120b0f060f03070915090303 72
    0x54641403448000701d000a8103d03400b00c503010402d5480143d08100250090bc0603066400082801d00e0410a50380c602401060040480304880080043c28100c180c0c001c012540141c40c0e0009115111400380030306400800c40f030b00ca00500c41d0041d2002407450301d00003c8000d01d50708054100200c43e11a00302e0454200e409000490384070040340641103807502e81d445847c00400282c0c0d2000e260004800014040d010940c0004072618207003542400300c240c02400c0d400e9403502001b4100e540d01c1d0b10250072030401d840031407801500649041d100003450b80c0000562107080041008000700402003280b98100e229511590406821501e012a481c1502500d015800900500120380100b82c0803548010850150008242c0d101181801402da981c0828861240b81640b01e03d44d01c00e0070282c002030101d4102c5c5610309881d9485800e041c000d80c943c070014116102c005001c02e51070303044c1c00021040c0c030b4008498032000104200d4000417008600e0322000b210181580b6100c40042c21a20101e410300c040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 488305746 1250 488304496 488304533
    0x1f020d0e04090506090c010311041410050d0f1d0106030b04080708090a0e1608010e0f04050705150418090b0a02030903070f0f12180e310506060913 65
    0x44407070b4940841c1d020b00c40144620044009490710340542000503086504c0c5c1207810311002c074244400d00010700394070304490030304e001101c5402c5881c00381d0030b044071036210301308400f0341c568102488403020080941000703010001c400b41c03c100f91034003000114200d501c684009440c8011407004a4082001e510040c0b400e140107009091601500c0c001140c0c01c851230b60f001a84a001e86000c1114440400c5100100e0308000e14041c0641e5152140200703491401078a5015012480ca021030104202084081c0c001d000103800295031054a070b85c600015006881034461ba5090306011008900c424851111565807060340e455080d1180ca42c040000c3d000240348441d280300801000c03000c075415003200d07107d040c4180c8481b0178600903858000c546240b00702d4042c09000b000a03044130303003124040c840e0042d12103501482415980c0d24506011400c118103010010041c446500c1280468500254256034080c008980b242d481e144140107100404480040c4181600303886000042c201d8180c0008201c038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 488306996 1250 488305746 488305751
    0x311040605160206040806040c05030303010b1c06051012050906102102090a020c0f010b01080c071e0b0403022a040b030a020a09020307020114100303030b011106090105061f020d0e04 80
    0x3d60214101c1c1c0d100da00102040c0c1d0061b010402002024082d0754013030704c4180c000e142103514020020120f8017400d4503031030881c0803c00c00d00d0352006082e4494001460700600844000e6480d46001c0d150080411107442e400d4100f10024061003800141c150003a044550500c89181c6803500e1208400c01c0d80702d846040da8407c0381c110000d0f0b61400c1500340158a41000180d451201101040c54801032201c14407140c1d05003c00c1f000076a810090040c0e0100340319032150ba95203003515215924a1900048400385100c180c000300510808202c0944035030303c2a021503803280f1113651580c1c540320030b0b81e410482c1e40807041c407085021304003908450418440581298000d200c80d900240c500e1003207400c0f41034200e07404010000400c2e0709028082030401d03070210303030740690030042c00c80f80304440d00e804017505260b00d99640e840c10b40d10800086082c2c0b09000140c40d400e05003000c015029140658049104213030801646900320343c0c031100c0740540360064000700343e486500441504d00105001c0015800366 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 488308246 1250 488306996 488307037
    0x15130507181a12100b06040e0c0901030c08151908010207050f0d090f09110f030c030106140c1509010f0c020c090f06030a060e03070f0b040c05010311040605 69
    0x7207038454030300c5414103500340c04140a1407480d86498207611800403680b083c45001ea411400c001c000c00d1080d08025440404030344009441d020900600c510391004031640c09100801c6010700c03400001e00542c030400d903000c3c0b044001d020012640070400b40d9803100882c0d580301400044c2c1c034003004903640c82c04441d140c404056540300c0040342244c0242c5405e5445412501c0648800d04061288800c0c0c901c250400303044c2c160a01a00c460003100340c4c0a2811111303912204905041c002030103440c4040c04062400b55a441e10f0200d070800d54100f072003000041241004003801000c223503000c1e160f0b049082001040e010741c0500c000c00304000d0140110304195640c081100c11100c0601075014919010b070005d0081d40040b40500200c0f00e0300500d403880f440328580a0040c196408690a41400c0d000780c00070442c1c010b407076403150462107000700c0104200442d01240c0d040100608000e842703940a200d120510aa65a0064054940202c40328004840410090041c6400785002c7d040e5035120458442100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 488309352 1106 488308246 488308259
    0x1140103020c0102190c060e0102070f020402090a0b0c070602061003030e010819090b1509100618120303021e0903030d02091206010e061215130507 65
    0x68000519500002c0250160340400058000300c550414482c0005011809002c1048a41d2401d104105203071b00010f1080e036a10355040401030305007000315402c0200940c400104260311844900010504282400c090986046200010810f141c20040083e10b000342c014039a4180b111511001e04c0040d030f02c0140e00350300350b0081c205440c0c952250300407102d04005003c48090000c0c6040303601d4043c0481d010300c3c40c0c0104000500044d07118042c00a004107803c040302d104028030005007041122500c6101110000a85540e08072441d9840b21003464400c0f41404090340001d40210701c4a16500c0d0b420004c841844015402c10314190100300840d031640250214003041580c04101c000d001d44030034080c0c0b00e11606d044e0546c0c0c81036840d4044817100b0070094402e0380c0070f202c0e12240306690b03800014034600080030a09800e2000d40d2040c804010050080f801200c940c0911080020b14 = true := by decide +kernel

theorem cover : BRFrame.Cov 488129496 488309352 := by
  have h0 := BRFrame.cov_init 488129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 488129496 ≤ n) (h2 : n < 488309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
