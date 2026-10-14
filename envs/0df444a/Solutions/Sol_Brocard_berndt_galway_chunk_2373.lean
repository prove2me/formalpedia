-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2373
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:51.355927+00:00
-- url     : https://prove2.me/submissions/4357bff4-d54d-4db9-a114-0677d03c5cf5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 426618705 ≤ n < 426798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 426619955 1250 426618705 426618713
    0x22a0d020706270b250c0303080414071409090105070c03180902070c14030d020c0105181008040b07090305100e0109020d0f023d050d0905070f081603 66
    0x204110308000c0c3c1c40c100e01041c8007412580035401e141d121007031444000c0340d400c2d202404000201c03040b20007030420544410300c56681d250344041500c40034041c40f0fa0700001600b0b00500500c4504111252003d480c0d9407a1241881c1074400c05140209008410510016600440502c6410300600c0143c455144034200c0383e908031400d171280500c071442c2114034280010100d4243c0090509984242c803140003840c1043c100d0720220040030784076482640042a500315068000c1002d110804003032038941d0b0740f45001c40c00021a5015080543c0e003000e4601d04854800d580444113034002da228102e642c01c0c40d101d0180403224220341d4000501a80c2010105138848003656004641d1240c0140c004107280203260001400d014801c01e003a24842ca0740c00e081021403804542c80c4a0035a0610003107000300300c01901580090010749010a5081400c0c12180b80e414020ba0546400340c2c00038809104a684a142240d110b0003a84100c68803050181e00210f40c2d0310000c50440502e038421950003120501e9038803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 426621205 1250 426619955 426619967
    0x1e0201081501050d0204090204171603321608010b1c11030f031201060c081614030c0a03020f0607050717070c061d01030e030a0f02010b0301022a0d020706 68
    0x40d0307a0501100b000704048842c1c850001d00002c0481c1840140c580c3c0c90680d0001c0c8002419116502d04c0d007101c0d0010340c038050f403030782d000045d1794101c1407001900003407080568048a0300c06809400c0710544152804600780007031682040d00411448803035a41c1e8482c291360070b070b81c4045d030455400048501070003c034003060409100041c9c010019100c2c040400404241003060100300c00b1019000000e012062800d1480e01a0050240b0300d030490030030600d529414154010148175003480c01d040d05580080c44803014a6001040d0913409603a5101842071885640c2d031003500003100075015801001d8514200030814a20030f000c15140c1901e084c9040e81c03920007001c4a495610360200d01032041e070f000300750b154400360302030a610703110304156a0f490030000c04082d0903c4219410142805130303a10000c8030100541c4d0600c00d9600340b59039403a0000609030701401c0c0075080140c043d03101003141c03241d8a4482c101028101c0c0c50814950040b050085500e84031404802d9030310242c1d022000400107144140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 426622455 1250 426621205 426621241
    0x219030b0a0e06061c1503051e120f0c060f01050406051c080304020d0c1814040c0302190e0a0c11121225030c031109010801090f1b09031e020108 64
    0xb001d02e10481e06140107204491b88280e02c804120382c501800c1c410001e0030030850000480d80c982992015801141c0f0030781c0d810b00031309229140d00c0c010620301540040c18043e96400c20860007662503501e402d130f08951550009214042c4101e0030a07d00086504061042d007801502144003007030713130180a0300c8820f150790020f0800c0381c1141441d440800480c01040124024000882440f2003120030f0b45000c0d42603501c200780103507030405040705200008030304138001011a581605c0f0082040c00724807a06581c02030b1503208000c95401d1000700004c0c0f415a6000c4490f007807494480160920052810655400089044040c000001c00401d1860080384400300e90003003600d0b000031031740d580428080b220510600807680c0802e8449090b01615038246c003c03a070305140840b030b40f142000c1100300001c00b00785040c0301c0c4101841e0b460005920005050b001000c0d9041460f036490074209443c40e000717020359860700c400d4038000528000b0100b96016241d4183d009070b0141d441c00300d1130715010301250026180c0c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 426623705 1250 426622455 426622477
    0x121503030f1b101a01030e0111070606050301062c0402042018030c06071e050a0308090111030c04060806030c03010c0c170c0303190b040219030b0a0e0606 68
    0x52018400381c1181e070703000380420000448455400104441c03802d1401e402481240d81c1da6003007042143d64440c10300000801c0000928000c150180032201e01801003018076500800719100042003018086580c0201e021940c081d002000000d6403112640b05090294012059a15081c1010b03c0c00240000f1229017290009200180c021311504038808040300300d03d20030519100c00710700755200031082e11098030b03400019409020700382c8090001580c0c0703110700400105403110030700c44120b081ca903403948003190030350142c1103a20160660038058000d08040360902410f41c00c0840003101810460141d80c00b075001419190b080905200e03003a0303020a00105600d070148940401041e09645c04d01860480701e00545442c00c4c030401e030742040456400b44000000500c58200040303003008d40c000048035072050064070b50208205030b110400002e03214140c101e40c0e01c98001315080e6528959200302e03815441058800b000008840f5050040d004050310582042c02c180900240841c2402401010750301c4038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 426624955 1250 426623705 426623707
    0x94d2716090b070b0402040b03070602030a030c090305151816050d0203030904151703090306011e03050a0303021201080a0506040201120b0a080a02151204030c030504080f0606040b010512150303 85
    0x41c2d250915a03900854026580034050030140300035410540308841c00004243c0241032100c0c00c028000c2d64920582281c80d08140e40c8560404940b0300c10841040a194000140c0f00440e61102102403442c406031100d00052001040801c0303100d4001650f0421507014024201a4500d0722042110340720032441d041c0d070507000401c11100c89079154410b0031440054100034014082c18205400d4045498100741001c0e540100300700c4800f42e600250722411100b1510041d0f50030150440558007075103055200074a184142000c0100b0103800d90007600042111207245125682ea8805540c0e031380c09250800b50041d04280c0101d005540f2405c802c01c400c1440350400300f4001b01c80c80208004900591080100d0f40041040c801146440e01001024001000d02541441c440202e9100d642e07902800060501024200c81810140641c09442c0103000c1e0707800b03481e1418201070149440d01e1040b10080c2c0b0a51402007103508943c050420354000307815041400710390b030769010036000260326519841c5a0601c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 426626205 1250 426624955 426624959
    0x80702180915190e0f07050103060b0301031202120703030605031b010c03080601030b0a030f02180124021006080609070b0301060f0522060f03050109094d271609 71
    0x2800785101090107500101440d02502c905c15082098036040541014240942008601000819079040d2600030300d2007a150f82c507901040e0b103884180d0301d560807035040202d1030a0916070142d00c0941110025800e40b4142040303050401e001070780c1d206c041404140d565150304003003440b412840d603105030181000940d51105100240160210340d104030b030281d12400107d001c6082043c551100d00d4000e405103000c550400840c40c0c50f84603980e10541d03c0064038455800c045200f0807650815060381d401c1000100d464640b282c1d25200100c0e00302c12548100c2d00001000007042040b0f80c125251541c8045044100e100308442a5000c0401d0b007004060b40d80c0444802c0585a4043e0001c00c0d05403203101c41c07403900010140c00d65805a00ca8180c203807802d40d1340300200d424055104072264103a040d4440c2010a045a4040c1c00c01150104540201c081d440518004413007214a130000b008031010784c40044001e844d0030b00d003140003c03400507254514000c2900292080010b40071801d0034107190703142e59 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 426627455 1250 426626205 426626251
    0x20c070513060936030302040509040803090d080709090e030c01050108010c141c05040f0501050c0c0c091b0304020112021317010c020a021e030a080702180915 70
    0x520300e550048805650b420304115541d00c0384108486070060004845070600070b06000c4000f1460002d003080b00c65140b4121a003014440e904690180a00400d890a14105801e1a01a035041110080714034411000c021071202c3c0211001841011310b81c0d02d00c3c15090400c41c2081c041c08030580152641e2000380151003490000780500c50180840c50000104800102401845c2c001c0c4c0c860b80000201c4100540e0b4051244029400c100f481c1111010a007500c840ca4008002e54503050050102d51902050120b1000d5140081c10641c44a0301101e15030440c6400b00100b0510956604c030703600e2107075465003030b0100002001d10f50060050400f0b48510101444200c2030b03034043c05154980499040c014004412041000401600554001c2041205404003c3d68031541034002030700c544518000c0c12140301541458403500e0b1809400e03209021110300d400d4a442c1c1140710708901c65800e44030a4010b0f40021a21103100e070000c4801040c1200b80148400c41305100900540e2100c0d00101003504e0003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 426628705 1250 426627455 426627469
    0x609150d1e0509010b0109030b0f070903061406010801140306180a080304060b1305010b0901030f0b04060b07060b0306090a0f0303021e0703030f050907031401060e0705180102190303020c0705 84
    0x3156034410102d018030b04500880e0841e0840703141c980c14041c4001c81800860f00070310710a54881030650945115481300314041e191400940d000078503440c20800c040b42818813044000d40521000e80b90150307030340d89501008a10201006455400d030344001d0000c0c8a500305160001c0440349070304152088840991500e50700c0d9401110180c0b08651200e20580b814144051040341d204480751f0b007008254140042c0041c17500c02c0009240c10103850703c04a200d1200294410010200c00030f02c20407402e6943c0c0408a46038028220944100e450722142003403034180443c3c1c2521a0912070b000d404007140a50701d50240c0105113000390109035080c04102d0000481110b11500354a0142c0810740320000f914000381a81c00c010050400182401e0600041100000f5164140c80d4031443d0240c074100381020b014010003040d0310800851a020050041d5250004001c2c50003024020444072504224801a1390b07499411400c11180110441c07070b40040f0f1700c6035010303100580c501c50036034908540c1c0d0400074240e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 426629955 1250 426628705 426628751
    0x110403060e1c02060709090b130c030e0c0409050d140d06030f1112060106121407030b150903060a021605100209010f0201050405031b0f0303010b0d0b0609150d 70
    0x86500020701200ca00b11140c2e80c1d25004415840282050300d00a8001800484684100f180003a26801030030b180356a10b9a07440788560f41d181c0304012481008030014041c000700e4280d04440d001d03003122903107a41024001d003201140c001c0d0003800d207104241030481c0c100c00c0c4a148043c44450a00415440b0101401394500440c054052a40f10f813005003001c5458101c0649141d1240803c1548805400804607840f8111071081c1414240c40e200b201121000d09040c108808a1001841c10440c209806910281913040c060311648a00d01c82030312640424030030760400310342c9503000340b00003000100c060b0002c1455204144c0142040303140b035901ca6282c02042c01607c0d15040d00031801e01041c0d40e001c2c0124801c0f424510081c8136a0030300e034031159224454001d4100b40d001490910854001c0300b0011100c4034066281125170780d40c6d44110801c46c1d80c000380203c0541604204c0d43d200540703000b80a44440701001000c4e6400c0850140385500341e6801700e404c41c20320300d40300c80180c5d0801c1c1240004000f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 426631205 1250 426629955 426629981
    0x13080a031d0108161211120f09060906010b090d05241b0904090501020c070b090a17061602011b0809010b1008040809041d1006050406060c0611040306 66
    0x4644010281c2420000e18001001810400c4050070042610400000c0c0c0100c80642e040054030220120066000340095400409601a000400da0100022140a94814036228081c410300d900c8651459884da2800e48001e11164089001801008a01001095898bd000b400390b0000c03007441d0b0783d0500305030051040e0984c3c4040400d5a0080c1c020344c1102c5684040009007a03030f107440070340070000e589001784640c5900496440c0711803000c002003581156440c1808404584141d9075036880d240580c5d20241416005110300d040c00600e0071403101840170b0f4001c1d0100a0207160f40ca144403007201a12043d81002159201d072100c04115000994682c078044040d0b135012030b80d00d000361603242075035802c0c00040e0117510280701107800598041d894030b40181d0300003500c55541d801c220000c0d014011811620140c540a020b03002d544050029010000040300364050009680ea141001300f02da425200710000309040d8164680000d10541c00801406400c8d00844e0030241c40c0d031150310407a400e0040c00340c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 426632455 1250 426631205 426631217
    0xc0329090c1201020a1b080702090405031803060708060904260a0e3f1902040c09030203030301170f03040801021b0d170601020a06090305190513060513080a03 70
    0x589801c240d903600205052031002135290151001004003000074000e0301401e19842607460728208460b10044600164005140c0c3d14542041c0c20026100e9100705220b0030b214481c0c00401307500d4140030540500ca640d054481d000565104c4060281c10385006008540805e0855030034440000d0051109500807441e221043e15580b200b03401500c1c410f4640d0840788540c0c032500b5403070034201d04641c5c6c81c078800484090503849140038035421034114000d40c0c08103900e401106514085500c205c100c0c0c0c0b203c00c5c021101403000181c1404140d034000d10f580230194050b00f00f003006000350700700c4401c0020800303940001ca070042641168254110380240d000f0711081d03500051103e140b00030050908003624040c0001c0c005064400b1009003c10000c6246500040b03020710004407240c0c02842241042078200600703002980940c600140079600c14070b0400342d4095041628a03c642c800c000f46c4070140c4200c0c1c041a9024207098044d907043e04104081401e8541180740031400c00390901c1080c01e650b02c80e441da9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 426633705 1250 426632455 426632473
    0xe0a02030d0905010e01051e210f070e06070c1406041d01080715081504060801140603060106020a0308041b0b040b070c060302250213091506120c032909 67
    0x40010103d02c040b10304205052050036051500d4100501207081c0140a03190f42d0001c80e070601d10f09d0080110303010072903c0d4440400649503014040640704a03026582e40c0400000441000320074001c1900140c0300311104441800442010000c10081d41c000500d880e0409940d0011500104400444001035142034801049140c000b04500f0004c0c1107006514a000030940a00801d9040020001c0002c000380c040c1d415455111907005c0c030050850140240b00e10f58049050200380369044c1c90003402071280e200001911440490111007030383c0d060342e6140c81911191501c5403410000e5028610048032003100185080d01440140300400d40c090025441d904035003002d9100c45003e03400041410300401580402e00d604803007005440c60782c2c0021911179880d40c004100441142150b82c500240f420016600f805030300008016a00304004080c4021503e0b000f1150741c403440000c0040000d20400b90500c0003449500c04840e0030007104400d84401032011181280425090b140380010f60040c87c45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 426634955 1250 426633705 426633707
    0x9090e0a020907170739030905090105010c060b0a0b190f0201050c0d0228030b090c0406050f030a110304030f1107082a040c0e1e130e0a02030d090501 66
    0x4500d51002c528140a6070740c0c80b40c000481c1340820018440030411084c00101c040710300b8481b2494040c0d41000354440e440c98140d000e1030090321600305007640070500503907001640385800d1401505a4030182e5400340b8090780d6960301000303021030443e5980c2c0b05d001d01c400820300d1040740c3c4c00f41c102d814500c0707050440c0c1400d141d405001c0281820f190811641130408010809090307201707c0380802c4150034016501c0e0b21898000605151450309c0c40c5441c1c581010424043d6459002035205210444045a8a03100c81849107464402c0b440350030701144003807052510811445c4051503004034150f401142c83c1980e801040519401124101c0118044003208100d46a101ca840d5074001c5011009207501410b02508941e00c8940111100c6000e05031000014be0320b5860510182151003d442401442e0180c0f82c040c001c0781150f14003034092000c83c50460384039580b11030007184090001c0d001c64000c1440344482c4015040d11854088207128800300700700140c60420a49058164030350b0b8000c0280d0074840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 426636205 1250 426634955 426634969
    0x212010f030206030103110111070608100b030112020411041a071403071119052d100c03080c07021c02133b060906090c1e090709090e0a02 61
    0x35504601800600040c0c64000807641503079008100c0c05040340c0701c03600403143c540c03895003103907028026440000703400c9170040d0255000311542e180c03000c0c0c1151114001035503800700344940710455001d5561030015040580c810104404c4a485c0c503880d00e519170444481c082d49990510028540010343e01061080400394110b425155401031440c1c81103c0c0c803048059210085c03ca489148070506010103217401282c002c00078580074100509410242c6607203a101d0075060f0401e8990f032950a0002540c0c5421000a2907111040c6c032204501074080d01c04544062000f03110400d114420840e620140c1d4940550103030101c2d0094081001c0b821a2042c00003010a0452481c070307507414520061810202d1034640e05941e91590000b850600090041061501c1c110701d083c05240030b0700003402411540490721a106003040360032034040ba0b40e0001403102d004120504c03882e0185445860190901c4c0415405401c4685c600d41241503649512804c4101c8102074800c21841e4090343c00403046003401c0c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 426637455 1250 426636205 426636209
    0xa0f030f0209010c060f1e0515010c031403040c053118080906040302090c040306060b0a0801170f010e010902030601050f0d0206070303140f01051804030e06070f0f0501021201 77
    0xd8001d5041c0b0b000140064819001200000d20340d603155500041601119400b100c1001d0f4005680542104641c1c07000c0b00900042d00c2c00110442000b0b001b5006501410b943d407441c0b5815903e00340d00c101451000b51860b04060421142d0484188000032241d90b10001c26240d64002110717000d10605842812010314050740c0102e0006041030107080100c00c4d07001002a10340c0d00a0b110039503d4040000154592003142c000070342c00310171001405041210f030000742056a10501d800c00006844941c0e600c01401940380040c0050f205500620000c158040c0c0b510001000e0400c4030a1450110203080c29280c2c0c40500d91b203a03030b554054038001e5181c01c110032030052000baa00807054a1114001c140c079a4801180070b4011500000c90204041c429030103410300c40c01c4003103106414100301c00c00e42c004503020302c69071344030700340e904060410840d440060324042e0340d0545034458620b81d1441484110b0f08a05e46c280c0701008254282c0012032400003100700d00502c01c6000681e05c107540c00101150a4041e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 426638705 1250 426637455 426637481
    0x171207020601080d0e04090b07050c0d0305010b090402070317040303020a091e031b0e012705060d020411041a0301090c09030c050112020d020a08060918210705030a0f03 74
    0x10070041090a1011400b80a2410585407807440303555984040b402034a900d0f40014a04000c0804100446a1007000b6140d030766600020b41d0070340001e590085050b21401c0c000d41e0500724040200041c940f4050f4010500d0511038101400c40d100c88840041640780b0899003035010a0f000141100040c1d8011070103000340a40c2031000320028490482c0c005800b4543c04014a41990788860391069061030a0f01e90060440300c991006039a1207050b000e5021507607180000083c2401601e134041098a40035141c07042034003906411032030800380c0030403000d0400c21050345002402040089551000e202d0202d08030380c480e16005940e94940076081c42203c40141c0d50000f0407092a02c00c1c00054410318189044580900c0c0800030b00d110003200d41d00a20411102c2400ea501c0052001e1140340c016000910980d01251615135a40e2a00f400f68001605648030054a170003c1d0420300c0881b030584100401004105407150406203503586213403440c0e221111800125407203503444000342d80d0602641d050005c0c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 426639955 1250 426638705 426638713
    0x406050618010504091703090c040c080609040b18101508060403120f06050604090b040b060c0c061e070b0f0901020a170901091e1505040206040605070f17120702 71
    0x80c07144510100c1506000e8a48119168048801408004201c2002d54800c0e402000da8034101420300603501c00d51804198016800c00000d003203118000c0318613a20070a8090726400070741d9110b07654208400401498155003541c2d140301604030120401038a40300b0303d60803000140c481e00305806540305c174011b5401221540d0080041000003039105c1264481c0c0b2010f4103001c5810516110712074050841c6800141d08400f005c00e00054042c4a90041e80180900b0f59081000e4541002032180b1441510013281260303000701c0f02920f440c03e0180c01804070b02c0c807100a107502510364100b000210b0740042000e40710413131108240615031114414890308410307024001c41c501015198040d146186007900004651080d40c000340e020b840a4104070b04040d4451149000603002075941d14218540d40015035442031503502d200703000541441070030f0180d40c0003009a4245450f10317204840aa004400c11900a26501d2000d000108804411101201c11400454441c0b1020a212000e000000c120600310b41c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 426641205 1250 426639955 426639979
    0xf100f0e061e130510050f161b0c0302060c06061f0207090c0c0209160e030a0807060209150301140f030120090604080f0d020c1002071814040b04060506 67
    0x88210100810b00c1140100490b440e0754014180000c0324a10704050030380d00a00f41148071081d403030781c04203120b001c0c50412250aa11540700d980d00b41a4210381030300100703400325100d850410710341e00c00f0000c0030700c5003240c0010281c40c3d6002c1a0345403c1440c031110305501800c140445440c010206210015140c2000c250000e0034820081d40c44115201e0700135100c1d511484045054031910040220356000342c060001414031348400e250320b003600310506002450105410030180781c081045c1d072040342c00c044814204401070300c482000b907000502680d4407135030000c50840c0301c44410000e14001d0200c026200340362100041031051040030300344034601c641d02d03102041c0e440c012015400d00000e4410aa401c0e03e07026230a010039801c0c4034640020100344903800c040701c03101c1000100e01e42d0b52103c0b0740c04c0c2d555011b19101404030401e0340070182c03009030300607800a1103009081a000d0903588088200410700700b0300b4402c0c42c0c00005040d94281c549540c5030b4104800d0240d94042c541c6c018a0580d00204003217 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 426642455 1250 426641205 426641221
    0x919110f0603150609131803020c100c060b0301061a090405011d1302061b16060305070f0e06070209040f030801140604060806030703020a0f06030e0127050f100f0e06 73
    0x510342ca48507841460040341d100c200d0b8aa00c0001c1b114500ca00d002007004600030400c44c4111007031004210010b101d0ba154240720b90900c6101011810b0643c1c0f43c1c140110102c0c5d98040207040d40e5049950150b51381d03240000e405614440240d402c125503066681d031080c87d001803006641050f004002c00810340e0b01456118000f09801d280d00002502e0000300c0c64490f4800540140318114001940d03989154801c5c0c0039130380c04106d040c58034090000d0304c0311056503120183c1c00ea03502149d1040110b40703526512980c840c003801c821203e14600412142ca01041d943c0051040b00041d80c0c180c3c1c0304001107400e18201900700c42482c0c050810600b010441c141c509000910f544154001c0c001080b10010105d403054508200280255500420800045484610400240c10f00d441640b0001c1d00380100102e98000600c22000380b0305960303007084a1140900306200031740751420000c8070325100d0400f05003c101001e204542900740c95110201d0007010003131401c0c042e12120008444181c0103581401010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 426643705 1250 426642455 426642481
    0xa0e071706152809020c070504180201022a0a0603050702010513050c01050901090b0705012004030c0311010c06060905011505040509010501030914070303180608040b040201080919110f0603 83
    0x1c403450124129503020180e5090f0b160300c101da130001007070343e0001c0340d4514030b032101140340001d842060b030301003081c080600181d201c6e2035240c40c17000c0e003da04084903044800713080045200300e50300720031414910900548003141a20300b82c0e50203140042d07a01d805002030300342e080c000c003908050a41d5a0f2000701d8126122251106c4003643d4803414004002090344899004e03c0c202d00081443c0020581c0707070815800e11a02810f011804000d41c0d144144941002588401c10f031010703603170072008549115085507140a8050b040322805130500c0074019401001683c01e025410242120400120f0194503007002c01680e800c2203c01c00050010034002400a40c0340c802c84141101c0c001d180101c0c152209082c044006001c6514450311401103a6002c0305250700b2940c10149020707020200980c45543c0c0700b044603d402d043c0d400428514861010070b0240d0711030700490303801c8810710040e1164084864510480c0c400e076424119004142601980c5c45c601d0074607681d5400c18800c1d183c1c00c1c0303103107480c031302d90804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 426644955 1250 426643705 426643729
    0x5190c1205031e0a1104080a110a030b0a020904020c06270102040605190504050a03200603010e070804080d0e0a12030c080a0e0139020705030a03080a0e07170615 71
    0x1c10b64a20f40011501c00d03071078000100380c0b9101c15515585685070540c1c80d407280c0000c00141d50341019064000400d0404483e94000c407600f0242480054a0b890750582c041d500652101e0b030300070b8083c0184042401c09210041c000e5400e00140c400d4249042c40b1a88418185601d0b8601d0ba4414041009001e401608540341071071403101c40b008010048106803401d001c0c540083d030300101d00c5040442040780d081e000d1041820000e51000c0007401c01000c000036803000b40a420842c0c4d40c0c0e0004503100a01503882150040e200d156141d003416120403202c01111000d088004240e0b004280e05010b02c6805200240c46d80518601803016410b5620b0240c4201c401038021310146640f205000c100c54400c0d4000390802c1084198042d80050801d1015998401515210301d000c004104102c4030070700001c1d2480071210040c0207004020710544058070b94510080c0754105031911000d400078004400c4c40703850090b01444070440305540490041c170380b402c4402001000d1460705c4040041c070384d42d9403003000d0074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 426646205 1250 426644955 426645001
    0x31e0a020c0108040f17030f060a0b07080703140c030d1802010207030b0a020d02031003060e011509091506030f05101e2a120b061809040305190c120503 67
    0x140e413104e20b800e0075540003488029100e13130001c0c41282102180003004501401d1921221011a100d10f001c0144c1055a44212503182000f00441c10020301e2000103043d9040c000c0c00c00c1071000d10320308182000e0750320401d00c801c003e8200040c00d010200b02d5201b84034480d905141c45445155241c1d0003c2d40e20b0960f400040c03c014400c400040c0c021503190121014580c000d041992281400580254800300600044618604000444030741140502c00d075022a041d1004c15080c15160845a500404400348107941c5000c0001c0c0075442c100c450b0080310010b512602e40262422100c1c245a401e007440c42c60350365103843c2800150440c214014821a10b8400c440070300040c15810082c2c03c442c441020917040079844040c0e0840c80c030481d008207410300302c58440310092145121103410003c0c0340c860054552044540310002c00514108001c0b0250b0140c86814060314082c18074000c80308540141c00340500082002c040740041000c54416207450301d407e400e0150035800c007507081c0f0008611640c0008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 426647455 1250 426646205 426646217
    0xc21060828060e06180f0615030a06020c1b0d030210051009090c060201050a020f041e03021302071112152511011b02070605071a09031e0a020c01 64
    0x1480704100e03514420302561211040250480f483c009944030a03085079800500759017280300c4100040c1c0403c00240045010010f0b040300e650320703004150407800003420701d50148510340401c80002c410307100130400c950820008102802078101320706280d40405040d07900400f9016091400aa00081c085001c18505a004110b07542d88000c2d0700d540c080140d014170840350401c42c00f9403e1010400c8080c0603260a03038000d0080340c0d1044c803038806a10510a80034540710b4200810041c00c5440004002c0c0080c41d1403000002c2c8e50380303070006441e1031030f000b41813544030382c1c009030031020080c40c0e407031000c032280054a00720103104000709041e80315428511281900e00c80440021070007240c03509550350021082d031000040301c4c000074008142045402002c003096190600181c0c1201c4500e541800f00303110396008000041c14010215650342062000712a000c8444200d00595880400356034800d02543c4002c40d01c170000000480303042002019610f414020800c076008000e079010940058a8000b801c0003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 426648705 1250 426647455 426647503
    0x60507201501050303070210031806060905060103050a0510030b0406021b1b0307030309060318080307020c0108010806130f151e0b01140306040c1b0c052403041e060c210608 76
    0x454807000210ac000f07001615003080403400d20460f900c0240a11001e0b6010090342d540c074452202203a070280d40304001d4042050081002030151404698020300c42c0308003504090442d00c0c2e0084809445c07100755001d811001181510403c4d1144d0191111822001050b01030301c1d644010f0003600c810302a030820503444a424080c44414048101c15041d8080411540da1624010081d1182802004240062038003000004c141d007000680b00d0240301500440201c0c41d000c0e65a4031420300c40e4403002c40d002c0c031f904019101081c1a9103da011118250310094405644001300030003120702d107035a002c4c1400680311010380d00a1482c0d050b20707401801038070001143c4d071a5100503982d0080c134030100d41d030b55241c40e02644100000e00000c881241c00c00d5405007900180c0070180e407188041d01e21203100f660b07000c0c000100800c40706d07800328600b010412400c254440303803602d591099030681450701c40410480d62200c03107049800c403007070704019610f15002c001c420305002c81240ca42118242481c8502588000707 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 426649955 1250 426648705 426648731
    0x8191710090f0e0d050417070e0c090109081203010e07020f070312090810090b01081209100905090403021b040207110f06250b0f070c06050720150105030307021003 72
    0x8911020380c0c000440b45a1141508010820703032290080347d40d080042c1c0c0c00180d955000040060076140421514401a40d80c4402c0400c2c80c0c0040c100d8a041019403c0006440c1c6428880c800340c1104e12120107035030703604007407002d20100c0d0090031407811507115011440c1d2000e07021820300152a032041c0c80080040e50040304407103c01280d0803400d190301030a60492844403250b44030301075451049507555020b0780d0b61140c442c1c80750420709608500c00c40c100800809482e281030300d05081c0c0d44a0424080c00ca03207560228114075404c441c11805a441070400726050f041300d1b0080d02c0301c031200b20345c15441c00d41959a542c3d400c00206a900d8002d0004c0e4030360880a0346d07444142d03020000040c1421100078090450a00c80a03040c80742551103030096004128002904011640b24240c2916294007644e21a07850310003c0c14020842401c219002600c010038040c004c01d001d2191088500804403038105121040c910041a802030b48030754001c000000060316200c0b5105401462800c0c006803081c0d29423a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 426651205 1250 426649955 426649961
    0x60a210f0c05030421050706240905070e0405060102070302060310120c030c0b0301050108150406090213050316060c0b09120d021207090e06040c0c08191710090f 71
    0x42100540c41c108180d00d14a030303602c2030107584514001da9500b01000003200503008007440300104000020010440000412880d170414032500c10300b111400702c00101c0e809410b644604603000707802015242d00078068080e07170008020402e010201c408003c942014400030b0766480785440002d014450220010320300c48c0708445030700300400f071100800d610500c0c14940402ca004040c08216022402401c001c1410304030002a24103031481a1074480c22034032011040071000c09482010f40d84507840718008120800c050004c4d00c040d4550120054599050004050600c41003100e4036548105d045001c10a450780100c40080d500c0d0880030304465911180076050800500b85104002094006107003c3e070a4031a90082000180c049190071440d100d1220840e001441c602c210708801c091000800ca071460b2907449110340181074100300180380d070f440d07449030717881d070402000d51910303554050105100030b800c0001c50b501c1040301c0503034002d0352400510f1600030746101c2c010310f0f14055590220304410f1040358 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 426652455 1250 426651205 426651221
    0x120a0e04270311030313030c06020915091002060405191b0b070c050303091005031e0103050c0301180c0e04080903031b07091a0d0201050912030903010506060a21 71
    0x5000168079001454411a299140c980110001010b90030000e08400700801903d0051441b07103808045640161401c039220403000c182600c005030f0810200090340d5230011481c5550f03100388002903c403d104010401c1e410b00081001e07003550894410080043e901040b0441d42024a04480c4492161401e00d1000e1005800e510620512003a401040000a2101400a42e8454aa4000810349072007e141e1280514441150082d6052000e0300d48103000e900555402182801a100009034421894000c00800e90050b1100d0308900300640e03150a0130301480d40b60075440e501c52061000d60750b0300c41c240d0034401d01c10500301141c400003090400400c0c1080f554843c5009003143d403203c02c81c0c81520586881342c030301e1517480c1c07080c00070001c0e0392000c500a400c0381c20701d8000309890000c5402c040c071040310785501c0d0403410000d0820400c4955912984400c8040c4c920000540e16542d11000781400c5480103000c81e8480c420504c100040e496000d058040c00e012a203e401d00c0c0c40709074501241c0644602 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 426653705 1250 426652455 426652481
    0xe01060f1a0706140a02070203100b060a0309050c060a12060f050607060902040b13140106020d140f0d02040e0403020d03060f0501030b1201020315030601051203091c0b010b0912120a0e04 82
    0x80020300101c085d50340c020b00150741c0203d085e1107007100f0550001c2c048130b10140c48150011030034043c0c40c107254080d27801904168010b109a4049049141c001105d41d44064110008100420390003101081507100d040060000801c1d900344141c00d080016143c2d01801c0e80040909484500110440d01e031a001403010341d01c00342119600445072402d403000781003100c81d0301141160b98030001074868400209030340e00d40c1c819200d0702031909008140c2205544000025420644104a000b01d10501c0788020002014003842541c207a0030940b40003410305a044071a0001c040c2017910500c01c00102041a604503542402e0004001103c10003007454031643d0b83d40400554804003c124030054240c07802c010070030046080c0c511603078941040025a84031030701c0c803d0041d4003d000c40851404c2454004010030301c5000c1c190403040b041d955900d04503009803c40700b4040400b080210a605190100c0d6616283c1d505c003403c00c000902d40040054051041400200031004517051a1500c0b564001003c0340d840c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 426654955 1250 426653705 426653741
    0x7081c050106120b0109030209070e03071806242a0c0311130e031902070305060c130b09030616031d0c030f070614130b0c010e01060f1a0706 62
    0x35451000d050f60010422040744036003094040c2620758824408031b01a01e50003001d064141d26076490884d0410f90080c0c24503054841c400700442c00c03e00903400c2c5407640380e00140203d0b2282c180100301003100c1c2150a8103c0715403018214486254005024810038243d10100358240404910a40352440c440080a0465a6908400f10500a1065040702815030035205103528000d840d81d1030013181c00305140d5102c0d64100340f103518a640202e00c0b46049507a094411640c1488e00c6c0c1c2c84a90404006440303411102000007000700040b58a100010000c0020781000d82c03d0880c07020108e903c0307440090840880d41d5000c1c4c501150315000307a210f40801d1401d00c0401c5843d104080d9003a0b95047d003044075a00c40d1003000980012160000740352000d076a00790b0346e441c8481c8051401514960040600700b42c0700310b0405004160804144040c010051701d04001003115448640110b084644c05d0b0052810f82488190502c030b400f107800b54181c00c60b04c400b890345680e41040d003816802020b212410303e407001e00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 426656205 1250 426654955 426654959
    0x904020c07030b07090b030411060c0d091a090102150a0e0a060906050a06030503070b0910050a15080601060f050904140f1b03040b060d05011b11101107081c0501 71
    0x190004505040d0b0b03118440c02540c3d81c4406005071181d40e030303038480d800d014001000090005000315000018030300d405041c240c00e11003414607250410002c0030b2164002010100c0c104940765040b10300c0e80f10386034043c44c004e1400f034030400000e484180f06568609103c08510204400c03d0003544916403031810342d0241d6540841e90725006010305030820341590312a0800b00440d0110700c481c81440200da80c8030f80218a05402a62880080000105001441e000d2140c030a45404018020305e849aa04d0700c10004034180c41c0300c1c95001c00c1c2c01e2504030300d40c2a4840f00041c0249604400c96680130085414419242c2c68103070002406000c020542c8021441c00d0814410580c0c055882070340102c030030a0580004811084e05802c05000880e0046c03c61404100800c07680c2c00c00715101c110740ba000360004a901c114469140c6040e0681120860014620380c3c200f81e4103050500076040700390140c0c0d109020710603240c0b030588a030340118140540b241c0400540351410307044103d190010001001c405114542e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 426657455 1250 426656205 426656227
    0x6061803120d090b06041812090506070c03060c08040302030d090c0305030406082d07050a12060f05010e03071415040305060c03150306040222090b0c0c07050108040c0e0c090402 78
    0x20f020801240c84900700ca001c40c00e0b900c0e083c000c580d0310b00342d0b034119156421050b07101c0c0901350a1030ba03e224180522030b04c01141588400300100481c90140d00010303046480c6141c040c0460b0001ca00c90020030040c00d0900000136404412241c4540c103084001c2460144d0341401d480f4510190310092051100140004105422804580c4140254043e4400125110030300b00e10a45424444080540546c4001980c0324003c4000d05981041803801c09845411410f01d4411588a900405601002c1075010001c40d03030711a1003001444815800b80135031924180000b8840110788000321301c00c8400c00300003015000281c1c2543c00941c1c1203405c603032043c1040154800f40e030b8400d40300903d60f0740b0042001c0031a414009822809130f035010b09600da0b000c1040300c51135001603510716590300b62506c6060b44c4c004250301c106e5039400345068296080d0307180c80e128030452400c5110f40c4160705106180c020000810811000013080302e10000075031600c1e90743e000c990b1080388943c5100640c8148041750006480c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 426658705 1250 426657455 426657461
    0xa0311060c19060e030a020d030c0516030306080c010306230d0f0b0105010818030a180b0c060f010918081812030c2a1e0a03031205010e06061803120d 66
    0x428000c6604005114413070b20f82c1520303440307031503d00809a0b100e4540d40081070301c80c0d840740c00e8110b0107207049030600010802160401180c20825000a03460310400d206605040c400420f40384c800342401c011451401019580c111103026000740124804084010241c9076101c9180819070b229503070500b14103140c500b41104600078002d2a00244030000000c904c008a00315402d4130380c0e0100021810301101840c11190416451404481180100000501750096802510310350341001c01400c0c0070702d070181300040d020b14142e00c5045c0d010b08103507150074980e00d4090682c00003908000000d6030f501c0104108800b4280303e08000d500a01c0b844900071205001002429440c4403020940300c0784519801544000e46171079a2016000080b0030441c4101d1501052030341070000c03040e117100c111040c0c07038000820031080b0754003d401103400090700c4001212544100ca01401c1114602103807410b0150202e20340e03000c0c09800311030b45030010709c040005c2d039004c010746c140d60305005e982c26548400195a039809 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 426659955 1250 426658705 426658753
    0x9060403080c1204140a080a0302040905060303090904030f09230103050f2205160603050702070611030f0304050c0a08010b041512062a030b01080f060a0311060c 71
    0x100180702040d2014868002ca80c0c00c0354100d00f50540e00c0e103442c0c0303c1d00b09541c12180c550030a4800c2520050008035188040d00449016440060711180340950b20b03001c1c0d0301d00030820362203500104440d10895503002c9800d0381054140c5082c41800e0f0014200380c1342c46071180c00000040325101d100f444620341c6140b0040c503003802a42e081c0483e446440c4986480c08094407000042d60384200701602e030614500a050303489004004403000300800c18030000e100302040c3c102c01d00081c0c440b0204182c494040002c01d0042140b4513050b4021300c51608003035120300950000418038840000800d0512400b01302c46030036140300500c030780c6c0200da442240178003c1c4441c0c02107d020b1410b10804185214410071001c0c21a104030302585080d40345507a6100c020320f48506500008000e03183c01186242048450800202e100e40340042d00300b0584001400308003008007198400c042c0b000030480a51200800070040303030b5020704c812000c1c512a6000601c1c1e0b0140c0805510584140c031882c0200045116076012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 426661205 1250 426659955 426659957
    0x5090105130b0301180917090d1509050d08040b012c0a0605041802130f061716090b061b0c060f090a0909030c03121b0f020d02011e0b0301110309060403 67
    0x50076601781044000d4804001c00074042da036000c1d42002d210001c41d0010b28000f84000c06110000700c0036030315107000702e103890011249107a59948400420404100d0000d020b004e900300707050240760950380c803031400c1814083d464180342c0b2a07985545420300c1d40c0380c071188020600b58940300c501e4100b5455008008a21420b8402da041c18a54aa04819100c000c1b061980250808903c0c507846064540a0802e102d141c294140c3d50782c40019200b00403140c5401c3c0d8a0509020f02003c1c103c5907001d4013688050781000000a10380441c00000b42c0c0d4103000c68028544c05206030000c0844450f000d802d1054060070700742c0000740040c0005440482da001084c2c3c48204440202c49544c890701840c08550044c0e074002c01140107201035101282c0200340110541e0720f111030208030540070300c81400890f0684074400c80840d02208a20748441d805008400c80081184000c00044685141c0d030210a07400300d00307094a255607540072440e5a00d0a40045605483c641101903503810042c16543c2d507001d0484080d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 426662455 1250 426661205 426661229
    0x3070207050f0a2601021603030c0503010e0403111c0c03020114040807170403020a1403010f1b051b01050c0a180609030b07020f12041d0108070605090105130b0301 72
    0x215080c5040004040740310b02c05400c0c0d040c100d0030124804980700700380c0b84074106400300100e4110048000d00060400900c03551280f91500124940502030b00e6050302c0b01800d000083c401440484041080c040c0d00035010b281c802034040c00b155403d410072140c00d038504820403003200300900d40b640190079400698440c0d03000b0004445030802034807a20009950080607490b04024183c00704a004540406400c2e5a41100d45820703a6680000d0800401e90302194202000e5110244245801c0c41440039191000d0340c18014500d00c140f03000000c50008035584240580890700094040d95100c0500544840d20000c001900b407143d0420390640200300c8200004210f50328400800c203180f943c8000301d404688480c03a08a0441d07442662808005140da01184680c14200028040421500703410446250300d0581c0c60b41486502c03454402c0d501c0400c4100707012040104140703440000c103441219021f2600d40d071611a030100407615403040340c0035040742d24407040c0045030501030707040114101c0300445412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 426663705 1250 426662455 426662459
    0x10020d090e04080409090311010e0c0915090604020c0a02041d060705040f12080c0a150b060711060901020c130c030f0605011d0f04140a0606020c030d110c041103070207 74
    0x3001d070000040390b00a00c0303420280020891002150032401002d8420308000c50b001031200c0c40039007111589140200564040758824001303042481c50142c00100e0114004004e00124004c40e03c1d241c806841c96000b03035030005950400010910145d100194002c0080c4480340001070170404220518054883d01d010b20004141858051001c40301105d410351007140700140761419100c0c4a061a107029121800c1c108100700024801780070444030340d07124000c3c81601207250507000e0101e66211320b2603400b440c03082203081d02150008101980101c011038010b07940d8401900100d0070802850341c0fa64000035042015554031095811a000143c5580e42c1000222881c110000580309680304007400f1500544a107012001200701c02c40e03078140003814602c84000d8480214040390b201c52544418404900309110301d80c0600c0c0103220080c040c03072000b050340f6202100089d445202900501040c4601c01e048000030310700c1032200842446008200f0070680e00c030020421410740c41203641c40b006000d80000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 426664955 1250 426663705 426663719
    0x30a0c0b0c041a16080f03090d0201060f1205010b090c071203060308070f060b060d0c1b170c0705091e0702120d0b060c01020d0605240a03020a05070210020d09 70
    0x3603400320f8009011100d2400b0343c540000031554413034400003198209101401c40422000d800a010500d5800720f0385035240340c90900c81e070500c0070700744007542164140701041082c0701e142c090003030589900b002c403154aa601843c09500400c074100313100342c02c00001d000300550060364002800b06140103102441280781e80c40411401c8032258000146401014400d03000800c0340700803071058061049100007840c20400002030080e4202c500002d10103912003040d0310080787e02c403072848410368176668454880710442d40c6030700d800c24040400007801c00c800701c1e046030f480404101c0300c0d0041201030310111040c20100c04c551078156084580c0714101c040a000305019920009008810710b11032004542480740070407081340070300031080007240e1160007403104800901083c80201307069481400001070344c4c7d00e00401d12944c4400c0c3c10a40500717100c80c0e82649100c499080032902002c10500d070040e074400081406494030f002d00381000c0d421201c003800880e00c6075000030b0000c580700303501d03162042d01c02d0303468003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 426666205 1250 426664955 426664957
    0xd1404060801090509100e060a1112060d02060d09030503150607050c010f11070b07110105040305070306021c020d15080c010504050f18070e090106110307030806060c030a0c0b0c 78
    0x8038000004050700300401504040d43d00207070b041070304801034409000c4080400026110303112086800c40c0c1200d81480130103940c9106504881e031075000340c030703083c22100201900317000002040103000c1d1030b203140c0c00340855488030100d03102c1c1544402c04005110240c20000d103240c008544414451410003400210b524141040e20041c0b136000c001807100d821084011a0f0200080903600c4c140807407028881c801c2c0c0018440726000e0410031004d1521030049081040e80080c8000016052200c2000f061012580c042a03590a40343c004c01d026a440c150803e007414040406803d06130550302c0030403511065109900b15a410f40d400c84060141c8544484945071104161010207001c50000c100c00c0042d400c00a9500b440424000c029080e800f9540808401d200380884a4070006001840c03020030500d880c2000a01404107480e000e62451201007100795207101c1c803000982030014510025040ea9120001c0b2201c0ba9503034403d5070344030012648064494091400e04464107501c100c0040d800304c40c0a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 426667455 1250 426666205 426666209
    0xa020d0c0306030803040303150f1e092f0909040602130803030105180901020712111203070507200a0617010506031303113a080114040b040e0a050d1404 67
    0x11319180d6103071542c065004104140c0009084e10082d03c0c0040c0400084105074010b2003140b103001e5a10365401f0300101144820340210503914030b041d15002950680442c01104007182a100b0034040ca00484070741524000c40210381c0e8040d480d80100010000c3c0ea4014140030301100300100d40c8151201c00306500d0340000d000d2142c0084880080040440645000540001008000500d445c0b82501c0350303203004115520400100d40004001080303164104034041882c81400445425414600c000500d103114014001e004444140361600b01403843c1e80025009040050045915580d80c0101800d82c0b52551144101c4001100000400d420100c0441c1d02c035111420001d8641c144964003501c0c1985880304e09551b03485210b880c20407800102c079600c40c0c012030308581e034640700000c0b0000d071041c84411040e10b020020400010051a18440074070741e07a0140498000c580014400d0200d4020600755a682c2d1040c420741410605002010401203601a00c503950442d040030b040101d404107200764 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 426668705 1250 426667455 426667463
    0x70e1303081015030b01181e0e04122007081c1e05031b0c0c0901090902030601151412150a21141b10020a11060c0a08030a020d0c030603 60
    0x4000f4181c4007601c250b21241910340141030401d50100201d906402c00b02940c2c111800a006804480302031261010803030005080c41c5414619a240c1340d40c0b001e49816001c1610011f011845808071401e8075140306511000800e401140c54869a4481f0550742d441083c4200041c42084414680f001d0b1080c040d104012515140340c4018800719007040741c2315032000b0301005e195140306c0755010400c0010001420100394070b070001c105000310001000880341040e07211000151900100310010780340490b40d01e044601c40d10701401c00700310100054078004d040701809800b070f4000051030265400c0b00780c103660140c01003040950554041e501031246250540c0101c80400c42d0794241205a14881620304200c10311950008501c000030f015814540b407646041020045400400220385082c54100012000300510040060240e43e8503402c00303942c0c14107185405142c0000700b501c89d12034100300c5101e0030b540c00210141c1c0e03844c00c3ca070608000d4100d20300d0040002e051100b03a600591107402100266504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 426669955 1250 426668705 426668729
    0x1b040507090b0f0d02041208040f0b07031e030b031905011103240607080406020606040b0a1a18120a050c0d0309180605040c030204030605010f06021e070e13030810 72
    0x31064811000d50808013490b80d00c20f03000c2001052003145001d81c1d102c1e80d4800c22040d03458034100414513a1000c80b68000c2e000c5034006003e0600070940c0415000040541501000144c3e40b1580c4101e004e840484000b0760940301d4031301e140b4059200580910752542c043c0d4000c010300d8102903140701325448156032544c0310001062078000780c030350560045919104018012844c0c400691390f1900260480d9004202580201c8200b10260801d80200ea001c030000700d5403005010708103403090307819040c0340407200f0064001042c400c05501c18800c0c2203c074142c00400f0310444042c54005960380d12001d0208840c1ca010380a1a804203052900341c002c10658551038840c91a0b01b4a8813034010403000d861015449522424000b840740c0b1180300d406180305899402580e61801c0d410400140d40c2c1c1a07101c88960b0842e91010018107601141e05648400d0400034580c611643c4900c492810942e5040500c1045222044c40300c880c200c0304606100a202c0d469101c00c0d90b0781c0003604000b0902500c9224100d41c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 426671205 1250 426669955 426669967
    0x40e03030412091a030103060b240a03020d0f0903110309031506130905010c020d050913021303050d03090201030b010806010f050a02010e150601090506030c1204060603051b040507090b 81
    0x4402010601c0b040b03945000701c48113a50f120000b0106010400d10010103800000500138044039008010001c08143e03010300c102c0f468011441b8640a1140a103c1c200d03102090070b2030342ca8072035011510300c030189010030312a850141c00941d00426020108501140c01c2004a8407840b8003c0281d9111080040203448480c50a441099221707000900300c540c0314050041c40307903c080c0d039072050020440c010000018000a4047c02a15100419800d1805d2002c1444804511340da03158008400e03114500d00503882d0741d004d40c41103080b05c0b010381005205014810360001d000c1d6040d4031040c07250b0b00036a002d104440c649070055131400e00a94869001502003690200c0807805680185800759091000152640b0350244d8141031520600490700c61003814000e2041a41e482a2404040c0008450041ca141061200b10810388070700b501c1c050803c0510700004040c05601e1348640c00131074000080d03a0205080302800301c0219907444000c0d210b5803800c00400c9201e4400c000c0001075030740d03082245140035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 426672455 1250 426671205 426671213
    0x2309222004260613030f1404180207050709091a040506041709040c03060e0a111215060307020114010816030609020406091d011a060f1c0501140a05040e030304 70
    0x102c02000528200004200154003076081010030f200709404888410604140d160061440c5140c9500d441000031001d4400000440c010480c2e0483d0500c0c40300d00e845c0004045030314043d00900c1c3d405011405600307000140080c068205048440c07049242c5c4150440c1440286c0509000340d401a00f10350008000a00241e020f41c861201c01503034201441c140302e9002c000406581800005500203038a9a804008414a0841c2260856503104050041d0f05416030320344000e00400a150300079607985004103200740346090030980d62880280045a5900c0d18501c081e01a00c802e03603107081e03c02c0141c400006c10401c0456030349041c03106415000041072554450034054104050140d911135511040051050b00a1090407a00e060314001c05e405001c1c08800b141c215800040c012100b140814494003d40c0e51300d2040b102c848403940119a160800e5480c0c1c035043d160900740d0b03940755a01d04000455482c60700d201c200c414a0084914600e81078565083c001582c100105840043e0300038400300d4000307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 426673705 1250 426672455 426672479
    0x20307150207020a05060f040920070b0415020d0204061b0b150f060c0a021807080c030a09050d0810080109050601030303020f0c060a14090a02012309222004 69
    0x2c600041074080d85035240c03030024a07035500a40461802d044005420050300007180142d900d0780c5a480e412076914480c1e00c6c00348c4d403a4030480c080108100b0001d000141046a0183c0b441c0c11042c60b04403c42d11968190781d43d4000750311500419000c00c1040700030555902e444122010480c1d407028240d1081e0b2540580454070485584006d584401d10401d1005140c4810002d0001c00300b0020003446841498018001c4280c040c180c0e502c0382404107010417903501d401016003504a0000c102003540c4e41c1c0c0c2e03240c100d030040c81000c10090840c05201c94400c1c6603548031910f02d004105511707a1541c0f56076206082c508039018010300500540106004001207406580600b0402d030050901501d011807031800c403403c0c807404031003540b0015a2140054010070342003071001e510100c510024181c220150300040c003803a4010030b100710140483c490b00108200850181c43c00361001074007821507807984140100c06054400140c01da01f40c686901d610950031004280314081d0b4002e00c040f0b2906080c50042800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 426674955 1250 426673705 426673717
    0x5062a1c0c02030903011802190b0a0c300e03071412030c0f06071e0c0b060f120f10060e0109020c03190e040b0406051c06090c1707060203071502 64
    0x55000c02d011104c1c864400b8080c101503901480210310341d80d480344c4104511014105103030035030700d00c000c1c0c4d05001000c080320888005440c2410100c074182204e20704040506100307909200f203035180d04907840d00141c0341000c00140c0400703501d5449002500d042810ba03030b18038500ca04810f004104840021a0400080708600d402c043d6040e00c3c50f01104081075890f10080341c003401155480320081000a9512021040c0151960418001080c00d5804c000744035490290300a40207101ba03801041c4240e490f2070610020040261134080c0e41034160706540e494071400380c0d008005000d484540e03415000c0600c208403e40f0034410002c0203a07424000703680c00a4000000c949030600c02008010600c880d11011840192010760341d030410036600b8401e10041ea0000004140a2810031500340281e80e65a1090301400c0e8201410320f1026259090540c040c100015020b00450401803010039100020074140080b011200c089480740395a070038049950b446004030141040e80c03216440e4281c03207026001840 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 426676205 1250 426674955 426674957
    0xa030c15140313060e101b0201050106020102040302011d0103090b0703140f0702060106110106030b0a02040503101a0607060b1851090c1c05100b031305062a1c0c 71
    0x1602c00100d5888000c4079020b01020710306280510074030001f40e41c24024203001d09810710095080620759400030700a8060440e10141b0100c42070014002c076413003507008605032a002030120301c0c03074101541d001d40240300b2401303512031002e040f400252078410203d80d0940264066401440039a2078440b0844a000c0380c400c0d4034040e552605000030200e400b95681314001c16080d03400590319881c0c0303001c043c42d06003040403a102c410700b8203000c06c100c5a04508420028081a103015075a941c0504c0c0c00d400919810300354907400340d80c0000382e070601030040c2c126a106030100b006884c403c41c1c0103150b0100d2880d0180c4205481607840203a100c1403e2000341c0071905003140c14071442400d03095400a00150310440d40d1020f26000410041c0600c070140f49201c440700303641c0310208400d007045110707a0500800d50084100d01d03071001001c00c980342204441340794160b4112090324824241020322150141e43e179070441300d0204100d0b5040009078090003c4405030030300c0e0542c0f1403030002032004030030140c00d403404420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 426677455 1250 426676205 426676213
    0x30a1202120705070609050d050c0103020f0d050c0912030304200414070c06150e061e060304060b03060a020f0a030509010e0a0305030a0e0105040804060804020a030c15140313060e 79
    0x1540301c80444007800d01d503032090000d400d600303080c0040280200c80320303884076114941060400002c100d022900d46118031082c80c0c05a80c0385100c071000d40c090302c0350744403500e03003a4135003403c2007034250440000d4210305808464200c0d50f4a01607021994a0005860283c81400d80b01c18408005080c1100c0346804840903001088655007041a018035240845805020070002441d01c030070051144681c118024507445410355050401c0d503103403540e0000416041c0a40b84201c107505104000306207000203000014407403650780c40d080c64814060940625028080c1c403c95020901d9020207002303803000013540c2403a103400d162496204401628001e0004112550b0b21200106051000c1c03144031007075806078036140e07683e050040490080702c4ca846e058120691504092000084103102280c00700c510900e400c941e1501c1390f0001550841c0290300080007a582c8107070000f10503229a02d1203030311512580303c900118190b241110050f12040b20b10075410440d800325840014100c2e4012031060403d03400700c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 426678705 1250 426677455 426677473
    0xf010203030c1e07060203160503010f1a0c0d020304060e03190b040c08010e0a110a15050f2a01050f0c0306040c1b080c1e06041203021606020d060501030b030a1202 72
    0x52144e6002c0c96060b00c034076030000201300e044020f44d0b140e40350b0b8402c94074003646950f00d8128814a541ca0501038402d11480f04035500300c0000000041c0d43c105045007007511501c10f003a4101070341d01d90161103040003146c1241c40c849810714010400180801441c42c1541d586031086d1b03120700503031200400846282051450105d28210f092185840035950040140858059400c0054098400152151141c1e442d040c06110190810324800003030340341800c00030b8481440c00030322810360050035150044107101000d4441c0c0c100b0b56082030a0800e011800801058840c101a403019520448000e083c0c41c504201181301400d20b98000c000e01c1c1071030300d08200b01da8900781c820780c0d01c650418019104050042018802201c040c8a070402e68800341219001c40002e07405160f4582c00000c0c00500f0f075006550180c141d080c002c3c4c0440e20a0106045a00c2c00c1112914041000390000079005002d00e14001c808980395000c0e1107202ea044400400511001c0342aa440002070381341038a0b1001140030b1a812 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 426679955 1250 426678705 426678757
    0x9031309091a070806040b030304050612040521040302151216170c030405060105030a03020a110409020904051f06030302120702040b0a080f0633120f0c0f0f010203030c 74
    0x12943c002d003099640e44409050400400c000d0b11111000e15110f50020081080107a68000840302610002800003100355510308110342403612201e080c87c12115000300e10381401d035800c001407080c3c07442100c514107044548480c0401a010350228400765441d8040030628411281d42c0449185070140b03050820b00c2c1c0c02007211400d043e400c0c0e5184c150880c2c0441440304010080c441d481c00340100380c0040c8405c4000e07441c02560f8003903d25014000c440c80350902e40c119280c41c1c00c2400c80c00d401809601c00c0d4202440d0160b40c0e017000070142142c0c100c44444007100388440d40512812079825074010002502c1010850516a00c9180b080380d0051303840c2490341840c0c0381d44a00c0d100030314030754001c1d00303200c101035003528100b00000308000080e005070765a1a01034000200100c00200440041d042007101182c00300d11010b4082212020501c01c0b004043d592800c001421181c01609680b5210700215a03c10300440000b05c181944c050781040c000035008031442c0740941000d211032205188440c6651203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 426681205 1250 426679955 426680003
    0x21201020c1b0f09130b0c04030c06080a0e0d090611011515080105011814031f0b0a14100503090316060c1b1e022107030203060903130909 61
    0x10b1000e800401e0504030b450245030a00f4148440381d03096910400a29105d88141610b100c5000c00801000c608008921700c1680d04003581c000d164004400c042180e212100074080881c02c0f640c0110720307030505108110420300420f1412803940161280c0b6095410700c602601c95a003c898031030981e43d07a60b400255255814000c0c40000e1042c240d0749414982c0407100280001d0058202a0601ca41c00c0c82a86803002901a10012030f0319814400c3e029400d0100040e08000d050803400790356004109040d6014207143c1d0100a0301e04007141c420208a41c2c46ca01000400500014181d10115020310b03190700034000d8004503400034004054170320b402d4001400080c1401c100c0025104607039108489070070180c1041e109000c000c0e5a54038070040010743c0c2e5414a140c00c0280c0416040d0447c154000115180c640f510450004c045415158035820640c2c110341e4ac50448c413044e4424400d05000c41e541c004040100c4020200e40b5003c0408141041603107806072000110071144040300c00a02001c0f991905 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 426682455 1250 426681205 426681223
    0x60a0c0c0605071401060e22120e13140708090703080406020601031208090c0f0109030204020705010c0305010e0f010603110c031309051008060121050604030210050a050112021201020c 81
    0x344415403610072500380704465113003240031500c3c644e2600100380040c0001c02c4080f079221030000520300011280c903400c4034681c0c4250100a0610000c020f4401e400c40e04410410b080050075540003c2c418550000c0106946402003102e49d11868500425012131095408a0b8004440403c50312642e80d03954500a1503409a40030310300680021005104015011a03202012491440c1c0f40065042c44128a071f01d0300003007008103200d2140300d0007500e810390080201070020743d0018011500c5841508102d40a0f102c0c620603040003034501000819003200e0041c81a001b90030000c2d40ca20203a080c1041540103181c0c4503c5512071880c10b101032180114100001c08a83c4544140545081d1a26110308165400548195296030741c0b2038041c0540d080006e840c0781101c61455020645000e44160194042441360010f4881e000d22401c00081c140c0019100d10044d1007101d040045030b8441044800701c50081c00384861034aa4405250301504c1c000c000000b8420544000500e001d4100902615000200c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 426683705 1250 426682455 426682457
    0x4270905070b0c240609251d0103050f0a0209151c0b01091a0f0403080a020f060f0114040209040b060a270812030a06081227030606060a0c0c06 63
    0xf40031070822810300c2075411022200301604c01d9400440d2074071030b81c00e4009107014040d4444500064011198000014a000e091120b072444141507190051030035103680210061184002c03903845055102c1c3c89828491203448401500548034111420060b51125000540c030241c0482c8203203da0100000802507280c0c1030720804081050b2080d58401e0b506501c048606000c00420708028040829801c0c4000847c02503209036034604c0c2132051141d0f030080e908054014480801c403501c000c2c1d0002031394144100820200c8900d41c2e1390003810100721400f4000c0d4145c01c400007040c0c540c9030806802510400310010000304040142d2004168035030004902000010401265045100c401c112007840f100703045545040305a091501c161b40c2c5400c030300004100303400c000001505803406a4403242c05000d100301500e0702c01c503c14046401540180c204004119142207040d03000a00064168040d610098042c0450307640b0f150411840c0d03003100b168241444031543c450340020701c841000350081d0280d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 426684955 1250 426683705 426683707
    0x1003020403050f0609250305100623030d0806012606120c0f0d0c0306021801080109150509060415080703050607081312030f05090a140304270905070b 66
    0x780d070421074641100402c0500c40c0c0d4215105100c0c0080d0041145c140030406032282c2e070340c0110119510420300c01294006400d03809601098030340a0a203401600072108258086143e0b0b614000c00400b0004000001c50b43c19031141c00c203444210300602200e90310400c1414031100c0c050150b00340040f115010340b01031500301c5080e001c01820b494002840581c042c0007400610000305d030340012802c0158208840c62040e45050549800c001d0141582400b95038003040c01d6481c3d070780c88209400d0105901c01440c2c040ba0900c030002c40c00c100b9600c15488840d80e1a4031441c1040d241100703101d02c409025050540040e200c11801d01803005c1c103407600005040641c01000164034500307155040c503030082c111400304a030781e60501031206081f44c1e10351101c9802203241003644000c070409034001c002c1602840c1030241400c2c01c05c210800c000c20401e045a0140d000b8980005001d496680c4900c501e01030040e0703078000079140e80c22401461195421170034120500080b1142d0a480e070a14042043e0b0040e04a140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 426686205 1250 426684955 426684959
    0x1210903020c1005070209040b0a0914030306010207060e060d0f020412080309070501111e0114072609030f0f0706060308070606050402161b210311030909160c0210030204 75
    0xc050040445030105440e04c0d6052130800d40c00102c00c06805800600130402c090041030541e2016401550304991104001c0d180130050700c03859443e07400840c1c80074054050b0100000c2c0b854080d84c0d000d0014a0f00403e80d502d001040b69009006140c5030b070039100307015428840880d602005a411183c11801144282d4a038078001510610f041081e030030081c100000300031402d41d030000000e030b551b1041d8a2544140b2510703101c0034010340107002001d03c003a211140741080c41456504241c2034620104645298810286c1a10041400e1202500c485a240d4401c0040d0051000c5010103402a2401c081c902480c24030b007915007905440042c0c005942281c1e0005028007086010303c2250000c100a4a0642c1820102400c038034403083c0f100000340950b85d0700d2030380d84200740b4004107032005052a1010030344140000c20f000f581040c4910000c070040342c0790540380c510303803c400030584d416010020702c1c2000c01d6544000d05580202d0070145c400503c661401040010390b170307801000380140300315580181c03594 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 426687455 1250 426686205 426686209
    0xe040b04050f06130519240b040609061d04120c0f0204050405070e090c0604210b0711120910140403080408011b0813030e060d0603050a1109130201210903020c 70
    0x1180101054018015101e000b50000d00d0341d20611714112510310711447c80703003031000102014010344c507105580a0300e810b5000c81e0002070341e40f040c410f4401610f41e44081120500c088014541e003510050309014007102c2c115502c40c410403000141501c03c4480580d060807541c0424103850090381c0407a540d0700000018000e85070703015812a84015134400070800c440c2044041250b5200e10f0140c5084141d51003016a42140041c011001c081d500214480052800e6034000340340d8511480c10b060240955101c1c12600d900a8082d11500781d4001c200300d860901d0000161503c00b002d50711132800c050207000010108101d4000341000f807401c20008166420049607580c110f08c500b0445001b801100c0d401d0010708500c803003140000d80e9040c20b00000c0280e0882c0040d50f140202c00410409605040c40407080280c003003201040940714005a00640c10407404014100c0800c03146440c0a5001132980750141d03200d030050118120840c482454110015510007080c0d4a6441d02079025a22488001e40b242c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 426688705 1250 426687455 426687463
    0x9080c0102040314070303170c0c0a05100b0409241d1506010503010b0a0309170d14092e0213030b0402131a041112071d0a0e040b04050f061305 63
    0x1141d84c201405044d400c2d41d401a0021400c2c0102c00c0384001c075400000e82084003a0225440c0504450484002c82ea43c0d281482d5624407c041c8100858100100305490381030500074840a00e9102c40101c401139000c4182c14140320a0500c4800b0340c4c1c0d255021900c48001514001184030b0001c00a03180d292501d13050b60400c0000a00090b04112080004000300c0b21202c05a5880b00c1780ba1801281010300ba003404049008158555142f00740000381030401812254455221891341468202e9a0fa407242d01803038503a404901200000c6802c24010030381540400f18000c040701342080010b09000d00c83c3c03800018000c01c0d07001150715500c220144804c0d850031b0b40c100e03212040035540a0084001d29807000c070341c0b0720126144500940c1c8480c2c1a5a080a20500b034840c1d000102102c00310920700718034010084a80c0b5001c60305134030000000b1160714100401d0715420b0300d0340d100018029841d5540da00c40d6400d4024015201d90181e11801d44040005002150160504c03d00d40c3d591040340741001810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 426689955 1250 426688705 426688733
    0x60906092d08090d0309051315090603020f010f0c080714010b0301051b0f073302070809131523031903081b03190e01050417090409080c01020403 64
    0x1040114486001506210850342c1d2000150340082e69011941707002d6503505c4a603040b81e03900080c0040071204501c180e5024068840e501803502e03c00b9586d03001460300700c410034040a504076011100c5c444165008201c0d000150909152010042645480f190402c0d041480215005030b142104a62005803d0081c10240e00048000304058102283d00e1540c54020754480fa1594401082c0b40c8034091600080c1c80f1101e403c1481e8015092810300150b44c9850740320300c40c1b010340903c81c1c0203040c04021f601c00c0e13600b40d0382c0c421011843c2c841001f08024100060000d0241041e49030b1400501819803404508010504800390341801810b9040f00d42078110401d00050003540070100c845a860004014030703500315010b01704903000780c03034404c000c00c40885801c94500c9416000014800c550016580c442541800320004100c0058180c420600b61242501d0140c009071131402a508010b4402004244c130400007400002e0400855440d001c0307680100b90304d40d20310795000c0340030420f115644c2c0356161 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 426691205 1250 426689955 426690023
    0x301050a0e1014060d05090c03070e040c0e0a0902030d090501030509150f060a03020909061b0406020a0212100c08150a050108070513030f12021608030d050406090609 73
    0x10078035080440807801c0c40701e8810110443d00022422080d52101800c031845076400c41ca050010303141c014065a51081c411049a00a12554000144141081d406203005030361101900c000186480c810300e1041502a00c40851039039250f40860059900f00b14641a20156480d02c0c04043e140000250485000400e0390b825600480341c034440b028040e0000c94bd12071581c1080112503110200400d4000402e40c0000b50481504014400d01d035000107442441003000c00140340c0c014003403d80c4203003980200d100b0400540d000e100c0c007400501d0a00f10035810004071404488942c120340003a101070f40c02a441c842d0120346a401881111260031100e0044961f06890400c010307440c0c00c000808000008144408004003c05c0360741d900d20903001d00317000840c0c2027084501039107481d0074240b074071800110040025208141031114001c2c99521410102c803818405142032400304c001d118050b01d8000c00490b083c80d41c940c215400103415203e4541101d02840c6903040c4007440b114604080343d21244199 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 426692455 1250 426691205 426691229
    0x50a0c0312061d060609011b0f0212030403120207030b060909010f1a030c091509130b04062309070b13170d0f0507020604090b0f09070e0a0e06150901120f020301050a 73
    0x4c000c80c0d8011490120f031480243d000308d0340301081c1c1040300302450400c01c002e41c4000b0466408402100c000040c0c41581d010380e81000c03500081400680e82c908440c0703c02049800c541d00025140d141a4038800c5c0e020342008004280405142d80c43e034111014815007268200302c10301240c1c60b50804010400902d10185d4105c1c03940d0800d215002550041c2c0c141d210312903090a0001403880c0c05181e0300030242540003040d0482801c3ca031034160007401b2014101c2e90b401c48000d42c840030f04c4040d40034441c0101c2d2500041e200c3c0b1030074000c1c19140350307200c1c405026401400f03580010320a450126aa82180c6600000d840d00500f0108010010050325489204210b001d002d0031000d0303903e40007154100d928807600010003d510102140c5580095070089a001140100704800a130b00640d20704043c00c0e0403038000d0400358035030781d00804951007a03545607000380c003408074040300b142e81d440148401c9105061012024850412400c156054400103003081c0d500400100b00c5401c0009144020b000340045a03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 426693705 1250 426692455 426692467
    0x11401061b170c07180501090f050402180619030c05041d060c0d0b030d0c0b0a020c1f09020a0305010e160605162f120c01050a0c0312061d0606 63
    0xc0d2201460542502e210a00c006810002c10f0b404100c408018001d0408620b801c1011062150040c2000d1003005092070401407050740814841c400ea0384907d600504802034413601c00310714040303400c00800d103980081100f1030390204071285d07000b0000114072510342d181d4211f040009200550b414030f030805c5c203403047d4450389400c044c6011550a600c6143d041806460700c0108842801501500c01c078035800d402250701818425074000311291015009013102c002540700d07419990304034803c015070f0460f642c0241e6013000d1070803808840700b2049119910080b4a444a41d000210341440507802150030303070764800030082c40380028418090f03507021030032009200e18135007a40542680305a01010405200d2034100400b081900f8a642654060802e444100302d840c4011882c0b05c8000384e840244283d0b009030401e0f800203c0018590106c01060399903504020240e001030700c0f40c1000241c11001c0c020a0045446085402e100e520028907800c1c81003250317003c0e94455071103140c1c4040c0c21603005003010001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 426694955 1250 426693705 426693713
    0x1701020403030f14120112050c0a080a11040207051207030305061507030302030a0e0d020a050c060301061403040f0b0f04030e090417090303040f060503040302060a0e07091d011401061b 81
    0x140f0400c49910300f4007402e41102101c0e01d104912800c00110030321a03106001250101940ca48014594840d50880b6080100e5004000c0c850362248a034a489510104007000000c00c2c401104942c91030141001d41000c02a43d66a800d0510889038481c41c10070101e145800d05506004241c1c12440a8949000504a64400400c144100b02000d414150004003040c680008e40c0d1100f88080105d205a4141038180107000b511800488415142ca1051503038040042c81e151045a04840550300c0700d04500740f21304422806504002d1098840c0c1074200402c034003080b1929003003131203131134035041840c6c480c176151030064660350301200c0e030500600c201c0b0b00b0080003500c10701c2d014405407461100070340c03283d42c4000081d02c0d603c1141c0140558051000c000651075070850050f6000724405d07003d4403816035446010710200e07281e00c85008030030b5101c0d00303040040c4060307984158455100e101190710190703e201d07151800e4480403d28021001b0076080100300c1c0c036034000090803184001ca0440a4041403a4a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 426696205 1250 426694955 426694967
    0x1050906060f0d060f05040c030506060306010309150203011d09010902090a051314011a01050c0d05031b160209070f0c06240305010b01080711190804050301060b04170102040303 78
    0x100d000c1c060900041d8a09296080d40150748180c081c01205000c41e589801c08802824001c0c441e15000340d042002c18000d19001e4010b50b82b0410000d07080f1802c45d0b030f510004402418202000ba104e41d00380380740c00b0b0340c0901c460000714003074600f418401c1180102204c40d500300020013440d00540764500602c040c010ba036080d100c282c0141009402207416102c40000b0010340b4000341d0020b00501821515070080603043d04030121000041ca01345031200320640054480d0b114a8400c0202500404014114540140e01035504080d10311303d130305059040400c4082c625805054880e00c00726052402e0802c41c035000241da903003c803841c0f900c0a900c201c8100c000d003c40001c0800181190f80740d003400c05c1c680e0f24034a100000e1446031050a044641c2c0c900b801d5000b40450206107000913605c200040d0950b010304101405554407000408021030442c0088039882d1040104a41c01c540412002440355400d014038409001c510700d0071955189010045407071000c4600c807000859006000402c0440c4d0400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 426697455 1250 426696205 426696211
    0x28060302090f011b030e1f27180c090504061707141e0d0b0403120c08040209040308092d1e060f04081315112e020409020304030c1a010509 61
    0x70030f0460f00d000a52000070100150300002d8086007245040c00d03910141d00071230402402d01c03864800c0350740744540e44c850313a8009507900075800222058460140c001445500070300c0840f101c0c1c90401031854aa40024050b60066072125aa000101c60414041441406200010a90180d2088650341c1c80c2d404540350b000055000244102c00340703009c03015a11400101120194030202c0708009240502e006008450b00f02c20f1500c0d42450140c1c082c4000e03015a0780b40e4081c0d60000d0550b00c1940e150303030b001c5404200040c90030300c290081108907246034940c000000d2160091a0108035039031900348a05152000c0c4030308041d00040c030410000c00004000c10f605810218801c201c0f5896a118249201684a440d440303882e8144422030015002d4000c030000340e140f003a1030b41c403039a020445184850351200c841c4618041c040b5107040300c81c4e00d1a850107002007000c01e405005030a0640c1c2d03900103c00c80e001100c043e0302050b5106240c90412508110880c01c1380302005c2590015410302001c902c01c96001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 426698705 1250 426697455 426697457
    0xd0f0807110c0d0602040f06020304081203090115030503030109110414010c2405040b1510030b15070c0528050f0a03051b01031b020a0228060302090f011b03 69
    0x240e00803080750902c0b4006041901400c0203880c106246040d40083d44644580b01c13160300c1035180400c1440c8044211011584c550004102c82c5202c144402555440500a00e1080d0f58400e010788604010f1705071f0340021801800910744940c5440c042d030040d10040d60140c07039000e00800003484031103020002c000c0350340e4081c0b0782510800010310f4040755450080d40c0480c21441c0c0f4000c18540d40001781c115600c04c5102e2840c0105584403412420320029140c0d00d09580010a0210040010300c241d0000115040040c9074028035000ca11400d606a4081182558004030881c0306104a081a105204400c2d25190380861001940381051300c0380d2040d405880d01c909510b402c0c42d003590b03440b41950f40146810006903032801e54802e03420740d03440d4040404503002c82d0500028502040419680f155440c40e544c02070502541c4650806c880001d048001c51500e00140d081c1e18200d4a14070078100281055490042e66441020100005099038421043c100100b03d08954403400300040118021641 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 426699955 1250 426698705 426698717
    0x1401020618120c07060909020f07060c0504120602071a01050901062708030a020705120d1101090b0702070806100f0e0403020f010203100f08010204150f020a02091501020d0f0807 78
    0x15621150308050000c0e240a0341203402289400f03030700002088031400c441d2103403030b070a071215540c1802c807050f805400b00b8842585401d01c9808040385d0aa084000d038141217260131494542c0328142c2c0081602044d1007602e20780c0d0b000ca801020032080003125012080f01d041a0b101c1ca6140c200040c10107941405100e00b0065a8002041c1c90107140c0c05109a004a07044082c0c1030360346801d442907480d00000000c000511940340c00007002d0804040c0c1071104909807002e003605441042c0d00b41e0355030040501419096594035120000b00e0795500074240244180c1c1d002e0103829180610301440d208020f84120040041c51382c0030044d1481401000041311002402c1c00d0242c0d82e1030505a0415044016429941d4000010003011401070f08401c4d058603a5444d0760192251205c084a08030b0081d0f00510394071507145104d5900c00790192104170b40320441841210059011580030880000c002e80f442c00074221820340e400002e60701170000d00d04c118034070316042d4005450820000e00b0082c4c00341c610700601c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 426701205 1250 426699955 426699991
    0x80c0603062805060a030c021e12090a030605040c0611120904320a0f02070503040501030504210201020a11150c090307030503030123180103020f0a03020d030c0c14010206 75
    0x600340340e41009003401414142c417084900800303405402c0e502e405400501031012a0f8080c10280d6490341e0713500000200410080d01107210280103a4010409940e1003200c00c3c00000020320a07000740c3e4440d903c2004014162307413500201802d100e4082d8060100c64003c03051071540030b0304d0601543c00c180030844005c00d160004520901c8842038441500841d81c400100340049030b03144005003809010804410003e03421a90400800c0780902c0c60000d000f0b82040104010640c42500026003003409011482e060302d40d01c0100c00301c0303912244502d0001d41d401103003540c03007076070802681084080140054003250703020264180203440020241283c607a80882e6900c1e072500e0802404010b035a0000032640c0e01d503110010311413900030030421030a880d400312075025610704021464129041121480020341d03400c40c0d00300100510040020f41d081106a2800000750380c3c0e9020040405019880304203d0f00003c2c14080c02040700f5401200c000700b0604100c030417a9a0006040e64400c09812034503111302 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 426702455 1250 426701205 426701269
    0xc090e031e03070306030206070b0709140604090c0e0612010f050f130e01020c0318030f03040617130c1d01210215040816090c0f080109020901020f0610080c060306 72
    0x203e86c0000e134100202140e000204010004040e002d8012522540c04144c1d441c0101c51800c40c051034502d0b04043d062000f00070350040c0c1c0e049103d0b060f1460805011300341e850000703d12650088180c901110224070010000c0c1d1504030880c40142900783d460081011410001c100214078070728030160129a640c0174a80184029816100c1d880b0078581a01e81d600340e02e0a00c2000c1502440c01d861007801040e92411100e0000401c0707038211001e40c4c441c0c5640320400780c00c607100440007d190041b88c4024a03941c90010360304110500251a415030458100155804001000303801600003040c0c021b0b800d024000700f0010032299582465040319510300020800c440c0352490302603944484101c2c46100003a0600741403000001c0b0550b50102c80c00c0240c041015400c4654540c0e40883c080494a5000103001d4140385400508600304180102c6042c40341e0603c100786461001c40f00c0030700403040c1d510b050080000601142800c00c00071a112411410200000b070040048a81900c40071843d1001060200e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 426703705 1250 426702455 426702461
    0x60507020d0f1b03020301060503061608090f120a02100911040209010302071712090115120203010212010e0a0e0601030c17100e01051518010b0f0c0a0c090e031e030703 74
    0x101d5072140c240d910030f0004694900494040d07000407071084d424440080791a044c000345580c4034482841c1e062110110088040c2c070071000c0a020150580141c41d400d000c6100e04028952080c5000ca0850355148048407009040c01c00c5041103050b0b250800f40a00003042441e0042142d0356012100145d94015050058000348a01040100f408181e40203040081981502401c41112045541c110955613400035038200c90703c1c10308124042d51070b02d40c04e0040f0203041d0b0b800e0b114030b44007400041c5081e240d40e00074050510242e00030740200421104225041e4110f0054103d802940381c01081594115030b1103045280d10303800348603240340d40c44d00d958003038140c1000000380040070703001e0800414004400395400f0303010880c2c201d400800b03880c0b014843e40c10090915040405622480402ca07402e00f6440e0039a60b002843c03c0120700803e1120158255003400700060441c03081c4203856840d481d041c00d070010b0710003503100a441500140100e6054050090303041000640c0322240ba83d80c5c1d40e803050b040e401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 426704955 1250 426703705 426703733
    0xe0108101419080109020103050f1e06060d020705010504030906050a0512070504034b0f0c080d0c02091b0318030d050a0b041401080c21030a08040c080304060507020d 73
    0x64100d15030300003c0e8404103502410303955000f81c0e02032000f1f07611041c40f03001c4000d0503104203468103189030309034544000800d0b80c1e0b034000a00600c2c2030310700300101c071100090341c00000c01a6410f944d00c1007032004054001401c00c0040242c0c0c1032203400c21078407940c068064020b001160410019000010300100d100b03c0840c1c000d0341e0300c0118040b913802d002c04807420700441c551090340c0300d51403241ca490700d00040002d6900701100c2034400034150381c0c06545071b0040300114041114191100000800e02e80070600c0000f92440c4240d075006e4462000340100304001c54080c20052101081c240b036041c041e03125104680d44442111524846800c00080703085c80e622400510410030340c0740c0414444c500b41ca42e000030341c074803600700c40512550b4410507451102d1042813241c4041340d4003544007440a410044903001c005031018100c50074084038410310505585c04402003e0014120504020030006000303502405003180400440c140f40c241400980703030344500c901c040d2140b43c600780b4000070048042c0361811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 426706205 1250 426704955 426704989
    0xe0d0f1401020f0d0f0b0a141906020f1c0e06030403120c030516080126010612030e1c030804141c02070603060801090c03020d0309240e01081014 64
    0x1660f2995118440c0f240d411089800c4042424001c0d044c07100c101902548200c03c00c01000c03501c030030345840344d41404100e004194a80000b500b9220504541050484a0003048280c02030000c0c485124401410b216500d40c00d00321450f48013910b5060241e0000c541d8000030019100c10303039240c540b410b007602c030403840412403c00103052a031310300340d6140d1541104d800340004444698a80040701402c1d6052070090150b8001340c088103030b008800d408040a0041008000d5000054258035401100c11005d6410025030100f100d901c440d000ca410038042c5d50140711640003003001c0024960760010409203002d040034101000b01400343ca134906040c0703c40f48146514801d191120450840e0203501e501c1d0700e2080360046032911000142080c412b0151400c020b84c885001c4011900715800c0102d05c1c00030350401d0b410440300080204004010a030f0f00100150f40d00c0049203030b00c85042006040302d07040b0b440c3c0c45c10004c540c018002e2901c024145201500d2030701c00001c01c040c80003808510300b8007010b03402e58 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 426707455 1250 426706205 426706207
    0x50a060e0c011e02060609060103020f03010b0915030403050f07080c0f070512010608030f0c03250605070309030e01300213060c02060a03050c0403080d0209100e0d0f140102 76
    0x20340581000440020a210030f0302c0d0340a00c40030070a0100b06007648140f5440150b040000000c06a01d0f2400140d0b80c0940d0504006080c06c07440740d582d110641090704880c02e1440300180d0640c441c5441c0d69a0307401d6203145502103180d413901da0ba005085008000115898201c0451484200014013055403d04a00c0c80100c03400130044205c0c0f9651010340d1310400f8003c43c2400002078445c40107004420590f03403600011850414244184069507015961f901c1c1140801d20114044801c6008000141c401800030440c0841c01ca042c0002140c002030241020305150801480c006500a031544041640c01d00f8142842031380072948541d0b542039617800b2a0700c40203005248020b082580e0250903048202e1b900020110f07221141500c20140c1c210b000380d030200301804040d503900e100390480c0d80c1c040841d0210320304040d0350b5030714510141c000820b070000c1c030780c0c020846028609040740c80c6031601a00e4940070400003503d0b80411013020051b0005400d03181982d0441c0c041c0404000790300c0020345c11900031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 426708705 1250 426707455 426707471
    0x90602040314061506130605030402033f04151b0b010b0703081b03010513150b180406051c050102070f05060412050906250c1e0b160f050a06 62
    0x2d5212a4112030400e201d150050003040c10b070a101058449541d5540d9100c0081402c0400a90f180c0d0001401240d1500c210000400203031f0140508000505942d6030300c2403d0b01800c070400301120042d0291102c03010080c0420003840701c800e8604510103400d070500d14182240000440400c4520304000350003550b281c0000520074001000901d2981d004e0f903110728564590070030703001c0e030034101e50360000c030954050006024074940f202c5e100101c0c0100e00310009213089144040b842c911410380c031070a0b00c03501c046035240d46070314070026040b03a810082340c04101241c20b2500142030005002a00384242c1009050103003041804d40c112494150042d6284901841c01d140c096a10a012201140d465000044049078240510301fa51342d04040181124100038114243d00070303191a40f0b5448840034150841c802c089207440c40000060525607140c10351042c03684c10340c0840540168858402e01d00b04101b64126007240e0507800c403030140e0240111020025505241340703805840140500362503e01021 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 426709955 1250 426708705 426708743
    0x1a0103110c061009110906030105040c050706091505010603050f01153b030a0503030a0515090f0108010b03030a020703080a0509060f181c02090606270a0f030f03030906020403 77
    0x1662003100c900000170300c0801001c0100c486603006108a981d0030113401d000620086c0707415000b0140e88541440c099041252940302c00040e06d030a0321050b20600620f600c1c90b8400f2009009140c00b501c05c0c1e080900050600400307841d01d074401480342240c482541c4000d404140d2113100c0c0000100c546104440103060081c0c0c1900d101c1e010705011541c03039079405c0c1c00b64407036040c042000300005800001450559443c8401702d409404010011541c658500300103490380d65440014500486880244196560400540f076084404c00c580b541e100754024010f0400e681d42c0000c800f001d4990141800d6111081d414080d522401040e400d20b6004cc40480d0010381c13056520060034084601070548507849460310300740510b25466041d00342c00311152620742d0025050481000740c2140c000b07000c80b8034141c070a40c056800303000e91745010701c550503c040c0c450000d8540b6075458006008840c42200499182d980d41108444141c00001c00b8507803541c1100083c002941e042c1c40003990001481c550111035010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 426711205 1250 426709955 426709981
    0x111306090b03100504080a05030a09060204090f06080c1315090903020d0215070503010e190e030d110a0c0b0a090f080d15050919110a02150106031a0103110c06 70
    0x2500034000c0c0300c1c0c015a11800001e90085901171070f08060000d1410400c200c04444643c0010b10386403604c0e80315100302c0000b031640d00c000e01c0201201440042c1c14203101f0040c009495480c0e000c20415445000e400c811507031407100c82a00c5002000300010104444030f81001c018040d03074441c009031071414080c4000d1580218591905244c15030a480d50150240030703403550380f00d081d09d140000600601c01403142420004103140c0010401003290002100b07689844203031082d0424117030700f540012980080c091002d0041c480c01c48429008181041d10f4080001c00300b03489000064034040700030700807948410b016400a52125001b102c02e04441c00c1d18140400c1c149d20050440d07100707070b20344680c41151076030359075884080c0c5100030040b10081d110058014a61900610044182c2d41d03076000305200c688132030000f060a00c5180d000f070030501d00da030324048540b1719050744980145070801040c001150b542200ea50030425003402c0c006194000d880c020500d40c000c20030303844040d20a4400780714000130a82 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 426712455 1250 426711205 426711221
    0x60e04020a0e190209010203070606030305190908060604150e04080403031403090d030e0309090405100e12070201081b0c0606120106031707080c1005041a010e0411130609 75
    0x1852040119658882c015006007040783d6001c820f00c3ca00041c10203403007070f0340c000b420000070501c107d0f404c0031256203070340e401c40c0c00c035500c201d001c5903002070310840c0d0b074041190011020040341800d00426250000d0140c80d1007005181e84d2003560344646c14180c921074a03144d08040c0c2110911000d840c42c040c609524107030710a01080d40803607849180c0d0000549101c04491060841402500540600241c00c1d8041d00c00fa0b1980c403030b680000e21030070300f035900d50740d0301544a039004000425910300302101110031620042c4401e4420380048950f039500580c0181290642582841c03d010b080c0d0340d0382c018205900d8569070301001443c000035807501c8c20340009000b0707004e0f07136040b901e900ea0a20342ca25000c0c01c076503da12005108000c4d84c03a4400b500c48000010708034490003944a030b07140040085916041c8142c40703030341180560b5144244802d00941c0030307648a1400c08290700ca0100e50524030075091420300140010403845207282d000e0390300d80b124802003c44551020082c418281c9aa00c04070140542c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 426713705 1250 426712455 426712459
    0x6022803050702060f040f0212100c090e0f1b0307120f0e2e02090307051801080601090515130e060732160507080703060b0909070e0105040207110301060e0402 70
    0x403c000c101c05c079030070400103130050354131100f450406425a420f00421b509500203180b414019910302c0d110070400b40c0035640c07203c6030b1560b95028090601c0136603004032401400c40703441030300c05008104000c1c08204c0700303604007485c0c1c01303c2680302c0d0380e07061003259074100903800840380e81c0c2000075000c1405002e411071403484815030300742c40c400c065200e2004c02d0762071404180000c0712290350710210043c02e20380c024441c6e04005030544000e0f940300c00c08507090011143d0300d82101d10880004010340302080c44458050818404148010300f000101502200e07410b00040d8401d06225241400c0068940c0c485009045d0110682c2c80d549003182c400b8007203d40e4800c1c0c203101d29240400800000003400c00c42450314420021190420001c8160b90320304600300038040b41d0342e02c124840803640100c00c0000c400210b203c0c0801142e0012003c0522403d854081c180013040d07484030106004d01d0100c0d40c0042e06448007513400503141c01d8541000311641c1404212903400d03501e001c1c80403c44803150b0010038812402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 426714955 1250 426713705 426713713
    0x1e080702130b03101a09100612060b0906030603010b0909030a0f11030301121401050124231c0908070b070c0506041b031a070e060906030406022803050702 68
    0x107040280c0040c0d4034002941a415007024100c070907420600d610400002600d002c2c00d045142021010a07000c40042c0d0399255122200303c41044070651042e80346980310074502c0240025407505000e40c086004451b01c0c41c0c0300e9a8080b0014040b07803800d46c4051401d220092000700d090078050a50307604c075400303405070400048400703212080d403902a4102da4882e56148004619503840e00a140840d8403807000e080307500c2c0100c4004040b0419090280da17029120403800d0500c0600b56400403c0080980d1100d0001d0010408407520300d503589041000030742d103405040c6a903c21482d64000d07546c00c041c01503034002520700121102841400e2002c1c2c03191521940000510f0f80700c1c03120a030340c105060000188240d010500040000d68449110303502000504003c5440c04d03204d54411112101150b2180c0405090f4010041002d0703002010180c010426038403d45000301050101d04144402040500b000c0d40004101a00d2982004492070000720300c0b241da00f14400c080b100a02902041d40c2d12001882 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 426716205 1250 426714955 426714979
    0xc0e0907170718090b0f03030a020706030b0a03020603180f0f0106091103010b250c0602010509060c04081011040902040602030d0b0301110a0f0903060608031201170705010c1e080702 80
    0x20007203c60845110703038070040b030442c145040040b41c0508042000c2079042045046100003540f410005040d1104460300030709021405c1000041c21215110a9075120b0601c0050030405030311080212600a44181c1071603d50b0600c02c05c16918107280e045c400045c5200c3c80c03081d0078070b0b11411341c405419192014014000a6501c200300c40c800d0000380038a0541401c104004010740da015141503580080501c0090350901e1151589a0914043e03440000980d443c1d004121450300d00f4000d882d40309170450034680c00c107800c0c4030005030b80d030040c02001d2004c81d903201c9810395a0380012041e240141042d09095507910b844090094a981055141c1e510407030a040750800c03075103818014051440d012645c003034180b0300d8040040380c20611110504050105045010005c2a2540075100c09001500300841d07035101d0124015540e8141640031042a01c0107549040071f088010418000301c0d02c09107800701102d4145e06045200d0890030030200c80c685210400041003158410142000710700844014100302 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 426717455 1250 426716205 426716207
    0x11030a021201090903050415020c13090b0f101e0b070614090a0206030601030b010302090316080d0302120f0403140d06090b030f1528020705010b03120d0c0e09071707 73
    0x113005420041c0461010301c0188030040c070000f111b1032140d10034030450f07008440c030300b0103d0000a0002a0380030001e442c0c18907802800700a0704a82e40260294014074100c0c60001c02c94a003084d218042c0c0544071014118440100700d82850f03600c040c200c0321100c95038810051603e20f0003000440d01d502c42082001c800504082e6003c41d0000d45281c01030030b400d2079030f5642030044000b410b4000346141417540c03d0180003c2c588041142581010441f1145081c040c203007000903181400d194065020140100841101c1d20181d254454210386400400c01d0140c4941c0b6054481c10031000070340c0c0e0303280780100e010781c0710f40000d80007503080320082c840800904d040e00e0245500c0d0380d180e42c8007128980c40811004100e85501880ca40d008409007050b0010f40d8400c2940c2c01502070802d094540f254020414905120082c03142c003459a00850062041c4181000d1a0707803e4002c840e0141803069540744071201d00e50060707800c442840401440c96190380780c2004040c06a0f004202c003609110380400024680d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 426718705 1250 426717455 426717461
    0x903070b3d0905130f030306080c1516020d05030a1817060f06030f010207030e0f0603010e040b0a06030b0c0d110f1b070510050309010f020315010507020411030a02120109 75
    0x540e80081141d10460601e0390000c05031070007420f0b5598030b0000c0d25280002c501051110f0003614420707640858968a0300c541c607403400b203815444903c507500c60b195010b947c0b0352020403201c1c0458207181c00c00710304174580001840d0b40780703000000d802400009002d01803285e01900d024014490403486c0d0060980310107000e50b0714100816078000311b500a1001c601a240c020b02c4c0c00b80c1c030600080c2107808814400e82c200e4223a030010803048002c6445130010100c14607102c46404e20040042d10360908542c036240c0701441c100009440506100c10140118514603299009071002e0340d0407400c4c01c441810180d41410242d1301018026070325070b107007003a02d108480700b580448040f00d03628540c0b50b0400c90028007846c00307240c003211221414810300000140c0b540b1642c04401d4034803100c1c0ca07083e88901c1c11000031400d5904500309001450b2041080102c07103050000d8071003819034280b80140d00e901c102d101082c014000d482c04007410b203070b01004002c41d40849400808489060b40207501c4a642d8400f405415 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 426719955 1250 426718705 426718801
    0x30a020a150f020102130311030f0d0f14090901120327030302010f0605090610030906110415110a0611090a030501050a141b2a030d1109010c0206030903070b 69
    0x1d854451010408590609002e60388c02000070f0640f0103d0305254001c078a01704180c1c00c0c9001103a02d07090300b07982c0150005105100d0345452030f901c40c5860a41000200100414004c2e042181c2551030008203140c0b1446090640c80382010160304042c1062710803c000411900c0114010341c00c200040742c03407406034011807044a4002d03080d001035031a10b800f0004070182c95803400c01010355030600000454401e00610300c00c40f903042c480310b40e19030602e000805211904050704041c030980e000f100415510002d1b80e241025009480014505c003500118800f500c182c0e01d0081d40000d0001002c414094117503c010300566555004000f14100c82c403095102610480300e024480c0c100d051012014110300c00100500e0f20002d1603030290225603280e100e0040c4035160030101c150320100781607041500c54840c007209900200300b100c1c24000208002094002c070484024021440400440c91100d010403ea6909540c802400141484d0618502c048c0300d80030307000c0240900c405082d402e62469000c0011007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 426721205 1250 426719955 426719977
    0x9030606011d0622080d020309010c0c1805010906080c06190203042c0106050f1b0309030d05130f0605070602070507120b040b06011d0f030a020a150f020102 69
    0x84159510001911040010344039412148004803004055980b04801440f2050f1900c2c5180b0404070004513810140ca450703000310803075500c19801212100d800000703407402014240f80c0554010340b1071514070100001a480404942d00c0c0c90040040c01c00b1a8018170f040e681014403c014441d0303200507459171b4451079000c240c0c20640c2089035400e03509034803145015600c9140100d0745010b039075074106404032501868048034071b00031951300c4514400d1040864010701d0145042414103503606294400ca100b52404001c1008072420106400c0c01c1c00d0050310741400009003500c030b082800280c003410990120009415403880b4560100385582c800031010142d8005035110341c240001651020000c0d07106401c256464480e400c80001d00c0c500d514100071400d440354405118a007014940844403000280415040c00b0b803003d80c081c525229041d414452100842d041c048820b411408a4107111314403c003c1c0d00440c2039600401c2c00b540c4592540150260341c0c3e507281a0409103a0224204d01900400c0070b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 426722455 1250 426721205 426721213
    0x10e01050f0f070807030804110102161701091e060b0a0605040b0d0f0204030819030902010e0d060e2512020a0308070812070306050102070e011a0f040b0c100f020903 73
    0x7210307407410700c000303407001031600c058072460005a40c0380e4480e1600403a00c1180091174100803c010001d0a94030030304103100c28002002d0501c450b1041c500e03c481907000c0c13043c1803d903900d40110b4480d02508140251f030b4005048010f2035138031074255540a00303112015182c2c036051070300b50381d0b490a104041070100c40250391142d090a060160510040d8071541d444c400054951001c0c07407440146100810065104100c0190340310b103039003e807940081207000e80c00181f61500740304001603600400e603085201c400316000d10000b145032030042c00070107170083d194500e4407030f036943c619090082180d01c070358241d4120085481a41c1d901102001d9511040000350404030881c8208005080e080240040701e114441d1541480e42e50f03100300f18200011101640000e440c2d00d010025940c040c0304a801038030000100344910340c14a201c01412501001114000c0d01000034100450340080c2c040e10003400449003025910070040e14100d9540400758803440c0107a00e070450f842500c0e0b84d00e2013100c082c010050701030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 426723705 1250 426722455 426722467
    0xb1f0b0304050c09070207030803010e0103020f0402070f0201031e050903030f10060f12091a180a0305070b0702010b1206010e22030311160501060e1518100b03040b070806010e0105 79
    0x4c00304000c006400751066205450000c00003c640501860180c402400103019a602d54010041c40c1f6002020701c9000d1881041504013180484c2c080110058080c01c0204000c1c8a041c000d850400c04000c4205410b8900030a0181d8070601100a50007801c01d000301d19103548800b04d000d0925100d078030402c1e01090703603078802c0c0c00502e024905000d0f40712900c91001600300b076503855441d022481702030008240f410420801502a42c902e200c5403444480700c006080200f20b682d005001072043c9070002d08484284000640007074800d4000504282010b0b01c00c1003001212024035541c0c0c8020f0242e40303101d640400000d48003501c114516a102101c41c00445c0030010140ca0550041c40c0c0c40d441500d900204000380180004c0320501107440a108800004843d49001180c1c0d0750301c04007520049a062180c488505c0355a20464039042208104841c400c90380c64186c0e40d83c2d48000c0070750054071007400200c10081485002c44103184076140075102c00c0c03003c1d81ca55004540c2c0c48042040540441e0040c88230b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 426724955 1250 426723705 426723709
    0x40b010203090a1a0f0a02030304140705010e0f040e01230106021204060507050f120c06010e040c150903021503091504050615120109060221060a1a070b1f0b0304050c 73
    0x11540c0200544d44c501880c00c00035075450386981d4026018540981d100005100821003070320b0840300710301904005840d595080c00c00003400880001e241c50b206428240032610310f03580b994490b0014440b008001c000440503541000000014104559a1990ba0400014040d030000c80c08400486100e94500d103070504041007038549802c680740580d40c0f48030b41040c003290144204419000c034400350110549501a005102e440d00c2416000140c10450340c805010000348541400e0b401e54003a0a400e650384c401e01202112005280e50029601c00860001a00451100f100442c0980c24460960b81c90103c540d12100c501542a200101280d00490018a003c100f8098481c0d011400914040401080055650964520044c1034940700d50000e43c0076003020640310b081039012031350060060700e4a000000030302c1c1c0d0f013014480c19014030010300d01600352001e9001218006540009810780d5418003040312122441d50f008460350081c08104041809803101040e40d100c0ca5001000f03104944084003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 426726205 1250 426724955 426724979
    0x6080103020d2105030109060603060b03010b0a020313030f11030114041209080f010f05010e01150518060d06081249140a060506071101180e0402040b010203090a 71
    0x40c01e65216040c00155160152143c01050424600d0f40d9010b407254101185841184e43c40c0d4000c105061811508100036000c070000c0c0c0f030450704201c0e0b07001e85401441406030b0441c41480c03c910381000c441d00c0041300301300000d0440000b240c0665030240c0c00da0000c006050032a8a50f451021890b0308040000d4001615100d004422040915229040a5407030036441d1501ca0fa0010840700ba9440e40c3c603142420000b84103039401003d1800310420340d5450480800403940920413014200030300042e0304904084500c2d10044042c0b80030303100380d40c1e98214108040040080c2e02564046000340c0190240d8030182a06448400352005940d46070900e0100c2c1603080075020352402c0c00031301c40b90080082150328030b00c902e640044074400f002c0f580d0030072151a41c242c4a0010900780b43d8500e041402c1c401504d03038100362001d680d4800b4400c0000c003202030060310f00c9219031500c0361008055040200348044ca03094400c0c000c0b072003a84c0500586011300b0041e61203010340c112140d00f0940002007040b030031103120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 426727455 1250 426726205 426726229
    0xa1d130b120d11060601020c06030a2003041101111b09061c0308100b0406090b03090c1c020906040b0f22020406080906060306040b010611100c080714040608010302 72
    0x3020001e030080c0907005a81001c58542c0100d0101c0e801c0c0a11850140c0244000c5601c12030910140c0200450f400020b6940e00018000c40c99060b600e00c400c601d146000d03006441502207036002c803612032406d4031b0b2082000c400c1c0d00f400c5001901c08c2000c0c4403d030030300040c0820304641002c0002c0c0700304211710602001c0000180b10745d5101c070101a00300e00c0908d40e0300411000e140260354401c050b03c3e24610141c00010b440e40440b500c41d070100801c01c040b5034025032403001c0c0c990111820383d8036103c43d5402458020903000d8182e01c0720340d80e20b0800d1021680d01500e00100c2c400d942000c0256108010407044481c11601140c1041150954160324a40003410076103c00e5003d05001c041c4011100d0001280c101d40c00501c007145500060141c07016080203416442102140103161510b4035a0750414000018850101803000031048041d807294203128151100c0d84100341000035451043c1cac0241100c03000c0e9010300110f2103007244040324003c10340440f010342d196529041c44036440d584c284001c0d84184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 426728705 1250 426727455 426727459
    0x314010b0d0902010c1a33010507050c21070b030c0d1806020d050105090a0c121814070e012102130f0905010507030e07030515071707050a1d130b 64
    0xd0340720400006c0031112580e0144071081d804018928004d070419060054010341c50b5280c0310002c035488500810003106040e03800c07082c07a00d02e40318000c52514506c0e2060808840781d0001c4440144022807001e80051a2940f05900032501c80c140d0b1030221654601c0700341c85901c0c0c4900100110300010065070000c04030444401480707aa8041241c6406040ba04843c148481c11621880100150700e0601c6885030041101c0b0410400c8601110003d4070411141002102083d03e03071424018100f421000c59100030341041628905444180e00a038442c10780f802903034540540a0004038801e4844100080c80f02d0f2000414030901e0303c150200001e00c0591030075154655200e17100048282c900f4058809128072900c0007080c1d604010340060199545502c0d1002a43d22102040001c108005070516035170103074200050481c4c880703e10842e10902c15000e002a04903541043c0820b0035800401044845030540c0d6030500304484024071441064003041c51a8048960103020100c944c569000d07091030180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 426729955 1250 426728705 426728717
    0x738011a0d1d0f030901030b040204060503060928060504051513050604090c1e06081e150319051501030305040b09180c090108090a030801150903210314010b0d090201 73
    0xd8004040c541000d00c002c0720440c2e0030114401740c540d60140284420144102c0e0103604040c14a4402806800000c1100e4450722181012401905081d00394034204e0030707500c400501107106458600054001c51040c0c601603840c102c00281c040088007008038020360b008020f90f2108244041c000e0103084040c000c6580030b5600c00300300c00055080750305000100420300b990400d0f400c120303801e078440d180e0950040080c09000000c1110b0942d0300303d900403c621a9141ca00d9407a00c82c010b0b0380c0c10320780c6900900d9405100e81080c124405103421980c943c42c9208104031900804107000c4824829002e100003030108000340020300076000400f02070485000050200c115580007d10030240803401a200301c000001d00007030503011075a111280c0d0b980041054001d048005095400800d40c5c2c00500ca01c2004c91a0920360980d43e40c46040d03510010340c0c000440c0348100c03560441086496600d04d42e000f01091415130541c1c1a0322943e0347e0f06040b1000001101c0c20000d07142861005810062000c07410040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 426731205 1250 426729955 426730001
    0x9091207051507090608070311040b1305060301090504020a090903091401110714010f020102071709060408030c0d0e090403020a110102012904060b03010f0302060738011a0d 76
    0x4502070440d072083d82c50399100c01d40c6030329000300a8034005018142c1010036080c06486504030700000101c60803151222200c40e61902d2284600c81e41d00c0031900301c2d0f9400780000000241512103504058012030013104e0a84016544030804422551401e00c000c002c184102d40400580c09440b840c088000e43c1810030100c0311040a24039410602641c0101483c2c10302104a032080303503030098441d610f084550008501c2c0c004181c45828180210703040310700f43c04500040300e110300d440e044141e8008120795803c40c1d86414802d180c190b1904076001070400004e46007031101e0900d00d02209000d000d150144c01900111001d03884052003c0c0c10104914195904c4091070039078006070700304091000140c0d08140394541d1030241003205130307405580444030a010900042c0f144070234521040741100c0d81110a1a954049403400c1e11941412421084017020003510f00c0e40343e560101e56141100b40c035060310144580e00e6201d031217941e50030080080c0c0351036401c0c800300c3c20a4013164803080b1101455400c404c0110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 426732455 1250 426731205 426731233
    0x1110604060903090b0a0c060f0902060403030306181e09170a11060a0207150902030109060e160801110a0c0609020306010611060f15010f0c020402180a050909120705 73
    0x1260a540c11aa000e669659240501d5446003c03040a846a1502103203080018070004103194009100074002076610041486d01503440d5205104055000e0041e5440315960304020300104903030f00c540045044142c0c004030708407141c0e1061441081c9142d405580306a00200400020601f4100880360100c0064070355400842a002418861000d6030310313406207041c0c2081c05800e28070054855000319006000318000121252071403c1b0310740800000103a03000a500010b03014215089015007040d00d0031200d00002c080c00316441c0001c0c014010b080081c280d49840880c00c81e580c7c0d001f6581310000901c030a0580b0b40c4200301b01c10301940550000308402c0020b0300084c4c140300c400e0340010081150080a0203804000f07100059000c404c8451901c240d00e003d107090003280c1e42d0404024100324960140902282c040c0c0400c0c180d00e41c02030411074803640102c4042440401c2244000c0c840c40540c0b900054915007a90711701c0c407440d182006800e40b01481141501c0c15002010b048480c1c3c09001d007610480c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 426733705 1250 426732455 426732463
    0xe100308120601120614210d08070918020901030c0f02060c1e0a030222050108061011010f1a04110f03041e03030504061a0a0e07020708030c070608090a030813020111 73
    0x1800754050400010050f4000b0000300c002484080c20140003d01c7d504880064082a40c2048640ca41403c4242d540d640d54200e0302040c09030402842102e0203000c00c1000f242c3c0d54044c250300442038030100447c5501040c1038840040344030700d20380183e01001c001402c02d010000684070a0200e148001c0302d117010504510f210307802007030f8000000b0303a0224607614aa000c411032040d10307400e94030010044600341400240001d070000c11550190035180c03a03240f481e612031410740c40c04668280080213148440e080d120003030305540c03545910f02e01c844440e003229032809214039406101c40a01d981d1804104c04501500c64000500130b0b102d89019210b00c041c1c1d04e0941c508090300030300c290740001e00703460107140501c01c48044070901164182c512005c0300f29601c1e0782c0050710540321a800e002220b640c0b0032804038645080b541000d6014040450402d440580010f07051052390501e859080e032541d1101c0100c1d40d55400c03410301500040018011901507012003940d00007190046c90081e0454104541441c98 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 426734955 1250 426733705 426733709
    0xe060f160210110316050c0c062a0a030f050f040905070e060c01050a05160e041a0a06050304051209030703060905011404030c02090f1e06030f0f0303010e1003081206011206 76
    0x1010300001008174a06030107075904150704442c1065810070f4074220685660b801d01e016a580510000030f864010b00c1d1251b9081c00c0103081c0312100104030081810420380350340010000310085000307461703940c4a460045090392071a000ea40102410036113800c0001018080c041c0c1340e5028842d0404050003070351540f05c01003c20864400010900f41441c120316000c440006220f0000c221005042c1c10320240d0050603007090080072100400c6d10700d01d0109e401d0340625a10703040c42d48080c503040d0000e16140c1200246200d1800340c0d050f60481e886e030f81048001031080301c00030b0740e06070086002400060079550120704898015000001e40b03524100c5285460002900c00303901003056107508404514115040302e40c40480080d8000d100d0504804030160418210000c40403124032400041c940c0d241046124100b080040840713200f42003508685840358800c1c02039180d82c00e0b200c000203058030398201441003106d9010103c3c52600080c83e2400040300d0b03024241e2810072401c89800b00e41c01c6024040c0e400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 426736205 1250 426734955 426734981
    0x8040806090d03020a0e0f040b090702010b03010b0402073203030a0b12070302012102070c03030c0311060f0c0c01021b0106090e210a0207090f0204090e060f160210 72
    0x100c203060941c1082e00d4002c107501081c04041c010403c1680b1241c0c40040b406000c08140c60490903c44034000150140c2940394061b90001c85680c20481031a81c15000040340c10420f500800030b040e001320074042648103566003d000c0c6600c2c17405a0320800b0f003a1031020301412181d6801e034010007540d0340d91400c651041c0c0d0a000d8084e240e010b403110b24905180310003c500184801003403901d10f55800a0513601a080348941790a02c441107a11425003180c0440e8280c507405450f015440d80c0741d24024042c1158079a05078000b6090070703004050032000080850203070415214a4041d503446c08140981c0b58415440c100d6607540a00521103c0940440d00b820700764680800400c403141450345407007c444100e0405089a400072408100d90031101c5013031b09403244180c4007555200b1410700107900c4c000c055071001b801149008a82c1048031500c2d07000c3c10954980f55000e0091a0100600d00d80e11841030b90024070990220340468803109c4140d50051201d241401038420030b0074080c4500d01200e541c4000340b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 426737455 1250 426736205 426736213
    0x121050a020622121529030a17040915081b1f23130513090b0c0c060705070203060601180b0c06040c050301060305070605070606030b090f06010506090f01140403080408 74
    0x6020000300c0c08008042c1c005d01c0404012503007001c01142d1080302040c200c80091a08070321108000c1d10107010820000d0782225003803500c0c60100d041034081340d1041c410020424a0b110611104005e4401840121441340000f846c1e100d200006001c2180314001605903c500e60071b010341600452010142005010b907110100d1300c0a02c044051010103650740742030f0982e6420007041c0c1125413290244d5040d01c50644907405001d5145262400404c403800300580014400c00800c03401390364010040c620b800d013840c00c0c1e90301c907110380d41d0580340c6000f086402580740d00070b04006105540b0500d000d9a8200c01c9410494070305544070704008595008900b0040c1c1e5810800800003444000d040700d41c020072003600200070403495134950907240c0b141401210108807000521000380000c0d0f410880180d03400010341e00140c10000c2030656a60a0030a0559190099900002d0140341c10800d659030050080d0058410396110801100c511280241210242d5014480800418003800282000c0d000d500010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 426738705 1250 426737455 426737489
    0x1203140405040e011a100207030f0215030c18030705090103020904110402030705071109090a0f0528030f0804111201090b070504030b010f08030d0e10090503030121050a020622 77
    0x2160080c140300d140e02e00500242071000d504d51f50000740c44c0e08990300000300c0703000d49000d440040d2138038180c0c401200301501d01106001100440700f0060081c5034038542001d5003010f00506150f103c0915204165014900800400140c28003d040e0341d440b61244003401e0020002e000010100d80003a40c8500000e0004280142002400c004414503a0401c940c1d11180380380842c503031a40c440c0440002001200d006034503508028080013421741a810610020b0303000a01a02c0c40a12500c0403403090700041c04080d58280341900481e500c81c015a001441819100035440c14050841915040380368150350b24030741440410900c1c03201c5800f410003a42d41f039903100c0c80c0d810000707100501a0010311b07820951075030400c4030150001c103c501600c48003102007094002090424200184019154a580d0034641369104202c00800114103a5861000305104a4808030103440d40c4002c4650080203940b04141400152814401904003e6042e8000390058062030454201c2d02500b40d014008402900d114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 426739955 1250 426738705 426738731
    0x1509020d060e01120204091406010e071d0904080a02240a1409030d051005061c0c02070311060705190b0103030207050103050702030a0f02070506040305100c091203140405040e01 78
    0x241d10003424000808500b035414081600c41c0390040390700081c07042d941c1e01100010004501908480c4501400a1340c1d150741e5591220324031244100e4113040000c035a20200614103514444120044502401c0252940c0e01c0e555070345a568480b2156a0651042e08640010b10501c00c0d481d405c8480f09120000807400c0400301b0b1410b480070f4400503040141c0200c00c11264610000580700c04514024020401303844a00e0652400303802c1da08a10340001c00061071a442007103003440031482d540701c0f4404102500e1070241c101d80340e880c00e0100516484100461250a260820140000382d01441c161050860a1010414170303441040c000c8402c85403100040082c940c0600c4180000c01d820308091100345041c04000f5200e00c1002e5101c0244003445400c608a28420802c400240401070541940d882d02ca091659440b900f5070449a0700c242440000000d191040b40c8410848203840041200c2031213540e4259200a00103211614150741441300007900d607124001c1072603450f401000002d03c0518140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 426741205 1250 426739955 426739961
    0x20408191b121106040e0c07061d0318090712090c150906020105100b030a18051603050636030d0c1d0a05100e0303070b18210901050c011509020d 64
    0xe101ca110742c40600081240401c0c1c100c88541c403811901f552540c88245181c01801042c21913003943c0050b8030302d0444c1c101c4400c00401403462071985201304d203800000d40f0800100440c212803d8001614041c140c404802c0d0f1070b0000c058492044a0100030306840c3c0b91b01c5401c0f90301d8002c10400041d408201041102d4085c803555400001c0c03440c40311581c0e81842c42c004014400a8400c2c0e12080c0d17540100035600c040300601c100c040e0740c0442981e003102c1180c401c1109a818502054442d401103001250b0500350010811842d80c501d050240120216207000c151020b0111a08034581e0004005110b250a558407880744001200d480300c10489482c2ca01c00324446080100c3e060150707410050070b00c095550070311018040c0089140c03e40d48004d0080200c0e0850082c1100204103081b404103218003030300400301a8855061a00032203440070308024100e11a540c0c03807400004410300c20080000075510400040c683c480001c000030035801c1600240b90504001c40c0d100706440c65010030440b8482031280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 426742455 1250 426741205 426741233
    0x91104050c031e010f0302150c0105010608011508060f04150b03070504030b0624090a030f050c0f030d09031b03080a020106140126040303110724020408191b12 70
    0x100c0241d0304000041722134032801d000c043d1040b41c1c412070116110751078034122005010783c5c0c802400316580d10b48010b80182d20a0003000420300c41c00700384846161103501130601c925001020b00031180e07101001e1000820007600c100581c082800e002040d5081c1d06402140128090360b01d8aa03554038605000d2101803020b000288902c0341c10304042c0031040c11014054582030081c405d40d41c0c4194000c009a00c02c00964002804540b141c0d03d14007d002d00411000d182060039106080c03906c0d1807908040c0c42e20000398002c000301c0c80350003041c0041004c2060503240c60642c00c110713040c6c0d540c072500d4200342e0742c026501200c0140c0d1225401c3c040f00c0d42d459903144404a0070b0070a0728494142c2d6000d03c00000c00c84042003c401c5000000506040c42600150100240c1980050380c485075814103401c3c4c14120b841d82a102d0054400d06925440c5601c2102d0480344400040d0400b4251a060012000f00304101030354170301e00f089401242d2201031f840c40b8005201c501042c820344590303454914000400c2c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 426743705 1250 426742455 426742501
    0x30403030f0e040b1008071b1505070e06120702070515190f021b0a03060608330c0d0902040513151a010f0302040b120103060e0105150103091104050c03 67
    0x1100211210f920390a95070410030781036082410507987e8411007151050381a4004a5464105000b04020b01c141c00c101c5009034071300c601d001d11040d5507075242034589c26078840006402c03c0c410004102200c0c41d002d0042c0e0030580d1841030b81da0716503454000855500c6184406070442c6800501c5000c0301c0c0c1d030940a1403043c2268201421140c481d80400394a80303580c111180440702e01e40311a21026502c0c808214091640582c081101544407104240d45500002c0036035060f4052000d0100c022459078008906020f102d01c3d0143c090f80e8214107013140342c01c060131800d1030341d844200a0340180c0e0b413805003a02c2400450840c0201c207600381422640e502c0c00c420341c0a5851300c0c2c50b569003a4500e09030031000c0030b01c0f82804c04801c0c0d540b180704202c0003486140d01c0f03a4801c1c0808110350b0200018420401d0482e030041c401400400808207549080b035070b0984151944c03410380780c00d4008650181d00b207400310034000c40e800c900120515010406445003141d0034200140c0c00420401c0c0c089090000c0a007007054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 426744955 1250 426743705 426743711
    0x603070503060f150f0d1b030903020601080a050a110103090c03060225020a060f051c02030a0e2a0f03010615020d0801080606090a0912030c0e04020c1f0905030403030f0e04 76
    0x20624110000d072103002881017180c0f1002480340040c81c059088201c64051103800c3e0030342580c181c04020010030149400f1001170150800000d1244c4002900504698001c006800603c00545d0b40400c402130681c2004d043c50b403203c0c1d400d400301d11070005410085014080c05a0b440c100405040140260300c00c0c01c44035214074951100151300d91007002c00580343c817410b011a403482510000c0c2c5882c00f540524060380140d0301e0420103410b66a07000355010b90f4076604c00b403000440c031300045d60303ea44403990651114540d102c2c481141c03028102444d06601800751400c0c10000c00500440d096440340c0e04140d85d101c001a004240603035040102010b905500d10b0b00107060750400300c080707884103000780c4507034400c8001c0d501244400581d580214440b80c3d0017829819580623241001d000349c110b0281c501c001c90712106442e004c604050080307900f214224070280849601e02d44a644a0344041d401d2240074903070b00c418030000500100000d001840c003988990780c0300d820b04000104200c40a0410300e000c0c0d41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 426746205 1250 426744955 426744979
    0x30e2e030c0804110406050316420908030c06010e06060301030c03060c021f05100501210e0703020409152d0c0e0a12020a080f03030c07110603070503060f 68
    0x40d10159082c0c205600c102044050115400043c014001d10b0701f2035075040c01a401b808021010b840100c0c4202d4141c01e01e046c2038802c58980c2c800584030000402001a07505c02d81e6116600584459643ca404003400c010800d59219200285160807210a1001552102c4014440c2c6900310180301c0c0c1c0a2011101070345990304655812302c0000040c070000700400d45071406030001ca4020310129008000e072a0170008441102000480509001c0d2250018401021004500c5522a034100c490f640520b030841c00034804c205525500410094600e00e02c20b015040700800180e0750b5000341210f444c0107034602d08801d010041280d00f1030710180d42503d820404140780030251164615001100354003158001408002e5000c103598050740c0c02d030941c0d031142e503441d0b01040c0220b4030008103051500035242100580c0d2103940c116a038604e100101500c6600510016400950740001020301510450850b503035105280e010580c0d641041c0c44c0c0d400400c50200410020f81001011100382c3c240446529120b40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 426747455 1250 426746205 426746207
    0x130f0b0403031808070308030702010f1103060915030303070e0d060207060509060c130e040f020a03032c0f0910032f010f0804020405060a0806010801020c0106050108010e0105060304030e2e030c 85
    0x1172000d21008000c8a404000502114001c1d8403100311020590010b005000c80030100480c03d520895115120780108000305a12150014000c00d50800140080d0301d151a585000d844c03108088007801e07800b2180d51010b20006102d400604502481114081641d082c109002420004014042d09a01c0405e2010884400b180c03c081c0003180e805000c0740003251120304008941140d601c4010303421a0603034000104265224052501d9080c40c511005140c0300401110b40d42000c0300e00a06a11522072a16400c65181c8450055044172000030b21031012540c3e5920402c100900c81c83c02606040f1001105802501185a14161010074601800c0d00e580924024042e03003805400640142c0e502c01c000380d956200d00b0700300741c00380281c85c08441c45583d41d6901d85020303510402d0200e1365942020310000b0704c0e500070340b0240d050b2003080181ca41160700b00811b009080d00024016400c00180c03201c20300a545480c050070380054503000d034098a002002016180c40900040c2443c101468041882901c1d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 426748705 1250 426747455 426747463
    0x8030c10110724060609030510020a05090a030308090c010c200418050a021807050706050901020d09030f021e0c151e071109010e0705130f0b0403031808 67
    0x31504440d001601121070600d008190080c035000601c2c01121841050b0982c0804008101030b900d020b4040c00100c4d22003500711501041440000c0c640c0c0c4c0210070741c4041c544250098903c800e000d2905600303254589000900040c4194802c0d4045818101449003400b0188600040e410080c2428805c9002c036545280f203d6061115410032104602c030340124642e1075401904008000d8032900d2000b0505050240c0ca82d90700040032840b40503000340e040c18080340d102c0c540c0d1103000300d61216420a43d41c1d840310005000d0007098100f03075540c20854000c0310410f62103828051030090340d400500c00c2900c280030b868100d6030750360301e0b04400f001810b1001d006800140546810401c0d589412507084003d9004c04038050b042d14640c400380700240c03018408480c800508815409109002415580d04040c0400c0100a0141c1441d00d040c00340090341c41c0d07000c2c80080ca070984400080b5100240e85002c1d2154110030b41d00003038100386001800700300b410341c0000e00c41300d0780c500c0e80d082050303071440c003004e15543e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 426749955 1250 426748705 426748723
    0x5060a0e011b0503030115020c0312070b0a06080a0803010e09070e1f0b0313170301150c020303070b09060601020106051905010c1b06020a02010f0e091b070f1a0108030c 74
    0x10418410751032511650341e1281c80c42c1c507540c0442141e80740d5864503c006152546034181341c00600c291011a0440d2030000b81e4030840c01c02091f2103500e4520107403100f01083c10000d10741d10415480b5100000c0d0b02204214560005000c0c01080351254180000440c42c994084c208072501d501c008001d101d13010421a582d90411030400d98090204118000074851114903845a141450080308200c8900b10b007030020b0440d00d103e0392180030b0388207104011410500080c00361840800d41c1c0203040704031394000d00122444a000900b101d080c45840c1d514504044011070303400d015a00141c0600c10656024042d04000c1d040440742c4030091002518482d030284494418503042090098000d0223102070000d201440801c4065450041c1c0d48600003c0d55403980400101e000501d01100e0b61030703581c03007850b81c01449403004290710313855210303003401000c89030f42c03200740e0002420700304050700c0020650308034011050b1003442ea190380300490070380d1070820100c141c1c0850041d401c10081c142c104003000ca44d086d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 426751205 1250 426749955 426749957
    0x3091509050c0913060509060402010f230a09350a0302120a0504050a14190e040611040503010903031b080402010c031b02060304061e0204120609060f02190905060a0e01 74
    0x310f159181300d000ba40049075a200070b0320031881d0500b84030307807040701144080c4614000e032152561041079040890700703510780400800c1090340c002418601310302450014129605e4038a050a0000d8403110340b42d00100d549902e100c58508208400e11108107590308840c44010300d500903107810700c0d494038003a4071340c914600300c1e0010a5001608001c9640500c2c1503801a010180901089036195804080c0c3d1403000c0c22410300c10031150500303c13030307039188660000e05407041400c0e01c0419440da640c4143c003a10003140203414000040c4004280358600340320303a50481d4000d5802180c0058680880420005654507420030040711038200800350f40c00c50b03400385c60140d142c078185503805141500750b8001c8000c100000c3d886000041440188038180d0450800d40e0030885400c400a5a45151001248607910908000c2002e401d452404502640d01c0304516031700a040102c1c454184a800d9001c0343e1140d80307400b1050a80102e40748a4990020007800030381003c0c2d4400d4903058030743c0006040311040d180114 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 426752455 1250 426751205 426751219
    0x2030f030a090c031203050c071106090d050d0c15060803040b0d0609050103111801030b1902090301020309010c08090714120a02131a091009151503091509050c 70
    0x1101c074440c5a00901c1e00541041078030388055203e05d01240b242c600e14031400c0020307040038085040005294111054154014403d218450140c0207209840e0001c088041e44030070b40154000c0800c90a000c90060260660f442c900c580f0101c0c42c0420040c40c0003130081b2100c901c1c0c11018007108900200301c40584500e4821191500c894842c01c602070001d54008802580c1098000070801c064202c4a003040402210040b049510348108055554801d104c003030400200e40c0045410401c0d080d0400c01c2d02400b50601614080344c0402180c2a83d0050b94a0a204e80d0340e4000c03a0021035106159076048a00380000e090142e241810581029103840303401445101c1100003000008400c0210301d0030103034013800080181600344401c03802041d06800d190103502c4c840d01200740c9443e00300c00301c0e031080200120f400702c054103100303032100100300094001c910038000905c081142c0e00d0398242001c09021964000c80c205400380703028800e41c030000f034035259035504200704500051000705042411380c100303845d10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 426753705 1250 426752455 426752461
    0x3020429040f08060a060b07020306071805190608010b0412030e01090305010f29061b071a0a030c0c0203030901030f06090e0c10110703031b0b091c0f02030f03 70
    0x31440314071441d488000c0c010200c240000d49100d021800c548610309514041103a1580c442c140c00c018854190000d505d5000b0900041d45135008a441c4880054000c0101c0252903d500100d0085040600c0601603491089820800070f5806540c1d14050080e0100540c1018600021080c0480c00490003c00f03000200d00c209510340d20030780e0058019500701c8000d0128203003000340c00300144002c140381680e404070030b40c60141611903400c103582e03d024080c0040385401c203181c6004c410b07118400048030203030140c1c0c86d00080110a40c1880d41d41f4442c00c40c07203956110460780024044420340804a800c3c010058180030150b500030059600d0000700303090200b0a182003107510001050903401c407040e214508a13499900b2800010039141074002603074942d05a0805090030740d0820072205124005a01c401000c0c000284200440040e02056a8032030085104a80c1c4041e28135404484100056002b07624103051f419800d03406091041c0c1a080c001070b800302000c402512841031040d4850200030000c08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 426754955 1250 426753705 426753779
    0x1d09010905120a17070e0301140105011403100b07030f020d090608060622090c0921140709020f0306040c0f0503160e03030a02010507120b090f040516031b06030204 72
    0x104920a41c10200481e285c0c505040c0c041c0c81019050754050003586490389000c120740030138440703505079401610340300342800e42042e006407143d00080c0040c2000701c101c0c40028040c0002030150901c0b038483c0d21408102140e08000030304e42010381c00d03502e040107203440c81000030a070048045500914140d582581d0741c00c1400642400050701c2c54401110701181c0030000e81903071194050000c000c90fa50ba000c0320907a442000480624505e52000002c81c460068400042c12429909075414514015079410945d581c034008226003004041c1e4031281400001c0083c0780c5424400d6083c2030f10f15003444111180d80308402080303804004c1c00303000a14075400681010794007456800f0040d01000302180e0761026202d000a028020540d00e40340451450404542c0d82000c500460305040c41c040d1058102e580c0f044202840944040c4c81a00c4074020011030004510710502d00340c014500502c1e40001024011000c4080c80486901040415205000900201c0c0c2522200514810b212074540d03004a01114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 426756205 1250 426754955 426754967
    0x1150b0f130f0f06020f19020a12030c02120a150506030f030d0c1b03050d05071416020a12020306060f190617100303230d061d09010905120a 62
    0x1100c1205110303500c4000440c2d00c000d18030305043c0c500107881c403400c032030740c0b0082070f82c0c0e03840c0381100e58510350800b104a1030282c52500440003090700081010801d40d54034403203104069036000094000810940743c80c3c080d403c010309564101e20480004040b440704944582401031f5025003c214103c1d15070011500c1c030707582044500c401c90344001c00d5982e42c010703040000005040d001000400705540c0c13800780040114a4440c0b0b411150542c44040c0381400810f4050014440100000c041c8511602c5050b41d012160703016001055503045807240c3e001c05401084484802c80e03001851800405c0020380060b14040342441c1c01c0740003950355915420101000580e41345000e200180c5515603604000b541a90204988000c0a0080100c02d02529110814400f100c25804040d02040004001c00032031481c004060094009007421282000c2c400c503540815070308640d2207002002a03003d40700e00603801071140c1503040b2030444001c11000a840c0d46c0c0135240c030840000650211004146d640619008907 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 426757455 1250 426756205 426756217
    0xf05010f0c0e0a05030106050d0f08121807080303010b0904020c010f091a0112120e010e040f02070605010f290702040204120b13051009021201050c030402011101150b0f 74
    0xa5041c482011100d600502800700c0407181c502c548054500010a8101842107509a8801908042118407a9180c2c21503502e03003030208030341040e030400401942c803c491031940c2c0644038040d00c0325544060183c1c140c3c138100407500405500d4001f00010040e10b02c0351002c50f010000146ca01685810051441d207006100b140240c0c1c0000c0e0402d41c640c010010848514080420038a150100720303604c80b46070400c540c00008000307006100d460502ea1125014984442e10705405240c490400980400418262544d5403e011202500410303001c080000310301800f4003420480360280383d461f107003820001360180c506050030340c02c010140d15070300411881000c0b07031541350b00070300306641d115a110012803030801c65442c151444103c10011507a84004842d40316a0b132a0000010540e12107107250a1006061003103041ba440320600141e81e03da03001c207000d80d910640549891503101d251500024040321710f00f19120300c1503450091000714a002201c0c0e0b440507074201000c01a01c841c04288211030b03e00c903003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 426758705 1250 426757455 426757481
    0x120c090503030a09052e0518030708030a0e030604050307030e0303120f01170c011710030501050c1216080a0f020f070b0105150c0a02060306030a080d0605040c110a0f0501 75
    0x403100c030740f03070740141c560b0088070401e40d2004a80c5211191244260780c1590f121285800b0000c58014183c3c800e5010341483c40d414160f5a01480e04440081d06c1d011003a400f01c026504040348095580f03030403240400c07560509070040c01c039a1800b9520580c4901c1020300050600c49400084241c0f510100b09880e002900003150406a090000340e62009a0f001d00c5000384061600740c0f00603111340041009403040f00180c5820411144000781161620740081c040c00c55942c2c13080001010681c240a0107000c2d03e0900c0b0503599400744441c00341c2c2c5400c0c005040743c0440841ba80c1e8042895070080e091903101241c00b40004940850202c0300003c2e109604810840034000f00e50304042c8044440990b040703440840e42009602c104c03040081e024022800c0250445c4c005605d4640903040c09001180d00860060560f920b280e842d03510f1a4090f00100d0301000c2d0305980b4203047c8a03500385072059040301d52803403c2030301603004403d80b03440c0d944074200303030007040c0340750714002c030806c10000350030001c00d800cc1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 426759955 1250 426758705 426758707
    0x111606020c0d02010603151109090603010b040f0204150f051902010b18060301060501080606040302040209030c1f09061d0f012c040615080708040305130303080108150106120c09050303 81
    0x1c8502d0082c041e2078035000a440340c1401308240205403c4603c01c010025010400302824030824004004041d500140401d0b0195200da0135404242d60344e11410007621001000185c4641c1041010420b113000c040584060001d901d0000910f01d4000094843e9100b41101158840d1600c0b030007207002d4204100d28581180078090780076800e41242d60a580b14102c160b0081029942d20001120041002d44209412440c100028805420b1039001400031540c06821200c3c03010055010074017403603801d0300c90b40030b41f00c541e403c0400b0700350320080078002003250b0315042e041c0303050100c4040300407042004400d114a0032407110300c403580d000e0201510080203845040d0103c0c03040d200c900d299901c0c40103840b84210314151000c40ca400c1c0c02191410250410354400e00550b440110a4030300008c00b0300300398184541400001e0f0b417805030700800c00180d84690703102c0542d54074090905140c1620f40c10107505402580300180714099010000c13100d043d0005102240946d03001d44143c41e02020341d0041030701400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 426761205 1250 426759955 426759973
    0x503060c03090a0f0311010e0d05042d031a0708041a27060a1508030405370905160806010f030f1118030703120c020a05130c020c0103111606020c 64
    0x50031611b4410509800f60081c0300c248d020741511912041d5500e0b8207800b09206000a0051015244000420b80c21003484582d1180a505440c043e004466004852403565a00386850894078104400e4103d80c99082c000298105543c81407201c0803507168503074240c4c08a0000508007142c0180e8980b46c0c1615400c5e02040c3c0e0b0040c5450761310389804079145070314541480d00075908240110291012034026002840c10542890200800001c0c507407488580d09080824901d200c4239010004c500300c3d549400c1d42d0386102c2c5407115550a50300028480750f0a80c4603400915519500000210740c801800d107410090f800f03280c0000d07001843c51014401c41c1c0b80c83c00803580b58200c2440000c100300c03030326480f030403040d040362008240d0381c4d04050000414044000e000e8001c464040d9840a030b295100615140b5540d8031000403c10303112071010b070020b05c261113100391648039805110b680544e030340a10341400403003403040710909540300d41c1d0480030300d00303080b86403003414461164140d070390703440001d4150f800d621 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 426762455 1250 426761205 426761207
    0x30403080f062701060305060a0e04060f062105012d09213f050a020d0507051c0b010e060f160506190606080406090501110d090501050a060503060c03090a0f03 70
    0x2a401d0045d01c0c0480c1c82c29010030040c0c640043d1110031241520301c080782580e5aa919100582094460340300d08684440022a94207503d010f0b0702000b61061000842c80300c4141800e40c255102000d4104130100d075030030030533041207008003441862481c10002013801c01561400c80f009020035001c404400402c201050040390340140704100a60240e16404415081e840034240c01d515a03000343c0080e88000603c01200c03e2075a000140d0000d403000c001428003503401510010380e40100c5202002450001d45081c810140500e115549840b070a001c008414001e000a42200d868100e801e114510205501f82e50400002c102c1c0c0785200d41c080304842c1345559240c056501c80701660311016240592600d0b4072601100d102d414111200f5507140940341e11981c07103240c004d00e030b00e039403d40381c0395251901070320150304a00062404070030b5501e00107009046400d020b0708440000d41400e483c0d6007003103810421790354009032854122259085099807911201c441a1800c200300c48010007204040c1c04110031700d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 426763705 1250 426762455 426762529
    0x24030c0405100f1a1209030403080a032c031c150f080d170f2e081014060f19090219110706050c1501030f17030403080f06 54
    0x9a54103040c0400f955142ca10040460b00d550b8000007104606010001008105507200b03078002d0303140000d5030302d00754807522071042507880ba90380380001c25240c440e081600e102202e005065041d8185094021001084000f5100d1040c60000e0706164148091002003944552101c0c001105108001c170380c142e51840108000541031241e02100d0068401c80385085028a0202046001c1044c0c0591142c1e5105154484000b0140a102c01038101e2000001200110302d10100701c11030300542400d1191601100b18a41803180d070640d00140c2c1000b020309a20382d400007055070020021102c200e620707001c0d41c01156040942c0030000011154a620010b0744454950040481d0b8120b2203411202c211003502c140c0c4c40c00c22420f408400e541c003c40041203103501c980301030305910313040d14151540410108525002241d081e00281c0711501d28104040c100a05c04050074480d04001c180c603821498a91405410100020544c600719806a07002800690b01c20701c0d106410340c94040042c00819000b2040281c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 426764955 1250 426763705 426763709
    0x14040605010503090c10051209060603060705040e0c070614041a011a0d0b01050d0e1c0314130c0f06050306130e0307030509120616080a020324030c040510 68
    0x51854240042619440b5004403445078800a0007440c51800041c14080600f0902c1352a900700308081c0400400244c0221015010f80300003c01000641020402c0500b0071a01400100511408100400c207440340d90003400e90203041d01180c103455504904001c0058540070f444481d485240790100010044803680c940000003298011035066038882c07030101c0c0d00c2c917400c0003034401c007003818090f285421200713801443c01a0703010f142550401d0340c281080415164608001e101d6900408000007086140c8810602da01920380b80c24002c000c800b00c841c503003c030b4014010700401c8001c4540390090002c40344c04070300201038a030300500f000390f540d1100506540064402c20f03c0340003040303240a10201c4500420240072031000180d8600341041d5011345071540304051160f00109800e038081c9009034244182c0344103064808448200c0c6c5240c401c01000c0c50340081020300d01c68410300034000d9291090b0020b17418070540c2585482c1c9a403a240000c3d01d0078440c4444a94040e041c041000010b4070200d1800c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 426766205 1250 426764955 426764959
    0x414031207030b221a09070e18130b07020a0507180c020604080d020705100c0201021c06120f050102090a091d0a0209040605250c0b06090708070f030b04020414 70
    0x360b81d070402c041040070807240b201038100d041c1300045002c58030103a03400340301c400d170212080040304a074035808611480303c11201980499118400d421450801d411500003640c891800c85141c0e240400c0d0307249940e40381c15005001c641c4100001242c4a00800494103101d40000883c0c1550ba582c103d42c85c0c0904040040c4030f0468100303881881914000034119001e564084070340341c10701071010307018070080d0846a002e845522501201d8112007802e845000e0a6295560026a90f07400440400b000c04003001c00001d183e514011081002c026007080380400203510544e02e148004450400d1801b82c040d481c841d5900103411100002d0021660307222800d08444101d11604102c900720178a900c07103540200c043d42200084000400040706940402d50203202d00e041c0003981d1f20017408480700310700038951104c0130070050400c14050040183d001c42c3e00c010f04607119034151a080d00001d0080c03030050514030a2080f417407000520b00d4001c3d042003210507000b810440d1601c3e40c40c400d940580c10004100d40c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 426767455 1250 426766205 426766211
    0xc071401020109050706030c030209060c06070e03061911120f092a1201091b140f1807020705030a030c0611030702030f03060d08030406020a0914030d08041403120703 73
    0x284040d40180200707900700c1d030010068440d440c58100e00342c01078a0101541000c01d40d08100241d8542d54150152038204c0f20380004201030711b841c81c0040c000c541c4600c0450322a0f4801c404104ac0080c115039500e03140b9040340d802140c0942c8440c40c401c200d0040703100300940d899414040000c0341e0b80000c0b19038445c180c20811100c00d2406e00b40c201c2c0b10048068103001c440317031031000b11a13030504101040c6a00100640e00005400c29140c880e503051442d05440c8901c2041003120410021080407644288404101d0340c0f407410030404c00003d14181404140e46a5011040d00043c0103a40240304020060401a081d103203140c2180c5402402c0c110056400c84006207045204050040c400381035903c1030303000350019480c0c00384040f1582c3e1140c10040000790b21090503081000000d03183c4000d180075a2182c800540c8404403500081d00c4400e0582100c80118111000400725681c0000c2040c284121401d1040086d00c6609003403845981c40a400340c4d86100c0081c8500310746000440207407061800742d03810 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 426768705 1250 426767455 426767489
    0x609061508180712151503060b04060b03190e0d030e0f070b04050d0507241704020109180b040903020703030f0206040201020d0f030905120a0e090402030607050f0f0c07 74
    0x4002a4019902c03048640e034030601050150750321440c00c1c001d00900900c1101820501c05d62880144d41c410f42100c030303c61198070780c00c200b000340700c2c0140d428000c02103400f408070604085d80000d0902004001c8500030810307028822110040354007080301c15080400365100d11004c502e01034040c240800396038103688140802c095100030301140d00c2094500c2650349a02e800c1c1303058204100141240313026900c1c1e01500c40f00041e60044090300003000c0e054000b0030000c013140058060f005550484842d41500c00c4081088010b03a0301001c0d000030303610700c1c0b911001e05800e2880f4420040c034002c0b0f40513030401d24050b0355105040d0002840404c0300d04ca940e40b250810201c84040fa1105002c0c0d800a0250b0700180020440d0341c051b01c804000940c407442c00003500ba05a8407164a4440407e06a0605080014904450960140c030441003250281c0d040070b59402c00ea40403da9500008011030100b00d00803a001d842c00200030111038500070392022854440d41e000304090f0325080e140c8506a6100c0c190110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 426769955 1250 426768705 426768721
    0x24050a09060b0711030304080d0801092d020c01090c2916080307140d05040507080106030c030602130f0305010b0f040b0102060a090816080d0b012c01030609061508 72
    0x740c2816510b2202c2d031142005070380c1d0b8030188805034418120398035020511021a03803980802c42082015004c1d0303115409945030210f504c0407201810a2080300c040d40085600e6059409800c07500044042e480060751900c0940500d4010301a0792001809034043d10310000e0203c90140f07000b03540300c40701c1803c003c000c224051464414403070f0704060781845081c000800086425000a9907212050382070001e902d400702c516000362640031032a0315041036a980240030502408010310300c05410b400c0000c1180c01e0940c0c4860700d00c41032a200040c0096000109180380c1d9044107084801000c03002a000029a1a464214041c3c6070a0150754013415092032034114500d454051501c0640307040c0c0103840300791911001803019002c0d104066581139070800420001d1003880c51412951400384070382c1c54450180501c100107079541d0640040c10485804e40720061903600c03940001c1c0c070038582c8590719554085100180d010300000c2e170001c0c001c203140c0740c0c0c00110321203140c000004200082e42c905e8003a54603a01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 426771205 1250 426769955 426769961
    0xf0e09010c020d0f081003080423040e120f0f131401050715050a090212010c08090319200109350f0d0b030f2d190624050a09 55
    0x3540c80700103900410303505580c03401985c907181c100c107440e0200552280c0703a84922081d94425401010343c5a030810003d008e0365519050000c8a0800300d405001580c00420401c0d80e44819042404482070000b800c011468140d50840b145440d140c14040d0301c0340355181e504c0e2080012886140b1142e050344841003041d603c0b90046415440e80010b0f40b4145c104406141c000911008007040130a0360380d0b110040250303403001c1d00e500000614500110305c0c5c000f5070b000204401805000102c49600501901c441406401341303602c400c0c00d2b1071601c41091068403d145080a5580043c440715503c0c003d501802d100c40407504004400000800c0b440f90880d82c0980070405080e81d00b000740351079050001144c03038401070b0300500181c0c48205010401c85003040000f800c121401c1501d402c1684001c01c000c409641c3c000dc1c1e0210001d049034403582c10366500345402e48824a440200d5615000112040100502c56101e0303841a80400313001c40c14141941810701140743d00307000312489200c242d1400201400b80e40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 426772455 1250 426771205 426771223
    0x4060f05040503030307030c17010b09030f0601050609040e120a0903110f181b0c03040510020a0f12120c030b0a050a0b04050d06020c0a030302070201030c0c05150703060f0e09010c02 80
    0x50001d45c50355444220440c014400361112408000d24244000800c0303100001850180628102581e91400c0010401d0719141098030061420782141c001007280383d9a40c0150366809600784c4000c0303041c5040c50442e42c1000c0c055140702200542c04502a520180d00a04450a9a100b075032001c0c103894a29003000306111800c06400d40c0001c1c2c2100340f403003000303440000c175410075040500401c0c0300c403500c4000f0b0380a4000b42210010380c1e002080801c028500791103c043c58806500241844130420b807164010441c0c4031401504409040007007042c614030600c4007444086266400f00014078240c0b90040107080705014240c40341103403107000b00740b81c50403804400c00c40350003086191500f89028140400d00a401b842912510790a01134900550801d0002110042c42984c5c0140c1d11b00e0944000750441748801c180320100300b0302d4400c2800280c030015260b061038001c021450b0b1665038400044003c0d0400f600001400040d0210000c0c02110004006000d01000c000074030011000d4a812aa0707500d0003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 426773705 1250 426772455 426772459
    0x8150f06011b02040e070b0f09310b0312030c0702040c0f0207031709280f15050711121605090f0105012610030318050303300103050304060f050405 65
    0xc0b499400041c03030701e81e0004e24031070342e440c0586401d0b550780c40f9072101381d030000880c0c007503001c200051544445c64080070b1004a128040c1d1404100c1244912500c40d4184006941850701d0351003000b004565400c1103145030000300d4124055491604003000d1500d904041000c0703000300c0c00c2194085103140220072100903c3c42c582e008054103072030f640b5031011500300320880c445d00000801240565488034224200c03031858000081412a5a100002c4248401503104034a102d04010007405801c035a5454140c2262062070001c2c0ca03110141000340d040501103010641c402d80c610180e01d074000c008511400c0301e0030348002c1c40c1080c56441060041807642200e00003045421103005012540c064614040c071405103807101c0b410740b440600503980d0001c056032a00440160140c0c10420142d20100a602440c01000d4a0a1491804010036641e000c1d0143c2000015800c2508422404c4252034181101c14241810041560340e800c199459501a000c0c400004200ba4824513a40d40240c04640c02c42d080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 426774955 1250 426773705 426773747
    0x3030e010c0311250c08070e1803121e0f0a110909130503070605010602010f0c110705040c0302070501090609060c0203180f01030609051801060906080303040b1008150f0601 76
    0x40800f10780b13210001160301c4132070390a030140610080750582c4840c070090300800e401060b03464202001085440401804400904503030003180c90303020008401d8038110b81f01011044402d0702e030447d13114001c003406586001070308444010011400b00c0118024040c650500003042403081103407544d01507110b01b6070903680084024000c0342c011009200c1c1096454041c00a5a0800c1410703542c1d0720070f9823420707030103800103070346031103040803c003c103449095540c80741806e0600c607000783c288405850f801244589031280c0e0740d50b00c3d42255940030ba01105c100e02e52080081009084610702100206203100c010340d1010b1508511082240c00041116000044d1240306449200710004100b071101481803024105501c4481c001007508850203002c1c054402c0a808550180e041c1c02d04500f150350540c440c000c8141402000c10820401004603500240c201640c60440d035640090308030462a240c3c00300d60103201d00071035805564100350f1742c40e01400ca1285c03500131135190744004549000c1a00c0104d450800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 426776205 1250 426774955 426774967
    0x270819060e120f070501092010050c100e10020703050c10060302060409050601200c0f01050a050f0304080403080703020d110106031a0a090209010605070605012315070c0303030e010c0311 82
    0x3c4680c01500f1031070f02c07034000400c804500350340b612071079000403c070103000202c0304e007180700140387c03000d1080100e160901e402c5007005410b9481c40d95500407c02030b07401865540f80d80b2504903909004111090351240b0041d9660302691400908692051800c440540190308007058000542d004410850360010100c5050031f0a10502c2d070028a0086c140034140b050081d03110a02d031000d400e00292518100c03004d410300640740000c0c07151214290780814100034040184450b643d03001029500c0d40903176408036549036680c911782000940305030b0304050000500400c0702410075600180142e003070746c00c980d100c90b142503800d0710080c01e0350007900000b003202500c00b01010002c404808841d50080f280c2074045a14000b0390082030500034203030048000100001002014003c0500450f801080d003c2c7c00000d0f20451400e10f9440340b01c0300600c0c0c078401c0420040c011460441c00050312055900107941059103a0b0f00e107005002024800a101615401d2070340d00d4410344d0113842401c0120b20001401880e2003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 426777455 1250 426776205 426776227
    0x4150201060806010614161505220b1503070b040311031e030f1813060501031d0607080601050d020d0c0932060408100c03060f0303270819060e12 64
    0x1030000007158141c03140c840c147c1d20100b80203c0d08101175014801c00025a0306146e14400743c01c60328240d000083c1c00880c2c1b0000c002401d48803089030701940344514070b424407120700300007802c080c229842b070089044003050210900007070800ea090104022000ca426001e105240395444000900304410260000c2c024050f0410280c002459180303e815090381c0c1c1483c038040000c0342c4041010508054644e01c00c820710181d40c0500c07072070350401c1d411141c4414203617000c0c150a5071990001c03d54410044102c001c01d0450b40914240c5116901000056403252801c001f080001d1420710b040b00005500e01400043c01545c00481322002e101c0302c1c000c0008803140591200380e4005c4560087c0c0c004404005c0000c900000b4800302c4080103103840702082070211403800030141c0d016504034000415201c1d0341000081e810010480c1c001103002d83d402d02040c0f040c0325540e100b0303000380c1c083e100c64014191040c0c0480b01c0c850a85910a2140340100030a40c107250070240d48550108400218050401c81140c190b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 426778705 1250 426777455 426777457
    0x30803250813061e141902041a0a0c020a17070e0c090405060a05120a0c051801030f0f061410090506010c0f02040f02120406050109180b06041104150201060806010614 73
    0x2130440f01e0104c89810101901040c1121081c681d01a40303402594103000c20f41645503496010704130030340415030405003480e50780ca03d440b0341c42e0100031442000007013101c90b4a0041c00304042c2607400800100b1415a45d91a014180f0620b40040f1624000c8030000305102080d030018900a00c40c4001d594240040c070000d000c0208000b0307008561028880a0005e01c1396602185a0340f17502150028007a199010b10313008400f5403058100701d00c101481540640a1a1104202411030b9003005400110b1049403e02a6440854420241000382002c0b8451441035205030000d0140601980000b1115940c907510741c01c980064a603140040e6500362000045081e65016500940c0010800201030311928a01d0040741d100340d4080190307214a40803c8140400780c400c06006102c07580d42405490210f003078407100311020b0348004051507011404601e044d1074075400b0703200074054030040700e550f5500c41040c20320081120141200560800b500450402e00c0815424100c9480303880d514441b07412241c034a266 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 426779955 1250 426778705 426778721
    0x110102190308060f030d030f0b100f0c0602130b09212d07080601031a0907180e060a0b0307060c0213020705030d0c0e0a0e040317070903080325081306 66
    0x130103c00e404107410659024842004401c00c59200021500c2c1c0d9413065200760380b00300300c00c607110700c060f00c0c0b0204600d81c000441d58006017840c42c3c080301d20b030200c2c68180020300410011400c1004102004541d106d00c0d4401400008001c8445540c01d010318070004914000f46915401c10707421850040c5000140a8041501c0c240c3c64000c2da0384601002d41d001789042c0b100c0e8000f00155002a0040081c4081c0070050340d5101d2a528003040540b4180c08241d039220350302d214202e01000000039002200480390711802086015009542290500c50400001303440c22019040c0300f400751140000300355004910031b01da1503038060280555010380880f0350009402840341902e003800100b003d101d50070304d1441200c41c84101600c03084d4180c1d58403818401c50100517000760780f043c60540c0c00d01000c6a00070b9414040380c07210414041443c1d035824012214146282d000400381000402402001030494401c9440001d22240c840203450f05104221442042950007020343c82c5480c8954010030302030741280785 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 426781205 1250 426779955 426779959
    0x16060203060f030f0a030905150f0d0b0303030403020c01080a020702091302120a0312110307020a112808010b011e0c050109020a030b0702010f06150804020d02060c060411010219030806 81
    0x2d81c000c0014003190504c0c644000562031a00110340400406802c50140f20240000355802176a02e01e209903a0740d080e00c50815400d006040200b60011007004a070071130104000c000e0103803a101c0c01c162174069551980a24185d004ca02094001003412101c0d2003900c049540080041c6103580b51781020080c22268024240e070003400344100900508001c00c0201c406901c240d456141070000030107030b801210221344400c0403180c0304105210307000d130780018022000c0d034000345643c944009100c00241602031140b4040300c000002c080c4903400c40340f040109402c13a0502d40003840000611001191010516510503c0c0d2451484c041c6081034420207001c84800c0c403c600000d8026201d400140400c0841ea00440d14010a01c0800000741c0c0c2c28010500080301600c0140701035418007003a08803100003030380b104c1e080043c5040020700390b54a00000142e029000b8140c82d50b220800c2c64555181d4600f1501a960305d1a800072510341948001111104010750f0741600c0d00109483e9070459800101900c0350f6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 426782455 1250 426781205 426781219
    0x50c0c0d11060a080403030b0f01080f0a1d010e070801050702190c0e19180201050a111204081c0c0c0b280503072d1b0f0309030204060b1606020306 65
    0x8150380c56440040c580c000050700c4031385992804d80350080540d1214041540207607240c6000003a240d802c0030307085070050741c01d00d05403065030790301d52410004201c00d01501180c2c02ca081030250040c00107500c6008a03404007010345240f1a1150341385400c1e250265212801031b0b00640303000c040c2030702903001d00c1650b900c9203655591107680d0700c1c01110b4204082c0c41503006003404020400811183c1e110702c0031a5501c9030070114010426030006002c07805849039241c01d01803014003842001000f4000c01c41403802580e50340e501c031619001c02681d201c60107030b003003501040d4500e261900540078000f200003060740107420502540c02c00c4800b4500d60403020b10194500fa810034048102160040011034003001907031025100d02d0900c0006240d000c000c04420748020010101c0d03801e40c00350f2a80d400c15548a8148020486a43e880002880d01c1d0402d01031320800d00c256100041690001c800ca084074000c4405004c5a03884580385595486510b205000c00400d00b00c1d40707400074178a81c01441d40035030010140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 426783705 1250 426782455 426782483
    0xc090b03190b0601080a0507200705120705010311190309061b080a050a060806150312030727060203070f03050d09110405070513061116080c040c050c0c0d 68
    0x35955403401c41001c55101a80d0300411070302d940c0c091a602d0b848868004240041c5c2420000508032011796480c0241000107900580c01240307041124500920002d0b107414186908600000d803959003501460380042d0401d20400250312044c410389846903200c00045044241d6094140c000b441010401c40300e99840340e1032202e2a000d450380d41e285e110b40c00e0711070301c04602d00800b0700422100700034a8041c000b03280203003c3c84028000031340c45500c0525070034010410002c59000902d404018020040c0103c400001c0001d450f81c844138a4801240142046258102c0c4d05092101d8080d2030044900580c4207008030780100b5204c641840119004c0e0070500d151183e10495082659002401a0750001020100d9050342c01d052089560140031481c2860034004080d003020081800d5201c3d010401441604440c7c80070424006607000e01401c0c001007000395031b40c00d9515101c50310300000034131842c0b8003580c0880c04d130b0040c1c00300d41c01a140200680f0019034503004100e4007586401c001d9425445110340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 426784955 1250 426783705 426783733
    0x105010f181802070501061a0406261612061215110c01091709012001020c060a05040317060109061404081212150f06180d0c08100204030c090b03 64
    0x106140d04400b98405661030390541005400d41c1d203554840c0700070381c28841082c8110190720082e10280c1d0054601b0340f4124510404041d4071a5a8a20031300d51071030040103204508034407007a035000d001c0e070b0f64903110701401200c0e000d182110700920955131140c5100088d88005884115443d0321009130303030000907010041c00658051600040202c49440e0740d11032000d070034008800d5103001d90322a03e01643e803034080104002013800c004e9184801c40c8a8262500c044804020f4065411050300d100495800d40381414030100a810140e80a5000c142030b01403c40b11000c020500c54030584040e144c2c011941d1a1107402c03520451460708091481c40240130125408105101086006400c00010b43d11074005d0010340300e080c207000d003002c402035131200e50440c003945480c442403441e40401c072074481d10385103003c41005c2a036070b6a6518a901124242008040110000f404415202100100c0d6280a8540740d000100c2c4910700010f0101100b82404102c165a03a030040b204a02010307003a1482d055000750 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 426786205 1250 426784955 426784979
    0x10317190305071211131403070b070f05060403051801030e0c06130b0403080307180f230d05100b0402071e0c0503120d050c0403030f030b0f0612040b0a02030105010f18 74
    0x209500d46040018100c54806c01b42c0414001400e003c801aa000e0018000081d175189250301c17880c4040900468804240300038800100c050340d800c501501c0c81440c5c035103002072a0317a20015a404082072815103001495109104103903450340d20b18001c00e510110075041001e19080705c0c0c0300c2c90b05c11005e040301003440e0406030003400c0198403580c0401d031a4100000080d1015404142e0814080d03803d01c4c040148071600c0c00048200e0365007840e5484692010744950f41000c56124145801c050712048000030801c001642813004c0318174900810940012000700003d91007005405420704091950709d41c501c01818000c440145d2081380000640359590012030704043d0340c480311402c045c03008200c4030503900890081075440103510310003a290604656000d0070011010f0710500c101036690100c00080d4444584651014100900c120b443d0381052150080a01c1c080b18115068092540890180c075440d000380c0b03050b01e00585501c00c481c210382c5021965040841900000003a12030030000b01100042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 426787455 1250 426786205 426786221
    0x9100309140a0b1812070311070906080c091b0f250804140105070332040902071104021806031b031303181a0f0f0a0201050103171903050712 62
    0x40d0b80c840d00e40303007181081c401c96400403156252038200e01c0340b002d80b80c601e040440b46d0040e45410045021041c450a071460203000c0d8019006562400d000420501400100c001c00032000b201c003020b450ba5401042c85912510420700c2031070303150900109081c1c04c0010050b000d0036a9550600a48910071907080285031449041950480d20009046c0b001c03120b004c1200c106c0000030300b09103241021503032303004001168441c2110b00441440c00c5609025440c2c0740c1d40003003050211421911181c40b00f000c04005d602401c021268941e04006940d02070a10b07000741c90b1840b281c500b500d070703402e4040c2090000e44d5000400c003e8454842c1e007800c0451a0b0b82002960007111070300c03502400c0b10150703d006000700f0f04915015542c0801200100401410004810528100554425154010803071540070314002c80c0c50700400c6460100c0e00d44440765056112504890180c400c20584043ca0440881e85100361080104140c0240c150742404070b0013502b0680e04010185040c0440741900301000c1e0445242d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 426788705 1250 426787455 426787463
    0x90201030e2407051c0b012609010b0d150c090924050306330d0b091c090b030c040e0403110610120b040206130f0f0b09100309140a 58
    0x51049034084a100b8580c0c541c8540f0303d00700b0300d1400e442481e203450750290b640c03000310085407100d0300084a6441400e900b042c0c00d40c4801484040d562450080d030810380d04544c8500b142d807030603003072020502d0810002811643c02045907404000155155806000320007076410a2254804000500500d50310801440040c14213843c2058954410044011041c80e48207500c240d0044040c00440800403445180c0714282514811011441a4980ca4000303400101580d0150011408a09104401140512400c403100981d5549920201254503c0c0c15140c800000199010810300407605040002d40d00465592100e03070500e60f5880c001c440c4d09104035004c070000f03100381d81020f40701182000303155000b80b03042a014100070305020780b00c107401d00164030103800c8101010204c2c0c2952100d001b25208020f56401c0c0841c07541e210001488400300610a4aa440140c18400202080c009043c0d56074032100910341c03060842000c4085000e04030f010402d41d42610002c40c070f540306110400c8400166446 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 426789955 1250 426788705 426788743
    0x1b03031504060605090f04050402030f010903120501060507030c140a021005123313150311011809020a0e0901060905010905031203070c0302010f050c091f0909090201030e 75
    0x210509200a65900d80d0041013804010b100d4000303d6643c6280d207100c80c03142a10005407030b0b80c840c00003c2c0303080c0064580c00e400e0b5190660b04e03414145d006030903d011050070345050159913a140c0088a0303522484001900041e2604020740c00248203000070014680c10034211121000960001030b81136280700d4520b0007080380000c1c0d5042100e070700001154417010b10145174295400c1201020101c129034440d5091783e0000c8481d8020701d41c1c8001c0c24560641902004100c80703400000c42081d21035690009540614805020414542c071980c074240c011000c840200c0c0c0154500700780c1002a410803021030086c01080b2100c0207280d00e80e0413002e030080c0b6071980c03030b0350b0120b00d4a0f0003d03181c001035412450007034001c104c45148034030010f402c90781c0200451505a401d00503d0500300c0c01003124051101c10036042209001c03c0901d070002030030004a080f1110036606890510002c100d45158440c54045120450104022407040d40100621401810082440e02d449000d590800c001032245500c5062 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 426791205 1250 426789955 426789991
    0x60c0c06040b3a0209130e071a0a0c03200a030201060f08031e090d05070f0612020c06040b0a110c0d021c05070b1003080d1d01201b0303 60
    0x660410380502e04514512821140c894070b6207240e00e1034840c51141c42e60f02e500004c240016444808590030b0001942108024600c41c036800c0a4032480c2500c0b440325006170740310094988030300d041d0480e110103809071660140c400c10741d0b8059410042d1082030780380c0c00310302130590a4801004c0c0803d8851038866800025054140401905901203039001005540d1040c031941c001303901003400c0f10204185a445241d141e1100340c0009070950220f40004155002d0082c000a010f110304800b80b080e46c030180c68101d545803101010100300e0242074110080e035840740001c900402c58904607030f500300c0c6c5214030100e0f40038103103030020000b6448040403040540c405031603005920b6050001c1c0b0261066000140031508201c6401131840c02110006040114100c000c900040f040321016402990b12194131a1a403d00c5a9004d0007007100c203000601c151018410410384175818030070545100301d0015503240c50000c0c141e00e401c2c203810000301c0709100a1854900d18034a0010000385114038030252516002d84 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 426792455 1250 426791205 426791227
    0x50708090a0206180d0510050a0501051f030c030e190b130c0b0d1e0b12030901020d0309021206100611030901050714070e1003110a14060c0c06040b 65
    0x14400400c504025008400640700595911044980b0481d01c010140340700c8210500180c4006030156004015200300324048608000d2a00900c0c841c440c8100204800d030b0383c41d014484400d50200318040404c04940710b6011040c002d600c00c0c2da05038114500060106070b00d100c800e1628501c0e42c130600c5502540003000080104940e4035130303484580c80d00300b26000740c1d29607150184100e81d400f514504101c00b248010366105642e0019541620000f0985620a00524907034028410300e1041400351080e101e41400500b000022101642c2c0182c3c0242a074594410040b0000d01420b481241c0c17011407485400b4103540108291802101e170480f8010f403c6140c0324000d0030441c0301c403100c480c490300706100580ca182e0b00503040d50b052907003091032080b890045401340c0e4280409500305041c0350b0125810b0045507a030000400c41501d10507203d204c4018480c2080003400304141c414074010050a1020481b6130400c0009042c40e09120001c449180c08000d001070045d03040798224003009080822051811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 426793705 1250 426792455 426792467
    0x9240f040e090a11090702030c1b031009050715140304060506031e120c0a0c0602030c0c04090c09090c120803220201020606041d0111070204060b270d0f060507 70
    0xc102540d00405620030b8542d40d0b139442c003041c0280a0300c50780a20340001c1c203140c02032049800c541041d0b416102c1410803800362000403944c0c40c0b0140d02900c60240c0d00c690a841038411072070f00641000080c8880d074500740d110a018620f102c0c42c2020003c1100180030741000032400b56002e01c1c4140d0000c0b440780f074090b05051404010700010000f500c050107a51040e0500400c0b080032042e5000d400315501c00218404030f142c032821410051170322031441400202c080d808009070444c84030040c10b58090746a040100000d6990704000a0100d0164480c204801c14031580000161481010701e03125282d40c03060702c0880810120300580f00300000200b00f001c903e000c1c00b80f40c104a4034410015550301c844d600000d540e00e400170a000d00450f03907111840d0003242c5600300c1c08880010301c0001e01598141c0e180d41d00998000160880c0224140040031484140c9202500c00310601581c0403e1103001081a5007000040d0801c0b0603000b1000d00d246501007196501d00c0000580142c101040c9030800510082403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 426794955 1250 426793705 426793711
    0xf080c0105070816060b0904031106010501090305070e250305010614071211010e01230c04080a1106041203081801061401050928060206060f0609240f040e 68
    0x1080740c02c00006000400b65402d4509011114440110f1842c042c0340c030300c0040c050840c034a03600c2030315001040b003010b501c5070314009003c042e03500b0b0b80c009903070700c00054600500f6400f0007840c139005447c040c02046403140030700d42c0c00000700c1a011500c0303400e40000300803c900000c0490010340c0b45d0005209881d04801d00c400360f0302d01d082245251000d00d44071420400b070b901000b0020000018403000c85141d0940281480c07101f148001c0060210000304040390b000c0c0c11000b15549102e520004460168210130b52b005c0304e911802030f00c0c251406540b00b01c030b007954440c001d503480341e02800b011400440b1081c80300e28462007a201c0c001c1900784004030b5445c4603c1e02d8140d02c01a81040b2043c0031006500f1000251240282801900ca0108078000303000049403003010f0749a07866100c9044100070030800c80b0004c4608035025140705455101c14003040c141d0310f0320007079004a41040f0840e06410308180380060040b15400e483c00d16101c04c002404030394850b85901d454a04042014042c0205e0700303003181c2d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 426796205 1250 426794955 426794957
    0x5090412110d0c1b05090108030a12020403030206010501180305071502010f050108031c1d030703080702061003080a02031902011b03061a09031f05180d020604080d150f080c01 77
    0x1600c00b591440c002c2509800160007008921340031050014100c1c5140c210300503150051500400391713104d4801554a1f0880b00c5a000051140300344005c10900034401c031001d0340d8055000d4005a03003040015245040c07815a40c101c440320110000000c5501800010090826040714050314105914000d00f500e1000c104c0382001840d000042005000000403501c405600c002e8038144041742c0c400c0040240b9140b51300c0711188460036210f06071900003000030901c051083d00c07098850f0300c46490480e03582000b00d902403030904900b5410300106425501910f1401c52a204a038a042103036905a848030382c1c4840c90f540503039151051180d658000c043e0f050090406403900300000c03403402941102e003ca0481c040c02000070001040003076914280020444000103440742d1002d503480c5580e200052804485001101090005400340c480b004148010030140c56401402c1c50f4485460742911903116080d00d1504556994440c82c0c038034540240d001c001d203a05401c0580485c50320116038206403c0d204568 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 426797455 1250 426796205 426796213
    0x20d05160f020615030304080714090f0f010608060a1707030c0b090303030c1e0f1207050304240b0d030c06060e0709120c0b0c030c120a05040905040c0509041211 71
    0x40002a4000b4000b030b407043e59080c031204102d141074046400c61003032381c0040101d40100040070825001901c91020998000c1e5184201a910b010042e44040b03002d4812000d02004d45004021711071141842e1908064010400c180303403503a9441c40b026024158400c035000b500090400c0003440035014180000f4034070711180318601001040000e40364880104a044113060103d1888119119007400c24100802152082d640380c6001d00c0744003c5400c0451540303902c252500028806038450001d80e401194072002e550050003c048400440c020303035103032001001e980d40c1c6000d41c40d03039030b48404419040d00130344a102c6a0703540d505180b026540250807650f02d000001d03003844007aa41c40440e5000311101145200b040d11500d00d050911078a080d4003500110002003911200c8043c00b100801c858440e42c4c0c21118001140f0f00103000c24000c101040021480c10710042140e890f242d040203600602ca07a103802003282e00c0d0360000b2441d810649059a036070f0b40d040d0809904641015030800d04001600040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 426798561 1106 426797455 426797477
    0x14160b011211030a020d0206030414100f050f01050121020910092c0c090301091a041e080a030e0a050f0606010f1b1e06020d0516 57
    0x41d9a142d803800c104282e60b00d0001504200141d0103451626010743d01d8080001c19040103000f5207640d0403d81526507011018461074812040c1520f0000ea241d02d40d40540084502c0200748041c054440d07070060040740c0e0003651200e040550300a0600c50035202101c48401703070260200d40e58000700200412a8860b820448420580c3c075420304c0450040b031403050b6091500c07000c41003100d0ba4020000810540e07042e42c0e00911405101400101d04d001d030507911929a94048020030302c40800c0c9038280710400182d5158012000e4201c0d4042851050300d80321501d4a2107402024418140e44640e841e10090080c03150006413900030041d80c0d9001d0300030418903103800080b1006800242181003c1c0051070149542401300421101e0070310710222160354a0304c0803d611907004002c1001c808031440007480b00d000612000410f6174000c9020b08200d98003544064403001d41c5010b0240d14281307 = true := by decide +kernel

theorem cover : BRFrame.Cov 426618705 426798561 := by
  have h0 := BRFrame.cov_init 426618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 426618705 ≤ n) (h2 : n < 426798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
