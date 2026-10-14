-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:23:20.354376+00:00
-- url     : https://prove2.me/submissions/c15248d3-a96a-4af7-85c1-1cfec28af78d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 3237417 ≤ n < 3417273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 3238667 1250 3237417 3237419
    0xc17010603060317030103080706020c0102090405040510060501021204060e12030c030304020a06030504050a03030209031501080105010e07050a17060a05040c0e090a15050d02010903050607050304050d03060602100b040e0106 98
    0xc010090089484240c034560201104241c2c000842400c07a41201d50090b8004d160000581c0c520b0040d4221407280401e0755401d0140440f9a00da82c05441c0c440e9103c0c1001c2c0c0780b03103c0c51010800441d8084e0300028115480954400503141c080b1048501381c0341729050814030000c207a400528030318124848141280404680600c140704000301840c041c5100302c030b18404540c0c54800403001c458080720054821343c0600b070072001117402030340181003200300907050f501e00b43c1d24900070002442c02a031000b2030721f81d03440004024151301314580980000d014034047d8644400c3c004004d0051a1038250041c0c070456080220b00c007560f40c1d1000100801e40944244800c21611718081c0500008100280c00b40c0d041d00300140c0310070094460b002149c0901032020389860300f00340600c007000f522a4422818040048d0300030000c0794080140d2880b5556540d80c0554170702c0c10340351050811100c820b101007454200042845040d07008559000d252030b2a507000900b5100c40e0001401406143c00741c060154a4488 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 3239917 1250 3238667 3238679
    0x3070305030a2309180405070b040305070306060b0306010507060e0705100e0307050a05010c080d0212010305070603150e041401110d020903010e0604020a0b030a090611030405060604050f01090c1701 87
    0x8401241e0f416400403070480d900348640100188500c0d8100c0e540502c03079403804110102ca0b58807894020380200111580c1301e03100c54207032942c0c6c1d00039041070314107038000c2c5030400400c10107010707000240103c200000c0c114241000040c000740200c803401002503440b0206880c500c002007010030000e00c8004c20300301c14002e1705100945a040c0201646d4000e004107031010400d828051050000c661060b540d480c0c45a106448200b0311350030a40f0f14003001174082219000088a03e280a406540650301501c61140343c80400340442e000010b0b1194206800c0d102001842c254440d415230042c0c02031403902d2490444200303980101640903140d51080408646006250000d5003d816010003c0e4020007911403030400880d80c656003103400a40c0300b60100c00034809941c0c458080c581160f1b441d600801c1003001c1c1d42e03805040d038040a1400b4209d034030101c100018802c040140940000c02a102000203040400d1180c0d503400050003216580303038850b004202000e21480c0d09950f0000c01c07000da0059035843da8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3241167 1250 3239917 3239927
    0x11030615040b030a0302370602030106020d03110d0525080601020d02010908090f01050d020c010b010e040c080114010909060f09060807080319030b030109060603060e0f0303060f03070305030a 84
    0x100c21903014518021529106040c005480702d42c05030150020560400f030200c08010442d10100f00d140768101003035007442c00402e80388000c13011511031000580c03a58180b06009180012a6802204060030411043c2002e580c4504941000f00140c0011400395140c072043e03e00c03115070410901001898541402c046a4484100c0d40940008d909490b856498904100c2c00d9410506010344554003c00400034549402c1a00000105040c10a41c0c2130060b00114003040381c10101e8107561030b94480710010801d60340159030b001c0b03d00044400f04a0b0900d03400c001802d8501c14000d4800c45403821026405503030040b448040100f440c41003d00c02aa183c1308050014000c51107108112400e255012548403030204101301035413804001036041c8803443e614020840c0d502d580001c10726a844e105904242c40a0042c500110f0003120042807251841c54018200c6a00c800749043c2500a5400207451120100444c2d400a40480e94405440380b400006414040c0f81d5200604074032000904401e066040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 3242417 1250 3241167 3241201
    0x90b0609180106090b070506010e10080607080603061006050d091704030503040e06030109030206150105040312030203090c010207140d02060c031b070501080408090105030a0b0307060504050a140a12110306 90
    0x44d0380c2c078400c00e036861074501c0044c002d1080003410f035000700c0c0040c4402c40121070b00d20307445441c800b040d00e1b40e00e596140841c1000c0060722920700242380d400400c01d16040411155802c00055420b69090502d4000010030074002c165149511903200d420300010f001e110459401c1420025019a0f908e55503442c069641e5403191049c228a00d090000144040c034040c400c5000103a019006000c070b03035441300000c66522940315800341c1400400c1c000840450f482c01100c40303010016032001a50b0b03084c09002c0501c1d120100f4070b828110350081d1028880030710720115895450300140c81c004c500012520009400c0d00a190310700d15540310200d400c2e0030740704001c01c55a01f4021004151100c540d03d92004642ca503904171009080d0480800010040794401c000855201d014208000b0f803200742800084d042840960043c0001603000ca4103100038503000708880c004204145800044036400c1000c28500c40e031078403414401e0100744184406000c0300c41c03103a4403c4400201030351003a16003d42c02c90111044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 3243667 1250 3242417 3242429
    0xf07030e0604080c01200105070c03230a0c0201020102070f0b10090c020604020d050109020414060312040f050609030709050f04060e0c01020a061a03030f07030216030804090b06091801 81
    0x4199000241810301e201250151048840681490105a00192a00300c5402d15052005001c012500c004040a115580c040e0790b00e41e03600d0a146019040040c03c250910700d8148080103009030303200c405050001240e203d040315082c2000741c000b1710300050340203020303001c030160000440000305010404402e0b0064414216800c1d0540c40ce51241d00740012a903440201e40c0c0541d01c17060210b0098504081c0000f000351142001050f550140e0340130030195003a1a003400680b00744d03901800001d1400740000070fa5404c901110b036041c40c4c6000c041d401e03a0000e40c0728a03401b0b07242c00039000600d80c4041c0001c002421001c0c8041c170840c2032055000800800c2141d06840107450301032140903241d800319680c1c2d6400c02c140e00801c1c0789061a00c90314020141c203620440e141c1c00c04203030880c4a84050011742620705200d011141c0350b00160801074103140e510014044042c2c01ca08080c80096071070015181650704400000031400400c1c000f0692500c1444849540b00a0142038065152410064941a140c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 3244917 1250 3243667 3243677
    0x604050106090b040b2a01050604050702010c1403040c0f080c0a0504090803190605040c020307060507020604030507060c0e040218010f08060d0204090203030d02030711010b0901030b0f06030c03030f0703 89
    0x1e07852204950403400c80c00f0f2003180503002c01c000c0052070f2508001d803c143c1c400c108429500c2c50b4100c0d2010356580c0300c10701c5031000d0351036104100f8039141501c12541e0000150000340300c20150a8801080707110400d411000c01d880c00f1020904bc401d5a10100010f80b0100c2004100d20707403900e10b00d41c0ea81403942c83e0030703200301d40b2180c01180c1070074103006103422070f0f070302501950031a220b154080021540ea0341c0542c1c00d00d030740c0788000605603036135000b000f522440c250040d40c0c1c0c0b60550304160054a0000b0101c40170755010340103010000f03502204a40d0070940080c0f000602001458007190300c1201004820b070f000e4004120310382103007000200d850800c18240c0390045100c07950f0f801030703c0490f802c851242d0301035140740c03c5601505054201002d114070003030030b6925295002c442c0030101d800c2911044009440c030310000860711002d11480034084011201e806140d80b5665402b849044014078150360001030300045155a207041010341800c010040c10f490303c03008401010500b0b44c02042e800d0380094 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 3246167 1250 3244917 3244919
    0xf0a05070b070305040501030b01022109010806040204060f14040305120306040507090b0306010e180a02030103020907110c04020d090b070f0f030b060a0806010c060609090b0c03070c03080907030b09030306040501 93
    0x5090740840d591035615454940c1440d10340340c01036005244014a190660045849044901500715060020102440b50392610303500d0203000100000030080503140a0b030f1040206005840d04003c0b10501c0080303e1400089810721f6002546041c060b5502c000c0c41845000405070044201001039842554203a80400c8507a0360400102d0b904402413103003c40340e03030080022468a5124141c04903400c0c40c09003131100601110321454024040403140102038503170110040c02145403150410360400c046142c056001100b405000d03071108603d0b0350540c031884c0c0c0040d4000b81100c0c1d6400220038190481411060381c40d04002c00340c011608003a0800002d82ca03584d8002c0b0035400381c820040c40450107010141000d403840341c16603180c000641a541408041c07034403000000c055016140281010100208082c070403854000704041015200c584a40b0b814410090143e61085030201102d8240c6000c01258032a441c6150804e40b0541002d0b00007130214013000109400080194012071041d1f070100074607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 3247417 1250 3246167 3246179
    0xa0b0103020910080601030908030c07020312040b030c070606080307111002070612020304080405030d1d0f0108040b06010905030109060e06060303070201050a0e0a050406150201111303020105030a0209030f0a0507 93
    0x24420010001d52004200c43c640100d107114400d040da1041c0d041c1000a961401512901c1c80d640045401d080e0429001451404505060000c0c407100340000c01020f081c00d08260044429001c001c2400d03000400c0810701c0c00605c402c0f904150014206c03002541e0f40d41d03015090070b1801074604541140185920410503049600c001078901c100c48150303a680030307a03240204a041c0650b001400a07101560709200214a555082c04001c2d81a4170f00d071035041c0350403030707603010500c1010301603c0c030b2481141a950191110f0b47c110344095817241e03004400841c990340b124016510400b1640140c1d400d58a4080c50034208a156400003c06035800b101702c0c0c8107661000c04040c1d69100c1c000c1c000340060310038058500303e18050507211607007283c020100b0502c240c907800801d08031084c0d0b030302000a192113065408501380d020300c0b0300d85104c030740d51181c180b0b02149040100740002003480001d0400600000240ca064540e03419500342440050507680c1151480c06840d5032401030000960f1a801110f07000154 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 3248667 1250 3247417 3247421
    0x60f010510021002071506170f03030c03070c030909020a0c050c0603070c02060d060b030a0f0e06040302030f070609060509071505030601020c0409021c0804060e04020405030709020a0c05010e03030a0b0103 90
    0x207a845140d000701403d00901040802035000040200c85811148949141c0802c6d40c0c004c400103420340382007079a50143d910004a26040b40c524110a8a0b0000c105002880e49100300b1079901030220301b414008411613160480e4a88815440030300d1041c13000c6040e500c1d80740c3c40a540320301540601c0440d1110560301081040a00c420ba440b100030818840c4248014284500a03250703009048500058961b541c0e0301b40400d0303520450300c8403003032135035500101156540c91040044030b1a40358001c3c525031815680195030380c400d480c9000300200001c01c0050401615070012050183c5c000401e000c14100000225558466400341c0f54418241d41e51000c03c035485141543d1040f00141d004000708070419003030000501562105a0f000202005e100d0100484100320041305841541c03841c1d515442c0020003040b2400340400e45100e02c0c01004104415503000489400b6982070250059481d0110f170010f03501c4a030f0361070700100554200100c8102c03100c4c01002840c46894001014082c6142c91801102 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 3249917 1250 3248667 3248689
    0x307031a03060609040206070c0816080a02010e060c0106080a050109030f050a080604090c09051806090a0206070b0a02090a08060103030e0105070b04141212010f09060f06050a02030d050108060f0105 87
    0x901a84110b001401c0c901e401c148090300f0500140c005894648507484100c446080c1703811902855110141c94201d5000181c0c07c00700030701c3e50300041d10034080300e58002170081c40300d4010b0701d10981c404a20317035103100003e61001d001840c045d42210f130708400b5480c245029200c11001900031a141030820070589016100f150356854140d0f842410b1959001d00300001400280401e0b103e4145001d40842e003148680710b0680940f8601300c1c820750041003a404145880e50051145209400c14616100103855400581740f8895004440031400d540d0903504000a00651160f00c0c1c0c450004940010300100c080f6205043c6c9000307550b600c3e4502d0f00240152103a128412004062190b40c200040225032412520300c0c090080740305641d9007001402da0508150000300c4503480d09640c55004202c20017803100410000c0545603824844581f4102c805c043c00b0400e0b20902003803140c001580f103491032080c41203810f0340301200b60030800b5584802c02c1954401c02201c3c1401c102d40c1c088000300346840c100c041d8034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 3251167 1250 3249917 3249919
    0xe04060507050309070b0d06030c06050c0706020106210618080307030501050a05060a030509070302060309010204050901080c100c080405090403030e190510090c030507030602091005090102070509040302150c0307031a 95
    0x301c45ca030f2030060000c565612007092814101c1c0d840d04007000150703100f1241d01c020203480d0b6078192542d0701c850420742011210ba000c0000d40e8901a002c01c0304151001d2181c44904920300082e445075458103022000e85410382514224816881010042001a801660007601596410401c40e82c032403041c0201003040e4011154040d0041c4043c8603028869044150b000365110107a9076038039034a5000c9031503900113851a04050f5008a018005030604410031801044000010b042d140c0003a008240c458007250540c02c10080052407142c107010014045500411740513003103c5403850b26040c014000d002c0300d0f600c00c41a0242c1402900070303240e00b440550b040d03034000000d00310310480184444000c05001808507542e95825200001082007440514002c42c041c0724096078a201c00010401020b0400302410b00380007060009a1a90b45c0c00942c80c010b0711070a40d03152070715417110300f4280c0c54039070091a60030a18003800100501084130b0400345005001a13242030003810300960300c40356000d1040d00382c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 3252417 1250 3251167 3251173
    0x70207030b010302060a0302090a090204050301200403060b03150f0f090d0921020303040902070501050612060402060306010c0803040609020316080c061303050f030703120204050607030c08130e04060507050309 92
    0x40c00076190100040528406a01f4014034000d06240403030510803c5a000c5280182d01280801c0315090a014150141c20301c40014000c01c0301110b0555403e0059000280c411135640d411524103407000c2080ba820580c0444510415140c090110f039002041110030440303158205c008580c2d05540040d0812a410481d16034017612400c0050050409100c28030300c25420501035070900140e1000c0c40184003424080002580d20069400c0070b600f503541c05407a950041c010904000c003941400300303c290300290b0403244d881d501d0720f0710310048454140b003010207403155100109000800503141e10202c0801d01c203600396a2681941071112214102c1441203901542019403c3d0140e482c007800240801000e254400c481140c80e13488440c0b600345500e60446542c1d00000d0703036405058000b403980e1b0b8030710080202545007500f0040800e405004845000307060001c0d4802d0748007004108000c1d81d420824a90312080c0480d940c001c030366060401a101a1080c0d4580004941030a2041e01107920a40c00c03c3c0c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 3253667 1250 3252417 3252419
    0x70e0106211e0501030b01050a0302010903171c0905060a021606050402150c030406080901090807060203041109090120030103020a0303140403060f09110111060601050c030f07030215070207030b01 86
    0xc15140d800382550301400442e5100282c10064020520248a4401102d0b00048543c118500440340c050b042e04614452440a802000141c0e840202a4141c99002089016803100b41d000030f1254081e042c018001c1c140c0b20038013185882c80b154420b801d0305000e00100c076081d441c0e88008a00700d1080405502d040d1800102030008a00075030020303130704988094040440e602c0e040f0300901e10b030381000d40b00c0602500000380810070a40e0003901caa41003c5001c0007046010b00645d241810f0740b1896070001c06441d00400002c0c1800344d104096488500b01900012031460041c0c8114021700f03841c0c403100302680e10601c80278048001442924180d0380d002c0c03c0f0f5041c0c1411078078140c410303001e12001924180b90810000c030010304140a0045440d8001300c01244691030791030250f2544021980c07040c10024260250b0141481c0000c202c0d401c2042820000d588412900f50903055104960000c0c1040000061250805900180079458214172911407026500e40d0b00049841b945940301c0680b4661b10580 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 3254917 1250 3253667 3253697
    0x306010b09061c06320f040c020c030a0b04020108010806010506030114030f0f10060f0b030105041d0102070f0209090604050c0405060a0902030103050a0c0b0307120203070309051507020106060216090f09050709020c070e0106 98
    0x12201d122307044c0a0046420040070346001078600103084c441100c1840300c16041c0310840d42c00c501d441380900404c902a0016604001c08900f690005216400d091b60103c2d00010345500c06200c00b10390210300200b540c0b003541500400035600c0d0921034220351418900f150000c1d85480a001203009d440101c0c040e07619513441c010800c00034091a82410210702d48402d80500c43c1d40013403004054043c801c940e80c820181751801003000e4810000c02612a9404c40b0081000113040410500741c0310b50708031000580c3d5240c800114503c050030b40c01003803043d8400000802444400555840312a01c9206800e1207152035020f68be030381c0c0c0019524400820504104407910051a401660b80451245400201d0300e0040d1182413600305c1c50043e00c00c200b51711405100440754207000e00030280034540010b00740060310112041c04015a8411800d54a0f5960301140c03500055400c1041901d41040403180480c0c1c0718a0b080c402540100c00030b0005100d542000614102c24040490481d0f0b0b00d0f88400c10000703a1f1f01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 3256167 1250 3254917 3254921
    0x41107050714010906120527060601080604050f040204090507080a060203091207050303010303030506130504060506040e0607020c01050912010c0807020115050105180406030501060b070309050306010b09061c06320f04 95
    0x81c2c0342d030a01e584589007a020b601c23558083c040d00380046000801c914100200007500050b80640054042d40c142030401c01510705c94004240c00c140d0680d40025054201e081190902c601a00000c0b031a0003524075400a000083d0040c40c007a0440d0f00a03500720303102e8080300030514410100000c0881c1c03c244010008a8040c1d07000783d80c80381020708842d2032030503134144403012108111800c4940941d100b05102c02420a44a03074104034a440000b0460b41c108204041d40d01d1000c0c15001e41007103400505800c407511034038442d052100d2444024007521414510207030661200b16079050040d0f10b040e4540c031108014280d07400885406071201407a0038161440d14200b6400d11003481c0d00144c2307510300003001810920a10000305512190319031501c0c00c1d850001c209200a074070140c4079500120051003402080703000c44905d45000c4a905940d40c90032005004003050a00301600498548940065508504605400d00394114464031018800e800864080300007180c600c01c0c0c1203045603981000d1400c0c80c0e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 3257417 1250 3256167 3256171
    0x3031603110708010207081801030b0609040e0c03010203040c050108090703120503070512040602130504050f070507021906020303070816080a0b0303070209040c080609060702030306010e0411070507140109061205 93
    0x7010944a089482c0d00b44182603a1080030100e401c02000a07032014102000079a50760001c01c240b809105080061000130101c0c0101007506109a55459400164240401464800600c0580250f44929050415480e0b0151911500e404596103000213141d12001142a1094a5002403035240165114a080b916034000910f000e060010030019213843d124400f20040c8201d102d2a0056642c480c00d0040071980d441070740c080c90141d07080409000200c500c02c240705501804034a4415201c0301c0500000740d40050f098031045101105107000f10b440d56001c80114030400e035589805920f038454401d810000780c0039449010010f01000045001c558268102c0c90309124024100ca05004c0c5a0300001c1c403c07101030b00c0c211101c90303d1180c1000a58024012950700680a40151900d03140c0004003949a202c007c1005041200071008960070340c2d13440d17210b680d880c0c4a180005885401034501141e40300d40034024000480328200203001250700c181c20301000e850440d0b840c41d512074104400032020b8400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 3258667 1250 3257417 3257447
    0x50406080c040509040b070909020405030c04020a03060b03040b0103060b0d0b04170c0316050106060c0302030301060c020402040e15090916050405190504030c030806010203040509040b0907031b0806010503031603 93
    0x2000b0000361903031100040360140d40208404d407070f00d05040c2d07009040b11500364801c0088500512040105503030220304056900000e90b0056600c1d180740e0000c42c0107005980160369960404005d02050002035901903069920401e0b04110340c3d003a1b003003040382c07415000f00000c01080880e030001c2d00040011081450f15040c002800f4106203180e140141583c004042d110502400340780c115042c0030090103001c0081c0f02c2c030308004e0000c0d025502c000b5100d1205000c0d4000f130000c406c0803038086450b070f541100c00506c982600e501d150b00309100b50b0200e4484147c0b09503c0b441444020a1005401050515a68211000800744d07a440c180c24071020380740040044240e84103041e20000c01c402c0501550348100e20a40c1c0d418000034051030301070492000507144d2811035000780300c207100644078140e11681050300045030000e2546c400c91202c1c500f40140e00000c03c1d41d0300c0c1c2d1308659503280e40300100c8801e4410300410382d40942e0302e03101410795038002c0000030031114001c00644004680038600034120460303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 3259917 1250 3258667 3258691
    0x60403080c010b091305070b04030506160203070c06030603020f03010b060301060e010e0405040302070515040522090f080d060801021e03070c12120605010c050705040b060403210e030a0305040608 86
    0x1004034001010b113038088443c40308081d030f8000741c542003000030b00800024000070701d40d080c103250541c3c8510740d80710002880703c1c0200b1410700c49451101d008109444c0035541c00018040c4171034880310020003034226444101e004012913101e100b0b07589418013800d1012003000c0d01c0c2c0303800c5030302e0001c04941c448040440b83d41070101c10740d040e031007503101d6000340791040340a50000c06101d80786c0028015500f004010181032002c042c4803d100d5139448003400d8192550002444c0540403011000348020303d0181c40003480003504881007001c0041c040050459030450020803ca0950754003103143c280e02c519282400400511401700002c80c01c2c000103181c1003c1c0e207280c01c000c82c0c03080d680c885002907506640040420403158514603101441d0040e2005403000b803910003500c40203513595566411090007664816a00c0759280d03c01500c41c0011380e40150b4000c2c104010034488000201d4541c4d503580da41c01e00007009040c1c11217040c14001030441c407440e410b0741d2742407400c0c0c9014011241490050607060640c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 3261167 1250 3259917 3259931
    0x9090b01080a050703090803090106032a03080708040b120402010306050102030903030909150a060305090705010905030c010309050c0a0306020c0c09040305120c0409020a02010e010c090602120903030403020301060608040605060103020702060403080c01 110
    0x21f804000a540305041540002424904601300305441700c0ca020030a81112030099007a200400c80d58880c0780c2140d50064400b1340300c0400d454400d11030700958000c1c414002000c00d80300d20050520300b289010f1030003a01c04005554480004907101d1043c002d031260150300401c42c55a59040c007040b8990f02442c0c00328210300d4884d0002c00602e404c0c0095101c00700003a2680244008804184410380083c80c00742480d00c40e091a1002003901c848002809905041d5940041d40500005116012480600600a550786900c074900500203402c407a14020146c86501068650303410080071003800fa40d015103480c1d00f070040c80c806201c0c204400900b04900748900b4400050700d8035090001c0c1c41c1100c4079800200d0b506415020040c00c6034040c0c02e203002003288107a41004215008a4101101244070f4843e40d40c45800c140868038504c01c0d984029055840e080001031482e50003010207000f10301c41d075014001c07911088011030981c00740250103540b0020401003040000ea00c40000e28400700b50400200d052 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 3262417 1250 3261167 3261173
    0xb0d0605040903020307060b04050403090612140702030a02071d1807050312030f0a06050603070e010c021c030206090a080d050601120e010204080d0305040b070c05030c0109080a09090b01080a05070309 88
    0x1e00c42800b412400359002082072010056107004644804009032005c01c454902610001c0001429210f1007080c000c50700f202800710002900445080d03010b010420703100d800d110302c000390342e54084210740c0014024550003040044a60305020b084264100b241d000507194410140301c4030509401c0c0804c584551400081c0e25142800000c1c5040c5050107210b4a80c645080202c410351001003803200703003902e401828002a0b44280075a80c119409103000f10481041c400144d49034600d03190040d40c001e814281e1503c45180b0a411000d203184290b0903a4110303102c0310a03090351010308501c020102c900030700c00202080c0080d072100340e200905240c56208a001454410b04482e001da40d641c0d000e940000d000d02a408003004009840411850200010b1405469000c031595015251004121028800105011040064400380b11224000b04a08010751a040c0380960000070346c0000f044d203000000482d00180d1051092052041e122061990b13607007241d0100070031004009509260346c813100f02c004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 3263667 1250 3262417 3262421
    0x270a0b0c0405010e01171504060306050405010507020c120a12030216030207030308011505030402060c01020903030f040e0c040806040308060a0b0708040f0e09030f0304110d0605060a0e0c040b0d060504 88
    0x409a80100e941d8490414000410440410349603134140041c0308030a100308950b540200c0d03400044140100075800243c00020007412850f80082c2002e030605090005011040d4095801905580c00b155500c1650314113205105a0078102000f454000b141d0940200d8010240c620910103245030040c0391980c00b041241d99103032052000c1c2c0050740154400d00406070014145801742c60441125403484184030390040c144e00c0001c10090113044041689075a4601c00d40580d01a00320040c00d5985800481e41094070a401502c42c507603034080e5450205030200c4480040310b0070b07151400041c00301c9946544003506c410074042c0c00340f034204400307120005080c072094018242c4103128502d402d9440c1e28129041081d100c81c0e030800d11070300c07c183d000e0050402c8008210303100c41041e032103401d440f40e13a41d0500c00314981da4400e0b00c5030400c4400182c04204180740c0d1026209070710450f4800c0c101919407507403004150044641d0401e4075401c0000341304200d00d04000d01004809000701082140d11000441c0c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 3264917 1250 3263667 3263671
    0xc08120112030f030605030304120c030b010e15090c03040204050907031515080304080307140c04050f040b070c020307090b0f040c02010606120207020603070507080c070e010602010e0303270a0b 85
    0x140e111040505008065101c03a1481d0350f0015440d043c07100e5828040001e81724842c03440382d08207028600008108100d03100f2103802c02590013080603405903a50780d0185c0c5031840c0032906c40400000b91902407640345409115203014070b61013800035086075116070900000384805040c880a03441a244000002606e00d004850000d03040c410100e00c441103460340142c0f01049405c1941d490300300348014440004000140c0701c8003500441100f0400d00c030010514103041140081d990040d0921040180e4a46410f0110707015900c41c90031007000750340c3d9400454041003000380082d40f54001c0c01d010415102c40b9003004864110050906c588070030700e00d00040c1252188201480980d456101c100441a08003444511200340340310300b90310300105540054282c2c4030003400c44d01030003400300e5a4010b012400007680d420f03041940031078111540319825058501030910039070b00150f00f000600b800e0154040140c030f0082c034034503070101c02c2135911800031200d0010352400b0b0007a602c945205c40000c58804180a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 3266167 1250 3264917 3264929
    0x4110a06050a02010c020c150318010203040804150201090308010b0307090e0f0403020609060103030c030302030a02040503030c0120090901030f02030a02060406032a170702010b030109030207050a05030105010e01060c081201 98
    0x1030752101d00d03082c06401d5621003000d03541590041c071800000390700d03609a0f0724029080264490ba4a655840341443c010030200815071096101104200c00c21048d09d008000344c6002d0384c01e071005141c41000481c00d90340001c8005001608010042040010560141d5003002590030300040d016140e0303403896480700c01140e603a0300755030302c1c40d0600060680500c8690340000c50000580001c1d81152405080d83c80c1a038002810540d0001c00514a10703415815203002e402c00809590b560111030301d080d8042c0c9035041400340641e000050a07686030030450202c503071038a406008042181e11795102c0000300d0310b0303182080c0d8040c007035100e030340c0010303503803a00100003a0485031400a60a840d0411080710f101c0c03503980d9008a6460008510b0b551303a000960807190900d406900c034603e6607540000c0303014008001002d80c041d030034104154105a00403841c00d099510a40315410115a11020582070700d9007840741054400c02c102c01809040d1286080e055041d01030145140381440790840c1444a8074240c0c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 3267417 1250 3266167 3266177
    0x90f01110a0804051003020703050a0e1c05030a021002030105030a021201020d0204030b01150c03090509100306020d0b030f0111121b0a030204030204050f0103050c010f14030106020105010f060f02030405060304110a06 95
    0x1c0c0010b1504251715a040340b1035140860406140707036005840e51141554002c00c1c0848900c1c50100741d92076900c3c20381440103243e0101400040c910f48640e50350010803164015026045180006012600c02d4904075071b0020010700c0c20100d15000d00000140b10740f50b00c00503540806c41d40b000d02c51540000c2004500c1058000301542c58406021080c031070340e08440c0100044910664040780e801103500c1c0a8500840700002e00b23031641c80818007040d8003544010092800400d1180c000b00c003c2d480304c000720f43c0c15016035041f40c42501d40da81c00c0b60b00d501d4040074000c20508c800750440c4401c07030040d5480100c0304411a0b8500301c020b644800b58000599040009400050038021410107016054128152507444062075055031386031600c81d07140b44c040c01d04006000d400d207100c580c843e008003508069406030841d0740356140c0500034081c020900405c0d03443c2141c14000a4824411791002125420650256081600700820003030603500c06032080c0c940e00914240000c0c1c581d15408600018030701f40c2c540c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 3268667 1250 3267417 3267419
    0x7080609030a08010e0f0a0b0607020d030201020c01060b120103110111031606060504020c0a0201080703090c090606080612030a0302030c040815010f050607050a0602070503190206040614010605090f01110a0804 92
    0x1403c40605800c003010391030798035050100080b40890890b800c514902004900c0e000302c1070100380640502c0c00040c0d4090f0091520310245034065000305134403880d003402030049949500c0c941c14244184141010300d02000c40c0108003003101c170000f00c42c001c2c105140114080c0300e041d5003a0700e550421a21014071191640c850000c20003141300b5500144030648056003040810f000d8652104403082029041c0070403800000c4010b4400d40c04840340341d92180c003c01039540c40f00c01480c006e0403580140c9010482880104d102460401c800c01a206c1c0c000e0000c500d410380c0309400300c019400c054006030818006110214000ca411300c04800b02600d03240c04c4184d03a6152007102e071055003e41d480342d40900350400c01403000c2400450071025071a0002005a52031500b85045031a5100703034102032a900f540c0c0c3d11807024140c2d02180145c0601e0041d001481581c66900303080000d06030030312540703011800030031855144d820028440b001981e81410030010024180c0a8682080d00141080b1003240740020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 3269917 1250 3268667 3268687
    0x304031202010c111506010207120f02030105010602010b0901270c030b031b0102030f03040804030606060c120e0d030f0c05100f060b04050901170109080a03050a050601080402030706030e0708060903 87
    0x8201103c0d43c0503031408013130496180c28025110b101c1c2c0a030140811100c0c00000f80346034000c011100c0148098481c07075a0200142c00e00703010061407150101d00c42d50070440002445071050040740f07440c00d0300820f05c2d44541d2030300400020b80028149503202c55030100400545600c3c00e4820200342544903100031845480c0b0074200b600384200c1d046203100c44440b40710740d074500c0d0b42e001094072481c40c241e01c0304503a20b07155070400004071300403580014031682c1090804a4950741c0240404d100c02d1241403c490004041c0c501a209060010b00c40d0380c20004882d10300c00807074031460000440510500344a038500629450382400c041c844a40d00c103040744c5a2041301065202c030303c07031100208043d28071a81402c0c10900060740011061160050905003204000304001c42036020000480d0f000c2d00d42e5603101d41000780a409010308403000b0345020300c0d100004019501401c021841260300401a1041c0360404c203040c2c004040100c065030306441341200201e503400b000c120041c01540d00c031005580340c5000c0781c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 3271167 1250 3269917 3269921
    0x1603090f030e0f10050301140a030203011a0306010f03050a020d0f020409030e100203040b030a020705070b04080105011703090112020c01020412050f0f0d050a03020901050904021602090a0905060609130203030403120201 96
    0x8100e4600500d0740c041201502540017090340c0c10b680350961400c80010400d4006116940140c001070340c55441c00c4000604220165882c021000c000d030251042aa41c0d0101e03821071054610010340313180c010f20b07110f100514080d00008000b40c411944002c1a642640101e011580d58140c12804501d030400800b105242040320202040c0251008510f0141404001c290b5800040d004840441d000304001d4104001480142c010340b000c2d078582c40e21540d0702d5180c94043c24082c0b0807803048055010880c2c805074000f000f01e600b04c0078107841d030841c05134035881d40d94001d41c4a4034150159560034440031a040c154503103015801c41c0206d0081a540340e1a058290a04080d80c513404095403010074161030058001040d5140112141001070b1160311840060714031b48962400c10b98002d10014444543c604420003003160203000b07a90500d5107130703214000308048071030303514014001b60b00031800074030b00e07190032400140d00c02c42c00b001d8140403003880d41c046072031904190821100081011001c1114030303424 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 3272417 1250 3271167 3271189
    0x602120907080606100203040510020703200405010b09030d0e0f0303040801060302030609010507140c07030b090a03021e0a0b04060204030204021c0f0507050a05030403030b060319050c121603090f030e 88
    0x2200d2849020005c190f000e540c0e84114482d041c06a81c0103445844024003e0102d81300079074010004011040d00a1007828008480440142c41146001c00204503000e00005480c80c280028004040e03460540b241039515400c1f000045502c0788145d030480f10280c40503c06080206201000854921b05504c101801c0c4180101a1200b50f850003041014599103d1100c01800e205500003c0e80c80d052480c46505240b617039000540810a900144443c2076800110b160313100e4041da003500d15481404460b690356154a808a00c6582e00c004102004201590142d5802030b1240200524040d983d502040076070b0032000d2102c0342014042801b032001010741c0030341c40c02003e001e50200024641150081c10301d00803040c01c1e40400c03001000040815000c3e91003100b20043c010060b54807441c10299100300c8078258901c10800078103001c0403880740d01b4100d080e680711502c00b4046030481e40c0d4029404621070140f1000da020141c444001e00c0204540d0600000842d000b80d40b031401540e0034005000300541c1c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 3273667 1250 3272417 3272419
    0x10c111005160804061803110d090e07050d0b030703080a090f0308030109050606090a0e01050a080c030601121e0308010302040605010c0b04021003060305030d0204090b0a0b0a0c0602120907080606 86
    0x408042064100210b0100382c0c451000d0304111032151140d0030701c00001c15260101c080b01d82c1c82d03c0c882c20280358010480d04644024241201c100024840b408c40351000c103440380946021609010440c10f500a2000c0d000c18400d80c1c00000d045065000007915102c143c1c2c0c404d40d203160000550031444e40c0d0040710b20001d00700b1003e485281d50b1442d0340d222920b11051245103416aa80c9002c41c815990f480100c1c4c01c010401030202038136545070700907038400c41001c0c4282c41c400c110000e80081d20300c4002c5002c4840400050140030b00780c0c0307041c244001030b030304008040340c2e1120183e48000c1401740e140d0381c80d4001406a901e540441d03041d4411710088030110740015042c0154001c0c0b1300009840100c8481c0d00a60548001d4607289050400707502406841d0801449800b000c2080000e0f60401c0d03016004603130700e60409000740d044000602400c1d031054025480351210030825850701500800302e901405118010052410314000011031010030188da41d5000c07504001e900700404582080542d0304003070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 3274917 1250 3273667 3273671
    0x9080c011d0606060a03090501050f07020c040b01080c070302070f120507091a010315090606020a0501140402010206040305030c040b03010602010f05070905060405040b04060308030c12010f060f0806040905010c1110 94
    0x41401d980940d40c140c010030300f912441001402004081c840c1c3c100d842160350010003844a41000400501800011610301d40180b080c040c040c2c200d49882e00419000e000c040e1500ca10340e88600e01440c5499008550550952150354400180700c9040115080185110810744040c45030900d003541c241072003688401e40d802e0070156410403025407035054810910302400d0004010040380044601017125034440400c82e440c0040000e0240d40100e8040780507807040c8000c0100b0303050f80f8440c0440d00c105036400303030041e80620001400240580c004540000d0f20702410790901d5a102d00c1520f180d40309811400c018ad4685c8196100c0d82940d0140c0c0c0c0e00103199080944041d4200400f040050050344216442103450310030003000d5880715402840039540081507996a0300e400c012800c511740c40382c541c540e100705c04d46000203844101c0400c401c00b520b1460b46c0b0190344008002088170107503c00386c100756000303507614144800258240305507280b500907612442c0b540382c8001c00b2581070441d0140d090701168 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 3276167 1250 3274917 3274961
    0x50615090c0405040b01020a050102031014090103030207030209040303090b040c081b030303060607020109030609030903021008070c030302070203011b0201050a06050114041e0e0103080301051002030a020a02040e0f0109080c01 99
    0x80c112401c2c0e9043c2c41c01a01c0000303902c0b8950004070701e8050416006001c651000081c08030400c43c031074046054032180250502c072084403205201c80d03400e00f40300240040c0c021040a000501e0083c226540141c0213141c00310300c2c403810380c1b41d0b444000003d4070f044400c0d0310310000c10070041c103051100c5c55481800c4231211a0385601100400e80700d11004140c103110315000512002168052030020025503080041041031210a01d00a09030342c2c00790000341c1c42540d02ca400c070f107080c03845074400901c01c01c00c913550300958201580e02038000c3d4010740003c985c19501c0d0046805103c0000c10014020200380e800812981044e000e00400ca40c407a41240b8100884000400c1541c11780b401190101c4000070b4212a0b20004100c40000e400e03020340000400c51000340000090014a402541c10ba45007141c41403c2c05c400c42c0c50590742d9114203210318002d604000b4240c00035203021341c13180c0d071500303111801e031150405070480032404c4840003101220703440703408154035a5400c1c00b4070074084e00850000c02e003000c003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 3277417 1250 3276167 3276181
    0xf070f0801030201050c0a08030a0207021f12180501020307020105070801080106050303040308030a1d010e0d030204030209041b15030207060c080106120c02010204030602040b18040218010503060d0503030405061509 94
    0x40c000500019040c058006102c0c01d142a0030002074003000c2d0080082601c0c0c0c10120051400307544400000d03803140500c0b61041e0a03415a40981c030000d0059070300c0740030071004070307092080c0600707001d0420345890740c085234545002c14030a0004502c03500745640000303454034100c07501420340302040e040801c0c540e00d060713820b12564600200711420b80ea00b040c1d0b82501d036030700c9941000282038a40364a61101004640703d0124082c1500443d0bd280d00b69015101700d0048440220201c2c000c621010390710600050219020610cc0780c12044446010f920400c902c0c0d440380a041c01e107000c034004500000e54001507510601c003080c41000c4080180b4a8030141c0765240501c0103245010b021002500c0030742d91544201c80d60300075030459005580c811400d5441d52740e5601d4404c400d4116000c1e0075440140050b00321402d01c3c1500c01c441c480007a0310050742c1091558801165190002003403190000d00078070000000c11000c001940c03095110340c1c0100a03a2400f10055201d5105600d006402012070300280044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 3278667 1250 3277417 3277427
    0x605040614010807090b0a050d08030a050115080c07050c0405010b040302040b040b0105090603070e030d09060206070201050403020304090e0309040501030f051905070603050c07150b0102011104030b0103030302090a0801050903030f070f 103
    0xc9509101000c50b51041d400d001800c08891f90380542c1c0d000718010806020010341c0d80242d4070801c000801000160782e9108030700c018594042104c800500c40380c00107502081700f81c01034082d141c0140110f40440502a011404881003a0401d511103140420704000314a000e0203403030541001502e0902072a402400003811600400c401c0300d120307407004000903114610411081c00c040000508403407084402a101500c11201805800014001c401c0043c10036401409401c0c0120344c150300070361600f450001094002e20b6006c09450450008000305103c40e540d03405480c0c06980180603c11028640e4036005103010b2501d0380c0308810b01c3c2084481004200003043c0041190454280401d0390341d1503a04051040c482c410700140562101000c003805030700c45c3c1d402000c110a00fa0000c0080300324203803a11009005a120040c4000c1c010f000500c0024840c1d00a030580c03101c050201c407141e6894402c41400d681c803c40d07004032254008410000b030300300c000700d4042d0408a64141581e503c5242c1c0c1000340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 3279917 1250 3278667 3278669
    0x30d020a0236040b040b07020a030e1002101118090c030402041a040f0507080c0412060c03150602030715022d0f0406020106050a0605190f02010605060301030605040614010807 77
    0x2140c55035407100400032042c11980320007044601d841480703610703051a000a810400b83c5040d07860030040da002449075400010f56204080c0c158440700f80c5146864108290400c440c21035030210b0241c088098910701d128012801c0e8000c4a100c2d8545500c80720001c80580b04810105034410000b100500c00002901c0702140d0708160141c4011428820300b802c00040f004007440d140d07800a107011514000c909485c0e00c0103000311900c1c1c1d12141c4a8aa01403a480540180c2c0103d00c40c14a022414000044640d400942803454908000c61302e800e5007800c80d0b104207403640c00382c0d0241c0c02c0041d641c01007002000f0501c1c0040e0f00f11000b141052944059031110905240b4201e50715008510000f0002d000c0070161981406103002d070b43d641d140ca4141c000d000c1c102e64030489020305079800380462414000c0c0d040d00c085101d4220032824140040c0c50468109401ea045182503541c2c41b400482e554035800700a5010b9030041c540444d8074186480c02c0c50489020303036409140c011031100107015012000c21200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 3281167 1250 3279917 3279949
    0xc010c060b04021204030302070209010905150103021b030406051c0504110105160602030901020405090906040209060d0309030204020301030b091009030203090d030504051801080d030c09060813060c020c030d020a02 94
    0x700c00c200400400d0007441348055215020242c00100000c060303150b0000c00d42c50744280e448100030b0340c0e103100b110150303202910b1400c00d045509000c0c02d52035100354007070a408a48440e01c440d4510741940c095045500903001500024400901d407081c90450312041680090640810000d902e03098507860140c00400d540b690402c00e00040144021144c500007484a50700710104556034200460014000e42c03142c401c0c14001c035100400070740c800030f000c90010311440e0050403140c6599224401c0050148915104400740300c1e0809000c8003582b540d01c0650302962064603203a4450500c8900645003643e41840e0300a4141480c8202e8002503020042d22456103064540b90102160351600341c8035400f0f00d810503a0884084510081e80a46100302c0f42c2c1241e035124251203204132045e400300c0035a0009041c40000c900281010000c1c83d03c56002158402c07100e0001048890b950b45d0345034147d032031880880e00140e11103038480d03105107070a000c2c2c1c1c0d09141d44d40c00180168400da81c00318100051000c00f003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 3282417 1250 3281167 3281171
    0x3050a0e131a0301230414010908030a060b0a091503180b011a040b030f040305160b0402010f0f1b050307050a030203070b0604050708040f02041803020a02120c010c06 73
    0x21095a40200412415504001c11103034241a034880c22900400004000300358892450641e0b80365428180300324040300000440c9400710308200221481c11590140c81110441b129903e9540c0c506001c0c4141180300780710b200780e1940c80c01d010440c2010341d15035030850928208100141115540c1140c039031022240c0145203140030f00808902030b0014840800140394075a202001035081003100d228890607181c48000d000b5881d00c0c1103a81a2607409030340074a420400081000c60240300706c01d4500381c1c1c070500c245059071400380041859288180800021100d003c280802c0c842150303004002107140d9403440c0b919070f000070b814002c0141f00c103004178103d8040e41080d031071140c1071000500131a880290440c0c1160550740048c07500940e00e07030101c1402d0f50240361040c0442d1952500d401018026155a038441c500c0ea25291120090182d08200c01c0381c0c0035507209501d40641c01c1000046a406000e074000d00900c6005006221440d20204000b50b65078101580d6180580c0c3c001076008001a000200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 3283667 1250 3282417 3282427
    0x5030f090f03040f08010e0105010605070b04060902040e060a060501050a090306110c01060e0901050105010c030504050907030605040c200303040210050304080d0609020702040b03060108030d150e040609050601080a02030303040305 101
    0xa9508048140076108110302001401103255110340700c03024102c030400b00003004400078400c1100d00700c2d1001e0040030b001810802801c0e0100e40c0c489461a00140200000600c261040e40001d003111040481036123550446401c01c510554144215002040d00f030a0261034141c040d07070000c0500c401400010120755442c60029404014181910b0884100400030018035403141c0c0c2003c50748104858040f410340c289000810701c2e52040c3d441c441225850746601d8102801c00007009841c06009004100701590762100040c03943d01c5008100c5002121307103510800062400c0040c204c0b46919811041c20344c01041440f00603102e032641c45042818928210b038480e01c071454106c078180724400500c403800d41480000b10b0741c07a85039401040840e20031141000389040c1c001c1030680303840342485036105a41081c8040c2c1c192600c41c1d0800b54600700f01c1c05c20b504086444564601080d20180c41c180ca00700d6231f8807190703410003e00b0408180036146120040c40144919400a5500e1000070001420440d011503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 3284917 1250 3283667 3283681
    0xb0a050f060c0106120305030402030d0e060304030509030a0606060504141e0108070c080307020123040b010e090c03030715050906090322030b04050a03020105070e060304020402090d0803010303050c070b0a05030f 93
    0x22002001c1d00e085c80902e406007826003001000341e00180e0703040c3e100380101c00100c0c0308580a1048104205c6025056034250761f155101601c080d0440d6850581500075010040009006d6114050240c1425140d041d00c40c5c0c08d2036070200030b0306081180140a003010104c00b4041c8142e882608181c4d40091801c001c40c0d42c0c5229084a9031924450b0080c0709034000320500103000e8040d0440d20030158113442c6a100c00c0340c85100080c58801c15940078288815210040c005d104011048035031080100003100d4010b1106404680741d94840c0ca82910041e101803022501e90f0130300d000f0541c008111000806039418070080640e00c0b4816035a01d440ca0045440c50a1080c40404101c03000440e003015140005103068102152903110b804400c0b0015460701d40002c005501800c0c10340c0c80e100000e4090341c110303541c070f42c02d2100035070007102070340d500840e01004071000504d10070007540a980f20369290703a12505616006490010b0380e41001c40102024811508110b40c414190381d4443e00204840711203860b811 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 3286167 1250 3284917 3284921
    0x30c050901140d02120103060507030c05070b040b04020a0807030b06100306060225050a0305030702010f1b080306150415090801020301060f0507110a080a020a050d0308040201140c0703150b0a050f060c01 89
    0x3120f141008082030000020308c05154012441000c680d103040c015006494005c40f01881050001003c82078010040b030081001102c80540c400d101070042841a034a914100303240c082540d0046640c2c40d981c00030013074581032440c942080c401081c10240181410031402944461007940d138280c1c8280c0d03d241c10000d40481c10740c2c14004010240c4003048030b51b1039046c8039850b64003440301640811828541615814030482c10f8007807151001c0d03d500c4031407510b9030302d005041d44090305141c8d006403d40720350312680e0070510082004185803040c0090521889a018001398981d9100d07482c2a48140010850541c100414102e00045460304540d0341c00395140070744091000741c0d2006e8000d00c40aa004c03480000001348540030500845040300029600c000304880000084001000503902002140055001c2d0188417500700b0503801c00750030701c0b00200070945040b4041d881070b106103031121140c071600340d401d10414800e00400c0e00c1a600301810b2401003050404a8404540204400500082403c0080d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 3287417 1250 3286167 3286177
    0x3040803070306230f010801080d0324060e03150108030306040207020105070501110306010e09090c04090804090510090c0201020901090312020c03010203040b010801050f090606010e040b130606030c050901140d02 93
    0xc803216101c6115400c07404c0305281c903810f400038000c1da5401c42c01020b560240c0500b40c102c40c1c599004180c1000703d0740040b00038100c001006600019048182d130b401c00710413554503025042e245d5501034a0b4240e902050b24021040d0720300442c10030f0041c014890400702000f1030364055400c0c1d60260b0b03684024030048445100381400603010f0351a002011600c11401030042d8090b80007660390502c0b0f06003003001c107c0d000c8010703924040680d0060443c580181426002892b0440c0a0391802c0d080994511100c1e00b5600c044403034020000d18014240b010401a10954944020a01c0211304029140002030315408140c04080c003c200d402d01e143d02c9440c400c00c0041c15801001c0c0007591a41804d24240c040b88401780244209542041c1c0021003000b85845041d00c0303001050020b10b419120000152061142c075048250490340300c08907500d0b682c440e000c580030121503681340010100c1c904000101200c0400c4440410001e0401c10441c0a85c0d011102050340000c2e0031b200d0b07540d5801c144040000f0f22032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 3288667 1250 3287417 3287429
    0x8040311150603010c0e0603060d020a030803070207081002040303020c01181e0807050306040f080313080403110f01080c090105030a0e06010303020d020105070e0a0b0c0705060c030703020f06070503040803070306 93
    0x440e450000540c0724005254041d8205070b00a0011014811050f40e030034880d0b40c00e09070454020710010f0450705d01000c0541c0f24500240901016503140d44034554160b2084440d07001591000c1c0080103119020030000b80d004050190071410142159002074132048406c0720a410486000c4100e0000300120380c1c1c1d500101582c81183d44074550600908100151a2141c40303500d000788100000d4606000c00c07010711860f4810a0116801d41e1070b81c40d08a10381010f003030203056009104000d03001840390001000a0f6015000100729910b5490421113501000341ca00c0b810410610148a912103500043d50641e64090078516200d507070303940241d4010103007001040e04900c12000008245a00461009192040c0703a000707125643d14510240c0f481221362010b10f030000b0841e202003100369160006418041200d01c25900d00700c1c1c0d69000555590800b208a54103600001000010184c0400c40c650010708030401510b460700d8006000341890100030702c045c0941d200000020750043c0700340e00100241807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 3289917 1250 3288667 3288673
    0x30601030e011505010806030d0f050a020708060106030f050a090803060402090d02030a0f020a080d020309040f02120403090801061d04020909120a0c03090902070f02010f0306051503040302060705030903030708040311 95
    0x40c0c86040c98240e07a04130302c9142d01080d21140824071904000c030380a134420303a55840b900790840040000300e4203030f44885005011409448404a9030784020705c0450700801e8165400b1511010391030700300f42240c80240079041d00500e05850400041d07045411f680e400741c01240e0068032101d1a0000c62820b0b052039100a502d070103020f03110070421940c07940c000c07550340c026603d4140c5562149812540c69910a0b810740242e481881041c03054074180c1c000d02883c4c812070202500b083c42103201d0200030501602e04902190030010f05201200d42440741d64001c04104020203000b002900700d01180c03200107000680100c4c01c0000140034803508003d000c58160740a10300640c1c03201c110400034903a542d404030480004004480016000c1010300a5556854101424862001c8940e0043d90700c002d1480381081410385a40e4009500d659910041c1c0450b5100000e0359500d15052038000c1c24088010020402c5c04400d01c2481141a000016a540806103040040e482d0b10f50b07007000c2c0d400314403080072180c00744 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 3291167 1250 3289917 3289931
    0x100315080a030e0d051507110102191404030c0902030901020408120706060501080403020303180709060807051207030b0a0b060f0309011407020309010c03030b040204030210050703020d030501050a0605030601030e01 94
    0xa000144a1000c1800707980c5040703da00708101005800e0302030a07405086507001441e0385d140c03c1d41040c16290040c240c0d040c0940010848801ca80c01c0ea084078034402d800d1042100039001058202c0740c01b503090203080c0d1100b4982801c40c2c0e205103460700c0c1c60080400d165408000288048001d5044901401d591001c944141d926189160300300e600c4208101c802c0c4c1c3c10040f00080350b50182110b80e014549c150041d5046a842c4950780000918120b103100251203846c0000030040c19900c18000981501c01c05004400d040405001120031351400c0e110055102d41402c001088840c40495041014440040740070f48000002031410302403000750b042021800418040360400552024084500d0f004078036156550307803282030340c13240240e07403509020810324448100064483e5004604500004000504041c1c4070b8001c94003200100c2000008901d000034050141a01000078212030845442d0611696062001146d810b01052041e0000e02c6004408299960b0081d000494480e04004c000c01401e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 3292417 1250 3291167 3291179
    0x60d0606030b04060b0901030305090f0f040606020f12090d080c0703020402040e060f01020703020105030a1508030c01050906010806010501090302060304031b0501060f0e0906061012050405010203010905070309050606100315 98
    0x100b010341d01124402d1400300c441040e8202a104581246c4c1c00d074403210301b0f000b1940144800d60010f0f5203191350084480d80b0b0100c0303664540c800c65020301026030040020513045c00c00700345054a440340d21142c0600a00c260021907a803001070307148042e07101e40856120f01c612211140340c07044c680c000a40c01070001c00c01098240d40c1c10308261155804841c00c0300620b40c20401039881d60b416000103400550f0800c002070302e490351034002c0e0704002c50324242642400d5480c20114290b422041c40f005060b5128014040e07503840c108812405031444c0c10180459514240019168403d5480300901820300030000a0516014186002442a04600c0c11416414032300d4681c0c001c050f6801451764070000c0c55400b091440051442c0c510030030841004080a4680700100039250740303044250b01c00c201135034401d03041c0244540101c034062446113002680f40e504083c1d0f208140c680c010040400c0601d02440071011030800582c10f904000165185089082144402c034041c01c460078040600e18005100080c0d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 3293667 1250 3292417 3292433
    0x30c14061209010f06090915050c0c0316020109050a060c0615050603150301050c07030516051c05070204060e0402130c110f0f0607090503120a03020712020c0a05090c0d0203060d060603 81
    0x20300c86404100001620340c6d071a0760031120416005400702803035001e002c0040115901c015004105280c0c600e0500c00740d481107624603440007442c1801240344882d84011560030a0018014010458039262664100700c402404c110700c42030080e101c251140c00704141e0801c080512b03809454060800360381c034540074465080445101e400c40b070103913203018001a1040e400303001380c0366203d5150f0399075880d08003a41c078188031004409a050f58140140f0850390100b8903854000703411407180b922090345500441c01040103d4046a203c501804c8544040000581d030340c55050a04084a040004601c400780c5412151090400d00d12907952150780301d03003003524500055441c240503109084804941c2e031450221b44000031032180365095070110601c0100b4071208005001e41c460240f600504094403034032842c0240714101c0031540541c02140e500070160401c2c1040c60b000c0d01060343c00111030f0600048072826441404074094119501102140150f030b10242c0d05042d50760400f00600540e51a0300780001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 3294917 1250 3293667 3293681
    0x20d0b06010206010905070c0201050d0b0306011806050105040e131406070207030501060906060f050c0c0612010303030b04091509020d080c030901120e03070201050901110f06010602010b0a030c1406120901 90
    0x8050703c2032100006001d151401168401c00c4a03907504042d10002c0e5005480f1504032a11400c245ca480f50302e03100385924100704490080000f103444843c0c0034034007401c1404503103c1c1d800850400c00108000d10440310401282c0350842c00700d80112803010300701d08200b040000380030101c000c2400742c10240306a00e82e00140c098141c83c00743c4001c00c04695208500c800b251018415600803480072a41406103e000c1c0020b45002900c0c6425140c1d007010441c00076143c0c3d403019203d00c9042940c000180281540b500c242c1d610304a00740c504001d001c04c592a0b02030081d0890000504440e21080000215110100210382c0117034004241e903101c440a0003219140c1d0454140c407400204103500035105d4201da070140480d40056000510324090b908d400450b10755124154a5044c40704180001e1115141000189a1110340c2c1001e07010950420400a00395506a103049100301d0303018a0500105400c00716400840e450082101c161500020103c0c01c90b000c0c851004442201c8141003080b10700c410b4000007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 3296167 1250 3294917 3294919
    0xf010504031d0307050d0204020f040909060c0e0d0f141009050607020105060306010f0306021e070b0105010201110903060a02032502010504020102060601080705090d05072705151507030903020d0b06 87
    0x1240380c80b001030600d03640f210140309055208980c1d102c40c80160405500805105e0503240305c1e40d15080c1c0b55200e02040c0d9203112401c0b0348981e45d45183c0401d860740000006007545007140d09085009113030310707607102c010810500034014020002c850c03900322100304640644182c42020600032130056044c080d484080c02c54524002d54280000210240340100c1c031503040c3ca400100c038103085415501c9000c002c1d005440c40341d0501507803400140c2c1001220001d0810b25200c0e9440032102d60410000a0030f41d00b003101000303100030060000141c1035502043c4070341c1c054110100161070381d03240396484030291080130070310503000f9600340d011b42090780c190040c51086001fa022140c1c2d030f40345c01004641c0c42000b1030b200b000051051260707510601d880300740c04800500034401c450001d610b800541400300b0030785071000030b12120340281030400e1100380107155001c1c5001d55001510340c0c40070301040082002c40f042d500c0000d000102602014050a1050041d6802401c50160126145400350b2074810580305e071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 3297417 1250 3296167 3296207
    0x603020408060c0708070b04020307030f06150503030c07030f02030109060501080304060306082803110706030f05010503011401030803040c09020313020102060604050714090102120a090303090b040e0c03090f01050403 95
    0x40c1c050240e40040f20001d03a8171412241c5002c03002c1d26000c0120300c02031300480e45400b9007000040421410188003100c14090040050603018414000403c2807280c0d0056000c0d4009000c541070300e080200c3c40004480d00203920a0440105100090040c2465000180300c140b50400104043d100040508261100d546081249540328041d15a4900559a5800313001d00000f1b6122041c0a02502c1c0105035880390514502c035490509050781480e0311500b0110000b6a00c0000c801d02d2285800341900518007a4000c0000e040403210900a601c4140005030244d240000414100072514403401d0041c90324050454581c1031200c1c0703184c0e0b646103021042c0d0043c1306541c040b4445160074418107024800b161603030b8550b103814280d9021070b6042000e85505500851842c031801d07000100041030300320030b6561140c40362400e500e030181c001403030394100002c000802c0c030040c0034012240d104e0710780000f101804a501c0c0c0da00c1540452a00e00e0104612202e035003800b05100c2015080083d540002041e01d0907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 3298667 1250 3297417 3297421
    0x9090c070206030103080901110a03030e0114090604080a1b0809090106170402040f0b060304061508070602071a090301020c0601050108090a0803060d0203011404120f03050708070f030204050307060302040806 91
    0x404065401030040181d4054001c00040000480340c000a20b00f542041c1455240c0445546525081c40d00c05901600403c0e15041d620001220a1107200464801060051a1410042c1e05283d80d40b80003480182010000130300088000e00840121006040843c2d00001e00001490425500d40010015a00a00c20000003088890040d1031170b00c074024940342050b8030b80e071740d980070040503000c48100340e080c81d0364070040710040c0d440344070045200300d001c0d440214010781303461940c4d1030f01d00240e070103800c460b04206000c0c0030b62640819003c0032181c110426200100742d11002e881c4034860703980e0180d4150b20000e0b080c00c03404d9011550302e0407500240c1750386245580c0c00074501c0d01c1d40384c0c020000b0180b840420015a5529000441d07480160000e00002200080703103444401c40c2c0815902030b2010409900700140c15903001e800c249540c5480d18050016080401025100c100c020740060b00744410800e80e005994400d87c107403001400028100d0f05d0a6a4803c000b40007548140102c00c41070141c040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 3299917 1250 3298667 3298681
    0x100608071d0907050f040e2401050d05040813080d0e030706090b18030a03110d030603020108060d06090b0c040303120b010c08131d060108070305040201020d0302130f0b0909 76
    0x12100e140a44440010070754008500410000e0140200b0307000a20800744210b2046880901c081d00280c8409202002c044c10700344403901304042c800390710141140c84d441d9103e22599201007910540041c130300c4082240e031603900d4410b2450056440c101400c03400300100241c0e0315000602c46030300c0d604030345030149000048000d02d52502014021400072502d070041c208240d40c0b0640040c0030005500030044543c061120002e402c18070100c40c160001581c828608c0b160940074002d02c1900d024074201080061f1440e40060080c950040c01e49200d88a0f9032a503509000154012185150b40711a21803c9417501e41e050001a0f08540015800540c8280301d21300207103694481c000700514140c58080342800d070703680c51020aa010403040244d0024a980020b0f4116009420130451051703c58900c50601d4050001880308100500e6903003010f081c03806010150b600822008511051443c01503a0350f149418000c1103e01e02c2d0b80000b4681080e154002030702003120010b081801811141c0003030340d4807165 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 3301167 1250 3299917 3299927
    0x60f0903081b01091205040f090203010302030a030f020a02030f0105100605040e0c030402210a0b060f0d0615030c030c0f0803030906130f080304060501050a0503030c030d050a0605060310060807 85
    0x40402403209104014548692002e2150086010800c5002054403074103561007044408420003c0c0c0007092011405014280800044a029000382c0404508546c0b449d000a43c0e03800c1d1156000d004e11036080e00f02400e05100384903030108540c001e412107404440c0012210b00030a001c81c3d01818801200101242444c403c3c000c84048640210741000903485030005401039500c090022a4406140b1401e02c00c41c00d1400314001d520020035028104110b0181030451b1940b03c01001c0c01c1c03140c0729444080503241d4548010444040d0446000200802050010740c0034002c213400140401c1104c00c000000c00080310b40e640d0a4a104a4200078007560701c101040da01c1c0425202c003a0740c2c0e00000000303244009450712500c1d42c02e004400c00c070f03d032407455252410b4503401514161842500c0b074005201c1c50038041000700041000303400451400c026034048644070b002c1c02c0344880060f603c0380d0104400380500d80201003c2c03b0001c0c40c481d600c0c100414640607540140c030455001c9410200040c1d1564020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 3302417 1250 3301167 3301169
    0x705120a020f0307050d060b0405070e010203030403080402060405060c0105011d0402090c0705010609141506040501050904090c0e090d030e010506090a0e0106090203160909060506070b09120f04060f09 88
    0x240148900491a801c0058440040840d20341600c54000d0016550383e507600d0344070040e401418001142200041404156070005000b00c1c01d20801c2c504d0100180da0003c05c0729805078262410f81d1003500c4500c005240307403045034411584000041a58404194198030441c100c070303c80a8480b819078105001458114001c0b200658007402c0800051000c41881004242461140d4000240349483e86d00307840c02c580402c411240d41c418003404024880900f20b85803440c1000850380e10307007054a0000000c045225940d04580143d444030b500d80104952100741c0800b0340210034010040e460402c44d116591010100e0000000b03041501c401011201845500e005160203011004d4a544800c04840078194010500718559a684030014043d03801744080c502854601561f65050318068100900e83d542d00d0f044507103040d25040e000c00560b80c440702101d2034030b5400306d00d0340f01c00e50350300360b2443c1400000c0e0900c01c40682c00107206080001550000d01c10303555540c450311418181e4102c101c03140242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 3303667 1250 3302417 3302449
    0x40203030f070305120703050103050c19050f03010902030109030201020913050103020f0f030a0501060605091912060903180603020d0f0203040b040305181309050120071101050d020c0d020705 84
    0x708210500201072030001d2007924001c0c100b40746400d040d03d02e102c14010040703400e4000680e480b80103008002040c45a400940011101032014014800710003e009403140700d250b02c1307082d2001c8030302e9141d1800c1d04624407a42d0001c000b04422032041c14040e001c0d51124081300d00c0360103411500c5416010768413602d4141d980140c5511422140d030b81c1801800759850f03c40aa051003a54128400200c003400f803000030341420340e901a2186848000d0001c0010441c520701c541180102041c4a80e0740a1030004004980083d40454030043c1c600342039a1001c250030036001c0b003000980000c5209905900140031904812000700b2986695800c1001240015200108080e075844046801303c0d00c28000b07465010040c0c9d0600804940d0100003078003400350851201f5445e5154800003041c01700a108000910f200040c550a519400904240700e501c01e243d00180324000ca039240c00b40d964451020740e0195680000308640c0c1d4648a440540d0700c4a10501442c010b1260400200d070310308010b140b4501c4008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 3304917 1250 3303667 3303673
    0x403050a0602030406060302030a050d0e010320070204020705030a0302041806080a02011218030e03010609060b03070804050309130e010b030c010504090e0f0d08041e0209070e010905190603060e040203 88
    0x3540e1800040c0d40042c2007920340365160740e40407016030380c00d0103040903451040c0000c2400d00c9450b680980a0600042d1a5062600e0000000510080c131009031090840e000c015541e40c80040c03001400a000e40c002c0074100d484085035040d02070342c169005100780d0b0301c62001003003c036025401c00300644200c0d000d0105184c000c00b10240040d4004c04022204281c48000410004030b02c0c4284c3c180c640c80700d0000e40000b91007151498080c00c080c07080401802840c0000d001d20703403c00400c91810302c40a0800002c00031131400003000c2c003206000740c42046a009110030641c2c0d1014814030082c040e800400c030119460720b89040d070039250000b41d0032000344068682074101460410020003c0c17000c0ea034407500c3d074082e01c1101011a24107000840c40100c0c2c07625a01e10f91b09050812003402d030200550ba80601811012481c09079584000083d440045850170b034600c2c549540040b102c1c00c45952207550400f410701902007140643d601094143c8182e0341d002c10480d907032240a0702d40c028040d203020350035130 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 3306167 1250 3304917 3304933
    0x31305060307031410051201050105030a02090702030d06030b090615010801050f0109030b07170a0203041709030109020307060f0e0402180607020604030804080309040b040b010e01031808040308030109050903040305 94
    0xc00c162014503400500c40c100010459403c00e0074a0245000b160604030781a01c020741440107190481c0b84010081444008000d42d41c100f0011aa41d0344100d14080c2c441c80308940002c014910070001c0740c3e80c40803000d9050265581d64600030b00345400580e4980c81c140203440002da50280514034004007032070705a690403000c0e403a00c400d01c03920350259040e07079041003020000840400c903103009080c000d440603a5510140e00c2d6005ca40702c80d0003809810b03504810700400900c00443c540031880ae2003032102902c2d6a688590110000780102001e0000039014040d00780300095968005000611212040d212451842c11180401080348a0300454586454040b00441d81508000e0b001d00440752018104600d055200c2d11401035907006070344619402e61000a07901c036982424001c1c3c40804000395810311011f6081c0380003801d034001c0351500310704144d62000400390345440d003044c045480b500104010b80d12512414554040c0c2d10034010030114030306002c0883d111060000880741102e8004010341000c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 3307417 1250 3306167 3306169
    0x11010e01090b090a0306050c0a09050105130302040518061510111507030e0f01020c07050402040e06040e100903030b0a060206010308030103030e010504030204060b0304020103050c0f09040b030118030801080708031305 95
    0x1581000e040f0b560400c3e42010044009080b40c82202e01074401400482e4a500d04403070000c0100081d5008903040000900c80e00d02ca2503007a185000030760303904950128007a0341c2c20800f000d042c41d03c0c1d036003280e0701c2c41164180100707001c00c5117051108c0c00c029151003843ca411110300780c91803d5900c0d210309895105044070180490100300c0746400203040c0c6004210441d4283c0c4c3e091800c003401c1c001000e9a5400900c120024ac0d003001071030000c140a40d8198203180c0703854859200007000070001d40c0210b45403081d0354403c0105001881c0d80102451040100b60080d04000740244594034074140a10544070010441d140005409030489500902c0289140e00310703501180e200c0100444a81841420300c0040010303592402400d01600440c01c0c0c094507403400303000040503030301c000e01030392a21300f01080b2a200c0d280e603000403101d801200380d0b80032a600740300030042070041c02c0d84510f000e2010a260200810190721102d01c9040300c0040c4d04591035507031200d8a854980c481c401e60080082003083d810002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 3308667 1250 3307417 3307439
    0x40309050f031207050a0501050108030a020609010501050105070809010c0c09060509090106030f030c030e0315041e020102030a0f1b1112060907030b0c09040e030406030e07080a06020304021203040f0311010e0109 93
    0x465100f641070f1b424115090f0784150070b4610a0308503101e190404034108a0656041103055030045200e40280119450000080c00368800c0700c1026120010001c2c185280d039000741300240740603a0000c0c42503c0e0640e148510001051540525403003902c01e000441da1610050045805894018407801700690070703030340c3c140d8034007080749021400e0020466000d4241c2c0d505100c642c422050307589101c0d00610346894403250741c18081c0c41c4010405015208400580d034000150f5801d090b00703050002e412074a40d007083c0d5501c4a00018204005c01030340b010400c020304109100c1811109554017840072210a14140c4c480c1021100104e40d40c0c00002c042020440b2515540e0b040304001090524041a120126060b11480c0200403403951000a0400441d035041c41742c0100c2c40b0b5082c014080541c00c125206864480303245025124580101c007003015903513220250300e0320340c0b180d0f402c50340e45da0b0342d903681e04c20711110600c0213485442e0401e1000b941c0b0b5020701c840c003c031000165075911404c0d08022071420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 3309917 1250 3308667 3308677
    0x801061a0306091302190902070201080117060105090901060806010b071406040b0c030604090203010c0c11010504030314031008030a03060807060903020907080403030f020c010504020f01020106060203030a020307180905040309050f0312 103
    0x2a000b056020b02205034451001c14501900b840d010150b27a400b0603000140c4a414180c0c1b0811003040c0d0714141c500c03d0540840c00e181941d104458007521a101c2101003405421507400400d0b19008510001942c0311201d0700030a0300507c160f4440000c5014500c0c0d0b5a10383c40c044401502034594400010281202040199404180148001002c0f591a008a0b08480448002c403001c80d48014030b0005104180083e400c60942c2440d05a241c0fa04582c0c004142000042c000e040c10000030010540500300d010010000d0807483e021251100c4c00d41000501401c000e10640c4c881d03010703540e00460300d144100560810f036034019000c14450b0716035840480320036000800550801d540c0c1c0300000b1101d01ca174001441c00d060400c0012a00d81424010031100c1002c0f254480e0542e80740040404c83c141c1c010040e80e5100101020042c1c5a0b0349158099940040500180c2a010003c000c0800c140e00a513010b00e0045019a542c009042d484074180318014070440199541980700440041000d030030390000301 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 3311167 1250 3309917 3309919
    0xf020102120304030806040b040506010e061b0312070801050604050a0302060307020709020d0e06060f0a060f14130602010b030c060f1c0207060203041703040308010e04020105130801061a0306091302 87
    0x500c5002500c001044150420b075404c41c0028a000c0c18062a0f103028000c003805520111801c0145003080400680bd5546144840d4010325000c00c1803185c40d0458020b01e1441d9014105582d41c2e030704110342c100c00101e0200d03044808513032104000f0405062079000c0d01c040c0c4101400d41007040e800d41c2c00300250354000a0800341140301e56800440c0400440c000f410129480000c04195031103858001810500000c1090380100c1c80480380c08400d41d59000584201c885a090120303c201f1051001c8510050040102105243c001000c00e8501000c414450440708540c0c0200415882c100405468450701c6074801c0d48004207104140c0c0c0d41c4a45c070000c02054001066004880048070b00003c1607801004c02a50402c2d401700801040c0114421032100034182e100030949545020384d400f40c1348500600410304031512040004045900030002c803500d080640360358442250740c032902c960281c1100d00034002e0203010b44c81990069075138801940d005060040010382195190b05080301d65094655060b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 3312417 1250 3311167 3311173
    0xc06080417031f03080a142805040801020304030206060f010503070c06050603070807090504020103050601080f01060302070201051c0903110706050301090905010204180203010504110f030604051515040302180907030f020102 98
    0x10103e051200a0600254419018540c940c1269070002e4006500300030360a035903550400a081410702030640d010450540c0c10800700303045503158012151405141c0040405620020500061540000b40c5510a0300200d9511980009a100448950100703464080109442c0d06042000500c640c014503400800a01280c50700360740d4000051404070994000c0403075581c3d40041c4400d659041c0206030b88040b0a0800c11090305164681d000b0800d014451101056804070307028046a106e031044030381101040c0696005071031104a9080140075a03d02113020410a880340c540020010aa071001c485454445509583c80d140040002d040f004034101c0b6555820071002c50701d00d1507401010101061940c00607125810f10301444100d4a042c0b01983c0d10a100303114900d1442210700850f07501c20003d40d0042496143c070f4101d02c0750b1404d2095117550120f1450030350460b5a00c000c0c060b004032802181c0340d050300420200e140c0c5802034240c440103801c0c1c20040e03060001ca0a65404003c00502c18070403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 3313667 1250 3312417 3312451
    0x70e010e030706030e0607020105240301021303060203060f030111040e0c04030602070507080c03070b0405100c141f06050a03030c050a0503030f07030c0201060b04050d0f0b0106030203040c0608041703 88
    0x10b41001c0780354000e040841d0b070307a40d00d40c2c240100400c0754552020181c0000c2101e8201000001e00345000d861010220521054030503409413001e40640311000c96043e0b64130441516844c040f40a5003040310003030301890192241c000c0c00d2605001d6422035074850900e0300d10307060810201c802c40c01d00082c14000144000c020000010f925440103020141c000c5024100c81070910124600b4803140e81da0f0030307100b40d000074014880316107000100d404071341e4101ca075038407480300461080d65100030054010340705c0c0e03005070b807092051280418031003418070003a00c40032040113001e601c0000702c89450207001d801500c29801840068007a4014416081c001d00444482210a60718940b55a008440c02c42000400d40c0c280f203038554240c01011103a0a0350b000034000035082c95183d0845000e6845105e1180a018501105100d00040300084842d000910000103684504014003c5e500547e0100d4508400c0d640000d015032054800a0003180e100d500758207814400c440e000480c0d00090030440e00b4200c4414 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 3314917 1250 3313667 3313669
    0xa02070501060302060c0715090e0c0a110706030b010306170715050705010c0306060908010203070212090a0e0a0207020109080f0706030209280501090b09060403020d0501090203030d0207120504030803070e010e 92
    0x4094000c00301c18000a0801c7c40c204024500683d080ca4220400d1040320352007484a81b031817000c0e244d4071168a0f20211380761000200c0c103c800030f11000c150072580c040c0b003202140640e030641005400c10380a07241400803c1d514100d00b10f242c01c00106660154000000501404000001596441d61030349091410106107448450859402d00074403000711b0b03600c0070100407103504240340781e005240d4034008504614082c1e80117510f031003039900032003860400000c0c854126903d6414920180000c003d180c440c078170701902607500039807101005a02080e50345e1000204c9507800070700c0900024880700500381103490000160081c1d042580300703035400040501e04100a0300c1e1f488900e0184500a850f40c40314900d05400548000810b40041c0d0080c0d1003048038001716140c001c2103401f1694181c0d000382c442d80c11410445d0040c680c45d0300085d810b00000541c0756210445401820030940102e244e1a40c0e01202203003618240700754480201010b005000083e080c0d8000c20302c607802c01c04c040c103260030070015000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 3316167 1250 3314917 3314929
    0xf1106040801020915070201051909090e07170307030f05130504020a05030a0b0906030c0d06021b0601090b040209090601030b030109020603070f020618060112080c010203070e03010b04050c030a02070501060302 92
    0x103001144039a50100300384c6850f2418840900034400003802181c035003001500001c0c001e02c01c003440010085c2e020814660782a03c12107403400205540784040003440e281c441039035103460440c4502e0fa0744620039110b034561504080126001d0543c991250b28040120110658954101e82480c001d000000f03440060107440f10b0008090003402951620b80d80e00d0b181110504030340b0b4038100b079402258400100031480c7c400140101110302c1c12282050700c036090f0725210020f44650100f5403000f0082000701c010003100007a4140c113030750301c04400b800040d0207202440201d005000318103900054410121b402540a540825041217001d000405c9a5400b6000b180e0300303074020b03600b0100044001c84004070f803c0d414020282c000002c0c580000b23854078088440c3c1e50b500010700400c601d0740c1c42140c01d2010003041004840d00d040d071540c0255100e10381000054800011641004d00075420001c8051162800d48503252040516030032460840e194484510002e4120398002c41e5190358425000c13001d682d0351 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 3317417 1250 3316167 3316169
    0x3030708071d0409031e1d04090503070203010e01060302010f0c032a0605010803030703060b07050309060a020a0507260606090403030b010504090609060302040605010f020606010305070c0212010c080c07030504030f110604 97
    0x29841d06c500601202d4080c407014103800b46540c0401051260344410344801c07104088407100102e070302107140030746820014114490000c00a5143d0b10300560784800643c19084401128000d80b0344001c1c5290005040d130300030103c2c0d40d004000508007440803031002c150701100c0000c0c0b1031010a880480a0f1955540100da80c280c010076282d40c400310420003101d0b07041c00b07210050070f0080189801e00c03000742c4e00d0310b07668002c0e040810311900700480c202c01d40d18804c200c0d4502c0381d50090104c2d01c5240d5140c1810101c408007590307112400d040a00220300460000a1041c064003001e4106071641e0780c0c5450440040c80c00c40c0016040100070000003450702c0741d5005c0e040140c031820b003000400740d1440c4108000c840151340721505022a2100c10f9055940118000d07a000030b0a090100e802d698008048841c103075401d100a611452072003400307020200c154440f24204d11980c403044203a0f164910001c066015110700100003c000300405e100041c0a03030007003039903144034003103000d0300080001c0012019005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 3318667 1250 3317417 3317423
    0x50c1905030a06140108070e010b070f0c0f080105060a060219020604081005010503010e0a03050403030e060708070b0901051b070f06020405060412030e1e04020304020d1e020405060303030708071d0409 88
    0x21040ca107134003580c1d04543c890050000f0f0004000580c5880318188014105214002d403462000c81e065050015240550003469805882040c5440d100ca005600700c00c15801001312540c40e003000078010b418004030301001e13196281c000b4010400005174525107115407020407600314000f07101c0003898134410800141440310343c2c20003240a6040005050840c1c40c3e00c2c50107400d40c0c0c0030b000305c2c2c03011035001821a01501d4051624580340041c50011466520683d02c0061440c180001c00c0d00c1400b5842c00b509001340b401c44024405900e0301c101c1042c3c019150824008000420480000003400d0b07801d000100c984511000740c00c1a80d1030001400039001a4000311420748a501d0340010503034003240041c5104070464071309141d45804500d5a140e42c03150140e0034002c95001001c14255618103401c618010307408117164800b10015556000103c00810040303014034100004141503207801f0098a114541a6a40d15010381c2c802c00304844101d591140d06c104071300354140d895103070b40755070040007a5680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 3319917 1250 3318667 3318671
    0x303030703061d0c030105060d090b04030c20010203030105060702010c06050907030215040b030a0e010e0a0c140a05060f03070c050304030b070806040b03070312020705041b02060c07050c1905030a06 87
    0x480c1011800801803c008510304a501d032000300511032803404107803030540c0da080e114180c1310891008164020040078201500d004441002c2100305907200c10320600c880d101d04006010005541c61072942207907003546050158005200510140c01c211002e0700050740145001410b2a580d504e88004030b40090311a5659a00080020303c1507003800c60b08400c40400d6488400d250528103000c212060101410398414191601101415080250440232640d516002030340c640c2029031030306201d0390040d4130400302282e80f0801c1c5001d103441c02e40080812a03001816003841c02504000700d20195000034400d40c107015120001d81d0101e001000588051481000d002401d03081c01200941a031400420f1103100768103102d00300d289902d0105042088a40c01032140e907154040804c164107000003500311a0300985003842c800500180c00803818086d41e841c0d001c2e2901e5071100b5082600522850310f000c5c0c100c0d07200f10130703541e038034101501a06901c08c00303503102151302030326480004d090024070700066407040c1e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 3321167 1250 3319917 3319919
    0x206070c080610030309060c020621010f0f0b03040212030c0607020102070219080a060e100c030207020901051017190203040303050f010509090d1202041703040e01050405060f100e030303070306 85
    0x40d03040004540007903034030982d85501c91131560001c02070343d1540a80e00c1004010b010b120210344850041d81c894062480042100300801c00c89440c441e1800d00c5100e00c00b404408001402031140c41005090340c0340309180c1403071541c49409024901140390942d25103480100040d0f503241d9030610105024400540c009070b604c0181c0d0040041894107508406580300840f4000c101d244800210004110751089010901b0181c03403020031f007401c0221514014107802c0011000183c1d92503030003400920700c00c035000442c990300c500038801042c140142079000b0414140d004810b0105d0400516403240f40790341c0540042c40d0315041d801c103030380007900d045010a0700c850500207103007401c1e501c1034094001a14041c0c6280f80510445594058040121051007100c5120050034203168046034080d02880300d02c114a030f552542d5960741c0c2e07400352142034141091400040f52524150040d0341c01108010700b0340d119450690108903080707403840719032428044520b000c001c00382c0301400a14403a01450724000b540c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 3322417 1250 3321167 3321179
    0x3210103060b03070501050304031d03060c0901021005060603010302060d09020a0308070203010c020c01050a030b010e091e0901020901020c0f0105070c03060209030c03010506060703030b0117010801270201080402090604090206070c 101
    0x344050b280c606200e500056410721260347d1003421f80390710a8062500070500320000c2d0101004441ca0306420b50180611020400705003a28802010194401c0c2c1c222403030182030003800400c6a0041e00d03203035030089003040100b0140c5059405400780b51599000019800015030001d50046010350040392480d802050007000d6140a1080f202040d0050025000a6940ea00001e106102e40174160082c10f65541070755100ba4494444112100000340c030807005814038100c542d440d10049040da0081080e0880041c4d00c141060082c0c800400042c1c000708980070703940d0108040d10b03440c00232480c1045000d0050b503001c1001c1404450045000c0d82d00180d035100c1103420305050a203107d0400d130081c1c4c108070900c40c15459920403918510340601d80007a01031407241c0101c3e40c030b0042103008012181d4401c000310315600194001c40c04042d2007101c256100340c41d020041100400000080d001c1010032001401504220300f02e140c0c01307070380240006000d081e26800031351560040007080e03e040400303180034060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 3323667 1250 3322417 3322421
    0x10909060b09040506071101020403170c0d182c1f050d03080103150204080a0c05040b010c08030a0f06080102040602030309060c07050607050a02010b0604120209070f0f050702030321010306 83
    0xc0c01c4002d07100b1040c640340035110540d9030403001c0e0244040080f10714809005a400394142c8010b960322020810700000c207a500e0462640141003400000e0207001281c82013503005100c1c1404548040c40028051403070000740d0065540c044400074400c17903000085001880c4074100040c8141f40124120900701e60440343c0b0045180c0300d4200f1402050606068004070740c210301c03410704480d40594641c0501200c7c0301000d010b07010725481b0701480d201e25000c2c50204002c1d140c0d082d060700c0c0b040e02d0410460700c1000044406050844000c1e00c2c2c7c00003003000c5061840c098009071060f8201c043c010034401d42d1030b1016802c90f03205511850050300013000344101c0304010300007a900038448968035410284103403119921420090b101c9400c0c44000504440b2450007904841c0340850010003044d110b90b500c1004030404800c102c000ca2007140c0c084009070140d0f0141c0c9444000e849156229480e4182d2004143d41c01d62044a05a0303044c401407000c81c082c003501251082c0b1603145088642d900394558a05101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 3324917 1250 3323667 3323681
    0x1030b0703060819080f0c070b030f0901020405090a0902030106030804090c02010605040c050a080709090501030606030605090d050a0c020303040e0403020309030601060c02010e010e0612010305011a0103090512071a01090906 98
    0xb240c001c4e24060110300e0010318000d00c401e4003e1229a5501044030000c1c14070312480e00d5a92140c001c201002982c01c505101951141031003034200711140d55149501400c270301c61801071551041020000c54107a407215070106003070f41d2016000243c6152203440e846100d0700664007000b10300f51900041001c0c564280107120003044280c60500409401880c050024001c0b61048010003100800182c0180d1003030034000c1c000e15261300c04001550712401c022010300f15078042500e202c0e041a02240011030001414001015240d1326507060106040040340c04035034440e002c0e40d00d48014403000c148980503d0300d080c0140d201e40c000310340c0c42141d03005043c14a4016800b580c28015100d00c003101503600800c0301201d0007024a00510700180460000d010b5000710f080364045849000c00200401c801540001045041914400302d280000c10044040d601d803800300a101c0d42001e41c9181d60040c040000c0d080c1c10f44920f0119503c00d1201500e0501c000d400d03800300d001d45441e0707a00d0106104151042c41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 3326167 1250 3324917 3324929
    0x40c0201090c03020103021309020c0706030e0307030c060c050405090a05040201090506040308040b030c07061d0c040b1f0507020d0506040b0109020304050606090402030309040c050912010b01020d08040203031201030b070306 98
    0x21103040515112002103181503c400b0b8145074001807454282e0021400150240040030411502d907100200307420380e981e004d805a00003082c41c0c1600003404060010654480301e6041d914090004182d50ba450054900914a5410301c41c0602020034150380340d00009110310400c00001031145081d000061403c143c69000e83d00a600810042c00490402401c6506994809190a50341d40710301c18002c00c18841d0b540b001c8c00300c030301c0c02e1410031141560300f46501d0005100b00442d00f4907080041040700300d50344800c00940c0050001428100c40303261241968003881203050040c140400d80d008a4010321030144200c2c0c0300d402150800c000c208451402c01d024020b190001c500314509a036806c1c0c2d8030750020b0b250074403440d2090005030840d50108200c400d4000f02600030b001107002c0307400c05072260b004600c2d1070340300c1c1200c40d1000311442c1051280c03850841050f402044140031115083da540b040c041d2090340c03d0300003004118401d982d070f402d1a60080d1300c101c801c2415403920440040840f04990030134 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 3327417 1250 3326167 3326171
    0x324050102030a03050402010917010e0106050111070302012105010e09060a11030f041104020d020d05130506041203140103110102010e06040201091509090e0604030207080307080a0e04021314040c0201 88
    0x610180e40e001080c1d8001c60483e050000b0701e03441e5400161810485c0b980003000001098034191115081900301014035a1010000c2c03000c02d443c2e00041d180751008d0030ba40d000561040034100003540c46800460350050301c100c404080700c141b100308002903500980080c840c04000505100c18940700b0080301d03510002d1004104174a104c0000725008522000c1c0c10301d480c0302d002c80045001d02030384d82c0d088405410018000c543d9a04045000c1001e90070160b04c11100d24a00030010700c036150880705030f0b41c0e441d07800000352540c0e54481d47e8803d00d08643c85406400c15a0300d068414010300c9140105010314015a508212800001d0009082d00c40700a071859240e00038005004c01030740c1284503582a50006d0b040c8084010500c201103900045941c0040c41c2d840c20040f20041c1c03500c001c10700f140924000d5003555805c43e110b00c041c656078800c01308010401d010812620021600c290055403401034028800341c9044215510030103440800d81010b4030b200003c00740003016140034456a442c644040c002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 3328667 1250 3327417 3327419
    0x405030d091d0a020c060a05060307060903020904030809030717040e0a14010506030c07020307030605180703030906080c0904050a050f060a030b04060207020301061203050a0212040b1c0e030a0324 86
    0x10ba424040c4900581c401000490700128081e800103405030340369907108400715000e501e812980038001e8001a1802c5001c1c0c041c0a80100b0500c3c4561304d08016240c024110071010b0b200d0b90b0301111040002041c4003a41d01050208000081499a80c02400300030003000c5034850781415001030321140050408150103140840d00743c0d44400c4502158110350703007240c0ca29240e5458000400b2b03184640d039002907050251082c044104603169001d40c0c064a219140118038540c0a550907a513a4a64003000e004030307640b01d40c04c100d480c4c411440b1a904c401e0280e181c5061845010200381030701c9041e546d0320012a2220308001702d075241042c07600d80c00142142d0341d859252651b256000c0001010b00701030555030f000100c44080d52000d40145005085188048600e400300f405c00526581250a0000050242c11154400d0845030f10545041d02d02040c402458511050a11b06149200240b00e0119a441d4007551070011814009402160f04540340828001109004e03088110b443e4054201c142810105c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 3329917 1250 3328667 3328679
    0x140703061503050c0904060b0a09060e01060203070302031801020a0209010b0307030506040c0c030c02060712050705060709030b07050309010f0c020d03060e07021504050a05030406031a0102010504020f060f0405030307080405030d09 101
    0xa513a12505409842e080601e450b103040c1600604048034a054002c94814030004030705650358800e2040350407a030000c0001d81d8032850120b0b160302c01e0743e8014005a00500c0801c904080d105140c0b4295441401140e2343c4400690208143c003500360300003928400040708020350a80c040c0202eaa00600c21038003000b9000c160307a400340500c1141d40010f0100440403e6981c119101c0d5800c0340e00164100144c032089180c9404001c050f0341c40421300701c60764050704002c11200c40c024903184c400e507035111080441a603a020802c403a550402000302140d503484544454034800c09109031003e030b001d5580500f0b00d00c000f0481c080c1c26140c0950141c0807a66401d002c00009590118800020024000503481c01b070300c4604216181004d000c2005d04617010000b0001007041c2c05500000042180b90740e803420360701050700164229041210081d4201040400804039071801000400a80100d804034038102138031480406d103107070002e4104652070040080e003400303946020403120864a01d9071504900302d6003012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 3331167 1250 3329917 3329923
    0xe0105030106030b0a080102040e0702100902030303010504090503090d1b0b0304050c04050c0f04090c030e030a0f0807020a0611030604052206090201030f020a081005010e0306130f14070306150305 86
    0x40324a004056440c80c031661156911540e05004280c01b0707000b50f444079154200c0395880403082c3c03030090140c030446000c40c0c003412a40c003c0c8204503070010302450840c0e10707003405d04c0040c01a111049034a03000c1044044940d40d918050b000d4403602540000941040c0752062411001494204445007030040c42048000350000403014196481070300d0108154491051130f08450080b041182448000442c0210382200c5680c000d640c0c1100903a0103000c00010007030203545074425072081e80002190540e031f08208500800203550040c007584100e50b5003140315221441124484140300e0407070f1b400002440300c00d161900a1030740050380a03007603004200a9a00f1503c420f10340c1c00c4000e0a01d80c440c9000d4055a000740d1002068070318918055680c1c0c52851001011060b003210051581003500d540402c4a501c2004025a0002c000d0001c001549070514155101c400c401c4048851803072031006280010764488407400e41903880002000f4080c114542002038071958411080540112841000421400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 3332417 1250 3331167 3331169
    0x1060911030a090201020a0b01090c03050106110a03080c09060f0702030c03060115080903070602030f1b03010f120503071e06050105091608150a060c0302010e0705090c0c01060504110a0f0e01050301 87
    0x240b03000180400c8a20041c3c0c1010813400e0041d11070b1030b82d203000140b00b0300150011000b40e5003954042219a8841405442410311608004040d5100d460400c0000b4040c0b055684c00c5006200d4a0341032815000008515922580c0554140380011802c0030442c04c0c10024402440c80031800743c20698140002148150008107210b4100040c0742d0103e2004202441216030164001700c040d9540c5c5031403035201c10368400580760000c89560101180f04910b0640041c1e0341a59071860003d41d202d0300e000b0300002d101c600711905468034042003220341e0010320582e000b44405624004018242c400703e080050071140168401c2c0d004100040400110700d02007085603420301803504050b80301f6298100c1b54003d0040d0210101e400080403c030200740241c110711100143d5110b68002d02409100c8404152511080c0c41001c2e040340f01c16010070080a086405401c0c1d100d0f14200011b08142e880001034156007806c00001440c00d00045c81034251940322010011041c600e08040c05100c0812000901e14401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 3333667 1250 3332417 3332431
    0xc03090d060b0405042108010608060f030102040902030405150901020309030703030906020702120f010608030f0304030e060c0a030c02040c0e030a06020a170901020c0d23030a060e16020106091103 86
    0x61000150410070540e02010034000050300c1003200786403518082e40d101c00611101a8414560364a21607021b00c03502c000da050751440c1ea40c0102903101ca10600c03007850450140c3c0c0e5030654080c080824007000f2407028600c21402100140f00252841005d02c498442c068404551a40100200030400798000220b4010940c18580002d2005150800318002d00410000035404444240060881040000c24001108420000300100da9440000643d2840717614806101c84a0500014000c03d018141400d080e02001d01100d2428801c540c0b07090600c0c9007614100c02096032201034038290b09061080c0b00f00b5525a01305001e802c401c50340001c0e5036000ca10f600030441c980009104805522030207220851510210b016041404d00b01b5400d8040d41140d4a0079100d4402d21120750403071845040c066042203080071103650f90411200340d04e915917000074070a8038095219440010351000300050284a20400b183d4845110041500242500c005512104540d810440c2c04c01e8903440307200441e500200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 3334917 1250 3333667 3333679
    0x20a021306051201060504050601110a0b10030506131109010503061315140603100506010f03020c011107110909030307050405061324030509060403050304230709020703030605060c0309 81
    0x10465a003801410103508400e030031041281044540c9101500142c040d5001213400b844503980b4100115402c4407030070f0f00040030b58007640103031022a5800c0701c03017500400c4036074410f41c1c002e07105c0d242e251400d242600c242c1d40240170310300c80e00140002c20350000400c002c122910b101079407501e80040e0344c0d5070010b41000d00030140c1c20b002508001d00c1e5903200c6242400c00390701780690082c000202c880c1c0c10003252a640680100d0340d01400703041d040d104081c41440140c440040141daa0300c02100203401048044040350359920030081c8007121403020705022031003804441e44c2c0010b00818030060070f01c080c140d20044c3d4014030a0004480d0410b0070307a0281c074400d4442903152543c0d03070f41e051f48040c0349500000e4908101941980710313250300300c0c0d107000380300058a0030b00ca50f031203602520395241d40c00c5130302800090080c0049000111038050540c0d111040b6488c8100e9922050b86850420381c80354400c15a60750b0000314542010303010300905009020445115061034000901a51203108a05103d44681 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 3336167 1250 3334917 3334939
    0xf06090e07031d0106091b090e0901020c0a12110601060207060309020102030f030c0301150206060102060403030c02010e07091d0c0a0504180f0503030105090a0e0705040b030709050c0d0b060703020a02 88
    0x10744643e101c2590529540c1c40030340061488015035000301410301a29039085c2c2004030740110303e5046030390800341d880c50f81d4030600c43c140f402d8004c40b00120080c0c51880307155000c02c0182c904000401c0516191801405d510540220030040030b081c0710341a154200b900c0d0002d1004011040e00890300d4030031600e10b807c01261b540300620041b411f5100314080c0b0340450101000b441f15201c04440514180ca05e00c0d07003014049140000243c0c0c5d940307004ca540500591041002900280c8603130400101c01e602c038000030602100c1003821505010085d0032158480b030351418010180d0800075020395460303c4c03440180c01c8514102c00810980007550090a000781d407521b481c8904480d25100c0d4002041c0c11140213403a040032894150340f603074000c0c4191407040c006000466814109841030f000030b50110f41c01015000e1808003448090048108150fa040c02101c0c40011003003241d00980b849401b0424030240e40c1c100c20707000c903000c440d190b00d0303da40100024048200042c2d00099503800301501122816152 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 3337417 1250 3336167 3336181
    0x1e060a0b0a03060305010501090506030705010c0b0c0d06050603130203010501120506040b04030e060d02070309061b020d03091802070c0608010503070608090703080c060a0506010305150d02130903090806010f06090e 94
    0xb0f0106507000800c60b40c41c0030000107210800e58400c40c001d58046064441c0190390f040119130040c2540c4000c2c1814082c4c001103400403655100170306d54101060008110180c0c1c502c006841da030001c650614128501561f5181185400e21034107014040591500f010b01c00c650710740c1c0340d0314440180020010256100810285400f40d44e0440d81082c0c0105080e80e2402c005501c040030b900110b808801251010402040440c0a0801300001e83c6a00d4202886a4410780030011504c00f6201c0c03ea0500440c0c28011400009182500c3c0304020000340c0580c0c2d030146841d007000c8201d40d50340300344100141d000040c0426980400c9010031140d07a45002540ca844c0c01020504155050780018004140020350001c000f00124540f4400d020b8210100106d580c1e1200640a8031f00407950100076802c40070010131756141c141c5c0860403250010b807000c00d01030500ca074a00c0c11961102c8041c1d000ca010801c00704280e11040021030b01401c45900400c8100740390280c0600b0790380f442d014040c403500d41c03200050382c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 3338667 1250 3337417 3337421
    0x304060e0108061306060504030302060c04060507061e0203010b1201090605210712060615020606010e100306030807060603020907030209030601030209070507170901110106140d03090801050403081e060a0b0a03 92
    0x1e002d504d000800445540d540054541d40c0103200803005409124001803049690400380c40464003a42c5a55180c41081d41c0c5440c01080e241070b01209803061080380c086080940d1010b140a407418003565a5030f0414004501240c44050340301d0780701c00e424500144000e40760000d212120101001c021407c010810260608000d1980c200700a060240e850680038803d0030b4011804880d043c4c9103448949014030340c22070311441c00325151404a40c004800114a090640c1e004000741c0d010b1078002485612543c410308694403002043c4d413000d456030320a02c15480c00714500c2c1c1d080802c5003000c5241661000119407603440510010b4400e801ea000040c480c00e010744125540b60fa44801c41c28880044068200c110f600310f446060b0000e0102480320072203040c14803c0409035214820301221701d80c1030400300199004200006c03810000c2c0803500041c001303000d01403d07000c1d5209032034031008c51424034840d8404404142025140c40405418070a4540b6481190010303034242d801c040342d803030760f00c6030050340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 3339917 1250 3338667 3338689
    0x3030c0a03030902011e17151207030302070605030708041101030905030a0801090c020f03070b0601020f0d0509041505090403030504170a0207050f040203040c0909020102070306061508090304060e010806 89
    0x16003400355420300810954140c0c800c00e452407003602d68481140307031007040f1820740400020b1240802c0f07517100481131220f5501c01c00c0d03a100042c000540c10755051034000c59860016070804071040e9000c1c16040c410141c060040101411145c50402d00f14940040e008101c0c1c100604003404202c0030b1202901c481e44660040d505040c2c01800303c0707039515031079100104495024440c40407420304d4014080f540710b1022501c60022a01200154142003039511010b00ba20000303010b0a05510070b00d54403510012082c080400b260500740c98483d00d42c8100d80501007039031490100079180703046030103041c0321564070000b109130490b4141c030780040d440e0740b145440d01922051024101c0481c4001c82c00920032a80040d210703084d00c00949400c03192001ca00144410b030302069a000381101c0d04000103010180a80c0c0c440d4281c1401403040b01e54465407500e428041303c241e50048005901504110b15045801c148020f0708400d18000544c40d080c030b032072001041012726181d1581000001c0b4003151035a50b481c04404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 3341167 1250 3339917 3339937
    0xc0c04020318060108030405030a0204180209010305030403030e01020106030201050a03150b0c070303030605060c0c100e090a0204060e030c0105030a020a090504020d0203071b030804020d02030f0d020106090b09060a050105090303 100
    0x56803420074507110000715900e9800b0340300900c40e0400200312060044156800c840c405001814404166801c05c009400d0300c1c01101c00c00b590101040025030789030b01c3d02034001c600400c0035656035030a6003801802c5460241e9140c0c1568102a01040140d86c464111a800c13038951400198103040c103a441881c3c00740390752040c407006802192920340c4000100c0d490301224402d89040005560398800c6c4115070084012541540d04515440c440605062422240581c02e51404800080d032290000d0b10700c09065501600c441e0740400c0c20f000031078200300f10341e400002c02c07402030591604460000b85144001803034801ca146e004104040c3d218002c41406010b014002e100b5501c60320f071002e000740290803ca80d81800105034607010880c0f0300c8a40d2224810030b425580e043d07102e41c0c441c5c0a1146400c0c0c400c50490b00b612030640f00680c07941044c00001d1840c03c1960010898600d05030030f0b1019101026602446600000c0c18040301d55188164042190801c2c01c066840b0904100024114000d0203615 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 3342417 1250 3341167 3341171
    0x8090a0311040f05040803010308070309080f0706080601020a05060703020f070f0b0603190b010b090607060905060405060610050415050403020a090209040f0603110f030106050a030b090601090506010807050c0c04 93
    0x80200074855140c080403100941d401c11451040c0340d000400d4480a40e40503000074410001880440e80a074018240180a03051902040365940c0d48680307461092541000340d500220400d00c0050360160000b908950244000d0001110030b0316015280e07580942100d061660014800700d040900390107454440307820030401c100040300380c10031880354070044803121f110f07025424542000106015010850f15000220301d03200e40e0030078100092070790028200d25030061041c400741000a1644c010b00780e045210b800038001900301407070058500030010b0310f4541705050049844024640c00030940341110702044030034400909070082560035102e00d81000e50041343c842c5021558080756001009052029a010005d5624035106041120400c1c00b005060001e2000d1071589843d01d1a46440705007001000080c1050b5200c1c0042c406a040d80d000700c640040080405c03803401c034107101c03d50050110900c140014a0400300003440600001c0a0070284400421a030020748020480b07860201000341c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 3343667 1250 3342417 3342419
    0x3050411030f010501090c180303080a0609060803070606060302090d030e0a0503060702070623030601080717070c1103060108150702030f0d06081c020601050d020301021303060506010206090601050a030602030408090a 95
    0x702e901a110900403226100e08020340001d07007511603d0f03030031000500c03451b40090850441d90121060f803400b03080d826540c4e80f030f80b0780418a21400c0c42031170000c004210045613203021a140120035100076900c03810a141c41482800140d0f21203604401b05250f061614002a14907200050144140c980000740c041c400c50007003012564000a410702618495200d655805903400020110700c2d1820007404800c680600104009501a21125800000c2d9052008003804121480c0c0380b104000c440070400160a0341440043c0180d0402c0c02d84521025005401e02e0342c18a1042640c1e42d0303d04510710034075095080041c4030244240b040d982c030604055041941d076400c42808501401c601d00a600c40c6005291600103080e000e607181c11400052a0054940340c3e00c0d2030100f00f0600c001840581e01550208104001000c040c3d81d20703c0910710030b00c00040d80e4104072000a03e028030050403021a0707440540140000d03036400305201c00b2240e01610141e500d46d100e141900c0c0d1805080b50a07604a2a1000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 3344917 1250 3343667 3343693
    0x915050d050a0605012003040e150d0303050a11070206030c0f070803010602010515030105040308060105030a0603060207080403030311071a070e03240703201e03010905040b070e0603070305041103 86
    0x7603002c66100341d03610380f0041c0128180280d91000306e0300442580d40208010001200300f001040d0740007810118803500c484034a0003044c072542c88140204c0009544600b000180b03041072060610503a1000040340c140301003640440c400e8800580500c00c00c0710080f4008186900000c122070f0301a038040d0704141c895a4410019020f800300340c600303c1504500300801ca003103040500c43da61055402da601c0c850591a001c0042d12a544007404180d01583c50702c20100100d582400101145445000b04c240e0b203624500b4010129500595019000038003004410041540d03011500c1142c03250944200190b11020410365242500380001501800b920521000c0614010790f00394544540e1288980f0a5440f11400c408845000c607456020791525003c0101035a90080580040c0c50510143c01c0751011502c54103c5d150004d0b4041510303907403110100410030000c010303030f150002800d0a090090080a00000b521030000134010401c08d0307030301e90000d0144040c80b603d88080140160a452104074181 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 3346167 1250 3344917 3344921
    0x602090a1503060e06130b0a08070b030a0501060507080a050306180903090906030c0a1802070614090708010606050306040b04090b13031b0203030702060c010209040c05040e0a0c0915050d050a 84
    0x264065020a10380f00001406082d00c0304814030480c0e0007042c1002d0700c00c480020380e0017803006034a1150820b2426a010440c00c40c20840e0801502e007905a50780c4074545604804c00303a0348140c10000402c1402e1000400150100c425140d80840c00c1c10119200c5c1e07a8900420350340400c500303000d401441060248007d4020110003000d4007941902c02a03940c1d961801030556030340340c0f00c13200c9411075000641042811403101c81c190440c03081c90b002519024483d1a00703010303903251803030041002100e082801f2804404100a9005006080083c4002403609070040c2041c0030060029005544580507007241d50303120791018800710344c003031035400f0581070021a981c500c030901c900482c0815103007448010620491006580050b9005001b185001855401c1c4801074120310f1900142c1e64090110030655519800f030003080d0440341c0e50309500c0d603280400b054900030004d80900c0340e00e440c22405119180d8030160b00001c1e50707600d1603541a00801400211514420407100154644c0707042d0a000b50800c01e5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 3347417 1250 3346167 3346199
    0x110d0b0103141006060801030302160e06010c020103090501020304061e0525030e0a110a0801050c03040609030504080d080a0c030e060114030708060a05010f050105030705070b04031416050601080309010e06070602090a 95
    0xe6080f12f00e80c10024500b480308080030f000b1100d030010f00200003040e030342c85983c102182134410316011800e20307029960136099800956089600b6500c0d40080b001e0003046042c2415000803050080c0070314107103c1824030346000d15084865034407005007036a6440a00a80117042d46012980407102c1142c1581403030f0b61000c1d041a204c42c400c6249690010b46014140035480c010112018a2807440e126680d880c1c00606504c0000c0b028040103000c00100030302d01340f21030322000d2140d031600c00d01850201c028004581c0b404030500d00b0b0624015016400440000748036041d21041c525400580c400d410002c4d1500005500440e2980b144500b00607032440c99411660403a19012108072125407204019a458002110b2041c0091414800e40c00403030100490307103400500a0500e15180034440c01d0503c0d145e8080f0120107014031f400d00f103c2007005020818503004000d0316014504000061000038001c1500d00c807a0382c890400401c140090099660460341c400c5001464246507641d52a1002202905 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 3348667 1250 3347417 3347423
    0x3011203110d110607030905070902030403030912020601091503030807080402150a020a0c0602210d060308070803040507060201050601020c060d060801020403030c05011a06070212070503030309010207110d0b010314100606080103 100
    0x8a601045d03a044c001c0c02030b482c00c0c41d440b6001c1d103100d50070540014001d4200610039410151111014008100c6030400901051120741c0940b41c1c80d8100720301d2805135a01c0300d41241404110340001c00100761701c808800e80008062070320809036240c1d400090307081200c0303402600f0590703c00618805100d400040d10421180300341c004514407641d0341c0040c5d07111401c00c2c80c1c0001c1b401c1e240c0f04e8001b40c034503410001d140040101d0000a2215100e840d0802150010401110000c40020a100500504108400c02096584000c0c0302070710704000002e448081540107035004020125440c004400f26410010252681c84001c544803a6030342001483c0c081c40c0b47c019101d9510f04003082c031481ca04c007403501c404600040d120030720780303030351503090000e542030801440c4460300412030003044583d82400210300238403102e0005030b00c2e5052420700f2804480258901889100c04a41c08800940000412411a60001071000a0303081c1250020306042002664154035171810b1004150642c0249500c1d051fa80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 3349917 1250 3348667 3348673
    0x30b1e0901080f0601060f050705030301030f030e0409030905010c05010209120d08100b04050105070516030b060f03070e07030506030a0c06030603030e04020901020a060507020a0804080a031106070503011203110d11 94
    0x681c99006584403c1ca988007101e141d00001c0c0103105c05400742400c1130001390180b0b0700c03506e081a03d4079040d095130000e13001100c0c0da90828424a003416440581400c07440c404603030803c90b00e08207a5002d440d80640d8031900b030601680c40a00801d101e029811b6604d4042c01510011459030342540d0192520b00c0101c10201081c14440805c6188903003003980825070700c44412061409052900560305500260400c85242c0b240d0300000890240201d62032000b140728401c8859141010002c00040c4404628882e00aa11074a42040590b040122290f0812803500b03001400d070b00c03400d000c42d0074001c040c00003501c00d111804000031400e9150f800b500459000e1b6a0300c610b00f02e448004c200c2684980d0300741d1801a4000401500801c907540c3c4030a8100d0103030300407203000e451143e40c0e10f101134009a00c249100c1e040030708030740300380350308a01075154020f82d2401600080c9051540542140018000c2c0384001d07986400300c3c010103014100303510503000d01e00222004003481000c01440f007462040c020706980 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 3351167 1250 3349917 3349919
    0x906010c06090507030303230402010507061d06010305010608010b0306010e0c070203030c0c011206030210030c02010b040c0306050a0902041802070c030807050105090106050f01090306150518010602060c2701030b1e0901 96
    0x54100c01c0c2c4140364551201102303415440d41d400440c0d540c1c100c644140ea0740303a6140c40b00b800e00c04045d49000107900704180600758962660425a0840e5482d9003c8082e036410030402c2c24550b175020601c0e50648907000f5689009489224040d47d2900504100035054800000e004070b40100014880c000c0d003000f40c1c1c0c0d075145668048001c2e010303181180300c000e42180fa080343c0b18941d58082d80203d640643c480c8000146100f0500c0020280e4201c2c2394900080b80d540d81d81030020b414028401000b60400c09429031800d407511a6001007820002e10004035158089142d40421480500c4030004603001170900d03032940c05600340780d4000e0205555031016036280c07100000b0706041107004105880d40503180c811003280781d0780320080030b000a200341e008800c1182c503000c500ca540b00d281e16500c004034050100d007590704204010385018009000c455402c4414011050781c44004510024542c01181c44800246c02240040e4054400c03034089907403194074074040c42c0400c402c01c6001114035204860141c2c01e0303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 3352417 1250 3351167 3351191
    0x110d0e03030121030503040609021906050919060203040b18030a030e03010e1b012003040905090d090807031e0204090503030a0605120d03051905010b03010f09020c06060906010c06090507030303 85
    0x30010594008000c1740050002801183c100d034050210280040c040f148800490580003c44941781d81014012071070125600e0040d0810720400502c1a80b2254015007482c10302d04069501d0145116010b06000c00143d40440c030344060058a14003d006000c5902c07141161034041c03c1c1010306c2d50020300030340c80c0c005c4c00301d0004000a00d050b8020f101c119410701c05500304004482203400c04c92102c041c40700791022041594010401040140360022000407070781044074403141024030030035145003003040d89001400700400110f01c1c60220390b445560050001d86004416085810410020754098900503a001c148400840110320031400b0120410946481d00200542101c8050410510768010074580709a14000d5001c0c0d034008400d81d000590340303100048190207440091b0080c0c0740c0c140c0003200402445145019100260650090550602031160750b2305507649070003041144140c0390704012411907405078605090441d0400c000b07100760400d0b810300301d41d1160b040c070003100080e282400503582c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 3353667 1250 3352417 3352469
    0x90c020a1203020906041715070807090909060b04050405010903020610030305030103020402030a091401020702010306060503090a0b060105130906051302030c0a0c11090103110f03031c110d0e030301 87
    0x14140c1d0042a044031400224001c41c025049020140e402890800000c229010803401c580c0501131644010807001c400c420440d40003000c040c140c2400e02881605110343c01d904101d1071807c2e0340c0300d12000070344007000d030401501410120324103035001403900c0c050109105041d044081c40e00d000781c00b02c401d540c4500f5490001505248006400120f042c0014001840c5c05d07001103404c003503001808030380007503641ca803110903035401c840701c40140c0e500040c40021035030035010340c50041c0054101681585041c489040e1074444586000700b820300954001445a80038800303403100d615807003008803e555202d1403003400408003806401c1c402e407103403840340b0311040850080302c0c86416054003041c01c00d1170004c01a9100031030340318212050140341c1800421600d03400e10081c0294013520710401c050f00722005021142e07910381582c90280d0810002040b220721000c280d40001100b0040010b0901c03a4144285041e002c2d5440840845040c003401c00c001c04800000f46060f507080c4c444200c40c0341000245e07414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 3354917 1250 3353667 3353683
    0x5040b04050115180e0f070b030a0b010206070c06020901030e0706030e0709050103050d0c05030906030a0204050405090c03071215020708040806010b0903070b030705281205060913030207080313090c02 88
    0x130031080310300c00d2100a804035401c00c82d0340000240c21540381c1c5010322003147c100304a0b60081032218030f000c0704101c1841c6007402402401e000a0002c0c1ca82424042402004880c45150203802c2540008270f01500f0707480b0f03511134140d00800c0015030f2082a103c1038014043c01c0354809030f1186100314440440c11000c14030915040347d900600034041c8810441c0c09540554104c0d60030b0715140000e0265001d245c0340c041c0154411152039400503580c0741000108411030b60045c080140076071040c0d0000000780c800244030300c1500c9a002813400360044601e0001c044140c00d40000d01d946001141c602e081004850240c4103581c545000e41e42280e80b40c1169942c14020540d0003685948186010026610755200941c6c1203031a40c07901c1860501014246c030307006400d42210400300768108864180c502d50084170007031030075003941c014071031410710100184c014800038007100e601c031014400c050101402009581d00501400741a43c1c3c540608000080407203140d441941c201d036080400d800384451020540380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 3356167 1250 3354917 3354929
    0x10e030f0606010f120c0201020415020115180e0102070b060301110a0504030803060f030109050609010c0c0507050f010e03070806041106040617100801110304060f05071403040302030d05040b04050115 88
    0x901a50b0300001110049042da2810307041c8030101040140c514982c0c018038480002c41e80016035203520780007907803c40b0204000044c04691411101c11764010440196804803003200c841c5440080c180c0d0070410042603c420351001540c40083e80104010b0300900c0a449424120700030401d2020421100200c0e2240b040b0000001c1c404110a00005005202450304050040c120b00007494180c3c0100c3d08448000006a65560241081010303a40c0f0901550302540e03243e103040012403185580c1e06607202010701841d441f404071a641c50703030aa44a002420500b03600102140c0b2074aa886104644468041da020350341b4103038065008046050110498044900c81d9580c8442955809203420407004080c10044c0350000101000888050900950f181c47d1104440f9980d03d042a1400c103040710301070700c0440d80301400e200c02c003c1c41d250494508051104a4070702e5035500d0b5a41e1504034294400c0d118014080d03807400007440701788004a00038610643c410f05c001c008100c10a4401c00105034544079003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 3357417 1250 3356167 3356173
    0x705060304020d031b0206070807110301020408030405090a021615050903090901030303051302040e031b12030403080a09080415030518060705090d150b010f0c02010f0503090a0f03020c010e030f 85
    0x5540068419080c840382e014400c5c1040040c0040d65002070b0707072a80051815a54010046541b000f440b00c62804601c013408210000c500d4186070804040c2c40b030099208030b5114414403800244101004e4046070003c62000010404909003441c0c0001003240c5003e04040461400f400030328140000411280f1202c4001c040c0440e91386075a074120090080207000c2c501141c0030824407070040e01d480c01041c140e0b0b0100c501550303c60288030180310844850703400340c4100d075001002504074207401c4021030750015050710340b09406948122641c4007401104000400c80f0381c0c000350000d403c01d58482892a02c440a41d410b2140781c80303000316800b01c0e942c102100107942e0070100101d0000c07801000180740040c2c000e4035014200d1210f0b181c595103540b1241c6c5000741251503a400759178942c3d10007901407160746941011014114a60002095401c1c5c51800000303000d800008684002001c220707803081103034000c401c81548401da14000b511421641c220300d0106003031041e100400d14003c506404004030403801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 3358667 1250 3357417 3357439
    0xf0a03080604051e0c0405010212030f040b091908040608060402181002160905090c1002030901030f0b12070e010b07080304020603060103060509100e010605250809130509070506030402 81
    0x100001000040d010184d00e02d00310401c118403801c0c0400017840350341120000d9440e00d1034400003a042174215000f05451000410400c000000065241c0c3d8200707820006d09611070b0b48000c000d5280130a60000c4001c0b0755102c551403c100904c40c0010000e40f0f40a50307800405845607028001a4021100b20040c2c1ca03810031302c08891070401e2000060204100e10480e0701d40802d03d002c046460020783c00a174012601d401c1049038070b0700100201c40308242d0075684a1111120400001d41340d020742c1010f07504141d10b03060501d40408140c0c0005101100013002c000c101c020004105940788028420044001101c0c80001403500b81603054549081c0c01650382890345d0303603607820011140e00040086d8185951858007041e1134558010a0748286407501030480081d0401080070b0034881c0581c401070070007004010380808846444141e06410303419030429103220b4003501d8600340c0d500a40d03003510b0f0015106824003d150650360003050003003010109481c0001c0e1100306011a900c81254080c1d0040b084103c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 3359917 1250 3358667 3358669
    0x5010b010e030d030b0f0402070b06030c030d02071403070e01150e011409060d0608030304050a05010b04020a090b030901090b3603030f040c03060507050703020d0c05071203031506110f0a030806 85
    0x7410341420020083c80c071000446c00024200d0300303c0c0c28203a07005025641080a43d0804000e540e8000c030045004280b0b0113900d2030001d51720720b428040d540e058500e21141c4c00c0242c034100b1821000c0e04142c0c800311865a141c000d0304041c0b11003058000000380039559402280d500130040000c10000521a5a142006140902086511220b070402d51503964080000e40d21206001540c011807040c40a0001a4040e0400a00b510003000c001d83c803c1d441000002902034010003280100c03550742c40c1d101d0303c030b550f02c00c0d24a0040c01c0441d4041d101520300010010001d200c0c048010200002005030401e01c41c0c650004619040a86000d5220780d004002181403e00d0811000c4d9000d8401d100888a00f40c882d83d6100588105482e2407000c1003010807100200f5406224041003040e00b0314002c400c0608940710107035034080e0f40c03003081c6502c0b4015002006140c420303040b078100c2c481500e902007031450303403036600030300a0101c0306ca500b401c0d000d030088144d031642000c518400c0468050b500c42085455847c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 3361167 1250 3359917 3359921
    0xd020c0c01091a0c0a050d020109050706031107120201022205010f020708070501050f0408030403080301050a0806090703030e030a170403020a0806160302131509080601060c0302030f07050a0b040503030405010b010e030d03 97
    0x404400384d44d1042598240000e0000c211940000d461680003240c07007002454142d19080c0e5a81010701454180a8180c00c1869200107441084d03070030801e58a48001421000d900900c2030513090401c040d401560001d80c102400e01e03040031078000303076607090b240d1040b454200d07240c0d55140a00e030143d801011041002c0d40c800c1010302131884c42240c0107858195150291842c41d8001d1b031044401d018048010400ea1400c0ca054000402062018100924040e048240c0b59030b841c0c000107080c4055003080c8981c0780ca04002008545034000e41030704211a840407071040340d412500c801c074440e00003244003150451000c00c07000d008240020540002414410040d0081e401040301b9034202c42002d000000c510080c800b8060050310144c440e542c0c0242420384107800e10034140c001360f090100400c0300790f0000c0c0c3e0000445841543e00828a0303142e000d81d10300241805030150010f403d1070182814403090000100c021801244164020008103520400556a001007010b03443d0341504034401d05030340c2d01d01079 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 3362417 1250 3361167 3361177
    0x50709080604110118030506070f1808070503011109150d090b1303030615090302040207060b03010203011e06030b060307032a02010207020306010506070215070302030c01020d020c0c01091a 83
    0x54104488225103544140d880e045003140c00740c0350070a0242c8000c05035600720707952011a14201407051515415038076815030b10140540b1290820824219044041e8455100c03800c14000701c00000c02301c1c6a540b2052a81c40c030301d074001c1030b1080d4a44805014040c802004685c00700c500a089448010f070000c2d0303140001c0d04007802c100440d40c2c4541d03010300020400030f04544900607502e0280d403002e0950070010201d0300031f5004810b50030705080b44060519042070a00f0101c3e9411034000d41e9880c01c1d4a00b940c0600001c0003403680640c0007200214840c484c01801c80302a4502d0182d950307002d95200422002d5901c0307000000d17040b0004101203541c0c5c4c0c0c4203400540000900d00e006001c0811301c002c00740c0c0200c0030140b103000145d601180620452400740440c0d8014003089400c41e09151094002800d0880d490240003183e040015004040500a00076140c001c1e01d140021516070610014002c0a5807006c400b581c11400344085010a41d8020000501500c2030100074208a00203440400e81942c42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 3363667 1250 3362417 3362431
    0x6040b07020307050106060f080f070e0409050307060203010f170d140a0c0b0403020606011206080601090b0a030602040e060f061e0d0b220507020604050d0c030c060516090b0c060a05 80
    0x4103c200003280c401d00a0100610043e5101382c0c101482190080c4841c41c068800c1c07071410382d00c0d814486250b91112126680c007804540000390344041303190451540c0b244e00e00082080740088000602442441081d900b21134004090222144241151903160b80301c0c50343d22030100301c0e2603490010240e0360314007411803200e86080c800b00c3c1e41c802e40c9403104031103805c4074100c005900c52020440c1a503070040075031688250301075080c8151800d050711241c888405004e031007503143e81d81901c40c0040e900c01c03030158000c64110f0340c11590b40e5228140001c010008894040c0100703404071410f0040e003441000c581d4500d0100407085100491600b040701182d01c0b161007000b02903150425218955284c11001c000c00d100c400d1500b26817480f654190b07080d5080241aa025508900704010120b0000300340b01c026120117203044c1c2000041841d095982c240d4a100c090440361811003005a04060351601300c0701511075890301072420307079518044c03607036032080e94005003c40d003201c2c000c10000740e0543c1010784c00c884 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 3364917 1250 3363667 3363673
    0x605070309080c0a1407060c0b0702030f030109050106020d080603060403030e0102090a0603050402030106060207050d0f0501020f040305010207020a0e1003080c1009031d09010b1207020c030708070305010b06040806040b0702 98
    0x340c00c1c0ca0711040b0380c0182100e41c5107600000540c00030001418080300030049404040d020145c503004e40541022080c0c0000b81c990360103040094082842441282c0c01ea1081d521010f8603540c5616100300102024007658026104190720300320040d004d00141c07481018001c0040046039030b541da044028050b0405204220764003030010340c02d943c1d40c0200d03600140030150780006461500340101070030b441e9035620041c1550050141444a5107604502e152025000100407a10b01403524280e4028411a40225910100400c000c0100103040d0010480303a8000c440c1142100d840d01d030315107100070055481780707030003510b40d1820800120903402a03c250b10042d005d5400350b0508488100a48040120440c0001c031100552000308d412424504520402070307030fa001907076046c80c080000b18428020100030801c88040001c00040c42007181d50049603000e0180d486403681d030450540d856046000407900d650801c0c00c100e109003014000c1c0e8044070800700c01446151140c0d198010700c014040c0060017140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 3366167 1250 3364917 3364931
    0x6100b07050717010b0109050607020303030402060a0903021504080d0206010503070501030c03060503010908040305060a02070206090103020306030a02031515030102070c0302010302130b030c030f0106020a0308070305190504080a08060a0308040306050703 111
    0xc1c2520a90f548034003440e0002140703050030980014000c2031035803c4288900414805c0340090784000040da90300690690300350b507865070841419074403407056500080d40420740507542e174952682503015104541c02a01240e050b04001c0c1801e9031564000d000e240e406900c00382c0100080d40c4680c1000b00b104420341400604980c840020a0a4404800091740c0b44480003e02700100502008031681c000040c2c4c0b411400d24285500003072071031084000c414105038010010900e1a80c0600c00c01e04a50341c010708440c018696070303e181840500c22500340800c9140000001524281802201c941c01d90200c003c480d41803c0d980150003c3d0000300001c1c0e01180c000e030f404074800702d08100460007107402c111601c2d180d00d84040e10b045000016004041150404121100000d80104140ea0407002c5030801207007903507685e0542000503004000a0940c00d04002c00c0c031080c408624024062450603079261400e99039035200340890007a51b8400149103a20402040021440f141e001c3c54000c1c0b0f0740d107404078900c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 3367417 1250 3366167 3366179
    0x7050111030601020c06040e040f14010906050402010806040606050405060f12010303021c03060b0909060102011b0e0f01020705010207060e040b060a1701061107060c02150301060906090806100b070507 88
    0x1100481103408030840000309000180d07804006014190001300c0d401440e043c00c00a4044404101800041c40d030b04292100f079041002d0110341c282010700701c00003040240f00078100781025101c00d81d0140d003c207111001103005030601d40190015030300f560f11010725103440c000502011342c1c0700b140c20342e0f507000050101074010400c00400c140298003a5000b800c07030000d50b00e03980c01e01200d0202c00c03102780362a0417420000700b034840041da400c480003224200a9940c0b102e0050b40905443e560044200b035035402e078000b05a40200552404902c1654903c51548001006903a244424080d940c0580d005280070415903214402c0d800007072102800c081079902c030030804100c1d240c200902000100d017668240c81907415403200410300520041c41c0c042c91007410b6001d9103031a103000340500400c12007103940501c20342d00c134a83c2060401d00300168a5075039680d00d15000303100305a60f004000c0010380000700051400000100c5c0b6020308440e110032244136142a40b031040e41e40c0042c2c02101c00340280c4500040d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 3368667 1250 3367417 3367421
    0x20a03141908040507080606090406090201090e130501050a0e0a0807030e060d0903030f1b0507060209090a020301030b0903030408040501031d0106030501050601020c010c0506070503061c05070303031407140a05070501 95
    0x219001900e8a030b00505140c5041400d0107402d4008280e0707640440200106076030381c0380005400a4105800084c2c440c40380c00122030903072030354008203d01c0101c6811301261202040d14012128041e03030003081207440d07100041d0103640710182c8014240d4406065074011540800080000074031a00302410a140d0510228080342c00840300d11007140d940380c81500c1455003501030400341100221040040500d000079401e020103407100341c00304001c80481c00740c0411101d0750444610a40040241e8024580186184040e520900048a1405500c40441c0842d1000815640103961008503541080c0c107000c0114020701c50f200c0a10040e0401e4003401200b940e083c4610000b4501480002c1031900e81003001910f000c0c0300c00110390401c2208032240000c41d4022400a4001a403480c0a0355a62640c0c0c0c005407161003220003418045003112034980403c10000340b00f41c201d80c807a0300c05200760081c0c0e61404403400d000b2207050011410b010608040d0192a0000300340d641e05030700b452410b044c1e141e15007500b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 3369917 1250 3368667 3368707
    0x10080105011e0e0708010303050a030b060c03090a050102030703090b070f020909010902030f070506030109020a03060510021c0903020303030703090611040305070e0105090412030e0a02090c03070e0306010501020a0314 95
    0x5a0407000a050864650340402c040034009400000c40b0070b0400340c1000705040c83c144000307010807030041030b8491424402d4016240440e40148503503221301c1c1c4800c0890700c90744007072102d51141211503030001c0e080d4000f0007620550f0b42c25464540c03100f45880010f1580f940504000c0700c04840000800c001a43d805100500440085c00002143c0b00684141072030050b110314018829480b1080401080d661002120b041d5211100c0258454405420543c06460950045948032241d20325046503140d00103a0b0006290070141520001111030f8810f440152840c000650580c0042001501080c00b07608140316003031080d21b0000e50354161951005c800d4200e5002200c080d00411400c108400c2d500014074098241200c52a80030f003400e66400244808056104040c5070720380b01401c5039050140091a503140c2c001c3c08a11061a00181040c0c459104072120341c0843d26040505640e13050000d80e180c1070346c6040e0018840c04515440c10766070005585c01002201404202841e601003000d03650720 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 3371167 1250 3369917 3369929
    0xc09040f020f0405060d022103070302030304030207060c030e04050402010e040609060e0a020901090501080c0d020d0507080a0c12110c01020d0207020909060402031e010e0105070504080c09040f0204051008010501 93
    0x814100281c81000304060346903507200c2c03046090005005080d901c0e189416803083c5c2c110340b48a000c80c4004000b41d81024440d003505200d0001241010900d5004001544200e00c20341c03d40310026151441510420513108010b4005403001e00840000d045c00d40c4040d4100380141010040100380341e0001d02602c0c41030f00a0848144c583ca41044540e0840c03d406401400031001581800c02400c00205040c0b000d128080c1003000003c08503842d1060035003241c003010350311407040d507444e08410a488040e2106407180b0002465000000e000e556240c403c0c2030a02c1e00702d54602c100d0001c40d101d0700c000b80c0300c507c0f00000011005c21040401100910060400180710000035841e80610300400410314001005400d483c1c01007400c00005960120340b030185450456514130207031041c4e040060041180081010b5550310b41014010025003090140c0115102c140848841e03000303220030320131502c6068800603e03021040f0780b030038014a1710b40c1143da481710f0803a41600c3c51568032140c95094410a034008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 3372417 1250 3371167 3371183
    0x1505070504060e040902091f09020703030b010905010203031014010203040b07050703020a0b1e0a0c050604050a021026040206070813090b060403020612060102010b0307030b0901060e0601140a020c0904 88
    0xc00805400049200410b00229004c000e4440160041803102000038048234060500c1030b810500d14020741b070b4031000b03065144d80443d1508254035015005089030250b45002c2542d00400190662000046a102d40c4d0b0300442801c40c186000d14111840780c2c10380c3e050341940030620010a25a0742c8201404c80b01703000b03100030082c042c650b005001b0304040d6071b080800b1043c4c00f0001040b40d80007100d4484000360140300000c1e07940103031000844049009010051141c06864240024001e001510079041c0d030003181c0410841000240580349000e207029510040340114040307100c015800d91280358000d001900303217403900042d6a00e00150768000000d14121013a0b6040500c0a141e0520550702c403043c0070b84901d0310701030850300007550314003170501424444184003001954592003034200a1302c180001d0100d40c2e000e612032401e054003030812982c0e40115841d0007800560800000b089038050328068441012881d80545400d09603800383e09528194800d01c054120261241402248035900468034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 3373667 1250 3372417 3372419
    0x60c030319021312030210060905090d08220c080703080c0705010212030105040b040603060c0507150902011b0303022101090b0108010305030a03020c07120501090b0a1103131505070504 81
    0x40d422803542581081c071518414000d440000a400900e1016103448400c041030052691404900c0c201c8010000c1032681d0912000180407140d68100900408005084e20401e550020040300c0412003150f0507440300f58035050b800c51801c01040b000840c00d011307841a05000342c480c1d00c0249021320766401190710584c0001c841040c13040600044010348401d10240000d000780c41042c0e5103500040c001c162150760350300403100341075940b07600070801590b1155052041041014000c1c08035003014006603240740400c0e01c92010301c890342c41070503c4140d0584840c078880009034038102c41c0303500f0250110145507003003241c10040098849104118620306030003841660405102c8c0040c0c8082e502418188850720005100280c004816071701d480c0341514006881d100c000c8030b441e207016081d41c040c1c60030311071a041440a00074107400c13014980c1c0c0100046401515105a520704071030b0b03c0c8001c44c050460910200301c0c0d803e0400d03515044180155145540020b07091681400c070340003030343c845002c84c03000a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 3374917 1250 3373667 3373681
    0xa030f02060108070501090b0309030712020601050f04020319020304021504030b040201090501020102120c0906090d08030703050f091002070c1707050a06050903031804140705030609010f080c010309050c060c0303 93
    0x11070302603c520806851894075100019022120354010720790305101c003100203070f1070f40010000d66824940040c85014030800388100691180828001d4500450848020000340d040c039000f1030b4054440c000000540140364140600290000785c000c0380c2c001008031100c1c1c1c000c10781c0400b80000c0c6004a40c0c011050810b8400036080c40381c0c580c0b111707041d64018444180009602450b40d90b11850310f1002c2c5903940c0425001454a121310007030a984940884c90340340c184840c3c03801443c440c0720303691001c0080d91605820b46449241c11a83c0100d2a03001a440d4408084150040d020082c4280407400f142900e80511800d400403d2141907482d1340000701c104514640200220001e0602c0d0903e41d2a1011744804a5202d110f10015242c1c100311500c0c80804030344550b4442010485154014001f90a000340000c00c264401d0b12114411103c0100104a14610640e00c074120b80d141d400501144050500640240400c5401600c0034052264404603d40303404d8020503d001980c40510358030301d0103034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 3376167 1250 3374917 3374923
    0x90109020a15030b0904050606010f0915021501270c0c020405090607080703050108121b0105010803040f080601050901060806040605090114010914010f05070606120309050108060d03140901050c0a030f02 89
    0x6004e0361042c88268180008250f011032440d0300400207280244c280d00400801356800001e40c0c3c000030704070588000c000d274400c1d03000c5014541c080b4518400c08190760790740300d1100c2c1c0d2080b62481030806075540c0140745210110754000c02d0401d09906242c80030101c0781d0009406c95034110340d01e03039658101e02c08001405034407100c890752020300e6003004c0000354100341e13220380c3c1c6000919803841d20b944009181910860014184015952050000d000c5076844020302504c82d0030511440c14404200c003808540d018000c02c406050303c0003d8030800c840d030f182c004115403115001d04000c3d0001d65030070001c00d0580b00e2002d140c0c040e2542c20705507000c0203202000140310700c04681c803c4071402d0b00400120001d0307902640c108408a002e19189495000342c3c103201c0000c000950258441c3e1152200328000c0507017102c104411500240c8629200703a0340d05050000080307210030004c00003040c41158941d1007649901501000c001803411a080c80a4010114034003040d8800030303808500e143e07a18844a40e410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 3377417 1250 3376167 3376181
    0xa1101080f04080306060d02070206030a090209070305010803030a0b040902030106090b0a0801020301050a0302012703050a0201030e01050603071a090d08040503070506040b090603070c020316060905030a050a060203090109020a1503 101
    0x351071245031914041e11403081600002d8045803040d20300013074803800380100382c040d01c200e01d030002c00483e561b04040e00c042c4000d08240b14100e0040e1614030000c0d05681c06486034604031001c445c040c61543e50744081c050002c000607480b040c0e1180c0d03646004400360701c00744100800703091103c0700001d00040d03281c20400e076a0740540c4202d40c3c03a13004000501040c0c440c985103c0c116030382802d100c00191003580c22084458691803118005c04007881000091040005a10080364001c0c0c90410122202500083c26100c0459100350541d2001000b0080c041c400900f00d100f07100b8008a40341440d003c80006134442b0490031090b200c000001c5030a0201d85401c0c0105e0004181c11140720b0301d05803821922203a24010519011b1242c6c40c0803000602c4203000d024003601141c1c0c01019124444031011440300c1e82041c6008080000d1894032011616042c00208660b54a4029000f4000c2c0402543e8520183d400104a96099501c07502100300584482018001810205034103c40e91010140c0060031224030f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 3378667 1250 3377417 3377431
    0x9050a020901020705040b0f0d03090501080c030105180403020f030406050304020f030c0d0303020f0409020a020a0606050102010e07030609080c06040503040305010c08040321090b1602010b0a030201020304060516050a110108 98
    0x810020104182c3e00040e804040743d50994020814641000002c5c1c4000b0f0082403003900025001404804c140d404628902a00c00980361481c10341c4408a03403074607502003409a41d400040315070070050a8134242e8005640203100e032040791042404160514190b0308568084d001040c404014041180b5200e07083d00d1003000b058004008600298001450860f00c5c100d0240626a0020f044c08200518004450180880103004e41d40c410b0304080081d07070b4202d06101512264504003022844d50f04c1030040000312401c0c48000c24083d41103031680030080108103021210004200410510ba040a00c5028810740c0104091078980c0d2950a1003400c1d142215028010132800008100c00030b9003001c04003079910441e641e181440035110640c0f030020903140300d019201440e00340030810088205c502400b4120140d500a1207094042020300c6031000315400000d000d41c005100512080d407062000d0b2981000c0348622051646503500c81d0b9090843d032550a0b1036028180c214681d440d41c010001c1500141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 3379917 1250 3378667 3378671
    0x111c080a110c120309010f090509010315050604060b0a0e03070305161502060705071101050c01090602030a0f0204080c0904170f04061413030305030901020f12010302030606100914060c030d0609050a 87
    0x200030f160a91248919510303d418002007583c0c5401d43ca01c034070250005800c0244c40ca40143d6128140000308545800401d0b0006082200190090805004a100b1140004501c034105201c2c00015615082c070180c410b501031040030400808034800b0041913918075491070340d00004c03034100303c0040780b0001d000d42014155444203040c00744503907100044520041c4c102c020f0644032400301c030040300d1520403402c040509600301a204014450f4030f03401940501003150f02002416040255241a80a03c0c407503000717541c10252820b03026050806c402540941b00c0da001e1141c040300c44e04000721640155000344000312000c6400e0040c01e42240c0384c1400c1c08804004181414180408508140c681d400b0040801c0004004128001025016141191801207a5a4031200f81c400c4c0703100440e0007448164404e100340c101240460404130300165400000b940d407040a14140340e21201020b80d600d1274a40c101310104510200f040082c07001d400e4100c0c0e00d880100f00345252078110020340d0009408168028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 3381167 1250 3379917 3379939
    0x3040305060103080d062301090603060605030402120a0203030a020a020f010305090604120207050d03020c1003050105060f0705070302041103072312100308070302030418020403111c080a110c 84
    0x800005007541180d038403190241e83d50355600200070144ca96607100015040700c03000480000400d1210f0f004142d503017a41c4003007030b00781e444800310305a170700d07620402e404a0b2081001c940075062410741f145860303040e20b084404440540e40400d1651748070011000041c1c00c92804041149014401c08034404c1013480c09120508001c0340894507004003070310003003c10f025a40490302d1203009108800003414010108204000c081c103029440d80401e183c214801c001007515407010b18040d02c102e80c1038541c0034100d1406c100841c50100c2e00c0c0c4d0310491040d500c610804800200594581c0a0f03072540140c4c1c507105907100c2c1843c0381c0c040c1002441d40032142d09011000301c0031550b01c1e44002612103200e0181201c0c2c9040c5c45000d42148100a01c6d000079004820000d6000c0c00d00d5000001407084404204031592035480000008040b8001d5000080c001d01c2d0103828000d2a251850045929050044500690100c43e50321090310380d01c074420b0180410680313881051002001e016440580d082a5280880304c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 3382417 1250 3381167 3381173
    0x60a080414010903090b030403090504050106050901030608030301060905060a02030903030403140c0d05101802031014010812070201050708090409050d030e16090c020f06010305060a0b0414010e1905010906080609030403 96
    0x102175006440308520040f000800703243c85258a180200300c00342040006586580d0010807a81c059410170f070110b418003400040140c8000100c85c1200d05a9607652112410701041007055408441c100085100500100005503070500c020700040d840303000190604480c603d019400c02d205080d4251140c005000c2c7d13240441c0c1c0100c0d1143c405203c81030001141c601d144101e11100b40391032800307509485034511403503610105600030240c4001384402003070f0076aa00c52502d540d9401d290300400812000b0b0001c90019400b071400341149038401d01005041c6000c500100d001c1746e243e0b04082c0d41c554000c01201040030b80501c24102c0d550042400f40003c08004082303040c20040a2281a4010766501d020308181031003400111082210300c3c080d14059603580c10040d655500c2940d0308200c46150043c44c00f0246003c0c421841e510544280101041c1e107803080c5411f154600034001c001d607280c0e4444244000e0304070321401e40030380903141c4000f5040b82040003440c0340903001003440c444c55000300400c0c008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 3383667 1250 3382417 3382427
    0x90507020a0303180507180207050609060403030605031902040504060e01021306030c02010b0109050f01020c03060c0307020601060509091801020d02071b0b0306150c0102090d12020f030415120b060a080414010903 93
    0x182c90140100101f103005424501c8001e209005020345140616024450341c00e0707011420705c0c090360213a90284440f0343c803a010180c481d4040e00c00203400c26070101c42c100050030319400c40d6500c80c4c000c7c4000034030300c43c03c8203080c0c2c00e82c0d00850140149140305d8a06000583e094416107001011a20082103448000000030349410350601590307100d044c442004003005d82c401c005280318681c01600780d46050401907054400c0390029120600540617110000ca51244502e080e1406644018a040d5090302c448400c1e0040e860805090306007550200041c072420710982c001020b03514490501000d089512049203100c9110540004600c403004009118256950310b500500c2e41074201e0100b42d136061070716a09070081c0700c2d42400a0b004100030388250144906e0240d444046100f03502515001c440c01c030742064481c4154040c10291107d015038170100103104030301c0c1a5102002190000e108441d0b100094101c2c0c0003146c141d0000f442c00c40c1040100110308224002034540b81000744203580050f90081c007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 3384917 1250 3383667 3383669
    0x2010501080717030708040b0301030b0105010c03050304020402030a11040605040303020708010b031507030f150302090f06030d0e01050d02070602040f080304231914040c05070203071509090507020a0303180507 92
    0x80c80840b000000300744a01c140120b17109154007544040d0b6895403401445800d4009200035118501c00400002d003550290030702c480c642d5416990140745980799405c00009400241c4111407240c2d0310101440200b44410060015003400d480e82516a40b942c60000d2501c17805401ca1022641440b000301c0d915140018201ca030801c1c0415a20010760380c800c1d040700203156074114606482d0800d4045d403850308002e032502040d64002e5230550600d82c0d030840f2031440c141701560700f00d800da403161564980403449000d0340e460f41d540c14134089140c900910440c0c0140d0b040301206803680c56001a0030044026139004d484014202c0070f02035800c00d807502c1800c054000e030303031445800f070611000300141642c0d5841c1e06403803e60307050044009030b041c2c941015154241580c01518052454040c0300c0705154015019503200c146d00a00408070503040c00e0550103040c45050381c3c0014421404004582500940611403041c0016401031030aa00c40d4240201078031008070b80480c1482d07024060345c01141010a9403c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 3386167 1250 3384917 3384929
    0x1061a030c071e0303090308060102030a0c02040c031103040c06020106060c0f0305030c0405130c020c0a030203071503150806090705150904090503090303070f0b0a0c0203040608040206040f080a0b07020105010807 93
    0x19120440b40c00c010003100c000c4032000030102c441000e00010590107a210581c4c01740203568a08855a503503005aa41e031240c0c1485001040041100340018038040c0c006800e01140c0d840c01085607ea0356008000300e4009413011600d5130108401407046c0c2d682486400010710241c9401c0200e51204c0d252042002c801c1d1001030100b120000000b402194050100c0e401048003900c2000d8020b4012401d10040c0203140c0c219005000f000c9820300ba900d0a40c0b48681134940040c050544545080b4546c0c0c660b000700c2c8450410305490382c0741c00840c200309024841c01001d201010700300c0740c039000214500700342c0240c0085126502414445c040414450f054400001c0b00340d138001101a0f0758100340d461030043c1000c00d941440700040180410a00c0200b80c0c002701e200b11004099902d5041c07065041d14400741d04070005a1007030004014032880341110780e03002070025041c41d240c50384400d0403042603149500101040d90105e4005401c101e00400784542c800382a03c020481541070480700d50300e41ca042c0c4510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 3387417 1250 3386167 3386191
    0x503040b04031b06050403030b040509190f020402130602070501081504050402010210020309070501030e010204050d080f0405040204090e060907030b0105010e0102030f0a111506060403030804051005071101061a03 93
    0x40070075005a20070803000f69071100350040d0410624215003c0c01003120210002401c2c042c41700c845061034040d0038000e21545025000c072840c814050700444075480c0046e208500b42c06035207005a1101d2000744002101014680444c501384071000c0c0c91304401d58001810003a052040001c984441a01505000360440b00400d050301c036800100d1802d00710704a808030061001041c4030650200207100340888800384c905010386240d0000c1c46080f401240300b1180c21030a00a003081c0016112001884807048002926080c01c1e04e9102150890304240c026104103580c1c0c543c030035404441008402c0e40002d0140080130030030b00b15544d240002006100f16410b020200343c01d8181c81e1300038000d941c5000b40080d100c5450302803010004240c0492541d0320b00d0280216072810b01c13001c4101030303411b21500c0c000e002280380615650b01120354040040069032140a00c000c00ea0943c1d1950040ea030050000d5501c030000c1001403900b6900710381a5a000302d0b2595425001c0740f4161269900b17580e0700003020246 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 3388667 1250 3387417 3387421
    0xa080d050f070503071b08190c03060203060a0312050409052409090109060f05011e060203030601050703090b030a0506090a06030309031202010207021908010f0203010501020a1410090303050405060603030702010503040b 96
    0x300c0c50360089000c020403140000c5900c01000108017446c0c1e0407111071500b151014408009103a10302c08010303c001d0a8850b1100342480400c0d1182c00464001c000500502c40c05a0381e5103501c1401c807034103000f4800207900010700300201103040c0541c2d80c01c241e400362116410440795100f440e035141c11115141c0106125400921099029070084a2003a04054203000550b03200c08a10020701c024062101c01d590400c200c800c1460a0035090000c6e5a03481e0011342c91601c9100054455421005088042004440010821003198001340d07008084060000c87d013820840100301ca130482c02011224210300d001c40801c040795102c00000c0c222500142010074408404004038064898a0000303500603031803056100071200301150180842c0d51182c000c00014480b9240b51041c2d1000303102c1c0314016802000d80318081030341e100d88010440c440c402241d00080c100b1607202e060717440c8170760103502003a555010401800802c4c090140e000c102100a549001c105500203001d0b4000508054201451580 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 3389917 1250 3388667 3388673
    0xe0f04050601120609021c020c030a0e030703020d060b040f110901030203040c0509040807030201050a0501050a03110a0e09071d070f05070602070512070201020f01060509070f0e0604060207050a080d050f07 90
    0xd50f045202c10314540038000b00f601c0d00500d80196001200d07081000d450040039080401d10b500c20745e09007460000140d450304450801c100c401049540c1082c0e898050343c0400001a640c40b5081d084c07444c428800840d00c425100c003003000300c41119102030315035402c000c0d4042401c280c0c0002c0b08c0e101402405d0061b03c940741c604240345181440e8001d140c00812003c02e00007400642e034044d01d415407003540280040c3d55414180820b5036000e110391508030041800510009035105040495540060100000f11780c0c1d46100c0c00c1e0a010545241c3c405401080341440410010311150400041c01d14a807069818500002407510011a01c100f04104010a2000400c18950115118103400c0320880303001d8510003603425040d602848049001d4807812014000d101c40600503507040760340003800005643d43e00314095680e90201b40381003041004090300080141e4580b406400a803000da4010a0258142000c0c0a82010300d83c11141495204100400419522004881c2076015146000ba00d42070146 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 3391167 1250 3389917 3389927
    0x20041503090f030203070b0703060503060f04020103090b0f010f0b040f0b0c0a05010606020303010e06040b0f0103050a02090316090c051201091503080a081005040204140409020a0506030405060901050105010e0f04050601 96
    0xe5001000140902c0000003890380c0000075007482030003480fa541d0f09444d0440141d040742c00070302c501505030304004c0014440b21442030500303500130b0042c1408105039189540b11001008110703028038240645e5001441080700c40c0e00c012000c1e0000800e4640b40504108074a240e0b4a018451850034250010b03805110316010722001140547c010000d019403521800c2c0a034582d0400d010f000e800083d5240040c0300c40c80c03e8000c80d1001c00300a03291104400c1c60074011009401d004150311000d40c0c08000d840150385040141440022040d40b002001c1030134150301405440003a0000f0301080f1041c011940704140304840c80f41100c3c103040b030025001c821002c4101494501d988003420000d8003191003840c064004150600c00d00c1c00700140c00e0404d80780d804101c100d01541c06000340191034140014114103055010b404424001050412001d0780c0d41c001808990040f1821111b0360402c405010010200340662800b416090030418440000d0750042180788041e98000742c89130352144082a43c0364055 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 3392417 1250 3391167 3391181
    0x605030c090612330717060409020a0512010519090506010b030a0f020a020309030c0102030a09030b0603150124020a02010503060402070615060203130506030f0414030c06040605090120041503 84
    0x808642920b40440c40315200003000700c5600e102c2031a1031800003541a1b209402840618160041c0001c40d925820700b4800201000c2c0e00c101c0c0c12041c070510205180e40e40200306000b0311040c034004282860140d582507445841c00300c0b04d600480c1020301075000a400894400d05640c46141d540e0f840f039a84a807040060300c11080503114451001078000070f441d501000401e41d0f032030250103e0300b01c044050012a034910480c0150400118403030030900019120520003500b01c01c004044480601c0310130200c1c1c565903000c7c0d000883c11100b100c804607005024605100c1d001941780044d200c000c1064001a103540300c02014103205a50019171032040141c190300c02102d102d0460000f480070b030b48900000e983d99001100180c0d8070442e010300042e10345480030849202c1c1904c60150034458a43c0e42d0b1340844141160488003130740c04240b000d0041d42c003040004a104900038030000ca06800e0249019084404421000068800305070910544042080c2110700301c030f000c8450090814040303402100140301c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 3393667 1250 3392417 3392443
    0x20a06090c0302120a05210405030105010602030702120102030106080103030324060206060111060c09011103070f0309031103010504110f0111030c010c031104030f0f0609081b010605030c090612 85
    0x5806903040c184070040d145441503034801c2d544100302800c4d0302c0c1102d0b59200781c580000c00710350108666412901305e600320301030000320b6030b0041418262141d0000782541c2c3c0c240c10000041c4d0001c1a48029494070840d403e500c41d01d104000c42c59035040c00001050450140000b07403e00da101e10b120710180426100301296121001d090780303826510369500035102d580984007140021001150203000e14800708003180656100003410b0300d800240e038019109a07180c03203520021800140100c0b00440c880103021012180703c1c1d501c1a140c6420b500e003021801104640e140d000c2d0f8903102c10040050710b9200d02c60101d4404540d0a4001140c00b40121f614240070700001d08580808500c44d0300701407054006603031940003071f20140248100141c00425130702a80c800a441d841d9012040808110001c1031802d016004503c080ba1803462501c6001d001e9019200600940721004220f2010100030f00c240310140038200c1c040d0035940c80344030005881c1100078240310301c92103400702da401c0268401c0103280d9a00352 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 3394917 1250 3393667 3393671
    0x2150307080603010c020c03070e0709031401020309010c050403030806090421050306030c09040b0106080702100c17010506030c0711030705040e030301030303110f042105010e0106030c0905010b120403020a06 91
    0x1a1012008104040542d09240250f003080582d503030490001c80c05c03040c0100c001c2c00510607545041395214640c84c020308820f0a1042d41178011000c19110038440d013040051400142e5a81000c4a143d400c40344400c49110400c0f505000c1440000d92000a241d00180c04403401c0c40301e070310356092010140055082503411400b0b150b40c03040b001500400910301c03d100880a0300e15111920040c03126030041120001d100c1c203082001444102e004000041c2c125070284121810b42c2601404401214181d981c17200100c0c40c50070411402030911240207026000035601c0a0440c14000d524003014050480010002161042281c03501d80b01040510000c043c0180706010100b802802c0a480354004e000a9002900300903001d1000c0402c403084620803031984800c186050b1801c04502415542c1030308404017200e90407041004035209000f504110101e1800000d902c9196203460b2004125641c0501700090824004200d268080002d40d8403107904006159510341d242d10f400c0381024044c40340203041c18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 3396167 1250 3394917 3394921
    0x20c04051005090f0709050105070c030507030803010905090d120e0f07060c0203060a05010302030604020d0f021305090106050114070318030813050a05180105010f02070801050408030a050106050403110904021503 93
    0x200381032204104503070703090710030341c0f4075448a10500c1c07000101140c07103001007540c01c01c0401095100d0300040403c5405030b000420402c0d2241d032203d00b0000f9940c01541c01c40383c00b000601c500b40403440384c1c5402002100c0204524543d81c00094100300b519041c6503610390396004104048507007489440c42440541003a03901aa482e107001030070340b8107051400c1c0c1c040d11a640000e01c158500c1d00c20b42e1306898008004000079038480d420080000c0308600212031614080300d01000589800f180341d881258050000300710b030720784100d01c0c2c0d003110016400346041240307000303200c40600c0a00b801c40c0d06203505417910011207030a4180c0d200c64604158001456050001403030959859409a12003e40d03004480690f10596590104500c200400a002000c00f40000041241d9070003541000300400ca10700583d00c00c40d554210b040c1c2101d01c11103040d07902c0180041003268002584c41032601420050030300e00e05050031a12030b51880ea84003502c2c28010000c01000c1000e42da02c10300c6940c90400104921a524 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 3397417 1250 3396167 3396181
    0x1002010617060405010e0604080702090c07050f0109030e010207030807060e03090303070501020702041103072c0d05060a050609040302030a0305150d03030f1103090307020402091201020406020a030e031b0108040201020c0405 98
    0xc2c11080b80c05a4055181944a40c0c0c48600070810502464025070800e0928802e0740800800034005000d00540e03003010011000001e4040c040c00d44800951000040c82c1842410040e103603000e0350100d00d046401c451014000100b06005031000d03142c114400069604c6003200841c07035441403001071545884003090310340c1000015001040c2c2c042c801d58081c00302d4140c0009100c0300d40429140c1c0c501061600e109040f59819200440003290700c2e40c05000d14480181c004640c2d0a19055010303206c941000c801c20511a00d00d000b4280c0081c002e071510205413410b614001e440e4050480111300b010303181c1000c5507034039041250500b650328004014100c810424600030b8000c1c81c201c00004083d509006a04031541d038000d056a01c0f0310103d0016600d8460b0b65404c0000a5010300e45c40e13079204d40b4981c020b0603910005d00c042c0000e000550018010340025040c041c181d6015194030500c290702c1002c243c8000e0001102500c0020020b00301103445031180d00c01030303007003400340c0b0f88203900185004100a64 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 3398667 1250 3397417 3397423
    0x120601090606030b09040f1703010603020c060c0301050d030f09150314060f01090504090602041206020702120109030e10050c010504080301090e010603020f06070c08070b030601030506060909061002010617 90
    0x4039403040e042040120741c2d94106605a5050b0b0b8484c950000c48000040c003c60b0f00b554502d064988034401804140500b8074200ba0544c200381c000500203035000c2740482c1c00390b00030052240c006070f40c202150300390361400e00000c1c0c5075050800010100484040390032403540c0a000c0000281c0008110032854040000c07009008002124207151070f5031180d00403039103504080710748004d40c241c10f9480f07981035402e040610000c0d203d00481200d505070700f00310004068840b002c00b5202c05100305005a518442ea004221680700c0702444107400345d00d0710861a00290b0042602003000030141c2301191403011700e4200391160700031031110711540d508140410080001c040d0085040c5d54401000308001006044600e00326509800000c0d001080903100c600c1d640761400141c01618442c0941c60321203615800c0d100e017090340c0c1d03602c45a9030b100040240801e0750707054040c055114105a600c03508100307580001031f140d84806040c1134010288440c507581308500c02c1d0840c10107080310940001c005038a02c504155 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 3399917 1250 3398667 3398669
    0x8010209040501060e100305090c090a0c110303010b0313020604031b031707080f0c07050307080102040501030b092202130213030507090c050307080601092102092d04060902120601 79
    0x1224601d801c0c004031320790380642d4a003080044080c143e581c40c809448030a030001d1001409168043c814408000c0b034940e1000c0c42c00307128180032000480e9024064401400c146400c106051854005000502002e03800744241d0340d100c4c404070b018614410b45800824270300e100700c0d080900306416000711040c01503a4000e14804891041c110801804101c000d1314102b8004c9546c01041c480701004200d901048c48005403800d40312210666504d20394a0300001d290200c180e00482c03283c3d4010604014940c2c05208281405a064402c84103514002c8940c0c86036040012042e41c9082c0c41460314030643d22000c000701200651490215034908494408107100300c8c041c07000b103495100381c2101181c046024001c0b995000c4158950b0b44c25900d45040c10b03a02014000d040d18100610a280001c22801c646100d0f69144450415440c0303440882c018404007400090400484007000d00c544941402c0c102c078014816a0b44000ea203c06494134030301403010b4004010003a6001e940c400070301080e004003040243c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 3401167 1250 3399917 3399919
    0x70c1a0408070c0608010501050901030e01060b0301080f07090204060507030f0201092a0b07050604120c02030304060f02060717010618050307090e0f0105090d0804020102010207120f020d02010207050a170c01050108010209 97
    0xf80365a11a000ca8100c035090140d54005035003800a803c295010382c200048000a01001003202171b111919070a007500242c1c0280c1d002c0c1d01c10403c40714488024402038000d0000d102081d40342604210002d800351042040040c2002203241c08608213500c02c0d401600b14a500c0281071a420300002c0032017010f000d03040c0705070003100d0b2010b00c00114004944100c800050740400580f0780e81d6200d44a005040200b49802c100340400d0f94804001030740c05200a002400300d6450303284091010180092501d4401070003442404003078040d0084039903a021003107044801d5840d00c002d00d00c2d50001007010044466010580600c1022404a807900b070700d810820103032419408407000c072a04003010900740d4401b13440f1141680c00054820045500c0b5510b2103500a0060001510741081941c80f0003220342e543e030f0020001040a051901c400b41e040c0503480070ba02c4544002c0d0308104150302da82e80c60f4941c17108002c00d41c0c004840015501100d07481a16035240903c0c0c002c10103580c0d40c0b98054042d5111110079 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 3402417 1250 3401167 3401183
    0x1611010f020703020a0905040203030f03040b01030b130209010306020906090409080c19080304020105090f0d05010b010f0302040308030a02090d0213050403030b04020414040f0209030d0c050d0509010503070c1a040807 95
    0x610a814030000b140c60499030000d20015410b0303d808907580007020068410782e00342c001004130705d071a07001d4a001940510f1003425400034662441c14070b40d894401c0900490b01c030286003452100981d95a079562415650860070060f920b60a410010304544500c56005030041e080041c10700c1030119610142a401d4001c0e01954500c00c50310303445030344036001700c20700270b06095083c00810059440351019001c2c5a10140800084007048800924502c1105101701c83d0343e91207040d040714559000c141516851003e06080d4102401c1d42c0e0f41c0100c90000928690f40329178003203600192a56045194201030760050030581100c4620010f140141c0800c9500350f02003410520300c810542006e20807030342105d00582412504680d0541000040c4c0a0607100c1100160240441c0d602c1d5502884074100d00b00464458038200081ca107031172810098a425060b06110f03050058a00590308581200e601000328030700f00c03050304020b10b00220142d200b01d101c04107034110041040b04000d001001030414900840710 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 3403667 1250 3402417 3402437
    0xb040b09010b0a0306050702010605090103120f0206070207030605150d0b100f0e01030602030601030603081303030e040501030506010506070c03050106180e0109020303160203010209060a02010b01110a0f12020102161101 96
    0x11a090b078648002140d0480078116040020461981c0803a8201c002880045840d681d964000b03140582d00307030010380d42ea0000303101500c0039640107007006d8010f45c46800a40380c41c1c602900041e440780c10320311001d08440d80300c1c0006050650361002c1c00e01d00d40c3c0300070440300d0441190b09080358109012503280c0800c030915000030032445014040d050889a182145901e0307a0700b540d4421002c0d40010304028103068031060080005803100001d010182c0040003105035035480c6003401070003060700480d10303801286050300502c0450310108416042d03500079039140d95280344515008980c00c3c6541d0014105510f0309001140890f201024006400388090050203541c2d841e007038280c200c0700d4211000358154800c0040300200506a0304001c0c5884c00140018100700c2d6100c0890380541c0800e030041700603592401086060b44c4c10800c1c41e18a10003c5008004080b59603652011070084010050030203016600740d500000d04c00d404464211480304052801010310f494502842c800d891555800301d009184 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 3404917 1250 3403667 3403681
    0x20f15070212071706090303070e060d0f0c0306050f0306010603240602060106090501020303090c010305100305010212060405010f030b060904060207060903020c03070602010c080411010c0206030708010801050601030902031b03190b040b 103
    0x90b0720780039131581801f840c5580c0f5140c10540366022402d00058001500744024400c2041c0e9120701e40c85035648081c046442500707414010100c03000d5800991207940d1068a0100d6503d00003190f5054585504000503a240500c0031b000380040311010942d18250382550114025502181c8a0304130303113003600c40c80000e644801c0160303100d00084844040507070003d84500c0c2258400c1d00055000802c03c0e4000101d10784036152503080e6070018184c061100e040400f13000d85418540700740c500404807607071801106825a0fa0320422000040d1030980b244620001003810300c010741d41218215544590208aa10030904d1301a441c4d00c001443c0710f01c02e0080810010b81c8600600491001010594900c00700380d03516596120002201c154560411028008040058442d18011806000c0c5074440004c1e41d80340c45600703400d42d01c004150904260070200e403080142c5000500103040520503103004603803d60b80010030301c3d000c06551003020030410b00079603c00748080200d55a024a01031105410305985040f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 3406167 1250 3404917 3404923
    0x10e0409050318060d06080309030c030a03020303010b0904140106020a0501050c04060c02060d0906020c061b090109120510110d061d04020607080f0d060602100504020f150702120717 80
    0x910107891900104026601c3c10790010246080000003043e09040a4500342000300311942600400344944c000070f021700c2c50345001c10840000000440c01084550b005540003501c5c0e002c184502c09841901140d04001c5d9522608048105015104510003070341c0d40c1c140003940c450b410743d416202e9510781004142c0e07149078101210142c3e9140c0e190700c0852034059007403020070f41c81043d0b001c140d030b13030340d8a4020009030150001700108140c003001800b4900309903102c40080740c0c110400039404a0b08200c061466604002d02d00103d8120412103407210000e41000c074146800c140c8481c0c803580ca4294034407100b000001c054440043c3d40d41e805c001154071a0b0200320a06080c00e141d09074246035100190040c40e000000b0030703006109029090502d03142c4484030f030403908980c00501500761181000d10019604001d00401c800c6424001d010a0405070081906100c201040d24003425844035103241d201404000c42e5050303a4040c0030703541c08100901c05642c641d5124041e43c6042a400c120ba1501c40e0800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 3407417 1250 3406167 3406181
    0x30d0912080f0610020102070203060f0103031707020d080601020c0405040302010f06120b01030204020702010c12020a060f0513020609010207030804090f060e090d0305040f020d0f060f021611030c0a1202010e04 92
    0x38800b0301d038071501e400301040b21299940c090101159020808240181c8050003144c0c042c1203022500070703495041d031030080c0041201c1d5402c40c403101002810006030640c00a00c580c14485503080031002e603112000103e0030325650350003294106003000305020825505600003c0d80c43c00d190000c00c035181d10303820105103840e1040d0018140186000c0140302518042d13009101084c414100314a072011a41d030340c051062607140b02c01307026810000605040c8021781c02000409841c039481000b0a01d0041165242052000400b9004241c0481e11940d0740c0d008000035000307581c1028549851b5a541c0c0c000c1c0c40075004484032480207030304002002a80e0316981c1142406070114101501c1c248014103011002058000d10680d0001c0001c4035030f001503254070800c800d42e5806140000c90b046124145482543c0b2240311501c481841003196040c103140070518810034503401887c040c4e00c0c6a002d070019280c0003415035582e521403a00c04001a0701c1c8104603901c60218801c2c1c0761450b60301d9007003040004480c0c40c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 3408667 1250 3407417 3407431
    0x306060e0901091503050703080304030810031208040201091703030402040c0309020603130606090e0303150312070b09030f03100801050c031312020109051905010b061306140c030d091208 82
    0x81c50005100319002030b003103180a41c4c105000d100d0b02555030f0300e80b145021250350040d218950000240300905900000255002c182009160100340c903550303d403001b255a07054007200300501e04003c5011a03108240013801018034500d41c10300b0214a0746a50b482c0d034006d0360200c0c4118546152040954080e00808206980083c50103040daa910303402e004000c0e906a008843d0710380c2c1d83c50040f81111003481400b01500e811001907840303103808805940504c41e04101280303c1c2e4003440e80c0c1c500d0342840a00b01c40d040b99000125420b1501c804114910b5409506010500c5140c080204070316105001c0740101110401e00080c4520b842c0c45400d04140d22080e45c400908554510801010444810990710040300c0d0b8400003488000a40300c040c00c1014076401c08040d003024403801424400c0034010945003407000c550551411070b070200b5403c9080b01e24406e9106005001710808800302c2107030306071030104014000b5280d0b41e5201c10300c2e0b40c00601d111141100d00c0c1060742407507200540b080e60b07000d1040320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 3409917 1250 3408667 3408679
    0xb12011505091605121315020306040e0106050906060c0a0b090604020102160b0409020702190b09040b01080606070201030506010c0506010605030f0109020306030a080c01060f03050a0201020c010f050414010c0203030a09060306060e 101
    0x6a89071080380900046c0030914144001421400103081d144000c0c203840460580107031a400c258040109941410000c1e2100c0e0b0304107407041c0500c2c1d40f03106807203822500480e4081d80c0c1d001c084941714108220f415010340400c03070442c1008446080442c45500c118400d9090301e007404e0140382d84083d052114050101d140c0300610040c0400000c960051034170320300003441c810290f80416030440400500d904015400d550208078200107080c603004441410609081401d81c0c1e20300440030401c54000c12401030f04042d250310202da0964080c02b400120141c02c0029100b056031100405001980b040e2452000d0031070280000035150158800d803402144001c000c0d045c00c121944541c80c0c1d54220304070040c4255a203240000341d541c0c203161040000d506c244060b000c400700380d000182c1010b120041c13480c144185502e6444880c2e5210088900f90303161000e4140a0600c00c0004941c1c86644d14170003034040c0b00018a2282047c0c0064109040b146503035410321240d525904221082101c070041a44c00c070b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 3411167 1250 3409917 3409927
    0x7020a0803040314031501020d03020909040b040206040e0c030f0106030501030503070f060605030102180906010503070c0f030e040c030203060a0503070b0f0315040603030f02070902030408030a0b12011505091605 93
    0x500e0311402075820500034507000d0080ca0303005400802640c03042d20301d002c0300142c84c24108001c1d40c0512490b44d45051a040850400c2c42280204840e0000108000d02400454002a04640c1c803102510044c051000480f04c142c0707070080d0103c004e5402500c05d0110103502c6070001810314481d0082d00d060f02d5100020b5420443c16643d00c621585031a501240d04c543c0390400402d580c2c60034405070255600e4203015003003801040341481641e810183c5580d042141c208104580c464101c08996260743c0d00c41c0f84c0c0200e00d080b6080454552030309038040c0c1c7d0311a051003800030a15074140c01075401820304607200360034540c1e100101595601ca501c114465070300b083c4121000402440040c503032116000f4605107100030a00d00280889515030801c6010a00030000a241c00d42e040020780060081c2980451850400c2d4070345c0800b50100801490750b0a485200391412500c5511701b10100c481c0074002484604d04100004400070340c0c1e802400c0c01000d598000400c44080700c01151224003c40d150b80b8605 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 3412417 1250 3411167 3411173
    0xf0905040609060e030702040e01200a030902040504030509040b0102070e06060d0b03070308030412020106080a080d020702090108010608010b0415030b060a0305030705100e1501060503060a08010905030403020f030607020a 97
    0x509402081651003942e5006400e0100d0014010110540829809103594400510400040b40e15140d41c2c00101d078580742d080807540b0034601162b0091a41c150320b83d82c886180c00307800c401030300801100035000350401080c40105a04107000d41400c075800c40301880714611601c012039881b0050b10600403100d0f6440c0c00714045003403001c0182808015480045862012800031901d82103407684100c4203208008100130922101e0044001b100f003040c0700030300001d403614109a03503400c1c50000140c00400002050124046203031f049518155000d094079103e5139440340214000c01141c82402031755400c0441c425240c0c030700fa104055894014502c400203072030a60302e840004120043c5030b150440311071400840441c070108003130280c41d0b101c1c000074a02c000c40c0548440075a01001801c00071548611048082c112070050064159202e0b480c05580300c8c0e80301c0d000501303042400d5025500700d5180042030028800c000c001481070740c0c02501e41540c0203246800340b50307803084200d4084005800809021f400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 3413667 1250 3412417 3412421
    0xa0902070f0b1008060c07030e0a0303091a0409050a09031206050a03080309030f030c070c05090106020307060f020f0f04090506011701090507020a080c0606011404080304060c0f0803010b1305030102040f09 90
    0x240c0c609900300d50f4562100f0780980f4013007007500c81c1511041d01090620806074042c8000d0442c03441a580041664a95900609274440300d00500c4603940c26034085444150f0f690302680c0c0140400813003845203081200c5002d0081c81180d0056001401c01d4041c2d0002903214001e15040398405002240f80c64915200c2d031015401c0903000e1034103400100060f51000680d030024500511140c44165075803403640c034000300c0610140d84030707a004000300c4004025540c3c02005540740030b40c0081c804501403e000c01020300034410000e001e40751160100d07026440c0c91000c40a00b040c1c4a40040070400d5460b07500044d00c1000d0f40c07010071281248090014411000c07650007036034000050380101e56989000350794940c20758008008907013481d4001020810304c2e40e4004030100719140340c0d0110390300c3c260800c1034a0f070326841507004400034004401a000204003100a40d0014680c10201c125101d58458003103510640c000c00d80e0b10403805104c0e8002c1068601071088600311040e40b261005191300e0a141c400c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 3414917 1250 3413667 3413671
    0x1903020c0a05030703181406030c070303060510091403010216031407080f030405010506010e03030d090201090509010303020303010608010815070e0111010504030201050915040209071404090606030501050a0902070f0b 95
    0x24a00a074041c0000061040016000141c46a111a21415192075207242c09800550120034000d1a400c95448643c0300c175802c0300d802c0394803a003400d40c2d5440d00e41003d4000e01400e034050350b004030b4020300e00020306500c03052040035500d17041503c46d809030000c4205401c0c2e026200040401401c4e02c4400c1000900801c0c0811140b00001461803d1170311b1605c0d00344458200265414440c80c2c0001040708104080c400c282e480042400c007400f8108c071240100366603008200640140a644031140c2043d60b0049644200078030000f01218003960f120302d402134513500280f14410100d007210b000410302807008981003460100d024450310a59540403411644402401e440c00e040c0318002912541c05a8280241446980680c0002c07507141411401e02d840c04903146042d070070400c03443c014000140da0300b03c4056007110051612590304c01ca02c8180c005184110391000308118a8150001101c98040d00314034103e402c101c0319650400c0e52082c2d520b040c0c0c0320b5000024243c1c421408030000003420007556076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 3416167 1250 3414917 3414937
    0x60e060a08190f14010501020102070b06060a03020403060f0207060c080910020a050f0a08011a090f060d1e05040b01050109030302061303050405030d080a0b10021e0c180702060c190302 81
    0x1600c00411107258008443c150f01e01012980e403501043d010a14030340c0031041c018182840210302c1e10702192203040f054000034021910810001400441c118401c0d0140e8024640112080040e01c1201e0f11100c029407241d0380441c1d125041c0340c0d54903013290003681907034801e800d40b1011303010103680302480c1d60007940f01c00120390034040103024542c1d2008171240070b89007419698441c100c2a50511409100d1440b19400015801000f04080f9501d5118040d0780940d242043c1d0b03026450700400d1040c10060407107c2c41010700440c00e036003005140032154001d00d01607030051b4044070450340c0300c40c0115001e030140d000140150f407007000814021062844000c03035242c0a4a050313803c080e19180080d040001d09025880000c02da00d040c0522070b009803041c940900021500084c3c503194910010f5152a4a0241d1110340036000d100c8141d445028401c01200c060024440308101079036420340c0c04205815203001005220300c40026001c00e42c60300032078441e034020380c01c10940b180c00c1c40c030114041d5010503065 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 3417273 1106 3416167 3416191
    0xe0d0f0303050405010e01020412061a0d0506040b0a02030402010f0c0507030b09010605120102191407050303040303050708090a0b011e080303090606031204030b01030b06040b030f060709060e060a08 87
    0x2c200c4be9010f01c01282d059031440717200317a019000c070301105c2e00b0051144507107042000200354540300d144a603090341c0c8542c40d070203010400ca02048800901042d2b800a10b815100d008080311110701c1c0c070135412250b0468880c0c2c2c429000c0642500c02501c107a4440e802440245403c4030302001d02a5640d00071420507400003c02d07590820110b40060a0041d070b03010500b5003041c07400c2151841a00207086907520304280c50018020101281c0b008002109000440c20038400807c0c2c90403034075009180000c0d6a401d0904d248038842d40e9412480054829500008400c1000d0002c0c41c07140c1c00d003c0240c1038600d010021b15040417501155030103c0d030000c1005000050300c55407120306481d0803044010595644d40c000c60018003d0000c44d0b54144140040000000d40010b071682c4540e0840d03541108880d600c0c00b003a900c03070701201c001d182e01207000d024920030380c1d03c1804600d900460710481 = true := by decide +kernel

theorem cover : BRFrame.Cov 3237417 3417273 := by
  have h0 := BRFrame.cov_init 3237417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3237417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 3237417 ≤ n) (h2 : n < 3417273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
