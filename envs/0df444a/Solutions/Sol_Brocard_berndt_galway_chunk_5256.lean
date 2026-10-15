-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5256
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:15:40.544981+00:00
-- url     : https://prove2.me/submissions/532b4c55-7e8e-4f00-b25d-29f357133e28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 945143884 ≤ n < 945323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 945145134 1250 945143884 945143897
    0x30f0204210b0c19050d0b090f040b010b120114151c060e040816061b03020301090b01020d0c1523060405010b0313021e040c051209070b2710 62
    0x81c200300340041090b6200b610a420503080c618003800c06011034100c0225030040050004842c1e075640e03000d40c05000c0f03892002e0301c24100e074613106940e07440001054800780e4510200308000568104510120b80030030010010990b21646446c0000443e00448a2030540c0030101540da03603110400c06000c1d060440c014004811595a0390b505501146e206d90021880d0380842c504000201c2c207200100c03a44900e0b04003032544c45644909180340100601000454080c18103409918a103500d5009103050b903540890801c131503040d01005a07a01c0c4291141e0a01088581c1c0e1488003144207544802c409142066001c1246490643c000315400300030070000400300002d200348001410903210369409842e19501441c07440c201009000d0750701c4454040203104040c024010724003201055041d802c1200007400034031038190000300142441c0c010803641084081200d00103004030a000440d40704581400c0040c5141844d05c05086d6103040304c1282801c211820030103412816103526810300d64482c4160703240c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 945146384 1250 945145134 945145199
    0x130f02120d08070f0801032d200a08010c0206010e07110a030c11300f030705150f0403050a050d201e0f0307200f010b090c070b0106030f0204 62
    0x1c0c0c03508240c1c803444e904000004005100240c0c000c20b46012801c0c0342c07480100840c2c2c2511300d0005032a405d40c401018440d40120000070311103020540c174010f480072101401144e0b140c90041d400c880590990781d00680c0003400401c105110b0700001a080f81c0c05150101380480c000c1d101920340000388030f048001420303401d452002c0c4900045002c901900455a28609404400a03850014017040b86144a41c22180019441d0082040115003010004040c3c98a400d0103090054580300710400d0700200d000d05d40c00041c0d040390034200540c4a00e505488060410511704400c03076060b00510113103260655984400c2c403445150380134800700181802130f02e9603142e0001842d0480c002c08040079040c140400d00031181c0c0d40201c103065990184042c07030700881c030000b8800c81d0308112501e5041080a4003c0d07010248464106410000301000d0030f903808501521508518555071003490405442509101e0040c480750703220750021100002c2c1603102505060b182c01805400192440ca2000b0404420040303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 945147634 1250 945146384 945146387
    0x30e0a0f0b060102250e07050c250f03060e0c010503070f030515120604060605010c02030a020f01090e0c07111f08060312180f010c0305030403050d020706110c060f130f02120d0807 79
    0xd1b2680004640b82a038200341c641d6040c10b0b912507582d050300d181ca87c0c0880c0d280c841004141040402000c2c0e21010b038401e01d942c0e00b080001400881e1011501c0d004005603000385500403c126401002690b0b0b4803000070220080c200c2c020070f4090513411100b0780d0900c03100199a00e1820700d001001814018248a0410b0b20b0100d0840e4030039400503041c4003244440d00003582e0080b40044015405a90051303002000200481d058030564010200304494142806103496216018002092113800341041400d041c0003008440b00100019030000b980080c0c1c4400c0141c0700d03002c0307030350054406000c03501c0701c1d03016520803d2142c020328070180708801d48607041c094902e02075050048140d02801c1c561246c03403242c1c41c01022484028405418005d0008408601016550480300b845030420010000008051803048840d440020711035510f00c22800412600c3c1c090001d403500640710107142e14000c03201a901d001d84080c008600741d034041c03000070b207080c20040f080c01f50460200381943e840940c1d182c070950 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 945148884 1250 945147634 945147659
    0x130903110f0606031f0b090403170a060b07060e0c090901090201091e0303081308130311040506060a0f1202031005030d021b01120902040608010b01030e0a0f0b06010225 74
    0x80c50703110361103034040c042d50740c0300801c84001542081000410f0100321141c184040e044110015070464600307c100030a0560100c1c0340e0300d0402c514001320700d0175101d078140c0c002525214024050020410002800000d440f03900c0080002c10300b1050702c24545018000410505080340c50701c9841e51200b02076002c6603801004840604490081c94815103074034a014404082a4007004052101100125038880380c2118001d141545c0708020a90710310100f007170900c0041e81c81c4030440b00e00450803009191840c060141604ca644064070301424003003c02c500b00c1341b0740b107201ea00f6400c0c8040c941500700031003d41c0c002035111f042011004031300903107004140340c680b9126410040c11500699042d4078a0095184464010340c030034a0304410511012000354000c080d2840003d602a140a40002d0701070410b400207013082100b600d0400008051003003003903c400b00184010300d00240c0e5a003c1c00040c02038038440f03401117010b204503500f800042d011011101c41070a004c00a8100c441c0c1c04201c403281070706 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 945150134 1250 945148884 945148903
    0xb010906090212070f170403030f0e06060d02060906090d051c110c09180105071809060506070b0c071707020f060a081513180c0603020a0507030e13090311 68
    0x114214540b25990002580000c0d001d00140c2c01c1022005c1003d8003148100329a601780e0003070480e00351a5041901d4007800a040841c41c0b201c169081881900b40035034040f030014450380d400780a801040020b0750070032000d5030101f00c1c1e00d80d120405210a0120f40c448003a88411303640f0550040041c1e003003241c0105000505a0141c01c20001d0451820555030700c0802c03040d03444071080d10443c5a6840700c0765800a0b0700c0c00d075103500b452076107024204a4100c0d406013a084200342d8038444010080c3e20780c1003d0701030f0355040c02400e400050411688000416090003181c0c8400409402421305400366117041d4803000032502448801c2001c03410800398a00500c0889070304104480c01071512079141409401c0f181c00408a80e13100481480e04242e50f1214010414000c82c1e616041055407816401c0c01090494500c0644054114400c0490101c2c003d00c215660b041054440e0360811304c143c0d40840b003900c40007030082d03004090310012a01d0b0002ca03026034a40c05111340c5851040385040d40a00d890000b040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 945151384 1250 945150134 945150149
    0x7080c1c020a09050c1c0c14040f0303051b011103091b0d060902030c090a14010909051e1c081f1410030219110d030203061f0e04090b010906 62
    0x102440165100c2c102c0008440e01554041840c1c0d440d007000741c005015114180344500c090040480b5400c82c0c0d81e02c1184400100d440e005003403009500410100e00490241d090002d03031100d824400b00340100d01030400d08848070b41c02c5c800310100009290075100c1e050701941c0492004410300006c9541844450420040c0c0b40c142c48041140c0300009124280104024141e0b5559400c21419034a05010000344110007600600441c1000154640144241c94508091896060021403c101203000e600040380d0840024083c05402002d00e021081c441d88945a003441109110404203a030a10250300c00c422545031726289140008076070940c0401400200e000b1500c2c42030620001811009440110005640049211410803403c2d8028031642d10101589035442041c4286a41d10407035407160761500d941134400c030355410303030041c4c1c01d0340001d030f468645c004400d001c2c1c00c9050a000048181042c55460403441b00c00580c07000c913080310a611800d942d046405001440744020740c3c02440001d100e036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 945152634 1250 945151384 945151429
    0x90b0a0b010f12021b0d030b0306040209040b0702032205100e090c160b010f030201020d08040b1b04030b0a0e010b0105160209060a051302220513051807080c 69
    0x16100020000b00201d10a18244402501c0f030382c41ea114990305032403506003405010410412200c088555540700d6101e4000001d050004000301420042600c5000d15809407d010141c1c075150b48006d403d00d001443d010441c401071142400b600300c8181280c014060b017158101b14503040c41b00307100c041e1400f03e0f40c600620801455002d0242c4940306900c0c1d210000d91611900e070040059a140c0c21000d41c0c002601d5585030000118000e003445124501720b81c405d0b000c030f5140d1403181d102036400c0d0a048901801c107644c0400001e2a000740c40d900e40c444000c03000082443e0503202e5031082c0034610180c440e5903c00da40c0d412401c0796070200744a404103014013402c025041010b0025100608584880000e0003009080e010078000e440b07140000c005400001c08501912008001c070b503001390040c5890052201e401c41c2c81c568034800e074581c00c00540794050040b244045407050f90790040c00e809020101c10328026004405482c806000380009090003078050300004c81004c003088000b030f00324250740c1d111402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 945153884 1250 945152634 945152651
    0x306060a0e07030b150a0203030105030601140603130f020d050d08100b04052218060609020a080c0c0f0105070c06060807060e0d0503041a040e0703050f060f0f1201090b0a 75
    0x5010038080d0303100070540f42c003046041001c40841c0754601c080568895400000c2401c2000640210146050b070342c1c10f500f1168181e80e0340a88192581740c0526140d0031030700410200d07088155904448201c02c0c000c2e40844e8401c035003680840c4c030701150041c0549090300108098120b00c2d6010b40e0554205503a40080c280207414400c4d010b003184079902c5424070540c190080075501511490521246051110040043c140e015050503d81d211400b01140c440d03103080d002191464291080c0c405008082c0e4070001550348000c1104010751026443e070110348905c8000140c1d0703074070034042c1c54481c080550b03c00d0148200c2d491724206a41c03150300861490b4102503024458280d1104110402010466600160081c541407160071481103410101ca20765480101403440c01d10100240102d03000c00c0e09004132540d5244040b41154000d460b0f448100c020784000c1449460080c1013002d980d00020032201c604240000050b0305803a02d44040c41099459800e00018020b082107026446162501e0500a00b038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 945155134 1250 945153884 945153899
    0xf0303140c040825090c120501140321090913050d0905010e0909121308070b1803010e0604081309020c0d020f150a0f0608010213031509030801030f02010c0f060203060306060a 77
    0x10b80d01d001d00117a41340d40d11142070380030380300d524002c6105c1e400b00410061746d41c45070b880000414144049500a10828036076552030f103000441e910b22600c4110780c20741003900c0b05040010501001c2c04401480400130110000314006109100d07506445841d01045903241c48009024882d05204036841846c8100c00c101c05a28041a00042407454240c0141d54108444420441650507049a4203510601c1008910b0b070000c0742c0245038401d49a0300740000b80701907508160070703610882c0008403150003d40100c2e0020f610800509a2007058081e0158019141c00315041241c00c443d80729040303584102424840c50360144000040c42914501504101c088800040d40030030000d010b100c080c655412087d503240b15154412000b0b0214400259a540384c141008200c0c007040b800142e4107840c0c03251406200e04103034482c0c0d08042e0b40c0768581d07905a038a0354a13001c9072200d101c04240d0500004164078400114540000d00c1181d00c110b1740180c407400d01038141850440000c01079401030441007010312804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 945156384 1250 945155134 945155203
    0x325050a080601121b090608100204080c01030c1e0305041a13030f120e0f0f0708120904093c0305090405101e0317090d0f0303140c0408 60
    0x110215944070b1040740720f919142c1740d12420b08440030318214041d04080f0f03035451585c100b04102c030341c08030440700d280c0c2602101034200d01c5244121007450b1b11660344000b4035402900541a00060b5050402c607184560514100c03100581603c440001d549508100800c1140c50307008418200f5004a030000b850010a5039107031041c00d0102405000c0e801508a525900c03d600308080b208104009110041c0c0c6401c10b5640c440c107010700b0458600441148204e84880040c14504550440000701140c0760270303040081003603000c5454550055224140c010110380d0281c68400d006045520341c142d050003603800c6204060015001e0081004515009008a07900c60140c8000240840300055603486442e00c9030003008a60340000c00190003201041d04c2c40c8151201c0000303e07800340a00c03840141c100d1704540401d1103604130b060780c0b22000c00d2509000c11030888a03440d0300c5200e41030000304411100411003a0340011900c8810050001030280000d80042c0300b00c1c03000d8612900040081c1d13030000b8006862 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 945157634 1250 945156384 945156389
    0x801141807083c2d0d09081e1209030312090c0a080703020a050f040b031002030907050d0f0f030909020c0318030102093a050304030309050105280c020325050a080601 73
    0x70025030303c0074524000a8412100200d003114044400009100801500902047c800c070007050042660b40c1d241c0300340340034070b8070380919901024195541041d500c810144d00140b01d580e80500c0140002c0d80101d510703501090262039180c000344521103101c42000601109500096001c1d000741d0400c100513182e0f06081c07015074000301c85d09604282c000020400038a589001c440c0d140c462421500740c072440a03402103000d1131559041d140044e4860080c4018041c1241e002010b070b0b5017024101002c10080049a05c5851280c5059401c55aa420b400b40c00e076000303215500303865000083c114180b0702c802802030381c004806600a501f0044030b000060040e06881c00d2040860020301c6540704400c20307090ba120300b075411401c8405101d9245003043c82d5207400a0008401003043c4e0700000c100c5600070740aa40c514921003969046445a01203040e40f0011052654418004500c4403200142c0c1c1c240001c4001f002c004241144003281007400362600381d460780c4401c0c080c004446003030004801c0401c0e101d06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 945158884 1250 945157634 945157663
    0xd0605030d021b0103050402010e03160e15130509030c120903010f0c051e2a12042303070e04080705010b0a051518040204080a0c0801141807083c 64
    0x104c5607110700040e0382b6000048a42645801100903620703848500f10b04400030f842140140d00c0c0c0e940c0d500b0901c03d1082000c0003900340e00104240140100c09a02d8100e258404511800c0c0e038201740c5c7c2180003501d0703c981d6403000746038060085031b521180d04092040700c41c58041c1c01c0090102c41501e413405480e6100ba0001c8482a0304400b0250b11152207640c110b031407500320110200d090296490400d070f1030307940030400c02400c1d00600440440c200c2c0c851041d81d06541e1783c0d59140d00b004078042c1c511405903185201c1d0316018000d0060000341c108802d0906071045008140c000d03070b070300c0c110300e061400c4401c0c42d08400d118100503e01030086840d02050f0035145a808003039907a9846031041c03607480305c1c000c002c0b086d94090700005010903800404070311040f000788201c690107802c94440c0c00c2142038506d0180540d9524079501d00140700701c03280104400381001000f040e542c3d0552074118550400120701c003c0c50b0010900c7c102030105498640d02200001c486041080c040b444c2e44e0700702d0340c881c01020315210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 945160134 1250 945158884 945158891
    0xf0a0e012a020a0b0c0c0a051014160206040e0411042d0209040c020a0c0801051302040b0409020301050a290607031404080d08070e18010e07020a080d0605030d021b0103 74
    0x115250f41184501400c0a801029141c040d0101d4a6070785509604600740140c020203c0000d00741000e820b86402c04059494000408031241450540ea41001c4244c01d20344085d1009000541c0341e0310000d0007e0300f100800704131305141c9030400486007403010140c41d0090385054900e41910200d641e010850610613080424040604403001740030b40a0000920351192414115a094a40000d03005050382c0c81541c00e0084907669103400d90894000300d4902c1500d212541c0c00400500e0301d54085091110300420000d00c28400d600402e00310b4004035030300b003801c5036130f0066001240700c00300c2c90030407040079000381d1119540d04c54003207001800352007002800d01046800d1060b00c03070810020340d0080c0004604a4002d1012950b0040c01042d05441d10004078103117501141a81c1000a1600414204010106143e0b40792000e07204030b5002c000c240804600a54034488006000030005090020003901c000c10b155003443c003003500b0102c00e0b000b4041907502041c01038020242e001b03010071070f0703000908000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 945161384 1250 945160134 945160217
    0x5060a02031f06050a082208030c0408060112020a0f0b2a0a0f0b1014090406060b0307051317031204110607050a1e050a0605061906021609020408150c0403080f0a0e01 73
    0x3032b089402641c011800c03038018400086200100d03501c074540201e0007140c41c5041c4d00e989800c2e1031000b848074050104075003000c20045a20001e21010740200d00616800d007401007002d05d01c55420b003110381c0300031585103900400481c24052003064290704414020004d01c00c1e903160071404198221600d0409000c2c090385800641030090581c000340080404040c2159a4030b00010700230455800900c2454911510040109840b404d441103552a40070072002545050241e101460564100802c200e500706151490318015446800c09420700034800c03802000500020701e0b01d2080d031480201c8042484c02d0445405000c41c00000b480b0400ba600040000752649907200800c40d200c00011121400706c405c51000a00c0e0340d0b00080c980481c00c00c0310710303060340b4544a8010f18240d10840c407540744a41d2003201040c0941c2910300500c0d8000f5901000301e85031696a41c1d03824400d4110982d54031005002003520445640c00000d9000c006209290441090f01d15140c44c203841002044c52060203080070041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 945162634 1250 945161384 945161401
    0xe011103070615080a0b091b010e1306090f0f061e030212011107032c09070f0c0c0602030a261b1c06080c01080405060a02031f06050a08220803 63
    0x1040c0074090781c0c400d4503000c5d90383d4141403c0784c582c1580d03504080d01c00c0c0240402500481664085410030580d83c0e140f0310b85e10f0f6030070405030001c040c01101c80c85a079503800058910452246440420010038007203a400359420801e41100c045078860650341304a5201a05820b580b100641e0070b03a90b048035500c03290802481814018044106150b10400002491a0134144c0003600c0001403100305c455005152203125014252000380807460388c12a040340c000c1603481c0e00a817441c43e6100c0031403410540c40324039621094402e50321907020101503040000d59136601da500040c44c500d200d84103042440301c034240754402c41c801503000301b401c04454400201280101c005600b20307490101c01407011261306005401240c02013001c2c4c4600d213098402d11070303000000d500802d0340c1485981c0240c042c04495980d001018080d50000303010200e03814448802c6441d42d01c009ca10600501001d54440f62105024440a01001009400d0449148d05090f0041c00c0c1d010381d00001820940c0102ca041d1640c80b0900c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 945163884 1250 945162634 945162671
    0x2070306051f0503011802010e010c0222110703020307030e06092205060114030f180a05010f06050f1c140703031e08090a2907020d0e0111030706 64
    0x2000c49040c0418040e440851490620075489400c9860800c0c90f074030801c2508a170408504a4464000c03c00078802540c007503048180c1001040c100742040c1d14155001440200380164144c101c00018801c04090105034801d2130039100e95010758074a062116140650380b800345040040810607880035020490300c4810513a000780402503c01149043c207003608106100c01c10014080c0f89180c0b0000695562040406a55010038280414510389411a01e900814001000c83c9080e81a01080c4254110200075403406980200e00000b890348013080307206c4c15920316500c458803881e4415070310340da03640d0b5411048056201d034801750b2440315018a001d02d10f22540c03071548043d50050107000410b041c0c0088654006500001c0d105440555240040d0380c41102540d407030802d54041d040f5800020b0b4164580e04406076001080d00c4400300e00d421511401d00111080001a0094549031081c590000c1407500038400c00d082c181c03c80b1940b449956500d014005001d4445910f6000d01b2440c40d40c0c2c0e50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 945165134 1250 945163884 945163889
    0x120804050a030501020702130b01090513020708030c030702150402010f1808070603061815030b0903091009051804120f03090b0405240123010e300f1009030207 70
    0x50101c10710036900e05041d4002e401034501640030300095049148220750520a4040d81c11050316001c6c603a608101c24050090034400112070382e954200509004555510069841042e0746813440b9030342d15104200a08001d01044801c0c50000c1c0340040c0801030384c1040c85803500006918041150740c81ca60710075644410703560700c0101c2c14043c40202041103039154000c98181d600e07100e014610344401c0f12224003150034202d2151907001030b0003824000a010352145940004403501182d003000e0441d40065540240000454041900700c01c0422a40c20404504144295a40c1c807164540c5482d80369a030320b40c1903a00d00c81d820000344203e0340e6002e9010b94000c5509541000b2140c1c0c0d41d00c0c007071409668072031503c56102c010801e15130090b0303601c11100b4691410317180f001c80308095001020010080f000454400c09052240950904800d904c0d0f1840100c00685d51440b42002104159441c800d009a2001d684c10f07640c205020a00ca86400011035000700c810396100003e1130845400d04a0a00001d80c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 945166384 1250 945165134 945165139
    0x150606051603021e160501020a021003020f0f03130b010602160911160506060f0a03030c02130e010e0105010608151f031104060203030a0c0f0e0f12120316110712080405 74
    0x4454024001404d050031704042c0d1491189030b03110b0005a81d2011011002540078040440103041640300b50043c01c01c20a680000320305241d249480d800351900100d0300006805e101c3d50032442032203a4030136007500408450001d41981e11481c41542e054140c5401101525510341082000c8001200100d513105004811f48030b07449420392400584030042610b0081c42098000ba6007d154540305400204a0780d05444852500e4016424800c0308900e124103028280d40c0c61210740e800002c00c2c020600854a1080002030769810b240000d80010300c0070300900700049401d20050742e15242c00c4000802d182081d41c0002000b458443d00f1005000080400b4403002400b0400141072600000914040c041030441032008a03960001150550060f6102000080144086200c11b042c04003074103002480207068604580300d10244585401e490360b8094180d04030000401c040340911343d20091400f42285800485802100c002698807100f5006402052030200da03286d0402803014221002450003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 945167634 1250 945166384 945166423
    0xe04020d02040510050c031b100603030e040f05090c1e031c170705040501030f0e010c0203130509060303041806050d080301090f0501150311131215060605160302 71
    0x340340c8840003940040c42142d006020303815003084030030f00034415908141c00d0f0718011824140350282c40c14002d000001b45046901900d132950032004928000c440c0594001e40396a11106c20360710a100c1218003071400c0c84406442c080500001080203d2080407505049030207070719158400031640e054022603408240c4c1403040036988144030440350343c0c045901c4503503207407411200c0e0200b440a0b2a40b100321240b20000b10f08110911103580a40d01010003c1d03800c400000d01d5035203545180303084031680300d0413101507880441d00d275000c0700d030502561006e01400d50310200c2030b003001000f081d5640941d000d0000c46200701016024900c609500400080034000c108044c40742c030504160010364020700505126a003858031162040c502402040d040342d04610703a100c100d2480d400300301c008050405680820200c204100c00c140c291040464000c1c140403d10000d0f09000b51401c280c0300c42c3c8050b40d640000742008020080150410160748203500d840d42d40c0e0031344c1d600600c1d0890401c000160f07412100d618 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 945168884 1250 945167634 945167647
    0xf0501031e05040501050712020c06010e090307060c0207050f06070503030103111804030e100c111201020c03030f09070e041203020706061d070f020109050a082104030e040b010813120e0402 83
    0x20150451805041f844d01c4034101051202e0f40396040e03200750305248aaa03880480104112040070f80900d60040301ca406413810f0076071070781c0d5040907505c88842000c0140c0c48820305103e285889070100340314000c1150300510b440015070701d89450b408144809400713618690207140050321a910303420044c5480c0c104514407450b05142c06401090100d0400d401003124602c2004128050540f440c902d45e0014240d074007620300c0c1c504100341140030b020240305a5400f8045040d400310100f000c0c0d40109440300b0140e020707181c0101c400d0325040b1035070b10501e000e152007014400800c5d11040500c0f080300300d40c900135a540d01a4202a4043c0c00f00d5032005e80b4000c00085d49941c2034140301e50b900d02524065803240e1440103120400c07405c0c0c0d40b860001074069000780101c000000e0f00c1d030000b45442100414103540c0540c681442c51362031070003168250080b818180c5024100c0c030f050300c200c805c0c4c0b400c02d0901403000d0030031070340c80c0f00240c00d2000000d0100840c50488000c4038002d11800361490b200800c150340d01c0c0c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 945170134 1250 945168884 945168893
    0xa05070c0b0d05220609030e060a020f0c09190b010201110a0f0e0613050103052d07030e210a030b04110408010609060518280e0d08010f0501031e0504 66
    0x2c1c0201c5454190902d44004100c902c42d8400d00f24840c0c00070314008501140c0640c540000030b1458540440a22060003010280b545400000c1e14407442c240d00940f503055041031016003000d500c01080b610852000b010081d56030203010380088418074481000170707030403a0100140e0040c00603980c0d400e030150001c208481c4550b80441106642c038059900c1c6510030765a0014030a9900030031000e0045140d40180a018075403196101923030020001841d40714050290590560401010f01c0c44c00400d07019000b0040c80c01e4150107010320f000c21840081c4100d0710358001802c801620045c85591211001900b1403403248a900300e1420507100a0003080703001c0d01d40982c0c0042768814030a10301254204500040d020080e44129001c40740054050308521200020341d1144180c01000c413210110070122410300040c01d4030100d881044000000240c2c1c4228600c001e00d0004090300500030041030200500020380350100c2d0004444083c01d020425a086014030800c2400c0481c3c0d40200d41c0c9030000308170600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 945171384 1250 945170134 945170137
    0x20d12022b0e0a0608150a0b07030305071107032111060903040807080c0603130c080111030709090b03070b0d0f1506080606040b03040b06130c0201050708010602150c0a05070c0b 78
    0x901c0c0944a8503200c45038030090107060041441400c002c01e88540015403440d010800304d500d152001845000840c0d241c5400d03005540080c44298002036507a8104614030790400b0040d00307001e54501c000c2251070315581d50040d4120701080646000d0340e190f981c4010f018081d034104400055504140c03007643c5000d1400c00c0da0f0303800510030300b0028814490b0014281d04049010084035202624051941d565a050040c0c590f820f4441214885540c9100140140f0288581c00b000400240c80ca076403410800001042c41c9550703007041000f10b14241400b0269a0006044811140f041d0038030b903210000c2040483c0242030750030300324014074140b410b21750141440c014944c040d00c20a4070303251a55243c2c0320502405014034040c40f02130200820200707000c05c0c2000440f0b58860401404c02e41920f0440c620101138644c038006000150391220240709039a0707080700403180902114802803244103110b40c10102c14802c003500e0740080400000c0c01c01c1405104504079084039410012a48040ba034820301100b06 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 945172634 1250 945171384 945171463
    0x50f071e1211100e0c0a06030506042307030f02091c0c08071a0f131d0a05070c06020c0705060c100506041a130902040f27020d1202 58
    0x101c4100701c0741c11081a014018070701d40740000000424240141080c2c0320020180c03078401c110301d84940c4521840035900c0e0071a1b0b80142c500ca94010445003812403e02050740c1c4220301c540c0700003c1000700310380d517a8000720030141d00111929010554500300240000248143c04000f03410800380700c58a0000c60031801101c000303500c200c440c02620ba03a5003500c20b40f2034003d4096104202c0324103141c5840c042c8100c1c00b88c4500d8880f07040480c070f0891040200b0722009440d501060340d800c03050800c443c242c1c40950081da03109420950500a07460042001041e1040041c80108195804500075040820812040000d0880a026690740c1d03003001004a540304020042103036090b05040009445041c00e01a4143d21102e1416954980c1c00003002c0010b60080b03401210051640c8918335009640c0741d02401c000f00003203d05c00078181c58080030395544844100408420016a20700d10401a15013407411440c061b0040381401e6a54000f007422400c4c000d0611400c1c0d401415034007204104840305150425 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 945173884 1250 945172634 945172643
    0x5041106030a0e0c1e12030c0607110c0102010c0801091107120804140d080601120b03070f1a0403020a0e0c0409090615061b08030a1104120b100b030601050f071e 71
    0x240381d54002e04103c944030800b90758044a000840761008141040100940d46c241202c058070b00300021a62014070303201003200d5100c0041d080c4803040c00c10080c18400c00110800c01e200a01010400c104080e2111206208800e00d80c1c0e034804e0400303640350400056614440c3c2c000d20700d1658007520b003002000094280e4050341d80c030410041e6490740e00c030009a40e000362481c5e0b461f4601d182e540c0c40010340d00700c0121081c4540d4503844820600040d0380c28018000a011501740d0181075508001500e0144c0f40004441c0b0f22104e002c05c0144096910141c50340c0444a286c0c06822542c0d40320424080540102d1f444071544e2402c1c45020740400c0702e15000b4a8094030160340b04007100c1e80d40c01d405c0b00c0705505400390780c4ca0603088c00e00d5107003c50100401140e12403a8910041036031110044d140d0f2169000b540034064490090701c103401000004640b090b0042400e209400e4810305200e03100d0080c0c0310203800c103418002d0026132024850b0400050310b2106410405403c4003603504140701589030a000e03011113 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 945175134 1250 945173884 945173893
    0x307020304050402030f0f0129030415090b19020405090a0911030a060506030c15031303021c050301031a04080d050a0605150d061e0303140c010203280c1205041106030a0e 75
    0x110100e0049c80762111229050000203540d6011b10414803076072000e80309030b601365032402000308406881c2c0500040c0600c200c00214107440c00d41302c40300c01c1d00d0841e4220300103503004110800059861059031504041705010004d400805403130985a0400709088080d00350041c03801c00020b21500d6070109218480542c140d421100300101040354240e000080c4403100c03801030004c00d5444803c50305a0440e240300b03004550710055841045201450f1548614001482c008018001c2146c0c00c098500c03c1c5026401080d581d0400b42c1d2560403500aa144048030140e0720300020f0190003030364201c9801050054094820214000700d01080c0741d014910b210181c0b0305000e030010b80140c0d8542070604019486188458550840c0d801710b03500c034900030040d40e0703004c2c0a00c480c402c1001c00f80300440c09929902c0342d0121111004c1e1030a007104041c981d0700c0e80e005240c07030795030400e6681108510b4030310070b141d400c0000d240d074451030611000313140c0000154101c480881005640c25041d40700d100301002c4001181e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 945176384 1250 945175134 945175139
    0xb0105180909241e010e07050c0f030c0321010e0103020607031809060302100207051507022407020a080d05031603020d1a1e060702010e1c050c13050403080c0307020304050402030f0f01 81
    0x14051301001e10803c546205400b00007400704d40b064015211070316074a021798814400020050389540c002c070400d0b02c9a5000050540c04006109410003e81304002c44400415894125500c561200500c0040c1c02250009488002c0502c42d48440494034103280c54140c0b4252141f00b00301c001d0140f8001240100aaa5200311105000040007011114004d00320a00000341d0340b201c00b000d8104c650308980190358444444802d03084d68102c0449001c1d00c4c800340d5261a540c0c0104070620b03550ba40185c01a4005c041400c0000358008103c2ea0301140e410b541c50940314800804030000d01c1003910700b040040c074004202c0d5404c41d50070340c4103c195a08842c209010040c0300054128424802e4040d54807400801000c40154000c0003d1000300c0700042584000d440c12100b10042034525101c1200ea0303410000030030b041c41c0f4007004105100d00030940d00b0402d0307241c03070782e4003910b288000b80183d460f001000c8005400d507407080048601500c4050415500ea06104807001d0b090716085c1c503107014860346200003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 945177634 1250 945176384 945176431
    0x2090117090a150209031b010e040f02031b071a100e04050d02070504110d0b0117150306070806090402010e03211c02070804030615120302100b010518090924 69
    0x5d5464000300100a4007000a10050704500301003440b81c03990600000310702580c2c0d640c0e91445801140c0140d42d102686d00d00d0044040903a0050b540d090343c15004040c0461800300720402107070240d08180302403030340481d10b0341040c040203030301c4070340c80303010025004000c0004004022410300d040d54a03c0d02140c0c07200c0c0d00e41c030400003941d504042d002004070b0180568684000b65070082c180842041c1010101125040d030b50400081b402ca8030b000d00d00b0341c0614a040181401c01010703034000704610705021141840400104400c80182010341040420044004690b40912500140c5054000764950708007204441c0704194110030704161500c4050790b9580300110395030003110241c0d079100315801d14107070171a0b984000138400d1008050a5028100c00410200441807003804014001d40040400041401c40c0c201a2f64402400b42e040000a00410180350b551032200d840d1800100d8030400700381c0e20070013014070b81400071350b2501540225045003600d01480700f50480c0035040182c0e070002c030303011004070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 945178884 1250 945177634 945177637
    0x308222d08030a03090611070c0806010603050708060904022110050609040b041203020712030e0c01030b0307210515010e07090b0d09030e0a0b1308010e0c0402090117090a1502 77
    0x760641c1034004001c6150b20a10a900c488091449420001490072250720380b12a80e4100d1102101c5c0100340340350038800040304010f80707401850b0b103190038443c614100c04002c04904014004e64015014480072074119a40c1c5003c01101e00b1603030000b05480510a04101d94485400c0107000d81d142ca444049206070030110740a9104a0b000995094103842c2e0b69900789001c46601c101c002050b43c207210070400560302044404c504142c0e50780224255030318004803400c110780c0902c4141818a03111030110641c330040307000c1003152803030703000c40d00d0b5485210356110004540341c030020547e0003041c80903650150075410030f5050f54180c03000380b109941c510805640442543c003504240b010184030503061100160131100c07136140f09240c0302c010100580046014020950010354080f440070a0f1884161a209500e000070202d450090104040400f070301604e459054081c58000c0d600020441066405000280c0102e0750071004e64616141c4131100c1d03510790703922000c1103515006000040004050500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 945180134 1250 945178884 945178889
    0x90d031e0903110904030c0c0605030a2f031003020d0f05010c020d0203030126100b04050603120403110d150b090601030b01020d0e010908120301030c1703040308222d 73
    0x3e000028081c18041000400480100200c040110b15282040042c003281c003584010f29054803440c0d200c0c140018400f041e100103504848100004102a0044494405aa20141c01462411648c90301c950300b1901c00551180c00181d00301c2c0c81e0340007500420000c200400d113907038000c1e0003c01c0511540c0104984a00c8940c98803801a40140014020200300d1460915903009402d46214036051111500c4d0403c9081401070250b180e490401e110310317040c00d008145d40940114040c00982c4003d001c5002c4500880c01b0191058031100300201503501d600d100c2e1158203800240ea030140e85a2903460350058019007034140c0c021003504006c1140ba5000b03004621703080c20141c0140894048100702164000b43e41045181004040f00001450003000c3c04600d42442c2c0488103140d5a604508109001c00e03445d82c0002084050100300340660380c00842a60141c0e6402490321795141e800040c100f440300078442d1a1118500800f400041c80d0a84041c14551902110740d1203062110302012000d11101d40c3c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 945181384 1250 945180134 945180143
    0x70c0312231f03060c020a021201021b0304050612150d080a090b04030803040f17041502071a030726070906080f090304060f031b0906090803030c0a050a0203090d031e0903 75
    0x10b01880040c440da0456102c0705e80354030498148500356000100d00c0c241005401d006039600084181441051203605224803800310b000310314103450000440c400d480340c61604403980b292540410100003c2110406e0408402013206410781030300e04200000d0352242154001080c0c0b60a00000c10860410582e4120784d0032845050560781c0c0d40c0c0b00e850340070b1034005040b601c100700f030b9605103405c0c00c0d90740141002e40b054459010b00d016181d100a40782250a4005007241045103071a034032803a01d080304481c0e11035540c4c54480c1a1208070401c02501c0213080505440410481c8204120540d005031920b048460320303904e0980d2070311365641c15010b0304001c0e220940650810032003403180038020103038811191000c0c45e00180c08401114480c00100c6c0e070058480004612581c01c10262740d2107003d06020341304c80030240d840c60510341c007841900d21132b00514905204001c9680e840050003802951400400a4429208440300c4d186c02440300e089454120140f600d00387d00190524402e40310340c0f080c0d9900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 945182634 1250 945181384 945181441
    0x60f04020f0f01021e0c0a0608060603010915030c08060613020a08160c15050402120f070e0c0f0a0f110d0e040f23151503070c031223 59
    0xc0800b07000c429440320101d20f05500ca0303000c021011510061a01d5001208800600f42182c0800204081143c3c140d010344104070044051281b650356000c100d9045460030400041d12518981c0d180184483c50707400544010140723000007602c0c00d4003007180c1d44150412030320848501c1360851200f04900901201c04000b5a91303200041480000040011022419080c0001c0490300d503545e0100401480c0d003801485a128ac090000710306103559400c00c04000c040141c00304c802d000050070b0f0713604001c0c03291072145107001c2e0200341e03030024a03000c4800301031600558560301e003070740100907040807038840130007000446610310701c0c1035400046251a02c00300c2d1380c0d6a84002d4151001000050113103480c0d518402561014484110041d0b030280c403400b07040c0e22005044c3d41c84c05001115025010740d100a020350003511016030010115401c4a40c0000182801110703807100d42402c07150700311200e1402c905103103081c001e40c00c0c401d1300c40640071401c40140c400600680e42c1c8d04034002080e01e228038600c201040d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 945183884 1250 945182634 945182659
    0x30060603021c030233090c10030e070e1b031b032706070e0103050907090c0801030b0603030a0e010c1506082b0504030f05010b0402031503010c1e1209080d0509060f0402 74
    0xe84500d9a030f04040b0000859440500c041f00244040e40342401b0b080c0803c7d40c4071240d0840d14010b01c10580142182984a10a4900360140c030a00880c6264440a081c000000068805003e50007030303038049100841c0203407030746410030407020200c455100d584803515003600c1800c0c680034001426031017442103598122581c019000154080e0001504030b081d28010010b0203d082002e92050228030351041d03640c48040e514500f0680b010749006059180a90010025505d09580203a0600c524440c28030b489101c100c580c0c144000c0301d540403000502da44e4248a800500740750f00041c0165941041c0d003d0010a50f0309031301030302e120030a104000c408a0810f00080021030070f0300840f480001c1c0a0800844c00b03c0c10000010308076801140c1d24401d420880d540030142c0e0401340300d920002e03031990400d43da2018510240c100c11240b80101001080400c0c9040e11510459810037118180d10001487e00c80b00d990210344c01402040b907045c8285d205006c00a092031218440b00b50003140c000d402403607a1030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 945185134 1250 945183884 945183973
    0x2300901110d090c17010b19050f010e130f0614061911031c09110f1e03010902130902010807170406050a060503060405100630060603021c0302 63
    0x1d800c0201341c4840c1154000080c40b8200251502c00c0d020b00080000b0394503a900080040d8030b2001c2d101141d08804940c02030215848895101341c41034424280040a00340410010341820b100912694989003098036201c908045500100140c070752055030b000c0d88920740d03414442a80030704d0702c4600440304401455800c04e40200e01c40c0c0041c4400f0000d5030310b014078901c10891400220103410180565035203d2000740120103640b008201801c03111600c00d181107500103120041c030720f02c0b004402d240880c842e5109980c25030283c010141c4c00f03041e400c3c11109130070529008000d41d0360141c0c00300c2c5c1c10030000f8804910466804c0c0304501603855441c0551282c7e19008004d0000071300103965150703651000f05150742c04109680c4568840c1c0d005026495803581140252405070b80041580c078100d071001c80040c01d070100c2c4210710350b0302003401c8008110503042283c0a052150b20207500443c0100e02419510400401d00284a001c0d4088074210f03e4100104c00e5110b0740c0d0050305003a800030400442000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 945186384 1250 945185134 945185141
    0xa05010c021e120d0806011e02100510091107060605060412202101060b0901020c0f13061205060c09091f03020613031e02030316050102300901110d 65
    0xc101600791102c07403540e48030813442d2000a02039180481c0d030810410130740c0d691110104110009010482c104c41402c001c000e903440c0119804404110388500000340000c3c54640d841c4001c1c02508000d1211006500f000c1555603c15581581c82908140000c100303030814008a4088030348030140c1c180a0449510b0ba405901e9440a225800510142158400755114500c54045181040c05109084442140c1c242100d13030903440841c00300d03400d112040300f503a003304203412001c0c0150761600d507100c04000000c291900030304094134218507010020410318140c0c2d200070702c4c07588034200301e641070b8030ba84580519074041c0c04c41e070b6640400440c1c001100d0f03014004c04018035044640c4a08e0034283c503a030020728650058081c5c486440850b000420900c07c20288410500c1589240c040c5401e0007034020a03140d208180200b0000b54880c040e080800500f54101c82a114413080c07802d0444515a0709082c000c0c0440d05980c040040b28400306003070000600c956900b0710001c540d2a4602801c090038403018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 945187634 1250 945186384 945186439
    0x2b021e15191214071214010f1e0816051005040e15040914060702012901050f0c011a040e060709030b13020405040809030d17070813060216020a05010c02 67
    0x5071500c3d40d002d50f2100c075010400074010031030307500c0703c1003079941c45207000c0121009040d08100e0400c0c0c040c0104410001c840d0441c0c180e03903041c00a000800240420545140300e9544801c0c20b510031180510781450000480500b0784d202103d00c4080785c01c0003001201c890155004030741c1564040c1c2d0201e1003c003030b07244000d00481809000824010300c00c0e110f041038608421a0b0300c0c40ca800c80010070000710713420712074448100111b6038501e061100c0782d100d58441c1900750342d115040c0000007500104412403042a02e004210060007031250440003c00100c44482c040a014083c504000d1905902003010912610409859803620320852840d260703c90302e407602400100705454080e4024000d0380719030040c20b1242e40519941030755030600d207007810b2400d0300040080d4100003408081800d20000d404100f0740048003482c007201a511190042104403200d00c42c004c01c00c80c40041c080380c51034038880d940c9030030600860310041c04568132401074404910903500203500000b0000741c01203c00e0310700410031320f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 945188884 1250 945187634 945187667
    0x103080901200f06250c0b040606080f03120f070203370c0b090d050a180b030f15030105221106031807090b2b021e1519 53
    0x42e0010020a09810b19501d000c2c48022600070104100700300304003490341caa450850030021504000740790f0004054a10f1a40000c000c0e18144d0b02240c14046585c0020340501504815118610f02caa8881540c0740c0c03160071003090290a40000584141c861003d103441200960091132401d00b4002040050340403d079025040c4480c0103207000300b0200340203424002038101d80c40b80b907004005801c3c2040b003403000074440e110642c00454052105544013003036507040c00305810004d41645441240d2100104a60400c07402c604000c03003044110003100c40d541b4040e8444180d00003a8030306100a02d820784104454103403454051f8082981200402c1458108290240381c84420342d00c580400224154410768005512080c00c807054281c900303090102c18020281c01a00700f100d02ca0040100b00300360340031200a90a8944d1074503650482450300080301d151503000f880d1a000014085c1070b60210015429124041c8103124041d11802e0800c200f1911035403140402c45d90f11001d415021504074114060241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945190134 1250 945188884 945188927
    0x20f041410090b030307050a0318080d1d0901030b1902120106030e100506011205072016210803060a0305010e03071e0b0604020f1204060c11060103080901 68
    0x30440c5500d0029074001e044030080c10800d0351811888800391031180350000c2c401d400c20011800003e0f40055007001c020f50508011540f4504401220a843c00984c00900940200101000c00580c00407607440c0b01151b200c40e212141502c0000d10002d0740302400020b0541607808045054124540b28500940c2c0305031101502e801d5403000c0507090200d083e405000030a485502210801d0400d016418a00c501054100010718003200002e2491004044864403d9511710110365403611944004100c140c0700d02043c7c54000c5081c01c0b19070381341c0354028594500c5059800224410500c400c0380072080e074441c07105e20507080843d126029280d001500031640180b1010001000607020300071088520318640203143c4400791810000001e900d0f01c14500d68201420280d980000c641e240850b030002800c1d01c00680300d9400300040501803044400d01500007000c1d9041104000103030700903414018155032403900c2c2c1485500e056030350790401e00009012001c1032002007015449403040c14076200e00c440d40013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 945191384 1250 945190134 945190151
    0x1303150219050c0304031a1e070e101103070b0a0b01020d02032a0a06020c1b01170a0b2110090206030103320d09060203180402031807061d010306030c03020f04 70
    0x506501031f11500c08005000020412025000c0d19800064104032030028002d18600100c006200c150b080c850244201019003030700762024801e00519903042ca00108032607440d00c0303d040900100344200d64500106040040d5200300d940b02003681d074012540c0d0b400450034401040c0d051095010143c007441244485079220b0180c2e00020000e140710a0f000d40c40059860200c0c01d13034541080c8055240700d02c010403510790ba0569991103c240303501201e10390b030300c4290754480c5400e07031024004000c0c0680d408009038042c0c0324001007900c3c98074441c590a00842d1000c010013403104c015624800c5000e0340c070070303c1400104081047c40070181003950761071066246408034420303c410f415200d509079281552060213200a2240c10000c0480940f140c0d0008600b0901c101440780c0d4000d000c209024000c50300440410481d5050f8044d418130407014200f60341d985915188010400b94240e6560401ca00140381201d44a5000e4407920f0b068a4106c14465000750840d000d000c2030081200c0d4983c0c000780d41d904039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 945192634 1250 945191384 945191393
    0x7080304030f020f0a02011704031101020c1b150f03090114130605151e0a0f0e070807030e0c0405061c110f09090607081b1303150219050c030403 64
    0x4500c994403940302c0c0d14030465107240c0245882e85401c151001c9901424190015030b82003a810181c2500c81c443c8460f00c0e50300d6190031a40a54264040c2280d0360000c620788a04110100d00c82e4010025070440c20360f6480680200598680466180c2c80b0030b51040100c0716000c00c0d810300640e03110061130004074803180c2c060301d5000080421a01c01101d1854200907a040003170314018030b904040010600b20b0000c51540c00a0300d4280b01d410744000703029107a1044401038039440341c40c000411003040e04501440e80c413420420316850448541c00000c4582c0000b1714558042e100e4101841c0e4128000c101030400d08060000424010305a0f03a4010901e1807020941032120211020451180c440700d80c444952006018a0030810840c441c4550030480c02c011001400180060303110406107060045a102e0123000100811021014158540f00040c0c0a00340070820072000120380c400c150881c60380d0100111601240600d01110b02c101d198500f11600c0c852180c0c0c00b03410202440800c0d280b400c0d9503948c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 945193884 1250 945192634 945192637
    0x1116020d0f06051e0f071d12070303020f0a0807120507081809070e06070f08070f05071802040308030604050402010306080d030f0f140712060905090f0d110c13020708 73
    0x1d046428980341e008110908261039504c60440b88101940542801c044c01d1599558900405035020444c14400d041190f10420603c116095406001500d508401c0745c085510b4032a20300083d0050310483c066124510744c0080c01181c4140c00840c1e15043c0f4805035542e01c40c4800032134041c1d04204041c000e000c08581688010000038552107801188030108006120034220020409410300001008103101c0d5182d80c0219080b081d844500c01009210f540740406560048140280461100e0905c42e0200100020728001340c40740c51340309501001000072100142d104078040106000350030f00c003062031070030541c2102d50001d10505001c281e42e5154801a85808120240d071070010b5210814100050014440c1024000220401740090f00c110303001440c0e03170f20004d4003160420204d1100c01807019407a61004c005022529001c3c013242c1050340c030032980ca40c0000c800541601a08a0340c401c44d60150b0342c00c86110300840040c2101400703603c1000180c90815100942d00c43d020413858001032114070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 945195134 1250 945193884 945193913
    0x4080f04090612050105070f09120507031b03061b0f081302040c0c200a060521040b04120807020705040e011b2114010909060e0d0509131116020d 64
    0x541c40d8020520130305140742583c2c400b0300380c1410300c00340c2540a10322940c0038103640c050302c4526818000c18000c078984203240036035990010b0104802280011200254054442d044a0260009001d005c0c480250b012455101a481c50040b40c02410342d500f01501803400f00c0d0788142014140b00c6078800c2900072805030745418816030000740c50650644100404442071051130030000c04000c00e08090034000c90b0003000c0b00e0041d5400d100c000700e44070f502080c18070741c5e2894468140e81a0441ca040618110f082050b041d1030440e0235069035125601c0c05440f60054503c0354295a005280c0782e441e080500009064903400040c141d5203c01e009184902d8649480a10381d00700d6039003486500c2c622040d62400000366803600c180d030303090964123469104683c0946065686104000502665034501400103080e104025401c42c0591204082c400d50004064842a4000d070384040803034038104802d03000c40d8a04030030084010780902c03031101320001c0281e48818052000d45180045103c60312040040c18551 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 945196384 1250 945195134 945195149
    0xf08062e08160605030910020304081303050d03060504050603060703051003080c030a0906020703030c0803060a0e0411040510030c12080f04080307150606120b031e100c021504080f040906 82
    0x8140c8118511200514034003c0505207010307400c608103501030030780315034481442d044c0264006c8042414408038104a0700950886164207d440b5564681035440f081b191007001c01080c81c058000406060500981e8400d1000030064600b954641000713500804000e8480bc1c0d05000018021001500a0004044c900c01c2c003801541c6038502d060008200d490190400743c21034100c030f0401c00c0020780003140d540704940e01c81c1016442c0c0c0d40304000324500e01188d41c85800041c0f200f01c180018840c103001c03a07500c5181c0c20f440600041d07131000d015072801e030214030000b0412462103008000c40b1a600008840c054404c0108a143c40410070300e41010381c009401c40c104036000010058100240002000391080b128101070100500d0400c0160070000d5110300040c9090b152507125003981c1d03052026000010021840401a06120414a6983e0b03a203e0500e88402d2501d0340d9045050300024009294444001080e4070640e182d65480c202c81e04111198481007805000c00b00d200110ba014000262015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 945197634 1250 945196384 945196393
    0x3010522260d1a030f03040308030606071a04020310051003020d02191d010503160b09030a0c06050a0908060c03130f0b01030f0b0a0b03060c0702030c03060703020408070f08062e08 79
    0x3c18106080e50b039800c2a2190344072245070312500802101707940842c0c0e002800e0070f1700c0399507401c0414458032130064024040b414402c401154a050168410b0007131340241e040b18881c0b05800411000c0341c000742d0303202c640013003072810030401403500c0160001c1042c400340003032881b1509150a1149920785402402854200d005c2e2424443d5200c0b115600400007200182240c00c2d64880a4400c1c00c0503000e9002220400100c1070200d0b1003c0001c4008150b01c000f030007840650366503004205800030b1100d0800034075013000005000100081480c01003910101c601d28686540c140501c0010491008444141205020070085007000d0301306030003980100002d228521a40c50140c5042000403c801c46007480c040307804c8690303180080d80e1540400d004001d11341d034050500000b490a5034103141254988a064200030503a503040d000f80c01260300324030441d2120384d26600721071840103081c040c2d0016039100030001502d034515104c031140545010500404050704042c840001d81101e80c1024019620 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 945198884 1250 945197634 945197651
    0x102030702100213062a08040501090b040b0f131203020a0209180a1211030d0b031903230d0911090907060210020a1b06060503010522260d 61
    0x1014420410b0340d110740441145428030388000f4640850850080e00200810480c0514030f1074545a080c152071880181000710040352031038804040d90140c021140012010500011100801d4068405865515101c0c50500c209006c0008080c0c00ca00344010b0000e1500740001410b44004107815000ca0181d030240140c0c90340b600610a10505c0500003601c0264032110700640303074401050440456900039140026070340b40301c804803070741d4002086011a038080004c507100030442c0b40c1d2100702c0d030450035020740e48900a102d0000030001d080c56006400f00f690036044a02c0c0684680400e065040d064038100c1c1441c504000b1001101d048050446200b04205a00805803801c0c030200b03940140034400402d880303814031030002c3d25100e03a05505a400b0740c011400495013030040980081030410303044a60340d20025403c16134003525440c81400c0c0a946424041100b000e5903440c40d40c04400b0849035000c420202e0b030358040c1c00c0120003044007502e0400745030340b055136065a4010200803a031883c0c0440c203d035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 945200134 1250 945198884 945198887
    0x1110406022802100e01110106060c14010c02031c060f06050304020f090106020d111009050312070518010e0f041517060601020a1401060807090507080907081f0f090501020307 77
    0x601c07205440c0d01000316480006135251400400c1c11811361030011500e849104c010303104190501811100c40d403c056020659a60040705c3c603500c24001d00c0b4460490200a42c0d150803107044440c4100144c03c00c2155420b9103c0703c9001940646010300006025951060301030418031454000200041000040c08158500300321000d0541d0b1007141c0400e0305500d040400b0356142580c2039400b050010801e9003031504403007404241103503c0c0810040c01a6100d41c81e1050300c0f50712144000c440c0540040104555510a8003039400c6541c6030560741c0c070216908001510301c1e00352003282580c040d0f1f4115140c50359440d40d0052204042ea10002e044205040002d0f221100000085400700c0783c1c00102000116a800941d81645d1b540081c2c2c01021030f00007460040c058071036138200701424410f002d400038040c80207520191048c0179079070b224001e82c0c507200c5c1c1054646d0a14450090a0f50014080140403240030480e0265120004400034035000c1c81c80082c030503580c0d01c0780d0070b8500e65400300400c41003e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 945201384 1250 945200134 945200173
    0x51504050912091e130204050102120a08070e1306090b1503040b01030609020307150503150f010c1403040e1312090e0a202805070507170111040602 65
    0x740c03401c05000c810a400007014098042c07000d001e841a00e80301110309059002d600e03074000d140c1001d840000d0000683d00414060341c014031641d801845074420040c506001c00c800e841001c000e9550303620460702e6820b4220313003450389101419800140144a004070349803d00c140c4008101c0144081200b50401c41000178015241c280490000c00400401001507000c40f03211381980d41c8000006405c0880740042858112250400e512550011200c0400550410b01031441079000d00300245186100c801840030401c0003010039070104001401c0d020000d07030700903140070f400600303441224101035445003c40321803001540c2021184030905c804005104c071142590cc8601020708020030064905141c5030000300b00144402080d50f03031414030200020591001c06a44500d186007503444005030b0717078010030546d29106255002c008401000803140e0048042e5204160030401a10b11185011002e0340d070704444e0b50b00b480c015560360421003901e6242001801c050140e40e401850b9540d000f900c0540003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 945202634 1250 945201384 945201391
    0x90507060306081e07080f100506060403260c2b05090a060509010507080301140901050324041a01060903030e030a0f0f05070e2d0708220605150405 65
    0x401d030512100b40083c620000f07203481041c05807040c0303081300800020042e0401c0f1054101c3d150300d000300d10010843d0b040018060088180d100e00400071515241c00f000361621603803000400a00801001c0e00c81c940412081066000d01d8000c102c1c64246440074041c20482c0d07507591020420501c1c4c881c0010b40300c14401c1d00c074141707005003461880c0be1001000100804000d200d140d0401000261081250348660151400f550340b054506841e07585400c0c3e140390024000700b40c2801038400000000b010300c0c0c00504403800c2c6088058002c2006400403250107042402001640e54031490181c40c003610b07003203501c854024a81659010b802904615000340704140008125200e50700c4030138202d010407014083c48020725489000d030201c00300d0510307085081c46040c0c2d0004c041d10704400208400c0c005a000d08200301400c01e0031404001080010020080800340c505c2800215000c00180039488192246481c3c0c1188000700c160303030100c69954005891040360004200e110503404180c40b4202409890341 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 945203884 1250 945202634 945202637
    0x9160c05061003051501080a02100207091103060316060e2404032102010b0a0e070e0919291c0f0804210201020d08130f05030304020f09090a060903030b09090109050706 74
    0x2d45d9490180320030350b1030502c0000031b407161a41d240106140f0b8000c100c440002e001c00c201c00d101580712203619224940040358440d009004a0b4010480c0000811000c1c05030380d1640c80d40d0030780003086001c1c00904005803180398441c1460100102e509568070011b00029480341c0501400c480d0600100e03158245e607466800296030500c10220000e640b00f80c1c0b210141e40f901031100d0061390392500111580c0e0004495207403c1074101040c484134100290200810355800310080c884c08000d0720540c505c40c00240074004a02440040b40c0080e8030300341c0701c44104254162144816000e154031800c403114800042114894800242004086c0c594084280c020000f001011082f008903000070b520364070084400030410260070006064030000203400480550060311002d001d082c5840c00039078a40c0143d6050b840b88000011600d22440d043c504144035002d2000035126250050740c8240c003500500102b10103064603144804404d03280c4ca2102032203840c0b040004640038180741005410122960400da0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 945205134 1250 945203884 945203923
    0x10905060705060a06080f15060103090f0506040b1b0d1802030d03090c060f050901030506122e0905030d0b0d0b19060504020a23040305070e01080f0c09160c0506100305 74
    0x1011f0303140800c440c245a140e07104003000e9565054012001003603e604018000280212031100380305001031407510442c414a01c10303141d600c56041108200ea40224444803080c1c2c1007016029031301c015004908144200307505180410510341c00282045490412800081d580c2c0032080f00340040c418080c03000301301c6400c00c0c9a458441040c000d003940700300c248082c18152140042041e03601d0b58030148a400d0101c00a507400c2c42c50002640c000c0d51003108800b00c1815403c0302d103202c000c0580c441c4034017490740107008614080e80d401c481e102511031800f0041d4032242c1c01305040c0c049070754500c645101f145991501c0c1c6e08074221190b0740e003c8031400e4002c103000701e03c1030040c000b6030754100040142255107651038508184d8810140346044c0724a410091060286a90000e600581c915006050b2121541035034512000c0b10740740f81d41e07492440940c990195000e000306050300744402c1100c3c0302000b0b920385002e240c40952210b0b80b6004003500c8410303180341c422504105008042c80800034151300043c1c4071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 945206384 1250 945205134 945205153
    0x309090c25060e0106241425080a030e0106050f180a1b110d020c0901230312070b16022a1009050321040302061c09030f110105040c14010905060705060a0608 69
    0xf00c003a4040c1d05000c0300305007004180c914130100f03102c01e05000d5550000c1034032b95581c00060010007408166016100da91b081110106403441d01c42910703a0044406040751000e8008441803444029018104c0c0501c40d0340c0700022295446039417070f0511100419100d001c16600d6007603c062800300c2d07006410341190441c0f24016503c0e130701c0b8190383c0c0c11907440e01c1d80d0785c8000005c0c00d034004008034032a40031a0701d0300c075003034102d8003e6107080040d200b580c0c0551115406551003a1940400e142030003000e4005802005407401c03200d61155600e4400c2515050550910343c00341e02140600d400c803124100403604c1103030100241d00e4104200c50180003075800e140714561313481040d0901800380e0b000080c42400081403c3c498048101006c805011905800384007036803040c100035017690301000e1014006840807201007100b50050290900550f80a0361000340366103040107078080c0340400200b040c10840d02e00b03000034040e03485102a21015010310081d000c5810403003c1c2c48100c80781540118041e070484e0030321 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 945207634 1250 945206384 945206417
    0xf0209011d01180b04021819080309011d091008010e0c2101110409020c0706080c0d0b120708010f0b01090503120711040e0309090c25060e010624 64
    0x50b0454092046002030f402c403c0005001412440f00e506030024404915244a0404e54952520713400040e0ba0898140740184c075403445580d80c40c00380b482e06500800030003160354070480e21201d01e021215204401c101032030380020f06104013681c0902c011640100d042c42004070038400c9048844041008106a42c65140807030b04800302d650032058000c5c0c400d5542610700358290084014884608078413a44c60b901c69080381c00a400240428400e4401c2c128042049806203c0c0c2e00d01545104216600f8024100c80036800ba1012600c034541002c10420200c000c40010000800588601000030074001420f4107500d04441782204560704000c003003001000240c0340441d00086200c040d2405030346c2d400c024100704020416000d00c0715007081c9803402da142e00240100280c4401d1204498102d0151a0000c85440034041c04055220300b11020100e10900800c005201c03241c02e22079000843d5010800b80c000d421600140c1c4101403100c1049803000030320300201070701c55280701c0e1030404440012003040c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 945208884 1250 945207634 945207689
    0x3150602010b010c202106010f050a05040209031c0203040305011a01170c07080703091d04082a0f010507080705040b0a05030402130501060216120503070204270f020901 74
    0x3c0900440c00212171403d8181003002d4a030b0b40e448000e088012082d02c0000c0c02c1c40c1e159000d00419a8a01441e40041402041030300c14604441000b00804202c0c2d080c01c04210095020094040c0c0c10310551540039040489407401c9200803141c0c1d005036881d1403444c103005007500c00201e91000302181401e50300c041c680c0c2100502030b03d84160020f007041e640d90000980d03003520990f00301070184900402d400d003c26034841c51180644241620f0001180300d200781c01c8511220507500180455800e000c00c41000c402d5800422151001094900e103172a00611480d08240080e00509661b94488042008850b002030005800c0b803010f03e0800d10b068038124815919020307140c42001080f4001000c90155a503140040500401618082101d96550740c400b070340e03e01d0440080c00c050000c40358001507149040c54150009500700d00036501d00041a0b00704801000407420b000c2c83c0e4090400c0b5900003481186041c10300921642c0f29548114503401045450360050340961351100c111110310303540391880352 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 945210134 1250 945208884 945208907
    0x10b0306040807031704060c0f0534172110091e02190e030c030709111c0c03050c0a0c23150a0e120f03090a060c03150602010b01 57
    0x881d03503841d48980d01e011a1030385d50101690107100e032003c080c0400e2083d0f0354800b8000d043c06468401003013540b800183d07070714024015100c001154000e18002140b00b202e40a003000c80100d20543c1c1403955a40c0c80000d01d81100ca180c840070200816404100b00800001101d2000361440720b450611b00290391101181450007886002134540100d161040314002ca500b50340b200c0301c07500355245c2400c0e00344540395800400a040c00510b0a4100600a04002c1090a070042002d405880c1c0309041c070350b24a021f00074984c95080400000c019403400504150000e06181c2007070503010070340911201004040c3c0320094100780303080c9002c00c01603e0f0f40f07802404009200303501181080f6080902e0311924001d20b806c100d0703a1003a000d2010028000d00041c000720b44992081c1c0700420010301035016081c0d46207405021012291403c00c01150300c0d20030301c0e015540c0006580c0032100006115640c41d81594103c51056010035103c2d000300041c0c40b0602c91000c054503042c4002c0155102a2000a1a501c00513 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 945211384 1250 945210134 945210143
    0x201090f060b1f08060f01090f030314071e1101090f050904030c02030607180b030f070809120708070303180305041a1b06010302010f050901081803091809070602010b030604 76
    0x602000c1c0403078484003100100d0498241410204004440020300030030b200b290418480da4841b880c2c02411b6011341c12360410b03a50032580b1040058103560307003a50f0200360954108482a81808640b00044422441445011000780491001525403421800903046040e54074144217201c0c0051007100e07401984031040305e070211180f8500303844a0a06a0303561103121000b030b406020344401c000041d5006800c0210115100d81034851165503000d62080501042e036091440300807000c0402e07510351080d10700c1c5030448500310503103e2000001c0c42c00400c41e40f003001c0071182d62201260b031809040c0c1501c104040e01051014135000400700780d034004d21034031079805400f190550000b002c1d1310300d0040f101038a8004075805030b854042c00008078083d80c6c1c1c0e00c0034881240051460144204000e110718141d40c030b5104180c4074034140d80c8540302001e041e440301c44050451844140001c410300d075645034102d590a0900ca41130313030060074200103007418686107401c45020b40e8140403103000f0341e450001d03410b80e10a411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 945212634 1250 945211384 945211391
    0xe03030c24160c1a0c09120c0303040303080402061b07090501050102150402130b090906060f0303160f031224172104050907020d0f080103050604021516060b100201090f06 75
    0xa1a294818400130846030b41d110074002c003000040c60380680100340d442001c444e030386402008500000e031707500042c0c010302c0c1e00360300300f40000c00c0000d004044168010f8030041ca024141021040c030504401003841c500c00c001e50045030100700c944018454079016100c00c4c0b002c0c0c11003000401c101401c9040141c002400391746040524078000406034003101d142c0e0001422025503007010f040e0151b5808050710201d10501c0c040d41c45000600c0c0c0002190410441c0d54400150f0242e1911104020784006d1750940500481103134040080550b0300c9417410000101c40c0e5140c54a409419401d041406500072081140c801c48841900c0b0b84c0000d507010940d0070007450041c1c096081504403005020f10b038402c41d084a078410900490f641c0101d00c52405100d40da07608010036018041c100c0781044c080c440500705420210228016040c03905040c1019260003d10b903103400100c045040348980c413804282c442c0d03079441184801d0b62500058501000c241032000b400000750980711070044150500c03008180ea640d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 945213884 1250 945212634 945212657
    0x405010e0f030624210c0f10030f0b04021912020a020c1302190903061103011212022104080708070b160f0f0f0b16050d0c0e03030c2416 60
    0x4034103514030b0b80060203420140d00d10320701c042e10300c913a02d8440b00c0b0305001c0c0908019914141001801211148401088d0102c000c9800b04146d0003096000c4000b820306484043c1402c054445000501c410604170224544914055070300400d1009100c0e00003200c00d004000c03104001d81e0014144d4a14031007112b000481c250722901c0400284030b0600c42840d00d41400f0309810401d03410882c0f01040324024202803150102c4100125150300c405d0141b0b01007400503a40d20004241c078088000b00e6044140101c8004103158030500140c2d803030341031016400f03c0000074144518101844000001c1c1200001041003e00b0040c00107010b0140d00402e9009803242c0821009004040d0281100709070014203002c040d04650601c04000034006106541b0010780c1c0700802d201d070414000440c00056a81c2d81c2c5400c00308801c00c0c5d0f60152031b50385e811004010110401e101242d6090000708601c5141e031000304420f8184203134a041ca040c500e0008400b161004040000e0710b1000d488000c121005454109200b06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 945215134 1250 945213884 945213931
    0xa2903030409060b0a0813020102100209130f02040501021e0a0209100e0f04020a0e09070611120c030309011d0c060d06090906140105040207031202130302150405010e0f0306 76
    0x40e644500340c018201003000403900c030761304014078541e130703150b510400303659290307403029400000410b402401a849180c8a113008080c5034090b042c6060010980c419003203070380702c00005980c8800d0f54035500f55170024003000a5a010032148030569010030700c052142c91b151601903100c00e8050b030042c1c000e2107905d0004180080c1102c0d6000a0040c2044c01e00351824940c0b11001400d030200d034124000c58a0000100d04030014000b45403103030740344000500441e410613070100e80c0f060300b03c12015035510803014020700c450740e0100a0400c41c00e0400c0250344034641f18012a0a503003602c0d0401d19503150b40300600039404404207000b560301d4800c1d13076100d60740e0b2519046a0000d10356507020000092419510208104040e00041d101c154000e0800c42141d80f6101003004a205401e070041c0443c0c018400c04d0042d10040e005050035150032044000700c00d036650041840d00381041c40240c20340c1c2c00050148110368212181426120301a212184011a01c0c408641d5968008c1d001840503c2905007928045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 945216384 1250 945215134 945215137
    0x180721020a0303090e36120a05210c0a050306032805060907060f11010b280e010b030711010b12071701020c211317060a290303 56
    0x65000c0d0090400719542c1c1001804001180104042c0010040104036554010120311a143c000c04000654a0702000c0501e10a4080c01e08240391a0103103203e0741610110b000046c041810045d181c03103641704c0148000e00004202d10f00c620742d05000d200c091044100040301610907a540501f0805d503207071148030000746081540c611320082c007600071036442070502240b1070504503a4800c07000c49100d52601c2c070f600ca481e4000c50003940000b8001d5822041c4407445008074400c038100d02000040c052091300b0210364030030030114102800f0801108840d00440d40021004000e00c03104100c0e590369410300404030703035601c0040c080300100420680d80d010000703001e500c10407001c80010300d040720800010700308580742c24152081254082e0380c5100c0e0617030850107000b1154000303440801703800c158060002c109640d0311215810840314406000021444040580705000f500140a9041d0001030743d09a40e4a0800002d0070051402c1c1400303000764038040c07005140e94024110030b03048402c2000c0c50010920b107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 945217634 1250 945216384 945216449
    0x30e030a03030209040b030a0b070c030507060203070207051507020f090c16150b030f1009081b03130503152205060a0c0e030f03040e06040615030b091807 68
    0x14040c4103814020180c00d5401041402070a075801c0c01201040300c00c040d110700001d20301810303a443d80400105241d01c2051450f00c12440f0382403042c14001b19848103005c9800840d20314016a002e4a41400300d031410803444400804d84280b01898900d42c0d5000c6000007120601c41409440000c0110f11401c51410680d5460240c11803104c006440c9400e100c41c840021180c0841414900f4075030245c5401c0101c1c1f50095446d00f04010640d4030100e90f043e0b4000e0261407001e45040c03070288542210034502c5052900303050b00075802180c841e0300488280c114100594440d038460340c0541c03906a0b01c4800c280405901900e040d10715648656813140380d00400c0c500c8100105180545010003558040c00d902a4200b00e00580d206203c0d030804905055644211000841c05a80705100400200a02c00e5106600c0f07c000b07040400c0c8542d59104056100904400c6140440e4440500030b06a0034240d807095884403059001c007446d60711031b0034000c1e210072030317801503081d0b00c14841102d445220324100361450707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 945218884 1250 945217634 945217639
    0xc040501030902210c0f1c152a020106060f02101d030703050c061605180a031a0906100f03081e070b0f01080606060a0804020109030602030a1406100219030e 69
    0x4859103080e84603511014085030303c1b40f08280580000040b814031074000e082800b10042c0542140725261596001c03008050b5006141c1a190441c92004801c4e0b42c641d04165070343c0310401400c07205800e02c00303401e41e081078010390108584060030540181e40044d901c0d400110041000407403e1900d8082c22119841d2555028544000941e2004159100c0010021702c0c4941c019202c042e15900000045130341600341650019106210310003440c0c0346000d041c007011400801c04035005a8039566021002d0390798203200c6c072156402c001c0011500c800c0c000d81c0e038806009581092007604241c40d100c001216400040c12100c004100c03817a111100da00401161140310303503500d07255449490002949441158104051300b5000000280141e00040d1030303024501c024039080c00c001c03c105085521300320040c810303810400701a034000301081c5640b0007140501c1e404900800d80b002c200d01d10081200d0042c0c8594014050346060100c2c09602240850850100200106e9140c0340d5040c00c582d0317034281e00509c55 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 945220134 1250 945218884 945218929
    0x50309010e030f0a18080604141617210f0a0e0402220803040b3405031312120f05070c0e04020f040504200114070507030b010b030c040501030902 64
    0x404442c3da44000d0100e0a07165554690f207110140c4c407404042000344034100181e480309000c80c00080b4040240030940c06584204c0d195010810f40915000c2c126500c40103190700300d00c0e8485800b12086c00005200942500d403119a07003440f043c1407144e80b064044003119000c021450402c0c0506c5080078158016004005544078100c40c12588081426a1910410003284010003d0001c4011003550b04071140d5202c240e040c40101c4556801030340b00c280c1140c2201c040024032032080010a40c4040185000300e0007580c0340c5140284100340a24150022261440caa24082d40000c03a50054002e00f4252403500c00d24004641c401a5910f0003000700040440c0054000407918047c810b00d0380380f00e14022181d01d0140f10074181448100c03841070710040c0115103040110303105000c4400c04000300007818500315290510041842200d40c1103914110355a4000c00b034204140400380c1c0b005405442e109d1034840c42e600307190410310407900c16032003007c0c14580c03182d01e240199a40c1c0c400000090b01d03455a0030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 945221384 1250 945220134 945220147
    0x406030204111b0d02030319090206030f01051002011e09050109020307060c0507050609010c0f03020c121b010e011b170307110f0706050406031d0a0b010312081303050309010e03 78
    0x407081d60000803c42a481d101c102025203600000507440d181d050b6036402031407a50312410851034103240c9911081d082544c46562140068071000c00840c81940d80d20f0308010700794106020001183c0b5840c20180440e818082e911603e1138001010110b1101e0b00800018941000d2420034054005084c010354580107100300080d8a9400a200c1804203210320183c07440c3c070380c0f610200309840c011900c8450000c2c0900b805a00040c0324200c40f0b4a41c20301a00449445030612030000300368044c8003100c06032a404c110401440d0003549000c404000c0e0702402c10140c1c00020400003403803138a00310711782c0c0481e0111122100a1104a02c0301c540040c5100d07500958901d04088042c0004c1440106001c1610480d00c80e44074508d40072072640165510355850510b81484c20000320041d09161003101d1a0b2540081800101c5008026030a02c82d0b2003285610b51661450030070500514860030f20105000014040000c030002324a21101c3c05641800c1c002e441c0d443e02110540100702c010701d141002c4c80001004d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 945222634 1250 945221384 945221411
    0x40b030d0519170604151e030201020f030a0806090c04120b060108090f06182b020615030304030b150a0801050129030105010509120a08040e01080d1d0406030204 71
    0x40004801e0001e00707100c15410542c007100c0015142c3d9812031203819402c00b041d03035490a608160a440d074181c0e02d600c041c079115000240f44416007040c120341422101010011560140410398100c0c1c001d0029509095040c90068002c140003130219105108090015182d036000c0310a94002d0030420100440e21710651900720701c20401580c065000c180c059000610210001a82120007412500a0300154441032815000703142c7c00251070000b80254000982c0b0521601058160381000c903200380403a40441d038000c2d0070300328040c0000d040310124500c0d020039034500004513800c5a0b4001034051041d60340381990110407500745c0c103c1d0307403040315400005004030054004070b05035459000031140c161045080707004105400a41d410b601c020034401041a9070150000d80b241d05000b500d4108040001801d01d07050030919030f01100e0f0040f0104042c06580362071562140907144000080800592202c40070b01680e40c0e80402807400d120355010b40078141c0b2581c00403001541d0180c001e102c1100d02d03020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 945223884 1250 945222634 945222637
    0xa0908120a0506041416080915130614010803041806050915030c040b01020a143a0e0d06091419060b06040e011814090d02101509020306040b030d05 65
    0xf40b8600c035504011290088040c2900c10500030b00001507180d4421820003400c2e241854018202c1c85140500d21b10411020700b0140010300c05c503403810b500c0d820031185140160490350f0220300d88043d5a6910014403503120300004035000d139581500c0e0b44d5418032a40103000040d0415820181d00315000c0340620085034510145541007120440070b458100918405200c22511150074441c016446580c400300032070412214003004000b01c03026101e864400c802080075004282c2d145602c038040c450b802c80c1401090315481700c40700c4500c1c0b400d68420341c5800009828560460310140545075261004401c00c01d025155038000c4452a0503070300c40700a00d51146008640022082e02c50a00340442072840d41707414012203054451000a4419990910b80720b100e980d01801c1a180c0081e0f41d815020b005040030024a038840c81c007000c0100b442c0c2e103040301b0003401c0000f03500500340458105180740c142c414542e041503043d107000c1800140c5a55843c030024018086280f0001d8141c014002c0c0d07006036660000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 945225134 1250 945223884 945223891
    0x91002180108090d1704050a05010e06100f0e0a0f0b100c2303040b03181614040c08220606120215030103150f020c0d050a1701050303030a0908120a05 66
    0xc03120000c59440014160303c81d03952004c2c0c0f80010340c06104002010f10f2401e41690090700031403c43e040034000f070b82d542e400c5501141401c4000e03440f1408000b442800c0e07801c850003038550140e10010f100d1510303c40552030b000107031080c100c5c030791501c0902102d00880d6009800901e402442c1050f07034601204003515030310704d90300155240b4510080103181405026100240c480c8420b00841ca00341c40d000d801c4c00240c202900c420030b40d4002007080b01d926181003044042e6030300c140c40e02d4401e662134a0305c0003c08000c40c1c01054061030404d024041030941041000c2da0061488016503070351521041c00200d25032440100514042c41c082c5c1c0420b00c7e82403228007240c220303c20303282c0700d04c01031580c03400b42445d0100b4400146040461482c1c0d108604a680099040c40c24052001d410201d0b040003c505040001c01c2000010708046407004885611109001c4050100b02100c40382e94104804a0f0700c0e440020191114280c998400b0340401c01c2c014202c03207100381080b085031103c4c24040c0040c2c001c0d02041d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 945226384 1250 945225134 945225137
    0x3090c0b0c0a020423070f030f02032203050f041401111501050f01020c090c1801140406050f300c0702011d1f02010b0307050f030309011d0402070b06130c05120910021801 75
    0x1b80e0100d011689c3e6100f243d00861041403a031080b007200d035400c6490104095030840800030180f142c0c0d5100740f42e00b00030b400608001099000791002c00fa0005080d5503041820459551040c08800c16490b8054002811342d2010740e61201e00d801c22a0050b4030b410449040b80390841953390410204400c640f010740329078000fa0b81c024520f0f0104e0700045452100000500d44444c030308020410485000303e00500c1149940b100c0107041c1444030100580209501c8100140304100161240ca20380c20b40c012140c0c010080d82070103007021000d400080011680105650b6241c043d40c00c1c440d0f80c0ea913400e6800b040390803050240c003140c039840c90009019290342004180288208103020a0782e2400b41001003401d10080c00460404602070700450751107841c003407043c51002d9000c181070300035200c40c0020410350f0300801c442e03089410018244450803008007540d07407103180341c03404ca40303891607104044070840062840b0804d055101d0055460510303a80c1200d580340144006249160a039100071901c6885c02c09 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 945227634 1250 945226384 945226391
    0x1b010906060501111519020a03020706060915050402180415140928140a15050d02010806060a05040816051810060f0212070303090c0b0c0a020423070f03 67
    0x9031001903680000404418038140c1029006555001882d00c0d174560010400c07520303401002c4c0f1403035000c0032a80078030400c0c0c0010350005507210502c0300341d014600081009441c1042480c145803000c10b0310f070b01940502c6100340d0f00040e10720580c1c0890306183d808100000c000300421003c5c003101807981035084c0b20b03003001d100c0103000c80c07681c88c600000c3c032070f20408002c000020b101548440707801e070300d441035240c40551a5852112150400c00010490b1040c844128006910542d01c0341d8000780d401680d202c903204401c2000c2c00380040c2da0081ca00c64000d002900e81a8980148610541c1c5070b0040c1c0e040703080b07148a001001c50303488103900c4220084945c159032140e6550404c45002c16190030440e1030170115015004104035881c4902c0c1944403085191065a0300c10001c0b10400340385600c0a081500003039264404101800859007811008113014622079203040c990101c156200c4001a8000c0e00c95aa1485000181d50000916800c8812003d582000d02d160070034000d00f41821030344401c0d001038075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 945228884 1250 945227634 945227639
    0x1090509061506070204050c0c010606031d010209151c051501080a0c09031104090506010807031a011401050f12090609160b091509031b1309020d1401021b01090606 72
    0xc0b000d64080090701900541ca04141602884044d0001900001202e4410003800b0300c101404e12070800541310541c0c012400042900190341c3c520b801c0c282c0c550701640304109100e0075580d000c0e950400c100782d260034652134600401d5080424100248001e2405003000b00300300c004203040d40140d80b080b03000d0b2200105500c402258400300d4441642d120042001d0410070710204441c0524a8580d040040000c100c24216949982c140a000e03446126035500c00307403052081150807241204114070141c0d000034150702d401d5a404902812640d554188000000c04030f000212450890340e80e69110440c1d41e41c00d0420759070050f030b1858125800c002602075070595411000d41407807500200c481f50301070310341080380803000c100b00215503620407072000404000034482524240710302e800ea0705544c40f501c100b0320404000d00007440449004a0f9405191a0f00c5030b0040e40e6402040074100d81194441f03058880c408411402407240841c00140325490b40c0a0014074101504a0314840d845090184011035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 945230134 1250 945228884 945228901
    0xc03010302090a0504021c140c0612150114070b04170a02030702060c10050f010e07020c010912020f062a1c27031208070c021e180109050906 62
    0x203010003540002d510010918921054100903081400141140440440c40c9854a00c009002d4821a00c5102000f10b01c0c811480c14400781c69440e20584e200751400842d00c030402c284c580001d14070450740c081c103015545264420b850000041410b11300c011f5503201142440c0c40c400c0c07400c8504a4110005007000c40710f070003401d010f07100c29411940040d424804d565007045180e4100d01d17450802403103240d030844142c5500d40601030040e6100504071710f165042c00c00e10f60f0181001403842d01554800758036252180d0307101100c102151581000d45801e03816510000303984d5007254504650001000c81c82c041c000c402c00c07040701ca071045245014401190395159094407401a1020b4202c1030401c219289102800381d0040c080d402425020503e0040d0315041205240e603003a0003e88107104443c12030141250404003031600460f103030400c690419100d9000071410200802290038140b20040d841005031211400f4820132040c0d0740c1c0003517103581c4030400900141002c5403041400d03c1142d000c1900c90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 945231384 1250 945230134 945230137
    0x9010b03070501050a11070f080607080601080103022e0306090c020a08030109241e061803031d0d0510050f1504050c04230424030605150604030501140c 67
    0x1180900a04801c1d45044019240c42d001030450b1001e005040e000e10380d0b082020710048024007002c8445d4102e407070916100500d48040100034006001a500034001030741e030041400d170304507a411690181e401041602c90340300c07a11b90955290310906445c9424070b485816030400c80503030701c41400400c2000a06071080760785070720021010307002c0d140c102300501591403643c01c80c40d4402e25845010003203074030319402c6139070754095988001c81200a0050084908c500d8070b0113480180854540407800c0c80c4080000c0030606a00d20000b420f004c0300c07480061100950400c208151880205902881d100710701307200343c80d6400703030400c40042071410380007070310407032092240f02e014024800140400719521024800207040103458994202c6082c04006003c002c980341c900b5401c042c1c00c4030348010000110502c000d45804021401c4110184801840007111200700b02c1d04503030b040b075030110b45910703961445120704481e2044141c0111001801005200c0d054000c08065615900c1050b415947c040084082d03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 945232634 1250 945231384 945231401
    0xb0a0504030210090803010504020d0204050901080309090f06010e04240e06090109020a0203041701270c050f0612040c0b0c0f0d08070e01081f08070501030b040e0309101202040b030a050901 83
    0x40c5d4074140014481802c2c55405001d103c69903000040c43c05403584009521100243c2c0320a1060f4030004821040382401491150444903404c44120742d414218000b80c10840e108140354003850395560b404e40f0040c904980900b02c564000b142e02d03215510b40131004414070044070003d00a030001030001440282d940300721402c64003540d02642c2410309080d8030a2410318001c100f0b8a0710345d00c1e81046071120200c01080f400501281c0320401c1014858070b4089540d01250740322912654035400c060040b0f4440300d003181c2408951004640d15540d451600b682415030b60f1b00400401c031b0010079a281030110000340d00350910f42081c2298103280508100b15511070b400c03203542c400244580c01503c9154000e040741e03900400c1204c00c09102601030041081c1c6135015506c409007580c0010000c200c1542c2500c034000889506035400e001c41440448084da0364800d401c1c81c00d000b81d04404916040d00d00ca00c110540b5400886c4042d503036196511006030352070304241d0b26031655610f030901040880700140b190244 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 945233884 1250 945232634 945232643
    0x30c14040b0c010b0a06020712290411030a020102060c09120604050a021e06092e051903021303020613090f05041707230106030614070806010c0b0408160b0a050403021009 75
    0x3115803c024002c2d00300ca41c03048044592b0105049420341008040c0034030800c0a60400034100a4941401c041460700540c0c4416400307a002881c2d2000540d81c0451000d80c042e0904600550300e00d503110114500043e03022252869008000600081000c0800d01d102a20700840f82d5030810643d0310080d040780c0d24200001a840300301085100c0e002d041034154122030004000d01d440c5001c2d4060780c558200c0c2a46201880010400102c2e404000803141c1c3c01d02c8000201e01c1c0440c200b5040140c103000b03454460201900c075440c0442c1a82c0010140140c1c24082e10510b9003d00400d40c1a50b1400d01405007a01c0032154a0343c0442c60500c0703d001d1405540d01300b070304210000c030709095035244c455070034080d80000301d01075407100c0b00070008c60664021400030302c10744c400b201502c0c80e040c7c8004003030707400181100e07041100200d031141c04103904041081c1c0045c0c2100841c2e580f905040700e551010544400c0c001c0000008074100500014550311080c07003907001c0c0d02500d800d2041400300c1c00843c1d160020060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 945235134 1250 945233884 945233893
    0x101b11030a0507061a18040c0602120d0e03130b0712030203070f0e0f061c0501120807082104081305010e01020307060b03030f0423030c0a06030c14040b0c010b0a0602 73
    0x6000c520290800c10b0584102d440403064017401e80017141c41000440d42d9a40105a040240000c0104510b4840c00401072031028100c54021540341c0c0a203403062401c050b038200d8076100d003540990410b00444c1d040320002d1a12030385150340d409801040d50018502960340c620b00f442e1b45d000c000c1c0240210391180c81950f46010344170880302d40c141c52003c6442c0348a500008034101200c2a03454006c0140749040049003210304081c510b850190580c0c00581000e481c804100c0c1d140800144298240c80a90741d100100503268038a0482c080300c3da491052400300d800c50340400340014841120005e00341050340c18100c00b03d80e5110030064681c0c14440204900503401002800f02041d200d6002840c5114010309070b0303180000b4000704d0700d0142c0194101d1494441a10110b0103403242560300c0104591040e0050580d0018500c005040010140301c1e1100b030507124a043c01c2002d00c507024424000c1e80d0240c0450711592075400003e103d4001c945c130343d011036280c0b4648046a00d01b403114082110490350040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 945236384 1250 945235134 945235147
    0x10e010603030c06050a0f061e09090203030a050304050f0a060f0b090105060d200a0810450c180e09060c07150e01090c050d0c0b0c101b11030a05 64
    0xf100510317008000840f0075035100d9180c3c0940059004000c000c1c43d01240440c2c449840a20000a61000354095150035103007410b60001030314080300f660640700680c18034548a03510f0f41041c6080041080203100640034460f9084200001030f8090080001c041001700702000ca4942845100134003801202d51064040c030100c40810b5054100005441000c80e500903001c4500c0382034002070700032505480208021408108040548400d83c1c3c0c02044100010000d001141600d00905ca203520381c9660480361507554012030a0800d400d6805481d40418200314010402c0c00c001e21481a031040e20b2230490b800f050000b400d400d10345c400c03401515a40040d0000b5103407480d8030000340e804200100e600155044d80d0f448110500d00c25aa40c080e94403002150340d20140c07502c11340c0d10005802040c0f2a15040c0880c2c00070401c0c1440d504199043c1003102561440703078070070440c64a40d080050420907401c1c039408801c0b039a203400703101c01c0c81d6406490b41600019180c0c6866220700030a0040300016905005c01d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 945237634 1250 945236384 945236393
    0x5061e190c0216090f0b1e01120608030a030f05070504080c0405070309020a09020903120a0e040b0f03100b120102040b07080304150509010b01080c0306010f180f0611010e010603030c 80
    0x101c0c0c040814012282200c000e128580c819110030342c0300f56540c40d603440c10f19065070392501500410b40030440700413560507030403543c00100080031142c440c104000340e034581110f40c0d2a03601003400380c0407000440f07855240041004024004656902407001d042001040c1e1080c01201500c0640d0107050290420f4000708090000800340140440e04041e10341c0d0070000982c0b5540c1c2d180c800340910745000350755158903a050624040c1003155040480508114190240368000806089080e0880303002c40d0325820000010101e1403907290656040c012a00d00010309061680403455090080e03c02400091040300014202d006501c110743c03400c1c0d010081c040006541c14001c2d41d00038418014103800620795403034001290317400c940c0070900740c0d90703002d482030b240d07803c0b154003a44802205885440c500c0d01200007440c1d02d008440703080a01c00035081c41021a507244080e1005810f4800181303c6007940c5000081c8060319844416096504e00009106c1806040c002c44050740c1d01a2100b00380c200281c4d49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 945238884 1250 945237634 945237641
    0x3020114100e0c0f130f15080f0a0608060a06030b0f0f2a040b0703021b0307090e0c060a41250c05190e0a0507051605061e19 55
    0x114611a40302041301400003000000900b036080744220314403010300d04042c1c400503030003000c0d000b40c02c6090442c03040e16002540080039070b40c4030108010301c0201d9180e10741030f0301c050170081c0c022003d1030040004005244040d9408030089030701403000c40c8542d8813050040c00c506481620164000e503500c800261200540c58050140c1c8000103040030008280640101c09541103608845039550300055013030180350341000032031403000001030340840207403500d00000d50314020340c8944030829880d42e41040030000300b400681c10002001d000c640e40c0d900f41d042c004000246012a24804c00c092071652a03036500103a01410000ca011001051050700c84400d00c102504400700044658280c42c240e5104200c0000903003040d5442480400121030802007000207411b0802c42c1d102c6808040d40341040029042c54a25412001c04040010075840d481d00c00c6030300b44682920310105140b00c5803c034081010000712544101c100b01302d0500088160002e40c1185001510114071441c03000004c841d80c0030041d403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 945240134 1250 945238884 945238891
    0x70204020c07120804090605032b0306035109170a02060906070c2402070210020601091b1d190e0402030f06070912060207140a03020114100e 62
    0x404482035580c0d200039403006042c1c0f6540444015401007000c1010204c0c82c0107120160100702e0180811203020880d1000c0341031440c070191f20141292812803106ca000307038802805142c01084884d04810214100b10986000c030300005444252041e00344240f41d05405240c40564001503009440440502c0345c84c007402c03403a0016105050051440300d840384500d802400080b5040d0083e00c824a0050f0b00700b428500e0040c6240305100d030104c622070010384404048040084a411000c0901e48820307032507c02400b500b08025004031030301034144030a980008096040312850b0005000e12044a080445e940170045107800116440030312940000044003a90a90524013034007007140b00709036490440401246503c00140240d6074805c2c0001c0d410305001000307210751640000d00c0c2d41e007800580107001380c64074441c003501d460745591400104005030b011a04001d4000b50000495400800003607103401040d8812405076103481c0d070030a010700303d40f54280d03c07820120056401d40307841e202d5110044940107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 945241384 1250 945240134 945240157
    0x10b0307030b0607030c0c0e16051b250f1a0c0c030709231611100504061d0601050603011202040e07030809120708030a03090302150c0910050c0307020402 68
    0x38401c0c48903036203e40d800f80a690b4043d540f80b1201110500b08108103200135040111f407611a00308101c4410b2035203001e2490b00115190a035914891141d212400250840382c082d80750080340c2030414200301c41e040034010300403c01c1214a55903075686c25250724018900c141d002100014810800e51003080000e000d203120f0000c1600d81250020300024240a103603044940d8040d580d601801000d0310322a606004515009044541d83c01c0032078403d000e400c00c60340841c0c20000300d082180b2000b001808840301c0e95140c1035090029003841e00d40351000d000314044100c04171020103201c01291038006103040c100c0320b001d40b42c40d00d10303401c241042944e09854075050b604a03450b0403916103080300c01c01c0350100841c020080d042c1c0781e41c044c104200b9200300030652030724a688110800c1c4075030b140200844505100781c0c14009041d000078030b810707070922440020088850380c0c0c020403c48030003170500c0140054081155265007080001d0b06c160350754050344460030200c2e030051201c00d0040c00e099004100300e6600703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 945242634 1250 945241384 945241391
    0x8041e1e0504051e0a020408010605040e0303010e0705070602071505130b22020303070b0703110a0f0f11060a090302250311030c030307061a040506030604030c06020d02040f140402030c03010b030703 87
    0x521020740b40000705846100b080307980084c0c10400c230314080c171903080a000102c8003449800340880880395a4081802048085c03403100c4081544a4025021030700295070103181952201c0d40313800c1401c03a802d42e038210014031508102c00a01420b40e80d80c00800c02641c030031108192038031843e84210049066020060b0000600c20301480036907002c1015260103482075040c1c2019150890005013541c050b64000301e0300300300a000c10b60400380c00503082c5d44107001c90b15024035814005401190542011890000307030b401203c0c240f01444500390455200640241c085421a28103042075018840f500c03d104100c241001409000250f418054a00f1216000302128021107500300002c0c1140d014040847c0c0da140c1d83c542201f8018510b41038802600000c60382000305180c0280800d4440000400060401900c414884100001a410344440c22180c92045440300d407102d0314403003640701c103000d090030000340c07484410014070b028001c603445002404401070850f4030304840025141c04c0035000c1c0742855103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 945243884 1250 945242634 945242671
    0xa0c090e1816090905010f051b070618030305090c1017130b1f050f0d0201030f06030b130203010f1104030807050304051003052d0c070f08041e1e050405 67
    0x5040003010083c0c00f54000008821039145806421900c111450001041c2010100035148a405c051900110382c100741c2195070313000926149004109404560142e80703201e8083c54140340e811743c40288501412003ca0700080300c2c00c000c011110340c880081c4400075a0700032a4148080e4044420b40e080010103500710b8184142c2e0750780030404002103c0414004075861100001c11104401890041100b0b40c3c0d070452060200000c0b40e00680607080107414103464060001c203808140e4008002190421030300015405c01e11410201c0342c000314000c1c0c1c8a5030901d940b884038403640c2c0c80754003445070340038885501d050700d181d4035224280c00603227094405020034400020030361102d00c20075500d03040c15500003a082c90004081d0307070030101c5510b813401c0c1402c1d1a410107110710300645a45800620400d0110f8845a85281c220042c61002000800070a00803500003480103409403d0030035110f00c5010001549e444483c0030712007050000f0801c50a0b400d0250270080d0382001d0703005c140c100301800d20302249105c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 945245134 1250 945243884 945243913
    0x20f0303011706010f05010801060c030c050a20010216060f1e0801051c0201020a0206030c0904020c010c0e0102190b07030f15061b1104050702240a0c090e18 69
    0x30002d9000c00440149400003039841e0741c09029540c050031000e5280d48865080000003000000140a41400e102c510715000c8249030181d0074907000d9a0f8050215042a401850018038480410542d000d480a03c00760000c074540c008640520718440d04004070075a2842c14100315440c24117000807105003d00000d103444031b0f00800b08407400101c4607441340100ca501d42024007800905030f045e600e80c03540311009010b00603079001c58210317407240d0100c6040e07403643c440c425904c00341d2140c0e0512542c010310000d0300c00903081c01900408580e07805030316102d801c54441401a616803d071803005290340c2d114403a04400180e41e1180345a00111130380740c0000c0132209450f80d0300403900c0301d00c040c0707080300c0540d8420080360758400000741c141003042c0c003d164029020381d201d01010740c507008403610403601c80340061070360f62080007260000303440f8101e1303100c5a0308080d9403545054010759068116034144018ac5a00382e00510b00c0500b1540b03800c150210302d80c0c0342d13003a201149a2075020400b10703000c1c0540c01142c3c2c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 945246384 1250 945245134 945245137
    0x2120307050f0607030207240632040c02060703020d021608030a05070f2309030303011d06040902010f200f070f090e07051504050d06050a180c1203020f03 68
    0x8a00c41c200402c16007001000742450400f000304801c04044c010448400014000d94402a01030200305041c00c000c0011300c0c251029215a030020461012002602c50700c0f80c0303086015803400118814443d40162211080c001600d861100020150380184085070140d84258001c0409101c040001030601020014103d007244009d501503a0340e010101c240480080c0d035100d00f03074003c003560401450025107018041c0c040c084415400400b40c1c031003032040c40344107444000c07101035a00003001d8958a42c0c49030030032080b481d001c010040f9070001c3e51002403039a0520313128040c90560141c4507000d03581c4044004954000e00343e140120030028008940e08039401c10080d99080101c500050b010b82800c0c1003180c0200720a039805014207a0406865282030b81c00403c2e1071080e21070646850048010044011129200e01d900c1260414401c1c4540000d11505601580c01081b00000c10b01851a40400d15480c24100d2103025115550b80d6000300308560980304142c04143c82070041d984c050580c0400641503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 945247634 1250 945246384 945246397
    0xf17040506040f05040c02010911010f0504030506090f0d02010b13020309101e0b0f06030105040e190c030c230906220504050d0809030301150c240c05040506030c07021203 75
    0x70360f40c1400a100310700d080d0140c040324113402d1000b0000c082250302d91181c00f0401000030342c1804001c20340c0c40120382c030400460700519041822503450707080000f003040d0340e0000c0075150307105401100003004404d807040c044c24030129401480a100444170001ca00000e51028010001512070310481c50309105241c0100c040c0c9451f8200c00e07001000e080c031070300300a4901d0481d160388100d134141740d0071035281d03a54019681503070015640004c412104030403aa00d4501c0d0704d01840303118017111074080100603110120100f0b9920a4104010255542003001c000103030f500c0c8200303c04040090307400200d013040700145601c04001054a03400708005040c0c60600c035620107801c41007503110343c104400e000080010f29102d90141c68500d04030700d0840032a5440e4001805201c40e2241c01031041d1003c07a00c11138854181c141c2082001c5074a80c3d14450240c0c0104030510800b105078200300100e0b04050042c0180c40407501c0113850186507682e0382c0884005a403111404030380c0521140041d41c0030480c100b01410300f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 945248884 1250 945247634 945247649
    0x3090605090a060b180a05090a0512090a0e061c020406120606030b130503120604090b0124090b0d02070623011a1303140a08191b0f1704050604 63
    0x20321020906140044e03a18403851140140385901082015901c1944010341c4911819400507440c0c070755010040c14140c00b40702c05412486505081c00030180424014a81513100b110071030b03a52607036003041054108088880301d502442e2840c0390395224010518060440e84010030010300070b600c44a03c0c41c0d03d82003040c400c0e2610346c0c0ea00c4007401004059120290442a1007040c016110410340d9819907034880c0d01808070440c1026030208074540c440741c002200055108585404941c1c440703000854080d01d0301d1410011003100031050308264011200d02c3c1c10303140111b4a891170f0003d0058414040c2d8403007882101c41c20b5542204505030400315140c1407600349030070b11803062549004940c02e401d12445d0201718654204102c0d070441d0702140180740c0c08480d0301241e030009003000303004606c2c100354100c0d00142a40c00005110090401100400c0c40f0011940d01c4034035450f90068480001d2990420004004e260b00500310408102d203c2d85600044a0307045260349819119804100d40360045d85c0287c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 945250134 1250 945248884 945248893
    0x111201060b040611060103020a0b070618150b0d2622060212040506190219294f06050c121801020c0303090a050606030304030507150309060509 63
    0x300c9520000c2e05813407428038002000a5411600045d0841240384507101c1117203400078600c0e040000036004a185181d40500202d040300003070500201100e03041540c180a01c6c60000707204503510b460030024048503004501c03009241000001407500100c80450404000800e0101640360050442200000c42c20520078148040c41c1c007502919102080c611074400c0c0380c0911040c040d6071984016070b55041c0c0026400640018600816400d2a41100003810f80201d6081084144003c00c0030700d8007501c241044000c00c003200134243c85001e40c030644802e40010307541c00d00c81c001c2c0341040e011500095864520780040080450094103004400707604014070401c1c1510620034004688503640c1d004030209011450100d60307205040c030f03100009015109206820030018105582541501e1140100303008680d681d00740300c01d140e03684180c00c020403901481a100021341a082c00300548040382d50200051056a052a0540e04418060304c042c504160740e8402d2280401c2c0789024040c040e4070184040c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 945251384 1250 945250134 945250139
    0x606050a152f070f051503280902031603020f01030c0e040504050c0a080109410102040f08010f110a05122a190912060b04060306060305060906071b111201060b04 71
    0x1240ea00e0529046d4103811030280200301e200001d05c5105030410003241812001e5008140c210f1008140621010b0740520486564109900d0030ba0b28581c00c2d64022140094110f003d6401103095a020030380c2000041d0028074030700014109900140c0d001445001502d0300c2619180100b4101141544444c07096919a03100405001c110101820354401e51004003484d840c481c00481d1103603004201c040082003900070358404131070302075041c0d07400f4020400c0c031074081523581e05019000e810f000702001140f51030805920550f143c05e004407440254941c85079824442c1c0d4030800d03446c040c0002c0078581024020034507810ba03c1c5400301e9a00e00c0c0d42211035540e8445008416407000450700741810800d01070001c43c144200d940600c1143d00c2d291744418080f58031508074000c14080c11132035100070045400c015011003004408210144103a040b00300b00da0250365040812a0086686401041015011314a100104a40b80044c00b9104000340054401b110b044901d182158070b1980800c0d5100c00c045400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 945252634 1250 945251384 945251389
    0xd0f0c08070e1512040614090a0201080c1602090c0f191d030709020f0705030412150908180f131a0103091703070210090606050a152f070f05 62
    0xd180d801003c3e074aa0802a0003030481c80714a101d8803060b0504080c070400020708014081d0040c04140e14100c28422403030500d2990165185c00391601240803503440b40024000c00800b40964251200c0c184884840482c42c1d001d00c07151200190510400c00010440206012204001070607491408101e201040d120303a03800a001004401c58011501ca200f601400103a50008030300c0c041d40c0c0c02c1c0e040165a40c1ca00e078a280014454240018458000818001040c0e5001800035903101d0051400c41c0a811101c0050b40072140106401040410103100d0140031300154821004400809820381c03c8407221503000400c2c85001180701c2c6440c5849010603250200034042200b1541c000b82018030007500c00e40e44840040307594400007041d041c0d001c40010f540c14401c015491040d511205d08000741c5010307081c02400360050340101401401e01c8440045c0d0843c1c003000c2c2c0c442460066580b11201940c15000070800c8500c40c404112180c541c91103a8a85002441007000070b0414003107007540719140405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 945253884 1250 945252634 945252647
    0xc0b0a09050f0d03140a09050d060c080108030c07060f0314130c090b0d0b07140304050c01180303020c01030f060b04083a0507051f0c0e04150b0d0f0c0807 68
    0x1503d00840703a0103200030001c0c1c1c00005549400307400c00c0b0515143e00302c0403403c0b0380c211508d901495010443e0360106040c030a00342e020b5402012244d98083d402d03031f290303a10780f80e5170310480c50fa15151b03a00407002000124031502d40f4110038400c40c41d004ca0002034500398407029000076200c2d4446009441c940c0c030b0410144174412801080902410b2000c490b0000002d00204032090000d03150a000c0000680c030140714060f28413444030511a0540c89003860300342595500d03115103009000c12100d02030740711304030001c82c1c032507044960560007042100301250044019000050900041585488001c91080d6810001d0000b4014101c020700107401c0452401c45240003080d203040c1e00894000300c4020f820210f464000d441070150400913074610551504516000503103c9258a612400450101c00341003600b1244904516990303078642280014100070841c0c1d007022081f00c28841c1d5840c04c000809240c0d01910428255000010302c6054210520b81902c03c8000e404000a030311408211480c0c1e0000b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 945255134 1250 945253884 945253909
    0x1e0f0506031b06090f0405041401050903040b0d02090a08010e010e1e0304030b0414010c0804030210053d0b1315050f1b010e060601260a090c0b0a0905 66
    0x1d0050042c0b4810036101608080d00c02c80c800c0c0900340c000340c40030035a00c49050b0580c0e04031003c1d108012038a424144246001c1c1407207480d845650030000842e480034000400e81d02070768110701d455890b000092141e06d000750b11155100e604123035810000140a031007840360801c0340345210000300d507025107541c1036401c00c0c95001c0011150444185107140199002042d0790503654007804083c610340321420501400102c2c100303004650342c01c00b1700c04040640c0c49182140118820380071103024103241d507011025610100c400c000d540446054010000510803581d6000d5407d10b000d0300e481001c4c0004450035550150414500c04000040c60383c0d0144410f8105030080c8242d0503101c00d02c98a01c00000c10718804c00032074400101e404591640e03900c0c0300d01c0d2043c40c0176240400800c5001545012161100c5085039014046a0118644000541e180d0500700c0c0114a114204001d079803050001d00c010124004103540f01940d641c00403524408245c01841c101c02107444a811461800e01080020744541303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 945256384 1250 945255134 945255139
    0x6040c1406030c070f05120309030703080f0402090403030c110a0b010e070203040320040e030d140612061306060b040f0311010f050313110301020a170703051314011e0f0506 76
    0x10810003140c1c3e42c415055524665020190b1001c10285081c018946a81005800c6c00c0755800000c1c4654954004014640c007442a210b44680d99603001c1040c9001c08200d40294010070354100040000c0e105e584220801006410f200180d420300c00314051410341212021200c4600350070041c81281d602624042c0e1041c8184021803030603003159a0080110310006003c00300c2c0d510760b0018809555a81c200d00c244204020031207450362081c0209a0103440c00c010380304c0b10b207044940400d0f800d0130f00361107a001000d5210001d0005071200c14402242282c030701015107441e0394441c008140e04803810000e00c01000d107039010071185415401c0100400c008401c04c0d83c18003c52309003022680f038002d000d90350701c0780240a52440a00050070700d2000010501f0034290701d940f0001e9940c4802c0d400011186519544002280e8541d945000035400c491054400b9040368200501d0743d00021400213412240840800010403194003950100c403030050304081000a080c3c075031107180e5241b0814807407140d101c80c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 945257634 1250 945256384 945256387
    0xe03070c171c0e0607050c0a0608090d05090f0a0312090e1e19061512111903060504140702010c0e01080703091707031e030615030513020306040c1406 66
    0x10700c1907580d4074580080030040c54003100003242e0035028030080c002d10503003d8007013581d802041c079019807200c61344814203100c0e1750301c401c0106080d44905401c52040050400030080c004e80c51100f950540c00284125a204c0703048200b030006601e40310b508000961144208a10f040d045203000b0300707070800e40e13001915149684402c10440d41d4461541d0300c995581030b805507456460b540030900214109000c0040c5e41070610100243c2c4900c3d4907040e08910f41c0303660360860f900d4240c200c40c1c1d054600880001901e28024000343d60041c41080b82030007048490f0600050859845020030160395211200f0401400260100419180c0a0080d540d8141e580d1074410b0041410000181148001400b004105940c0e4042441000380b60100500b042205c0103a41d42c4405031441c0027401d0007052441d140b4111220840024441d029028140a4403610740c0404003216035444100d00600e4001e10102419240300310701e4000d40c4040c031030140114080c01c0c0c0290028204401c101c0c2441002d100640901c2c030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 945258884 1250 945257634 945257669
    0x1704030c0e0420060c120c0c180f2a0a12022b060f0e01030201090503071406031320040c020d09030b15100507050c060f2b0e03070c 58
    0x10b800f407014070040b0403c0d0918043d00000c0c80030890f0ba005108003145140710302100d1a49012840010700314049800e422a503c05003400c00b0b00035090079040b1006c00108070000411080c01c00d20f8040c83c1e00801c800030308810102d026030205440540780388402c912000c0061a0307c0340075031000710b104403540b0400c0298174112402824602c00300400100d0080ca030311100c020103441c03c5d150454401050824000b0800d40e1b140d03a00c1e560204400e10007240821406c0c01c0010b55400c010800304101e03100c0e200c05a45001c4050700f4400c541d0301c01001a0071220f0030980700000200da11404800044145c07083d495015041014041182e42c042116820f55028080e4a110305600005040c162a444107040c00d0948030184104201500c1140c4c140c1c0c01464681a0300b00d0580c0000130702042c5020700b007140d516480035002e00015200700c0580d159034500c00c1100291a00144060303018188a105a40c0c0990303d1500c120302c1140c211130f414610603080050340d8014030000e10b444001601a600050100c80c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 945260134 1250 945258884 945258893
    0x206070c031a012603130329011a0a03150902030403080108060115030f18080d15150e010903020616051c0c120314010906150f020c06070503071704030c0e04 69
    0x6100000040713101c0814281d050308101c051091b2001e80b44052201468561a03141039035080c55030817440000141030011400c4000003008400c1c0c1200d828044103409501c40003910340b8030b40e2004030303410141522100d9030394841003c6011034008108195005850f4103040c54002c1400006a03c04602507201900603c41010800b22514602000f4240002c0110a0b0603100c0085d00d61800c2c502400c59400703141e1414021410010070448014a00c02c101d6148402140e0301542021b000d0507144440c0e6451030401507010712911443d51905050007a009a075035030024010798003140c2206240e95800c12080c0030800c040021103c54815282108224520310f080102640c00b6108040e10107030a00411406150199120f0408010000101c251640e103507614407020b8580741c810401e1481100146020052040601c5c00c64520b540d400f80034a450844c003080501d420542c41901c140c0001c100000000f1072081007030003030309000c0d40d284e83c236140345040c004c181d920b8550020803000400c508020006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 945261384 1250 945260134 945260159
    0x603060d350c2b12060e0901051e0403020604021c05061005040c110d031503050601090b100201094b0507050315010b0304060e01020a11240f0901090206070c031a01 72
    0x4501494072500e00c0c1301c5600843c004c0c0040e6805403901000d2036003804144007041d040648681094020190790074507000c00d00042040855026005802034000b040c0145000e418503100340392704a104100e50012500c40b80d04044040d41d0820606c03000c40340c108918145402560000da05034142500c003800719159003910f07110054012020907984a802c8180141112030711009142c0120440c0d00968540a0b040014190314950030b10070754810305444040c40c414010558690362003602c5500b140c8449010383c00c40d000e4410601501c1c440e000c054808044618043d0620040350200d5641d000d0301e60a05070304018554000a0013030300101c00d083d012800a01003241194801c1d02c0d407954030340e101c0c2024402850004504040f0354000520000401d5000c640145128840800d5840451034810254441c0c0050003001f01c000f003d910009000755041d019056201c91010b0004c00c05c1c0c0810340c00100247c5c4001811560419140d4091047c044607903000803000740314800c000099410034a030440c06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 945262634 1250 945261384 945261463
    0x5010201110d090302070806040b010302090604020a0e010e0301020409090b060411120c0f0d11030609160f050c01180c060305010602060112080711130f0b0603060d350c 74
    0x8450f01c51010314209442008450001c14800069400506252400c451000c5080c0300581c032680003040482c11341d152034401c407401811036443d02041450200c00542c0c00341c0703442000d5981035500b07110014010300c0a0080b460054400c1d43c00590b50f1600c4410001166603054034a548003000780140c480c0d0109007200c041c0c00900c40103019440701241c14003000c0a100d070801b5694424180700c1c00d4406201c0138000b85000f0442110150855501c1d03002404d888a5141c0c00400014a15042a11198002d0009049040c4194008260704034140c0f0682026031100324211050545ea0b00b0030070000744d140c450240500510310207400b55524103402c4514110a00f40003a100130000200304080015840c6010121000600480c14081003808444010700c0e08450000345c0508181040c0c4030b07444c1510403a4070852006100b18a042d009464203c42c03003da003890400c215000c07940040c0f00a034050310324811504080b0718242d45d40001000281820020070304000788810b548007260014500890540a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 945263884 1250 945262634 945262657
    0x12020c0601180608011406041802030606120a0803090d08011508010513020d1d0c30122a0604020d1209050402210f0f04060f0914010e070501020111 65
    0xc0200b510207140c0d004104581c085421903280041d01c0c0020480713211420f200350011942040050201d40410724411301c0c18000131352682010000074154070309030f82403544003843c00080301c00d4481c1c10303503070b5640e01d6200f80ca040d25642e01008036500303059408813429016000720840c00c1ea40caa540807000e03200c01c07418004c95104100b20301481d0010b0b100790307055030704402000a092110a0190160880d00d1460001d00409405071985d20003240c240035614450040d40180e13180190882c0300700300514040c40c0c0d003650311035020b5a44102c4440d2480e0019003204000b0500081300c52420501100705000403040b10b0005801ca0000c0002682c0d030101020310340780e00301c02c201c0c40030303000c106007110b0f24001e90304003680c841d10100f00100e20b521400008802d07070b03401d218203520341d84031952a444004411100000f80d0021a8000740004800c1e4100e4104140d8152021804244595030020503016000c2201c00301d80d541c40042078007810400c56040200001c0c0002c0220800c1520060400e2040749034003076 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 945265134 1250 945263884 945263909
    0x160c030302032e050405161d0109180203240906010c0501060b040303080118020405130f0b090117012a0806190305030d06090c09180905030a090612020c0601 69
    0x2041c041640c1c00300c109888043d410000c1408a000c001040c21100d80a0280542e2400300081c2c486c04c844140140903c1003510340300b031005684c080c0c0050580c6800300380d6040240e840300002c2c80a0310385c0e10710085d01c2500e00d1b0241e03e9181413803260341d15580c01c043d80301194070340d917116104e1611240c030070540221081c64000020603550034002e01601e1a42d00c9040c1d2103000103800018560300194550507030b40c0c8854108001c05c202032204e402e9000b503000c0c0952004024500d14488a10303580140200d00d412580400c40c07042801c0000d140b60000da1000781a01f1101448242d0010b081c41907813160b440810024046000c0e00b800600c01b0351131008860700380002c00700070074a50360f1034000300090240054070f04c84001d62640b0301a030316504044060340ba50740c00c21101040e0030b0740d41d001d4030030942c4241d0360f40301600f071074031030440500c1d4100c042c120380c3e1540d0f80e60322801248050000b0030345c4100f01e8035824211407400e10010201d03004607480201851044c0401450000c1c003241c03040c110748600c1d006a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 945266384 1250 945265134 945265141
    0x91e0b070b062d280b1e0a0e0f010201050114100302190c020a0803040e0f1f06050c070b0f0403080c10020a021b06070c0b0f04030c0902090405160c03030203 69
    0x103001401202d00e0000100c0f4100e4882c102050440e8100d5010f00d05a8040003514100801c5040801da030181c10400b8100308801400907a07100400f5009407008920641c5004881c0803125400d1344c06803503402e000070540c0721410700d035062283c2c160b801c4001c2840200710641c03404103030101c40000140c1c068418100303a11180c031214030a4040e00d08201d81c549050050310104a4050041c0140c0d02049004429650002440c49004020f940890b0000a0181c2c0d140e03075205200c510010b401806201c00e0401c040c800c00fa03140d50f038030880c00942184d03147c980c0d803444505101c1740f400c23905d036002c000404410009401d00d00707811070a580031254051412078aa031801c42e80b00382000d26000003070348424800314680c08807a80c0000c0072001441c81c14061030252061b4400c0c07094900c40c2c1403018150185540c01003000d15014001071281c031102520146c2000d0712079a4030f080704030181e07021681040e00850740401600c1c0c14400c0130b4005a00d050b1500146001c0340e405000080c0c0691702909256010001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 945267634 1250 945266384 945266389
    0x30a020f060d060e04020a0f1d1003080307022116080906072906010e0102030304030e060d0c080108010605010905030613060b090f07030b030102091509040e0607091e0b070b06 77
    0x290362103201c0248080c01001e0f295152400c03030b50300441701607104518943d00095070340001c55003603042d600380c0481c1e80320020700c030503610001c414003510190007584a840008041104200654001c0030b443e800341c510820702200c0c2c00782d01002801102e107a84002c0045c6401c01541030001d80c401c81c0e200b842e251f15480403c000070313640d005141313001e030580e00d49480210107030040480c1c200e022010846200701e03079203502c00111101003005040074007584c410800300d00440d000f02007917802c1400080c2618984000f0441c0581500c25407040c600100e0640f00040c04265000e00800300908002e00e05565880d02d01000240e840300041c004851000c12800600180182e41d00714040c80f1402908000141c1000040c50310a400102c1c0d010000070316001103002d6a140600071103080610050921500c0390481d480284580d21551010754000d6441100c0c800c1c05034180440b03403140e8115220b1413045490329058003400c07070350490b0003048406060020300004060300181c48000e500503040c48940e0b640c0801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 945268884 1250 945267634 945267637
    0x5010906261c050c01241206091b080609030906121003050304030f1a1501111603060b0a0b0f120c211e04020307060509011205070f1d030a020f06 64
    0x32040c070240a24210b68101540003001045965048002046038070400c500c401400d100e00c000d01c4d200681510800c106581c0001101f18100c3d0164000254200d0700b60380d42c105810400c510000c00d22540c0001308640e5006000d001c0c1d0000d080005545041005400140c02e441441c4400c1e050121560100f402d04802c1610b2802031035016040340d503581e84905000e1602210342030103e404030442e14036501360002484140380106191540304210b030b41c0740720040d14800782000c41c40720705100b9111518108000c80c69a000258090640007034500641c6050114407982a0040b60b07100004010341c103804c01d91310382190f2010740c20420107401912890003065003442000440c1652160103003102c2d100d00100364030140909a416070b1041100714420340c3e25007103c0115000b03035140d0409001002818041c1004154041d01403500142d8001100700c0e4074203d440541340000061004030014200e40d42200e1641c5c9175600c1c0821495480800e14006640d591840e20002c3c0034400d4421a42780700d49980c030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 945270134 1250 945268884 945268903
    0x8120705070807031505011710022b0903080903070807030315080102070b06040b0a0f05060906040e0106050301081902030d0c0318170111030606040e1003140604060501090626 77
    0x30507070b400f450b603e040c448040107001d0407405140d46082c00005404090b500c074144440c421801519403105059100c81c000c0d007210f0005458042c0c0180c421144164000380101d190071040d5002882030311038200144403400003803000c0200d178420002080842c1c0c100080c0d41070705030b0610380440c0310301c05e481c1052401c4801d139002c0d6100c4d6001088013020840803e025030b11811047d90308010305064001000b108100c0d034860b881c4d500e40b8483c1c0034003103400c011004107000c0c1c0f0301514207807070b040d9070740d40941880009034410b00c0019004801448004400e002ea141c0c0483d02e10920001c183c45500020f4903101e07030554580c1448402030700c4004142c09001041421448050480702817a035800728072145a00c0321108981951070490905000200001507900408010740070034240f44c2040e0701e20490078000741c041c11015081d198000001401410f02c014a000d0400141546040a1400c84291001078115100503802e1090601c40603403506031403500120710f0080607036403e0710700e10580d0030802c110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 945271384 1250 945270134 945270149
    0x30213031104110714160b07380a0b0409110607060905010c0c0b181903030f06030606170106060f030207060b03060f0f01150f0e010203120411040e06010812070507 72
    0x200341001442170426030240c5e51703002e0000742e804014403141140c804604030300a1140c00c8405101c07510104582c0e903189252142c8000782d24103007400704050b014054005140110700c110b00d500422184031400e001340c1d0f03402d0750306440a2003100d44a035a1301500110a100c098050038011900e50107122460f00b240d880315420a00822001c400d034440203102c0b00a944040e81c50340c00c50710128254505400807103040e5509070002e407468038443e90b2100855910302c20305608054030707180c1e2000d01c035903284145401144036920000e002071801880703a40d44140030a84e000c3c40d0b4034024080102c60380202948403113000e5482d00503075a500e1864038030000d140e44c0d000203805102d8001040910b01c54900910f0240c50203c013090310a0381d0742e440d14199401c01c1e00e003c50000303c0d542d003001805801200c40c89401c51050054a081c4090311080c1c0f00d1210301110b0540b00702c540c0384070400c03403070910b4130440422044078000707048a0341c14850216174031040201c901404288c0045d1200611105200c03d00291281 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 945272634 1250 945271384 945271387
    0xa0f031a1306060f14030406110c060709061b030f030506060f030103060903030506061e0f1207021614030a0209040804080d020a050c0d0b040b0702011805010e060703021303110411 79
    0x1122400700801d03203800b4040120f008104420413450250702c159070800a0610014659034a40d0355083c003501a0000030701c00700c102400844410320703060094603c40c03035250351407030141d81c9400303030003030810301c0c0d1982015001c405501840c0c080390340300314040e41036005401c0110307003900c0d04030103d0140c0c41040e0a842d003001c408000881005030b41d170840e000460107a41c040c1b01540700c15080103600c1c032441d259450300035501ca00202100808601410700760b400201c919007032409884880303034010811281d0f20016080304142c2c0c040304441d00210000b0708008002c0800d441c440d031001c0ba6441c200c11340064800c054070000101084041011a0080d2080740280d6188c409042c80c0a5941c1c070780c01c02c00302c620303005400d1003607172034100720b80b4a03004a42c000382d040790a42c03a581c4070040d0007003000d40fa0400b15500c43d200c12200440c1d505403082c605128200001e51001881c80c9136003012405041c500405004200702d229818210302144c003513a403c110410b15950421300020000c081320720800200880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 945273884 1250 945272634 945272659
    0x80109081201140a14031207050f1e1009080c0d0f09090902060d091104061203020f01020306010917240f090c0913020f090406051b0a0f031a 62
    0x140c90141044949520040000381d88902075029a1048038151580010240c3c1c03013003104490509074401d0f07456001d0159244082101d140c1040c40e402040b003510031764003001c64921801c100304040e009401980c1a6800455490340100ea00c030640c01c2030018409842d40780c0c04061006030412105000720040c200e035049098018041c21600c804540b40001c0f412040c0b0014900b0040c1c05038491155004018074a40800d1082e040d004244101c401e0342d0b550102c07a48240540c843d8412355019011480c100441102035140082c81c002065003038543c664014001c0c00380a1341c0103600e0f10151400c642d8605403129180014070b160181c1c011000015481c4411442c0380c8043c0031000c0303405581c040c074840c2d401ea616103000c41d94480d81d49803039580102c201c1d000106001045000b004c403640c4010009211000401c000845002c4151402d460565070307207040c0081c2600344483c1040107007000c000d00d0304000b102503001d00b504191068507000c8c1511020000c406c010501c14141c3e01d40c1c00141400701400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 945275134 1250 945273884 945273893
    0x25050f0604050a1d0c040b12070c02040e1b0303120f06150f070c0b031b2a06100608010b070f30030f11181f030c020d0905090718080109 60
    0x10782a440362403244d000000440d07030048140c0222415142d80c8a42a8500034500301605130a80c0c008040c003040220150703403440165200e009111541c00154020107160f08100d010408200800a80a100703034000c0251000c0340105843e4540c0c06244050040b0441d965100400c0100d06039941180d641c540c00202540000d071003401800146014075850440161a103440049510050394500540304d1140060350400300c0c903000901c0003140c12500c0322051350032028411b10f540c82c10300700c0c100503400000410150380c00c03140b81c4070000c20f0701e440c04404952528402c500c1ca4402c900000c3d101032043e041e6441070011054004000015030984070a0010310040080b5001403080c92100010341808001c201c1007032039018207a200100204001c0c6000c8034450603002e405880c4084a1304002403001084040390442c180c0c41e61102c1d50380b8040f0344075808450003820403240c0801c14003031020901090090380c4aa202c1c41d9404900c50800c184203521030000c129007100242c0c810149076081c03525413800c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 945276384 1250 945275134 945275159
    0xf0f03011215021804111b100b04050f07080907031709090703020309070902130302090f0907050406060c0303020d24030516080d0503040c2625050f0604050a 69
    0xc2c012015a0103038a00380706082d0a074800c180702c400c00510050302842d41481c0c1540000e0041c1c4204481034500540c4d00c11606c071f8002105c1c0069040d800040103c460081c89018121114100b1a8100110701d45140c40170280341007d0550420840707c0790028000c95020000c500145410405513030314054500b80c0c03841c0303641c0164610340c00380b0085c0001c2889640030b4026a4012a21240030308645400c108a1100a411442200c151201070039000009601c0f400c1c03045000350000f0141351501c0c60911801c2d881c100866011902481c64904108181e5a012007441c40300d030341c140380141c7c2c2c8070241e000d10f00140084004500c4c0300d0400c1c550030f0201c03070b001c2d16601080300e116000b910000101c0c0002c455040c0540d00c43d50200f500f19540117a0294410702c0259806481014540d444540303030850751156280a0580c51034a8680e098540802e503010080c0011041000c040414100c0c605103000b9510b0900380b00b250700950105d8140041962100140c802610000d070500c0340155440001c4240c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 945277634 1250 945276384 945276419
    0x7050327040b030705150d020f04150c0807110f044229030103050a0308090115150c1719090f0e25080106090f080604080f0f0301 57
    0x1014034a8604000d090501070544160001005042e90920b04018040002c19101c9001000c0204200e4015a0212032025041218081e20817544450030b05440009900e00f02d034000b0203200c4c1c21040b041c0068900f104031082c0c150700040c440c80034024840440e4601d0110404640d000341028650300d0341e110072114644624500c0e07245402481c5100c034004802d071031140d508408401c95070501384400c3c40a42c03c5c0502d03550701c03010104210112084245035540080c1c0080300c141d00a0300f10703a07007071591080b00f80e600107181600030000c80c0744080c0c031000000841c0c4100c54a850b58414202030b4140234480185109801c0410700f8a40148540b20803c60b609c00107035154524500b0b0150b8075000d00c1744403807000765030084c040200c0351400d00c0140e104030400103260a2070b0001d03170030600d1440c01c030481c401e00c141901915a1002075040c10000341141d500da40007a00e140c07850b82d008004072040000d1454016401c105482d50311250ba00d0540403601c00c052a100c100c48000000003100f40e10a00046003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 945278884 1250 945277634 945277687
    0x30a022107081510020312060f03060103031107230f0a15031b03050402031906182105090102071802070813090605180708091f0b090105060903071208070503 69
    0xc0c3d0440030420802d680626032200041e4001d2203059902c403050312000e50003c000074104600d40030032600091500c0c41c00d800440004645440004000b00d04100b00350240040e00c15000e418400d620380f44100041d00b8010921590b10802e400c1600d0301c800e04844042c001580200c580d05044910107006410b0720b410348461408011080701c0ca480c42481000d01860b8000c01a1002e00303400321415420000350041551032596881c1550744003c080d1440550843c442c1002160490940c0f60760207103007035103d00f0310741804020002c0c5181da03030f804214141a50318800b44c0380682e00740486035034024001e9010050039440001421207441e00d40e155014221640710200b032110580701e9040c000010034620001402030002404140f0440c05a030540f544005040100c0754520b000000381182c01a2907145298041d54072010390102d810306e9030100340540b0080d104d040c42c040714480440c0d0b031480148591040300b0b0940c07880304104985041203510302c0342c004044944604800c01540c100c04a00e495450f03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 945280134 1250 945278884 945278911
    0x109350a020a020f120703080711100e030c0a210303020405060c030909160c02060313060f020c210f1c0c05181f0e120a0b06030d020a08030a02210708 66
    0x10301510f00401e4021713060b4403040c00342503220720b580e94440490304980700488044c60f00300d4040c042c68983d5210b01d80082403542d84e50103d84224010300d800d150b81c0d00141e502442c42d003103040c40b903043c00030382004c00c582028409201c0302039582800c03402030049401c51523026000040203501114008044c00322040122030844c0282c0716040b1210891000e80704a102007000c00454502602d843c0b00559480741c0840381040c00d1240541d1045c007111501869103034001d5021034074000e01802000900462848040ca00d2340003801c400c3d40b45043d00604016240c400c40000d04003807640c0000000c0050445041c1c0140400100e20f08043e01507048803410303403400709900c1c40405151602c4070740092848404034048a9a540840c001c0b5041c2114480c003d8100440981e00307000703041c0801180342030741d02421000d8030f1070801d0000c05041040311301c440c0e021035202c00114408203e40300c003225001a280c040050b030f40e00d440000e111001c075001c40c0070100078200808100410b600b0400e03082c440c0301c40c0000c1c1c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 945281384 1250 945280134 945280159
    0x2040e0f0f0117121b010203070809010510031505071b060f0506220c05040521060106020d051227010b09071e0c0204111c05090109350a020a02 63
    0x8411400e07000301c0c0c40b401540002982c1c0455601c4c4001401003103100c440154804141407007031070980c0d00680b80c10000550000801050703890070311410f030f0801110080c000f49146951a8850359100040c01400029036030340c04120500e002c1d2a226003c060324025000d4000014144900246200004e4100c8281004009211403406051200c1c03814500800d00280c10043c0e400c1070b000700412101d08051103010400850250780d074000c1111040c001d0502004008102c481103402c0103410790180055601a00cac07080c0310b040d08074087d41d100e10b8691174140d05a03079984040406c841d0192610383c0c0001c00d40d88100c050300c203040d001900325260681d800d0b405901c4a1070200c4400d92031050a0300035280d004070603030460b8400c00c07080e0100347c001000410701c02d0b00d102c43d1900035400b4200e18500c4e00703000241171003c0861402104d030320202d003600802c20754005890b4100114190702e400c426200c4034403800031444d0003950398070146040c03048106807a103203113000196543d004200160710030101350400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 945282634 1250 945281384 945281399
    0xd0f14071116060302033d0e0708010e0a0f05151c0203061501031b0206092401051c0f0c0501181503021e0f040e15030d0e030102040e0f0f01 62
    0x7140120b100301d6460007400c520740303003048000f90809404424150300c440c0b0f805801d034003a1100c24060004c8828001c1440d24090340340c1000140031303030203c442140f51404000b00c464000c4c2c8210304603450100402e41c50368034195100000c210504900c100540743c007052200d000b0300807014140740103056401c440ca058100a80c420049100e000c001d505921000000702d00e810f002034040c0d00742e64181804601841780c1400c200d4800e48150301400168440b10030044010010800641c0f02c0c0c2094011001000400e40ba0411404050003514041c100e9842a20b800189544158809a80003408884624901d181402c1080042d00c80c80d40091584000001e80b0342c603201e02101100c14210402c0c00d81c503000e080c164040d4005807102415074030a10700346406071300000010701e6104c0c400311000703a9940c10803031841741809007c3d200c0740c1481d80d040002c0009480014202c500c00300907081940a80044100081c068491500300509080da000c040c00356602d00d43c030324140200d00c890583e0707007140c0e00d503440c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 945283884 1250 945282634 945282643
    0xa060806030a151508160f061706010e04090b04020a050301020a0c170f0703050309010507030e030d0506060c0d03200306030d05092e0e100f050d0f140711 68
    0x122103500da0800076800b000079540d00c240d2452a03106140219240001409801ca08aa1540580c1d8a5048100c240000c480c11040300c4000c2d01103614003481d6070b801c4c140c004040303444190000000c00e0010b000b049160303010b00045850480000c0013030004451340d107003800d2040002d903030407030041c9020040440c2c0fa14060095450952684d910068012400d071284a0314142845481a000d00100011462440580c6c01030180c00d010340c986d940c2e82e0911081329421243c00602e0b0104251412021154412000c0220340c42401c07405000304954a0300d400003110352040e4041201144140119542180d81541100d601c21070038462410351800d4040742180b0302e10003110b03941e134107070002d000a40100c0e008001030606480c0141004100f40c2030102c044812001c1c2e2550b2114100c0314050002e03d1903400180301c01c140d40e06440001d4041311514019020440542d616010300001041c00821241c050380959442010003c0c280030108000510402e14602a502c0c44d000610030101110071031400503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 945285134 1250 945283884 945283891
    0x40c1809050712090c050301020304050d09050604060f050d0f0608010e1204050f10050f1b0d0c120507020d02040c0309031413060e01033b0c030303070f1106070903020a0608 76
    0x110b440012041c2d41c083d61009102210f812140300116840203c1c40e910709101035449644900014501e1074200c1c100580343d03c81542c0a00d00c2400104814006680c1c0081141880300c12400c1082c0c07a11814000d0402402e03c09280c00d245a00c0c044000600360b005400640380071079a07100fa02e4125544981c4c200640c0700b2070040940242100303044007100c0c10b245102030250169458440d0511845250342e0354540c1c400ea80c2610100210b4a41b51000c2c1c0b014010410100c07201c1c1806004440241e90b05240d0710b154a00360740a000010a1040954503404c10304c2002c290700130800c0048400c0d07000050010405204140c0002e20b0514036030110301020011201042c042d9086108680d1908000315003090907503980b1410580c40e002d80c03185510060954080000403800508050b019001d440414402c01d1900c280b501d90041a006140d42c4000c411250003044614080303c0c0060001d9054a080d80030050741d00003845010200190140e02445000070b480c4221508104550766040442c0d03001d0064 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 945286384 1250 945285134 945285137
    0x1c020715090506090907021002041e05030c130c0c020406090e06130506130201050d02030403081f0303080103231f06170309040b13021b100c0207090218040c18090507 73
    0x4000303845030ba10700303c200700d60b0120f210300c100c440398411040108c0c01d07038200390301c5007011000409451401400300140c010150501360001e2075121215400148154903003402c94491f10307903030002c050501e845140d41d00c0d401342c0c001c0c0c03051110079901c120201c0140070788090302800e0700825001c15445603000d180340030039a402500138413150300c0e220f42c90501503020311012410701004211f2109045114005184038a010f80c0b1080b0152a201104892007061896956008c001100c400c3c030002c1d030042d14a07415660801c1e0b00702e040181810200c1c086480d03580c1411142d100b41c040703000a040c807080160400800c9100b0a211881ea00c10400516480b02c41802d0100d0300140541441801d16603c1084160802841c074481140400d000e40201e074080d005e44c09940d08524040031105c0c10400030007015202c2c480c800c01000d10080c50007500d40156015000900350005003040d440c41000c81c0b02820008028030412155031219005020324000e106203201c0740103208800160b0301d0143c4229449003416 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 945287634 1250 945286384 945286387
    0x310606080420010203040306060905090c04020316081902040e18030a0e060a1806030603020103180308010608181203041a07050f0a0c0609110315160c051c020715090506 74
    0x5000c071140e02c5003441109046104c00d100020100b0028024000140544480010349041190010342004102da0060307001d1030042080c8114005138103110310328441c061074822407540b038800c1c505442501d00e06400d10321a0003c50081040c402c44001c1c60300820007442c0810700310a68448894032070248a204901080b515800d00d200d0381800c0d001414103410f5454000c13507003032107a61400003144040e04814002581c448090086503003611403005120032000904201c40b495503401014200c1c14042c01040160003804140003c41c1001c25008082c00441a2504400c1c81d1f141072260350400c54054804400040c10703038142805200d2054042d80d280d40d1080d14182e00d451200c8d03d00c1d4441c8004000b04000c59800c1c4010942604c24080418842c03014562150b0b6050100b51038034620701500c003102140b40c03042c404950444c007601d12185040c3d041032080340906003450750070144881040b031a4104075a0b44801102da0126010058600440c22900d001d684a0011031f1848040e00070290008030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 945288884 1250 945287634 945287663
    0x1101110109030e100c0c03120e030712120c140a0308060d050a080c07170f0705010f1b0809060c01050a0501081203192004030317060d0605063106060804 67
    0xc1840103804c0510050811841c80c540303590f28a2404c2003903910079031b0700c40010080401da240c0e03c800565000314007200104500340c01c01600801c50f08a08400810100808002000f418083c500c00c0111a07004015000c01024107a240c0781c4038110000120005100030303001038035500d4960380e00c5a82c00d4010300201542da03c0b0b83e9942c030156101c0004010907202d40030f40050391072003c21841540200441c041c010741c44600a09610305800c640203581408070812041348115031221010720b5440ca24000001303951800c8c1070207001485044c4086401c450002a206c50f072800542015010307420b96007040240d41c0e600c9a1180c0c031299941c2d64808405401c0001c101d01500c529991507244084950010b60f892800b001c20034045441240032088450200e8100145074102040790350080b980c2c0c0707242c070703880c0b4040000030888416440010442079a40700440c0c05512130a1184035010003440d030010b01e54182c0e02030511100c3d04040c140d0401d900380f40c40483c015202e40d000d1405030740d00804003400d81a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 945290134 1250 945288884 945288889
    0x408030913020f0c1c020304080d032007080a110c031203060a0e28020901050f07030e06030a0e0708014209020304060f050c2d0301031101110109030e 66
    0xe07809294507249400344070303229501000e80002d000c1606501d0050204100110803003810345c042540b00e00554006100c10001c826011540e800c0d81b400d9494001403101145007070080c01c0040009540e1010f00119144042110241c0204440141a1500c2d500a21511816540d030400300d000e4036059005444145020402d0001a50300441d0081c0381e020307156250070304403602c28011034503103400f41035a020758115988100f8005414506044d4198544207a5034000317042441407414581c0c0d0001c00140c260113052042034520401d650042109640e0309180610380080e0920005400341405030450008a400701407141c0100f810703126180508048851124580c3e1511401c4015255a41a52505080c488403d540c1014180003c0b005880742031500b011b030120340d060928076104900d030400344091a1988001c1c1d4101080018003544240020300c00610032140c24010b039003410002000100c20024010110440c003002070303030f60312a860000104c0501b40c0340c1c403410103804540181da0f880300d01d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 945291384 1250 945290134 945290149
    0x50a05070303060806132003121c0f0e0f0115090504170c15280f020c0303091e06131b0803070f0c0b040b180109030c06080402041104080309 62
    0x354000e04000a601e9a100103890600c1400c807440180c00d01c40421620412441c009016071581101000000032000c2d580402e40d20851480307003400040f0045502040d038002980402d440c1c64540c401404a1041503810a014082c100e400d0021401100c0043c40c0e01f520510400c41e0b025003c112081030140f5100c880801840302134020703501c5500400900c1d5102c40044014610340034600d000707003280d5582c00300c010360341c950140019101c0301e4041280520300003107403c0c0040c00d281c5072100040c2007a00720420802071080b041c3d051541c1c00080200000c00201080c05142c002d070952031402400014400e003501e4003011034207254404010300c40000400c41d040c07440c2840300604e42d0040d1b5820b855880003840c54201d1841154800b001030a00303010040d86444c094001c01509844234142410400f90b21010300504c4003e038040c0c8013400104013143c3c4111801c0c030045400414100c0d943e521018001d04509084800b64003840c00c0282c1404860b512000304c0c1d003210340000196040c07000000c200402d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 945292634 1250 945291384 945291397
    0x1506060a05041a0711040603020f0108090c0a030807020901060203030609040f020f3309010f0309060b060f0c0c01020a0c060c0302010b0603100305074e120e10050a05 73
    0x1081000d0101044120700f519405680a0000d9031542c2c035a40301c1e20f085150212440c00c064015403c050342000142c9030b0001c49181d40c0d03400d08040e8145c0da20844040d240040c104180d960088001600209002c001c500402109000362030250381e60780c035070134266524401500e005030840d0b0701100103004200811442c10f5420700c02040301ea0401d0001c400510303410550070b5220944e82152400c840004d04003441b003160520740710b0042c1c3c00d15030043e00280490908030303064014141c03549072600030400c1541c80a104008010075290315100f1a210340c0314140c000626440c0316200300341c0080030780d40c0009440b0300e28683c4546840209810100e0032110380310080e000305d080d5900d415005200c1d582e05805184140c5056446012091450805620305103160380304c0421204914400702d59018410080c2a4144440294080c0f100c41e0141500d080c024442040031000c60155043c0c04101d030b4201e000302c8140260345c9010200940404011a041041c41e5060104100700840800d8a00600c0a41107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 945293884 1250 945292634 945292637
    0x6080705031015110d03050c2b0509010203100f152f1c0309151d010c0e0a06210e03090406030b061005041409060d021e09091506060a 59
    0x400c03980e903401000006091400200100362902c0c071340895502c0400209680101c1481c082c002c5040c000c40460780c91145034200d4440324082000074220160202122034410390403c01000545040c0421900035001039500340740e850a072403c0044c01e510b107100c030542507900007183e000c025062850f0603a03a40e02c64103d920a40000a1454120846aa41c4440c03d01c140c120181c007071404c141103040ca00c200303c500108245403030480c0c601c0c089079481d030102120f0749406000140d844c440c02c0a0006000142c1c3c0c03104070540c2402000d904c015841075400704d4a14003070750554001390b00e601703055801c1810300000d00904241c0205281064240360800380c0030200400640b4580750301800454192407454005403501200c150910413030f81021a001e80d001c0100f4a0301038109414001c140160180d0000128403030240c1d0347c08200640d0307501054085941d4001e00d800d40728441c6601d0003101c520704040c854800d20324400094400900440c201401c0650b070200e040c060350342e00081200c20b4202c81c45440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 945295134 1250 945293884 945293911
    0x1d0604090b090724021207060b1009031110021f0b0d0305180108160c020307180e0706110712081603091415030406090f021302220608070503 62
    0xc082049401c0080c0101e20000c0a4007150f4107028248442e88030140080007509080c0daa80020b00d036010034000042e5001301c02d21942c5111301d0401d000504400e48640ea40808501c680c5602980c1100c0b0003004c0300c1c4106216640641c1450410034165010b20800d00540c1100f0942c002c07000c1501d80755a0111850200045ca48060754086202c010000004401240c0b0000388006480090f20070403ea8030400d04c1d00c07030381a1810070418201100b0610008c024408030006820841d5805c8c44800050100e0260000f526189901e0200103001580c02910441c040c015010032414403c0302004c110810180c0109244c1c0d28014003c2d1164041480c05c0c3c2c2c22071410b00c6503001c01c100c1012907694245c0a603948002007810700d680b88c1e800d040c0144403035109106804401d090400c42c2801d072640182c20560002c3c1580c001d0410b160308481c07404009501808000c1c6219500b0042e038054051400810354080039070303d0446940c0840ca1443c0211408241c24600180079103101d18019940300100c8056403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 945296384 1250 945295134 945295151
    0x60207050f09100b0d0b0909070b0415110307210f09120830012106020d0b0a0b04090c09030b040f030c0c0e1603050f010e092401090b030303011d0604 66
    0x4000c0d030450402501120348035130003001c4511f090f1400c1c0c3d801c201d410000e02100d900c1d0080082152045e4418908450401581003548030b0050072100552681601a240e13200f0742440c02c40300070b100215080b010103080c81410341580b4415001e0044c5d40005840e6110f01ca81030040c400704204150310700700c0d4002010810811f08402e4401040d14071043c1050b0305446210b028168045030342c050f0000002c0b82c0000b01e0016001580030309007211b0540007400160346400000516000d0444281c909400c140c0c259400112079800038014421a00c0d001001c0040c00f824090445407038945100c0074242c24a40f10210b03001c5010507492880e454428145001d09903055682e40042d1007055020024400404013040b10071160384890010b0002c00b450104272600e409400e0000480781801b0700c42c0300f03022074000103400780000c00200d01c410002c025400301d108003882d441c4090620902601c103001e4108031090803141070000c142d9040c0e42d00038042400303030307841d103418800360003002402e295200352242c216 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 945297634 1250 945296384 945296399
    0x6020f070807060e010e0a0302101d0a140105180304030204151205060f13050a060506011101021209070911030f070507060e0109061a0d140a05070608010609060207050f0910 76
    0x410310b8078801c0310007050b040b4081c140d07982158144500d4034650303042250013400003540850010000f00e8100e10008100c80c1c0300c6814003a05d840c2d40420221840f0b044a01021301585050280749034003560000d0059540d0340217000340007402542070240540c82441301b44018a00745c3c000360f50703440c010009218059611030100b5001d815003a0265030a0b08140140102000491a00c40c1c0c0200c181064095241c195a02d0b01e81c1d4600649002d82620365400205010744c0c0f00300740d040204210032009544a291107040014100740582d1613505a02c1156400160505940144a0101c030642c2059086036030b071701c0e00c44928400042c0107004100040010000040c154814039180f034104c40000254a121850300504854282080078812022a10003100c140d4500301d6010106502243c0c0c60900f501b131660380d604c0e0500904005026002d1050007085c507a5104041d1812560036949034100e07590340c0d8000340c1e2503a01e54081c0c82d400000384c079500c0c0064107105039010782020109000c80b1031aa601c034003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 945298884 1250 945297634 945297637
    0x40e0c150406170402090f09010605040e011a090c0a2d0e03150907050607031b0308070207150203040b0c1006060207091409060106211103010603050109020a0c06020f0708 75
    0x20940c40000105040c052a980600250203c5040f1840d8101c81c1c2003580014034050700051041c0813402c5c03044e0020b01078000c290012001084058070501003100a4007845018200b840d07542810800e104030038a042c3e180c0b01c04110300402070320390700c03d10f811541041100c0188440300d449842c1004245c40404003401603000313060741d160568424100090702402c06040c10049580c091920003200280710080c0d80105142080383c00803140240e8907520742c03400740c4280303405a040c0703100e295605e280d070310500d60490f9840e0f00c0380c0382507420750340c515032a80b50300010156900d408900680c000d220900c000070401000f45030a40322141242d10000c908402038041e603400340c00c8400160411401004820454001c12a5040001d441514035141c0070341100ea44100512810342002080c00d00d00d0801b6410f07845007009074042c84000e101d0200d0011080440f64820700c81e01c00041e10b01000051480c0c1030340309441d15440307182c0d0741d11510042600c44101039044001a03010803c0c0801c400f00c0001d080a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 945300134 1250 945298884 945298909
    0x160f1502030f07050a02070e130f051513080313030c02031f0e0a03050906130f081f050403020a03121104090605040c020c0604270609290a05040e0c 65
    0x19005681c918000c00c09046001001c0d1030703102840400e0209150464010612100360b444912089080d540c840c00c401c0d0074540030720800362100e070018650308280440030820b140c001a522540340c01ca5124800d403807244208055002d04403032400d0011812404070403004800d058000e1401e00300345c031240d400090901d0310900108000308040e9440480180c03c50151640c6013040d40050100c0002d80d0310042c003035100c0c0e5180346110324000140170048004505084000c0c040014400d20025220f9105a603034814003155102c9d14800801c110303046c144140a580c0c4110b0741540074051003441d669090310410000700704e80070304545a88031040001540d2001d840104101503010406520308000d100450321041004001c64000708000d00d055100d0034221421260050345109021258608000040ca25000411003c03402c0100c0024080440d821180d00404050b6044018501c000e60f034203040811011295003141020740200000e103040d41c81501e03030348061015175040300400e85c0085c00740c0c541e58 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 945301384 1250 945300134 945300173
    0x10e01121a070c14120a0503060406540c0c15090b090714010c050319030c30111605070f0e0108060c22180f050c160f 52
    0xa0109418005101e4003030804001c001d002e021603603681180217500340305040081062240010215106880b40d81c4820024403008180b0041c03200800002003d141d150302d8170308228404001c685503070164103030402030300c440300d003014000c1c02500740040c2c0094201e041003074040c4028081c44c600840d039209007180030070000e08000103003014203140c501d829910150420040794000081480300c80c082d420304103e290001d0030601c0d0400464a0700703034914414801208482d40401c150014015015000603500081c0d544a0158444012000801080d0400d4090241d6000301c0700d101d00080d210340c0109851000d0b980514a40180e48810070308090902c03004450f55404540108400c44a440c010000f4104607040c45441d0751506412070703038544000d05805403120340041d1680c01c040c240540343d52104060520441580c0d0750721820102e40f08080c03036403480b0710305000d00c0555407052480b03458412001000d815040c00c8801d40740031080c84003030381c084400c4d20100c28032001003292241c59240b43c0000c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 945302634 1250 945301384 945301397
    0x10309210f18060c020307030813060e0f150307090909110117070206150103060305250801090c0b0d0608031216030b180c0405060a0e0301050105030303010e01121a07 73
    0x30800081c250410400310350100b0846405407542040c2e060b40c020110b4040345001040044e40c0c0c000030307041000c0740d800205a4040080c442c0042c0303000c07111183c1212050b0300d0300320124030090144105407410408880d0302c000d46402090000e034000000d141c02c031a2514101c94169110302c0c001c0d0881b80b2800082c0e56000d0740a030080025030f801041010041c400400b0820103050448002c1d50340c0e44050304501007405c4206110783d01c1d902c40d5000034000c640210454205e203401071030344000b180c0c480c150501c42020307090001c00c440070140160070009a104403801e407100e151080000140c1c0181c410710b0034032038441e40000340103841000a0402c0da0220040800740c0c1c1095090b040311050600c1241003031500f009103040f030715580c03622440a4500c12150003091682e420384112300d20310958000c990b200d02c020500c00c4680e0b900820315481034a0980007044188d803610304240e500c0c0400d00c02c4122130780c1c0c0200184481611002c41c580000d02c00c07000065131078558074071586d42080072a0000c2c00201c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 945303884 1250 945302634 945302693
    0xb21012a0824130e12040815060103020d051503060f0106020309130609360f02100c20030708010b0a180207020301020339090418050307080316111902010309 69
    0x80a01200179440801d0b088186400d203001c5101341c8440c0d01c125401010103040d00020502c1c0d0080d0101c0b014200981020412481c10040c0b021107400c04070078460080c030514000429043c84110114181c401315001181132100364020070000c651860f55280125454040002d03060f8454040d9110802c4d40c040c20f0358002100204070880d048a840e40040c40d03c01d10020500800e08010901c00300b03d4060ba503000312140c4039001914074080400c1e0082408030200840c202201c3c3c44d240c0700400c00e5088041d00e120702da5803480107081e5450012031030342c845075012042241103141e004a4210b8104d60001604010305600042c1c02c82c3c0040b03031900040784c0d0380740c0b00c2080520070075260030400b02400e5046d0407404080e960082d280c0a10201c1e81c0c0100c6e91800c80040d03d00b90b407488055141d510008036030f5180041d1800000a030415518002c0300100f0f0051002c3d668090885d00d60300581181c024040c0003a4801d00000c3c41e01c0814040c1d0606541e1248040850310480d51816207960b6001c0d0083c0742c02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 945305134 1250 945303884 945303911
    0x1104060b12070c110d020111150132060a18090c0e091b09030307051c08060901030f02090a0b04020d0b09012102040b21012a082413 58
    0x7040100341d007080160300c0a00200086280050020009056800388a02c6082d880103075224015201c011602d44542c0b541c035844141c5010055059812004c1004174804184551480d444115505120b04102d080c3d111710881c104200541114852031030700707410121190508440140c040c0c0c0050400a481c0c03a414048203420040210f600c07541910618030a180c44500f02e20f0380b41401d1804000c20304000381c80025954104203660a01c2d070400107403050342ca090709000b2004810025480045900e50300020300510b040f0060720b040b290440c00350203415406500304107002c000240507100403a80d42c0d402d074020780c8491016050543d800100040c0d5451070108006020700142c0c003101099503180c900c19074820395a8206801542c0c16030300071811300321920014041c48032902600c0b560721003444c8809540801504400c40200c40b103942140c148a4900d82540d8a10222500c0c20101707100038085040d6049400201015441c0c0d0044100301851800019800300c0c92001526142501e0784207502281 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 945306384 1250 945305134 945305167
    0x1230402010e180a1113060521060901090506010203071202061902040812070c050306040c0f0b0f1b1c0f080105120a030c06060909140c01080c04050d1104060b 70
    0x1c011620414446101041c143c401c0600803d404003ca498000c82e20300f81c209981944c0c0381180030250300c2ca0705034844400030001d4004039441c881800503030720034603100346283c00554000d9102034920040e030f80c00c064102c00600740c0504018114401088064082004540c0d042103000d02a8040e21309814182d6a0300c24410611a19880a5204200810a090002030072100b03841b030006031a51a185036050460f0061116408203030903000b000100010030200f51442d90948010b00d81c1c4600080d16611078101c1406048540600198108103c03424040c503184030040b5840d00004480101c904500c00009410b1509501000b00d500328065109103900301e0462400f41030107844040170100c48040c91a82da14141c880a01070010002c401001e00a4681008001d003030245000d02c290210f91070300400d0100002e01c4060b10707000b00c0002408544c41084914015400001c030070341881e082004020044540003800c4500e00480c0000110b43d89881c0282c0004024020101c1c3d115480c0c0c0341da041c0c0d070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 945307634 1250 945306384 945306407
    0x301051207061b0201200f0d0912030c060209030a060b210c060c070905040515060907090b090d02090f15061c05131e23100207050123040201 62
    0x5500410700521005502c078201d048203180c010f04410f5107000300d00050b0b40c0c1c40d101c0965138460050351800c0352011500005c03902c59112100c4c0442e006440b00c48000c9410703d0381c0d8050040042c0e0484d8250b408248282100c0c00102c0c002d5100514105074200000d1402c0d001c4081220a00d80300d90f41c4043c01d1609998854045003000e0600011080704d000142e221410a4001445400c0104100b01288000c11240d805003414003c200402d04050601507956110103001c82c117003660440014081d8244442018040d411f1505c4030070090707062913880b110350b80180c211036401ca11902c134032a0140c0c0e1400005030041c403d105101d8428208010015401c2404501c0b450090208001250750780c990340d98030001106092074006050f488001c00c2441c520f21451005d0134508481e020590000c54001e4031041c1d0910880340c006103001084184220090100300c0c8108075040b212003010350b0f05103a001056164422800001c0901c0380c0d00058103002c0741680d0502166503843e003040115600443c0c140311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 945308884 1250 945307634 945307669
    0xb1228170901091e05130b03120a02012d0c1d010e030c2706030a080d021e0403050d030b09100509061c050604060c0302120703090f140f1209030d140f0d02030105 71
    0x2c0d45600c5000302c2d0b41e403410074022880007500001d0017840c2b903100303500c0104035100e0548051002590082c041110520b601c0441550341e1402c1b40040c807081c041d400f81c0031052000d15100c11001140c00055480c00c0c0d240c15030311b03010b0117882400e2030301e56580b003080c401540403500340f15040280d82c01113943e100300041c41140a03512110340080071400d10000c1e10340b08004c2600c00f42c0e6543c0741c17442c2000004059082d2070346038400401c0c0441082000705980d40f05103c159030412045968008000d00341c03405861140120103944414001400d055044540c050030151484001010903c000400c91003050000c0c1ca46411070402d00013000302d18014240186054a0190b00380a942c500d4030182110107000c0d5018150754410701c804008412a00b100f44940045440410010200078551a4080d8100203c0c95002e0f00c00c12504040e0110241d45104901800809000011840646080c40324402112340d400c42800500c003415400b40c001c0014038000071000d03803607525000601040c0f2021081245 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 945310134 1250 945308884 945308891
    0x19150306110a081f03082a0615041a03100e0d02070308040e061c030504060201060e010b07080a091e09050a140a020a030b1228170901091e0513 63
    0x40e1a560000c46207070001002002c0302d007500c440c510a10a5000341740d000405507480030513404244001d0140340140d4000e8180304030344c98001541004c1d00e412084529240b200c8403c110b1032068140f66205408180c56034a040c481009080002131500b182d0a01804d60903444a05500c5031b2403050100840c0785855000400f240e078110307a20455036002d075001c1c061000035484002082941c070364502039614031180702480880c1c1b03400c1c100200300c0c0c1d000d07000d100050340c00e0440c00502d000c2e11810440c1240c01c1191a40d040c903d8583d41c480039584400556000c02000c2d82c800f2450482c8941c1c0351101c01e04602e0604822441c15035184169200208114006450f0034098040d0000310600c4962007440c001c1c005a4030144000306a004001048078150000700d003000d404070ac1a00002c0b2400c18040f81c03100c021944500304503810384038a030842c0c010075551200a401558001e80c001030910340e00141802c0100d01c1d01c0d11903075000d5104005e942603408012200812160520002010500055002c1403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 945311384 1250 945310134 945310147
    0x314070f06090b07021314040c0321050906091909050412030606020307020d030306090906050121020105040312020a0f08090a08120909100306090b15010e01080106081915030611 78
    0x2c1d8203900030608061b0160400c2c08403140740c0c07292503000b41d04961b01039204610a0500e8140404901124002107580d1500320441481d41146040b68448000b1503a403a41d2804528900303114084d000800718940148400c802112585140c00c42c16018160800000500c4d00c0d00c7c1c1081d00390544511041004d00d0f18205e01800f0481d07001c0101d503140c2d601a514049114082d240450060041d0b80c00202c406181259034001c03c90103801c154103c0d00780a840b50307000e20008506200c0c112071640c1c000c0c08560104070810004140312414140320b401401551040c000c95100c0d00628001d94904550390600020003403113038640001d07200e0203005001c0003052452400300b12407606118452185200b03400e00780000b01c114003002c400c0c0300a558803a00c00c0c0062001441c1003c5170101c281c404840607a4810f0300c070011944070f8035607405060320507501d0040907440c10f001550b148401820410003400406420118000107000b001d41968900c3d80d007290051030350034540102d40d2400c403641c0d160b5000b007162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 945312634 1250 945311384 945311399
    0x4050604030f08100627060c0309080c010c020d050c220c02060f180319020303061509060d02030903090a030308010807080a172d07021c02010c03030e01060314070f0609 74
    0x41030565085003060000c154280680c1800e20707600c01b6080b000540c02507000700d44076602c403041178a246e119440d080304c4240c4855415440700c442d400c5060001c0c42900901016280000c2c082000c41d0240042c0c40800000c140403e0903022a8100c00c541032807280a00151102a03118079a0140c0707a91019001e1800e0000700e0020900c0e024200903940320503600d9909808505004a80b0070300381900510340800301c01e200294a0780c1048a40c03911450500d0030fa401d407100058119201030500401b680d180031030924aa90080d0005010300c0e40d64401448080200d031540120710b070185029481d1002203603d0702e040303145002442e402c10ba100347c002035043c50003e04280744070405003080c031401c1c079201c10283d00703599006001454a070100110240c1100e20069880c0000c20b40a03000766412080e0841c0c2441c10300c01021030360002400a5100807441d03000c07078841e5000440b00420400041211562502d440c280c07802160007621080d0400d40007001307601c0c01c009410000780038500f040c0c0c901c945022807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 945313884 1250 945312634 945312661
    0x30114060c0607200a12080105030303190203070909140117010c0912081903050f070309031d010302040504020c030c160503120708120a1b020c0a1a04030b04050604030f08 75
    0x80c00c092003052100a44804241c20409041c044400b085843d05051030400c43d0a182d0207001400102c7d0300b6a001044078100401100d1113180310701080e030203580081815000940c002030105081205014011942130501d0086030b8188050345082003d550405d1a40d0301d036051882c0030341110740c0c580701c860002c1e40e4010103213008a905500ca541c500040c0d07820030030b07940d2240ea1500c0e5542441d9454442806400d1350115000f5003603004940c03070680e40c10074160b04031210a00046d01007043c1c015025220541816441001e04061401500727041da1880441c0c2642c00074484060301e40c02c0400c040d0010707401004501d00e6140544a5a4105883d100c042504c0308007a041c40c20080d40b0028040041c00660030403030b90000900c0491046034548102820024000f1078800610ba420f00448103040910014406080c84c0d401800700ba41e15150602c1158080039604040c2d2070f412003800000007099a2103030282c070503070044014201515051070020409800d501190080c0b041c15018003150081408 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 945315134 1250 945313884 945313891
    0x50609070c060e010b0603070206070e0f011205090a14151302100c0302030f030403090311041b050a120207080901080c040b040b0a020f2d0723120d05030114060c06 72
    0x1100041d10311103605003d40940420310445801070400018803030103540c0016114420300d807030b94540080000900030407440404040c81e031400200c15001500c254405984250b41100201c3c0c1112031014442e507664050001b01b11840002da00004030000b001c001021410f6440851040e03000640d910f02d50005101341800407800c0200401807080508041c02001129580c400a03418107403a45040c2ca001403140038180030032501c51310030740c40c480d42038105402442d00d000c8128004c0c000b40060402c0848081e0070454004081202e000354070400ea0100344010b1070303c1801040303016a81c4a005001400c0d015000d41000281d0200300000c004c80c03005401540c0a03100020485640c4908240c4220b02c1c00010a001820030f0103010b4203c0c800c9a00030a4449408005840004680000200300b517101d40051041005201074880896060750b5009000c41103014001c010700b480501201156180c80300040400c0f0110300c1c0000103101104a031841101401d00071140d1340d245c58a80441076031a0603018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 945316384 1250 945315134 945315143
    0x300504080a06111c0b040b1c20220506010903030905040c170702010c021b0a030807051f1a04060b120a0209100201090c12050d050705031615050609070c 67
    0x343c064140c4103a112046581511030000007509440c1e00d003203030304001c11082c0c85030740c825031170040e0120a5040c40b46421059554070b003040c0c01e03400c00750f8694800d1141388011003004400c1c510407554844c0e490084040d0403e06007000306000b900358080a500300e420140890f41402600101040000d40c0010134005541d8169001f28080d080351609a9101004040c20004c84c0070f00f030100f0000950540c0704440300c000070380c00c556141c07020a1806103068024507100c0d0308034440740c034184042aa108002c1039458842d2080b81c943c00a00045021100038030347c810302c00d0390746a08084d40761402c0001c01001010040354100101407400191300154802d003803154010644480000d8101c92503907055400820001d0001410414001002070007486685021240300c40e2088010403c8841504140e40d6140c2c003c00900d0301d112410001e0703032141c0100785c00f00c1c0c0706d1104002507a0042404d030303403c40f46a0302c03070594a1903020f50020010140d61000342401e014062000030051311030b81c0140c1c4003048a401c1f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 945317634 1250 945316384 945316391
    0x10608040f110604030204060306021e03010f061d06030f0405101e051b0c0a0b090c06041701061d07030f1415060403060c05030f01090203130206090d300504080a06 72
    0x80b074002c54841d008035800a0350061400f070001080c000a074004202c1c1520001c560b0003151101079018405000a0203039818010a03881c00344940f50003078080340070f0454603000c020f84000b254400100103900c121520003e200350903080c4810800704001078013401c0300c64082803041c00104602d09511040c190314000c0c05030381764004240b402400c0c400071240c2c405080101603569100c000015948c0d545403904880350f14251000412000020808020a1a00814143c541454400110001a152081390700350355079407440001d0341e500d4541c1d0070385150100075031001c00d8036001c1030140451f940b40071003180c8a8101180200403806c92100d09a110103140c02d60410745401d40b0119541d400380c3c0e040182100e143c00340d0440d0417038005004d91700c02e005107508206503a0701c0e507407450705900050741d0f0141d0b10703076582161380300514010000d00300036000607040740b40440d05a101c0c40440622801c80e00c045808181e45004621a00341e0152038010701030401c689441d1508000c40c0c1d80b049680c0d40601003555 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 945318884 1250 945317634 945317663
    0x623032d0c0c12040b030109151d01051e1f020106030b0c040f05010c03021b040e0a030c02040f0c09051201110a121a1806010e0d1a010608040f 63
    0x101881080049010603081181c6040c004420a039801544800700368441e10303400003000307046003040f1010746580245907410343c0d2901807c800601344d61710205072581d400401c0440c01e0620540910041601d00383d100480354541002d111084000380341d81e16404001c664200001e4882c10707030b45e54501842c0050301c41104008034040340100744581004111443c40b4080c0104109090054010307100d601441290441d030300c90055910030048280100540c0105c1440441c281d030b039801d01c0380c40b02000361001c114114800b03512428680342e141c040b004101544240415410310f40f0548200c3c02c005a0b00300b0001001c4400a46202d4403441010711640710410b00b04070454080d00000c41c00c01c071a54825031140146680540b4006000d000c0328181840e0110b65041d40d080250026a030781030207410500c0645503c2810100c00000400c0d4505000499402e0805925029000048140a070410001c80c1c0c0304020700c0d0039aa101030380f0070b90400056009010210760b001d40301c0707000181c0c010021644c201e0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 945320134 1250 945318884 945318931
    0x70201080711100b0a0f0f150c021c030908011104030609050106090c08012301050708090117011403010e0307110d050c0a0e0f10030c05060c0102090a0807062303 71
    0x8420405400c481d01482c0500011403580e070300301d030f90060382c205c1c3c1c2c2540058583c218062990414458180140900c030710810404211002d1211035000a25010701410f0080e0080755515184291030380c4950540d51010080c582d105860798050a030f4075000740111400b4042c5429540100d00010300790303503518803441007002000d43c8514010500c0460038042c407204400d01612106091040c400403090507103924814a41e112007000e0380303000503110f240c00c1012070784483d581c541005801da8188a0a40c0a84207090710f242d803c03070b00030700800c0412840d5242c240285403e4801510390441c50f913000340001800a448003501400401d400d403142069129a03052143c40e240c440f007921b54114410031000700b102c0b00d0000c5158030620001e030589841d41c684180c0f90310341103414070010744003100c2020f061210b40b07007480040401c0d58028001504000028000076403001866019900b1079010840400060340c106500c10b49003000e88146c101d50084200c0800c8052000411243c81c00114038000075013903 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 945321384 1250 945320134 945320147
    0x5010906050d140114210a080d091502030610050304170708070f050d030c020c0f060a030b041e0606020a08040b0703170901050f13021e0f0607060209090601050c030702010807 77
    0x144031400d0f4240c1c0c65070750344103088140519020060260a600c0358241e44071055804c00c81908140200806503221a6241c0d01d6160f001500702d0601c0d00c0c0c13510041c0300403c0b10040da0503820f0000140050b81d9041800402440300207c10034442405818001c01000c13950054101c0d494138401d440c400d07a10354041ca0320740628464250000c1032060324114010511800080070410b01c20903807001c00c17003001d05000907030355004006461503010035841c503d415142040b40140000c524541004280c00c5140300004d41580e45403182888022200f14000c00c010f00207002d40c3c00141014005812801034645458100d0f01c918007591230a0100010070380c003010310980f000242c5d1100710a1078040e60070003450190180005964201031403110b24040740304241040103038403c441d070040009003c00000300301c20a02c061074003070555009580201c554140e8444c0d000034000644508001030f0348007004c40c10001e00d0311001c1d00f86410400e050101080d40c04001088906241e024200031556139a14076049954 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 945322634 1250 945321384 945321401
    0x903010902060f0901090b03090307060c091205062d040807050a0b0c1801020c301c08010906050a030605060d0c14041413030f0507050d090806090705010906050d 71
    0x800400a800d11040c40702d04040c0804d044240c1c0d03030032181c50759160300c010640000e449030940c680007041510300144003a800b40c1d0a000c0e00d42800701b0034554401c6a09031040c1101ca0035100c42c0c00c2241000004101c440c01149180960041050074240e2002e5051408400800c01803e01d28000350810a1010800076100c141d90b00641c990304514044210f04580e4000040d28000c0080c420024011580040f40340c0d01c0300040074003100003100360a001d11501425854003a0400d40c03a01c0002003507032900744407601200c10302c2040a114401c0110300180354802c140d02055802e4500342d824000c0b540c6905001d000c40760082d801003440d896078030000c0c00d900da401c2c00060a40100f2400081c0644010410080100c0c0403030702040f4514100c1400300c45030704102d94688403141014641000240106007010f580209440c1843c105040c1d076031800e260090b003c181002080e01d01408200c400d108100d40c0380d0100180d070103488141d14102c00038240071000e0041c0010301c000401c8001c05105283d220810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 945323741 1107 945322634 945322639
    0xa050c0c010801230a0509010611100e0a0b071e02010c02070b070b0615070605130b070e0310020f0c1e190b0714070807030206011e0303090b0903010902 67
    0x503070111285135065100322a180d0100d02c9450320928035002c0d1000382c40381c1d418110300c4101d0524006603044101c80c103e007014202c507402c15000c60060380440e4040405141510b40c0c90050302c1c1d203044d0040d80a5408160b961280400f54150410820071a03241c0035a0b480b540c803624401803903c0fa02c03401408041e08440498100e0511107806900c058042c50628240007899480809a8006481c02cce180c880071041c1400c2841000700340b031900000141840440d4590384404a0f40b6941d03210b4020200507030108101c00002c2442e0100c2c0c0700040000151a014407455180c4410a200e00b10341c0c00040c840c1d80e00700103280e8982041c0410301c0d500308503804215959200100e5101902e00811000e041080c072055002542c0d1002808100b40b20340c01500700b40d81054a1040500843c40070490340c8464100104082600484098140d0300315981003580c1e1b96078400483d01501559000030b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 945143884 945323741 := by
  have h0 := BRFrame.cov_init 945143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 945143884 ≤ n) (h2 : n < 945323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
