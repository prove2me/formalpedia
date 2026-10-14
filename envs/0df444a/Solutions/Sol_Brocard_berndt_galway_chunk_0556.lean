-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0556
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:25:39.989259+00:00
-- url     : https://prove2.me/submissions/86f55a00-bdce-45e8-8b80-8b7a6d9f8b9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 99820143 ≤ n < 100000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 99821393 1250 99820143 99820169
    0x30616020610080727020a020a0b070302040f031b0305070f050f01110a0b0402030708070902030f010e01030305070b0c041a0a120b01142a030703030c0503100b0313120306 75
    0x80302c564900440500841049030840c0e03100b000b9285810340000c49807850302036080440442811140102e030414903640d0096041001000108a4000641a440181803c01714242420116245103402080c00014480304201d40b4404840114004801c011980003013210304250b120b1442501d01d507028403c542c003c8004d442d62101541c0913660000310000c41800818003c6580d440d401401600130f0301c160382501031a103000c200104c0900010300500005800507075242005506244c1c0d0300b10580c84002c03d0b69441c1e0050000aa004085541c500e4000c200324000c0d8075000c090710028842c1d58031407840d980007440c9000c1514020b0000c5c18101400b03861300002007414041c0c1c40140d503a40780c481130000326404220807000c0e60400c0642610102100e0a2107412148122001d0188181955912950007c12100200b40e810f0082c0d070b039484402d02d802c5003141400d0300c07003203100c01c0300e8080e03c801c0f040040700080c0742a4000c40e90205064100c403000a81c62000d68000c2c008100500130180c24040b9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 99822643 1250 99821393 99821401
    0x2060903030705071502061b0a0810050604090902011202030f0103080309070509010609090c0207060203191202070b011505071a07210f151203141b07050a090e06010302010305150306160206 83
    0x10003c82548480d140303552306241c640007150459107540020202d00710340444510104080c0c48032006030000d407540711360000b42002c0703900000d0840e20a140b010640280104108842540e00d40d80b1181140e038488c440301d880e80c0700e5803003039400e14240350002d03a0011002c4000040c09039000d10308000311410365004005100920b5000c81c2c50325428000d100c090390041014400c070103032845c2d41c9400181c052400c3c944a0341260390050507a80400c40640d1030310100401030145d000b4205c40542c01c03080f1400c1c001c1c0b41c41840e59441c0340f0091950900801440e090002030051805014200e25410020120303c0790b02c0c108104101c01013060300803841d12141b400120350110411a00b0070000d441c2d1112180018854594088500d015030400b450180caa0a200a10000d030713481e942d0820800c404c6007d003002c2410320b020302c05400c219500600303d9604144801c850340780007040b45415a9020300c0c02040750303074481100d030320245698500140c01d441008200078104800c00c03c40e018800440c1c0c01d80b021034031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 99823893 1250 99822643 99822661
    0xf010309020307142106040201030b0603150108040606051c0c0602071a0c0f03030901090204050601030c0c022e05030a0e0d02102019090504060b04030206090303070507150206 77
    0x500044020b4142d4003040c810300040107610101e00640300020400c0055405000c030084600d0044a03810f880c2da0f00c50030034001107613054054000350280c1943c42078110314144088e004041c40c001d11241c14400310724041014044140c20090281901900c2c112a0b94102d070461030180c1081c01b0309448402030468003089407072001c10428211049090210503840f84042e410019a0099100014510907441440c81040082c409184030b040da484c000074441c10107005100503510024000c030704151030046c07115512504148484500b5070141c9203581902070310b01c001400c0714245401d1503140b5210354041e80341540c1c0040154410f401c180701c1401209a000156a5203501d00051480540c001040b405030b10b405c6507001c10040c9014400b1801000500e011440c12a4404961600ca2880300700000d54010b0704024644028441680c0401407145490003e000a0066000c003d01c1110005100122503400300291806560401c09580d95656101000c1c1d208445989900015001d2200092285a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 99825143 1250 99823893 99823901
    0xd0218090a053d060504060f17010303030e0106030822050d0302060429040303020a020609060c0a030902030c120f0712120e2103030702010f0207021810090203150f0103 74
    0x507004441001c2d0850a0801d00c010740d82c1400010742034422200b10b0f6140c9107203031842c100040c4541e4503940d0f81c403800e0420081c00000400b41c0301050060b160411044a042d1305403441c112078061800144100d91210000d01600181d40040d01c0d07140f0210306514503081c601e201e250566400d14140445a90358824030404046140d000780158000c0320000b000328601001c01d15075605c1c0020041540303c0f02c0310000c2034641040d541580020f07070205c3c5499800e5010004684c0000da40c01c02800c9900c2c0420004c1d0752445421344446c20551100c0740340003151400c1011400d1628028141410004184800c43d0b54510101c524081485031340400034001910001500110360864030114070f01510340f200b80d9585070000761042e04100c0000d203d104002c00000ea006d40024440040c566908185400909542c010780446020504c10000000140c0d1190480011400142212102d42e07455a0003001003c0440d0703c820b450314000004c00080c001440381c07031045580116880c801e01005000114215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 99826393 1250 99825143 99825151
    0x50f07020f06100b03060a0305010509010b0f120a03030c0504052211030f0406090c03060f05010602071e09151a040f0e06131a060c01090b061012110d0218090a05 71
    0x200030340d09400c4c41010b00f248000c660081d40904040f0103659aaa40c450844004490048050b503480000340e0503071600d54000c060720301080710500c0d207100041100c16100d41038214014140755498a840304d09501410654005140050107041e10600d106044840c080014008011852520880d0b028040c0c02c0000d4900404841c42d042c586555140c1d90000140396951054424460521002000604601034110170400718080810740b5494004082e00e000348071f070010703110351030000b00c40480392146210400844202550200b031000ca14000030510980c5030308410006000314107100380039408400180212801260300d1004c0d070740d9074072004001c2c400503501c0c01c1d84994516003a0001c0b800a81120340c40011a241c003c0c1491020720005650360f0004111036056510340742080d0500c105409815404401641e4500c80301c0740c6460300030110442940b421000a90b142c8010300c4081c041b81c2078501035441810115545c0c42101a41c990301e201d91694248aa03002038001000207503140281c07409 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 99827643 1250 99826393 99826411
    0x10140a0f021207050a020c0a0902091e0f04180c0618050f0612041a011206050105030109020303070f050f1002030f100305031903020721020609010b09070e010c06050f07020f06 77
    0x8940f40c40b801111030380d21105110b0118818507921840c240e450102c0c540041ca0407100040c0d0f1201c4000038844a005610801070320b80212000003061a1100e25600c1d010900071200029817583c00d8042296040003110007030161952414045465034219441182080e2400609802c0d1941c460811803584030002d0b02c50340000d0b05100c14140c50504040081d00103101d01000117070074941c08000c04622109034480441c92402000000503c80c02d8402e032130145c2401c1d4000d001155542c0c022035600c0c4241e074002454410345520030818044240403107003400d0011800da40e060302d00c0d44d01e83c1c0069041550a030007809160310214000207505611300c0100e82d4030001a50504154550344c0041403580440c070070505800b0040a0002031020700c014030300792940c0240a58030585c002000745004401860118240e15100e48d041c01c1365110b04482e680203240d80382540c000c1c010348004039080500341200401c400e003883e003880b00300d00b82c007502503220741e06981c202c0e101c0110489505985031015210821 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 99828893 1250 99827643 99827677
    0xa061b080a050613020703031803030204090b0d0803040b040c1a0406030e0f1e12070804142421090c030d02010606050d05060325031506030503030f06010210140a0f02 73
    0x8a132207420340181c5038040c042d04000501c80302007141c3c0400400071580403800641d000038240074400d0184202c1c41e00d40029100340b5a03c2c82c9643e160320b00d03840090301c0648080811740006003084104440304002d4001d0641500003400346841034601d030b812501074400031a041100b01041c8080c005607085417161401c00500340f455030300396884505071582c018890240504003481c24000390740e10003068043e1003458026595071420300100304070180009903c0c444c6030401402c0710286490b18200030341586820300584d80d0b503400320700081c2c24014074150705000c400307550400c040350202040241c402c02c4c066054410010b61010102d080b00c860b1300526000c58000d024040481003541c0c4070a1780010040d08540c15102e8540f803024012458144040c82c000d00f0030418020089090030003140d80508a40a01c01e072411a130f81c0503141c0c00300070940080d4108c0383c80000d0b141d81c07003080102c1008101d0340c01001580f110b040c030010345031011110445034905014a809180342e003803003100d08021140e45059 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 99830143 1250 99828893 99828919
    0x30619051c12050c0d0815060a08161803030809010207060603060c020609030a020d0e0d020613080124030803070c080d020909100f061808030a20070303080109020c0a061b080a0506 79
    0x1990004000d003e405500c8490410000e07c8c0d21411300400390b0109030f03190b81503580b524141c0340000d64075560707482c000c01c001d042d9100b8403400d11a840c00c0503240d050425940cbc42d81e4400c0100c1c024091140c1c050501410324000205010b443c1c1c1c0030300b41046d880e40c00d9800c1a80c410b021030b130741c9204141e0b0032030041e803010285e030102c0740c421800550602e070020420641d840450b000140145c00c44080c0344801298280d08002c0f0303c609204038010905410b401032215601082e40c1d80440001f44000703001c0300c1000000510051213141007869040c0d101d01255110444110108000c7d00000d0303201d8056120180070a081d2600d13417024034111111201010f803854140642201c240f2900c0c2405040d030700503c000465807407414005025004002d980c3c010aa090003c0c800312070a50040104840d41c00400061001c69400007030903065541001c0e02690f00c201c031201c602e180c4021954044c220a141801504803e602407800260f64191590b8030409034650520f000e0031513009644803640000030300203103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 99831393 1250 99830143 99830147
    0xb010b0d0207020d050c01020d09030201090314010e0f061006080c030a1d03030103030c020a0b0711060309070b03090c0415120611040915030b100605030619051c12050c0d 75
    0x2880e8118a028015003800c050b80e01003080b01001007011100340d00170f94034101072035a04200c10081c5a2682c03505010142c555000a400c03c1001d0102a210800000c004404845c00350402c44203c0c810008844a007414060995100c00e81030b140c0451000000500150b01486401883d001e260403140d0750f8030b5a00c0d02c200c190002c20300360b4085440c1c80c20b00084001540010700246000318000c1d1500280541c8c140304010401d8440e40002484c3c3c1014058400460121044106660004c0d41d1a546d01e0312002d14183c90103c560b844a03003802400400c1021f10217000c10010b041400643c1c041c0615800c0c1120006508868010410520000d04034103002c9100c0340c000654030580c03a0000f6140c140c032104118183c0d0095040c83c203000038221010010403052800550b440350b010380840304240c2c03c10f040207041388005800207110740381c0172080c400d004482d1000d410050000400d200210020303d80c12950241c036941c0c2c1a120000722500d402d14050240b01125003410741e4101400c050b80800c401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 99832643 1250 99831393 99831397
    0x31203040201020c060c0d0e040203070c020f01110307060e0c040e060a020a05070c0602060412020106050109030b0a111c0c0f050306040f09150e3d0b06040902071a01030b010b 77
    0x82a4114481d50f042118103031150001010300030402e0000c0e0440c01d1410358080d052390b000150050240e40704004108040f980702a44003885a811144210111a40300048130b83c1081607154003c01d0000142d21400c101e1503502101100d03000d002603898000701c4000700011145240743d440c40540100300091800e4000b84d00406040c4030506041c0d0420b005501c903003500301d145030883e402690107003013400148161604007401c46c10040c40203010a90800300000c064148903c002030074640030401181c00c0c0c00b0b842d082100044252011981c0f191590100102c03401d0910b500c10030f5062031b25003600a0148030712220354a00504d5101d071490b54482800340700003044c180f0320480419a83d1040140016910030030300440001c40e15001c908070040901701f40c200055109515028000181261031091851950307411803849001c402010001c5945d50002078540703245084d03408140094007044c07003001136020b440013a000310b64220300300c0c400040c00d400c44802070002038070740d445c4403004100304044040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 99833893 1250 99832643 99832651
    0x9160503041b091820060901260a05041401060e01060f0c05010515010e0a080d0509030304030b040c030c0b03060f040e03040f140315070c02091b0304140d02030405031203 75
    0x2c082c0c000341e81d403480c0410448540d540781c00322446164803a5000e112050395a02440030021400039010881c41d000140c052040000c0380c2d060010b100c410040445140e0074032400280e08000740141850314080c000c00400c81102d0480e8900c12141c0c044040c004140700d0401034031010004200daa0342481d1003070b02c0b403c2414000c0c604214121054400165082c024103001f981d642014000d0940d184001400c07181d84161200c1c0140000c0c032003000300c4030000900c01008086420000d580e5a034000200f0305502c102d0300068151041d034000e02080002c0b2081403002c9138010745680710541d848880a00391488282c80295101300da21018086a1806510800999403402c003200d14180e0750300442c0c0c42601440d481400600301000c80454281028008403403801c090304041055031900c900042c0050441ca20083c1c01100c051000a2414403040c2488540000203c002d5440b45418904020714410201a600640c0034641000c06224000005c1c0d5058034070090103405014001c1100c0e08a40e00018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 99835143 1250 99833893 99833933
    0x1060f0c030309080f13150302160602030a060e04050609010f09020d030e0a170105061e0105030a0b0a0509011e050108010b090d061107050f0c090105130c11010203150916050304 78
    0x114510259010080049450f040c410b6502c840c03070040840c031f9980300c05444505144c0100241d8002410b400601d0a18507400308006840c2c0c0c545040150040040760000d400324650801030009021001030524070440c1c8400080c040e0806201c8400b09485107400c009400418440302c0c540000d009120000c82d280c8003811181d0aa40e07595064034039160112010141c41c0d6460040c040c050904001c0c06803c9141c5405055034041032a0000302244001040902140c0e690080c9010a0f6112507809000703003801040e804055840f80f2140d07011807000c01d5086c105d86841040042c01794001c100040c101e03051950040d042c6103d0009200c8002c00d02d01d42160110f80d40d0b040d00620482040160030000e0049008100320f800300100ea40c07608000c2c1140311b102d4144000100281d56030b2215461043e080a6804540108030311000e447e0011401c0303415110f54004000c100183c1c200c10000150b448040312906c15544494660440200c6800c1282c1d001039410070000c0c1c007040024024000c0d04081c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 99836393 1250 99835143 99835147
    0x2010c110316060801080616080c0c1002090112290423061003020f0a050703020c0405010311100801030803060603093903030c0a03030e0a170901020601060f0c03030908 74
    0x38a0000e4104000c161002c40c19207100b0a0900c2104d5000310342d02e02504440c40148880d080000a0400028400b07039104200912580060106c0c010308080d0f441d044c54100c1101e03000242c42000902940280d0722003400145c4040d243c030722291990040501150000e100c4040d8000c201284030341940d00b1914260304545c507031a0f6802c1d000c00310301004d000d220704c1580c81030301030404100b00414404001302850400d80184484465051440c04030b60010241c0d040ca66a80c500c5860241c3c00c03d9414101c0c60742c0075180070300000905c514140d00f5086001d048600711a104440c110039135400d83c1c00e00000e072030840144002042e50601300011508000c8850455442c04d1141c501407180800020008040c410900c941d000e00b00d03050751500814907000c1f070140d0b0504d41141c118540e41d00b481000a1b00f0152100310700030f02c0729002e100c000a400e4100b1024402c07d00c0d002c90603061075106c18160360041c030030000009800d81c400e1600e00d110041c076658a00c9000c00d161022005001c035580d05032015481 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 99837643 1250 99836393 99836423
    0x160e09160306120501020a2d05090a150f020c0418060e010e0d021501051215100f060201150801050714030604020f120604050601080610030e070801090305071506030f02010c 76
    0x380d256440d0f40c2900c16000560780313403a02e001c003c0040c8a101c0c255107600c892020b411001110b04c40c03240c2c2004540d482e01540700e10300c079400070b0f088110035801007250040880141201c0ca03480004560302c15007035000c40e061810440244000c55070f024854180c00700d84514503000084540c0c00034261004000000b080c4030015088180c105450343c556100035a0200e003800b0300b2401199840b500410049408114404022000d261100a100100c050103070208000a070181c1041003201c01400d90501e24920031610340c400a8028a007000e48882d001d80d145400203007607007050046d98814803d0390b64062900c0000f541001064002504040d440341d000d001d02c00b058500b0030041c2090b840e031078000c407065003420781c00e2004032813025040904210600d0100b00c41030312601c170700c901c0c41d10b4203140009011501c9480c25007040866044080c9550070088681c041c154400060000315001e8051a146094541e0060048400c00d10001b4548211055240c01560007542c80200c068003911840f018104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 99838893 1250 99837643 99837659
    0x1701020408070b040303080f010f05010503070c0b090327101d060706060905070206040302030f0a03140405150a020304020a0b0d02120103060501061b050c090907030812160e09160306 80
    0x1030b0319001002c044001090030018903a00c5024180c02017001c0200140650601304040b01300c610714041c40d4148003000001c80c0d00c5606c104405079505800c400484c03040c6c00c1c40d9203500d45a0f40301000d4401c19030711a0341e00e008415140030040707005e84001481e020f18035a00b40c0055865643c1d1040c40315449000300400ca809840780c0d0020035000d4481c0c40c002941900701241d40c811180d0203881082154018820040065000402c403580001d4a0b443c0903159032420078101c2c00350400509001380c0d51000c8052008020001078504130100c0c0a42140b451707569420f81090403404200d44c06584520700d40d104008040c10100104038206030240054034103280d036030f00d1810b46042039208840c0d0641d207000401629510280115002d140c00404c0030380510320b078403401e03038a505a942c61441106201d0114200c1070b41000a1001035600000b0580c0b10008002d074120b5111040340c004190b1460650b001100920442020340300240c001d21440a9071a0300144000b191441a840014941c2d540d00c041848d007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 99840143 1250 99838893 99838903
    0x601090e1312020102070c0608190612030219120c06020c0d020c0306060f010c02060c070305100e06010f060206150a08011503061805030a03090809040501060c0b0702030a091701020408 81
    0x100321070381042480120303103440007800c040440031804691040c04114001075071580c032201101c0003032030f03c84100d0321150300b146440e42c281c014240543c6d140c004009058a2036420505c03030203000340c00fa45c0c40111a04140703802000304920091004034007801011340300d0302481894107410701801d0014100620382d0840c501c0c1c104401c0040e00942d100c81078904503440c0410a143e40048143c0c2d4415101c540c0d4070000e4a110b4030048000d1080c03070045561150310204000b604011a00a8101c9545290300c80c1000000c11540428003060701840c80045541c004079024041100c810b50b0090106942d17010510305071192900c5040d80c00281040001a107403024020040b030503c02c030311140500703461413503c0400c881014195012990000c000600400e03400f0040d00e019407200e090100c0c88002610745100c0c01d2291800c0d80750300070300c0c1800114035558030109061119104020800d1076848104007680e40e03014104501340041c1030340c0400e200b802100081044074040180015060640b9008210b00341 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 99841393 1250 99840143 99840151
    0x3010e1015050d15060e01030e1015030c1d040f061e020d0b0306010f1806090f05010311040506060301060c020d0203070b1e04080307111c050106080f0c0f090601090e 73
    0x54020460551503a03c41c8940105001c1d5402c0c44c401c0c2c140f808201500000c5640c4002e81131590f5031041d881d141d1820301140601d4241450100b081c04818945160b0303c1d1103500056800001c40a000b0070b140358000074403811030040d8004440300d0b5440d0741d151180558015000c403406501c0d131072000d01c80e05c40224004a03041c140351015072030702c06e22800036040300d0f410b2a40c4d5200e42e0000e0010484402644104400d94510118072424055600383e0000540321540c080c0c0c121074a065540c6a03001d1650340054142c078442c203038203010781001c0010002a07690030b0f2982030f0b02640c1000100318032030064549074210b0b4409091404180e5039a0006800e03c4c00d40d600101280000080c4004c0b001c1f8280e000d680c0c02c00c01e15030980d0501d4141581c1ca030f601d006a86006140158440e1240d28558a81503c0c414081580607003803440441e80c0f03040b03400384c0450b124200359440742d00c02507070f107a16011903200308050b40545280410000c1504002400b180501524140220300502056145884c9406485 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 99842643 1250 99841393 99841397
    0x303070b01151101060b030a051b0f130801050403080f0a0e060f040605010f3002120705040c0c0f02060702040e03030403020d0905010903050309091005032e020406020303010e1015 79
    0x2248410074090f06040b050802103590764513110091040d200d0250a407500051500701c00684c07641c0e000c007100d8050540100001081c080400c8950048925200516408002c8041c0d42c01040e0f0b5410001d0a894007590014003188158000901d180c4130b25241c91f9100c03090f4440440d0403601044181d0411000380c451710303030a00e0803001b003200f80600c60042600500c3c1900c1012450f900e410701032152141100312401c40f01d91050842407240510102c0f40001580041a40040c2100074540c55039078595842118056410300b01d82000c628007500203400b0303903500010740c0701201d905c5900b0064550710401040703920035600d50340161111001c00c05184604c0c4681c0080400c030b45212000350400c1000d501480c1080200d181c2071002640c0881070b942d480e00280c999000d142c5440d42d40d04003018003500700c103030184a00d0340c07011040035a42c10141c1d19405540c400c0d0002c080001c207410282c0c80303540200c0c030142c1d0003040104040d0120781440c580c061b550303202c1c8a04e03041e00d41441c0300c4100200e03401800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 99843893 1250 99842643 99842669
    0x1050102190525051e010219020f0a0b0703080106020309010903030309050102040f0e041a070c02041a061306030b0301091a0c09030703080304060e0d0f0c140609030307020f0f0703110303070b01 85
    0x132084c14080901030059000c3d00d2240400c14210000035030319131081c074011048503141e04aa50441d2102c00300300e612400000e240200d0301e52038841002e80c03500501d10940005a0540000070190300210071070382c180c1010794a0300301d4141962002d801070003c1b080c08440c159820030000540c080b0800d030010107494000d140b40907904050806412364419420307100c840c1940c0344103002025030484000700c800d581c1500c0c0411450325014160a4120b0b8044c6010b800080019182080c03e038202410000d88513552410040100e0038404c0c0750803660300500041503444102e9485031030221100103140d1200301d50418034582125400405d007042001d0380304a4100f07102006000c10800a8024405000104801411402c841c0c2070008d11900005981d5070074070858134946004d208001c03258401c01800d54045075564140940340d035640c0d41c0201c400e440107004084139108210b1010a5001001c411140140071550542e01c42c66183c0b10b1382114198148010031404e40014083c0c0c1001d03008007401d01c5003103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 99845143 1250 99843893 99843899
    0x3090e1005010f030b010503010e040f050a1118011203030209030a17031905190e030c010e07030c0815240907021006141507020402040302031f0606050301050102190525 74
    0x1403c032048100c034060030325080031030100159a2100c20790781103400e2140c2d002440e8481d401c044060f80c12940d0090180c2c0107142e03618080c40300c10542100300b180242c0d40c9100b13182c444e141d22480c0c03443c04e0096800000702e4002a20100c0d1094010b00081781000b0309941d18201c0307641d640c0c40c817a420550392443c00300000c41040825100c04030b03154405aa540414000c5244c070900341c034201c02c40100c406618994450000006040c104180c0342101c1e0000000c20902c186104095500c035060302c000c239109083c68901180c824408a80c05100c41a5100000180d2b15068002810041600c2d035003400e0101d034102200b07540e80e0f1028070b58016602c0b90080c0c001c1c8460040c0d217005542d4150469003580350710303c00d01c880039210380d03159911214400c180d0701c1e04c07280c90748001006441a5440079505205d01d0200a4080042c03400c40c1a4024801f001001140c1d91500251a180001d105150140e0000d0080800e511581a00e0f0070b40c00e4441c0c002d56040481a940d48002141c0c0b1907184104007411210034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 99846393 1250 99845143 99845147
    0x6071a07021f02040303050a0c15020d05060a05010c0309061115270714061806030907080114012418090b0103060f0503030306060c071505030402030c09010612020703090e100501 78
    0x21020900b00a6410b52400d815a10041c0640c801d0341540740c200241500080248201003440c03c20140d080c0c4419944d61602c00c00c0c14000c0c02c401c0d500302c2c2c400c00c1c140d1000140c40d8050450041030643c1503c40030a00ca1404005950032103611080c000e65005540549202003a550842440356504500e990340006103040c01546401110721072841d00d60000c01d060080400c0b1040c030000c0541c044804550343c1e8010a048817a015420900c55003000021091015104010801c002595080c0000b045001d400c143c0d0304078400c000b882100e00c0c00a440700740c2c0385000b0565500000ca420310341801d08000f9055040c040309000d45c0d41c8132030350b800d41d6225414455a03050003040700402087c03070100c0c4841d051000003030310392001400c0548521000101e00c68145030602c0035100a00b981c00b041c45818a50901c060310360341c01250101d00c41c0c05620303054185486c4c1154014180c6500d962040e407000030656103200250310503841a000c0c040c1c8a4000299413a00d5401c1034461000c00f016444414546000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 99847643 1250 99846393 99846433
    0xe18151e09071a16080d0507080a0b1005071103060106030e0f03070c052106010f06031119050a03090f140f06010e130201030b03010f1d01090f0206071a0702 69
    0x5946041d4000c1002040203d48128559440003548806a550f45041300780340e440e40316810100812810003ca8080e80b0720407990b0180307119448644543c4401d6a8002c104000c40da034941c1d5107503000c0d0040c8640004207104201030000f80d40708028201e04410b8510010b450800300764005000139441d10b000089403130040c4002914130035450010340c100b403030658905914030141d004140c0291403c285010b032103441c80040000c224414400d6490030b50315003500d10807110103401200e000c02e0030300415000c83c1c4c6d00803044a02c0b41e4040d0556005d501c07803001040328240d02000303801c02055110414240071481855003101300522402010b210425483c03030280c240a051800004150425401045250250640c1691140410844407510b1015100607002495000b800c586c056107407400e0720540318060391000c103040320901d54000c003509211641a0030399050f080300030104260501d141c401414050090301c0402c0c4640104200c040c1c0340c88032131002d0501180c0b60401a031216014940d0b040207242 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 99848893 1250 99847643 99847651
    0x6010f020d02071e030c0906060219030f030914010617101b0c030201060f081e160603020f0c0102121f1409040303110c0102090108010b040e18151e 65
    0x6450301c03841401000c0e403140414855100104180301e140071066046103403400196030702990703881005403941008070040080c1d0164401520415030181940c1c4940072460700c200d03a050f90f5090f007280d10108118040d017081042250303c415582000810150280a00000b901d01580c00301380c2c14400030134282c500480320f0074101a141c17400920348505c1818011501403102503042800da002d1a07803408034010003003684090f914980059000c10800c0011a0003400301d006855020038844400c4189a207a004103081a07429044130b220410001d4000d80103404e806410765000da01b44245101c4003030a9900c41c0080c40015045841009021441c410085c01c1c0e40b1488040a030200e4207144100d030140500c5840d25100d28201c500103020144a6000488034158001800d510740c0d803120003141c080d4001550180c003207111701002161311803200381658101c4a0222600416440b0f42d08402102038100c44a404079020303402c80707a007544903440c580c03c0c02010f0860703a4040c6c0000c05161800703d404050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 99850143 1250 99848893 99848897
    0x13050603010311091f09050402030f0105160315050d0309060801080d09030b130507031410110d0b011e080411010e0906040e2103011a03010b1210030f050606010f 71
    0x300040c008034800e007140d4001d0b40e2041d00c01c40c0035611117140310009103e100345101d40b021429007010490b0481500914080c0d4401e600716100d8066210515081c8ca40c00c0701c04040c9199044032080c1224466005075603107628050700c414156032568081100e40c10705450540c04506059000c100712548861410700503d03c5d500030b0308001d07180b4003005040e42224403020f0484113904010808010107841074800040e0b0203002c0b50000c954910b000001e80d8405241005e136801040c501c102e41c1402401041c0c189001c0300d2149140160076284100108024401c990420003042c0721544840c003201084028002c3d01c0c0c0340c0031320b54a06842e0682488943c90708260400c0f6004484030000d441e040b4070103810041c1140c2c04201446504140d130b1030411400c0740c003c103145540c40b0f04504401007400450507a0503109581e4080302d8100a09240340c4428031409440c260304010354180b44449a40381c41d00015488003501101d070b0b80ba1204046c4000400085d1560703080305c1c0c28003040e903812034001c0c2c2c442400c40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 99851393 1250 99850143 99850147
    0x109090908130f1203030b0a050409030306090b181902190815010f0e0103270b040605150a060f0201110d020903070f23030c06030903040311150403081602040c05130506 74
    0x850f2841c007190004e0070040906407181400c5c4c2e80c6d81d88500c1c01c2c1024090103001000700600c1e0342002009008a8451105054a84040d030902804e0803800300340074141d8980c000c407240c0c942e101002c3c0142814035030038110301e03824010f21002c0504201c40c100100c1044d524000c40c4d042090f820718103c19142c0e111418801007100c4000c0f01da4200c0700103e00d00509080000300d15031089001c100c01c00c42180c5299a41c00d500e05400100100c0c202500d000e43d0084408000a41e105c900c27032034540740e050f040d60b0380c8980c1c80c1004019070b5116100d201480f509602c0080744048060900f002030340c00c2542c0410250340c01051181190a00300228002444401a0030901c0e44c540450400015001c100141c100078042c0c007140419282009a034090b01000342c00950f481c035045400340c0d120f8210740400c4820720703800c0310b100c3c1d05450504000700c0710008101d03105180c0b51035541c0d81e142c1d543c006032404040394249040e080159030b80d0721840540c40c1c43c1e80c079001d0703a60007042c804458000e000c1e0403851040c501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 99852643 1250 99851393 99851399
    0x71e0c0e0c0a0f08041103100903030b10020a02060a18030b09011407080705070303090821100509060d0614090303010f0503070803091009030c0b0a092309060109090908130f 76
    0x302c0300314081480064100110985c446003080256904c04010103031700340c440c00518103514100340d03000702015030095804110520b00e800c00c2110751180b6065140042e880075201501601e841d600901f94034080d4280020b5a80c0030b254201c500240c140e0047d28081c12a101300f1400c88000e016500d031000b0400031498852a029102030a01880504440c01704140440e19100300350181e44011081500241c12a8540401d0f900b26031800c014000e020741ea09131810089028064440817a60555400400c56241c81e82c8000a100345541c01c071070251406903ca24070b010305880c10b200c03c54060701c1c0400c040c5680358100030a41003401c8607076201c607020741d00000b410800c80d2008030540740c040c00100c1d00c00ca99009034440490311000305400c0608004e01c01c0e0780024642001c94024034141429465210402d591203043c8001c3e5070185001c0c4403a0805c002030350140b854400c184651201c4141000c1c640d00b61030f00701d0704084401e0020b00300c0784804001074003c09451100000b4001301010181c1610a0741 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 99853893 1250 99852643 99852647
    0x201081503010905010213080c0312040317070209240f090105060c1c030b040606030c0c0b07050408241f0902030a02070206270604050312071e0c0e0c0a 67
    0x4020884080c04020881400301641c1c29006502055089802551a4039640c410030440e04594421a0320070321a001e07200e2082c0c24003160b04245985c59001d40d0381840d146440f5180c1c43d03e4036150005010404000c1d420050340c0307100c071042c01080c00d08400016070328082e4616020b012041c4034a80b2890540c004d0251a546118090303055070019125951112036503119145048095104180b0100200900b104200ea060f0302601000b00215014003801da41c4035800c1e402c84004582b910005425207210034046203400c0039142e00203d1900d44a4034040c0d0381c0300d215081c100c407070740c0350302148010554016050746036016154006010401c80034a29101c00341d00d105813001807240e400d1042d0040700013036050459034142c500e0142c01400c060f03500e000ea4600c2c1281c880b040783d41e060050101d000003040c2410f2030300c10303030303040d141c010700101201c0c1e04a0a0003441500700010441e843c2c001c418250400080182001d900144520101744401c0c0c1000c42c0c42c82d220200030011a0042014460800b04503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 99855143 1250 99853893 99853907
    0x801140a02090f01110a120c0312060f0501031503021302040f0f0b27091305060f04030e0105090303160605010807080a030207060e0f10020601140a080c010302090d12090e0906040201 80
    0x7070f0090910b2010048410002810118506e20140c16a0450740300305070f0003a0040304074002c140c0700355070b25004001c0a003c01c100301c0c0d100380556001341030301000030300c1154026400000204e00c51009050982c0d42c2e0b034000740245441507a905038407a00480c0810000701d01082c03000c060a880011a01042d04210a032100390140c1003400c102d001000e564240100e504981103005200702600c00785031460b10350703201583d4007510f80d4100c40034411100003410070746210340c9260240b68184e607800c1f075449000d00111b4090b0005000d1aa15000400146003000e10381604002d50034803403100442d0a6240c80e4081c0d00f4105268040ca171290803000160000079800700390201903e0090810310403000300c05010170282c2000e20045a00300030300500944503d600010b15038101c13100103024a400104240a11070040407902c41c04149900031880d45002d58001d4020303050314500a040200c00c14410b0721040c01081e07404040101162209106016900c15044100e80c4066001d00801560030a40e00017800c1c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 99856393 1250 99855143 99855169
    0x3090a0f0513110f03040308100e040302070e0a0f0608010b0405010b16021507140f0106050307030308010b0c0a0507140102070617130203010b03030706060e0601020a200a090203010801140a0209 85
    0x40340d94500b000c218884800a5078607024410304c0454582c03a0603d00548030070000d0340c000f065034070340c40000039858041d1444180301d0f03640340d40944451403600c141200d4410020305094540383d180c905260050744a44200001048100008240610501c0500c02161410782103540c00c0e20ac00c11100c0d00c0c2c525110b0341c4801c1e282c1d06840d40315018045000441003070040810052540d10981c484120703e54001681302c4009002070000c01650ba1f4540400d075940c295440b005011821940041040e9034120015040840401c016100740c0381e42552150b0400065410881400315690310072911560304001d0030014002505040f0203400e0b0003013600c412908000d002a0805402c0c6050070119107003034000f03400c01a00601225160841468110040c00b01030140d5500c200010b000100c20750310000326409140e030002d0840c100c60203840a2403c207014980031068100c0c8034610005100b00c403510081d8000d1400300c00000788051080c2280201c404d002c2c00e10b01c45107005002014095841c400d2500305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 99857643 1250 99856393 99856429
    0xb0c09030a08070812010b031e15010c021c080d0f0204030c0e070216080708010f0203070503061504030f060c0809011a0f0a030b0a060513091703040812070203090a0f05 74
    0x40f1502441c20190910031300700100c1c0741000c0d40f07000041c02000600554080c05140007444c460032407840706024004000c59503054440d01090003000304d94010803900400d54006810301e2400405481902d2140401c14421600c0e802d0000300d100041e030043c4991014252a104190b10b020302c0d64903242c40c00340b8240036511401203444d01042c0c2c0c8900821206e00c0e003072180c00c1404d403136a84d07131020144c480300c16119055a550804c0c840b811b2a030081e1080b00d11a8145445803811902c4110a00807803232041000b02000134002c00003c800b09050b1003a41482503c1020041031041070841c00a101c1403014291804680c189225011008401500b941d10080d055529154080d02c03070001038000700566001074030310134401c418800800340680164050b14170135106d400034840b4481c070140032184520000b4201c00250114906402c4090700103580181c01031803402c2c01c0480c407402181c1d07000307801e81310980582c3c40004c21400c1800d01480c85030007441250301140383d4524040104502d03803030300d00a401c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 99858893 1250 99857643 99857647
    0xe0105131a10020f010c0201110d11040801051609050102150f060103151502010b2d01030b19034101060321030b0607030203070201030e010204090e03070b0c09030a08 73
    0x1000c103185510400e81c041c0024600801e89148041c00384d22a413003909a0381c81d5500740140010564014011802c84d40989040307a0b262600f000e01c0c0b58020454808198002c0d441004000340144c401d02401d40642d0314401e1404159a44c0c10000d000c404c02940010705542100329044286100b1030920b50340101c1c00303224103030960754000048004160a80204100f0f4104410100700501c50404005411403141c008004080241c0200407a070b458043c40384160f14032503102400210b0503d0f516110610040c140403541c50003650000d9010308105000400380c01c0504001c0050010506407044401e80c18a0030b0314034021010a52055400b5410003010803400405200e40620070942c0038000030354200900c80d105010304c40c50f00c458885020708240000381408bd032401140781c0b9500321011107605400540c41c000b056401034000e011482d0741001c00795030a000c0060101e03418010f820610349600c1c0a1a5144a586415a94601c2c0a08074080c001d07400d1242c9400e540780040d1080c20b4503002040e4076 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 99860143 1250 99858893 99858911
    0x70209040215210705090a090b06090409110301110f0a0e0d020a1508010602070608150d0203010606030603140f060c03090304080d050403051506061e0c01020c030909010e010513 78
    0x2015224804580c858008001403920f1540c00e00b801e002e210040c2d440301030100750300e45000494283c042c1c40c041c15031010704e1140070001021950300c110071210002d04214141007143d0300180807549074013400e580407100401001380c00d16082c81060109601104814103084810300c4081c21401040b0784201400024803280425a84401340e8296a583c005c2c2414225a25203100851516440c101c00012480203030020030290700100340308003135030b005548042d150364480080c803040d1420301c24000d82205c241c55010004da2800c1c00b81c64080c1c89c1c9a24003140310743c0385140c480c3c10344100c8034041000342c105008001030180041081c9400000f5088030030f441c1c0e01c44074051411441540d001502512130840d00d41803058010010700100d901850990358110100c101420411700100c4281e50301140130030949484685008180361040d00141c221810640101c0141d403caa10410401c0c00903440422003a10b14600800385a01411200d0101b60455261002254120400e83d903440c041d540c4940c581 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 99861393 1250 99860143 99860149
    0x26121c0608010c02010204050102060f06010206040b070c0501110a09050406050604090c18030302060601080127110d090614130506070c0809040c120e070b0301090e030f04090204080d03050c0702090402 88
    0x4901414400d070080140b440c00c40740c041e000b0f520900c269405402036038001500030464100581c419101038004e056181d40e00d84d00d52840709402000e50042c0010b2968031800718500b44144041500c03070303040c035554500c98040e010b0800b03181c41d444680710318244402400b10781c035402c0c2901d00701c076003a980114290700c203014142d5161031032401722810989600800418194000790300c1d8094a0203894541c03050340c90f041c83d074100981c00000038820751540e0b440201c0380c5607240d000d80c0d5840c070356030302141c02c1c041c9491030101510840031040d00c2c010f0b00c0c0e80c0507540c100618080315402c00f07030080709071a000707540c1d0f03a03800d894600041c050000d0007a01d1044809121291003241c1411a0040c010041040c800c01c0141c11945000394207400245400c80d0303030040400c0010541c050303864090070142103130328280180b03010b01003410560704c0a0000f4015051503506c404003520141145c07483c05a125800c01d071843c1d2800c0351318041c81c02010705000520044503400c00880707010342e030143e922007220b5440f130002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 99862643 1250 99861393 99861401
    0x10050d02090a0207080c01020306091323120c0318060705070e071b140d030513080f07140d110303160302030405010902120f0118020303030106050703030b040626121c 73
    0x10140c5103480004020307125206c1940158422082241c01003946e46480782d8440c1170045001009000b1141d4801103941101c1f5030604059101c5036070308071034802a0f5110510076507000015910742551000c1002240400420420304003803005540d094102030881d11040d9440046110300e10b03042c0381c508046410148103c2605c610031810019106680840b40740401c0c2e00c140030b40b0480c170f0b54011134098098151284c080c00340940b041224181803c0401e4031928066804484000707417075a401c102c141c2c001240072518503112511100a06202d0388070400c041d040100c4c2e48400000340d0010020061040440c0780c04450721419490010b840f60340c0d84c60002e00609210a01940c0b200000e0f420608140c0001110700840c910400280510050035560104010008600950580040c00140005407040c000b40c01500d01034580401e01060b0100410304503950350b080002d0b11022001c05482402409003c034015181d403000401002e4490740c15045140a615480c0c040a1000b001000e916040707908 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 99863893 1250 99862643 99862657
    0x81009020423010e030c0f040b0301060611070603050f01090b01020f010f0b13020309071e171c11070302100c05150114010503040302030a080a11030f0106030510050d02090a02 77
    0x85607150384466140c07803a51007807800e66024621000103540360354801d48450303054601c094018110311020400b088441c0921184803a082903440c021075a403a90240030b010018211a110922680d07000d204203070400c04160031883c141400c0030b050042c451107050a450440351014000103945500781d00403410b000c2441e408141640c02e0032006d074100c3c1000e41c801880c459089800d10004285020030900b0790008941006540e00403000811042054040c461003a030082c0c840d5808140d03c0b0044859107084181c80d55880794010034002000f00b07a14800d02848410608103041c941901c040000d550320756501000740180120301200e40e055000f00646400b880d03105080e03540c00000c12420741941c03c0d00f442201c40480104121710101d50280c0c00700e070702940e0140d01035441d01303100030000d031030110000d0b180300c4d0301940d00d1417614500e08188024601401504801003120751504400405844001d400703000c0c4090107040802c815503568100310061541038502c500c40f90798010f40c0100a0041c03070303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 99865143 1250 99863893 99863909
    0x61606090201140318060105040b03100207031107181802101211120402030c0406030804030609020a0f08060405070e07090512070905070c06050708060603060618040f06171c0810 78
    0x4c410302101100c00d41280b6a00c40c80e140407030354140e03070311010030041d1410b4100342c54041d04220303180011401281c0040440c14002e003002c0c50360480101400b4600200c0340e020740d85480301088864603141640c01004c035031a039500c1000344503400a07000204d2607001161010140b1104c4000c0c06040e220b0344c1c003d40d05030507a24440341e4803010f0b080d090a44240c81102d040b41319026101840c46940b810b8415042680d400001d82e5040c18203554075800140290720040ea40312402c20320000b400e05205402c03801801c90034001c2e0130b481c105481c1240c500340658102c12101003030a004c12144c180e0103000c40c0f044450440f20000700b80c0c0e040600e2805c01005e900423841d030743e0404081061540c1c003d036031281081c3c861002003103695074125049a010302c0c161038156105804101040291410070007070040341c24000d1408480281810010341221f0791010080962600c8543c200f0880c0c03296007452140300014805030102e441110701a40034a45e01d84000c009024116010981e080e400440c07070740142c0910 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 99866393 1250 99865143 99865147
    0x402070f02040c02071805070806010807020c06071104200a05090103020903011517060f0403030c030b0301050a27080702010c05120d061401030c0f0503220b01090b06160609020114 79
    0xf0a00081d12a1807502681c801a620302c00740c0c181b00501d520566104180969075200a03407200401101c036070710050001e800f14418521068240da803008028510300e0321030820426114403805c22b020540380d840f20200c102028000e800d80004d1241411980d081283e841d1080c0c0d2803414000507802402907200040d00341d8600700c07204401c0301c04080080e007685c3c9922581e07042c109030b0b40b000c980c1c0c909040740c28400c01440c850105000900a4104801c01d080a0401150352172000010a00311a000c552500c01152a8810121803260003401410280304000c4181d088042a0311501984c1c460000001d0412440c80c1d42c0f04103002c030500c1822084840341e0380c0a5590304480da90030700a40114013940c82c4a000c2d00207400290342c0248101503000010b900d83e0040d881440c0b0058400b60002004842e02c19031401010064003022030a6a803501d00c140340004455050526050854240c0c1c003000e80a110b0420083c107000c0803000c1407841d0260b20400120711580c0a200495400590b0707242c43e0b541d8900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 99867643 1250 99866393 99866411
    0x150501030b12060a02220e0403081609030b06010c05060f0103020f180c0309010b060403030315090c0206270d05130602010b010801120501061212020f121804150e070e090c090402070f0204 82
    0x12a000c170310302950095580d0380d5207445900d43e852f030347c1105e010312202203100708504000003442181c11075480801410080c10301e0700f60b03855039418000c1c02c6407a0f402c202c0b4070000500c00c624004094032003118003a0342040480b806604201e1046401900b20b030340e40c0f08084001104c46509402c03a49030b002015100345e0b1155502d2030060090504085c80350608200c2c400041401c401510039030038480c6050740207000d103888400000402c501405d20280b0b510101412800050b0020802078481002c5503480d1a6a41004c264118615105800c510b04590420202c496241c3e404443d09043d81e0280c001d1591041700c5292070780c01030805a101d100341111001158080c40014070301c164401c1403a400f41c81c03280819001d11a00c403540c4508000c0e0300301d0180941c000f07640780c0500c10000c03188041c1000844000b0030241d00c00101c030302d80c0800000301c00c1104010750f080e48501000c00711403003514182c00b581041e6032001aa4000c1c2e816241c041c41e4045035690a12081444860f10581c01800030080041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 99868893 1250 99867643 99867659
    0x1401020d02071d092e05061e010e040902030613021504120818090109020403061401061e030b18071101020a0e15160506010602010e06101502030409150501030b12060a0222 75
    0xd0805014031001c1c1c45c050000c3c042e82841e0040c1a015236411428000da0416007005540003010700b001990007580d1141c0c00f030b0040c1c600f000304a004d82c00b400e0b0011107176207041c4100700c8440b000f884a11200c0d8002d01003088544014100380c00e00d03030ba00425003900d4140da03404009240100c0c103031540e4481d040350f00000b400c445582c02001070b00e008502c00d0003405c602e00400605c200080c443c07000000c5000864189100c0060201c0d44d010310145000314144201b500001c81c01b00c0c0c0000032080d80d200b100305000000d42c2019a002003040d0400c0294100750382003c019212070220b905c0f1602841c803c2040219a01824040310b010b100342040b9502c0001c034604215a81c0d00090007070304055880d155240c0000360303000883d50711580b03250114503006424400c1007a1200502d41c0f00005606c400e103c00700d294802402a60710103c3c0844294014628120004054541c01d0060600480d90410710b1445d2001c00708a95901c0403400c0000343e07607510700d0050008143d203040100c4240000307001011881078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 99870143 1250 99868893 99868963
    0x708030709030606050402071101080a0b040207050d02010c020a030c0209040602040e040507090c020a08030103020607020a031203020c07050901050102060412110a0506090c12030729011401020d02071d09 89
    0xe01070f003402c0110319103c00c00d2000324455084041c281a4000250612a6100f442e10a500c56248080802e4050382440400e081e0b8101090881d01d5421034100740185503824030403a51025840d2004046500c203c5e10041c2c0b02c0401c1541c0a80182c20000000d000c2c80201c0e0100c800400543e02045c110f071400d0308100d80c6a218900070b9080517400c1c1005807034104d03c00518501455001862640307542d2940d030030408107600451040342c00404002001010490795082c444540402d61009a6511701c252039040c01c0c400c90b5040303d032046908400602c2180d90000d061580076510112500110074008820341300007010501c4110144100384240c1d08100c40422618000c0c1c1040301150f0010026104121450302518440c0000d50b1042c00102d010811140080039200b421222415413940d07015048203803091b09030424a40d106540422405c6942e041100c081c488138a407024040c0c1900342001c400050a0121600300c0242513400403400c021401e01807590b00c050348104200107071102c040c201c9401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 99871393 1250 99870143 99870149
    0x4050607020f0d0207060e0a0b040b180a060519020109120f09050a05150a0c17030114120c0f060d020406080609090a1a041b0b0306040b060c0c060f0708030709 70
    0x5000d0341101c038003546000264803c8650071500070b40205070400c00120780c901420404668400c0f9424030008030025480001d1000e00104040d4507902c0114200b140e01c0400740b0b13019503015003540e90007007201e02d50180070356003a203070119040e000b101c5a44000b2800f4000d0600003410041c008e01041458640202c15981c0119880d107070000260b0790b6a00704001602030307125507608400c0f010118030003200040000c02060305503091030800c1c0e20443d01c40d40c0035040e80003050201001c0010041c0854090100c0716140d01c0002c40d5040f0a003640318020544031a1552101406056002c20210f080e6503408141d132130200745441d0464803107680b03040061160009a0302d0078002d10744400460401d03c0042501c80c5010f800000407a003840744038002d003495480060090f030b540703644201010843c511040c030400c02090b0240310f4a842c1e0030400100021a01d180980e24030a460030401d00403003140219003003d0300c2d0030032036415441d01c02c134030a4070120b0300c55510020700b80100001003100c0140c12000c20026 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 99872643 1250 99871393 99871397
    0x90306180709060f03060e0f030a03060303030509030702150a170c0a0f051e0306060c010906141806010308030403210e0c04270203010f09050102090909070b0403080f090904050607 79
    0x1d0705503030720001011100301d40500c0e18018007030712040c40880c8091f007004944011060032500701522102c800c500b15000407428070002034071b1300c030108140340e41030203025004003016018610305901503002640d81c010410030004100004100300001c68091929401401240940d100c880e2501c0c0c0103c0a50754041092100070402600140c1d00081c0b040f410f03510702c40c801c0040c80001c00c04070382240d500c0750401000c2c10340c030010400071550701c1a405c0c062041c005100e0304001c100c07004a1446000000c1c8002c182010743d9800099400c041c0d03000090060441381c2120f100d5a4985a030f0a0858a00544a0150880e90310031000140100050343c04140300e07640e25010b5076441f46040e420001915220314510704000306035036010494180b214600002648018000220001640448015254010400d0310341b07940c04074201d640750030011103244e800401100603219450400702403081600a0380005003800001164000400030180219090494028060040b5140a107451030b5500012505600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 99873893 1250 99872643 99872653
    0x111c15050a0b031504020a12030c1713091e1404030201110306010f0e12060901060f0f030503071704090203010b03070e0f0a0510032919050d02010309060209030618 72
    0x2002207108806002c2c1c0000d000d40341c011004c050320b070040c28024106a92100e02980c0010354000070021405607070b8030944030707982c1908407400d06640124254128022a41d010810f403d403551224803010152500c0e91000a004035020244413103421480020000d0245040094031270b4000c0c04581c60b03c030f944281e0080c44448068014500507000c1604c00b20301180030558208100b82c0203640d0702d4544a030103400404102100c0c043d8130300c1e0810561f10820310380d5540c2d0050007054240301c05a005040e5501d0a029050f10b55035400e0703928401c5050141020711461594900301c4c1c1080219002410701a00642d141d5031030710580c415545c0b065490f07a01007440d488130020750303040c8034495031a0f8180081882d1502e80c43d000921000c1c443c05070010301090360b00c0c60414410581910300d80c4510b8600101005c0c1c5003400814418042d001d17044120440703500c4902000b0b203a0704e0099844d401582840d0114217000f40b0301e0003d010340181940960306004803005c1200241c10000041c03004480d020850b9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 99875143 1250 99873893 99873901
    0x1309020d1d030f0d0902030a020d030806011106040213020f040f0e070818070608060303070501140106020c0a0b1806070f03030b1302070327050a0f0503120313111c1505 74
    0xa50720f02c80c480701c000070f40070213000c80313841040e542e4020101140041d0a42d61145036035070000d8100c07030041804031301049181041c00041d50303002c1d02944020f8821001000542019000105030400c1408c4516400e03400169601d04526424141d030300500c5040b508030304141d200c0309801c010150456811000503805000155201e2440140001d0300b031201014059090070000103c45030305004040c203030148001c01003d00020024459110b0408400410f0100b82d414807800908241c120b10710544a1400c0ca03c1c240030007600310040b920700040c90044d0355203440700d0501203001c1e03018103000548038210b60001441030681580018a00d030304121601032818080015480481c00303a000c016000586410807280c0340101803078203c80e500c02c0f880103258640c0d0381d2000a101a030f1150880e0380e04925400f4100280d00301008200d5078080d66010003800d52404003032140c03994a104001030101070f020240007070f0035100e010025a500e080c400c0d10790040080c60500401510100c0c402504031450b000c001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 99876393 1250 99875143 99875201
    0x30806090606090d06060b070f05060f07050a2a0b09011b09030204020d020702030a0807050d1e2007090e0c0907171801020406030e100507090501051309020d 69
    0x5039100e104000d0003142010524403d00c12110381a890488400d99142e401003601a000c00c00f9140c0c0c24820301000801c814140340282c03e161024000e2000740c0101814440907941040680306000120700d0400e4a40301c3e41d98040e0500c0c2c0801c140d81002500e005004001e01084c00c401d80e03c64a6640000e01c0b411482001c8582c045400c4002d100000d10845414401450141c00038040d40c8000e01000d4102111500041d00b00800c84108899044c400a0010100a404d104208107501c20b802c01d100030b40c1803003200410301c100030700c0c810342041405000096495906681241245014001c03560281d4030341642c080141003c010000c00391240c00306150103842c0480040c0d200d500e5583e20121420242c030340d41d1301c0045015040604070b070340506440401d1402440500700512039039030045407442c81c00c1d0025013032410003100c03407800c9030415081103c03a0b0b80060030082280c900f031900355076640000c2d003c2c0341c0104039a0030020425000103888a00e00120b500924101080c407000d012545440c0da83d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 99877643 1250 99876393 99876409
    0x60f0c05030f0c0a0212010c14041202102609120712030207050f060420100c02130b150409060617241003140c040303020a110109030210020a030806 65
    0x10090803940108502c01d00318400601400b428103403c4219011500c46900180b1b4405041081c4a5282c2d560420302c030206034040000c4010031803d1460314905030621412a200103415440a4000c08600e032000841510910404c649030311409007035803259485a280d404040001d03a0111201d210f030803043c070841c1ca01e4004581d00e05500c2002e0642ca0030202c0415000f94011036010b13181030040000102e108041070041701d22480c802c3c480e00c41c0c0d108451029a02442c205e400d694000e8034410f43c0305610680080e1803140d0280c04a6080c0304526803140260082d0003246042508020010015041100d215018000b904c01c071800500207107232107610440b1a2030f0340d1180d81072005041c1c004900001c48108101440411380000241c60302c4202c4c0100305d4504001c1708440c0040e640d10f11107d03407400040e40b00d5070805020101189444c2c61501e00965550903a1409405c034841c54254041c0c5a004120344001190b02401c448040c0401d124003a44441e2240000e4001c1180d03100024030906d05026 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 99878893 1250 99877643 99877667
    0x5040501080d0818031b0304080607030207080a080402130f06030204050609130f0c030804120203010c09060e0105030a02070b01080303090708061611070503060a0603110d1e0302010f1104060f 84
    0x601e0341015558142800341343c40400180c0010782c0420000c0031075015000040360203030320394180119540c6180006130b92501c01c0007880030040520520010300081c10401c216a000d0b078091804003019111340c000034400400d0030070880039191801d1008c43d61120140c001c0400c80f4000c58040045543d018248031002030304036090301d400f60100c441d0000054004441c0d655084c01600c07050321003a140da070780d000c16520607002000c0501e03c21200008514090094160403402481d00e0800140781c0340002c2c049001c0050464103201001c400241c1c00c1c3c0c0e49074180e40714640c2080c408009540c0d90f507106030f10ba0b442620151441d0240110101d1820302c001140380c0100d00d0380d180500045520b1200303c40041c4100d00c00340c0d5501500c4000540e50b036040142d06d01814016400054152441c0f400c0408903a2910046000390041e10204000c00d104600451454804e84601c0d400303520b440c9012801000780d00c096242c6586800070034001c0d05110f00141013581d400341c03643c8503108000042524072001b031072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 99880143 1250 99878893 99878897
    0x9050105040207050d080a0207020301050f0108060a0e0c0d0302010b03030f07031103090303030c030a02131517060603040602090d0c030317061c060e0c060301090207030806010f0e01080403120e0705040501080d 92
    0x11451140500c80e43d000755009201f11001401c00015034002400d440042e1080c120808c026401407101c042c0500c195504103120580400c00c0665440c280c2d41c50390305140d6060322034081600d900c81414004c2d00000b10449000b4113503544d6081d08000e580282d00a1503050f400100c400640c0d090000c03000045a2080c0d10040045041d42d070741168001d03184c0c1c0000c142046c03464080c40b44141303101c80284104003400051000d0030f0019081c8038020245401030410012090700c8000740300c22034641308200c89d081030700040c01507950840040801d07110070113000000d0146408000c000142341c3c0c817003850b004101c00c0011030581500e680c070401c240c04450b90041c0c2803c9484100c243c0014140c0d60040f940845101b0a441030403c440d4000744081d08264004000280c0010b424010194415481d41d407040c400d081c142d0b500958258001c16a118031001310341030181a001040925000e8a031003d604d400300d0806106404105900540702c40440c031800d030049040030004548240041440d0103260f03a83d03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 99881393 1250 99880143 99880153
    0x1002060103061802060c010b15040f050904020d0c060509030c0108041e020a0803040b03060a0603060e07031a0411070201090b040515090d0b1f080a0b0a330905010504020705 76
    0xd900c4402c0140b148181846410403c203841c040162505000760a0444c030761400040e13011781c82c01c03d0000c8002d4007003420043c1c00007000140325402d4155001002ea600035134065800342c1d100c1c404104002600c0802410700b00c5020000525164084010400340500341c0940d100410710400540b480c803030940d8020031441030b4201d07100040d88164039003c00240001d1180d100e0a17512440242180e00a8008e0007908400100b0800c081c241030301000024503880c0360800c482072402e43c2400c0001000340200082503110424910fa1815415030314070b400f14001d00030020f40c0c0103103a1654042c3c2c401d040c02c030b01181068a00041c440c904800b50b0301100c40161a042001e071003924400403542c000101103901404003984000480c00d080082e9200b0100400114001198404d05541821041d406203126510490850307000802c0200750340d41184040d100840c401c003c6252401c00000030040811895213020224444031424034031180c202c410003002000a40d032a03806000a80c0300d00b403001b400030303881 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 99882643 1250 99881393 99881399
    0x7060203180f010311030106020c04063006060f0b03010510030c08221220030703050711030c10080a0f0207110f010513090c0801140307030204050c0403080408160510020601 76
    0x5103080b078407105014540003030b00c00d030089a2594660001c0e0003103001688501c0482409040500c10100074100030f8003480c20f40403041104a18100960b00c00340720300141140e40c2030421490f0340008014007201825000025100c0b2284612500244201c0d8811a0b801c4040c11010380a4030898041110b503690761031840d5240c3c0160b01948640c00041c411613000d0603c2e00001c6049004002c020901542d501103141900ba035020748214002008120650020450b80303001907040002c0ba33041d154424074140c00c5081d908000390408010825036030704010074145080d80c0036403024a140c42030640080810044071504140d00c00c0740600388000307003e12500042d040c1c1c2032a010040c00640b00052410314940843c03410001a0000154420482d168541c00b8100c80305411200490140426001e07503001005002c0c0002e030741e500c540c800a030107a50b40d00c002c20b0155010b9030071100650340202c10075584964404846550700030610860020850003800071440780741c02101d2000f917241580c010450750b42 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 99883893 1250 99882643 99882649
    0x306090c0a050f0f070303060f0b04050409022709060703090b0105040203041e030e03060a0227040605121b030c0a06080a18060209040b0906210c0d050607020706020318 74
    0x11107411a0014040103004041c00908200011301651302407803609921105c2030320b4081c05860139074204041680842d81c3c01d02829401c80700f950121a42282d0104924946001159203802c88003075110341d0030300422038018002d840034102401401601c04854081c0d031703002400c03002c55001c3c1d80020034042d00d520041004e4a4a600959042400750407030104245032511040030700c40f00e41d0f00442c0440c94200680c142da14081c0902580451003902c01d42c549003200781e44002c07c010b621740b2403000a58034003800d107058940f0b91040e009808083d1500034082c3d5820301c043e0b030780c2d011459807080a500000c0190006e0030045851a26103001402c602401401d102c41031301d28203401001d0a2400f0340d01c1c028000300c0311107400d0310303004140a00e100507580d103102c034107001c00e80d2010380b1660b0140c0a83c0d402d00c283c5865800c0b02203254954240c111268a007800b00c0c0c9801d10004606c01075100b460080c2242c24001d0120393b0902a09007502141c003072555490741644c89010f8003450761040141c400e0f6800a0342 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 99885143 1250 99883893 99883897
    0x512010e0115052505070f060f05040b0a020f031c06120314070f170a0f02010e07090b15030405030a0219080301090e150106091511060402040209180a02030613020306090c 75
    0xc0519201d90040e0350707004001d4030307180703855813000c0d00c680c0e0010000b04900180e000b4204050f080741d16002c08801300c4007401400318401c0d417090a00c440000a140c900140c401e201003103050303a0510680e40d46810f0307103d4492032592900c000070700b840d10707002000684914190b00029042e03030540324600304084490803011103801c4200c00307440800710b20310302070700180544049061250000040a86a0100c40e10040c04440d0758880a025a803400b600649182400136074241113400000c80400c02e15260000315014907030070140740090070b0001c0180001c200c1c01201038800c0d800d1940c21140580c1440d460303608089402c02000e01410010801401545541d411010241caa210100d4203410342c0458a1500f84009902c07c00010388002c0c010300440e00d04c000c5004000701c041c038000d07448208104000d5200c0c000500000c0c1305c0c55001800c1031180e141c03041810002d054404003c02c3c0b41c81d0203102180a0762007204d401d03124011131065009222014820391b8003460025008401c99a0f44007015210b903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 99886393 1250 99885143 99885157
    0xc10050913020d0903031428020c0303040f0605100b04050f060405030d0c0506060d05070b0a0c050a030203030405150103050d0309080d150311030f030a080a1b0512010e011505 77
    0x8140c1e9840c10400c00c0820380010050032002000025040300113040003012950300008454440045d4418811100792490030304929903442c805418000700001d9079036000f40308650025895000c04000c1009020080c00d00030045c1d4000d4078103010595a41c080c07045032282034003900490388820701c824081b0f0300340800702c010056030180c1078518183e04e8100103460441c0c491744480004030081010f404005090204c140c000c0e005445150b0111107a0b91140e0720f800b543c1c004c6880c90403001c5100040c43c0d129a4041d14501e400006448881020b411300a449a008850070340f400d1084051001014071380032801ea0403250003002030705122400080440103052121400c0e11100000e000000032500c4620541150904a2692100c01443c504d042c5c0904244191818420340100e810304144e128007000b141d07035441c4c1d1032900d05410390380e000c41c0070010209048509140c8004040c07407204940c000c80203003156200301049203120780c2c3e00c01c0c0f0400402e03024000c500c0204089450011131501540183c040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 99887643 1250 99886393 99886399
    0x30a0c0203071707021002030a05070305090d0b0f09060f07090504050a2901020705030604020a03030f020f06040c170f1f090803040b01030b090a050c01050309010212010e010501110c100509 83
    0x5001e09644400201d14078404021455410025019085281806c0245d0680c0b203c2d0025601b8050840c402520600031100c0180500c070300040c0407483c82d60764082e5100f005070f2280d001c0c640c909180340011280030044a9410482c441c04001c14440580003002503c200c0b015910203c3c0d05040c002400058035026081100440d12805801c0e41c5c5101000311820f0703910300340000340480c1031a0700020f00d042240d51166019400c140148800b5899a5a840c4183ca406080c1902d5518194034100d00c2c1400c08a00000a4000c0c0028403003000728031802c14007100c54401c0c1d2500d69000c0042850703158180031046c00299408a231030142c000e0190380c0d00d0340801d00c244034001120342c00c1c1d480b0b840070341c1c1c4111030880728008080014403c002c1e0b0904e00a810681480050101800a580b40b9a454452a16107414003001000090000740b0035012101c01d121034003848540317940d448401100c421000e00489011481000c00d4400410303000482e4003418070b0040a01c0b45019002c00107855a500000e0b103250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 99888893 1250 99887643 99887647
    0x30319030f06060f090906050a0e0601140f03060f270c0f071202060c040e2703070303090c0b0705100c03060305030f090a0b030603030318240105040606020c0303030a0c0203 76
    0x5001010740b00302401005181ca400d0034031401c80c607008026080340c1e0850038407680f5081040c44281caa640004090fa203a020b0081540d4940b1001a02d2500c0803d0001c045048001554003554004501440c000d41b02aa2024081c91601c0e040013890003000095143e0b440c4008d031000690712940011780c1c1c124500021452804041610b92503055101100c00d442140c3e020b018064080d50400c0780302c0e48142d01500c030901f0301e8201508592140b8010b0315080f02250120031352003860707044980810f00c01c0c400b407040342d554440302d01e40580980701001c0152225801030700c1c00904c2503141c404844020b5400400f030904050452102002008841200b00405684510110004104100400320141054101903c4911010402c04440c101d03821485018405006120541d24000240d94000840041c0249200180780d00709140000d0b0500040c070f02058030501c622500d05140c9013038182c0300e00f66810701190792a18426a95002e080001a801d94801c00004203545d80c6540074115221091064034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 99890143 1250 99888893 99888911
    0x60d0201090b0a11060a05010308070311010f02070609030206150a030b040830090c010801050906041b0309021807020a030503040f12031a01030501060504090f0204030812090f0a0203031903 83
    0x144154004560f50f030701080fa0380002ea41d03510000c0125550242101400b4040c2d1b43c1569505480d902541000a00344901407040f451000310a4212042d4405848002c40d2142d00e0342c1026005024007003015400760107a0008214841c003030551070590548050842d101c1c1524641e00c0c120400801072080c0d510340790911541e5100140040c060780389040f8400008610700d800380d071440552902500390b0501d0b600143d10611141d805c901010b044810440d04091650b40354004603020b0f040c8100100c041c40ba880d40b40805450301035110038040b60007501e40727665103400b940c20046191703030554010026134810111107002a22800c02150304c02d21601103020342c25965510340c032804c00d02000f00400309886040141001e290515131150001092900788455450860080c0203071003140144415503407078102c1010301c022150100c90007507a202c40e0302e541e200c00104e4101190903090b900070b1042d004003180301c003501e040083c1d440c07061a0024040d40c9811031600100d04001c803080340400034592580002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 99891393 1250 99890143 99890159
    0xb011e0b070b1015080a1e0e0d090b0c07031416090606110307030f030c0203041a030f09060c0a180302030d0e190602030d0b0102010b0915040501120308060d020109 72
    0x1e0100248112041030305030401c2200e2442206064000001500c04001d01d0728003a98410515504200c481d40c0c002400c1480c90003c42c0120f00703416024810a003041c004041d00c500000741c01300903038003966030f007016207407554110717541b0f4410360084141d0341c1e010703500c18000305c1c0f462290ba1440d036040404032030070580c000c80460030603015613002c284080d0361114200720403034200c50150303681e00c01c5c8005540390040315500038010100828840b000c042c6e0351030b80d2424050003001180d000e0120f075182c8880d454541005d0703682640c230480710041c205d02c0c15004a6400003001132080d000ba0b010b44580c0d81460b0640700f0071603841d090302101220498483c1000400b50b14180a0460100350b04e17501d20a40005440502c080c1d03805150b084d070800c0d0480e000422180b85e0100130388072000c0e0107482c04502c104041e00103d000d00040d00301c1e181c1c84580310061140c1c1681554809161000030340b010b1101c2d03139a07590103005d80c52400740041c012408410019003d0300d041104820500d00c141007407a4a21340301c000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 99892643 1250 99891393 99891397
    0x1030e100e0a0f06060305070b0a050a18120803060a1508040303150902070809090c0306030c0d081201060801150c020108150a09050a09060506031b10051611010e030601030b011e0b 79
    0x782e44c11555076070107100384007090001c42c025242c00e510503031400e860040c0040892140362201010403415182f1944043c22a0300b8900050120351001d5084016034101001030341e00598000b40320f120310a00018100310b031080044001c84460b00d86012550b00c1e03031070035000f41540303000710220314a802d000410025070a01c00b030b00005000703c18043e201c120b81e80621915007409040c04400c60170074400c0000d9598000380291010100360f4a084050803649400c42590094001514040c40c640f40042222944041140e040758181d5140c0c07048184401c20036560003513811806400030350050000b541011400c0125840404081c0c00148034a98400d081c00031500141c8103c120940c95242d11010700605018142e000300f0110064540401c00c07035034980e00340344d2500019004142d50301c1c03603144050050b02618611000c41c02c48404d0012135160000a080d0b2400101d07000c104640c4c1594814280020390905170395000380500056400c151000c55004088403070003405a2500401040180003040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 99893893 1250 99892643 99892673
    0xb0f10080907051011010b01030e030405060c01090b0109141f05040203041a0108030d11270111060708012c0402010e040204031a060a12080f03061c0c06080601030e100e0a 75
    0x45c8080c0d401e42040c40e660f00391342031510307241e042500341030a04403060004401c1741d08070340085036042e0380c8403d40f55250f4054000110094011103580300006100f0070070b604045039181d03200c00462281d13501c805210100c08650a0904100d080c081014401e90170560b0055400a001380d40f03420400c0b000310544504044240c01c281119000031a010581d0743c164001c100c001c8050310300300c5091a0305406100302c4060003411100042c1400350000d0551b9000d8421700301109141c80964000f40b51040001c1c003581403e01c60248628035080484020380c084800307407920050a00103e400315140c036001150403070308007003440d0b0388203030300700700010019032031403a0a80310003d91240c6d1036941c42e05c80e0400030207242ca84e124840040000c8600d500103007414044640144005011503260f44511010030442102d4034022a042c1c09007c1980041c0544031101c80119440741d91762914554407c0011000d6414400c081c154549c40441031000903c038035045400d0724081c5c0c0c801c44074541c005071200408654006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 99895143 1250 99893893 99893897
    0x41802040c11101e0903050c060405070519080a02100216090f1103010503070b0721021501050307050102150c0d18050709020f2b020a020c03010b0f100809070510 71
    0x401024031051050100c282078070540907040140c3c4d000829400644449150b03624505595001d02c007080600920a4074800d041c1341044620910741450f04640d5400c840c048c03036202d00343d038403d40001c80d212101d4000c16070f001c9901828403c07103d81e0901980203c03d01c80d94040d03001c3c0000c5000810b0f10460f00e54010f0a001d280450210f0b403010280c0c007100d0040c0345286801c00c04000501c840d4a0001d00c0004966151180d56070b1203100b400d2403050300100361040c2c902003600004a240083c0d0000751f040d00b05004c6d09a24089981c0c803010140c1c4c4220b50b104150144c2c019400d8600807030b410041c0c01c0d5001110143c003034a04003805818804440d540580c0351450f074550044402800300c01c202032000b42c8100c074011850140390000c80d6105000d11082d00400b038246503a101056500c00300e103040030f1400c50074255203500d1300e03200c060f41b181d04141c002d83c040d41c81c08108550b140b0b00070003107055249028002a0f118244140225060070000f440b1441c07078443d07800c00141c3c2d500caa503084150503c1076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 99896393 1250 99895143 99895157
    0x140f0705090c0f030106050d0b13090b15030709180605071106090f030706090201020f06010f05151207050a1112030a050f160e010e090c0a021908030402041802040c 72
    0x8209040708007800e110042c40041c0040f00c1d0f0000042c0459064840a090441d102d4845140e81009400c0010021340c10000640c1281c5511a0541010407141d00c583e01040e03490340c5805102e150600c200160580c15071048500f00720900041e40700ba17a034640d860f0b0600c0303000442e64903035030143c9070f09580075030005000b10801d4a260800340b09903900001c03100054616121404541680c2c0d0103280405880ca03503403400d05408580c020860b680b500c044010541d070b010b6070744264810314840c4034401d40d4001c2100c008011500c92412044521105421100b580c1d552074075002212950001302c0414107000420784070040d41401006207100c420180400d10303a5910342054000e0944001402c006424541c1c1418420300c1c085241d412403110950345003154811113001c004a4100c05240a46900843d9001c1441844113881008000000c42034080b42c1c4100000c1c0380b0800004000100a00400c00502c040b400602e000c1d0484072406080103014038010525400040131200c3c4041404013280e45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 99897643 1250 99896393 99896399
    0x70b0405030d0507020601082104030b0a0b01120c0903060207050c06030f0712090201020a020904032f0705030d0801150c060c0302030f06030d0f0e13060609060801050603040c090207140f07 83
    0xb09024240c1d0040140c8007030141e551502401c50f540f039140f604c180130300707400b40240f005520340c0d410181e0f0001c64200a4038105400c00b130b0700d03e400900c1200d81480c00101600e10401c3d2140c030313070701452000c1e01266407401c042e10700d551500402900200c40c21a950f005c6d001d030480482d5035140140d402120502c880b85524184040e0180014003102c20044141d8100011540541e0b00030592888880c0c0590350394103076075100d25007180d041c6880c0014803180300e07009190407a03000018002c60101e640745003c03500f10a80710404c250303a621100c2010b200003662100140040f0524021180d0348154030305040e90500d84aa403031400b40c07100f4400038000258003100300840040c400442d280c100c40150b003d012410482c200003440c80840c200520b090100c03002501885407250548440c2041c1100d00411903182c80fa200204038264500c6803200046101001243c030740382c0b090840340602d0b44415002015440d0004031800f07500229001d41c1d00460503200510b000c001442840e0340718a81101034400682 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 99898893 1250 99897643 99897667
    0x30106061206050f0f0d060603140a0303060b090603180f0613021915110a0b040f030f0f200a061401090c030b060a031d01020c01360206030c070b040503 67
    0x32040d881544284c0a8604c0f404d8141c03503d240304401c00e10140c407481034000041c104540070300100e500040a5000c407803205486110080b8005140ca4480e6800b8084550788040304600c900503450083da022100304085240c4005410b0300010740b00c00c0c4800d58055060506203a4101603085403591a0540b51005080031450500322842035026031486d4505c6840c1464000660855295140c206108034100c1d50000703a00f0400910545590055244d800d40ca4646080b0500d1400a00704070045284e81c11002510790007128286c002d0b8650365911404440f9420071090100004244a4024010000480081443d80c0920300144111291308034444d45800051422160442c0c0d00710304051030f21400540f66690703042110010385052802003201c1011000c1440754907600e009411040d0300c0014091681ea0064100e4481e40843e203a80c0030400c01045003004861700751030b1403403148030240d1507070030018a044405582c0001048a155090000640d1740081d18503090340c00b81c50340da10218013401480b13 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 99900143 1250 99898893 99898901
    0x18100f05070e030a03080718080601090b03010e071404020f04120c0f051806040b032a03061003081b030405060f0705061f030605090307021017010e0106020325020301060612 76
    0x2c0d819001040349103a641c0b001810400040c000104002ca07200703140d522424045002c030040c0c03100106a50980d40d5911664000b009000c0d41c4a01950030040341d45c41b500800328260084070200508144900008400c000095100050720106000148070104024424502c015232451003000400780381c82c00c0015108498405a000078460f110109020316003140e1940d6964002c041528003180100c142c0340040d00b8840e0743c0c4072005a003500750b400303c0740d0407041c07080000d030420094040d40c0d0781d81c40721420000c0034030007400b020303001140c01c11000c0e503c8400d40e0f003001540c40c0540203507070800382c0741c900155031503100703a01f5121500300101d24081070140500c103441e00080a911301203940e8240326401d00ca1081b040c40090310b030340e5071040094031100041c404c8800c2c181c0d0040034605400031050004d0070001c84580002101007c1c0707030000c00c0f00e084e840e4006060f0340d03150b0029402d050003000300b250449084920491840c861000b80001a02d0901031840948119103602c21801034100e5240101c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 99901393 1250 99900143 99900167
    0x11070f080d1103091f0b0d2f150a030608030412060f02090109030f050307210305060904052505130204080d02070524090307080c0f0307030b18100f0507 67
    0x1000b01041400790129001425241000c00300e04a10b0b40c011041c0b40c8400148101100650010129848202001100e0658842550f020802415000d14801600e4541010f403410f1a402c4070500020111502d049c102074101000c0d50300d000b01c0c41d142c4451740c03141150002d60002400318240f46008040041034029484508007540d011030412210b40002441070296100141c0f01403043c070f090109201d824070403a164581c0009446001e60601314101291000141c01c0030002880d020101c0c001b4a0411446401603800c9030003444090701104100502c2c01184c41c900400241c80000001c5540316030b01450010a464400107841e80e19082d000c0341440030618000c8215081940180455039030705000811100301c0c000302c5aa40d00301e006012155100e0300c602c0a0b4188103140700040e01c202c1c00190199000b0302601e0508102c0c90b800249559880c41d404020035006440000501c4542001c00d202c43c00803810080f00c5903109225003204c121458a401a080d058840d410059401c0e003080c070103001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 99902643 1250 99901393 99901421
    0x2133b0a02090c03100f081f180206030a020d05130203071505040b0a03180f020a0902090612150a0f031704080309130e03040e0f01080c0105070611070f080d 69
    0x1805815500146031900003c0035020401408030100749800c5006603014041c0c003000f858200e0594a851250780d481e81d02002d0701503445e0fa00e9180000580403402066100144128111a03840807542001400e40000303011a4800d9401e0114801103c0079002e01801459410501d000c041e0003401818101a8079802c4803060400c460a03100d02280e01200310307811504040b4a035511810320714000c401924600040031000e500e1001034505202c150400007591034421140b283c1c02036070342c0d0004000d0380101d01896921040900070346a001a1180b01c0e603500880104a4000380d80c48080090002680c9400c4191406089801803081000c070480000c2a4810180725904240c40e006c0d20990f01d01c5007420315406124620302043c408801c1360000e008a4001c2c1d4103031b070f840d00e448080708600d80d802114135500e81e1880380300020f0109030100d1110700320001a520546071a1490b12520003420440042503000c6a0070401c0c0000301c1d00303070750b0010015440f404140d542c41c00038190100a6510118000700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 99903893 1250 99902643 99902653
    0xb12010212070c0501060513051501023d110a021203040b01060e03070302041b1206060e09100902030106090509070f080117030c0102040e04170309060402133b 70
    0x1c5044076440441d9002c151441c00808101003841d01c5409800c455009640101c0c03103000000c108075550304580e00c42d54144914486200080004980e9800c4d40d110007058662a191250b544000d41350300d01404203200c4a200301840f0f2251003040c03c8440d103a04542900001003407241d40c06505104c0c103070780c8000040c0c0040c11410300d0340319a801c2c00c406105030310a1191500e643c652988060091400554000f00100701c4c2c410ba289200b03400c900700c100d003540042d030b45e110700000540c0240f0a01054a25654801035000007100500c44e0362040544142100c9004090001ea0b6103a070380001c0d40030744103650320f0100c0c2c50b00c3c16041c4219004080d003c10305201004905201041c2e000308101e0446844501004041580c8400300b8294800e8040c5001c0303035400007802140004908154600a030700c5128036078400410b51130071034000e020a07584800741c5d402c20340200b00903140124014820031200c580c000341d41c9450100900701c0c144c58002c91440a100d070306204035220380b01d03420000c0b01c01e0300002510f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 99905143 1250 99903893 99903907
    0x30504030503060405040f06140106030605010801081203060312040f150e090403050a0c020307030b0103050c09090601060c03090e16090f12060906060f03050a0c060f0c060c140a030b120102 83
    0x1d006800001c03d814081c694480c002003d01c842c0c1070380108074a800c100200004102d00000c03a41032030303003400703a140030a0510400081a51050324224100d0760f01c5e2002e44600c038000180c54406600103051154140300c0c80524403904070000c0300402c01440744141d0951143e10302213000004030003d030010801d05c0ac4e05044003915446018005912030761500c4c08568a00f800b040643c0c003080900000381d00351080e03840100412526040b514141c9001d54200c034540e190354420004011401c45466100d90000300040041d280585011080e5034801d0401c5010a500c8010705d40d0a003a044030540b10181c0850a05034405070440b00c11000741c0030b080d00070003071030b81802c1510a0709140032400030041036a4000c081d080c0f2606a001c44060300484440210f030719528104503644590b0301c034084c1c0328480410400948240a00784054190302e039038a6840080006484000c020540c502d00f035824420880006c024511408006040c1101c0d60f460001e48605a8001c1c056141c0c4095041806a881017101d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 99906393 1250 99905143 99905147
    0x1205150102100507050f0f0405040e0a03020d0807090504020304110406080706050405130905010504150f0501050a05010c050709050112060e06040203030906030c0408060f0601030b01030b09010603021b19030f03050403 95
    0xb41d03032200914501207001d850f8000d0450b414071036030000810b0094042910144062540014011500f04460500503800b80821041d02d4103841040140944d10000c40720610350300503610980c0c081c4480c01e008000e241d88034007050030782c0d104550444491801c8a1400a1450f0a00c1400c2c040d20400c0001c112442c00d014011302144201d02601e80702d8191959490441502130b004a05002d50282c024013071400c1c01c6c602903d9000482c0c04213607400342050070401e40100c00384074070350490b0402003080c19903a00d460015a052100048181d8003400307521030100d0106080c1c06140d00810542000383d500940c14208601210714500020364203401000600c000b40c1c4c0c000050b11440241121010b50325100c062040406209550002c0d085025100c10411400c50356030446201d8042030b01c00740020801030004400f152110718050b40e014400200500005220741e02509090f0b0480c2c00c0301a446440e860145c0c41c00404c6070625509000800c001c00c10181d00950b500380e291620b06040c06103050680d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 99907643 1250 99906393 99906403
    0x31605030717011e020a0912170702010201090f0309061403040b01091104030606030c05040e01020324040209041a210601210f0605060a0f1d04050106030b01061205150102 75
    0x542d00c034100755046000000d042940595104000f4448207030003074550b1040a4080c1d04443c1703600d40800c42d2580e00150200d200000308110a51010000c1d0007556000300030145500520b205a04640d6604600c500040090f03400e81041070080e01c514007072a1400c10f0082c103540d81c0c1c9607a03801c0c00da0280706210000d4005110941501d44040c000300b010542444020640c1c0599840940981c1c1400800014402c5051030841601e038156001d201860300184414242e21090b82c00095000c4104036094006054010b03401100e000200050310b0460490009003d5844524400e074812181d0060042c1318a401116040034590109403d02441440e0203015102d00051240c041d2403511018601c80c0d00030b141a2000c1c0c0c1d5903001e01d10030150140c40c20601e00405044070480e0040c00381100100d50518038502c031a0448031030842e000040107503600d20103200702c0f0280080303032550748070400480000e09184046000c0d2a243d0303244503101110f410b0a80c151407000e8204120082d00c020704013a2660b002c51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 99908893 1250 99907643 99907649
    0x8030a0c020d17120f13050c0409020a0b121f150e0a0902031501200304090902151b010b01030c0516030e03060703020406090b040f0522090c050316050307 68
    0xd281c01d1401000d041c110000050b560801d4040d543c005480111403005651540c091262015100c4540d954070045901d02410340c10054042c0e440a1504221403800e504025589480134160002035955002184d40c5504080307240c1c010342c0807410400061201d0080000c034280c1c6c8500d014103140e0715001179284460300e180c400408104c000c802861582e12002c1c203803001004a113104640d6490007a0388584a01a04440d241c005120050242e001c00174044000751144016400745140c2841d064190008200c145030403070b0846d009a060510b0100f04501601d420106401200c840ba5804010303030742111350150f405418185000384034815150b004040d12202806800c203024001c01e030f42001d807012100782140c10751501c500310801521300c0c0c0c10340180080720740c0f6466003540c540e258031840141c1d019074015810f003000061030400442c40d2100c1d0f00c4036440d44507282d0451035031500403054151410705109440da42413241c0108010f0508004440c00c0ca90741c51001a541410140001c0e00c03000184 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 99910143 1250 99908893 99908899
    0x90c040501050c010e030409050105100305090d0e0f0301020304030e0909010501060e090405100617070e0112080f0c01060e011a180105180603090604030206010b0a0c02010c0602040b07110a08030a0c02 88
    0x3203000591660f003507010342c9841040b1400c80380caa560364030700075001e8002409083e00660041c0882020b140c0a409840c0c015038000018101c401c1911358200d50809540c0304003a0301465004e0884a151801e10042d4012030281d961031900000213800c0c0f085262000e04282a0b0345e2414004008540d0302c2140c140814108031000300c1e8a407103500b401d5140c42010048440003600e442c40004241d15042c403103081141000b42600c00350b591307449a865400c4024802c22150582030700444000880c21802800860120b83e041070801c107848028a0849010350007404801580324014420199018210201c3c0850f85400c031b41b03803822100b44030846403091141903040c04000b28a29144044141050801c40c00160490f912864181010341d0782d0380044d107099001d801000004540d030603001c012210f20b5030850b10743c100c02400a0340111550710200c0000e803080c50b8281b2022450048410040507902c0c051040444070f200c00d001001742501103a032000505620410640341503a0b004510580c1c0b5980403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 99911393 1250 99910143 99910147
    0x403030e0109080d09150221072d0201030609050105101101020d0e010b100c051e07051f080a020322150c0203040807050d17031018021206090c04050105 67
    0x1140060b0750050058100d00f40c01d004d0001c8050340681d202c0c0d000e0301141c0d01c1d44541319044201c904140e0300c1d48002c51466550450350003e02d022007901200900c8800e2042180960030170780e60203a00541c1201d6060320600300c1906d10800250369040c040c0c1c1014103400e1a040002d94503080000d46c400784001b6102050005075110405140d50a505803420300c03800341c9040c8421188501004e000b00f0b00400b11a00c46d040400c00501041e114021254046601c0b000900300000100c0116100b120070010a080d50701c034100c00413509407640840c0c51850ba09001c030602050a2100d00500840001420040480d10500030000490807070f031102c0400d000582401c24044d9541d042c2803041c14900b8030300b011490304180689a14039400402402121405001e0720365a42d10303881000b80301003522102520080341010f00c0540c0c003481c0343c02160840581902c0c101950740d1002001d005004469544000302e0740030425214021300040d085500400860300421189482d1620321228040d40c010070b8100500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 99912643 1250 99911393 99911417
    0x20418090c1802070209090a0206030c13030203071203030e0f0712081e030105150c0a120c0507030c08010c0302040503070b0304020d08070609120c0c06030b0d150f05070c0305040303 80
    0x1d4005020054102100495440200c02c05004082d6109910480c0036100b40d10000b003100b0801f2030072020007507004041920b151500350348040c0170380000d0491800300414403000401a54100301e01002848001a00b4403200d940d07040103400c8505c1041011041d41003005100e00a540208081051b501046d0700c2e0307c60100c0505060b80640200900407403000304010400380259200405981200c1044074000d0401140480200f40da00510710183d29030341c0b0180c08040080d8201040441019080c03400c034041060b1a11030a1401186510540384400382d00c0b4140825034081c05007881e00704503800e00394940761a1201103903450003244110b0070016004004901107550b9038122000d4981c0050030710b5210065810441e00401d146c6008440303004104030150480740c050006010442d4004070350710681803400030160040e00380d90003507641c0400040404000100501c0011404550b01c400c0010607007001d4010303104840010b4150740a00581b0342c0d42c0c01c0026405001c540c1540d5040c941640c524039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 99913893 1250 99912643 99912653
    0x50a0c02011803050102270a0806010b07020d06090312150e040204020f0405090c0c010c0306062f0109050c03070641180102010b010e130e10020703200102041809 71
    0x40c5604004c1030f5500001e40031100300c10f5114104e04241c1503649040240b1040010031840c0300842c443c200322a000940100860030010b8090500c4030b0020305901a42012a59001b003103a1243d82c2c102c002c107848000c40c003c502103a21a1050030f048003004160464201000680c034000001e0009208030340003d86440f100c1c039001c040d100201000741950310141030001c071000c5150030040c45d044041d0318001c0c500ca41e062090060324110b80c482c0d224140c4a0004403a20030302a0740d505031001c2003001c5240714000c14170003441101c80e00c034000d1000c0d19803009004101814039029512000400c0180550f00031002c8001c0920100f1007181910b503030008100c0380001155031404803540c210345201003002020300b2000742010b0442d0009900800104505100544220b940c2035601c9030400040030100b00c9910141d804140c080255804881000d070021802d4410381c0c0c043e070402c07000034260104030040072001c00d000c00c400c046010001e5040a0a00c0c244010400d05c01c000c14400980760840402404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 99915143 1250 99913893 99913937
    0xa020f04150303050d050903040f0303030f110a0c020a1203020606100c080f120f01030c05040207060902041524050324040c0e030f1513240912050a0c0201 68
    0x2500c02404801c65692400e02400a402050595480f81e0070300c00003601145000c130844084d01d45800c060803c3c6415510210300800c50a01c1e0072131401c2d900d1041d125411040800b8011004580d51110580ca94034410720484182e031f07520260218580d213000c4c0780000e8000c134030b21341d114905444562044941280c2107512540740c0101615602e8000745c90195400600b000b024050040445c40e41d0300d4a0f14002054102424400640310805600c400e0190f4a0541c0040010a00401011488480580010341158501d4ec00c1070174100d4502c2d010004003103000d80688100725000d18008414000700c4000e01b840c403000385813200704c03e03140c0040d991800040c0101807145c400075000300408514801c0103045008403401491003071040300b402c0090071741c0c000703840548000c1920341e80c4659100c2070481d2840031001002101d080c551803092880441d4011200101180444004100c00030a414030484a014103072240d0100301042000914080d007011056480607420b181042c00318400100c940050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 99916393 1250 99915143 99915161
    0x60c0c0308030412090e090606060a0302040b0c010f180f320105011a0405060712020304030510020301050108061e0906040e0703050f10020a0801061409060d05070e120a020f04 77
    0x4140007005110034409500c41c8405562042c1c0c40d80c282d803a41b01c010080c2402403c641c00c02c51f0350b2120300020414100080541f21012180c1009810315071141303101c0e1010b41151090003580da40d502d00021f402c64290086102c41005110303000000d05940d00d43c100c01413a20140030340303080340b0031364041050160003850f134090810f00400452a155056442c5028100a10450342256268112100e4100c80b85044400b1180300030802c61a1015035a581d90941401880800070750205000002c00314505000c0038140a205c8903006030340b0f40c103107c005000410050703d0300380074040ca0310044084c0b4001c490a03182c80003040368603004075501d403c005009811f00000300440c900468200104202d00002d03410003051a00b8140c4200d07900051038101240502030340c9400069440c0010495036000341810302401c820078000e01d01d007009000206220f0340c4011450020299160204101d0076408101518210f00494100c008840d40908031030355058064006881526462840e1110b41c1d03c82e4802400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 99917643 1250 99916393 99916403
    0x90902060405060a12060609051e0406080d02030301061205011d0a110d02042c010614040e0106050406030e010e030301050f011e03020307080703140411011106010b0c070501030e07060c0c03 83
    0x15450300360703900a0041e4200d142c170072805406e0000224246011700e500c40292480940140168504882644a1684030340207271900581c0c0d03100f01050085081c00b060306020180c0c1c0046980754900301c07004110502c1490680850f601d00303030051020603903101c0c0d003030a24401101c41d802180ca03000c0011004101c02c1200400e11100007820b41c107020916000b8000311081000526203418507409100f9001844101340f201d252442c50042c0b040e24020f014804061204d8154941001d07243c3c0c1002c154a2805e81000380818004070b010824140c0c580210784504100a0003402031a402d603042d0350340c0780010300400e4170580c03030a03a0790348141e403107400d891041c0c1640c03411210408802d440d01400079441a00e0000000b181d40e40041d2905009020300c00f0340001d50100000c50380d8468a48851304074040110904010a40001d0701000d03000f04206406031890f0008150360308c1c2c0020b07005280c40000d030300030f80c1854101f1495000d0250701150000c2280c2c1c030341c100804165014a80350302c00101607000101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 99918893 1250 99917643 99917647
    0x160f060f210c0e041a040c02150c07020901050303090d03030b040b0a0b070506240d0f0210180504151202150a020102030f0105120a03030e16080a0b0a0605010909090206040506 77
    0xd0844042e001164004002d443e580d40c451100014030064440b0b0503000001c1c0c420300f071a00825401c0c0750307112010101c3d0610566448603640e107840645100b041d0b524103d83c101c049407200070340c901041000c0c01800f00710020362030040d000010414070002d105002e0181a9986030400c4980c0711501301420440c801004808056141c8034078442a07006401c080d5082d104810000318905108400f01c500301001909a45c0c45814071030030001c3d1030702000c0049540400016041e80184c1324043c43d01c4000206441c1c0020607080c0e0083c40c2c4030f580e066407259203d039044c880284a2500460300c40010384034514060400319040e400840c80207410442680f0030702c030001500b4104a58194051070003448407201e110341c02d0740c0e20410002820220000b0881c180c101e9482c01001a00030b80c400810300c08004140c801040d006074541c0301c3ca542da90300c020f0305500003500d900c0400041c0c400c41070340030340040c1c82004681d0800000030000007960040880c0640e0764103103901559641420b0b03900401d80145112303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 99920143 1250 99918893 99918947
    0x804060c090f060c120806030304090c0e040203010e0603010e032d07021206150415090c0306080607030e0f0a1110030207060c090311120303060114040b0304080c160f060f 75
    0x8100c00029032017620300e000c0c113405015030f03d03205103442400759500500a6060a04118094008144038008041402001a8200c02c2511180055070007050004100c22583c50310000341070a4409841201d8813540042000c9114405854154552001082c840700d00384a05006004e15074441c000e0003a602ca4504014448803081c00074405200320071082840c0c2900140c3d409000035250300781c1402c042810039010a005d42021a802400403940d00c3c03402240c072135903890341242440e405039041400261100f1001400d900c0401066003c1d1003140c00624410303000713484078240005842183e6201d001c0a080c40c0c10200d1013501500c40301038000e00300700201c1d05d810340041d00c4a80d0a01c8100c4155400c401c1c4038a00341703000d0040c0d65242141078059495503542100446070720208400d031340007580083c003000c00c0c1c0c1002e0708042c500c01c5100e402c5071561443c1d5210010b28003103111080c040728024a6405200452800e0740410444085041c48003684040940660b0714a510314a10500c90900043c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 99921393 1250 99920143 99920147
    0x12030909090b04050d0806032e0e0705100c020a03080a120203010e01050a1502210c0304030b220c0302060313020306101703040501200a0b0114090a0504030804060c090f06 75
    0x30b00d001d284901d00300c0d0241540141d082d10140000c80d2a950706400c0180d43e5110700850210103070102c030b8142041c00851403d810a20102c40407583c10640c00d500081d014011800c00c01c440108244e00c2d03042c00e010502d01a4005000801903000082040401007580ea001500440c8220b89182160100f0b40d100d607150036144621038800d105403031040a80c0b41e030002c1c080c4441074002c240ca4030301c1d40c040c0072070445212106c050540d1500d20000007400400c00107802210a0000d00b02a40c45a19050f03400d041101e401d000058107a0740e0100461314000c031920001d0440d01c014022a64181c0d07540da180d0341c66903214044a9070810008c0c2d014000e06c010400c2205c5004800410750f2160208402d000494078000c5e0b50b40e00450044a000ca417a0680e003142d08140301150f40c90041c07030038045800000c810b80c0c131654001001e0b408402000c5844418001c02d10307042408076802904e08008100e61700d002d0720001c0c014400640081c0005582d800300310a01d501c41ca858001601200c801d11000d241d440c140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 99922643 1250 99921393 99921413
    0x6020a050f0c0c1809100914100515040c0c0308060402120403030b100f0c030507051c120e0d0905040e0111041d06150702010f02030c01112508041203090909 69
    0x381441080d10a6603039004140b46184580940d17450360080c00110042418480102140388040d648854a078000c8049103030308118103410300c1a1040042100c1c181004c0b4080c55040440103248103609040c440d12099600c002003400cc9034151400034461703141c01c00481c00900c0303500700782082010400d04001c24150150001c0d1070040e000d030340e407040800d10884100d0784064a00e00d03c1002584400345d100100740700d040030b82500d9000740d09440010f482203401100c1c14050400d0107010403092404d6400400072031040b06209190b0b00d015007020b816840005100280c1030040d5403055980309003101d0404030940c8a00007810f4008162a0350303944891103c0c0c0500154002e50304a80160000124103080c81c03e6000e000440102c501424143c4560040d17031105110700554045210510454060b0002406050310910300220041e0350345402c10100b00545095103d82008040801d411a00140000d0304a400b12100380d800030038412168901100c511010354410070085062100391001d01c500180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 99923893 1250 99922643 99922663
    0x1b011406031515040b120105090a0201090602011401090203040602071416050f0f04051905011d0901020306010906030e0111030c13080d02100902011e02011b0e030a06020a050f0c 78
    0x1124005015020126004207007100d01010700f207a22540400e513418940c01841580d10003c0403840120b181528a40c00c4842c2141c03a0300e9190301c808480d00955811a82d00009000d0510003844615440304000d00740078818410000116170020000341070044950640c1c44083c0e200013011210301140000e195103000030712185400311000c6e800000e5918050001300ca250501506806030094917800304402058014042d01c2580d440c01021003003810984500d0307002e002109136413000034800e045450111003008013900d207203a104005210850b0303080005030080700c0e400e02d40841d504e190040c1d003902500241c590ba4003590800300a001580352680050010b400100e0001da44165403001480d0780c581401c0c00200141e0800c03a13040c0c080440b41c0e00130102890040c101740301840144191280d0868052040320010303551106055811102c84c80250b841e10400c0c5841c001321040100000d032200c0c0810001411f156001920103c424001e03000d8a000111b01c005c900c0c3c4030f40c0000c46540e01c48542d44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 99925143 1250 99923893 99923899
    0x1e0e13021f030b01051c090305220e070509010c020d0501020f0a08160c03090b030c0f16110901050a060c14070b0c0601050612040f0c0e0709050306090f0307081b011406 74
    0x1100f0a030361540724005544130300d20450035011001c041c51a001c0d0007000002c030280c3c10032400300030414a4100f010200c4543d414410015040305141860301608564083c10300410000c081080c081d9582c0d001d00a01c1a1507011a05468581e00514200c0d0091084000c64002a400450755041c455004440c5520074400407400840c1050a031408641c50120010700030003003107003802c090094000e17060286500180180c4004c0c0707450000d2441c0c40c0280c201e20b04c28110344d400da103500e40c00c0000040c01104091010f8540344d40b20f504103000a60301e540c80f4019038041203005c2e5005824801238850042060f00441c090350545501d408400089a202101d8084244580c40000038141050030840c2c3c581145d20518101036119607880003505900400103480c6060021400300382d41080020340c0b07024890075264004103c0c600700c2410700300a401071090010780c100706580801701c10040200c403440c5a1080821340d503103c1d40d404210445001500311400c56107030001c14501e500c4200031141c000c0c1801c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 99926393 1250 99925143 99925151
    0x50108011a030c031e04080405010e1516030c231203100311030307050d080108210a0507031e02010c0e030307020102070510020a020603040c0f1e0e13021f03 69
    0x118141c00c0e001801440c16040e40000700001042800e6500285400c41d1005180f01499144040d460b1040d9509440986150b240043d04104075071300101241e8138900e05a43c0c2c5610b200307000c0142c80f401d0044034003149000780000703042d00c1014490802007900f103030310581d4540001004089807485140424030780002c1c1c807404803041c0c0c120b59090152403081c1000a08104400e007160740b250b000b410f48145054041c4401e11081d400a00e01740000c2d851084642c0e90f6840c1585020030300c0c2c3c034001c150304003c1d640800241c0c3d151018404007040301c0c9251402c0c10400e139107481c1c0e0321701100d28a421540801d811544500400d07506581034010340e4104076035580e511001c506c4c5004250310380c407034803e009000d0ba00810382000541082c0d4a50440e180140c0165500c0c0d03400c43d0003040350740c5d01c220350444082c0200502440344c0c4403110080713005818550000c8035500c58020007c407444c0741602510480f80b440d039000030007000d0f50302c050713500b51a40500b40d0b010384c060500305c206086281842140100c1d040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 99927643 1250 99926393 99926399
    0x708030a020f160501120e010e0d030b04020f07020405060d0c0902030403120b06030a05090c330304150e0123100510020a06021303021008070e0f060403030e030f0d0905010801 77
    0x1031401c0d5240103a0b41c2e02c04111314010042d9901200d8040022085403a090102e20010083c450045240a1117010781082e00d100e920040c00c9a0907081c0e00352045106010b07850320010b81500341c0f02c086070306407000185500c0b0100082d0341623f11032801000c20b406400d005c80c0c0400b03aa00998001c40c4030f5200d0202c2005035030010001d44201e02c0c0d00301d400c41d10601c00502c0c4d201841d0030042d00582c07100240d45415031004040790f4480b03501c41c61a00c05040310080030b5520b10094801d8170b0001c8003c000c29085080a40e16090308032200d610140a171a2101d4941c400041c00f03500000c1c019402141010708145c075007281c106503603070440d1607a40114003c01c0014403030030300c0d65561007441841e130b01a010740e210729a81d6030000c1d00401c461320305c4404d03466008801a1200218071000e007081c1c0c1c0302d281991a0289006002007000c10101d4003403032600400c0f000585415060b5800d9a1340b50911207000c0e02c0c040042460403401d401c041c0404d2162100fa28211500b03d018001900d400b13981d82c03a200c0e07072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 99928893 1250 99927643 99927673
    0x1119080a080a06060c08090d06060b040503070b030709050d110306190e0a030807032a11100b01140c10050406021305040e0a0b100e070e09070c030903020112020405030708030a02 78
    0x100f6032285402042c542142000082c0d130620081003410300003045124a40041e403240380459900e60011651800700040a00991408010f40c4c0001e0001c414018610310304110003c0c40901e9034402d540c0144c0301d05d0001740400000c01e215444800d80501211018034060300503921301c03410b00c0b50002e07105140032251007543d20301065402d8440d81646505a41d611500401c400a00d034520909086000780740188116400d040482044d141040d510b6100c81503038402e94500b4441003560b11003003545404000c844690300301081e031b40500003d207907194503070301d0030b291a900380080e49101202e4180b402c070410080080c15400b402000c603030141e4218a654450090000b2955031080c00002d6030f114000100020303100341c80b5194000c1c0d1ba8442d100b0171690b00d0100421162003a205500428440500d0ba0754608100d020603911801c10310f04020400712a490142c0104400d00000c0e0400c0807803640c080c8070700d0450301214020030001d0103e503a07080e40e8003e215140c0c1c1200d9402401402030000c0030100c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 99930143 1250 99928893 99928901
    0x10903031b080118020405120f06090609070306020315040f0c0e010e010c0f020d050d0903061107020108070e0604080d08011a21070e0402070506040201020d080907061119080a080a 79
    0x24000d52030710b5003641d0031304001c00070030020000042203d680801000c5403039100c40d51515141d00d01940101000107400f80494100240241100314550040341000700403403001441108582e00000010780d6500c441061b005804a210341c074503009424a818114904581d0f80301d000d4014503540c803500d00304600e900444012600701e030180d0016184e0f070000030118184c400041541480200040300c0c08081d5030700c45080042c0700300400301113900f90307104006214007070103a40c2c0d42d01c4958009504c0d090443c1c3c000303050801d01602e2401002204080b40c90240c0b03610040760040e0502c117085807004006100018101c12090160303040303c80c1c21140454940d513405041d02c803980d091600644098040b07074900c501c000310050000041000f5403800c240c803a00c4d50302c01058502e001d4405440545840e000281c6030410b102c0015041048800400c807050001064840c2511640d140a2041e100c02180aa00d0010a04106404030380f003807100000f00000400109448410b6440703d0035241d1f50b00162204903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 99931393 1250 99930143 99930191
    0xf0a060b032802071a0f10030f031d13020a030e010203010807030b040602070206040306020304020f1005030727240903110402090d05070905011701050103200d0b070201090303 77
    0x2000ba4869495440c0c00380050082c400d2031042c0050400406488901d00103005800003416a50001c05002400c40456145944003054203401d8441d07a01d542d40f41c0740d0140424030040c0803c01c02d8001c541030014035042045d00580011320514000c054100c100009500c1802d845001c245803e920460320310041c020340341225a92000b81031018a151941c0b0001c50000b03008641056080200754016030310040500702450186200681b20301c1c241c814007810840c401096072240900c05445c0d440154043d085030f902c03204901c3c00c003600c420410709070b640100d096103260384921071101010030b04600c4002c03180012651407407180310807900ca13041039943c04420301004e460300c0c003041c8090381c4504280e0000c10300e00601500b501c55150580d01c0e014240f03601a040280c48540315001045003403481c07050800e00442c80310007000b65514550b9200640580c0c4465600d03000f0a03d0708020007959200c12101266811040c005401d1078407a400038024201284120040b0349405400104107801e1150071642d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 99932643 1250 99931393 99931411
    0x5011107060c050f071413050f0a1109121b06120106030b010504050409030c0b181009060914061009020c0d11030409020706050105120c090117030d050f0a060b03 71
    0x50504004071002003502030181c8162244484c1c6001c0312608129440050455650301186130980307a081050111005400d407401c6030a1105000d0400202c944803034000510013800201c90210501c088080c3c0105a00107511005e0900c84c5424000081800c0e0500c501c20801504100c0141040000d40e0084441d000c2c02203a18200501030b0b40d0181d4401d590030f80e41414601c1c2843c0e034400001e010354528070421000107494480e2601007107031400c1455000107424131815540070024100540d035071130000d0342c0805c1688920054042c01155800b420000c1d81105080c80d850204040071541e880041c0c0e00044c3e60a01c00b440025108a20310035643d581e003000014084038440c0240480b454a410f02120070140001c020002c0d07400d0700e51004101c0c003131241e0b1000c94550301d02002c1040718400c3c406034215581201d450034100740c2e6402c98441c19200d0b000c450f50000300c0c0002009103580909010f60021070700d06800e01c0080c003040740006114441e0910240500350310b940100801b40030941e18641 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 99933893 1250 99932643 99932653
    0x6030c0f18060d0906050c09180408040509240105030c040302090414010204090b0109080c031c030b030a0308090d11060105010c030c05120405030706091a030406020c01061509050111 80
    0x24100c0003180c0144403030541424400e00d40101d84000501c280c0c0002c0d20380c0d62040d03031640c0b540100300c55401210b520800d04100d80f030804260001154240c0518030a0801400d1600002010004240c0686010706800b5125100e03030714181c0307803404120144004c100400c500c013550b007008940c400d4040340d100f800800c1e219420140b0307640c01d100780307100c018004460601c80d0100b02c0071103007024070161005115402c800706280d481400058288142ca8000f500960000d900b481280d840002d13042554080b0028605248084510100c0081c18141c207019810701074840750200345070380645a08d004040e04410740304a07840c940c00c1642e000c2903c2c200980184c02c840c004100c1c03580984050004103004c4c1c10320100c0544165130351410120b07004035500b61400003080600083c00c00b0000302000e00014100240c20703d04140c1d00202d1401d084a403d11007200010000701000711a8040c1d03016244108024403010341c42e01440c00d05140100b040c00006948044006900e600ca850001405175059010702 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 99935143 1250 99933893 99933907
    0xc0e04020a03021507020d0821060d030f12060308130902030f07081305030d05090d0804051c03090b070c060b030c1305040618030503010906060f0203091212130302090606030c 77
    0x201c501d0810b1651200e503113006100c1d104c0580c94900070710318450b1049044070b80d6030540280c50242000c26400741600645c0d40d50810104d52141c8100ca04400d40609000c01600d0803080d00b00d41e0740c1c00000c0c0341135000f410322030000b0800840c0406401c0400c0e00241620440c2d07110403c030402ca000031129040c10380c00c01c1c004116214004c00c07040d81c000c400e01c90740002c26115511064519805110300d004126550000c000c601c200510100c4609040d9141224080c24951100f503684c0404400120401000e00100d02d0102e0095002a038020f61000c9007080a142c0000068010401c1cce08060722002c0c100ba000c641d5602e004200c0030900000104692207040c0070294010017803200802c100d503074070382d2010340e40e0309681c01083d4144001e103e580d034660390398100f410110075282e46030300130402e1140041c0c5180a8035000f0007541d5100360140c98501038030700303204041e0786072507000b80e01c1c1e11030110f0018803284d40030940c001e80020f807402915011f440c0d0b00d40100340407091100700c400030b0300d00100380510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 99936393 1250 99935143 99935149
    0x50402031b010504090e0a050c0316032004091101110c150d020c030705061e040b070503060102151303030e030a050a0c060902040f0b010e010c030f050c0f16030c0e04020a0302 77
    0x5001c4151040c5031450600d503c40300307503c0855094000030089a440550b0b203100f001000c019503000032000354094851509032a01c1c0120340340300d501000703080703403120128042d00c0d005c1820260250711009006100810300f5050400c0c048070916075850010300300a051500500000400041d1550050000d440404031544001a650003500c4202c60743e035000c01000c285030304108040c0c01000d000b40c0c0a4503c90501a0404904400303403050980c00140500c2084007050b01400e0090b40940b2a0030031560f2a900c07840104e080111800300c91114050042c02d1106c049816154111310314803a0701e007008401161500a079036405130450110000d5010400d03c0200ba2081807100400c62150001082d04e84481d80050255012103502c40342c501d0359546010020b6034000795954201c0f4080c01c01e8850380d0b40369200104810f40e90588041440000184280511010805900320803044806d44481072070307045060540103e113101c161480104000d012544c80144202c4900466004010541d2140b444d828 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 99937643 1250 99936393 99936433
    0xd0f1a011514040b0c01060f0f030c12030201020d050703051803120a151206020a09050f0f06030601020a0b130302120f030a0b040209061c0f0b03061503070807060302070302010f05040203 82
    0x84900c030b0300082c0310009003200d07180040c15006001400100b203c030b050801018814180d40c0c8810101a589070003040482c04d281c0008065408001d0400c080107564201a400380c805c0346d80300d5002600e40300c01c00840a5150748590b002e00e00307004101d410322420f194595507a02031102c0101c1c40e050000041401c01d2220391100c0894140380c02692044e07965800140c0940c1407050050315100c2e000580b0103603040d031101200d00a0501124400c600465110205284c1000901c0c9070f0302400c800004145180c1c02040f500c141c0a41c0000725544c0e45c0f81500340c0108201143d1030031009071050f10004090044044191840807a003072000c0c90455681c0c030b480001914a1300442500203a0030041031510751a0034000f400c01f1000700d03c103c0141003211458070211703964403107a03000041c54000c520004ea40c01158050300021f80c0c600c0782c0418101140003904105003940200b48a01c10040000395090b0550054203000f8000d400030809442c41c0c0450713105031501110001d5041c0c100000480302c620790412 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 99938893 1250 99937643 99937667
    0xa050603120c011407090303121d0307030e0f090f150112050f160201050615030406060f03030f02010e070303090312090503010e070503010b1005040e0702010b0d0f1a0115 75
    0x4844510940301c5034074805600242c0201c840f079441e142020034a081d8011003582000b1039280030003109296442c008c20000e800e200d82c03240c80d6129038940c0080703401003d840604032030070016283d8644c0342c0c0c071b07010705001e0042503501c0c060280d0800003c0940f030a000c034148156281884074099560b50040081000c4441c0720304c03410300c1340074000052010f041d4807601e032140078140d04035541402d0034102610302910340900c81086a04200c1040900d4860841c0d8580000060303200c5c070f841c2c1c0c44500e0030f81d0250132150403500410002d40c000106141d840200c007000b00700160000c11180c0e101c0460180c44040340e01000d0046000c44808100180009a2884441aa82c0713001c1040036120230000c1c1c20349061015000403940115000c1c4114502132040c400203074011078260300b00e0b00d102000074000d40034a210740f0344102c040800003900c190007074000c101a04802480c0508407001468202c100d10303209041920b0580080c3e9111003110414a1740c181070700d555012900fa0340102d0348084402c011109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 99940143 1250 99938893 99938899
    0x40b0112060f020d0c1b031407080408010504050105040308160c081b0a110301150e07030c12091a1311040c0c050601080601030318150302070c030f06090b0604020c060a0506 76
    0x140002e800b803510b91014061a034030400c40405e55181c8010001c01c031461a4112860201501045c3d0300000d0700216150003044280299a480d14040e041035205402168812043c5509010030442000010340c001d910440c030a4490203034545036403107200350342031003405a400460039034002d00e40400e19001c06040c080501d82c0c8003149180c01c1104180c104984103100300d80004421650201d10700e400e00901c40600100d00303207080c00e00d18000004011810240115040c07660300d158108030184100b0911811f200007a8060020240514000000940c2e5489140a000c44903011640035003802e0050090705402c40d204040c3c0c86000713020480140b000d00782808c244407542040c6000102d003400440d000700003034005840c0942c503508016010a641c000c4540c001d4020b46d4090100003808102400d04018510700161185000d10308095520450340000d4147e1624003800700401460741c01280c0098490300340c060081e1140810300099000c2c01904c1d40e500d800c40c50010714014603981c421130b8401c86c02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 99941393 1250 99940143 99940151
    0x604090204090e190b01063f0b01030c02060c0c1e060a0609020301050907031d01181101030b0306040b04110607060c021b15090301110a0504231e190810060905040b011206 75
    0x465005d081c0608016680704944041078808c80268024440c13120002c0003820b0502c40c1840d010320007501d17104010b0152040c0c442c0031600c00c5400b00100f0880e0104079a02032040c0b417044005002c15600c200c12a0703500c6c0020f0130000d000c03500c1500c500950741200c01c050001c1036203480350003096002d4821048a405070080c045644241140c0034010240b00310031205034544024200e0600b04403040951400070306060800d03000d00c0094030006481a0701c59001a0144100d440d2407804540011030301c80920b40c80100401c44800740415035020b908004a10f80845031003240c02e8032081000c00403c1c03840b962014181c6118010324107280700034046040c0c01000005c401120003e52405a001030003140f000860120781403000c420550b1001e1075440030103000c80f03c0a50340340c001400e04082110707041c1d4820b26201c1500c115440b92901054044182201d408165071521115540c6180c5c03d091490b1440c14a5000103d0103964400e00d0302403900144210041da00b00001d15030f8589c1c108074111501c681c0c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 99942643 1250 99941393 99941447
    0x110315010e09160902040905010803070c03080c031207050c0f010c0e040e0309090c03010e0708010305030a05070f150f060f080c1c0804090c0311120103110604090204090e190b0106 79
    0x30480a005802c21210040c0c545047c818035170b040321416000ba0449900c2005550040340c40000070001b101d51011030245d036140031100c4182580640340180704210030b80d406100300300c0e80040240540642500c103e5080e14048115036080ea0b211b0300402000c94010100c01815080641102c049454418101e074509180c507000700b803a99000300d4135805c0104000c0700521100d0490700c915038006890749040320140d4110340740c10340ca0f4410742c80041c1c103116001420300c040000c1603102d1440740c1d030020344442da10f0404810007409020b6000c002e02541d4904800451001c500113102010b481ca41c10080030544c0052040c0303c0003444800740d103420300707400c905d1040018110350010130143c0081c5401041a02e0208409403d840305000c1c0700700003480070700003070140884d007d004504494000d42070264482800340401c481d8401c64100d1003005000180119180505810000144c8260021502d80304c02cac1c0c90007036000c0701014a00415403032070b51b0010441144170f10788d1018005881a500c49180710 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 99943893 1250 99942643 99942673
    0xa2105030c0d0314190213180b09010609030320070f0b070c05090103020f040c030b03030a091a130e1506040303020a2d061109090112110315010e09 65
    0xc40c40d0500c055219400e100c2c1e0b0076505004468190941e0091500c003800c102040500c0a1100440d00e03008603800710b41103811044051260008101201d04504450b00892001c800b07032400d408254000d1544c0400043d00394868141d050481ea01035881408101001c284a500c5820220300c22526204d016030201d110300c02c0031240c038010301c80035008541c1c0d18860301d0b000b01000d58503480544111024001000540c84402c8102d104034011240000d0460702c9010039401408541c0080d0380610010842d13002860304003000c03d0603501c104860400169205200d204c2c2c6100b400c4580800c41040342c020410401c40c025101c0e0050301e030703060107090340c40e20b0804a0480d4116500581c0181e03c9002d611081c400000c0102d103100400894400c8541200b0301207032002403032500c3c0100102e9458a0041c0741074815829607184c0035009044800e19692444075012181100322f0503144800050705504140c540003a111074854041ca0f40c000c0c1070b038a0070862141c0a41c000f000300c080c9000d07809103040c100d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 99945143 1250 99943893 99943897
    0x70c09050903070c0e1513090605070c060e010501031703090c0607080a0305090721030306030b0a05040b010602010513240e030a020106050a05030615010909020a090e090c0a210503 79
    0x241c400002540c4811083c2069000392495134001070064a042060000e01400400c2d010000350080c0e5424994812440020004008501010f0001e170b140c0b200340103420342c0c880c401d20705850048109000817a08840c0540c2210400c0c4001400d00d14031074450110080c544003d9980040d0729001d07a034441d5094030104071142c0c440a000c80d008030001645070011501442984d410022610003045840d00340f4440003408900b400f04080041c481102c05401c0501c00d42021020355404900e500b4281050341100d40035000647e41110398802100020a080d0303c140720389072040030f00e050101c0c440f50301a21110410a420150180c0c50320500d2000d8581c443e0500486000202100040d542e44000c40402800c40310140c2006104001c030325810044d940d800110703160048501d00100c01070540e24001a02e4540b8250320a800d05800800c8030030015401c0711900d400c8600d8419580b91903910100d2040c2c42e0120228000d0b884000c8030000d02541140075046a9a0001d00710050411034080e1100c0c2e1540d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 99946393 1250 99945143 99945151
    0x402180a09030f0807020a021302220e06060a0503040b06010c1416080a15050c1b010501030209070804020616030302090d051c0809060c030a0b1302090a17030d02070c0905 75
    0x101e895000901c205548045052100300345858250344a0a140100030749440350300801a00c43d407241c20484400d1000c2d0780c125045c0140d070070151740310b0a0440c0310003040c10400c1d02c11907184024030000a1010b0628074101c545588160f5205450350307550ba0f4a00d210701d48040c01480c10040702e400e41500241080c1c0c0e80744090340b0100018a18004a4414041c0043e01d40c0c0201c80190406003a4400203010a0310000780c185a01501140d03030354650851100a010701180c1e00003034441d0021020307270640194803290580c0e0013a07a102055035160a419122204161002504080e04010b03080c010040020a61b0721548603107400361034400d041c0c000031001e18261405980716003101d6412681e1b80442da0440c11301e402c90381052502e85c60701010040d1070715001001d4a00c103040c00400070b01041d038541c1c84041400c42c02051801001e80b1090103030000e4101100c5940108851000841e006a60603400c00031105080f00540c0740c0361580600300065000a034080b150100da12001182c03060361f5002e040c0c85 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 99947643 1250 99946393 99946411
    0xf15030905120d140a020406020d030b0415120506090619090609150c02060f06030705120c060304080901020118020a050112020f03090105041703011a1b0d0503011404020f03040b040218 81
    0x20740801480314404c03144040c0548080742d104100070089a0b4020900d0343c41c2a82900340001d1024080010502511402a91602403200c10101281d14120b40c841360711854011011540306940b41c034030307940c1c1e502001c3d0f072000582080c04203000d4409040c0e40202c0c012500c2803101160310400350303442082d54224000342c192086e4513220b1000c0d0b034541c104815548005a0300104d40f25003010300210380c6030705c00b81c0030746401802c401c24641e00030b040030829802103000190400c0c0d039a1510741040f041c56003088182038015420710054245a8101c003040c1100d550700108000c9146103000015078241c00d0882001000e41e0702400303200042604003010350700c901281d1001090304d20b031915092849a07112904c04c540c0e244140018450307441c11101c55088000e502440c20790b00c01400041182100c06003048111a1040710303450f070545507000c000b660480301203040012160642608010a90040e00e4100c07442140900016002ca150406c42a410600281c81004101c0840d082c810964100311000743d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 99948893 1250 99947643 99947651
    0x80a030e010c0e0301140c0301050609120a06060f060215010b1303061401030302070611060f0415020d09030e0301020a051c0b06130e01090908120a0204050319020405010f15030905120d 81
    0x82d42006c1c0100b04100f03000024080307091500c0500e425080c00180141401424003003001c601a440342030700e43d10409100740844a0112031032920202401641c050303010710b6103c031030f00040e641c1c0c00041ca04040300c03030711200c40356243e0a005020f0529040000b02c55003103482620004007052051140c2240d83c90fa08812046030340c11420068a441c0141d440b800800c40350000b403049a94000c1000c0d50070854403000c1c0106900c079801c044117403189400c00001000d01c0040c4144465605900c4841128400e4903031a1000a05108140c00c03030040000720800308200700900b0200b40500c00018036410301da00070005e0011890000308096821149006030800100c03a0700b4000d0b411048211401450320a105001640342942c5030740e41d6000340080d84a072003845501080c3c1044498040e900901000b4080302c030442041d6060a090039503a180270382c0513618240000c112103c00118081c2924079040030708a811807000c80803001852111020341e4980209513005815100146c002c1800c44962a03005c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 99950143 1250 99948893 99948917
    0x11b050318090103050703080903070302040e010504050d030b030a0311151e090c0a0501121b0923090105060d111303050c0108010f05190302030a05150a110403080a030e010c 76
    0x50707152030900492069a014004100007040046d450007643d520042443d2105406008a0300e000200d400083d4850b080407880d111003001544078071b1003140035500b01c071100d4a18100c15411546441141c54154010b0859180800c2c020080c00c0c510130840c1c000c45211503400c5040c1e4442c18800d5901e6440d040c001e42c0c401c80c05003010745510b03801240c04e10240131241c403c880003e030349003428461141030040c108070410320001c01d54080000c001a411040c00d0340c28a69000821130316544c0613030305500304051003070b0044d106035078a400f50b6108090b01e070200381d07400e0808101864100c650881021511074528200d0f038101e95024059264a85080220032419444e040d41058460a502810441d0790401000300d007480c0c20b1038908942054450080310030800322201c04c007507400c0e0030194040c4180c0030b0000c20003500154542c804416050804a16100c1500b0007054510326880c0c0c03203030031109100510208880e10000e00c05c1c80c416090000f8800c089503100c600356120000310714003041c4820011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 99951393 1250 99950143 99950167
    0x203070801061704060507020a0f1b1d01030b04140f0d080105010c21030f1b09050a08070603020307090e0906270a080f070503030a050907050d021e011b0503 69
    0x14074054905410200d104800012608140b940c00520281c101038440c404100d219000344240d00c20250002c100410000c2c031030800420507805140300d000c135400005000268500707070500e45590003000c6155081d0740d91039500d890000441c05001901d0560540c0042c1c550300c42e0400c1100b58042c203110140100c1c40f021980988503000c141d01c0036040c0000e16509000090000c0c21750380680c07804c0030b500c000044104000324010301d03007200302c851028a064407000c1006110101c400a042c4250b0340c5030a415202d8003030240f041c1d114442c6041c103600608041c4040350098002d5a0302150324604420b0b842d43c1da0942840329581070b41c0c0140700b908100c09216842d11100101001010a0980078500034000c54110381e98110b00000500175501c0860f200a0303088480d000c845415400404a0b81ca134248032601e080101400d0321000e03c0c0380304003900041c0c10701301001c007184210340081c0b0750300d400003410755040602c1608a1360031303040007544e00504a080c0c40d61920824081d001d00002e580300d802c010350b2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 99952643 1250 99951393 99951407
    0x50d1103010f050906062107030b0f01060e0102330103080306030f010501050f060c1e060717040f020603060a0504020d090b10030206071218120b10060e040903170406020307 76
    0x2e400d40d90741400108102000700080c00c0350068002c4c3c07002c00303080480b81040500340d10080702c102d099004920001040c0824255140d0007401c108da84e42401d030341d03075000a544203c0925222800360b04822500e49828519410f4052840c00881c01020031031a00c480007a2058000d03041281d00210100c1800f5080c10b040150b40010071116008104a505001c0000d400d0740000e11f0151042400280a00d145c0c58140301d0280d209070070103400c08625150408031511814215071842c002500110951802c11100d20828010754000300d04040248a940070701039a944024181b503040403640d03000144a8545100500418901c40030001c7d9075025890010ba50f81d2003e0005400741100050a10144c0d480c0d00840e0070b156400f20f07042c0c4c00c2c0b590901041d10000c2c10340100400b9080100c4001030b4034803e0300c0f0203070011807050642005076542c1e5400410040c80c10700a4200040070354500a1250419034418404a40031313040c00342052800d00410b11042004075000c541464012050000d006d4000c0705d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 99953893 1250 99952643 99952661
    0x40605070605060a030c05040b03030d02070b190c090b0702010c1718030303040b07270f0611011415030a05160f05090405030307080a060e040c030b07092904050d110301 74
    0x504413102495500c07500950826402002e1182d81d82c0c108204059600708125542d00160a00075500c448183c14050380c6210215590350a000340d084945030210810b10500b01038101d5603c03083c0426040803900c911641280c032041f418000140c54000100755085e80c03170a0000c0c1e20300391303031540c44011000c40045d20380a158858004d07801072007400006044981c0f0305030701045900c1d16103d000001c45c0307258001401c140855401895850001c00d141c0d100300680d00540b003490711181180384110354058203c400105100551110240100700014030750700000540c25402000c41d800d0301002e460b801e0401c09070782c2c049610380380d180d402080001c814100f0300009109c100c4008402e0310f02602c0301522844020119000c102070300c80024030750041a4070003c05040140b00104052802e1f00e403071902828a40001d40e201d00980000501c581e01c0344032010182e4008101c20404031000e103189040b00240c0c44292698618180700c0484d031900e615100540040c0200d002c01c3c5400662000e050840391501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 99955143 1250 99953893 99953899
    0x70504020705030301030f020402070b0907030506061206070c02060c1204050a06020102030f010b0c0307120c020103050f06060412060b271308090d0302151302030705030601060c031209020604060507060506 90
    0xc07200c5030104002000b41e9045a80140e041d02801c000c9100090080c8620100103004200030b10522084240000b52101034a02c01d0044604540b5120204490310300da180300d21a45600550000e00081c0c1b01d1089d4a880c179101a05281c148140010710905205402c0d0280c142a00c0c040360030000e91902c002074070000c203003d00085286080c0100302d0703810300d030050180c404000b200107200e1184a40400450340039541050080020f50a1441d00070821107400c64103034000790400c80070800511405000a01079200103050724601458617001d0252820030340d0055070b0490b13480364480c0d625200c11441040412005c560f5200042c3e20310b410380c99844020300310300510000c6007410800204d1040847d1b02801c000c480c01c200d0300d003841c0350492034040704207450582c24414409014042d031038a8451044a4800c600f03840c5a551100149552080709128800000b42511506000300f07024260101e502c1400180100d00b00600b03401040d49607000c0e91100c00002c10014600302444014420141c20040813 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 99956393 1250 99955143 99955147
    0xc070f152a05030f0c0702060d0609140106020d0e1f0e0307080d0e13020919080f0a08160f0b01030f060605010201021812010f140703060e0408040306091a0906070207050402 76
    0x10301d0014542d0100511000c0044d42c1c140102c3c4240d0201401e40c0e0003e54010003ca54a60018020710080e0605200d0b4181c0c0c1428800c0428001200007034160603a9040c0d0700070000800c0c01c86003140c003011090320b03540c1c01403012500c4810500b160940f688450070151681420001e0315030506140c103000750b020108a4000180c00300c4620707403240c0c0d2042c40c4141150754884000d600c4143c0b030020310070441c03555030043c1c1849802c4c081c6201610100d00300c4440e2000c0e04c00e4214070601240d00c0e80e03580b07100105203c030300300310082c0e0044036089404811409448414210071440e500c2c0c40c00c078502038006980601c00c0405500410006c1d0099102a08081c8000e509090a140c880c07001052031200c2c448c852408450001c019034425170111a403848000e00900c45506d6860010300701a109840c80070001c1d05046021403100e81e08140c40b8050b540c00042c3d81c1c036092a41e11900010b10500d1411504e02d095030300602050150303d10700d60b000d01c1541020786030f0390500c03820180c94624940d0100c0c0c019401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 99957643 1250 99956393 99956471
    0x6030c011112070311010c030e0106080703030905060705010905030a050c2103070804320c010c0c0b07020d240c0f2a05070602061501030605090c070f15 67
    0x10038902940c0002140c1d02d925900340346001c0c1d408032910348044020b5840c294060391881e50640061200000c0c0c10000c02032240ca034100d071500c130145808043d0214071100c00c01c1005041100080c1842c9000e0000050303890300c0341d900c183c20340d4031410900e40010004503204100c0c07141407080340c485040003200700da540c4030086100c02c04c1c5e0100500003010300051300000b0b4184140300035081c12608205c0c6410304c001c8184043c0219500440c164103000d4441e00382e40c149254020700e481c041c555004808003081e180341589819141c2c0c4144001c85e0841c400180b03038800501f07105029150321364262001e034200041008403030708440403c4444d904209171010741c03620564111400a0b140004004180c0020701d0400c285407141c291030720700500511034250f00080316a804105030b409240b0b0900d5000c0e16581c0e010044069801310300a0541c080701070303808514410081002400740030303c076a03414180d034485a1a050b001866080f030103484070b600c13200b0100c041100f6014014542c40310000348110303151 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 99958893 1250 99957643 99957677
    0x30a0807030e0a020418030306080304141005120708041a010e1603060503060a0207031e050d0506010c14010501090e01020705030328020715050601030e1c050d1406030c01 75
    0x10040d14030001d1596900e01c0042d4038000348048042503401501c240007030001000305080c44020104182d00003490f00401190110380030044070300315003003081c1d061500d441c030008100c22403420104050903c602005030b0811001c03003031901840b07916151160000c1e443d05090846250b16001580044c0703260010040c04900c0d4074080550304a07031080c42c451030031044414207800400041d000964544102801c11103510410f4006100c61403195450041c3c0038584070001c200003c507604414081002400020000c030b42e071381d0101d0313444001403601c4500c0c85000c1e181c9040c10102e041c032184059450b20300600c9580c01a004550311700f00c0c070300021450491183c9541d601c0c0d00000e01038110b04d246000c00e4102c8040389030502212210796480c11540c941482ca00301d0480703841c2c03180d092100741c208400501c807503010f0b10401c10110755420103031040038244c084c581640c010440010741030180910041d41c48007110300c03568040904400b403401080c1018401c05190a2601c0000c60400100c100006034a00d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 99960143 1250 99958893 99958907
    0x111010c1421040b060406060c0503030103060f1d07060206010f030b06060912060a020d231b0d0c020f010b0603010315090503091002150c04061403041106030408040e09030a 76
    0x160049025440c1d80b40c0300c0481c0030903201c0700c00010340c250241051109221103c06007074003555003105c040102e581d13115016519860700307450142a5800030310040021900c990031a6142c90006c000025001da502081e030703418070242c003040c0c00c2a0352200d20140641d85d0100a0540074005400c1d40149181c515070b22042a41d800800d207034018000881c00690584070601c0005100404c801078518510340440c2040c000e401030141c100b605818460b06012014400c4140b80341d810003243e40e1440c5603a09020366099404141400c61035180c10020281c5c505103d2050302034100e40c03030780580220a15002118250b400c1401010f01c00d440820040001410502009000707449841021aa550300c0d41080383c1540500c0400c3c0390400d0f03d2903100c080c03c5601040070b40d408903800781c950089456220050b03065000b5801124040381ca081c15048420b113106001d0360340103102340800c000603080310001c950250000e803004c5882c508c000ca014003d05144401c8150300c00c4e6810010760800400e400024104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 99961393 1250 99960143 99960167
    0x2306010e01270e031b010c1b0209090c10090602011a06160314041202011209050c0d0c090f060509090309090406090227071404051809070905070206060111010c 70
    0x21291010150b072003140b01d0300500c0801c104102941d481e584000c0c00348854030340042c0d201295502e0300380f8502140c0e004031051084c6c44515040800448200d41c2030001555018040302030a100790303045043c0903911840c5141c00e2070580e42c1e42d203d983d403421001900390780d0501070001040e21400030708001602d80340f00760396500c01511050480311141d0308094851426001d08086030300000180400d07640d180720880c1d00e900d0301c00c0c1c3e191840c0885940a050440b84c01043c000c1c01034102964400291030003503c0840c01c0350080841901e82d070350354000c00d4200d546903e080b60545494110410007864001c0b4220342c400007982c043c608c0c003114200014104840240010b01895560505409540361510b850010b44100d2140510b03407504c0b9441e880c0901c00440e8600c0c001810101c41201c1500410240c2d811250b001d0041003000b1070780380b42c1d07201390305000b003510340c1503c6130704000260300b207a6000c0d080c000c00c1d46401034031550620900041801c4100320700c0d8085a8148044650020381c810042606 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 99962643 1250 99961393 99961439
    0x31c0e0d051e0f040303090e19020a030f0e010c020705010809030703030f0b0402180301060f030f02060c03070206070c0509070f051207020715020c121908030a06032306010e01 77
    0x81c403030040300040c0c800030303a01c0c0c1829820003002c2001c00484120f94001c2c0241ca0007611144462a602d28038148082c2c0c0c01c446150207100000f00800d22421300f500500015002d40c200400e000000071141400c07215100e1804174941c3d101c0e18046c00b41c0d50140301030780103018286800c40f5035103000000300340d41e03209583c0004d0415a590140d0107200d00d542e4844000d201009000f95501c5480c800c030890000c4802030341505c130754030302840011540b00c59241e040403250b0202c91100307000020740800a00d178000305203c095502080140100580d9204001d151541c0304046881c0641c3c10312040c8014000700800c5030b000c1c02030103414040d03502e4019040d9038110840c0c100803400f076070f00c0010490030300b0555440f200f42c0d841000300f00a00240c000c10a14100d101c00d455600c5240403104003181d69010781c03040381001183d40341074540801c003c44002c5522680c15030001c40c079503640342c1c5d6406500c501d200c8412901c0c51001030020795a01c0911a0303900405171041a840ba03541800c04498113640ca14003c004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 99963893 1250 99962643 99962647
    0x1401052701031503080c07090b01090303050705070b0408030304060612080412020102070302040608011d03040614031b030115080603010507141e0a020109050f01050103030e01140d050405031c0e0d05 87
    0x3007680300303412580b008035164500311500c542c0d80c94100901e4200791408803503802510310100300a4018494106503542c142d444880e00e07865614280d0b515440038509403220300402d000410311040141c01080101800d400441c2d880c941410301d407048440c2600301c2204940c0165040000c01c42c075a042e170f82a2a10007100f14103007005840180d00e408029403009402a040c40780c00149140306501c00300f02a48a00c4a0300350006140c4c4600c0e4603482280581c0d40819803940c14a14030b01e1619002e50351140d15001c1140011034030723030340c40c5800c1c0d007007680034036101500c5600005041e980403411640200e0f007907000380031070f04141b0f030083c04111001c51090749a03900130508202055801d0004c005001ca0a586165074080150009029100752803040e140b5114036400b80d203061105105d82810ad0740c141d50356020011001d40111491035010300005c00c03500c0144004641d0710001d105060203184117000444d520b240c0d4030b8140c152070441c1d0710900c546070301d030030031010180c440880d0040d00d081309490119 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 99965143 1250 99963893 99963967
    0x8010b0306010c150204090c11120c0f011e060b0702090604050a0209042f04060e0405040303060305010f14010801021c05040f0c1815080309010c05010605040f0501140105 75
    0x81c0c00000d400f0014020706100c0e807200c100da44a690040041d01c00032502408100070101055620300c0c5c60740451000c0707030700c4103882e01c0706044080064001c2603981400c0c0c1742ca8115103419642540c031514030003165140248080020307203089108500080084881d00340c18204190005120b455000340418000e603215000a81010f1807981181c00400300144100701b428041c02000c000864410154088041d10078940d560480440059504907003d96540d0654481c1800900c800b401e0050310890515880d9540800099028086c400c1030551301c600c0000c000f04144a001440d20041e440007140748d00c1041500041a50951104c92550314004041066116460414124000200007800c5840704610100d04180b07103880c01e1814000202050142110009200c8030061240c420043c2a030b00401402e2183d5006090f03082000707008000001741d107a62750012400b81c400c81e075040180241d0343c00040c4006000860407010191080c0b9195040c440700c184051010007000e6141101d0f41c0c1003420b05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 99966393 1250 99965143 99965147
    0xe01020409150e01060201090206070f03050906030109050a060b04080d0e0607050f07140604050a17070801021b0f0f03031b0405100f030e0d02070b070302010b030a120215060108010b030601 83
    0x21802440c20071020008000d001005030507406a074000d812100c04540000a8824414080d10001c55001030809180414a5030340300314001c011071084090020030300010b040756076104065070003041002e1010640d454049541c0d0200c54164203c0801c207030041c0024001580002002d9405075614241444001c5c80710001940702c0c01083c6005045d481442c03a0202c0380013000c01c404088454160748060034504103010040c042c01940030703058100046440400000302c545032072004101c1c00702e043da02e1280d180c490305d90036a8130003010086140c2404a004410710410091010000800005860404e07601500e90341c03070b484040e00110303a4548003101240400d054504440040c68001c103028000c001c0f20001500c180300d0282e20101007880c0550f6800501004210011101c4180e80902046d81c02c0490303600280c0c0004500380c08540d0388103c011a41d4404104017124140034142850788860402d000a11f040e040c8181c190244840d01c0c24010640d8118034510305407141d0810f29512a44d4070401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 99967643 1250 99966393 99966397
    0x4060e071802130f030f02031209090a0b1c120e030703080a0c02060f07050604020a09090302150c07020405010b090a0f0b0412021c060f0501080f151503030a09140f03030d0e0102 78
    0x130603000700948500008000700d124494622074400c0d42990241c54041503a2071003401440750658110150000260b07105440d03a01140001000600f05400c102e0707203681ca0410304920b010304071210781140992482654004104a2040314110004d280c0581140d50341c0382503004803440d04041c4080040c640c01113507160415a098080b0000304551a00b04504180baa1558155070681c09220a0000440d51446a0085079051601500202128007a8a0507840041401042c11010400038020040180d0b0750b80582402820302c42581519000c8050400c0039a401940c0305580301000702000700550301c0600140d41c1111000c1550303860010311070000c514505854850745010100703400f80001080520b9101c001c3c4504000f504000d0350381c888144035900e1035942c611a0b810352112004c04091040c1108040e80712070b0000c1d0091022075442c3c042071658010300b500402080d40c01c0000c1c05443c200011640309410111142c00d02d02c0301c50030100b0345a11611900306909170720744241880d04202501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 99968893 1250 99967643 99967649
    0x6160305070b0403020c0a0504020a05070209041b0b09040506040606020a081c051906060e010c110609030d02030a1b0809041a030d0309020102060a0c050f1309050703020304060e07180213 82
    0x103000d102d40f0301494003d460700300c113200c464815091000d0225a60400e442a6104403100d6110549003a0f2181c00704819600002c3c0100e030550f0310301050040030010414082e0080903c0001140c640a1030030801041e2540200124002c900d8004100007869002036619203054014000c0da580701807540d400a01074806500308a6628200300900500311102c20b968001003081035410416103858080480c0d8040c4295510381c0021484d014900203e221038904120590004003018600b0541c200842d00302080c1d2241880543c00200e52946415042a8090b580b099aa00210000f903040da070f82c100103025041d03100f4080c1e5581c48028100c107004216035117500c2c0740103080729941c00000d04010064503000000700c1c0103004602c0031812410386402030781110b41e219100c80b42401d204000900301e0390044400c60008075114000002e0002071882031a01801050303030007507030301c3ca00387c103108050301c084040c10140c941c0045004c1002542250350008018610f410240c0d942030700008000c01c07410150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 99970143 1250 99968893 99968903
    0x1e150204060806030f011b1d03012c01020703120506030a051506100e0906040b0102160b0322030806040c02010b1f020106051f080406141e150616030507 67
    0xc010400582000c0840d1041004404444214588100d464241c03544100c01381d64100b4040056480c2d0390040c91516960310074052000034100c00c00700040e0a41c3c0c6a81d6480d180344249181c41120401854810a0807403000e1009526040c0942c3d8000c18042c1e0b1201c0ca0200c3c42c1d51000440d402c3e80e030606c40b840245410408507500d40c110411038031480c000645255215114201c01006150300a03401c507840c40500070202c0c4521703955802480302510030055610b04600514120401e40344807014a5005030064070318490722850401d4803445c0c3d942100c0d25507107500340e603191080002940301c41c0b010750001e02a203011030708010ba01400d074094084401ca00d03510840540d4925841000c8000b002040e1030703a40c0c001e00000313940c1c40901483c591041a0111016005c45400c3c045034043c0980710341151003168001018051128502030601080d103403892100b0301003001d00c0c800140d81d0500780e0890001c051041581d443c00f000140c19100c2d03403e05220300e1107007200d01ea0916011f101551a0700c1d400c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 99971393 1250 99970143 99970147
    0x10509030423121506010e01090e0c0c01060f06030e07060504080d030e030c07090e070609030b04030305091c0c020f01180e04060204051203030f07020c0907050c0109021f08010905041e1502 83
    0xa944c414110703134007282c040340003480c0700003818101d6100301074001c100c0c3d168980c044140d480d580280703141c590220440c141d05640362200001c1040b42c41001d03c008001503035001640c0740032428080e0512055910901c02c200c800e00090045000116100703005841c1810000f034090003001100c0c1c118054140308203010f008078040024080b14607041841c5800200b000d840450340ca400c41a94814800d00001e010708400a0014000a000703a11680c0c101f103110044070044100507a0380340d5030400c070501040001e1403031100c5500318140f20002a0030350000b42403901030710710860718480300340070148201030846a807034000c00d0500c901c0350b044802800024041c0f942094280303c0c0150744e51b0050310440c820a11810006248501c080f0380908880c000070b15665a54950b00304c1215681c1000c0c0034001c19550301c0a465005070340d0001e80c00c090781802140d040196517503440181c40b20760140d00c0200010700b03110070800081e880203480721403401e441c0d010000903421030030128289180c00d1801d000315480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 99972643 1250 99971393 99971413
    0x708011a0f030c060d060e06030313030807081207112b030b010912061d0102270f030f1e06061008040f08070501020909010b070308070e0d0c0b040801050903042312 72
    0x100d1b42101c4261065424080440e84480e001e01d44c3e6446907030076100450000503810300002d41c030b10700200031050141d05018100b001d54450b42203540c2013903980301c1c00304100c5141c08400388000c2c41403c1400e6140e95404804014418040c20400c503c030071400704060f41d448040d125680500c0001c40a0841f406034082c80181a241c44801000381a03410412080e1020202101ca4014001c0b2901d889441c4500ca10740d0071745c0c0780404800e176441280582d010740306a20100064408105902e0880740141c0204011364800c0801c0788060800e89880301c06070003032400c20480c0e4551321051401d00c81a807a0001c030301da480d401c0501d08a00c0c040c900816a43e0b0004200c401d1280540103481c0616088512081c2c40c0d07611400102c1ca48035119000b40495400c10000b1042800746000b601c480c00d024001d0084c00906a07110345004409030400450241d001ca818031698500b4464298806e050000561401c1d042a4400d4425107050542c1030a00c121020b402c584c40d2141050002044a22403c0741c0000c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 99973893 1250 99972643 99972667
    0x108010209211018050d030504020f010c0809130e06011205060112021e030c1801030c0501050307050403140c040f020a0e090c1b120307110708011a0f030c06 69
    0x4840140144a00d05061061880042d001c01032002d5014150081c10228050700403a009040c0c008401070810300c84001c410f0109105004482c540300d21544e000810b0f00d0709104002240c2c00c03000315681003020704e400500028000d41c044030380001044a02c0b000c01e1194880c20b00c068401400d060003680139a10000400410b00d014155580c0d11030011380384180c3c0c071490307090b603101243c2901a5210508507060081c08051958100505002606861003005400c0c049116291080c0e100815072034818010404d00203031050940c060a03017440c00c81d18509008030010428011400060a628500304560074441005c000040e2400c41c054410300405181c540800025080100c441e0f020802c3e49140081910786901180d01c80c000003140581414072a040301450b8000000600c1801d104511004862003400e03005148906c40302e0ba030748401612080b19250031300078980d0294041c0c0c1c2c1086402c821080303a0001c498042c0c0c10a44070140804d1007903000900e000102160741c0d811100003c2c014000c58 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 99975143 1250 99973893 99973897
    0x71e03020f0d02060c0307030b0f0301110903100606021515180103060f110406120212010905070210110403020d0f060c030609060f050607031b0605010f051807020a0305031e01080102 80
    0x1014071001da911a200c02d11042e600d0705030844001e13040150400c00112240d00030b80c40400f04840c050903c1010000c11340120f401c44208201d03580301e034500401c10309400d00d01080100703030500c031201040c00328502e4040040e46d544c21b2280d55030304980c014400502d804c90215055910440002e080a5031030780034481c049004107081c00251600c2e420044e1241e0a000c26004210088154250f05880c1c83e1402100b2108a240100a818019001c002ca0440d41001e00700340c5002c0c050b9402c000a250521807006031822a025480b09076207400c00e140d81070310500c1e03e400e4800b12a01079030702d254450704900c0e20303480da8014010000c1c08180b815072119001079240c0c0c00178040e2000410100001516460485882003840c403034164401c10802a080003c0c0c4241070010802c1c0c006a966180c6400b00d0f43d803041920426000124010b41c6d0310301c10005454214202d12250751100c040400c4d60070326101c002e440d180005000b6041c020000003040310020ba01c860b0300a050240140440c4550315645118003079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 99976393 1250 99975143 99975163
    0xf0102030a0902100201140109020a020c130b1206190c0e03030703080601020c030307210903020310020702041a0d020904030509061b06060a060206010603050c070c09020901090b0a05040605071e0302 87
    0xb441c084e071082071050300511a91042d0f40e03801c0e9080340b0a81c079004400d406075200030039410860044280f907001036141c1d5064100c915603035140116041c007401007030094030402c1e0301c0807540c260300c80421b01010314420b00720182d1091a01901140c00c040e84c2205a4030744080c070038600e41500c00041e50405040c0d0005a00f0b0190009a00f5103105850510416507240500c00c0040d107041612001c040c09080c903080034040c00800ba003400f0fa001ca40e6500040d061402c2000318158064000464504515040c80342200304808aa02d02c5401941031010901c2c204900300024000c00850011078240340c00f403010303154040c0000b00b00c0c541d00c400503600b249100e203000081402c3c92282e04040b550528190040340f050320060381c002c01c00f50b86000c80440240c0009440484c0001c2d08216a00104110080b1840030780a080000750340c4001001c00148507041a60002c00c20020901c41d1686050b4040b0840702100c43e0b51408a40f90300700c0d03045c40d070031804101d40184525152441d43c80f04141d008a501014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 99977643 1250 99976393 99976399
    0xb0714010507030203060325030203070602060f07090b07060c09050415080c0609011e090914151e1512090a03080703020306010206130305131e05010e090403030e0f0102030a0902 78
    0x26403280e1100743c099000c280e9100341d02d034001000004100000c070440b0110324140c40c1c1c1340d1441d1a560b4010a0418010b03402040c0181c20102c100200c041031065166001042c5240c8410500d15001403e041802035640050000382c855203e003107400e228140c040090400188108a618582e84500d40b1211603441040002c2c0110295800b003441c1c80019580e0104040c2c403800c00e4070b1b88001c1c42d210000c040d02101011700901d40401309541c1c100e8800e800580301d41e035074944e00d41c4c1826040742000c03421031240240301703100c1c8903a99170141d2514a1914405a0152032018090404145100e01c500810490240301920141042291500001c22a04443c041d0701c030a0031070b4445090840507440101c4005001d40e0206010406c1110a0380c98808414040e143c03c42c109013010412149104140e849552841c103100c0d0032585e020740b80360b035413002000d090078100b500840700c034007044944074010005018981e46112423455140284141c103003a0041d00c0c001c43d0703030303290080311000201486001640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 99978893 1250 99977643 99977651
    0x6080c0a080c090f07021903020102120c07051005090c0d0809010e0d0c060c110913150c0806060d140a020406090906030308062107080a0501050a020f0d0b0a0b071401 73
    0x5015480801c0041c030b40e1001030f0501010fa65502d41c803100e200c0004c2d2280341188100c0c2402c203054803018401d540c2c2c45100703034000350743d815103190483c5450b51b019022802c55001081284c0015900041c02001c404000b103001c5116074400400134240304840d1a100d4112a141000408010003a001480041030980350341c84030f00d070058140300c0e03a811144002000c6410b01d141c280040c1e40152156851148104a5800721019034004200d603c403003a03c6000d03910030440300c0360003000b11903041584410407100041241c1788180c1001400320002034800c90140000103000b103542c003504e4004d1076603980b02e60003511160521400c4040294024413607040094502e04000c181b402141c0039607421660591f0714000d00f0b450f18410407172990b100314501d0304c00080d40d42c0c0700b40c0049400d022040041c82c0c0078000d0007921103207050840c2544e00c000c0901c8001c6104010b84424120380b541910001c0d4208100040c4208960011503c0c550303c50b08020001400414400c04000281c880c410b91110448004c0c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 99980143 1250 99978893 99978899
    0x6240f08011107120c081605060702010e030c101a030d050c0105150d080307030b03061306050c070b1803120c0a020f1b0d02130c0c0c0e01060c020405180106080c0a 72
    0x181d141c001c014008019041111030742013100c0c840c035043d2616500403d1b4281c81c2080914a8010403200c0520443d10760300150300308040d007a0203200c0c1d0f6203490740d80006186041d001d40803140e11058180303141c8200c3c540d100801004620380e469a0703c00700c0c502508036a2510803510020700190448100b4494542c24132001940d2507455001613050b8990182203101251100c2d620862310303410090180c1c04140d03507000703000c04568007044218020640d1b00031050b105400b5060050554800500c00403110104110140000d17800d140300310f81c00907040000d05c4011400c00d88284c01c601c2400140030340c4000420a00c60403001070401001d50502c56001c407011100b549454603150000100d004030815080da12283d81c030f00306045510000da2004002282406618034804215131034010341e40c0c0000c0900c103840c8200007803200d0b0074000e1320102d0b220028940c5410801048005881d4009000700c1d101c0022800c40781e0306184510714030000758000d000741d5869156540d50b48110f44215441212040800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 99981393 1250 99980143 99980171
    0x4090c080f10060f0f210b01031401082d010c031e0e15270a0c0f1a0a030209031c1d0d060c11030310150302090303030406240f0801 58
    0x68049504948800001307001c0c140065071001c2e4002d41d10000c1c841c0f10a100d5004001012201c02002030030b01002941c025160001021500342c181c48031700d1280c680c40140045ca4001506107500a01f150a13002904440e020723040d81c00c40780042c520195800c1668021803160107402c00d40300c090001d4079818090108030b0742017003034031704100d40c906040c0c2045190015030344414110341d9002c056550040d88080e24501c081c4003204050010310000c1d0000702d0007030104140c400c41c0400500012401c003d80c0e03410152401190189a00600e04420b0000f500203490b5000380c06550502d407000742034a560400e00c042400c0041444290040010074117545001c0d51050205410f5212901502039410105541c0d503100c01420807a81890900802c00c0000c189401d081001f0f501c01c0001030703440c203141e0f0710300f041c140340c0c1d00c1c1c2c0b0300f04a0060500510118103151000025251310680142c0042102800380343c10b581d4024800c03442c0b82050350301c0440460400c4007034400d0000c50741148020807243c4040c0c548 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 99982643 1250 99981393 99981421
    0x403110d11040e12070804080f0309060d0b010e100203120601020106060c1e0c060903140a0308060603040606090204060c050c030a05030f1c0216020906030601030b0c0c010204090c080f 81
    0x4225032520480941039040603444800001c8805088071501c2401130a1040783d40c000c540216030b190000213040c4044034051180300010104a8003c2d81131407000d800091550044e502c04420655560480038105e0b8450f020028071150081d1041c10803518401d0020f459600c2258001403030400200424119441481010700300c4079507070386042010081e0b540f02002084052104440e007030320402424041923180c2c000d41c00034001034a445020b9807440c5082c61058121809201c0e89030003041141c80803d811148070b9601031000c0307580722f58a80d80c1303160810007040550000981c00d0320201d808035040380c0002ca44000310b40104c08540c0c00c10103120425580303071888a0000c00a4000740804001e2540742400760407050302604032400e1400800c17080100300e80001c07040030b0903800120b061605500b00480001c3d000f00040d40945410760650702c3c4c00c582c4071000362260505a20000c0e0040e0042d0307084d03054030054800004180201045a28014065a0241c0703241503035514920105a03071442d250a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 99983893 1250 99982643 99982669
    0x71d01060e1f030c1412010312110712030314040525030c05040203040203100c020a0308012103050a0302040302130605030f030a141e030403110106060905130515090c040311 76
    0x500c2d030110760210074044000d000007018800500030005e68a00c240318a0034050302c0c2a14449a003c2c5041d851810500c0070400105001410700403080d421b0f00102c58042051000d6494652000d0580586440d089001303044c1d5041c001d01ea102264280301c108070020a6100000000e282c64001844090034103480300e051910000b454144400010821030074207802031580140003c1c25a440d9204590152064440568140b0010327000350305005c00301904680410301424681803016800c8680e4005503403880e000b003070040e0038040c0214082000354829011070b0301455000d0300c2c031b80c1002280158070028001d140601440f07402503010410501c24000161810780206641d03122115079141000c07001a03020105400b0610450401030303000c103080000540c001d43c4680c0d64031725009240c0c1d803c103084554a801ca001000102401041240c1c0c1e0031300b4411075884104800a040d845006102c4405402c94a402d038200103c00104070b100b030070340c1c8040c1049901410700c0d41506c07025081007004541020f4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 99985143 1250 99983893 99983929
    0x1020d0b011d010203031504111206090c0a0c020d05030c0f031e03040512091903030503070e090613020d02040509040f060c020304051503090709050c090a080303010503030318071d01060e 82
    0x8400260400410000f1040541f4040c0000440804050007880254841c0c4100c14810b102c1c0003d102b20360038640c4001e54401c01039446982070902c6180c000305024009227000c0c1c41400301e11707000d105110701032044406c240744e41e40495861010505100c2d880780c100c0517041020044141001c100307030750b50074122032103251f0000c0980150b040d8024420115080611640d0300300e10315588040b00c1c1c8a40d101158042d50080e03e405440f0301d0304410007410581d08404180c09503141400788501034540c0b03485c1c02041d62184a0250302c4400740160b140083c020f03548010341c400c0040003031100340258685103800d6607000d0a0203210041c1207000a903039a12407803181c550401e00c41e030600100f0781d0b4044080c5802c400ca4506485000b03640d202c850069500079038154941c00d10004100615260083d0184c005081083c040e504543c98080025200d000041c0180503107042400d802c0180001480303400301070150411100c091000d1140c1070700c0c950400340910300119180d0200c1036890b02d001403241005500d14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 99986393 1250 99985143 99985147
    0x2010e090423010209190302090928060906090807050708060c071716110310060b19020708060405010507110c030705011d0d0b07020706170601080c0c01020d0b011d010203 75
    0xd0344210b014161082940c03400c5550922205005a607091001401124240b505010807400d40c01004030503040a040345445521101c8007100342d00240101818a081c4100440c400c107203241805406040310040040a50745071440300c404004046024007441c90007002151030064842c012141d842070251100c6c0c080d002c0034001500084c00c000704036901009070341002c0307040180c8802c000c503200a40480850f040450641c04a140382000c002680881960b03032018401d0610345400000244034000c4c10904845c45c00405058040c0204402e0008000d1181194403d16150500314020b010a9414100084080c150300c00045000920b001c44400000c015000807440c11300151109042c680c0d00c02c1c1c01901074500014140d6802e84585c581d540608011059403400101c003d0400030b070307500980d0034841c6160300007296070701c8100e0180c0d1001e07080c02d2041d00703901c0742116500c140c050440000703429800010394200a080c05d8202912500742a25618800c2d42c4603400c100c0103c03030800b8040d0050703000b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 99987643 1250 99986393 99986423
    0x301081507080420040906051005100f0504260f0f06010905010303120507120e010608070b0f0d09020a0308070312050c03010b0d050c0c0a03090f06050304020901061d060307090302010e0904 83
    0x908190310035030900510000d1003c059603282008e42c0c0048447c55207502c81d0035400c02c8a810080c43e0500d04003201d02c0c0601d20b030302107644003504a0050303018000b07c40585a4010b04111491790f040344030440e5076400c903074441e10f0010300c071542c981d030700080615540030305000000c030221a8001c040c1070340d5040d06c071511510350100c0e90750001c20004082c0d404026122126820010b458894280c02e1104100045446402c00007201d1500900c1d80c0101c20b003850401240301c0c032500d0103040c0c60b44c50b002c1e8036001c80c2009090000414440880d0400350803104009107180030590400080340c80440700010500c50b07980c84010500c40c0c2d0009106071080010f00b0020300c003200d5084e07807040d035214211500c071300d04105028140d549050320880e4110081025140b0600c079401d82280c1c0e2400a0100d0324100c1e19501e0194046901003406218000074001d0500840c0c880044031500c0b0603843c0d9010f001d007038492911160013032030045584410f1b80402c1ca000e540804900706031031080c0c466604103e0380444c1c942 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 99988893 1250 99987643 99987683
    0x50703031218110a030b01080312093408070b0306030114150103020c160312020709090c060804030e280b07020d02100908030304050601150507030206011a090603010815070804 77
    0x103e99040d483d4465400c1038040000307030000a00d42d01900403c4010341c3c1302c3c4c5000d44810b2411101410896255110b04242d2203064602e620407401d080c0c00101d070914091517403c0011000105400c200300381d025400004c552040020080d5209101c210005c0c010140c1c0303840f140d80444010f80d00c1c140466040e88200c00c8550082d0014509209060103d40940480308510582c072001500200d0352030906404040420303a04021400c0501100d5008002c084a41e035140b400035002440b0b013000b880050300000e01418040c0141490600000c7c080700c0c540030003c0110700058814282d91003500840c0003021840d4286903041e01c1d01158082c1801c0182c0d1907540810030b0142d124000030007001134079040460600001d001560086215800030310b01ca5041035111010062021180b0040000074000e80011a6001841e141120150a544a51070b075071048511614071400c0c02464008000200002d51450009038030780000c51844248201d80c0c440120485150038140c034081c10340a280013004403104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 99990143 1250 99988893 99988913
    0x40b040603090c1d0a0b0d0b040f0203070e090a1b09020c0f0706020a0c180e030a09060e09040201050304030e040204050a12110a0f03030503150405070e0f0103061505030405010906020304050703031218 88
    0x5500a080710040701f0341d40d980b00500c2208540031070303c802030403a8083c211304081015602a00344104a4280c0349000307a2503d0703690603602070180480105c02e8000985d540340031007040c09000c070018150740d1015141c50b10703541c501d150b41956045214801000500c1840491400031b40c0750300c07880b041d5100745014210f20301ca411050040040031369171a02042d04c9401000200f00b1b902050722025076040ca400b43c0030741040e0303500d100580980020410080140c0c7d0041c1200c0e4002d0349400c22346218400031011038001d008075000150488400351000c9107001da01928400c0607031148010070000c40d234242c1071003102075051184010718801c0c01c0c8140002801403014552002148000a60300c3c038030000045c041d04c4058032440003085281c0750804007414243d4036040e08040070f08040c40498503225141c0e62485500c905081041f2021010030100300080d0803024169401c5001591241800d0600c1a200c0066104c00ca010461080d02c3c4542c22015024130080300c111118403c0c158405034681007002c1d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 99991393 1250 99990143 99990161
    0x14010909111e04080a140d02010b060f31030b0907080c1201021309090308241509040e0c10031a010302030a02070b0901020a03150f1a040b040603090c1d0a 68
    0x202e001400003058494007000480c09182c0a0f4841c20401d0000c02512810090113102490459041c060340c513a4980320710b0116800020b00300c0f005d513a40c0a80549048003411018101c0d010040802200340d183c503110181d01c001e076401100f401546485040361103554141d248110b0301d035500425001030321440c184881c00c80c22440c0e00c001503d05040304200f511a03490540004500c0c90740c5a4a410600d540507101e140e022410642c0440c0703100881030308211034903c10f11004d01c610180102545050054816940158070203002070109203034554403d41c840007124001405a00308100c030211a43c482d000e102c803c1000041e100c40c03503e134404011006580000d00801e410354080020000180c0740031680c611a03d0302d1000180c45141a2a00409407032226a120040c410300c1c0c1c40c1071280007607040039038048480140c200280540440760704a0140900c0c2d00c500000400494009070f156019041007a41c244100b08041c14903860b0800701e0340020404030320302d8810301c125001070381054166004410b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 99992643 1250 99991393 99991447
    0x2010c21051b270303090d0602030601050408060a091a01031a060a0302120606040b0a050f040c0e06030f07021002030717060f0a06020a061107031d0d0b011401090911 73
    0x1608108a0203280c05510040201c1c07409070140a100d02d21030034250b6004071111013100034600c1c16031400d000480b0680002000b0b0705442d80007002c0f621680c02001160008c1503150706032036143c90842c80e4000103005e15101602c04803407070301101001448a5146078180c3c0d44c0035160107201000c80c0c500034520100244640d4100841d03801c08400b40e81e910380c06440d00c40c00d6100400551038130000344810340f004900850300800c80c2503000e018a48d0780c1700c00905519001d460008420340451000c40d0205241094150171442c0001484030084a008a0a03ca180700b5001c658400c86508140b10892000721644000103400d5448000d420300412a03d03038000c0c0d070081148001340c5240000a80c201d6940c2e000b2801350388244556001c020f4503010360684030116481c0170307041260070740f0050400500801940080300c412608000e017940d45040710320100d034100e0034401c200c0da16098641c04c10311100b907000340420b40e0b6540000b50403465010b45010403461244040c00c0c10b02017840b24451152500c00d801d6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 99993893 1250 99992643 99992671
    0x3160c030309021804060b0603070c20041e05091c08070e030106080304061805030601060f0309051506030c03011505060d091a041703010b0304030e0d0609030203030702010c2105 78
    0x56a103d84c4900c426039104600c3c0e04150519182c24012a00c43c1400c10380103403000e108208240e41c2140407409000c0e082140282d042c080d080740754032410401f50301c1ca60301034075222403a5001558036070700306c861303c1d1000c40402281d102c00350050356560041c105400780008410b14146e0b101d2152806940090050030031958100b0584002400d4410607003002415501c081000c01909a000c1840f0003030301040c9094080050074900031944890703050292005004444518901c000d10980c05081090740100a0390823865061a4100c200101601c40071b01c40e214522226100d0315040c41000d040145c0c110343d0b03c508600e0002030203000d410485100304010b90b6030079100046030290a4440700700441c2070613440946000c0c0f03004c41c1b00066000b401c610001042c001407012064400840344c206030075040c00d00c1c0d007504540c001020410003200090003a0f007002d203113204044e000800385002e421560000d00000f1500482201e055a40c9081d114843c04112940001c800d1503a0105030008446c07280d070b071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 99995143 1250 99993893 99993911
    0xb0702060a031d010c0e09010e1816060c0308060f090f06040e060406060302100206070e04020724052e0306110405100203070b01090509030a0e03160306090b060603160c0303 76
    0x2c1c1d282d4140021079600384d44070500680f0709648000c0c031b411102d004075107094041d4144852003c007280b0041c200d5040e00714802a098015030b0401003000302c00600100f0b141c0090f02c0c0c1d140102600e590140840103d5950b40204550b480c1c6403040110714403001d081800683c1c2c4400c1c80d080f18540203000781d40c100c1d6903222003030907980091003220322940c0227210115145103144103000c2c40440d906c040703000310b40040c002d01c601f050b4400c09549440004072800768a84609081c042041c040e1003508500072046107100140342ea0319500518441c1200154803800c0c03030390314400184a60890304140390b00140802c02803000231044e62043c1c50040c040da800078107081e01c640201d80b10008010240300580c1c800710b180400c1000c400e07400e50140001010902003810914041c0c0d559004d404a403909100c1580300c03042d100d403810014022200054034801646603174904005004050010003070315800001d500080e590b003894022030b80185140c1090000c0b090302e940040b01c11000d8000201c0804d40c6400600e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 99996393 1250 99995143 99995171
    0x1b050a12050d0c0308070305061305010e060301050c0901091806080d0903050c03010b09060d030c06020a0c0606090501030803060d0609020306010b0a1b12052d07030801060302040b0702060a03 84
    0x1402a081520494100c4601401d150340342000380c0004a00300540202d0540010360b102c0e201540040b01420040fa070f41e12610000f0b08603440115410075201d207000c000044080315050080c1c000d8100394001c00c0141c4908501c0303600e43c400e080640380400c1e4403202c10001118a0500e030074015130311490005501d510392420a0a06114444110010350f682c00b040c024014148401c2640030000c42c0200320112503503000c62400e05006000f148103601105a420074140940c1c00c41c84616800201107648800a030400351112074140ea06407170281c0391500110f060f0030709125070b6050340c0c0c0200095003540e03250410004040c2501c001180d98940310302c1e0a0005840030009240a400c4140c5030607100c3c29941401064504518158603841210110b0200450140c82c07005c0752074071651520540e9003481e01000e041d205c50301d440000098200c400c1c40c00030b041c02c903400b1b050402c4c8a41e0301c20380305076626802202680214054280c0b280c40820540c80140340042c0140603200d0241000306e100d8150040c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 99997643 1250 99996393 99996409
    0x705220204050a0f05130e0604060911090708090c01052d0c1b010e040b01170601020f19060c0810120f06090309050a0f0b0306040207030e12030d0f020301121b05 71
    0x320503131282c0c40c2c9900b8801c91400c070003000c00c50b903030400c4100032100c1c3d415002550351074050310251095036500124014040808000c50301900080c018250f0340c00c040c0c00080030002c04585480360350041110700301080d03100b1000c81d96801d070040d40100803100c001c44000400341c00b5805010790114104134641c00501c0a002c5010078584035030083e10001140e80001d802d4401401e9458840c510b800c840b11100d03070704800b01e03855020b00d450804d0b03559620100140d10780b28282c0e60701e499511544600e103840d030310b4291030078841c00d114280511500080c8603007500e00201c195691114000000701c180308070018009144101805001e500d86540340e651074000c100c401c12802030300000d08004007401039041c40d05201c402014a044e9542515151960038035a40c00081d04180c07180b03030001a003d0a044c4100050b10001342d004102c4c00840107241001681c9078009404880e20701d040c007980501491061003640d040320302d94942c81c4601e04941c0c0c0e405149a515020703414109005c81008102138450f100c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 99998893 1250 99997643 99997649
    0xf160e090a020a090b09100b07112b1a01031703040f0803090c0103060602120703110c0411030a0c081612060e0a0f1404080412030302090301020d0218030705220204050a 74
    0x10005950f1740b83c0806d000c0d014000400169400040d03030700810810b180d02c0c2c2200c020a411011040012410300e000800705040003940508484400341c000302124840c4a40007066031044035114903151084000e043d644400744000b600d03000b2172215018048103610002c43d0700500c24040c0b1450141d507540d036010581c0056440020703544c040003094a10307503090300c03840c400741145000a003000d840003500050280304000d401802c100b40c010704141020000c2000f110751180081041c0020510038086044079007088402d401058280f42800718110301881c03105001304440300e0145c03543c0f5420107040e200208510383d10064250744040000700030ba549070650b0300a84000e08003082c00e8640703030148800d468014015020b41e29284040c0700c00682c03090200c5007282d00051100d50a0031070b50805800a0041c0016650113500000725284000d1f240e500420f0116a0301e01c80203481c2d1008824107036103880c00d005054100203c4c4012019102500a0103030703081032401c0d8094a85910782c2c01203800c44510358 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 100000000 1107 99998893 99998909
    0x210215040c05010f09090609052a04060311071a090d110a03030b010c060203010b040e1501120e0a050703081801050f0f0a050d0905070501020f160e090a020a 69
    0x22040c17032001381381d07450040050550720003840300980001c5400401d44941c43c1021a000b134942d04010076030010258007142000d0170104198000c05468a590300b82070428450900062505441c101c3c01e1400700c0c1b242c3d410b074103182c80442d2514858419590900c03d88600d024071160f00024000142a054034010600251100c01a5449040020301506581c000000800d042c3d40030002030049510000b449a07040e95034003290f91011082954540c005042000011458545504002020206c00b01503503c1c011250741d900c1d00e030101c6548220b981078404100c03034210390b8020b04003804400c000e0800c2881d02c00c022810040d580300304050068805000b05840350510320a0702924014107031800208101c8100d4180141e0b50f8446200f200c0c0180b1810104c803080c450302090700c0b1212494141e08064081c1890103c2c40791500040402c0c00b2481003042c4d1501582c0c650f0015070060002c0c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 99820143 100000000 := by
  have h0 := BRFrame.cov_init 99820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 99820143 ≤ n) (h2 : n < 100000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
