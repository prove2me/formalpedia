-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1785
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:40:06.310366+00:00
-- url     : https://prove2.me/submissions/5a78dcb6-ea77-42d9-8e7b-add6e7ed7c54

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 320863309 ≤ n < 321043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 320864559 1250 320863309 320863339
    0x3072102030a080408010e0601060f020c090406060902071a0108030712110705060c0c01030e01020a021903230d0c1e1103040305032d0406080a05040f060f050712060506030105 77
    0x40b0346044240d1240c60661100d0f15540c1d16402480309051000389407281c1d034000110f0340d01905810707144601c0c03036006d481c00000942c144096071501400869203d9070b22480050107410358405018007074070405000e00042407100e5a0078281c50103800c440ba40303400c2040100c0001344031981401c0c800d4014204550410390341e02d059404c0080300c0c1d00003504440700054202d01e08a002c18040402030090f2020070504c0080700d0414201d0151480d0f00707015034000136062115600c50310440c0340c1d0901c00e18181c02842c0075825210030741e000b62180768004070400708580361500f041d07000d01c05a56207640742120024051400d0f45255a080c10004410b00c1814040001405414000c0710091a00282102e558224041c1002075480c0d8000001e100c803c8413042d4403006400900480b02101c0e0203644000b0780fa252000418000c0c507011f0011200c1503801504040007404c1401f4144128080c8600003e49240030342000d0041d12140d0300000c801031401c8020300c46a41c518040d241980c0040d101c01a1710400c0e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 320865809 1250 320864559 320864563
    0x10090602070219140d02041e15060813080f0c0109050309090112110111250302032505011b02030607020105040b0a020901020307080705031308030a030c031b03110f0f0403110307210203 81
    0x21105c4071550500244040d1003100341c00c01011040d00030070060003907540b4401150740b60ba0907203590b068500d03203153303d501169004001c0d01e02c1c1c0850b44c10280c9000c2c5803c442a084601c50901260640c202290342659403820760704950040060750302c43c0d1a204500d0342d4610001075041c04442c140000d211001c3c8400030204010100000d008400c0c01c024006110317440441c01e00752104900c00d2040c50800c90048944051203e0311000c85a520030303d060604005441401403208a030f0408401403146d1005070745e080041c18007501d041d2700001082d003407070300b045901940020b1110a40318010088c41c41c103641e0000442c7c03011604054401d8a80d1900e1504074154881c1242010300007002440100c3d481c20301000811840b48103403000c10154452100903420740d0b500104445406010146103008a402a004800c0201041805030b140c04103a81c1c9600d102d4219044c0e207403140c03502040a02c10031002c3c4450a03200682100100390503031825413201c2e40195641c0b641c880080c10840070350110340302 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 320867059 1250 320865809 320865821
    0xa120507031a0d0c122018070e030a060609020a120204080a0f08090301090c060206060a0509010303050a0210060906090b030c03120d151706130c090e10090602070219140d0204 77
    0x801784444041d022905181c0d0701c00308400219009200c400a8050084c90300700e0800350283c0f00c0e04a040d98590720008141c502030102d030031143e014015510582d00240c032902c075401c0a030040d203e00607110f544841c0700806807401d0040e0300140501c10001486403040019100282d5940003090901e581014900155503010ba201c040d6015801d000240e003c018018120005441c42a805c07242d0780c1d036900c01080900c00d10361099540094003c001400428031850081050595a004440006280c002400100d401d2075008000040d07490300180542ca09a0003a000d091008800400d00e071006200081d03110449224084e61b0010300162800310340c05690004030040110000c5501c038980c3d00d10310860f015080c0f000d0100c15000b0600050b01e603040a00710b40000301d820001d076641c0c032030030b04d0f030326100800a5410308026407082a503c285100f00f14040c0205941c4544400b40c1c031148644140000c00c440b00100e06e030030f014421814451944d6485403c1c25a403412100007480c007156001060040c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 320868309 1250 320867059 320867069
    0x117160c050712051b0f131b032c060a05040212150a053607030203070803130602030301140609010c06020a0c0507060504051f11030a120507031a0d0c 66
    0x29400001681442c0620443c5494016400e03a58502c0d034a001c3c00340103291080b4013982c07005501c592050b842c24601801020304c40603040004280d43c0c2650070030b04911032080240c0000b505e401662280c80340040c0e201c0c100e213054904d41c980d0300c100c0e030111076112100100311141c0207035241e00050655648013400b80c0e4011700e0a0640318024260207003d10300d801c2c220b40d240b506c2800c110100f2075080040c40700c2c0301d0240400300886d005c0304035400c400b012100010012030780340c0f041c11400700140c2e405000740d4004142d10030085603038407010141b40303491000c1e60b40074400395002800100071520060084142115044031817599900403000182d0380e000329120058000ba2001c0741100240303070800b60041c0031902940446803010360b598000c403560b104034000e994106450400151468030b40308441903244105080000d124102c203071030245150010364030800080d103505504103440c02907200300f40d00000903244c01d04c00040701400344d115510b649070802740105441c403031940502070032441c4140984 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 320869559 1250 320868309 320868313
    0xa090206070c060302031b09010e040b130c0509030c030708072106110715020f0d0f0b100c0b0f01121b0510050403030809072105100207080d0b0117160c05 68
    0x740c3c80d080010000d42045520a0703a20754128800c41c05880c42105540b2500c00c16580c0c40310050b44d1b0010301c000341000d15035068225241010340c14803020f183c0a0103d0781c3c40d01d0742c2c4854440301610101450f103012100668042e41198005101da170b400410404180c8409800c3d1511240000c0170f0300d40b0144540720f001c0c00d20340c6090051000010400018a0540e00480b20070240900120003802244120303108144409802c0141400d243c405801032600b10441c1e402c0000ca03010750b40086446400b44012550010b041f00009031700f04810078141d245c2003e1026000f040543c1030010109a04081c00c202500000b0091109028845a440c07110080c000c0a006a00f142c02d0b10900070380540c010b030004801080301400061102070b000207200c0d0807a9003407403071010108512079070341c0c010a81100302541d02d03029520044020904c940020f001c01071158064a644a03804845181190000d00c000c43c10864101c1d0404012003290214075000400c41c1c14040c00d000343c00505541010514038010654 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 320870809 1250 320869559 320869583
    0xd2406021f020304120842040501061b0302121303150c090506180a080304060201060b031003030f0903050102070f150203130803090f0715031d120d14090c0109140105030a09020607 79
    0x350100e840407402c00c00d4041a0318107c207602c942000240d48090054200217041c000103a0302d8408503c52408089000340161040f401002c180613085034400c04001b501440300741030070801c100030880307003038011409034004000d00320218100401d1203030380380b04841c814000407500c400c411020b8a1f20072484400103201d00500c940e12940c09490340c001b80f007800055480c01a000034200304140840b80b06a8142c501000c2a6096681c2900d40c25031503801071081003200349000c00040c0302440144145801105410001e090340c0c81c021312015182c4a0740b04106005000380006c4000e00031a40020940c0550038503100e90741c00c1c4481c0d143c6007210010340400d2203090360008040300104103800405034180d0303060108000e40801c1090718100400400d802d03502440600740d801e10b580c4040e00500c0301400010030403a11869600850200684102075240c010413043e82c15580c01005500c002c2000b01e0007c044203507038000103003030340c04000c10040455807140700803421551000211140950720481040070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 320872059 1250 320870809 320870881
    0xf06050f0307120b0a021903060e09010207050705090c07080301080703110f01050304170d02220501110642040501140105090603040f0f030503100f03080d2406021f0203041208 77
    0x5482e49100e05500cac03100a00118000381418002c991170b41b90003000411415242034180702c5645401000c0c1e10300c91505111240004108000a500a0600b040200245402d43c1048da880c035009559891041001003001c0d82545d800c801604d50203a0418582e1200c0030704060700780f05921134982c0d505e011303c1c030008803100741e20908400405011055240010006e803901e00650719504c1000d50f046181d40030f4000681010030303001160342510010040d9496902045101c05002056488440f1911030569140b00d07040c1070602c03c4a00429030545802402400d003030002e0482e00c24820124003800b8000006028031034689507035102260301c00e0882072031204c1810020180e17001a42c061489800d440c20010700340b05861b580009803a0819001840d050150a5503070040224000101c9046880ea6542c01c40c041841010002088039402400803440348a102d0b092022261014100140c418004c0c000400e10030b154040004000d4100100d00352100d0000300422409510b0b51415005440e290500c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 320873309 1250 320872059 320872061
    0x5072301060918050303061002010e0111030f090d05190e18040516030210030905150106081005030a0f030305060d06020d090201110a0b04031805040f06050f0307120b0a021903 77
    0x1101c421020401041110710040340740104100320203421341c0e0003032011981c103240084100005040a000005030084c420012509555407078004d00e505810100802140002041d07100364080c500c04060a03501c99048005070a5006021035850720300c1c04c0c508600f410900610f218406608028441101d5086407074111b808824111000c4802d4007079002c040101441c05c1c103003041502e50040417070110349440da400b01d0003000c5030070098650707200b1010510141c00105081c603020706042c0c0d8031086549040003c207603294800380d005500990126040d0070105110000380c0490300d90610b4046110386426001500a849a9401800301480081c00240c905504c1e440240030078801e80310310408000483c2d5a07921080c0c0f02402a2101510100040c0000d126405c60310034141060b001c3c40c62540c550001c242180c56105503900065602c210a00ca42d203080d10f051984924110700410005080c000c0f00380c0e140c03a02c070304010a28128038011900c40010f1350181c4500ca280a2080da00100b102c00d4020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 320874559 1250 320873309 320873321
    0x13050102041205190308130c05040903020a0507080a020306060d1424010b16120201020c01020f0309061f0611100e150105040506061803030705010501060f08010602071505072301 78
    0x3e41c11300c550030586440396054058060040c1c0c0546401c850b43e9152180b8031002018000100d8004603610804905640c40b882140030807406540108005c0125140c15850b204084d0820040ea500c10300d900001650005404d07030340620709480c01020090145080b95540c05458480e4400d4026409128560080c14001e180c0c585005640c040070382c0d0340e92071039100c03501c43e0f4600101d501da10003420b80089620304011001c0c4601601c001898140480e2007582240c00c000c150034201d840020030700c14600b108009154000e42510410840c0700d1810ba14151544844d2254809104107036a4544000c0010b1202d003403541c1281c2c1d4188021505049901d459a10183c240f5143d407200d40c0011445081c0361194030b2182d4000f07000d09207031990245070a14460030300340c0030b03503850f100c100002000a4000c1c02040e00130880c54032004080c4050342001b0300081c205030812021035014034400c014000300003080306031240442c00d0055a811140c02d0510080082982c1c41075241c1e04170307480c00d8042c20158050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 320875809 1250 320874559 320874563
    0xb340b091203070c14070302090a06030215090102062d0a09030f080601020705040f02040306020c033103111f051b0c1f170c0d0f02090d0b130501020412 67
    0x2a80c0603107842020094a80019111400012141c100e0752000869003e0311242240d0503008403100075950350300003240b403117088954100341d5440344410411414100038111884108002a908082200c40000c1d070310b04004090360710f5400c0e5031000c50b041801c0d981c010010862011000c003503e00c0d00d45480c801401003407404600180030000c1582840b8410006c49005241c142c0c00340020301d241c03504110152400c4501c500181e9400c220010004006200502500701140003560b00c4480100c44030740c4592a2042c040202c801e90795004010440854480d0709807175025a280f01103401c9000858603001209100c2070455401600c0d5219203030304000940998441c0303c880c0e0a0400780740740c1c810b480b402c0c03512940e03030462040e00100d0304a0001d90802c05001c6490b00d040440004180c1740e0380c0c1003250588900d0100c030400035080101003124040e290700c401001405515200000303001c40c407028a1994040c010100310300100c3c4e50000b42c102c00305001c0390050001d5450ba03441e8511000030100314081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 320877059 1250 320875809 320875813
    0x7060203130806330303030a27080301051905040c0903020405070c02180c0f0d060303080606031e07020c0d050f06011e0b0c0102091c0209100b340b09 66
    0x1801e0300000031914800da00100281d4140d0380d10542c04245440024130290705000980700001d402c0c0c4040010303500c500220302000c5102140c000c026610200c0310030249411198000307401e00840c0c00304003102d04650044d10011080c4402c414881000c03800c54000743d81c440d08111401b228254400484015030740200c0b002c00c0700d911130001c203a031509c91030b02009400600c14a0000420f800307000e68554001c95444640b4a403511641205100c2d0703110410342540c05640f00c401b4000d240c1d00502c010b501801c00d555003461820f01840b0009040c035100d2401c06140990f0001417480e5200707000c8c0c9040e620014041050500042c50a55181c1083c2c05412815225040c00020482c48202c05843c019090340c10601e10703141088803c00c00c99000d000f04481d1590200200111904d82e0010420b10030b09600300c0e0004a0000e10401120300d101601c4101d9808140e03c2c2441040e190104865811604442108043c800000c1c54107100311060000c0340c0020329001450b013803044081845100d00e1030740c42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 320878309 1250 320877059 320877097
    0x20f09040c05030601020a0f060b030a0308010f09200a120203090a0b130218090307020d200121090201120c0801031203060303020606010804061d0c1302090607170c07060203 76
    0x5000c54050200b04c2e11540140e101c010107101196607a2012070038540502d5001c1040088440401e1415010702c0e0110b0020b41880d0040000207030750b150b06e1018011201061021414112900b0700d40f02e105014021b440e440024090b660a0082041c0e90000304510010b6480e07142c10a80035485600c010015160800700c807000850301c0700410790340c1c801c05a00800c408040354000c6032400e0684001054242940f02c00c1054502580d254550702e0140e82c815119003451351101c5144240d100c0170b140c0d01506000041041d04001001e44013495031442e10101e002445000e18001221a54940f00120007003520300b1075003510499100b000d841c10b0340d02403a1080a030490031039044003110b10030b100150040c1c000801090b140d44c81030b080301d0b070058040c0c000410b400b40310010302c00340786000f69049405640401041d40003030500c803602000c105803a081c11030501001101050720b5224104004000300c0070030030507204503117a03081580d510031603441c111002c80b522030781c2c00303581c03035001c411100410f409650b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 320879559 1250 320878309 320878331
    0xa050102010212040803040f1a042d031110061202011b081c0e011b02061807290a0509180601050d0c0e03010905072c01030f06060504020f0904 63
    0x402102c58041d00180900b00136a100c1d180c144441d040604112066100b032a5500086000010024080003c42003c084103041c1840d06100c01608156601c0c2c80511001c000c0b012901c2d01c85412a0640d01070400d800031103a1f188030f072424815030302070203403001e031500c40089000481b159054403002c0c401e890350b20100c4c4090940045505140400a0034001e0421030100c4095400d5400384014588160201e59007001070741080c2900c400a222000001543d00309041c03069042014980200300c80459121000c42d01213075039201c00c1d003070080407200018a219a14859180400d203101d88004101072600ca42e40035000400c5680811041846070004800c1a41010200410180103407816111149450501d50000c00540030449042040c00b14a882c000c0302c0d0f07103080c007a0000346071044014140079400c01044407410b282d01140f08043c0060351842d07002402c0348a4110303040da500807100340030000c0c0c285460f070040c3c1400c2c7c01880d00140041b518080c0206010081c4c400401d0442e0203000c0d6607885 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 320880809 1250 320879559 320879561
    0x5070302040b0403030c06110d020702130e10110702220e1c0c1401020a05091224090304150905100c02030706120213030807031704030e101803030e0a05010201 70
    0x5401103004596041101304002801a810300d03078418440c2c000412010210207060703485820840460540300d4000411500b1441d21404108036a0000c0c5020481a84006501c503520001c00ca900f0860a55a001748038582c0719010035505c185600918040001c500b000505801c010072181441d90788e0f04003c4050090702d80440c0d10714003075010407078001d1001900881112641c0c50100140c030000214040412010b50078002050307046160789880d42d660043c00c0034040d0f42c035000301c0d1082d0150850ba02010b544200101480303440007540c00401c10548410144504511640e407100006080d42c0403000c40d8250811b03050402c1b00c0049415003011007650340192042074002400135419044008140181e601070501e0a4500150600c0141400d03401145030012026680003650141c5010034032600300365000b012407000040b0701c403074070400e402c2641c0d015003c099000e1555118452074000802440e2050301c210a030304240c034001c2c0388403907920305010300400c9100c40c089018003801c000204080d401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 320882059 1250 320880809 320880817
    0x60e0a15080708030304122001020306010207060e03150711010504031e2d03020c2508070b0a080408371103040513021201060302030f0709030203151012080301030605070302 76
    0x25101961640d55140e407010290107035001e0500074040b899811404040d02230103401981410f02000580e01e060000005e0b2520003141c0c0715504100650381d0751490340e1800b01d4100542a480020004948c41d0382400351908800242c0200c40d035841d140400003031650105144101f0340d0581000031a48203414000c40392030711440b64410303004005518208880742c02c040d4122443d503003440e00504000c0c0541c0a00d080101c03850001d032035180c81c1d1034071880032064446580014490711f4000d007180b80c07070040c000c003031805406550010b002d06440050b0074480b0030421034010390401001003c00c00030ec0c0b0b4614a0344007003c1d90002c2c0c2901c4c00b03450b6410080c0a140e200d601d1a1044000394140791074102080365003a200380ac01c102c015000e2102240104511031030f140680700c07544026841c0e140c20036024080b008014a0242045280d00c4100050784011036803c2c05101c144600300c48540e10b048881160b08001c0e40700303c924031880170450007400300c01c0c009135058034425042800307613480d00c0700e0480503801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 320883309 1250 320882059 320882069
    0x306050609160e120304081606020114010b0a0c02040905030a0e061e07061b1e021c0e03070b0c0309090f06100c03270504140f011206060e0a150807 65
    0x510070703095154083d4000824100300100080d440780d40112505046030890b81c0940002d40c808244171703400c0c11902103da40070301072600c020070008102000c1d0300c203070300d406105615100400040300c0058a100f15401550107802034014080d20b180e81c07600550741d521404400780002e44564040c00c0314a01032040307038101d20f21030f2001c84241c15808010240c41d03200c00402c6030801d50720042400980c00514842e40142055161101500d10181740410350a094081c07000841d00403040740b2022201c11000c100030b50400c2d281245200c51000c1c08249030505035009240941c101085102004078000014480404251890006c588810503c1c1c0d00b01c001c00e4400d01d6100c2e2000c00140354aa202380d285000542c001e25240c08502c9000721a07180802030b40011526894100c44240542d003041c0c010307240584865010000149400c030180c07407040c001801010308880c801003841c0705002c060f401000240044104601c1e10741031800020005200c40072014626500d2100005945180070070510b084030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 320884559 1250 320883309 320883331
    0xb04150209041815050105092410021507140301180e0105010f050a0b0f040303080702071e0914100b0a050c0303010b07050708030307021b0a08060a0f0b030c0109030605040317090105010306050609 86
    0x245609e00d42c00c4841402d001084e860601880703a24a89aa1b40c4e43c041d42881071680181c69404249d0340284409035006040c0c01c20b101581c400d200b07800802c241140e04650b20921684070b95003000080402410f01049108800c0d82020004294000405503900490f002280c0b03031502541d942100b5516800758018004640b80300b80010004240100300e80e580c000302c2d074810784022949a16614000c240c01e214041c40701d2511001c01e100004941c07040c2507203040c0c58041c240440c98800306501c40c04807140981446c88401251200300c01e4010320548484245160540f0340b65a1106c641d80074030340007840191042c0c4a0088000f03007c09010049078010b100e1603024142c5000807065201c51400c052203000e8000e40d0380803001036000b2042c068907002e1311001c0004141d104248400d0fa0940f41130880180c481c0c0c0001e0030b403c000383c0c0c04c0184c00b001c0365441000445c03107642d00c3c1000d855892603422884240380d8000104569400d040d0702840c1607a10641041009407102e20603c5032095040f903102d1420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 320885809 1250 320884559 320884561
    0x705041104090c0306030c030326060f0d0212250f0b160c090e01020903070f140d05010e0115030303061a030c03040c17010c03180b0415020904181505010509 69
    0x44036141e0459203c00318141000300c2c845503207036204103507190603030f200350002101020442490f144911104c0309107140c04020f25003c0c100040007440c07000d5040b050310321601c03e408100f021515a005030f0034080794400c094903144503001c510030f607441c00c0040007450907003848040481c501c400699200182c5004012071030602c0017014904107180b007003100694845902c2030b8001407039019401514030111501002503158171648003818545038090b0015407240c82814002d1040c20000503211440c4002215080300c0c0708000d040403401009900000603d07942060b0b1482ca003105081c810f90b04891003940c040080700d9496141c00d804e060303400c0981e4000030081002c10003255105c405190424001e407100500c5a41d20300c070a0000003800305164190303035194a04004065051711562041c00c42452440d1184000d0782e0300d8038a44800200300600805070503071019509200d95043c2c0701c52200c05041009401c2d0b0800c0c080b0400c072608402214903211243d02a00c0810f0300307020302c1d41201c001030031801003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 320887059 1250 320885809 320885819
    0x210c0a0519120f021e1201140a0f181103060c03011a09010210050123220e070e0103030801031203021611010512130b180c0114160506090705041104 65
    0x1100c0b034a0361094400180c01c48026015907a5000b030b80c0c0d4402c2191044003002d01c520030503c001e10030304070020510b5900d0106015a96400503901540c030041002000640720064011040101001c0c0300d0740304031010b02c4452408001040301081280300c801c40031600282d4500e1043e40483c80240109040c240210bc400c1d03441c0420302002e40301141c014015900800d8410414a00b2120709178450485072484e0155100025041c0c55418110342007980d810032000340d0b140c4800300b082c01d008154000c40e592500390a150010520110000c7c10760b4840c1c2e00041c1d690f03420014850f074000c1c041a107114004a40420046029208545540f242e807001480c1a4003540c4071512307441d00440c2e015042c4001002410004514443c216100c1c880e10b5005800580250804000400005040400300780200e01001c9900c0c500040c0ca8140c1202440c00d0f4201156442408100340076845c55809116885015031040081c00300b1268401c582d100d003100c40c016035a204010941740d2600141c071688400f0802400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 320888309 1250 320887059 320887079
    0xe0a060918020712081503070303020a0b0c19080403020c180a0e03090a030c030c140d0b0702120d0506030c060306010504090f230f060103060302060414210c0a0519 72
    0x126281031607100500780511510399003a00c145040d007020000d4941d900b044043c42904d0604400c16206900030451141595000781d50303004040b03000350180d4101000992400c180300c08582c00c1c1060a0f00040345501c1205c030143c0282030030348048001d4016081c140001b03003003071031091092005031071100e04035841d0f00b40d2200081851458589190208110a01d115200c141500c002180703e02802d203042491030816550f4203800b0341002101240c1111014901e03a500d645450659802c010880b0640e04c0b0042d09070f10340754650008582040021134510020341541d07120301d01c1884143c06440810901c0820801d66120031507825000c510240000e010745881070780980c145484030000014540c02c03407a01103443e11210708003c0901c4030007a08000a5000d04c00b101c0c0e42107002070a00780031a5065034001881401140607203c07060145121880c000c2e61078044240c00001000445025100d160000039101c2642d03801c902d001d040340c0b0000051a0504030081041c08404447d00c000c40340c00c1c00312080b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 320889559 1250 320888309 320888339
    0x2010c0602030406150b040e010b0306060304080f070605180105250c0204091e03140403020a0504180c0806060a0806040206030112052103070813050d1202120103050d0e0a0609 77
    0x113220b860b990007815003082c2c0d017100c520000e06800001c254070389103042064291101c05800ca0000300506009015481e00e42000f5240c126501105164440356494000117150144480c050100c9090105101d1500300d200f4103401c01c288058000e0005580c3c49800340041c0b90350b100c03a02c0c050b40204501a4040b4803603010040a240700500c0418102001d0b184c40030045010f00d4682401c242404078942010b17004030303200d03901102e985c4149080c603185400240c002d07407a91041d039000701c1c1c681075220352040410201410300f55000d002e422800f511820b0135544c032102250518001e03a081c500100c0c50030030000d9414400d80c2c0c010005c91440e802c1c2074a030708040500400c00c0369107200362004c2c1c07452140401d040d031509481d58901c50b912868032850040910001a088040c0840030a0821020580106002c418011070f8245085a552160442c00c02445810502282500418004420001d001c03a0b5030074004166524420a10f141408000030714101e8882c5001140c040c010402c6000002c066070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 320890809 1250 320889559 320889563
    0x10506240405030a080307080106110d0804150c020a05010b0a030809040b0402160813052e210e060f01081f09232104170a29011202010c06020304 64
    0x8281000e95600210780f5200104c10b084440715004000c014505a01030b44590042c2400e00c0e207800300c50f0f951200c99859541c1d08150b02c08100000c0300080611460350404850030300444001c201140c00000000c2d20b8514000c0100d98030750a056003150340b8a03140c52400d0541e90000c0c00c15107408603400411000f45950070040780c1054080c0020300181c2030701e503048000503000c0c0944a80e80c1901510b44180321000b80c021600c0349010444240c1800c0460000b8180070b41e032111700700981c2d1c0340b102060300caa042c0ba401108441d1965201c458800708160000d00d0b0700b0075203d08913412602c440e079203103d581c03c0034001c2c0c1425500010804a09003107440c111111031800a10010f02c140301c3e41c840500d11099107152810403808003003458001c44081098a040a0b001c1c0da0042888407048070f074440a100300c1c400ea02403840c0707800074031f5045072044c0301000d0f500340e00841c0c6954000d480d40020182007400201001c80707581c2200002415940d46150001480d030580d524083c95010742c4d40c000080d0005082 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 320892059 1250 320890809 320890879
    0xa0e030a0b0f0a0506010305070e2709010207050115030f030f121404052505010e1c060b0a0915060804030c0c0806090d05070203061305030c121803010506 68
    0x40d200c08101c20351012030051250312014001841d180c0c1a101c00e03518042d081c3d1341014a48001c00c9180c681c421400310141d402200c0900001d26aa084c110040c1f610201e0040d0402140b4140024084154018002c0c1e038802c40080c091950300c0300c0c941c1c202d05440e2001030f06c01c9800210702030000384130b240d58403a80c50b018203104c0759550030300c4014030072140500d00403e414004c032400e10003800410000c0d42900c40d541d007940340000c5240d64521000341042e11032207040c06040c00000149541d43c0b403400010301c0c5120103040c0c0752640c40c2450800781c03000301941d030301505001311b000c90208468003601c84591f01c14100790404c42e1074040c04842901d0300400c294104880308614400060311008505c000b01b06200040005081510001e0709102c04400c0000500c441001034400684022440680c0012580036103825511139007401c44c1944030710324868540b03020f5582c22290000e00b07034001e4409121003142c01800d00000c2d00a00d8200d41094074659032001e040c1103108207108405000d40d480c0505422 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 320893309 1250 320892059 320892073
    0x1051906360207050a03090e15100e03030c07050f0a08030703080a0e0a05100f02040e06130e0d11150921040906090209041107031e1707210501050102030a0e03 70
    0xc00d0740407038004072400c86494004030001c2003455405082200030b805440c280051605140144910b10280030350a6402907031300e02521071603140150072100320079a02034140c90b40c503440c01c1c1c030698460b140350140600c0b403170350700c025282c0328184002585c09503074928000714640745181d1003d440c0080c00500c240440c989030b0640300c0103010103001c60700080e44288002c01100c1c10b0406810f0a541220700c44d490007900c1484200007101501d50000e40211054907028401e4144140d42409880401d60f5840e40c5c3c4580c2000700d00840e400180c100b0009492002c1d10301040c005103140e07410001c103580c100007581c00506c0c0e43c9512110340c4c500300002d1842106051501e03648000c40c3c015960b880e80b001002c04c3d800b0441d540c29080a0051810f4051640d05441c601000c075500075020134118459041900852484890158000da110840e08005c0810789001450b000400611011004160b2074558907480020464030705e25004840c141c690503000b96050046c884003c070f07200400054465030500c240c0b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 320894559 1250 320893309 320893409
    0x91908013b07150f03050a02030603030412170408030c0105010b180108060d12050a08130206030106050315040f0603051603110d0c0f08010c1403070c020f0d0b0901051906 75
    0x400300c4030040550303280c0c0e000070103031300340090106c6134000d20301c4e6220b5004104100d05903601008590607500300344258070443d00c9600b0860b2a03080d510700e006181990010300400c1140c4000301900705140707104e009010503a26001c0a1100d40115442c070249a42d0140c580042c56005044c0342c0c1e13000c640544485a144030a8a501070707400b40040c20350700800d400142e0319072610340c0111f02a901c11004a0103940f4210144c1c003242441c4014801d107010000013001180c01c41c0140b881c12407520000034014444410204800d9000f000e83d031004665034414035030b81c8820881c288420b03d0440760043c00189060034003a05020200780200c0302103405160700e01c408102e036580429814007804c80c10000103023000c8450030142c6100200403050300404400d01c10031540543c854401d081c0c891b4107545114980c1c140501003003281d07400050003000d4040740000c114954505501c001e01c600c0c40c1d0211114171300524012601182c0082c003c401d1602a02c9103101d10840c1c0021585d074072411001e00b0100c22070300d50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 320895809 1250 320894559 320894579
    0x909050a0e06160f020303090a061814010506010e0414040818032b05040e061c050a050d141204020907090510230301051c0206091908013b07 62
    0x40703541160b030030403906000203141d0748284c146101d030f5080d000031851401c2600302140c1e1000409001000c4540b0703140d9400e003240744002d5603a48640d0182d0442004a00050090301802c0c0840c1c0090006000c407001c00134a18050090404020344582c01d6a6140c80d19100c0c0034555002c0c1c5044042da42e103154425100d07032030030000c5400074681400b1403002d01b40c04490b001c810b020011701034070400c0818042130046084030048190406000c481110b007660314401d408003450254180602240a504070b114107215004c240e07007d1112045d07030f40c1d03000c0502440340c05849008450300c000203005848002801401c15660b0603400202030b05000c0703401c2d603540001421480da81304c108030008480401071419104894a485c4502c401880340c00d04540c18200401d80700c0c441c0c0c803031004400040c100c076a419500c801c030031100c100720040d00e034455451607589288440da0661064502c0f035880c0018101c050b0881540b04c140d840110400f81c4036440032618400005440c0030400b05050103101c6e000209940c00f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 320897059 1250 320895809 320895811
    0x1021308070e0c0c0d1b0c06021507090f05040902041b09090b01090302010e01120f05090c18010f0b1b0114190603150c0e03030a030914010902010909050a0e06 70
    0x20001081c0482c200103480c00381c2c0300050010712012606000610700341002090042d0740883c1e6280c203d210b4101d88104c2100c0c40180301c4040c00c180e003075a0004c940194045030101d103440340840c410f081603d54240885007801c0314801d080104002c09001d00c07003032038180c0010450900042c00800d14020030805407040c595210702400c046407442c2c104020b95902ea00807401c6149003420070016031403560b000a0404005002d056042015400d04111842d0065100a140d0a240303202000f0910703052011035582d41c1c60b41c8000d449099401055440300284581c92070580f000160020003075490504c00c0007a6401801c0b250301c1001c1205111114141c2c00d01c80c07010aa1500c020706402420b0180003501b018100f40c03007003c070640c180203081c80801c0b0040880e810214000b640091042000801100c6c100e0625801a40c140000142804d6155140c0c101c292440c0c007440011400b00c55a21849080740c030424802400709146032801c0100e10065030009500c07246c075482c08942442c0c0c1422650030024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 320898309 1250 320897059 320897069
    0x1903020306180601090c03020f12070f0c05030412060f06030303060f080303090c0909030f0304120305160e0603060301020705011b140a0804020d02011413030b240f0f0a030c09140423010213 83
    0x361030000c0141060b44040c0e33881511071941000d200250302a02c44544900c50341c061030148074447c9030400104040d913070001c015031540441c20040c2075281d01e0020b014050903c40d0b000c201d00c0054001c258440084101c80c01502036000600a040c030241c2805134014004000d2001d81c0800d203c0301000318003000c02544258480c840320022444951005012500d01800041007030002281c410b4500343c020300c0d218001d20313040b9003494883d9121030020b806481005001040c950a01240100741e86801c5500900f003015522050110041d0f803007030348041d000b68a40d0f1030000d04044081400740c10842201216580103251240310440720100b803640700d5120042041140c40f58440c00c2052010000301290080d418514004c1084031450b4118aa4441405400d100d00804540038001c0e50f180150242048400b81c0910282ca42d05d0500a03982ca001d0720401a5080c14104405015410442e01c507201e0b41d0312800e1581862508c1005800482c42284140c10703a41d030801c024600c0d01c01d21566500100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 320899559 1250 320898309 320898337
    0xf100512100f1b12110f180d051e010603170304021002010501050a0918050d1805030109021309060b04110c07120b160e1903020306180601090c03020f 66
    0x381030400320880342841280358074186001d08051202c2d1018050f920100042d01d4014008248682d40078000e180307884d41a0040c0c0e00c00100004c0507401c2c4009000021120701d5001c0c81e0319042014040e00340c0301203070014020b03004521900c41408010080255020784c03107000103a0345841c1c0d5508040c40c0c1c05000d010602c2d09001c4100000c42c40c200254040e003503c0c620080c0301c25450640800c0610545016000303866844e0386e00d014a00400140e0b00c4c0a01c1d40002c102d039072035260180090800110072583c908080a1b40e68045901c0c141401141400c9901400b010f00101e0180410300080804417801c880c4140c039080c41d00482e99640c040c00356001550903410381d40b40c06507010f06243c40d0384d5600c0708030050040d04500300800d6805081651003c8402c02821440c07501031821035151034141c40c0d1070703071012644001801240840a81c0c0055074030a9045414070b48600b000310304950281c0c00011016802040103000c0c00c0041e80003c00c14034101e0801600342100b01a200a150700610300c894201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 320900809 1250 320899559 320899573
    0x3040b03090316030c1e152016020901140d06020a0302120f060109171903020703060216021003020306100f11030d0e010c08010f151214040c050102030906030f100512 73
    0x40305901c101c110b502c1c000e85c650344c0740c2459a6a582d8000034503042c401009541d4407401c140c0022490841411020182084950b03038048001401c0d4060080c0350040cbc0c0950b030408000b244080212007042104440105445960341e0290340704006907010000344410036800303000300c160f592a80301001f070180c0345c2c20480d0380ba02d28002d00010101c036800e900803155602e100e0407924180001082c245201c0f403440402c015171610a003000da1810a00e0380c0002c125038400644080e44035075250402c4c3d01d02d4400c031000340c0802d010103001c40582c04141d5409611010000040f4178041c040c41800840b4005412300321400070010403a40d065400c43c00002c0005a100e124031400071500b8450502d02d00c0740e5091032121035052185403a40071800e40140403c58200a52900d40301d400b404502200d07143e0ba04090002d007041c2000c0c0303940c2101c25101101d8400f0b02c800046110343c004400d80d0303d0580c000e0005808d43d9a21042d4008180c4003400110160b4590304003ca01d80e01d5074204544d20134005c20007000750f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 320902059 1250 320900809 320900813
    0x61203070c06121503080c030c1b0109050f010806040f0f1d0f060705160305040b0403030203090102060627190207050a050f0c0a0e06011101020d0603020a0b040803040b03090316030c 80
    0x298400707243d40360451910300641603503209502d80460050f240c106191070340300e00152a2240c550301c01c9244250251268060000840c050340f8a411441072003230781c90f6017140750f95400384100720550900c0030340850120f41c006103130b500b0705600600310036440410200da550324400c40b074412245901490b500e8102810f90440300514200000e00f0900e0400b8014159440e01090003080350003141400c3c0a030303c1d01a41100185071160042e50080d20b00c182c1c200780d5555a03481d001c0e41c0c1c1e81c009051a8098041d21002031420320305043c4001d103800082100c60000c03240c80260180b00c18009028500303201c26000040300031000d41c405803106c0b600c900300400c03170f045503030404901c0c203030744030800c28080e500202c003003440d68031581d0010086602c211807030010343d12041c0060780c00e84100c032101d41266102082c04d891010302d94000c10100c0740295040f00c050b03034861407070012030703c50360103882c4103a40200000c000607480e0100441d4400c085c54290780c1014a04449110040402e01c400d800113081c1d06540c0c42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 320903309 1250 320902059 320902067
    0x915090b160227060d030302120f06030d030b0f060c0102070f0804082e020313151b022d030d02040807030c0509040b040201111e0d03050702030f0405040203061203070c06 75
    0x1515015901403804a00c4041201c00f40700e103004080c1e50103051781d09031150401d07001c0d80640f60508540ea001002038500355080f0305d00203c044918612074407401d58000203aa000380700300f043e00b800c080d051201c048a250140012a07002407800c44403076500300200008115912802c0642510401c500c0c1ea4070f0749000702c1c40740350002c0d85009540e4801440d01c00207a954503c038095500c1c402c02a0096125918401c84000740440514058480c94100241501c9140e0303c1d4003408503250100d80418114100d02800c070382d0303600c0162880e01c130490246440808000515450075440c030360f1400301c910301b001d607c060b98240e1b02709a0101d107980d4048074050081010100050015000994689100b490f01d034607521401240508003070306101107400d0f411420704003800b40d80300700c44d051241402000c40b8078503059500c0d1240f4503100b000031703e09004503040d00d10100c03c950090000ca00024100b40c03d103801c00009503c05058a9800140009111024101031015045850103211f4510f8403614004002d8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 320904559 1250 320903309 320903329
    0x2030f06150d141f08101a120d021606050405090a020f0a03090605070f05090909010e010c020a0209130302030703120b0418110f0d14030d060f0810020301060915090b1602 75
    0x942e8248112042c0700005c800620341007102c4030880081281c40d02d0032192194184503c2c2c41e180c1000b68040981c1c0c044000248010800007a54211025000c410071000305504460140d0000070350208400c01c10303894282842900004280401840e0030040d00d0f62070201d502020003030f400300f6111400002800005d2248a0341715180d0700380700714110b0381c44400902d940715440d8017512441d03100c0046000420254004910001c14100802821611410103555079610080891241c080c9800180103420401c0c0003248041e0f05030000d50038940507075000e5400d01040400b41104550340c125054003a030b51401181641010b010707096085014904120007030300001e024480c05810134040952140d110070309442011170300b00d40518000d9001a11a9045100751040400402d040c06004541401d5a003520000c481c0c94070102d4001c010185200802d80c00309119400100740e11000c20000c2c40d9400070206410100392400103c0913854195012072900032102c00d140941d0345400380340840c10445000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 320905809 1250 320904559 320904601
    0x10606050405150a0309050105130501151a07110907030621020604060c02060405061305180403050a0e1206041b14131d060405030703030b0402030f06150d14 69
    0x345150a00301404244402002190b100305640001180c20070284a0713440345201d158408000d1000741404440c0218206518105546a521304440d030b000440c4150280811201c00c1500114001f030519078801150704a28001d680008000c003004c2c04a07070700c140310f45100350a551400150503080004060710269405007c1d92003000000c0f2020241c0d4a080c191400c854840c50314076603070704807403000c1081c9004680c80300303400103800f164849a00070000b5a039019100c5c117403030284042941c3d030f01401e00240140c60190215800708860040c803481421200454613014080c012698554945c0c1450140100c609560b0000080d020340b034503000044111000306080b030050310840d10b00c80000380b1200c101b4003100140079038407980c465984072140c10720340341412408261101c03480c0c2814081d880e94082c0c2001c6002078a0321000750700c9480c152003a0381c090840d203500218299190010b0003088211811140000d503000e00ca01c80c00c0c0da07150301a90440300d81000c81107009083c080d200034400a141024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 320907059 1250 320905809 320905817
    0xb070305181f0f0e03090111150c0f070b0a0507030c0c0c090e0c0303040b091306030f0f020102030c0f071701020715090309091103040c0e15092e08010606 68
    0x41c01105400098546442c42071450b22200d1611a0401d5030000c1c48032481d01e40c90709040c15800000041d000c03000c1e0101d00705c2a25020842132192030160344903603d03883c081d56040317074540104600c1ca0111010302004d01c10301c03003110301d0226991178000010f2000c03500c211000d51980f042210295241c050380b40d19040038108140303444e03680d541c0e014219203d0b000e0303150801d5481071001c0f0919000c2042c010003074405001e0306e680d00d0706e603a03111441c3d500043e0880e00602c00c51880381d80344203140c415007007166041120442c0d404403d0b0744030341e0b003a40d00403800e80c1144003e000b003010070344086c082c0e056030410716401004140d00d010700450003801601480901c40c0d20501210000c500b6224828902050200000945103582e190580340d1680680080640c20b01d032804503180b540d8100300940c080c83c020a4458910344d62440d00c0b48000d8400c84d04203402c103110007011a0b00d804c1c034410b6076400001910401d00805403d00b441781a402418200000800081c40708100360bd00030b2140c03401030305162034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 320908309 1250 320907059 320907091
    0xb04062c010b07030503130c030c1a0301180c0903020a09060306050a09050a17070807080c06060f15090409140724020705011b05060705041802030f040206250b070305 73
    0x128005180144400030b01840000800590a21a03c8090042c0b890f480200c201c235081d10390401a58041d4980280784501d1001880c00c484050035606a80c101d0740b44410f2112140e400c07410b840701800580750524240281c03400044016903900e4552800741140d240c000691502c1d50504d44191400901000205480c05850b0808585c005c9580456076030022040080022020f241a8292240080c0503140400120b001e01c2002501002803140e01d03030003000c44449032110420001203072040c07184243c1c00030129848105c5e1115040180840d840028400500da101c0340e04c030403078080c0800010807003d0708212018014029400300c074007110001031f8141ca01c032440800000e56542000e00409060104c400c200744802001ca920545a06038820b00b0341c1c1481c2400200503140340c2003405000348400344882c1c15400710401c0e01c00c1c0c0340300b45034000760741003241c88640902c0580e0340007010310032160500080300c0b11035048540c941007009100c0c41d14021f2a01d001c105c010708560002e0821891006c0c0f800c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 320909559 1250 320908309 320908319
    0x501081c031104031403160501140c0c06041103030c0f2d060a0f0e0d0c1119050603070e100807030605061c0c0e03070f03021008011a0c010b04062c01 66
    0x20b0544090303c1d800380c0300d1362204003114a55490760046000f104511217228490204220040d001115000c541e001e07c4a9283c61300241e405060240c120b0303016180d8007130300c00100841c43e0701c19004240342005e01901c0c82e19024901c8507080c201c0303014a004081d4002d0460021419019240000c104050980e0002200b510101d0589456024045034a403d131504280d400c20300c06580641071503800d0b10100e070100e8880000c0540070302840d2006580d681c540110344940c904001d42d1603109224010750802e0503e00b04070402c0515040036251400f04078045a104583d900d80b1410118085103d13190402c0394a01554000c040c0c5800c2d81041380a01c60038003202080007400a00480407210003076021503c3d031801041150400c0701802c690364103125083c4002079503540110b2180c10307a4001d0311401d500c40c07010300c0b00f504c200800784a0f8903024030710b640c7c4d040300b000c110b41d0240044007021800407840c103045100140c10f50b0f102c2c0c2c110804500711458a400110381c0b12012001504c8643c5602010358940 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 320910809 1250 320909559 320909591
    0x203190c0915030b061c061e0608090f01020309030d05130f020d022206080111031006080709030503180315160c14010222090b030303180f010501081c03 67
    0x58410720180c0209651841d074840c0c00f036007056401c0c0d20064069511601c01c0300c1c1841c01c01030314400c0403024924111010410704c8203000c45051413103100030200b070094a0031030200d83c64400209040114000c410a0880504003800210b000c2c00b001001540c441801000c1581100c002030301800790726500900e0300000038110a843c80700f0980407103c481c03030455980040346240803030315042905404020f041711545031803a4000c0d4207a41c1540000c02c11b914018034800c9c0c1c1484140c44941090704c640200f080311610955040d0351000c0985004044142c1e07036510310f883c681014031504400500894407d4260138100b1644001e240719480b00740d564240202684030444450203140d040040c5006840140300354244199900341d40480215500d50101c14600041d00200310320340d0b0312460030074001566507031500030a01c4401d0001c01a62840d2a1012a0510b001d608600d80d6403d00071801d5240b2030304e0080c420907008050500240000c40c45e2800380c141c44840204015050525000e0490000010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 320912059 1250 320910809 320910827
    0x90a1403070e07030e011b0201140f18120a17070507120f0903140c011e050405042a080f0703330b16020a05010c150b15040602010203190c 61
    0x45202d115515441021005800d89100f141d91030340c2080c03051040c02000c0f04c546107012240e54020480c5800403101c42403181b4040d552060382c000f075040070071a203500400d0045001b40c3c600084601c00402100308100e10b40207401c00c4004621141c14106912000c411180c0e409485480c042e450002260b480030380e04410001c07400100180c900705890500e0040c682c138000b85030000008181c003da001815aa642c1c401034640d4009050080050030301c401607140340036500426112203042c6800c01017400300600c51a004140d48034140c40313190703c0030110140b01144400c00d40d0b591084074500707601403041e40c1801402e000d04040c90403024803440300e140300c1880440c0d4907240d404c2606003018000051100401c1d0803080780c000300040c072031552010340b120101e00c0707510907154044541c0d40d0b02d006488410b01560082c00007254000b02c0a030b403076000d9201d0280720900404445044c8060011040e803901700350880400350b9400020f201d074414002e154500ea20260602c00d02042c402408010080c6030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 320913309 1250 320912059 320912069
    0xc1104061707051f200313090e0706020307030927050702030703140c071802070b070504030606050303090d110a03120c05010605270a020d15140a03170a0509060708090a140307 77
    0x34442c0f41441e04207030301b80200c4c2c8206400c55044115184c0320610303040108844034a0300f15a11480c1000642c00d4000301c2a55025500340d10780c010614601500f803840b00601a0020740d0300244c600808441150702d100e100c0c000c000d107034000c40e11001245400341c404140c04001c0f406004040c04070351000d8600003030510a0700c880401e1210000d5501171408017900881d08018482882601040000369012010344208c0c0d01498040c000c10380d50308181601c0c0e00c21140d249030803804030304d060b43c086030026000a84c007000c0a40070101507a501c0d162038448807080271140300040d221505090500c00240241c00240c41d0498900b5000c4c00030103000305c00095540c44802c25503d0b4080040c60464090303054030000000c0f048207010303402042c450481940103d005005d01d007444002500c0c17603070402160b00c1090740d07400507444141d404e0441e12441241c00c054038040c100542000841d0385034803942c014004080c4120304213070301c0302c43c0d450070072045000907042145151a822042c2c0000c0e64001621011a9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 320914559 1250 320913309 320913347
    0x260129180609030d0e031c1b03020c0405070f12020c03090d0f1a0f09010e0c06300a110f03070302180904140705060a0c1104061707051f 60
    0x6204004540d81c0d00841c07440c5a410700803107103c000b01e95005020341c20310100031070594444152041c0402c2d22514541c00c50400079603812200740f98640e0501036552a903000f030044507a8200c10701c00250a503035084411200189098140504042e000344802e0b0000b001d084044d42803e14003c030342641ea00901004601c200a084045018031030300340c140c640c203190440302039100600c0f01214051441015102c22800b2220100001d018003810b2003000007103000e66001d0100d01c0044820401181c00c1007050031035074542d081c40742c0e0689007007052a9903c044001c81c0000310380307040f40251088a15070405443c4100b030801c6803640c5030610300110707076000c1110300b0010385890b0b0203000318246a103008919500401c440080c40240201010b500d041c0c1c2d4800411149603685410920000f4001d2055450104142c04000000079210b05078620380504040c00c00102d048d81c0318141c41c03a02c0a110044510340d00030750070912403410840d207201202068080070006215040034020018143d8038100d050b00307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 320915809 1250 320914559 320914597
    0xa06051504050f040f06050a060305040b070509090402090a020c0304080105190c0906120f1406040f0e0a0b042d0b0f0105060313050c04020d1d0a02030703080a260129 73
    0x600700c90362001c005011f01401040f00691112009401060b080e2400e4035441407842c00564054443c2c02103e1071110b010300310440da51203a1382032041510010300b10290041d0248032409850f1401c0000c2e000400320750b4004103182c10855982a00703403101c0c0000c2400305050200d08000c1c1500012000d084410610348101a4214150560001c100d0b03031292040b850300308050548540707403411050f0b001e0001110304100075018480c0c1c40e4200c92810074032001035041998520042a50f1401542e800380c02120800b800001140b85e40a0801302e0401c81e52807215100141810301c4413a1400a9000c015803295100307650400000a03260f010040c48421312485074401c00c81001000e109900121002800a6480d0000c01e00300001a04400490030031482c01c240c0c488011341ea0010b02c1101c216005009801c0d0241183c98090840c4c1c0510b50f01c40c11f00c181c08e040480c150408032860030070400340e030001c001594107101d03080f80405802d0f2601c80380005074007455002040440c04403002c00c031640d1248450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 320917059 1250 320915809 320915831
    0x303180a050304030f03030e01050402010807050c0106050a08030316110703020d02040e0d1e0e060702060721050415030c020706120b0a0e01050901170309040c0c0206030a06051504050f04 82
    0x14200300d01200038002c1c00301240000c10483c1041c0303140881031003601d0130b0000c0c1e440e1a80f014201c820464002c1c0c00604024041840304d8001c500500c1c0c0c0ea0340c070f08008182c1c41e49500214107003180d194403004140d40004200200b9031240034048817046006c0c5000003220003400c2c2001c0e603507000e500011744604140b444001c115616035101041e445600790540796082c00c03150000c0c060040300d03c001c02c0101c0c1800381801e0610706c603100a0600c0300c401001c0740e040590540a00c041034214240032904510050600960340301c050030300e03a18810f0f1503500e1070750f50b50401641503200300401300c01d0814141007070000000300d42c0209412023035070071524002403510340b01040b90003d07201c00403039203401c13540300d04011603a0001e14210034140d5400381c82c02e10140c0d90714904403200b000c4d0030b845508160000e000c3d4039001e2525803c03000000c410340c5003403544000c89400140c095803040e64003408165444904110a04190785003074441c4030340e03503039090405103048081006c03040c0b80381c890351140fa40d6420500d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 320918309 1250 320917059 320917063
    0x70204050606070b011401170a1b030e1b0d0807050303041505090316111509150702280504050a05070201060e01180f06030503070f03121109010c051015031103060405030318 76
    0x1e11265212030708c0382c06003800e41c294401400a03025100341c02c0b030802d210b035150600034001d070045124140010004a101460b0034a900d20260101c43c0c0d000020382404000701d0300c03034006058200e000300040c42d41c80c18207241c42440720f06500301540071103041900300b001c0e9031400302c00d484122100c01d41001e0050b02c0342c0760502c4c2243c1c4161800c0c0c0d01c0401d40d070b03492002d184d00b20040c00d00d251040d10610a8a104d08801d4031503070041e203400035070101101c0441c68641d4030a0049040380301605c1c4503401401d413507000050907140c08541c4d01d828030383d440c4100070070a507090003084001c0c4644a41201294103243e419041308041b0514900501e440760030700ad1401e02198001c0c1c0043da040400d0ba6202c0d121882c20599419210005800046000c41c008a00c84414440d50106040101843d0320780780c807000054502c00c8503100165240e01443c42402c0107000343c0d0080d02100c5148418007100f440c00c6207030041a0030440c0c0c010f02d000354851020040002c000004581e0031000281c0c1c84042c0c12441c2e10514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 320919559 1250 320918309 320918327
    0x8100504050709050103060e0603070b1b0a0605220b060d050a0c120b0a061404090303020d0603050f10020309060402040b1306060305180d080c160804030503070204050606070b011401 80
    0x1a0414a04402c1010301a880003051064560036642400303865524841e004002e041642d030142d040c0c01c141c008008000304030b00180741000010243d03041c100001c000140c00c115010030190b58940d01e03202040f407040c122a80100751450700c0c819100c00c0c1c6030503072214080e454004000c0ca0084020202250621004003d0f102505601500c2030240760b46601983c220211102c1c4100c9a828445020409082031806110301351002c00d020302401c1c1c81c842c401c03c4041d11400c103041d01855400c02600038040154068240170714098802000220a07052800b0b00e4190b1070b02019942602c144148000580045081034006030125004108814131200151b40d0380040b290180241d80b500000241d202d403d9000507104507404041c07007607400005000a61071b100301c4010440010640303000980b13400040d10161a900d40c20580c8000c86c41e105036500110380d4040e81041d1080d070b0001c60300d1000c47c5803030702403568404000d4480c5418814903a03280401c00c18180100e800f62400401c0c43e01059225030110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 320920809 1250 320919559 320919569
    0xb160908162c0114091e0f0a02040806160e01020d05030c090303091306030611030c030f07030b0d03050403050106051207030308060f0904201219060b0303270f060301060810 76
    0x240c50b03565200a0500c1d1046103402c040d015240c11400610710012480400d012201c201000c51201d654100810f91482c200034521030f00190300344804104480200105440f0300300c2c042441d0781c10003080304017408641007a1401411035102c035501c0f1040d19401b8050f41e40020a909036142c40e21880c0380041c2c158041c000b4025004034031000c116a0b07000283d00080c080768010101000703a003c6442d041510740c84101c0c1c5158694000300080356040300450803203640600d95182c000740d030011603400200400b26003941500015004235013070003446001e200300c1d40142011a40c903070484201001b0591281421302c1302509100382d14000401a4070b44d081c44d800510802002c0402d40e203130a2078845e118080c0c5400c03201d551422003420326518200b0713100354081103031400028240100402c008103589030800c0001c81c3c0c00b9031a0502c444a40d1800c0018040241544040c08102005424468503401e03c402e541842070f44440888405512917004580c15a001c1c0d00c0c3c00e0040740c1e51940002c0301860681e00c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 320922059 1250 320920809 320920889
    0xe030a21092901060f0e0906010306030c0f030507080c150310030c0b12070c0206030604091a040303020c0f0307020607151d030a02010b180114010c0b16090816 70
    0x4140600d00c160b080d000c0d00e210400140102d40d8a40600701d80503007040c1104804580202241111407401120b0203a20000500d0082061a2255581400f071102540040715410b0a1402803041003000c0c001c010143c06038400801900b1902000540000b01400c405001d000b4000081460703d50510003100c09990050b11410340c0700d07076554a03070f40c8a5010000303c0a103c1e1065021400c45481082c500d4195070b00101040e09540342d84c0e00300002000450340466003040f40081012488904001c01c0d8403aa0103a200141c4650b83c1d001180e04002d64034081203410b4100300090401a51000180c80402d80c2010004c100c00c424a10640010482c4035404003055002080740e03d00104000300819503980d107a40280180c42117903081c00030804820040d850350090307540041c045c0440c1c841c00034000f6001403500d00010f115903110503005002c180c0d48070365400044001e0801058101680c00c0043c80c516005107000010b031004482d2071942401100c021001941101d020000a002c82005c04c41c03908103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 320923309 1250 320922059 320922083
    0x10b0a06030b0306340207030b15010e09060d1a04050f0303101a09030a0b0114061201140f09010f0807241d0a0f0e0a060608070e0315130203010e030a2109 68
    0x4010759550248c0c481110b145a10000044200840414951300c1c40b0040e104d0f071514564440c1088505140100159007026440901c9070200c1d1030116a00c45004258016625174109801c1c12820300580c03000e002034940c010403d020140c1480f012800444404001c034481200c098004c100c060310490f04001d030306201c0d0080340d80c24800002c5003d030489000c00380c83c1002d06003141c14000c1c00e000d0000d2040320b0b181c140e0010044681b2400000340030280c01480c1401055003103000604420080e04401050924000180480e400401c0701002401030120111001d061100c3d0311001c02c045202050f042144200d2600305940d0f480c042600000c0008100c0d0350007a0710784005441c101d45920490050305ea9000120f00381c0b103014402e001c165103040c0e692521661710b00d80d003604c03140b0075107074150741621030000d41c901005140d0a0480c001d500128480c40300d110769004241c00c3d0f541d0b0204540302c40e0400c009201c8101c0d088550200c4200442c01c5040100c4c220380903000081030703c06000783c1005010780d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 320924559 1250 320923309 320923411
    0x3110301060305070201060e0105062203020d0c080d0327051501090b490203010c0c12030c020d0f050d0e010c021603050c04050405011d010b0a06030b0306 68
    0x600010304c2140d40d80c0c0208015540d6422802c0e41d04428461690403000401444c03140d00702a1040000601c00c5180b0b106585035258046030440e0700d9007105980d2049004000c1c412000c0038440c0c811104400d00d030602c4036a00503284001c40a8110300b9001c0c424510035054003c01109010002071000c040207018803e42c0c0d02e0b20500c016080b0140e2a42c0b140941682d03d00c2990408040c040351190b1000130000300c0340030201c0c001c0700710600d0816504901041da41440c0165003d001d0f22625060b20740c1c6059050b4101d20b08007481c415001460b03002d05003080c429483e15a400506241505010700c4c00026041000300305660385e02c9151103401c40c081c28a50004003400d8150042c49050040703508440102a502c0c03800551719076036020007416500280d42c110032030304d0f0681100703800501a000000318000ea001501ca03102215007001c00b8103944810b4291528170b04100804010090342c203040c0b0011604500098403054010078000d0340040b00282d17600742080c1d122185144110145080612440d44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 320925809 1250 320924559 320924561
    0x190b07030b0a18052205030910030902220e070e100602070812030a02040b0703020109022d0d030c0b0f01051f0c021021020c1e0a060c031103010603 65
    0x12551500030038140820412981080039510303040701c10246824074980504a000d601800c00075103491018040f0243d14500f195641c0494021144200c00955a41c0c0b09242801280402c02d05040c09151408010f000580c0314181401c010046a501c400d040c505400c16040c000c1107a011180c442d0303c5480c6020420070070307150402d4050140207502d02080340d5104001c03a81d03820140210501d5400950b1514001c0e407040c07004d950440c1100101500309625132041c810250413081d019001070b0744410703403c0c065042069201944082c0d401c13200c09007441041002104003000c007115401400001c0c61007050511030b081600c2c1c030a60000c0c1c0b24445061482c40303214454403c0c003c13207104194010b801e0342050b031031824184c000303a40740c0c440c000446401e40030000d291341522145001c0c010242010f02200e2102840c811140e090404010303162001c801c001440e048071032074030708104550006808200100010050f45d00c81d0301c103201168402a01108501030403030404031441c1e00d580407001040383c41d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 320927059 1250 320925809 320925811
    0xb160204050916090e120703080f071e0c11030102030f0a0506060901091203110d09091503032003090310050703050f040209060114190207050118030b0a0e190b 70
    0x8a409200030340350550b0007501c5034505141200c0c40c00a0010400116100c0c0e0800311130090f600b004d81d66018100300354403c0a03803001c18201c0c006044c520401241c81024410307143c200d0840d141500032026a822280c12105080100e10305100c40e0307401700c0f000c014002c500c40588e8040035000359201c0c28a12080b5405e074205544102d9041d051600103045411b0000907906485016510820040d10703155694851a600039002e40030041e10816070242400f00700010500d000032599001003c43ca04281601140d580d030900c1808215003120800200350300200c03120546440c0100c6284442c1c4920f403030740c80e51203041c00d403a415024440e0002c903200fa403540401d1080a440e10240816a10b08004104a0780101c4000b5072052005022406551040540b02c2e5010104081c02e03180c91640100d10744402800d80603007006034880710701481103590044030100c03015103944401c2ca00d6400c5944d81c8102000040500800c1d60f170b280b55501c03075280b0802800e423024040044070001c400080c01c00342802c0e80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 320928309 1250 320927059 320927063
    0x3050609010b030408030606031807030c080d03021c15080a23060609240306010b070311030406080c0a05250501110406200a0203030d02030108010507050c0c0d0c0b16 73
    0xc000241000b1540c0440e44110760080115186a541d602080341c3c0c1d4202034005c02400c0815140303040c0c5400c0400085020318041c0145080c01450404501c0ca8001004d14010805006211010303008124003503900140e03440e0500452140c0d510901c82d4040c1010b90b2060466115241c841000d0004d84d44900b58980e004408124821807100042a5a01d505035207150b008200c1c14006001c640f004040442c900c0d00c44100a400070304100e000034601042a0041c3c0044000014400101030b0040a4489080c2d8000051400c1501d03040e805040401c005000c242e07645000540710b10803034810f03001c64a03440d40c403280324001c1c001c81c06e8040c0e04a11030314004444641c81d140302c54400410b003000b80c1c0c040310300540d81c4c8003000c0f081d03161084d40ca0b04e00c03820080b1188640c0250900503a4140081c6c02d00a421f4600140c8a40c50100c20b1829200c01419040a0007400c02130b0720712100c000f0600b10001e10003921800492500d920301001101165801150390120205440901c8507200140c450114 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 320929559 1250 320928309 320928319
    0x1603110405060105040b0304110f030703080912010501080601060e19081e16050f040f060303020a0b0105040c0c081b0f160b030f13050c03030a0801090507080405060711070504060303030506 83
    0x10ba28400156800d1240e4020950302203414000a0001511102c0300d210482d00a01034401c541518401b091070221290012241401c01081079001381c144254007420684d8600c0085c44594501090649c680b08180200c0080004400f2004000e442c0e100c04107124205050348407024603914a181900c078600783e5465081400c0b04100300d500307000d00050854015950100300c002240c80e10701003003030381140340c8400e82e042a00c0d050800000e45840c4150002107000c2d03005040304020301c3c60085c09860b01604803612035464520541521039211041c220040d070700801e644d90f070b40004900d14051000195542d542e41c498951280d0f800302020403840b283d01e184140d1104000d458803602400390100710703003848c1910380c401c0014420380b0241122200c814000c205454417080342c0c001190840c2c0c031001741000818082e000401030369072a80309480d8491614a40fa504508040c0d0303c254803400050b042000300074012070020102c510621a0b1070042400520400c2041d9503890042d02400003250810b02c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 320930809 1250 320929559 320929561
    0xb091302120f0d080627130510050408130902030f0f041406011e1a1801050c06010909110f1503100b070507030308090d0c03031e0f0e2415031603110405 67
    0x2400416100c0c00c19246c055640740203981d84120500e01c4102d00801940c9510890a40604100c840d2003001d005d5030044101c1a52030842d9101818420702507800580d00c01c1c410001c100e000f000407000c290b000010003089074010b40b141e0400107014403038108041c1d002e010308000080c042e13040495814080b11002d40c01d214003641c954840000130800019442c0d01c00c8c04000180041c942c1100c1510103080504199040c20a00d50f003d03031030400f0980215451a070350341218001d0000041d40c80f41401e40072a04030002400ca6000f03d0603040221140c800348000100101c0d81a802564851000d4018840000e0310382d102414a40d6980c000c9104c00d90124400101003110400c020420300e0005000b0380341c1690b160000e5030118004c1101c0b40f03014201000c0030303808404c0300c006400750441c407520461000c10340401300900c2d00d04000302003c01e82e0201060710b940101d84001d1200306588580944034030043c81c900200420b00f4a410b2514400c041c9002510100801c000308061103402c040c1601d0070006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 320932059 1250 320930809 320930839
    0x10815060c0606130b15030601090b0a02010b03011b05070f0213090f120801050913060f0501080c04141315060b03040503040f0b040f09020c0a050d0c0302010b091302120f0d0806 78
    0x5c07100d61445103a0040d10401503009200700810040d40c00c40818581680d12956450303030500d013030b000040232000507510307009542000e00d000d00403400c910615000d4000b071f040a074180074000f841034060062005256980b1581076503a60030180c06010390346072061104020900c3c0400c004111040b04a80c010031121102034018443c4142030b042e618042c010a170a61228581034500c2414900121140742e111b90b400e04184103540200340c002e040c070400400b070038182c0c88100025a200c13544508a285505c5003002500010003c2503a002600b01000034022440d002e40580500442e8100e00407000c0004148001c012001005100300d844603818403041301d03184c41c0204140d100d14855030706994284281400005910790041c003100c03140c1402c865140101c0d6503254180740400d80c03003e000c03411801746101410780a00400020321022145410a0310b00b07005180050b1050880180c059580e00e51619070b035a4007086001400c54410702100c00e043c92800c4020500c01044a03858001c0d070428501c152 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 320933309 1250 320932059 320932061
    0x101b080c04050a060c0f0507030309060206090d1209050c0405011d0f1501080a1d06090c0609060a08090307060f15090b100e01020c04090b09010501060c0f02010815060c060613 77
    0x825290b00601d0380307111510740f8078226030314260840140d514640c44001c080c00180b0412030070000314441d440d044059490700f100a410600001d0940c0d085070065a20307021001c3d0300011183c4950000d040c002008000c40c10300d9860b0600c203e42d41c9810070b1030500049009110350030030580040603000915040d641d207501001c6566816a03500341c41070301c028800351003903000d0b10392540e204100060000d0551070f0041c0c40d07a03562548120407090b541000d0184021844140111004224244c90152074544106c02282c01840346003190300030403040c1d01c04601e0724081481184c00b4590011414090746032420a0240180340c100d4000c03203403000210000035801070034050600282d000030800751891034601c00c02e0b1035400240302081d0441c0036484a40030b03165980c0c461795000034051600c912036864031410701821035206810038006d01203081011400903664510101049034203107040c070700300e454000700d11070110119a90294400d5011400a01100c00098110700c5039808442121400c0c50a205800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 320934559 1250 320933309 320933317
    0xd09081b1905062a0d140105040b0d020d0804080a050f070e0c030415110c010b0a0e190f06030206120402010810080c01051c1425080f09101b080c 64
    0x100642c2010300041c070713842c844126049445107440d1180c0b0a00d120206864003503441305e500f042c00c0599640401c440321303c00402c101d0151074103036001c01607800d03010700040c410442007100a22030400c0804d51303810058880240e8000700401822622080620300d41503482c0e510480e0351040501c191000000c141d448455403600840e034100c8110302e103854644a07050110840d182e4082440e0b111340f0a240c2e000860300060a4506d03201000041d400d0b00d80d001c0115250090340900c2040060341c081c0f01d00c4060101c03045141a2950200051402d03035540800080c1c01281d1003c2d40c0a03002040e44444026410001807065100760f0707400003143d4425801301d0070451396000301881540324800da0602075000c0c030000c2040c0c401c12299003522007150160f01c400c4e9414812020340f80501d201c00d0000d24080e0b903c1220310079411864a001c5c281005070010140d0138020030401c0710340e0b000c81c003003400524180214921802c9040003403200c00841c031900810056180c484400007055a400aa400030340381d070940d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 320935809 1250 320934559 320934563
    0x5040507151812020a030803010b0d0612030525081204060b120304090b0d1b03120302030903031b0c060903090a0f030b04020904080c0f0c04051303020a02060d09081b19 74
    0x1d00810b50419191601400118008907041980404088049290358001c2c500800101030b426944415501c83d000640d252548002c908902a1041c9000690800141c5080c01039030b0102000d62010a600c0c007a0b0a18a4440079003012f40008008845c1d20090311824807541c01410180170201c8d0840602ca40080480819052074109100a010035009a04040d0700410b000340003500046241c0c5441900e04050a107403a42c02c80008030810400211035146002c07801141811410340c038120600e10b4580c400200220388840300101d0343c540c060074020a440d9480303c03103c00c490207440d012040940d02d501a000c102d104034500701001032a201400140741c1604e40c080e013806601c0d21690309000011038060800c0324441d40c18094014640030030400440d904400d02c0040c840e0981040500040307a50290460190b00c00001005c40445d0300000c41c1901184e0680b4031540c0c488180185100820722000700031b042d110000381b40340c240c03e02150550304c400e00007015a001c0000b501200898161038045c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 320937059 1250 320935809 320935847
    0x60c030513030f12020912010b1c0803010302300c0306011a04140105041503020d180206070f05030f0406020a050c01022a0312070605040b09010c02070e06060d0504050715 75
    0x81900218804c1050802e4007800010150400c240f080002e25121003101119000c1c0c6e540e000001c01d00d1400c0c2000800500c0314240811941c006902d403075810b44014000a4042d440010100960090301c89001d21035038040c485d0000510348485009484480d42030f20144079102c1c104c00451281410f4403e022110302c507120091801d440d0510407070a03090210300c03190601109010009007070700c6040c9514000030711640c0c016524010f0106131000c0320740c03d849400442c54669040c034016144c0340211460b040c0c00000500c410b900031702d405445c500c070780001100b601c040850b001540c5900004c6000714039114005491020002000490b80e403040da5003014090080b204280040071102040d25a0286019064907038012502d01850900d40c8180c8044a14a5644080000f0301010290310354201c445da07002031080d680b4145c00296214034902680c0011402d030408103c80e0780e40c01044174480c82c1200d0f800d00c600d18050030b080351036105a10484005d071038078038100120f1a1044100e5104000f01c0c0c91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 320938309 1250 320937059 320937077
    0xa1a0607020f2107060305010801020a050a1809020d0b010801090b0307030f261b070b031f030b01080c100f0c1529010905090903121e04060c03051303 66
    0x2000b402e81d10622100360000c0024004400d1805544458502100003c1c01441e415242100007002c8400503441107900741d1051000c00c0c0302c0380c1e0110403121b8140241c84c011703906010004e618505450785600100e125440002c0701c894504c00354200449180098032040900e0382d03625010800e860400d9031856141d0013601e01400000c0041491060050003003102194a020300040c891850704081004c000c0b00c04033203124002524030801c1c83c48030610003405030144074030f002002442400081d24410100b201d8842a200d002c416015a6000b1600503141c44095603640306402d846003804843c19000307210341c540740000a80a403003013400e045038036a14400c0c141080e803a003001c200101c207001440540c880c0001500303420b42440b1600403455000d01c10802004500024000304a203620040c00f4203030304802c205003c200030050f5401d2890716942d880066075a80403001036003503060f408254584c0713040148002d101840d4800c031169166030720100059182c101031101c0d20700d030f0b26200038001003540c2c0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 320939559 1250 320938309 320938313
    0xf0604050409052103060f06191d150a0201060605030f040b18011d0609010c170604021c05071214240a1d0f01050607030c03020709060b030a1a0607 65
    0x15202c2c401d0b00c1e02460580703c0920280c40c101341042c00780c4081c04040b600201c107215841c0703003d40c45082c82610440345180390541000c8201e412143d5508031708180300650000da40c02c4401441c400d000344070002d10100c0000f00c4085082d041d07402c882202e80040d07290500108445000700e044a000e800f100800c4c9600b03079101e6840a51000c402420006002080029035548007803d029150481000e55002390408032238034012031400e00001d242c408280e040c5001045499046400c5a040c10b00c810010301007592401d0200d0017a10845080301121001405032a6921030194070082c0074440d20350b00c882102c4031681d100300541e00f0603100c40300b81d2007a94012039004103e210108100c900500c0005180111030070000340c0300465540060183c0244102100203003c00e0301304c1c20f5201240140320782c1294102004500c00d4000d44100500344000110000103040c001c10812000f41141941070225644507e0144450b8106903444030302c007801c054940d8045520324125103112240030f4400b0307050079255 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 320940809 1250 320939559 320939561
    0xf04090c020106170a2a06110309090705031518060108060a090608030912031201030201140403060f02070212060103200a0e0103231606030c02030d06091a0f06040504 73
    0x540514400d542d038a14000403a044d1007482c4d410241c1d082c1d4043d0019510505046a141c2d4907440c102651302048a03000304409440c100350410384469181803c01c050050060900e14401c04580702d501071644d000300110194040015482595401c0d540908415008140524a240211003521002c034940020703400754892040660f02801c02441c0d140c0c0070f507030f500725001140c640784c00110315170300000f0300d07002e441c2440b074105885001d20178029840d208040e00707103c0511006000003410000d8542804000490031301c1540d01440d040b101c2003103c0d02141c20302900940c0302c007030124000d0440b50882d480d10440441c02c14101c0740c0114401ca101c800303a103101e070542d02c002015654045509080461040c80f43ca00340b9018504c600640300c6040308884005c0201040300081284960100d45100721043d580315120b0200c80c0182408601003515003020303403c1d40035012240382e8562400c03000140b487c0041d082000c0c400c00346903202000e13450040c01d000c10750320540040c2c0d4004600f000f0803c154101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 320942059 1250 320940809 320940821
    0x6100509060d15050103060f03020f12030f0d05041509031d0402040801140a0506090c091309060905070e07030c090b13031203060e0a05090c01120b060403081e0f0409 73
    0x40107111074a02002d4030014400c441d8490721580d55900200400d20065800d84216005132484005181140b80313145d00195802c3c03a94802039000385480180142c043c041041980d52244207000300d55143c28200020300000c120854050b68072490241c10030110315858440c091405805540e00a010308001000808001640c02c14542041d4200000280c0300030a2040780f000710310720041c115030b90038810401415128050060361143c006d00341400b100c011164100c4920850a65002c4002c3c1000021140103000c0c140000d0505420448201c04001c000f003242c100b940d020a0340030001e83c03203d0340100d040300c00c100c1416002c40c0360550f00b4417445541402070041000c50b60700f0007020b1900c03541c80201c120744400d04100444d0b1643c009000310340e00c06100c0c40d4010300c40c1c0c10811851902016643c0e032281142036441c140039401030802c00c2200c1035042074403081c00190010341d440e0340d01e250060595100c0c1e00074040078400c500c00c5c408051241c0d030448a0303005e00b0311515400d083c10014183c00030f100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 320943309 1250 320942059 320942077
    0xc110a020121020703020c0306100f090c09090903231e0304060204030c0b0d1109100806030f01020f0c010e010b0127080105010308040617010e01090c020304080105090303090f06061005 81
    0x1590600c20b45694200d030005082c510310030ba0203818850032110925180c0350004d065040d04542903403050156268210303041003269120040401e0002116030241c5024402c1c1d00320031b504506000c2204107050700500740d03028071003000014071404148850071041c103000c0e11002182420400651180244108010f95006402990010700c0c0c81daa940c0ca0b001543c12603448511480c1001c90425400047c51080d070445040702600103281c00c50003000601460080c00340c0d1402c1c4840340c804915140c804202c04c1440410100085588005050078449181c00c014031280c100d40c02c1c9460807100c410180585070002c2c00684a04041080d4640d81100c200d03034a20a5107542d20340602d0004c7e4048007401124020b50140040c03643c1c5909001c0000d1030000c00b040c1e08c070b48128905004208a059140620741140c00302040000c0c02e50145030704a0452045600c103003010341c00e010601004080c01300c001c41c016220b44080790590103124014a8980342d086400c198044d10040e01c000c8114003c1c8020140c940c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 320944559 1250 320943309 320943347
    0x5060f1003020d0f05060a091b05180901060305150d0f230a0803010f0b18010509060f270111060601050304112d19030807060902090405030c010c110a0201 68
    0x4002c00c510000b11000d001c803070203104e522241400142e050400e5440b0180c1079584060050418007190302d80f03499007403568039041020008982c00821404c2001c00013100006180c6482540c0d621b000030058402600d22000820482014140ca4544000071a941c55800312035007651440765207130b07540d286080281c800c0000700c148035030860146085c8031b00e0012510a02d180b83d120350411001c240c41002c11340040d070702d1403020007410103626076200040d01e04038800d180c540c0c0e4600c03118012504c20b00038060342c0e40300e95101082c4440703000301940c4208a9640c0c8040c81404400b10a001100d1354040140d4441d045d800071000b183c4554070910095501501030f46a041c440181900840d040d070858184030104002c06108804e2121580c031400ba40c142406c64940045400701c45d50080071251610000301400c400080040c2000800e40180c41d9141d0000c1c0700c40c0b410724150802036200c0e48a009180c049520b044103194000b80a12034480420480000503c1100036640c010340d60400d5000030342c2000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 320945809 1250 320944559 320944567
    0x100f0b030303010b07110402071e020a1d0a0b06030c0403060905011407031406030c060d051008340e0a091410020a090b0415120b03100605100305060f100302 69
    0x25103081004500a001085059507108100d0500034078011006c2d018912a9004010180104140310744a40501507a000343c4000d034106480061803268441d44802254008001044c6404910034015807007981c50007001d0140c5e0040310100285840100c803000100c8205010510104155510a660052140000040300351150b05e070190b12740741c03c40d41d240009803104920800200d0415440d50080e0b001c0c1c0090005a0700c4900107010b901502042d90801c036520f100040345031800035003440041c041e090070343d0a030f41c0d080c4699a0a031100b00c000b84661103010b00142401101860044003143c07aa40e812511a495441e080320181601d50401e4170040840d40040700805014003400b0404800c1084c0141d43d20b001043c0500180040c0c1c4c040c40c2c40041c00d0008000600c0c100344001084a490314289070b1803140c2c0c091a500034040383c41190b0701403186900390802e0210301e910100540300b04a6108401c1e4500807022130a5071011940b498001281000d00c011904005801c07128042480c00c1c09420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 320947059 1250 320945809 320945831
    0x902160618063b0d05070602130e04020f0d0203060105040b0a0312111b010206010501030e0102120f01091a060d021308120301320f0109050d0b04030e1005090f060d140613090302100f 80
    0xc504450704060000060940be1008501d000f20881d201d100065880d080210890740006e511008148582030049860b0300e1100b000c0d5448070100e0000d10380c031404074401c8900c158030082c001f80980301080145e102d404c040c490f1a00f00154001200c101c160700401c2c0b260700b07210045016040880d00c443c0e00799002c0c03040a010420030581c0b07a109110700304070039603290b02d0840e811082e0350031080c1d05000200d90316401d440340c0d15082c0445141c20ba03507000c0584c0d2608212030310f13a035440259006241a0090001d00c034003554001d00294100c13a110300e40050200344005009078504081d0030345007020a40904102103905014079850010181418407003081030392000851000600c403031084403024100001c000c00c068000040481591003035544802825014602078a24400e40e107900344074a62000010b0b580b51380b00c8049451800c45000148604402e01d403401184039029241c05106103070704800302000c43c140e4829102225095402090044082c0e00007500810713a01d040c03103482c02c0d2203200c6105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 320948309 1250 320947059 320947087
    0x101e1206030b1302040c1103040b0309070803041206060e160315050d06060e07020a0209010306020f07020607140c06030c0406080603030408070608100902160618063b0d05070602 78
    0x4400c400f00c05038101e4035a507500c100411180c1c4410810180071500800320030299000090703034103607449016110303501d0300d43d0011503180902e03950080070b0901c000a8003003415603147d0301004425115040502600703444884060038010100c51b028450040c9480d080700c254480e40002a03905902c403809101070340c581c00800c4d14007200c0c0505899654491208100c0760443c076505661140962000e408061010b0740000c00b00751042c84090702481d000f05541c1101440d40c011a00c0e111760003416965201c40134504038051351000c281c128a14000d20380802d413139041c84400c4900c9400c0720110540741608044064402c940050006505440107010200314280c081040e45d01609007501d9000043c502007120b4410014140c10400240b0700504c4600ba01c0c690401c40717a010700d6400b130f8000c10402c1040104c10380401e0072030301c0030340914180102c4000c400700d40603841240441d001600142903010219800502640c40f81c603061a50001010b016030500c185c010707141d0307548180d401529203009201054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 320949559 1250 320948309 320948311
    0xa03090c080a0203100510060c0302010b0301020a09051201090201050a03020d0603050703081308030405030d0c0303241a070c05040c140706050709090e10020307050f030903040302101e1206030b 85
    0x4a840d840704103902d05520301005481840052a9024449854048107440c0404050f201c0c08040c0950740001408050003034101c520191400f070021900c4852490000705510024800d003800750181d02c4061a01c41018001d24000d01e0701a1901480c09580100c2100254402d8460813003590360b8000100005a003408803800540c010f080701c0b074440d0350b91500c60500c0070b150703400961a42e008002c100240c1c1c03804100d014803030783c190030300d0480c00000d03090130340182c80d403080f030044c4d401400c20540a01c900b035082c0d140b0903281c04440650701c6000200c45000c5d94846e406001d1315020031030404105500e850b800400000c1c419191100e2079400050b044e1440d904440e00454005481d40c040204103540b00c0e1020004004442c42840000000b0f40819200d14080418802e1150008006003040340248111413494a803604046d0f03592401c07558064880e001760004910075480c403071080090b54410459001c245d0312081d00211144e00c0440706641c1c1060350169000306948482d000008604240016 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 320950809 1250 320949559 320949569
    0x7051516051c080f07120609051602010f0603020105040911070803040b1f0501080a0f0e0304030302031e0c121e0d0e2b0c0c0504052403030a050306060a03090c 70
    0x180040350710002c01d80075a0012403030340c1c0b0070403102ea8200951096030440c515007060045c01d10080c05442c490581c0040d2500ba00140302c5181004280b0007141c81b125000401d07808254020801501800301403070540b0000d1102a001807020700c0103010004680d07004030803131001c0082c40b03480d0801ca030303039080702a4004407804c1e14000000003c0140702d5240c140c1e410448505240ba507400e8509103c00641803040c060140000155283c1141c5502d4016521164110740072404880d1070315501e01d8029541da024640301032040c0a4003110b400551500070a461004440d01f0240c005042004c110b10310a800c465940c144107c0001c4400c0702d0405404010840301c08003e002182c01150b43c44914a481c4400f030b000882403000815104603000020400410368100d8900700b07680340300c2030a012070302441c00c2e0405680503260205000c0001c0d82d4045c03640085400350010b111016001d0100764a0740200c05004020403c00c1000608510700040100355180d4641000202c550030b07034448040a95081d080303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 320952059 1250 320950809 320950813
    0x1020d05011e0e01052101110c0d0314060a0501110a0c03120e030a0210032c0f1b0904021c120201050a15140f030f1218030d020705151605 61
    0x5000e5580120b002d104060800642004455450180450ba00358405021042a00310304148181118020740140003600385a84100b52186002184180c4503007503d50140007281c68030f001d18000da0311003260148115402046184401d11705030054451035901c000c0190301f0701420502e040040c2d400809032003e54021036071000c1c074141d1840003078010032040200500c00d9004441e0080140d0303030f01c0ca50701c3c6104890714000c528100c030f0303002d015070042108041210703002070040307460b40c000c2000540c800c0c2141e009080740c400e4004245044028041c000306207070824600b000140c0541440750784251008400d0703080c4c02103004075031030320701130031011070002d0005175106c40500c41c4605460054412026200c207070201420716044851030091002c48070750340507540d024480c1d519950f0038040000000000300940d2100e0700c88201c611015413280015000c808844809403419080010340d44100e140a47c00401c501e034100070801a401411041805c01f000042044040c24040500d110302035902c5040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 320953309 1250 320952059 320952089
    0x30305281706010203120103020f04090b090c040b122d010c0903060506010e030606100512010e07080c0403120c050319051b0a02030d080705040312020d1202040b07021201020d0501 79
    0x200005080c1d01c042e00c610304540c8103124842056018a0b041c5045a03030480c4c02c0721060042801160161030800c50181c081e000c05420464003001c00b01e0509000b1030700300d030200300c202245000c0202014400510780040c0d17021600540d11406481080c101b24044070505804030501c0600300c9007512400c0d1001400121000401c0013005401d0040640100c024208800d0592941001c039944400041926101b104400c40c22100240988121111041782508000c403941c1c42e8503070000208420364007540058521000254949200f900751070a0b26845030a5a41001d010802140d014003410303019502c6000030808a502d242a07031800e021030100783e031141a103034840500c00c2505244083c2424200781c0158010b400140e034040342c0d910141c510390810001035180c00400721218003c54000038007880c40300c43e4048200c0c0d000583c0b090f5082d402e40c1c0b14560141a041c80364243d001e41c1c0319805203042c0c14803030800186042c40c039009107440900e00040c204000040446d00b42c2d0000c0c0c0c0b15103201d016400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 320954559 1250 320953309 320953337
    0xb040201020109380903071e06090b0163142401050f07080a0e1002010c140705010e12040f1203020c04020f0c0706021e1603030528 58
    0x106011340b410010000a183c0c2c03a2170b50625880e0b02c20701c14020201408a4040c047c40b4104203900710b1055003204080240c40800e00d01104595820301038000b200110a001050003100303804210030560316602d002071800310400c2c0e000d8102c0c010592040f50480c00c4104070500012007a4040d90007403101d0b1000c150030308481c1c84000301e200050f05d5486500352003101d00b0201061520b0200409000b80380542d910480c4c0500182d00f8000d02034000d164020014041c01d0312680030f03005112280e000c4940c84041040d0a40a82c226040e48200d400410f04034540d0340315040c9494054043c8034000c034004200c46403494256400c0050440d141d865610001c5024000c141d1951220006840180500d602600c003c5c0c50117540c913a0140c081034490390b00000d003e9944524201511800d41d080d10032070300d1907611010065211003044100740c815a50b107400440544100040c0100c183e0040700540e0780c40707801d5440031949070f441030b220b199070300800c0d610141c540036420b0a502010341c06650b4180d0718242c40c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 320955809 1250 320954559 320954633
    0x309050d0201061d04050a0b070207150201060e0c120429100f0b21100305152e09110c120301030605070f02060a0e0c060a0504240c0b040201020109 65
    0x30f51384168256020b40402c800a01c00160303020303440703401150400c0b955036446007ca18050f242e41201d18401c1904400503006501504a01e0603074006d80c003040c4640e603620f42072a625004400800800d829013a011402240d109840c6521076246400180c4040040f1402e41d9070014003039800520410500004000b140d4040a061340a402521621031400742c4003501000311044441c1500703640340004020a444480a40c1820b00969005003511000702000800f841411030071900404291018260b03000c5a021440c84500c0c10502c401ca03580d0400e0030b1404900041110305d11150002200300003020f11840f0400c581c1008800b192a065502e60561425100341c40717001d0150801d0082c000e0101040640100720654080058000015035444c10803080d440d028a4402447e04880d00040b003160071944040103000340d4000900040c0024009100001000100310014001521444203d0001a00c62a8540d0014014400418210303460b8039421300c00a005ca0004c01030104650b41140b002c0f9031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 320957059 1250 320955809 320955839
    0x21031306021204150e090405011e0b0d0602030a02040807030f030e030115061b140c01021903051b030f040902030708070206070203160501022a2109040c0309050d020106 74
    0x40d4405007030207205280341041180107600540c602c40d40d62400708940148038144090321901c00405114103030070f06061040c001d10240b403904443d401203c20340e040c0208a809901d40150300a04240d10071186a221030b4020740026200f00b043c00d40801c40055010810405003024600603164524000e40c0c51501074010140300c0d840307500990402032001402400750541d00103c80f040c1c202000c80003210030880001c451028002800e80301d6045031541c02c140c0000300d417420a0402e8084440d0640c481c1c60080780b405205900500040c01004118425500c104080541461990850b8202148440f10703501542094108441e0168080104125140d0244140350402d00c507001a082501f00080000c2d00ca218424845840200740310b414810071900354102e48007035800c501515000b408401c00044c44410242003030340184100c1d0110800e20102d0310b403130340c9000a1420028600b800400502008c1c0c02500c50760b030700740765450340004081001842040c0303204a041d0b0000503803a051442401c1c0d0300c49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 320958309 1250 320957059 320957069
    0x2040603140709090f0f0206130311030d14030703090813060c21020606041a1c14070602100f1404060e060114060904090f020a030305031e0403020c090402210313 71
    0x8140301340440130071543c01e151112a0380107140b8003030708031090002c58030511968102104c07070411480f000081c01502400d5001c2e892045054a0440281c1d000446407003500c442c01d001c540300208085200c0e24013a510044045106c2c03505542031110304000166003c02680c0402d006c0340c0e0700a0080b042004194074020031004014040181d1a20408029a0341c5801080c80d405541e035a280c00050400103440c40d02111340042c498144d0744030305000d010ba400c902c003d0851301d0303003609520803540440100d080001c0d140a60300030001400e1a01c5c02801424410080c0c8107010343c0c072500d92100640400110384514084d0b58081088295103005138680241688070007020340351182c2c00d4003150750383e900301c40e500e0b0070450300812001d1407420120340c1c0302d200850007544251003200010030950050301440c0f04056003aa569151403000386084106001241d0050040c0c01511070310346280360000203950054005800751900d0061100301045003440304520800030740c000711f980e18603c0024118540506 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 320959559 1250 320958309 320958311
    0x10609110f16031e030905010c170435130605040f0b0d1b080709080c0f090703060503010606050c120403030e1023090118051f020a02040603140709 65
    0x2600c180c40e5207186002e1003401e680c1c88000d545031401410f10031844464015000b851442107981c10280180043c4540c6200702c50a50a11030410280c0703002c0c90800902ea030b0718040b541c00310b54440e0b41e041c021030503046104000424020340e11f0240940c1c100c24072982e440c0c00003890394400d484013041020f802c4a5003c04100041004280440d11550102e44200c4400701d444035103031740c00c1c89031840203020f0301640c0010710303500f44000700000ba038170440700f03806003105444075441e06480d1032803281c840e40900101d6400140c490301b10146ca04141c2e0380c05901000a00e4009161a10340c2e0029094420300e50080c00050300100c1c040f940510240300300c030000b40b81e0140e0716103481d2030750303030007519801284a40034460315940d540040154060303180008100d040c501070030403f418031061880c07a41c12072000207002554055200c0d1100a00d84101015688018080900c06a400d01200700c881f907441c84801c21401404070f140c0042e112401908003552103a080f2001c0658500e916516050b0f503544224902 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 320960809 1250 320959559 320959567
    0x3140a0501081f0e030a05030f0a06120209070c05011409010c08060f060a18030b0103060c08040b060603090a1e0b0903031302010e0d0f06060608130809120c0603070201060911 77
    0xf0100b55004901045424035082c00303100718001c0086000012660100052002e00d0a9101008621402040484d0851074450107592400c403402e84c0a0031f81e00075480e040010151030441002036002d0110b03d0070b8a00305035039030b03196070942d149921407041303154481d001e0004469080c041c014821403940351204403480c1603800035a81100312980940942c000241c802c2802e8428210031000004891103104d42030740c0c0786040c0e00a03040922041e9071140c0b510700504901485103a001c1d004582040c0d010280340c4403c07040001c55480039010b000a03205d14282d100000b07020146414090300841142000c5a140c1c0c1015940640000d141c540590410010049010a404242d038110ba40a180c03e840301107078240404c040004403140508070b03140c1c40301e07541c042007640e402010540f00e5590312819541c48035481c0140c2c0d0384000c10001e1486105000d444070600301084140507440007402101c60303c11480000c69143e5009440340700060351074200500c000e50140c020780410083c2c0c810b03507605c0c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 320962059 1250 320960809 320960819
    0x203010b1014030604023c031608090304050d0f02040e1c050309160306020a030e060c040302091302040c0203030429041e080a05040e0a090804030210020f0d03140a0501 74
    0x200340203280b0560044140880414015102d50381518411014526001d0403845140e0221000e007050311000c00c0050039080150555019500c1600c0c0505252140300480c40000710056907451402000c60f016844207100c00a603503590b501c0308648150040c400300302142401d0040c041502c4404800d810543c0c8900c2c220031030b6007130070b01902000d20414079102da10b030f440d000340003810318111b58080340c00c4c048801c2000c8180003003a40248400141514200081844c88000d2a201c0600b140c0d010b0b10303044244030800c05170426400403684454180000000da00c0c0940c009030071210071140782c500690001c003c110802650308800f82c10384e61a989a525800041c842c22482404000d100822158001413194000200640c0107108254000c92a544607061820003d2158005119481103818008046070006400c1e2250080e0160080207a83c0b03801e007141c0038410742c1d13000c0381c40400841c8114490f107042c03042d0901c90b000c000703107407603402088240321400300d68a8008060300658020385030100405c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 320963309 1250 320962059 320962067
    0x100216140706020303040320150f07180504270c030507060921050c10120606030204080a060b06040e01030c14040b0108041b03020a0b030108010e0f0a1506150206040203010b10 77
    0x2600650610300320042c880140308e465a80501e050b01100d55100340050100140c1000507442d00c40e00108440605664071040102c4180c0a4003052045400007007005021500302030300a0207004448115030081202c442040c6000d007214904c2c141c50b003100f50107082c030800c0b0040c007000005001d103140120407141051941c80c021030306400c07002144140c41c480241041070500094904110040004c0d9001c0c494080151406400c0e09a14442500d00540820498001c0c4256001e940e8100d00410206529a0701c072001080145810380d8000028003000070222252080e03d40a0341c801d036510740780c0c0380c5081c000c01400703404856a1842681000d08403c2540d91180065500c2901f10b03144011401c4031558541165a103604007031740010760741da000f0848a0050b0700035812a0041002000483c080300c01550300c96520000c06502d58010300940302c082900c404140c03444402e00e460003d041607035084520744403d40000d0b0400503802c100104015071500b03100d48000e40106480305511039030401d100030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 320964559 1250 320963309 320963311
    0x70e04120c170a03090c09090b0c0703020106120501020901090b030c03061e060703110609120f0901031107030e030c01050c0c040e10091406130b0606070302100216140706020303 78
    0x10045a44407000920014024030300300c158a000340c850340c98100d003000401410f100c1000350b50503a040000001c2c4d02d0602c0c4180413485030003805104c0f068a488400300055800032400b542150340b104c1c004555200704a28440d4810721900c00180d54070991400074000301100d80c0306104402d401d000300224150340c60122907124000b112200c1c1d1122000208420318580342e440c0b10341040000c81c0c0d40080681080714800c444201e6803c4a80680e64408025a5481042200650610240100b00f141d03001000604481001410003280c0281171020b45542e5401000701900010900641d1a100381070900040301028001c0c0b80003498000340700e8400e03a071a441d505d800750040f41e880e518500980c034180a00903121020003000e0180341900d06008170612001140c00981c0c1c02500045040c00550507403440c2299030000702c0f811640e40340340401011f0741000c0b8041c0c080d8010040b40010040a6100512151400141d41852410603061440f04040c41407600c034030a0340a60405d20000342c00009403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 320965809 1250 320964559 320964593
    0x31d1f051005060d0e011103010f080105090a03021911030a030c14060628051f0909020c0d08090c210d02010e3703030203010e0604021e0f07050f01020705070e04 71
    0x1141000300170195900504224030100b103141c0380400003103850444881d503501142d607504024003807a10f40340300403921b03035103002001405a4030440402100c0b6951002d00116640101c00b400c40b03445100022900307042c0c203140103c001540f1060100100a26029000c1c80c0c0702c0201d0003483d15203000d901280c0000803007030851002c0200c050444600080d03040c208400f4000117080403c000041c00d54079900c0c40c18019000d40450700805c0d010444080c54425194944945002007100c81c520754010703250a40b01a1258143c1d000e0449400d900307441e410044500a544050030320960b0108051007420714008024500c21641020780d000ba10910004001642c0d201401c6145c0030b4000c001162007070094a030302000c9407802c1240010007450381603400746048032210001080e040e900c40080000300d1144ca251003005040042490404c5143d403c0604001c0407151003c510704401919418541071002c134002415a400103848020001c2c2841064010803690106409500f80307940c0b581e0b00e400000c0d800d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 320967059 1250 320965809 320965811
    0xc01050310080106180501270207060e1608060709082d1c0206070c0224090a0f0311040c0203041505040f120303200901031d1f051005060d 61
    0x11404104041c81c5000007001020000c02030300f83d071400344040008074038503c00c4445251100003d03000100c0300e0340c000e01c1002c95030411503000d810503106d8000d401480c000e036500c40e5590085801c80c2420003e0040040d01081240151441c04192a14046000f000b14080100d0180c0410900d080061501003036a003082260720060300052080751000c1841d1407000492162a1907254000ca90181c40b024441c020b030b080d54403540d10700000303491101c0c1452001350090f0780e4001589148109240c5890300340113519601d0302d08001e200c00180043d80e6a0864141780300114020403c12843e5800305415400954050149144091000e5102c0c0120710640c0d0790540042c40030500c0e94451070885020308170b0301901c40511601c54400c0c0020902c81402280420702c2e0854155607031200305032611481040080543c50540030000460203071a03201680f101c01d500e140b00e911103503801803140c4004a955910905c041146a101d01d0040d20409004030041064855050016480b908111400c1c540d1541d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 320968309 1250 320967059 320967061
    0x2040506180c13050406030f03050711122a060702010f02071d16030603050316060605030a030c170403021e0607050d110f070815090f0111091c02030c010503 69
    0x1c142460000407285103034140c0c0000300804140000d02800ea08000420b11400841d12a030510044510501001e01002c00f10b01c001c1c00003d100e84007d00301d1504c030f030800d0140103140501040c41e40c102040c848903a0740040403140d6000710400c0c0702e41c1141007040c04030b22850300500c1c0030a10500c02c85101904010b43d941e0407040c41c50003080204014541c50701840004c06085101c00d031341c402c0640d4010f01c07005441e41c0f80806240320340110303803d50b40c10034095441d1600e0440d202c06c2e9048256021909d40d03450303940016503681c0a000412040c1d000341c94002e00c11256180551840c84402c209048910041c0b109001585540c0c0d00852888486034000d0040494a40054520300468900078818412280450f5000c0d60100f00402c0c070203031503003c466400c0151510540c0300c041d07034003030b01c840ca070b04c2040545c0000000b03145007a00301000006481c1ca580b0390b0300440d0300303580c442d03002d14038101e8001540001d94102402c0c0c07034500404122061000200302e500003500c64203003a000344c0c10010044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 320969559 1250 320968309 320968321
    0xb0105090402030a17090f0607230f150403090605031b031b0a0201060524032205100209090a3335010501050a0b0d021e0c0c030f0a020405 61
    0x10115084a800004101d1400241a1100c280e030348044e14580c003074803045441030001d04180d0152760140c0e82c030445044062024280042c00380504440b072010a200e00301c0402110601808000c0d010342c06d002c030540c2c8501d4942805003800e5003650019080044c200b0030000490110318800c00010308132406640d41c3c1c0c89108070040700316280d100302d41581e40300140d4409043d40540c0114201d030015070300e100340c2840400b000d085103003801146805e8410100005581b40710051800c4859500700c01e8a408031856540766517150185080c1d08100027903000543ca1460b00e414049260300c504000303004d00404c01c024171070b280b00a507001c0c201e880d10010040c0f41c544086451200d8000b0708140b01211440d0740060200c5580700e0038261420200e0003624103d502d032030740c060007158140d500181c00d031020b440c50544080c030941e00c400c0c496218190b0034015401d480015144100141445012964440d5001c000444c1000185414248030358401c450841c075448020650b001006e4045070002400d40c1d4035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 320970809 1250 320969559 320969563
    0x11209080f1b0c0405070c0311100203010e251b02010c170a14090a12050708060f04060c0305060a180f020a020307050708150c0a180305100b06070b010509040203 71
    0x103641c140c0c4040d4004203403060740080e445003040d0380e40c1001e400c40d140c00000000307202c110b070030a80e00702c40041c01c4440300f42c0c0840d0084404800c0000e00300c2c1142c0c1c89068686140c4200d030400c0e001a1a4081c007841804450340c0c0060120b420807a140303070f80f19184618502c0c0034080000300ea0448001d01002c50090055a00540d41c000025400c40e00003020034048142d04241680304074424804500040f041e1106000000144c0740c207004080c00404d81641491804900f000000e40d04481c2c0b48039440000c84c0080007400380c0e034003d1442803404c401300c1c2014900102a0350140390b41d00100351810782001429560003120310102e40300c03c04a1220290340030400406800d01c5410030102a00008a06d004654000010300c0c180d030041080c0c545151303c9400706500c1d4079141c0101010b0705901404a41b90f0403585004000035511424a00b00b041c545810a582c612150f80c000d9841d03410241d25003c4e20411b0340100c102c940c0048a80600d040c50f147d40745083c506041c0581402190000d00103400c545007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 320972059 1250 320970809 320970817
    0x100f080403110a0609031101060618060e12010c1e0c0309180603060203010e010e28020a030b030a03090515090604031407050303030c0715050402010203340f060608060601120908 78
    0x4c540c0a100c00a030908000c2d000065804160220f0342c80c280f000a203103071080510040d11283c080708842094608401265410188502c1507031000c2e0008a01c201d6203004d2192000c40011038031202c2ca62007010042086079150480460b00380851840010000b0340d00c48940419145480c00c95601c0b07649a8041c2c030006c0125810060041c3e01c000004240717814440d01584c12500840d29011482e500d00035070000340d00f09198040c5540b19150000045400c19402619100303269160008110750840c1c0007903c0c0044400e02500801e02c0420140002d0900034051509108020789080c6008517180c04500e02d4030503407002a00d46040c0b41c24045c580070048c82000300810006040369268100102501000c2d80310b9001160811454481e12881e01c0c1b1901a4612483d0140c004e0350920105500040c00140f686000c280c0745820004d10031000302100f4031002c806405986902e10f452a58034120301205d440382c020f26120360108042181c03d80e4050380f207001200105a000c03540c0065841c00f042d039400307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 320973309 1250 320972059 320972063
    0x503071103092706010c03020d1412070f0e100c141e16150e01050309010902060c010e0c030c062d0f1c0908091c0b07080105100f080403110a 62
    0x1030721800081103c07041c4040c030003001402811000d5680760b190040d101c0e01641c02c00200560440c07849042c100d1f028015201040654000f02e03071804030008182900c44c201180e07a20301151000e500c90144070f903c07400322010410191460341e00300e25807240141000046850090005420ba04802030440c01400321401104100d624000c000800b400d030182c807007020105001010554007000110b8010001070703c90000f0541c2c80b41443e6400e40d00045489510007440c8515546d00c03041090b0060702c464005107014802e131000040e04a9070320a95904001079490990320aa002c040c0000066071904206c2d94059240b01c0d80c1c003030040e95030411070b1301500301c07c042180c0314201060455050825038000c04555400c00d0100c00c83c2d180c03008a603011280d419034080e18840d001e11043c2e69604150440e99001194458070141c2c5500c1c55542003204e00301200c03c000068451300042205007440e140c0c0d901d00400310301740030324500e15081c030084c070f41c01d0000c1001e82000968103000c913440c007041c042130716005c1d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 320974559 1250 320973309 320973319
    0xf0d020301090e0d02070b0f0a0c020d1112010b1c0507090e06010504060803030708070f030b040f0f060b0f03040201180305030d051504151a040f23010f050307110309 73
    0x1603550350588008228040310956503018a455030383c44c103440810600140e44605900074103004514044400641050000b0340510041600f803001607680c1800410405105e10414000180410b0610000480c0c03100096050785c104000c40c1c0d241c0e6164162040f401e0310140041c1d4078802181015403904225600204c0b81c240340c1146e250600c05e000ca801030584000383e6052000075601c0300f0981e42c2e8030045a45070002000741e80030441741807046a240d05c000849281c04102c0000d1000041e0465507500100180320f584c4d150000005500e074040c00b00100000d0983e103062458400741c60416101c010f01c001d04200840048124006443c2075a40203103401604603a1141c01c6003840c2c81c010001601d18034464000d6241c0f107400d62800b8010031000d507507a02143c0600529202c40d038032141c294150700d002c8040703080c0f0004c102c441d010499400103040c5981840050b40600c0031110b455a1101d40d00d07810000400203a000079900135044076081001440c060038500c05000700681140514100185e100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 320975809 1250 320974559 320974561
    0xf063e0109110108090d110715051e070c090e1005090607110c0102030405091e100906060c080909041515080f0c0a030b1b21060a18020f0d0203 63
    0x5194154400022035210300308108010008000640c1d0454049600803071a60140c540540042e10510a1410582c07028084464180d120b0100981c5c114504044000090002ca80803820f9120482c6100c000b50800c004107240a907551115040d0f50614001d40141070784520010784103400c20403143c10701c00503110040155050555040790ae52000f40d6000c000141b041c0716891801002241c010f0813044140c004501d41480c02d428428240c1006003001c4280602d04140c100074030005825522030801e440400d8041d5042044e89000c0300c0c1150072400401c400111038000182441044460801c001c071003000b015641c5180042d038081c1c00f114000002c90904603813248205d64917403580b0913188800103031801011440441555034442450850348070880c0c44040010400c5414003a402441e0940c41c044200500344002c0550351021401001c0d1203000200400408100207600345c00000840e000e444142c504450b4101d000c026038012070f070f100d900090110070400720500300d4000d11011742c02552a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 320977059 1250 320975809 320975927
    0x40b0a110f0303070f030506042901020102190f12150909050c0d030513090b0f010e03071e0f140f040c0302090d0803060411070803150a051201150f06 66
    0x605c40c240c00c00d0070042400c0902040e1207203803c0c0500360105511900301070680c07805040e81e0092010300030071981903550802c03001051044d034092048a504041c0c6448000404138000140401d0120201c40c04252a01b0f00111a81c179140780810210b603c0404041101800c0713007056828800c44d4036440d0340c800c0d0101d03034000c20150048040d00f0541c4080a800706015507a6896400343c41010381c1c4241d20000d07040701c2c243c1c2907004d50440320f10644098200d0340c1d200c0e01c40502020030300d25a0b0706100e01c20803070380e42040b001c44940040c40180810280340000d200700035020464040c0c8043d0341c644156200c2d01c44004e10740c4254103a4080b00b43c001c0a105141318039041403007a507881954101c1c0540c0c00c0410000c000100d440441b88801c0d8450340641c0755585410b507008034059080883c0341c2c400c01c4118000b40f40d070307107400c2c619180c021100c0c00002c0e0100c031072210081701400c3c0d6100704071890160008000d010713080140400980724050700d02c00c2c410004103100c101078045202105080840c07030741c495a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 320978309 1250 320977059 320977067
    0x70507020120010c110703020904080d140a0906060914190b0307060509100c020d0f0c1a030a06050a06020d03021b010e0a0611030115030e0a021c03090b040b0a110f030307 75
    0x105000d060340b103041034002d2003e0344940b41e8125020103504a5202c09c040740002e1001001005001c209a40002d03650400b6030314640c3c0742d5000e6034590292600d520001c414002d842c420400144a4401c0c10004140e5800f00c03c132134200002e01ca14000b121003101590300d0900b81d08282c1010900801340c0b02c10a80310b0001034102d821076001c05005500318071805441600400e031545540d40c00401c0203407035007a01d5490440a065666003129801c20390000018003c070b188019410041446160325100d1904c01407107000c40d20645d0010303110380c1c240c1c01c042102c40d0f000715402c1d0890303045144c05a5500c0d00008440c0c1d44038401529034a540d1328000d600c161107500451103a07501e03486048148401203a001c22a900342c0420300483c50410002d100b5201c8090203503202c505240b06210036100c0791b0100341c00292a21401c40031440e10201010114010140d00c2902071000d084019001e6040034204a141401800380d41480024400e03552501090036104014032a5a005403e0840e40d4900d4000382c020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 320979559 1250 320978309 320978321
    0xa020913020d0b0a06021608150402060715090803041203060b03060103090f08070602041802040506040509061908030307020c0301050c0412050a05011505043801050702090f01060f02060f07050702012001 89
    0x1000d99413002d0011400031008101c16271014840703200d5403101e442d6a001c10240703a01c1048110340300b00441145828981d0380b4021401441d0080440b030783c4030301c4c060502011441c425005001014900311050084000400560390000c4080c60000b41c560010303c1c092010289003400505129000325402040002580081c01032b80d06800038042e805101203e180f0980c016070044a80c4100d05100c00c1c0860304004150315400b42c0020980b208501200c0450b241d0b80060b07420145160304000708001d13030b00340c0400125440203001da0003002246407603591500ea0780194000c80c07681565404000302170120400c6415a01500302008000a0145450110340c10980d446030501640c2803117407d07030324501c54484556000f4000d841561201244403809984401c07010740c2e407810311000744030342c41c090f8030307980c648030300c40d00140d00d20500c1541040e0b009882d500d1540d01c11011940a5010880c03801c000f1104540c0000c01d42c200f080e00d9001e50710040c0d0304800464500f4901019481e000055a68150042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 320980809 1250 320979559 320979583
    0x100e040e0f0d030608060408070b0c0412030e040b01140d02030403030207020910031208090307032a0b0f0f0c0a0507032c0f030303010f0506031308030115080a020913020d0b0a0602 79
    0x40000f81d1742c2d90340c0310307440e84c50480e0302400900c0140300c0d50011411101c000c40e848610400560b2400c3c2c0c42d128a805444103010050300020b000c2c00d002c0c44c00342800d10583d240b000c0c007400c151007000c4850460b00168411900c0d40f50702c2075008004202054000d80546007006d500030b0902003e40303400c540c1006040c0c914030068518451551481d01850b0048002501600001010310b1410032651419a9802c0d403403001c090f403c0c0c42080c1040450310000b090209000e200e034559114a0428011411a483d4090800e50400076030300148a14031551108542c8601d2207410030741d0f154140c0e800c090300c0394240751010a01c050903c1007900d802c480b1202801e074800601301c0c0c3d1032003110400c105250762400240585600c0da68002000d020034504003018590010f010420b103900d42030b50f0303950045250020f9200030004220740c1100c00300030390404d4100ea8071009a9504500300f0320481c0c001000505e44c500f10442c101c0e8002400c8004055940003c02c8510300607000e80c0540f940c0701002950786a0040207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 320982059 1250 320980809 320980811
    0x304030305190309120f0e030d02010903021b0604050907030f021303061b051e04031208060102060901142d010b180904051209030f0706021c080402100e040e0f0d03 72
    0x40162501a2181103101034002908000715150204140c500c1d83c0869099010b000c0320307d40f2001c10740e40070841749690060f25030000c90341c1c01091601a1401e9031140c0c00300c075a4619030b9044603050321034800391821142e04607034807a150f8640e800290300524040b003441c0c0c0b04c00d0000a400202030040942c142c212480740360104003420301c8414400c00c009140c2e00442c00a0010011001c4050107040310041c1d014403401014030703140c1e89949403030701d0703214003498040404c1e481003c01c62250b80500680d80d00180340720091000384046c281e0080706200040c60541c03114104403a140b40f00300408020a14117060032070203d11945c544038401c02680003030550392075021010001d4189401c2c40021180036913404401001c41c1c4212803081940ca40000042a4151042c048660305040702044000001d06190b0040c0800306809401c02d10a042107403401d90621001c1000e000c01a141d11601030000103140c80c00000704400d10000401410a02080800d94441d51048454062001c90262140001518 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 320983309 1250 320982059 320982097
    0x3050319050406090c0806100b030907051903020103050c070506042d0b041b08060f061c060605010206010605070b0703050903041824030c0b0307020c04060b0c01050c16030c050f0304030305 83
    0x1071151f45500488a886685460b401c0c01c2010414460281d0b0f0010b03d000181c2d00540c0d12a4081041c01507485100c1c3e484c10140c002c00c10940d40c01d403041d684c00c50b21540300c0600d040102e4071a00c1d91140050001403041c0e480c070988030b60740f0190303070841c110315480040301090510090624000d1603605440c00d90b07002c6c0710502c039080701c560300c919004100d5a00e50054100b40c3c0d5016444600c240b4001c00c402d03005544c0f03500401c1c4014400640e80445031050000040c030a05100c00203240c0075050b0001000c0c0101080200e021800c42002d465024400303140108440d0740d90b0a007a402c60089a20070881c00103440880401404642c106680c3d00400c01d40c0603000b031011040d0300e402e4144074400600308103450401407011041040080d5441071b41401107805021411700445c3c225090303940080140540401e00003907d08080c040d03550403400000f0f005017880da00e0070850311302c001c16180003000d0140d181208802c01205024640384c2c07842400c1500d032245e0342d906025150740d01c043c9805000b0024aa = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 320984559 1250 320983309 320983319
    0x10081501020f0a03140f0f070308090105060d0b04021306140f030114010b07080c0307030e0f01080411010516050304142107030f02450105090403050319050406090c 72
    0x801c000c0d401811402825164190344042d5281000c1481000321400100b06c0800c215203c1402015403148954a0319a0b0311040d0400911404014168002503410b103405c0c07084a0381c84000d01c1c00c0d40c030b800440d1051a03861318030000700801e41c20540301807103c0c240320300050051190600c0824402058840083c0c850101082500320744000d05038203412000b040050002c11010b0002c0d10b10984954501c2c0c0c0342100d003504191458000034800c40004501016400c000d042c200748140c0d52031400e0030100141d0901d640c8145108503481c440030304103c0302141002d09000c12a0800b042190410241c81d80d070354590750310748040b1032400e019a0113144904d00340a03002c01030359001c3c885050f0000180c407115040d503a848009800d00c01d000c3e0ba200a0004001c44042621060080c0c0c401031022412090350301c0711002e000110150001100492050380108500d88400c005964410b500d40f5280d56640d4602c00c40b108288990701d29104158070348030070400cc020b80307036102113201402500a010700b141d4070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 320985809 1250 320984559 320984563
    0x507051908030301031202030408030408010213120209060f01030902090109320105060a0e040c030b0f0a0506030f0405030c16050103060e1603090323070b10060f0507050c1008150102 80
    0x81d11030740328a640b003000100049520b00f89000f400d5519031054034079107503858504928640068209800d183d60000f08058109105c01c0ca102c010305d415100310209a5880d00022a21140108400e000b1442901c29082c83c0c1e11a60050603003a900a200a565585454403180100030824041040031701c00000c1c0e440d105900c024440c1800504c1d28510081d81c2040140032064020090784400d01c840e541c120150b40e030340c80c081d1640d5a2800e070b50001b071740300c21002005891400448024081c184c5001e0902c15520f5400c1104c4e80050583c000c4249078449142c440d00e14811141c82529a0003910b03079011200708149019002c490b401d0340d080c00065118100030b54900000d44039280e14480881c0042c504ad40250005074070b29000c3c0c20800aa40e0070380b000c0c3c5151807406000d24182171400183d0310100310300031401c1900042440c1080c0d13000c40c2010005002484001100301c10302c807010a0040800c481084a032400c0e90016241e038003e01e04000001e008070000f40c600e400c02602c10050f040c400c0d440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 320987059 1250 320985809 320985859
    0x1009030e041817030f0a0903200d02010b101d131d06100f0e04050a350406090e0907050a0e0906060d0201050406050a03020f0301080d0801081f05070e0409050705 71
    0xa5246003481c0d4852105d0300e070050860300411018003003240003030300080100702d4040100200d0700c000382202b6412014002d003110000c1a00b80d1103440190300607424581e010100020894580103444504400d5500240b030040f80a0f480c0301c451410b014514454a5007081c0d4668640c5100f0104d80300da80f14526002c0100019008102c5145e000000c100408603c90480d65013281c001c0080d5504480c4a445600001101b941c048002c2d0100e25414101c2a100012901c1c8032079040f01c6250916007480c01c000c100900310311880d02840600004120551424401d8070000c21000700500a511f92721045a2070a032411183c01d20076000b042e0004000d400d01c2110500c403243c1c140c2d5400d10300340c103000701a00d10340c10100650301019400c3c05009000403960005501a0241c88000c0c549901c1e0198014086801604014400e41007a40f140e000344034074412404890010031717000b10b41c1c1d664080c8103d501e20105403401d40d005040c180c2000038000042030482c1030b20701c155035202000303003642401e0450302c407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 320988309 1250 320987059 320987071
    0xa050108061933060201020c0303060f0a080609070306140402101412090c0909030f0d0c1e120614130c02010e0a1b0e091009030e04181703 61
    0x4980d0015060300520490b5994803a146071000401d00e240e2104120140c2c400c141420101e500101281e02054007104040e004204500c029071a000d041e41070103480340000303401503000d01292a10036140f0b0356910a42c801030a0150201c0b600c40c07509108840c0e03540260310003910301d10303c2d040d59882503045025503203100b181c01411713010055090003030031104d1007a8481c0308980070b1000c0c422100590420071649010701d929000410b402410f0f10100084410080e042c12210780c400c000348810003a804055a03103a54000d040015501d0204109480c1003580c0082d00030204145114540c0c4240c06c03800c09071071010525130410400391158000ca008a0a001041e03070310044a4a101d007804486811517003001d0014400401d00e038480c26030007840c1c0042008121081017002030199020506040400e0080400c9120008903040039000641c99246032048582a40d455050f69000d042c0100342e0300700c1e00c2001503c04c01100f4038085802101c0380e034401003101d03032010410384a0312010f1004243c0f40500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 320989559 1250 320988309 320988313
    0x130510033c120f0306120f12090f0e060604090203090f0f030a0e0910030b0106020d1b0f021e06030a060f090203060a1502121902010e210c0f1c080a050108 68
    0x8003940010f40d0141c1001c9075800030940c5503d07001c144040000081500341d849042a0024640c1c140f900e5004003110b09a10b40c10444200400c0004c090b62401d40403c0782d0180e18001040d0300c54801050191040d9084407031124000000d00c022080000748504021803401c040e6801404408000340d268450b40150b040081d5205d180700145107085400c040d0001c03e0100c0b95644c1d540c0d80c0d45c41c141c441100f6800705c0090b070007aa00c484034194000507052000d501a1000714520b440c1540ca4411100e4080c1d0080e0152900100308104900d80079000c11440c140246010f0703c914081400f500503041f41d0007550700d00342c07504500003030340c2002d40252402050300500e09000942468150300a00a400e041e401c110b00c500044602d1119001340100002c2060409402e01b10000900180c01d40e00450310300b089030360100040081c0c030f002503c1a10b80385140140c15980e01d405080c0024940011000d408005024440c64444c5406005c0d00050b092040c0c1c1c0c8a03c1029a115040c0e10b084603401d115400c029 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 320990809 1250 320989559 320989583
    0xc05090610120e0319090518040209040b040f0f0b1e0c07030302090604090204031a01240f2105090f03033903090706020f0309130510033c 61
    0x1200d54101d0403203d0204000c0302d0800f1000c41600d500040c0a1004a000ca4818141804507081401d0034540c101804041400c450500e54003040742c2c100d00600c09481c080d00107020400704980d440c100c19205e030304051003e40b0640c0600b400a00c0503010b963700707040841440c00e6000e01071550409603120346290385140342040900c0d103081d0701a61085043d0b0380e02c0b240401002c6101141440500b010b0f41c05965140f444942e690b13100c012a40c01a0040c5546410700d101800302d0440d081043c1441c10b00d81d20740b00c1540041194242d80d41c03100180395090360070f00e1040d51015a0444d50196110b040300b0340844621030f00d401f1500d078581c4400c0d08c1280d0703a40075030014109a000c1051541d1130080c4840a540c071040300c6d6240000140e002500c0c5261290051003042201c190304010f0000750361450000340d4070b801c03152400500c111840c01e04410f40d0782d80364400981c40c4103d10829200441e00b00d00c00f100c0ca4946040c0003c0310b6140060001e886991841d9913030b071020306000c41400d40c1580444140a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 320992059 1250 320990809 320990837
    0x140607031a0d0804030c081011040302030a03030e03040b0a110c0f0604030b150d06090506010b0322020307030221010e0d08041103010e0f0109021503090604030f0302160c05090610 79
    0x4806410b0019076400c041008004009031000038440024010113010300303103000401042a09840c504040e2801d03600e401d0009101607a0302040b01003050741e250400244c0c0303c082000c05e5007580036950090340c0b030b00008642000d000d9000100c220b41500c015069400c44224041044091803036100010b8022100344002c0c000a00c4100f1403582081c042c5a40010410b00d641c002503000c8507120046607121744a01c001402c00034104446805041521071040c21803401c01c104000080541c80c40004000240d071080c029500c0038800303035001d590090580964400c20b00d403101c034035541954281684d50311b0100d101840d91004240703c02000d0066030340b904c00c0e840c2c0c1e07243e004e803a80300702600303603810b544c1c540c00c010243c48204900500129000004111132000e0f004100001c00d102c0d04800b0011010020092800b90104105e80c0c490740c1070512000341d0b41c445404a009004a50307075804449460441d04013806402868542261030442e46004640d80d01c4d018000d40800340c0c058040850300344030390020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 320993309 1250 320992059 320992069
    0x30a05040e101e03050f0f210705010c0504051c0506070c050f1005010f1202060702091e04050303040c080a0f0204110c060f010602010c02210313020d140607031a 71
    0xd002015041c031a071a030b5441d00d4200c075414080c010b03582c01d581601c2c0c1040040042c00e1040c841c03080c070080b001e4038400c0f5101c90016222030f0000501040003e40c80f024060b00007150041c0c849070740e081350003007001084141001c0c01c594040e004251080fa00b221b100c05440c660a060201c0b0564080c4c060410707912449400d0380e00c69544102183d190141d0b14901c03000c00c07010404401c0c043d42101d0081419454208101e2404000303800c5600040382603080031015840351000c17203481030fa060718111400c1d510f0113080b0080303801318072210090300c44410a03c024040000040c500031402840340c17101495460560940e40c4a102c64001c1c00c010510021402620309680500b142c2c6410a02d014604044440b4980c148003040301c0318a0805028001030051990901c14040107081500003085800a000f048450503841c2c601007418800300000000c04018003600c0304440c1e2a40a800000c81d403c842c580303400d5036184054210a9880b6a40002c0d030b106100307010f10760601441c49104002050743d201402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 320994559 1250 320993309 320993311
    0x150105151303020409020f030a030804020f0d050712050f030d0b040614011e020f010905011a03030304020d08090a03021201140a110d0203042901170102040b040b09040b04050106031d030a05040e 85
    0x191f40813440103080202c0e40c170203000405c10310f4407a903078811b80b511380f510401c80034040c007820031030090040d00340900001d040090150256100d04418190381c00452030b20b10300d0051295990301d03140c04003003031a03400c48405400c40b01c0042401c542c24003419441c0c0b40e941c0d038110078813410b1034002141440c04854280098610400d455050f00c10382d1302114803c0c0f080c500b9100d510b1003c0b03a440e0754aa99400d40f05d0084540803003d0007048014501d907003060340005807050158400070b4400600000c0c44840daa03250300c03070f03a00190b6002c1d008282d245180d0703001c103000389201d12030000782102100029844406622888030903d14008001d42862007141c00c001c025000248100c40208002c110302c224100b003004074605c52504040354504a6040501212146280d491000c146d40c1c01848140100c41824080e1019203e0f0000c9050b2101c1a440001d4090031880c4052030300a881d183c00841c4040c0d15400a44d5003001811620100320038411481da540d100d41d04468000400903c02070002090300b817055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 320995809 1250 320994559 320994563
    0x5160f061d04020d0f05100302040b0913020108130f08040306050609010b0a050a030906050c1e12061c0f05010c200c040506060d020a050a0f020313031211150105151303020409 77
    0x10441c038401005ca040300e5003620310000200641100b0030443c940703401500c18503901640c83c4c00403030511115010406406140080c180810000010b004900d0680750814143c0c00140c030560810241c00c060310707140d02a00040c0d17400d504000000e50700d810b01c4801981200c0714160b00c0391a060885504484540181203d20101515418964085030241c0103942c0a2500d1103005903a44980c544460f105080c103103800da4141034240006100b00e4042d2115039440303c0c043c2d9a072690320f10840f04c404410011481e0003481070a80d90010424800e055200d0940300c01242c80d801d40f00d000580d442041d50111010f42401da520600700586582003540003680c00840180000e41030110750607182c42660002505100010808240c0103003256001e11301302c024002c1d90003e03500c2c0410350040f42441240c94040500307440103d203101c07400b40d8441c54060000e003800f5026101c01d01000140741052000030701c41c05100b0068007014a0039540382c80100c0d5030a6416403c41031045182d90b0038400904401c0d642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 320997059 1250 320995809 320995811
    0x6140a14040b100b0f04052d2403040303090308013305090d0302030702040b0f103005160305010602030a080604060e0106020c011e1d060705160f061d04020d 69
    0x280c40d816000181a201c0c00c03101940792294200002c2c003c038040c03032102e00094550010004d0301d1071050f08d40101c04034001075a6030401034200c1c450000035154404001401003e000040000f4940d059011512451083c0e542c1c1b85941d13650400482e14017080032600d180108845241e4906004e4445249e03400c11403428181c4c10f02c00e20000180b2150845001580586c000040070011490700348102c42444400b02c915440d0340c0500f1003c0f8050b100039040c90400d200d4007444402440c030985414070440000b0081400c6058070800402c0d01405041e03c840350450140726152054074000c0c003626040e1045540118242401b2a00441d00300001034080703a04180da802c0301040400b90603100e107020f094503400405444604400060042804406d48283d034126610f001c106140c0c0940a0081c09101c042c07054281d070700349000141c1e10310448100034164402d4032003425840c01141c805a04440445d515101c1040d52070500b96040b10b208085880c01c0103500c1c1c540c10304c1d40b8043e07014102444070000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 320998309 1250 320997059 320997091
    0xe0c220f03030c17070f081c051e0c1603081b040905090610062c0301050901060602060a0207031b032313060c0b0c030612010906140a14040b 62
    0x440600e4204103a08154002550b44420030244122540f214500f80d40d80300c0e800d4900703912030701c031100c84c000c1c9500c0052000b01c00041c207501c0c10a50150780010700f10711020400880c1404486030720f0308043d02c2e141000d00a201c0c0d00003480c2e9022034058441d9201c02010083d1410320035a000ca0303109400507c0c0b00b940458454100042c040c1000143c4042c103512080040e15041a50906281c084010010060002403000c00d00c10582d00c40c8815000e001614015a50001000301d410020319008405507003540ca0841042400c40e8150880400c803051074080d10a1500c070555100c003a84103046000e40818440c24011480c0c0d1220080c2241881c00ba03c0c15948114203035481400d00c40d80444051343c84000852034400c6240c0d0440e0010050100d810100d1000c0701c40e03601c5401c9140001c0604003100f00200004400d0344480107001c0c50295940c000f004600c3d46032070720070f005040740c00700c05601400000016076892140d2040304e99400e402000c0010a66581d80d4203416014010022180c00c801d01c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 320999559 1250 320998309 320998319
    0x319020705100e0604170319090f110a0e0c180d0506010e01091e090c0803040f090b040608030306090603010209040c0801090c0203030f0a0c05070209040f0506010e0c22 74
    0x210150034000d12400c0503158492800e4005815141443e400140c1900302c075051200084000ca10b021800307900c03401e026129594980d0a141c42c40c080d08080c007685003000700000801c0111031a00e02014456031070442c099995800b884a100740718080c01800d0750039000400c6500084501419000c0b96081038601e5954411010400000724407001f2070351039000c2001800141d551124140c054040d000c0100811003544d04170200b00075003210400055076890300080248000002c24034050942841200d03034070f55440000d8003035080e681c890865000d01e81070700221f562500e0300502c400c98054600640c01c540701c40e41080716500002e40300f241d06650802007505503486034083d520a6034101e0301c0702c025944c03500e9019015a4509a008030842d001002000600010100c0303040d00306c0b06852000540303800c0500f050b00d00388a049000b0754058508010401008012030100702d00c24410010b80e082a42d03507283e40b40406030283c0c4c2540c020001031000500011801040c411950f000101c58201e26a0311 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 321000809 1250 320999559 320999561
    0x607021603141603061d0606010207062303010803120105010c0210051b0f010b191d1e0a05040614090d0507061404030305060307060f0f0f1815030b03010618020319 72
    0x544c0c0101d65043d01e80105244005000701040c088180c00c00141c940f615200b40000e40b98100c6025420522480407410300c50b0700400c5c506408450901540c0303550381d50b1920440d81d80c94010164000c0307822100400410154030546000c01c2075940030b403011541c2c91a2810945140c3c004034151000c59a0304c85491440080c2040014054103914000050030182c600074070510141c800002c0712200900c8004005003e0508a00308000d846000e0751940e54881d043d9000d00f140c1e03e07207004500501c6140901500080aa2180b030049100321800c101d000790f0b07692041c3c0310440c200c40341d000c0c5030054958842218020401070000c01d03c01c290004d25a449411491141c050a66040d1300003a900d40401c5028141045541e021f0044e40c18440c1c01e4002c001802481d44000c80c400e9002c0150504070089010301a00318602581070310301c42c40b0550394444581000328209030311400b000a0800500010a040610402043e40c0744a1105201200c40349842c0001c0e6201600c031001858800700c92602402c16 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 321002059 1250 321000809 321000853
    0x11131d19230109060e0c0603130803060607050f0706122a0201020d060f030b0903070510020a090e071112160204020a110a0305040807090c0804030e040605060c03040305060702160314 80
    0x82150300040041e005c03246545010604030b0b41c45e00030201001446002e00c090248803640607400780c0780c160b0342c2d5100e0002c64241c3c050044020401d106040c41d0034408900400c4ca501610120344d10701940f0310790b004500d4240c40d080c18606d0007408406003004445e10790001d800c01c280405000152811448414520071100310707070b01c110301c8085149000e1040201d001c904c3c0340c1004205000314140030b0307240c980720b4449040c801400d5245900140c011000d500516080c802488c0f007100c3c1c10028903044101070402b041000602c803003802403034501900c0c444824156085000315100d0350070045442ea09010080d0b1242c04a4802e1001d4034490100d01d040c1013001d01070048c440d86d25903803954a054170031131800c1c0260304501e100b24101040b81c2e80440d4080c3c04280d009030140b071302254001c003000124001304003d0f00400d13000f52000a04a44800b8004000e0044034030890413143c02e503503404002ca032a4103017041c83d10105000d201040000c034a02c0d001c014034048400301034840e03110524076010540c2c80303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 321003309 1250 321002059 321002063
    0x1809050919020f21030721170c03040609060f0b0102120a0e06030907030602030c0703020c01031413170c0c0f0f1018090c0c030216180911131d19230109 67
    0x101c03040140c040e082e145940287c040819003400061030380402c118100c0300030010b018010085012000405010b03d64110071400c5820481c20068a091a00380001601084400754058403d00305540d0503014032104403900c8041941c1c0303944d41d03149020204042c45d480a441045640300f200700c044041207051004501540d0024080c941c5c440d104c2c0b070003034107144907001070741e051500e000b00e000b44202d1042c01035a800f8500141d42c68407184140350458040d421624020b003210780201d0503640b0060000b234040c00c024021610840d502038070a080000305d03418011595004068201050480d07401204440c0110f00c001c841410b509440c0c075510402c42c1d4040410000041341003080206260f01070008202d440700c000200d120f941d0410249020180351150f40340304095607440c00d60244020900e440012207030080011541403c40c41d21000503100c4905e40c0358000a1150a1440400001030010740380100b07224802c0281c1c00769101d0070b22809070910500c110380d0f4600b03000d0031030034020311500e00818 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321004559 1250 321003309 321003323
    0x6050c0a20030609010603080f09031501080303190506030c0d081902070e0a0e210403150504110a03030e01030513020303030703050a05130c0b0702011809050919020f210307 76
    0x746400201482e001000d441c00182d41d24100061020440c208104d4204040407950503540301c1e50800428504000c0c180d4403079441c0b24038800841c000401000840c00f81141c81d24070b03c2c41c01240c000c80d40403560180c071381a030303d6404100000b10a0400800c1e2500e4140120b00050a010b62034043e000000c0d0348140500c0181c101410900500c40702140c0c207030f000780301460304002001c018a02c051307a484452189480071030000003605021141c000866020315446940560101c50150041c009010305590445000d101107068500500340b0038104c3d411a03030540e03104c44d00c07015910015401010702a00501010b500d01c01441d000d03840030070003140502883d58001401e40b400d030041204071038014041400b91580d40202c20f0205012503060819180c00710071403079035442a480140c81c602c059540031030b4089030012002a601d04154000c1307100b00c014605482c09860f0302c6d00044040050b4080007540060020b00d030180c0e07824880406c2e01081480120301c80030b56409010b161450300036400495100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 321005809 1250 321004559 321004613
    0x14010902010318050c0904060e0f03040306060605340c031506060e22061203050c06060303031026012f0921010f02120103020103200406050c0a 63
    0x55a1503c2000f403c1c00c2c01003000740c3c801440703940b099201c207540000c4a00c1490754401150074042e55512a48030040c0e400d04641c03c820741c0e005541d840350414441a601549480000200039010352700311040c1000b220003031158020310046c3c90042c0c02c004540810b45091340b5003480009909800b001020310300881144542c0d0360f10014007800d8503096000101004041e059540040e101d40041c0f40d43d0183c40d09007655503840b90700341900244074950020007052001103004050507005001050300d481e180d030603114076070f4804c0300307040d43e030f1006850b40020b1418180082129a0251182c460259840c40c01032901201c0c0701c0402d03003981c0001c0a8030079103450005410f110481c801504032440607460b041c00d800d000554001800c030403401550f451154074031003d10140e40700f0a40c00344215411030201107484030301038101c80721000000d001c224007191510041c6400781c1014040c64012070b00605405240c00d0901d541140e242d00300700d40c540a00d102c3c02c00760711f00040c026050100d6400b41c0003160124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 321007059 1250 321005809 321005813
    0xf0c03021213020a0501050a020a1703060a0f12061116080d0b0a0e06060304050a0f0b0403030506090405250302040204080303060405130302030702240d0e01060812030121140109 78
    0x10076805801110454088404040140c5410a0b00c5003200c0c000d080168544400020680c00c0a0001d003005208541c10740055407420400b50143d806154240c85515007580c580354158042c480b503000d000d820082d040350480001d14190802c4031403a001d4090203062000201311a80e1180b1540801c89000d131022a41080c2c2c0c487c0c1d84200144118100c820030b140519104005030390302006403845010b000000009802c0c8581000b010840c9544848018500d1a590800d0b0310f00c0700302610103c000a0420300031444a14001030214041c5cbd80103005014080740c00712444646192440b4064810303415801c0000140e5030f1480030380001e1445002031a62072030301d501000101c1704010704d0b0306003c0c04000c05c05030229500000f40e584556056a852400030000240c8140b10140008092145140002d010042000c103400180301840da120091110070303200c0c200542c44081040315801014403d10040010b00c0725046500b21072440d00c001082c201d141a150f41c10400c10064101049039115000042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 321008309 1250 321007059 321007087
    0xe0118053003090606010e0d02010518210a030e010c1a0928120c03051803030d020703020a12050c100f090c060809060105011b0f030e030d1d1f120f0c0302 68
    0x1d4943c220781c1c4230307015010f507800070384a405804006481c183c007118031040b450711003000e1494882c0c3c0329614030b02c3c0e1000c0d161103942c0c0c9a40c540c80850004460300304000d05940207990344908650310000c110780812070070b007002c0c0440d00002e00400c0c55105500d444120029601e0900414620b80c00075072840a559080c0403003010350300c0300d0f0141004242d229400104c1d03400741c181e40c1c04a40e0394214032040740c4c4020000340b940c040e1a0f80400114800144142010303000640302c1507003845804910742ca00c080c00400d440b079000e21034040603190401500c0c103c00c071901e030303010081d010501800040c06541a0310b5071028041a5000729000c03d01130014400b00140821545004100074605801310554400c100805000c1261005210002d5280240e0400d8010329000707030001000350450710b0141480000403e1007010340c60010325055100130022103410414100c07000c8103400c03801c6540804420000b00e8a084003c0000d4800301e580d8121444103500c14080c0c40103000c0d895401684a07205449070007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 321009559 1250 321008309 321008327
    0x190b0109050a1701150b041e0306050a0b09100e0606090114030403020703031805220b0909010c0f0e0a050d02031906020301170d0212030a0612060e011805300309060601 74
    0x3042c1106000f404110801b5140119410754480d018008019800c25004051a03c080d4000a1481e07081030f0400c80100703a00d9000c100c0301b031404c441c80c101c55211030704219181409402003805007542840010300781e0410368014a1820f0041c90658010f5200c11170141d180c2d0004d540880c01a0400c1c0c00400a16500c02c20b41d4980e0f002007213136221907a24100c0010f40060b10085110025406c00b17001c640b83d822a40e01150070400d025041000510341043c116000340fa66000c02c40108801c0203001c0502849051001c8c8000070103448000c0b0325040c41c00f0040d5a000400b4101d074140b04401e4101d040c080c0801c044d01c3c8840c0302d540d0240e103075410301c681041c0303c00d00014109400c0d0700240842d07010030b50014131452000019a0701940e40d40f100346030741000c2c01d0f19422a0b450071940030754403c10800705500c4044aa80690020010b45100240f503181c3c0030088800640154480011001e00c1607613111460854040c607032041030500f205100121075500201c80c03600e03280d0065403c102155030018111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 321010809 1250 321009559 321009581
    0x1806020c0f07170a150e1c0915080c0d0603080a0e0114030613050705040902070f0501150339140a0504020a1409040e03030108070306060b03190b0109050a1701 70
    0x180a00740e0f6601c00349a0307181950040a081e40d82000c54010f00400c0946c00700c500441c1d42c0c000c0d0741c0590342c50000c407441c050400a881c000108035640010f90a100c14590030804411940da0a21544911051003050b4022540c1c1c1d0750281da55060000005107500300500d0341481035198004c44a20842c0050680d403944000034802020400401145540e0407003411200710090500041d951900750048846000c0c60300000c0070700c1d100007400001e01000c40700040b15148035100a1080305289100c0038107281d00c0f03200003031010900c5105500b0070380403038103560110108208600320501c0700300000201006560700084c4030650040002d04c0606020f000c02c0c2c00b901058074258078101c00e0030300081c810300900c909880c0c1da88000c10728843c65a941e800c0301c2e5402a80c101202d45030b5841d4016a600d512103480f08a403901d1070080001034a0340c5480030342e4030030321104450f5400900c0150103071024002e6628000d04206144e44081901da031030000700b02c007400003c4811621179015480950848482c0045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 321012059 1250 321010809 321010829
    0x3120504060e010f11030c010e011104030809060c03091c0506090d020318011205090102031819030e0402070204050a05071103130b0a0215090303070e090601080a1806020c0f07 77
    0x501c5030701c2d00301c040021400020f00e02150821a41d5008852018101035000024017000408400c0000150020340b185040c540c000c209105034080540410300c103e00c0020160942800107800618020000d0044400c2d004207491800c00d8240000f03c6482112803002c01201441c80c10405004003007240c2544001c0078030041c04103c4d00c211300a03560780140a17041c410151072007490400e90744100303030450610252241c18010b03814a191400e010303420844042c0c5d400a024003052a204400241a44461005d48030b0741100d040c00d0b4804480500c0d42d0315a15070026000c001c0d180058035144180c3e8411191400300040d40d05003400001e0902a40c040705c3c40e03150388184804c005c000210749202c0104da01400170142d07038000441090341851107819030400b05403921001c120000c10080003c601c039014542c0c80e140d05140c44005c00050000c103a4071140040d50701c81c0007803595000c1e90f0181c18080441e042e5030303403541c4940d6614030590b4014403803100d00d600b000c4c1140f000701c4000c100c2d80000d00f11941d2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 321013309 1250 321012059 321012067
    0x1207080a1208090309010806040c03020405130614030304061d210106090606050403020319030e1002011e1b0c03050c0a06060509130206070303051f0b190206070f110114070801031205 80
    0x820000700508112700c2250b1703c0060000090083e41210300901025045601031180004954000c040c00c0c8500d481c101c0407007103208007610b804001c440c01d44866031200a03000b0320035252024511544c2d800d0310340003080d002c8100c10002400240c003110b40000000490751900b010f407030f4020b0b22101d034400818494140400e000503035001c81c100100411030418000455003500b801c40740381600e12911a0003502c03080030f119050b0390641001800c640c1c01c1110301e64a0000e4400c080481e040d042e0750700e1524151200d2058a00e01c103242e0850060300910340315040111008515091881003030080382c034a44c0e644400c02480c10005a4598010609401082904502d401003001480b0710388000301010313a10000900c804100d12100e180b5000b8681d40700c507100c1d46400700f442c0140c4c4040b141c2800064a0986891418030001b80385201d1038003030741c1e4801d02d40d10b500802d45490800401c010003d5481304c0141421580040b5907034880c00c0f2996800c0f803654074504210064003156040d0000b0040208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 321014559 1250 321013309 321013327
    0x4270e070911040f0e090105070507030503040f0203070e010b0d0e03043b040f020405151c0c080613030f0302030c09270421020703111207080a12080903 67
    0x819a4411141c01c007a010526034120341e8210344a102c0c0d50000c00040710280004204440040a89440f4800c03c3d0005c0007642c8450001755501c0c02000310040004404200080c00504800700d112a00d86c406421107100d1500c07811111080130f0260402117803ca00031480c0c1071621094000c0c1190004104013a40c035090400c4220302144020007a2560404083c80d04d190340045006d0328802e18043d0380c50040d5a82c00c5c83e01c2d00001d80220702c84207910440c107000210b45131030038049140040100061440320307500b12060084664150400040da0511540c80000034008405d0012500c5403a004200e1499007031a4640500302026007005242014814420840800e00e450708680741c0600c1200d401102e041d041030741401e202d000310102092203003040c00344000c001320000303483ca10003021907902d0800280e08800302da6684003440041e0282c3c000d0281102681890041000d58102d010150340d00d46450720101481c102d66100c040351801118030b00382464550110360260010000009546460044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 321015809 1250 321014559 321014563
    0x31b040302150a090906060905093601020d0f0c0206010b0307120b040b0303120a0b040c0504050d020d020d151d0a023604020a0803120f0a1104270e 65
    0x100b101c80782c41000002c2d407019003030103a994840180107420013808a551500c100603c1c1d00454400c0c94090000740300030840301c9246118503800301101540020501c00c58500c00b000d044404004201d842d5420018402c403000380e4001c2d00410301808801040c15002c1c008024a04030050f0300c100418601030007402551036010f0b000701100555644007054001c0051700150050480e044000c1e407510002490b14840022400a00d10905030114100f0143c900395050100b0350f00c07003000c0f05000600800041c02640750100604c00418009041603001c051280e020840d0006a01e01c140c0d54040814844450250300740103074a600c6084103100900c85c0000300c841c83d5601c4821740e00912610103200c1c1000c035100601d00e001020080e061138494228075030042c0000200c404e4030260b010300800f00c001b003407444d0300004942d941141d180001e8503e989081440307010713810182c110081c00d612662003500d446000005000a05416007044003d20810030340c0305e0740543c40d241c0b04511039003000e05598440da80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 321017059 1250 321015809 321015829
    0xf15030f09030d050a1d2815020c0a1509031e0212030705040302010914061c06030c090c0224070c0c051201090b0a1808160b040602031b040302 63
    0x1280d40111150326851051815401007074400040c0354a08020808504141d801680c910003030030030781007031203400c090055031110610007907000340302d05101e0030060400b00010782c1c0d132110b4001c61178002e510340f1034541d100591703114641580403584800d581100707001e84070006105011142e0f03420040500c80350b902070003c1c82d640100c3c401e81c48081d048482d680780227000500c104e030107030000385569240c41c2c007010b0581d40090005031700007000340c40b01180303500030105582d0380104001d0280c1e003411405851208070302c071403d520410140d00c414000001500302c0c002c10b4003501030400082562011400d0082c0760503000c801051141031442241d0502e11510026075800c0003035403a11484098050409182e4110a03600464004621f10380c03043e819401944140304103031180210703220f240c8540f440842600e40031003030649400301c002041000146948010000405280c2c01c811030102c485e21049a103040840b82501c580c1d80000c200010480449008007a120070611114201350558000c1046100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 321018309 1250 321017059 321017071
    0x41e080a0b0c1c050117070f05040c02030d0e03041406070f03050a03021201031203060b04080601061206030203060a0f05011505160f020901081006090501060f031a0a0806060f1503 79
    0x6801c000c01c0d000c5401d00110307001600b0600c1080d26015041000400405091066194005660380d0060341d0a102107182d808441c0204001c08a16081808110080000b00101030943c0300030000e000e05d940b41c40c005c00c1402c2000c0c0c0080c645842ca040030010010124010390b91003100c04024450001d54400c00c4d26074150303014075269440301940d100c260300910451405004440529000004200c00c4200c14019070585039410711641e070356400c00e00180d02660040c611103402500051050034855500d011481c5040e48000c500c0300c1d80c80c0c02190400c6415210b059010792503a00700074041c003c900649006001c4641102c5400110640013042d40c0680148040e60881a05452080c006000da80008003030300144a52036659503501d0890340e80c0a40324100726100d090040c006a240a5403052034101c60540c0c4801e001215501800c8005041034070700e4600004188002c010b840d100d01842c0c40c064200b0b000100010704040c0104900e0041c82582c480c0308103904400399494801240682c2d8001c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 321019559 1250 321018309 321018323
    0x30f081b070611090307090608010b0603240102100e0303041103030310060c020d02090c0d180c0303080901150b070204060806040807021c0219090e061605090d17041e080a 75
    0x90b500480030f0210712810002c2503241c4034100740800c620f105a8400000c440942000700007059404003840781c54013040340d6030f1020b03a0344000300c2c65200c240c1c83c03146c0003500014810341d1011401291004101c3d40c1003010450554400f104010070070040c039041100008080380110b05500d840c2d003400742042c40d90b0103a00c2c00c011103074a12408546500a0b0420926401410b00003580f4000c00d081400790410001c1c04072450400009208100040341c0100e40f00ba000074011a009045072816a601da1025103c880e441d0350743c4400d040041c04802030380016040840d440e9544895600411065402d680c00075180e580010050000083c0c001e411941450b5050715200384a8140100f070030003a03410400301035040011b0f64414441050071526600c25140172510070042d5240c0051180c1c3c0c0e510080b500365882251081510000d58060b40107025034031401016130503d03408a58821050480c500a02c08590310003250a00003540011385681d941c04800d81c1d201c5070ba526192074156220014030f0301400b40c0e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 321020809 1250 321019559 321019571
    0x150c0501020c0109030e0a140102060c071a09030409063f05070b07060501060f21090812040b0708090319030b06030405070906080d090e090f0a030f081b0706 69
    0x1140a4040e520b00034031090081180c43c05908002d0b01e030b00c43d0015075611401d128513002c5014020702c000d621241c801a030003414540d030344508601c929401000d0039640c40c0001300c1c141040c150810b212603c40c0c1c2100010395111403030702c032203031056070a20b401c0b074240c00d90380350b201e1100c04514000010100418540303a01968002000364551500d20305406021782c0103d4101060040010300186911807183c0010050b607070769a2021070b840d000391120200043c3d0f5055140b1040c5031440610318102984c0c580005910001d540c1e0550b46500102072641c046220408000912450540703c0d6030220b000d0900410070300d040c90348513441740314110000b090510034090070701c00c4a102e5071281c4001d0001401c0c043e0389040074101650b03506000c1c442c40b00a1410000c02080c00e5201140060030300c00d013901c64508850905000c441940740c0200151420720820041502d000c00400421030840d0181c3c4450303c1100c0d403903d00070b290520041072421040e911084450f405141042141d01203600038100081d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 321022059 1250 321020809 321020813
    0x10b0f040b2206170706020705011407020f060d09210c08030c070c0b07080702150a090b07301409100509010c050d02032a031c0905060103030c110307150c 68
    0x1030400d07400120b0082516001c511104c00c00240742c00684009800300c800050b0b96500445002603140702c1150300d04030510810740181009034980403514002400c2c242024114100c0c5c0c01101c440c0c00c001d036101c0d901600c0c16a240c080c100b072000750451081c540b80064110301d40745e007a044d02c0040c1c0120b41d0b003100054000c06112341d09003d84090911054011794841d0a424002400d40281c28182d00c40c07980b0150a03001c0c80566400c4407200c04042e2038666005113420795296a41c0c003e03c4050f5640b04072071001c039040d01406551007001c0c00455814410203414050b000f0b1807880d81020ba034056020402c0452965030b90305241c940600e8580c50300c203544042590040f02c120b565114010540c0c807914030088401c68000c4080d100b40b03d0040e41d44c103c215104000850700c500c8070404010560002c0040b003410320a41034105400d0103620030041550000d503920076103060001d0f441940007400c0390041204000c50748059400446040b40180700390b50801c114a0b0280c0b8460700e8007014000302a5107841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 321023309 1250 321022059 321022061
    0x3010b16020d1101030f2928150302031b0702041d0d11071d06150c03130905040b06040507020a061103060f0604030c030b04020d0501050702010b0f040b22 68
    0x8455405414400010550f280403c1d020200380c039002e000c24140709519001d09100e2103008881405400d1100d5a0480c042012501440c44400e0a8124410454050460070000107803c00300345441c0300240d450b45021080c144000710714004c13508144c0100140004403d00d1010200e041426407500c030341c0c41300705100080060200c64840c90600a40024410020f003001c602001c00810a45810a486221400080d1180d00d0703406200910880d4800691a008140c00c141780e01c164050300085648840c1e039211055600b100c0030329082640009440c5c94000c072204040c0c002084030030418486800c2c03aa585080200000300110b014035504c600040e012031080091380c9600390001010015025400c031040000d03442118400e0007907002800607100d80c180762040310203ca8000b09640642030071551411121440500244d0f4003000340c03251000424400e1250a0140c092074000103070026a0001340988804000c01d141d100324a026081d480d903407102030042d05a1030b07800c0ca09198280402c00c2c948 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 321024559 1250 321023309 321023347
    0x19090b04141903020d03031b0c021503090c220c090b03040b15040e060604050108120403031d040204080f0c0603010f0608060d05010e0d1419030216080c03040e010b090603010b 77
    0xa507010140c445c11000303254150380291051035410600a400c54515601601e0302d0998860080d00710f00d8000d07060445413010b0014581000700038041e076004803580d00000d0350b9001c40c0e086030244001c201030201200c40f1175102d09101c6006608201e20041d241c541d1220a50000070005808000f0840c00600c10f01807003803104860a50042c0100400a004000d0310798071001184c00c45d01a82c904000800d0309a0000341501c0c0900ca076401e0903140c642141d80c21107030b24200c0244c1035072218a1142049555445002510103000740e10000e00b03501c000316264138038001d07107400818011001000140301d5414035202c0d0310151801810910000e4403a0004a2001405480c01915a51808010042c0601301107000009144035941d05e10600c1626828800e69108000c00e0240c4107018000040519000360094000c0e030008045200550001d51600322156000c003c4c40103154000083c28001104107201a5001d0007045070014108404400403c00e5440103000b2807043c05c001040c00d0b404c54100910b04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 321025809 1250 321024559 321024563
    0x140a0c090923090109020d0213060b04180b0406050a051207090501030501090507061404060806030a0b1807060e090708042a180207020d2619090b04141903 68
    0x410030101c500c9410442c0c0c20210485400d02402d81e80440c04000050183d40707000c40d00209002420070165003041000c160400745000303080e403107032400190043c0110240000308006510301152900c40e84049080b1a030390602684034501e4000c040c00b46458004002040d100e054491100096031085400c7ca01803090340407028090600001008014042d0132401c402482441110810380d2100010354003510000e05040150400b40400c2282a03c600d0031150801e170040d080c0d40c48400b094803185440c2c2d604992070340490194100601000a080181d0001040720f850041d0800c4007100c00224140c6d0054000e80c100700318007003c0f50a2040700c54000700c1f10076002d844a61903481d40305005071a00d80c07501c15500004215041c0318201040780c022101034690041c50522100c245946e00d080c11f000503407000682513485481034505200d840d004015406280040b1461031610364801842c8480d940c000e0074419034284010051082c400d56810000c00046030b601c003400840f1040103030004025840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 321027059 1250 321025809 321025811
    0x30115151407110114040b030406090602210403091202061902031c0e07050d02131e020a030510151704030c080a05090a050913030302070503041509060201050a140a0c0909 75
    0x2504100454143c0d89035902d02c0a03290141000d0030710803c0c2541c0e018034801e807000c3e514208000740004d05282d0020f0141032041000506015825060403090207000c9031007512181301009020034541c000c00c9620007002880e182030b0382d035a81a4041880760080a0390355440c00e8103412890b01060080c4280c910307008820343c4480030541064840030107030100c10010000c0307004950011131142885200e42d000260043d0a000c0725400d10301112009240c0c0c3c0c3c07108862503584000407030034004c0900050041160f40d40e0040303001d060980b24501d42250715403080441917640d031070110a039a0060241c800350041c1c128010000c2d52181815503440c07001e200028803540c00000c0f84a6220b07001809484040c4081e1540000103465600b40311148409448c081c2d542203c505401d00040c5c884e400400aa91140d8160b03400c11703a0314500a581040d02410500200b000c2410a2207001d40c248619640288607400a12074124541806440158041c010501c117644074184614098082d00200f1300400300858 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 321028309 1250 321027059 321027067
    0x1110307080718031a060a0905101410090501140c0a080319110f0f0d0203130b070f080106050a030219080121050c0108180a0303020304110301151514 66
    0x50000c05101d000c894401c0822282e803490440005411014416030b070340041c85240582c0b071030102c0c00344200b00601d040da0154080e02d000c11000c0b46805424001c0b80d4801a15078028209640a81100041c3c100140500e800030048002c0c190b104020000301d03035084c2403202e41e02c039a204003241d040c8210290510a846120b20600c200810500254841c13004c4507282d07030528491090200a440090210004482d4148a05410302c4048001003070110308204079503140100d040310b41c0c002da030021200740106100f691611014002e01e0a051744c0c0c8100d5074609164401641c003c050700008041c042d0000308a0085119054680030390f0440b14116071400801b55030030b1038818003c06c074420034080e000710850b1176540207a80220780355004e044560300c00c1c080e02184d80c0810044800010080450328081081c5400d0000d82c1d00034022581c03440d0207583e015a032032070641440314006c0922840c0038080ea00d0045020030301c240c0c115444040d42c14600100c680c24611081c2292200c101c0c00e2030360050b0304001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 321029559 1250 321028309 321028321
    0x1051c0609050307140a0b07030203090307150c0806092802091e0102100608060c0f12070201090308060f09040b190606080103020a0605030c0415020a080f09120106210203011103 78
    0x406418800d00c240314451001e001810170685549176480000c15400161000c2008103010b900950390010490084908001d6103854100ca091b881168000410b1396403c0c0c920040c1c3d40c00038101d9800442500c20803040d042060314041c000141da1071982c840010301540c9819119660110703040c0c02801841469500315244041000c4050031180b14054811004a00102200f500605044076505006060f0b681c0d2552080010782e0300c15044075401c075204212469444030510382c1240101d44544c00000ca55085140c040c0107004098003561003851588070800d0280c4e07035400c2e03450f4040da02590340f0415850340003400d00800501092511500d0174901d000c80d0035070344821518101d13070088462580d1195555015031303051100703681800f0303040c2c8108010310001028140d0b080c04070b011441182c14102d1107864040c0d0325004200c0040e03480c1000aa441030510b0a0350250300b209020300004c03c621840c0c00719020b11600c48007040f41d00a4944c0d0b44070025540c080d4813071030400b902c6a005030f42c0c0f07187c04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 321030809 1250 321029559 321029563
    0x3100212090c092e0f0b040602060105030c090a0f0621060b040509150c120705031f05031009050f06010b1b0a0c050103240303050406031a060301051c060905 69
    0x701c440d40c0c11881144400d4049180c10401d0344e01418845040003d440308815646064104030302c5280455090342d0000146103403c3c942030002896040d04142c1c0350340c1401e80003402e011040c0d1100e031180c4d026000e108070ba0346d40c410310503402c11240c0000040c500d0080e05c000700508880d50150303510142e01104018460307920103e04000300d10803072041106003900070030841204c1007a074196450340e01c008501055042e442c030419402400c017814490400b00190280801c5a004551500000d98080140040c480d21500101080707280004041d04280c01c20000c26619216644014910b98480c450f0006006050000d82d07078240c1d0040a0310034940c1c5a030001d03400c07540409906000c01408568000c5249008645e0060032507000306c000d2038192038200114040d080c60706001e01804c060400e0300310003d070105490001144240c9030141c64614220300941180d14046001c0110601581503a00760768409048906440701101c44015050807000000854074a03c0340c0200080d1410103e03209220300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 321032059 1250 321030809 321030811
    0x1d0a030b0703140c0405120f010203130209090f100507050408030705010501060e0904030e131b0903050601080304140d0f02130504122d02010e030f04090f02030408040608040203100212 81
    0x141ca06008560540c031041403440d000703c402444c40c40042c0030902c81c2d071030807141001c80c1c280c2400840300c010000a400b1400ca0b402a20309a011788074800300d2000b103007072403801560b020101c040985180c07105580426128103003080210041c641d544002014076001d2070a807070140c244002103d40b201e01c0d52a049000701001c0c0110000304807a0380c0e4400032850070525107481a90b240da1560043d880340f801344120461030840c00403a458446141c500c140c1c00942c00000d44110070387c0d80028013440c44c200141800010380003615690020081170011408080d000e00b620300c01640c4d804010300d030034140001c00b030f04105d0009520400c05002c030720214509800c0300340550300841c440381e4500c43c942c1050701d10000c003030180e0794000521442990500941c1001a1000c9114000072510284280d422411075000000501c96006c011800b842020440d11a000710150314003030840c40d504240d2a5401079010700c0c403a22040100390400039046440600c40100010803811095480380781041c80304d070300140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 321033309 1250 321032059 321032071
    0x10e0616030e04060807030f060902010c2001080c0a0906050313050d0906110606090a09020414130c090c140d2405030c0a0311060706020403050316021903121d0a030b 73
    0xc04d0450104101501040d04400c0360f510a81c0c200e042e4809603241c001400550400344c1c140040002807002048483d0000c01d44881200b02c0b010300810340e040054440c10010700903644600307042c06803680c40e03500003080d03605640c080d04056480e640c40c905800341d449983c107001405406450018404690010102c40c150b40c8152190318240304121040c507900c0c0c070102c4030079030301080c450049002ca24141c4d10030b0600c00d001910218a10894600e402098141580d580248510071907416050100341c100d02000342024400074840b05040c1040144840022609041000300c0050340c0c0b42074a09541c403256030307200341d02c40d0700a102c03415610b48002122a84039590103402169400e1004c1e00c0c052000358256540304a12003824540c04043c0440c075005500b044404030f908000100115204201502e00d6807694400620b0400481c0f0501004048024255003607051100f0148002503507207402c0064051035142c141500842d02e515450310001641c0d00d9900704c9180480401030019100070030313200364 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 321034559 1250 321033309 321033311
    0xc04021306120e150712240503030f19110604050709061403070b0a0504050618120a050312040f1208180304050102070e04060b06040e07020613020f010e0616030e04 72
    0x1401c03100b89201600c040102d00da2030340e00040060b4450144103001641c01240d1854803070300d000118031141c0101c07a401e5821410100410040d11250840c03200c1280240c40c040e0041e500303012011a0400303050080028449054084c003922200c110712a0340c103940702400000869000c0d00300b50078501d840301c0c02402107079641410400b02184400108900d4503c01201078010b00c082850300c1e00c103140c585c105c090004204502000b001900780e1b181801b901c0543c421390062840c0c12107250402960310601907400400d60007040d82e1a000c60004001e40744100056400d448560352549003c51648900310340042902c85c10001c1030160940c003003e0644a43d0910301d050601c0d40990207959580d010358860140143c1c440c0c441407021840410401c0d4220780304910200b06a115100001e180d5007050300078210603034080040102e803c1e8100174141d00300d00500710441d201c107640d07004108464542403441c3c0c10700c03075004210314036502c0710000c41d030030122200c0304404000302d180390085c410b504855509110b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 321035809 1250 321034559 321034577
    0x5042f0717091905030c010e04150f17010e0327040e0f0c030f07090915181104060f170a0203030a0c060506101e02071e030614010b0409020c0c04021306 67
    0x94030388007440f14103880c401001004505058001182d626500d041002e40041e01c036200d020b00c0c105061845009410900b9914000328141702c4501502c00c40501c0490040c0c0c10402140c08001000c0308a8400181600407084c1c09040d000021811258103c0ca2a800500d44554803110700e02c0402c2420040c41200c065035000c0c0f85200c1095a10030904203010507036000403100b00244034503540000d2007248149207a48010840c1e003005401c42d06241562609551540021000c2202d060046069008200c400308415400c0c089082d48401d424043c0000c0901014100c08019401300300e28041e03694007c00b00d95072083e20140080200d1106c0204690003070034540801c00a240c070f10820b100210040c0c0d42c9101581032820640b6403c54803000350b1066015049001c107060311109501c07043c19101c004040c1d0040e1451902d03400b107403404054800000103c500602140c50008202c1702203440392440540c43da4200c003c1ca50030b00c0095043c01d5401840000d0410680d18040420011910ba6480d48159 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 321037059 1250 321035809 321035839
    0x1014060d050d0c150c05072a0501030b010e030d05041d1608040f1401051b0711040e10020301140306090d020616050708031f05042f071709 61
    0x260300301a00003011500700004007881c4500c0303900c40800c490f0042002d2480341c20158980b20860b82201801e1000690010b190418001c248a503004001d84880c60300c0800e155024030031075154581d0140c40c1c10903407114410906a03105e0500c0d0008403500400b942d16684e10004041e02c0c0341d01503c02c54600720305c940041510761490a800c244910840720100a840420f034404550030346000308100d41d40007222543c84046008010084071010610f800040c140c1490000c8014001844c007142203101d41c05c0082d04001282c1c148114821081a14045940d24a0508550614010460740700201d8070110000071400789200d100e038221a01607054038100e41704e90040380d441d402904801c402583c0700c100030441445034241ba141c0b04c1d02e001d140040c208110f0350741e600980da109403114404c403a024045000c002c02c2400b2081d0007400111070400003d5007141c1d15494a140b2064080243c0000749504000c042419084a078250790242d00380742c440a00c00026a20f0307070042c03006203004174a55120307884 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 321038309 1250 321037059 321037069
    0x9040c0b12040249080a0201020d050f01052d12070e09190807062703140c100f090203070e0103030206010603110f03040203010f051509090601030c0501080c0903101406 74
    0x84e0341c4104080100c2c03034681090000c00c6482c0b9026148504500c0703040210200d842600545440f054a50000d071b51070380140d180da030507103001801208403030492900401c0036603120617440f820f02e1140552421403140d8085035031081c80f00d000c00d0f1a0044141408150388810200e020700c01d60b0505448980e580e1900302500c1c0e601c0e00d100412244030040701195002040106000d8070f2003901ca00f80c003203910591039200407d080f01520510322541c1454500354109030700881c01c2001703000002c40c45410314080300502aa03d10707001c100500305c6641d4400c8055000810f420180d84683c0140403503038255a100451034082000340301c1580140224800866510302c40d0060000180165000302d081107100902d100e0641e01c040d1080340e02d9941c9540d981846011401881e108011824240c03000b01c00c4001440507904004100e83e00ba03030400c80c018800540294800d809031042071070680070942d20107aa400b07052141851684d4103204101054943c030301c26412000c040c0002d2000d80a25480f0070090103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 321039559 1250 321038309 321038359
    0x1170f0705010c02011404080304090207120c020f04090f02031c1107050d0803060f0909010e0d03050603030301090506010908121806091f0903060e030a03050c0703020a0209040c0b120402 82
    0xe0000348410f80341e401545c070075441301c1e0740c0703c606c000341614041d17850030b040f0300e07551151b03029801b8550085440800c0c410150404182c481c11801c00081000503907000030291000c141c20b2a12980e0345007910403c1c0328040c2040400540c1c06012284030820b0710310204060362454200c18002800304000c001030900214202c0202c40d80544104210303c4a50344925503a08001c0016030003c1d89442088095034452903003070700034040b038400090005035181d0154103100100100c42d0a145c100700502800303480010403241100c00c00d500029072519280c004981110302c585c01000c8c54801d03c00703003a110381300c018001e11100c040070b5a502c04960342101440224003819151950002c0b1390005c000351080c2c49000c3c3c8980d40c00798900400d1082d01d075911401101c0b800d04654060f64000700c0d1140d071740c40d01032146a8016005a03210b50808109681c003d41d28103c0003002405104c018020130204540382810102815904100507110040f46034500b0034400e08a500f41e1240b00d101c88044640560120b40c0c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 321040809 1250 321039559 321039569
    0x80313050c1509040c050c030a0e091303080105060a021504060212130b0a0f020409020a02010f0b04140a0b0607062a0305070203040e04081b060f010906051f02010e0601170f07 77
    0x410700303011a903003c000091403451700709070500c142000f00c0744c1007407418002000b40004640f140c1c101c4005410a000c18050010b10006181c40706482040200f42c0015080f411a00116440361340d40c4a2900304a003091000064040c4e4140f591044c0000c01150740c001e04500d18000024203a00c0c0d0b00c230501000305820042d00036110f101c544000c1081203590b50170000f10340e039600c44c02500d0681e4a940040c102d9009024800042c2d54641d034880004a00d40500d07410104111424003a8100303502c00032203c0c4002402021307083e583c032211500395803105170680d4140d5400040801282002e18020510042c81010002c05d035030f00c5000a0907041d002e446060300070103480d4004c50030113050011410103000007138070980314990140035495032201e10201100c1000c072030001a04007400c0a9028071156401038005420003800e1003000d1081e52620b0302481e90700c40c8440021410821064000d0b030041080d081d060b44035010300c500110362202c61281e030341031441c405c208450b48055241c80290316030102e03004e6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 321042059 1250 321040809 321040849
    0x13060b0d03080c0d1d030414030102030601050922110406020f010e030d1e0509010606020d0504050603060915131a031504140304170616050313021c080313050c 70
    0x200c3d144200c410701906403080c00980001e03c01c9603000302c0d149291290410035503280c1c8002020b109442c0e090513580218030003500254114241640040c019000303003100c090207226003540d0080718280ca9460711459038254901002108c0360210500c425500c207000e504098465190b400c2e243da4014030810308000c0200d0091410602c0180141000d000301040010702800d06200c030341504540e6108403402344511700d00000f1800d00e4600080e042030b946a4040d002e204c0184404c0005803075581c1120352182040320464041d41d16a00002441800380743c000c2d81086240c2403030800b20000b588001800c0f05416442e112404010040590b950b021852070541e1000c4100132400180c0c010000304680c3d0038000c15a0300700b9032603801c000c0303c0c0d00100149401319407000007031001890b400d42d4075445401482c9005480c515291201c040f0107007035220000d0044030012900b0f030107030f440480561010303a44102c000b5500e00701554812350075102c4010944039401001a50251071806110106007000c076224 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 321043165 1106 321042059 321042061
    0x601060908150109051021020a050a0f030803071b030207050a0f060503061011120912070303081302060706060b0304030f05031021050613060b0d0308 66
    0x80040340682110444410031645100b01a040d148030103008107071600d940b41407001c040090390143d03c0100311540600c001c100510a80100b203070085440028864445040184a024500c1440d4140d40340c1e07041000042c525402455010b00c40d07082031300486d241c1c03065840c06560342110446c0180c1002c0d00a01043c501401d1030405003900e20802c146041c18103101030075a00c070292130107114440224070100c0d1ba81c410031140419031f60850980d900b11002000a0307149070410350501d031240341100c00302070404c24001820b03000c49802d070ba0350792180c0e114852a01e545804600c8241e80010741004200003240c00d83c0078140040c688170860315524901410001c020380c0e8a03101e80c3c0c0c10040200140010701d042c13400341000351107003030400c54649400420400d0038440b803500010320320700135401000700300c0b030324100c2c4440740901070f0105000c2e10b00710000f003018107417000c8401004210000 = true := by decide +kernel

theorem cover : BRFrame.Cov 320863309 321043165 := by
  have h0 := BRFrame.cov_init 320863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 320863309 ≤ n) (h2 : n < 321043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
