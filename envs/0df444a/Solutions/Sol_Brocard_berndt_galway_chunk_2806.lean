-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2806
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:05.899983+00:00
-- url     : https://prove2.me/submissions/15e2436f-1321-4963-bb45-2a66887cf91c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 504496402 ≤ n < 504676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 504497652 1250 504496402 504496423
    0x504150e120301090507110706030209190510230406110c03150606090303040f12150b0901050f12010c1220070f051504051b03010504260906030a090c050102 69
    0x107450a503880c080c3ca40016100151108040c4120700c2000b00440c2020b10544014040c9918050b9135003031090184100300850300f15841c06080100801d0043c0d60320700c41c07403c21214180c54070080c02c0031404445800d2480d17803065442c0c8440001000a0581d07040022520040b00c400299000925001305060b01c0e22030503501038a0b0b0032400000284280340c030350007800f5980d501904607420b05444a6018515a4107038021580703001c0894140020855000414100c3d96400c80092100e040c007240444d9000d80d06008051043c11085208801601c070044403500342064100240252650000054020b030141074000b6081410698200703510300c42d80d110101c10001d05071180d8603184041d100c006100049000444440c003a5610034002e800d00104044d0050340204003070020005288210003400743c1140c6090b0180c2d0500007000086035950300b0a4004458201c041d0045c000715041020046c8100d51903075900140220a0002d50788103a440005960f204030001b01803207844e68010f90ba41c106003030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 504498902 1250 504497652 504497683
    0x1a070c0504050c160b01170a0b0a020d14190f0e150c130303020705190503031e1303143007021504090c0f080603030901051305040504150e 61
    0x15040100d42055800154015000072099050818000070a069003042c1c49054511104000040c00244400310000740185403079401054001450341e146445590001c203900841b0380d01003100c5900172042c0c7c020f4080c080c8089210f800a161032001c005071061001010000685011407442c0700110501c01d0030840c400d08801416119921620a40d0310301e07006101013040301042c800c0010ba00c46400414001d54840d401510145046c00d040c0050684210b014104d090803070103041207181c602008903103408590001c100025072443c4030021544c82039807031060b40347d550400000144035007100c3d4026400c0e00c00c2c050f04c40f11050520f2100320f544103031840094035500c400c4001340403180c217801010154401341c42024510525035003c5140d82065000c01c44042d01c3e0009116410f074000500780340040c007810304085605042d008a9680c0c014040c0c00d0381800301c0000c3c504060b000c0307482c4007001000000d2091100e86064605207641107000241489102d0416203950303c0094003103807410020704c804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 504500152 1250 504498902 504498923
    0x40308071815083903060f0d260a0f0f030e0f010c030e061605130503010903080a0b0109031e260a141e0912010c08011e0308031501050409020406091a07 67
    0xc20380d5001c2c5c0c0c0040c10300e540c001d0464814000c2916182400c0300000c1c0076118000007840e90010040b461051160151404e080070043d5421a0360400002220b80c1102e103407410000c1c4801c00181c006200702003005030b044c4100e840e0050700e4101500300101c007511560701448171080c4209000d5540c181690040880b80c1d49840354006c2511405c050300c4001040903c0080650744d940120342103c20245050340041d82030402c001180c0814003600401107000c0ca03024154600d95211a6100c40150002504681d0410355007002e200401e90b00035000002c811a5030144c50b1405183c0070503600020049004c1582402c1b26001d52030888291480c1d58102c841500007445011600909940990106640b0040144652443c100244a4202d4044554a91036165414140740001604c000d2280f184100724886060000680e000140c6e1f0b0888540d040a080d41c105010060b2a5401290009036070a8804031f4005a040c2d44143d101c2d00b15014034110751400700d06164294524414440042e1280a40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 504501402 1250 504500152 504500251
    0x14030412050310031a061c02010e04050c07050f0a0606060f02030405040f090b0f180106060212070302070b030c0301030303050f090a260c011409010504030807181508 73
    0x10740c0155482018090000022604e9540c1e1442c4032000756010420401800704000560030100d000c071003c0c0c2c190741214070544000d90300081040540c510014095602c500114211000c610b003038440b01d907448419250904038801d00da40d560710700400151081c03814941d0024019014120700d00c0c51119036800b45183ca400d1605100240054110810036140d6070220840070800b861420b9000f034140700c800c1c041c1401d0503241c035041c0d8803c29000d504541d150101c204405a00010480302045440c4c0e220758580190b07003400d03418100130f5804015a0b000010030050450b40520045040e240b03e510100034035191119514004d2008450291069100c0300b06140030558a0b00554180480043c1c0200c0d49142c0082a4042c0d80007a88480110ba450740001c442601940004603030029101008000c545030a88000301001005020603041c0700e0420040d40211000300311003c0039000b485503a50b2034408407500148100b0003110b031104c0b540d952810401d003000075080b000844005050849098941 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 504502652 1250 504501402 504501407
    0x30803060d080a120b060307020d11070e16032003070c0c0906090b030111130e0c0c0a12021501030803070509121e07060c020307060f020307060609050714030412 71
    0x25046a611420041034400040c2940300103000c000844d9596403048803c1e41c64107410f95042e080030710701c1000144108188140c0c00905d64003480f119107040b1281c80d02451101d406c04070990860713141031580108006420030b01403001060b14005e075404000c00380c08100d0604180e1401c2c0032032000800100007188441d4030900342112218000e07100d5040b51540c41007084216000d540c482018280c451422902a107000c0c454080d2a1020440c0c062401903944849082241d0a0184d10300e0703180c5079004101d0524101d030a85030414182c004a4100c0b00d41c42c100110103110304003000c07005105224079481c10741400300c502030407683c3c007507034003400c5171030b41f200541d05900700781440c07500003260705d0b2030810000302001030005180da10b40c02c2100c6511512042401c14546810001c1480302035000362006803400156001184c61341d1400e540c3c00f42440c0340490131842012009000d01c1c2c00e140e03000c201030505500c07250061038a80c40f0030201d00c00c1102560260f000803180504208200b20000e048a030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 504503902 1250 504502652 504502657
    0x40b0117030702040f0b030d2015040822180b0f090705160503030103061b050309030a0507060b0d110906100509090403091205030306030c2209080d0c080f0c040509010308 75
    0x40c0820000720b1014840004649864803800f00c51001880c41507641040c40e27031058904915440c034801808207840c1381c50240341d68003806000140308070000298282c0200711b90031301aa4546d045010f450f126030f9507203810244640da104200a50520340008401185040c0d1003880300034030f010b040003200d41e40c0c0c20800d45d40d5070001622840080d4540390f180300005c005000945c007852080d1400070305a90b02140c12014030110352440828450700b0000c3c17004a140c00020f41d22041a14980103035683c2c61443d054020303024502c10030f9040740715004803104012a140320210801c1301945c1481c0c690303030345000b000191941e40c2e6425002c0766040007807028504000c141107500c20b000703081c92a9072655400752a00090380d4014159401c1e007004c41801803902e0140801b180318072084940c1d08840918200324582c030841010521101555640701d0020000c82c0001c2c1e8010301c407420030402900c4214600500b01c002c080760a0b0440c041485d0014104600c0441910280d401c0905050480d030f00f5543e4240065 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 504505152 1250 504503902 504503921
    0x905100309020d170d1d010c020703080429030930040323030c0f011107080a050309010b030f0a1511070308070507020a120218010614220806040b011703070204 70
    0x3510420007500c0c5081c1d24010718625266030003503401c1c03061a1b9555182114890f10360081190090501003006c0340c44001034030265503080c854101e04110b10711440701e03050150224116003281c0030003040101413001ca034151041c0321450794060340b240c81407c002c615013003012110140e2402030109002068440003c039803201503643c1c040781d030103600044007455a0014451003a00740d005100d41142c0390000e0040c0015050300140c000e0030411103503076154060040f040c0c4402000f0001c40060090182500300324402580501500d8406258564564803107004941c1174ac1e0b407692080303005910018900c154061034114401007814580c075940c040301c0314000500304c142041020701424001d03036103442c00d0100801110b054506984110710501200d0a40c05911400d8010280d00402110b03400c10080c0012030f0710354000701c1d96400c4810078402c0900e40341400302d0f0105107181c008154281e001070810b024a00400c24142d050380d1380e0383c002c1d00da00c0115403101090327003081c00424018103054103c0c8005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 504506402 1250 504505152 504505193
    0x314011a090d0203010504080405130b0f0409030e10110c030331090e0c04050a022a030d0203010b181e0603060406030f030c030e031506130608030a0905100309020d 72
    0x101074843c1c00007400c0d540107540507a5840b0300000c1c100682d02d48202500082200201c05125010700a030025030074161050003540660340b1030422070201807248198001d881e0f00202a84404008000018000e0302c89414016407807052403526400b0746400030558800320007902d00b40207a0014501032411b49036800d240815800c055050108004443e8000c01c00003500910060101c0c0407440100000d0b12806001201261720422182d0042e40d4000c18403c0000001c2006504188807041c03410325510406c022008000d00c080000714440d84880010a0103000c0d48081c041004000003c22506400846a110404c01342d409480c10030306184010f542d010300000c20010380140d80b500c1d4009110b40c0001c0c101c0005a41c0d0040804140c1c201e14040c80072141500140048070302901545030480d0b000e0190b81c49040c0000d08000f0100981d0811400340c110041a01d4607903401d02d034003500d20881409a98460043d81050b14000c2d8880e10480c01070707a80040010381520850b4480391940304810320114407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 504507652 1250 504506402 504506419
    0x150e0a02070c050901080d0e010f050304020d0312020706051005030c13200a051e0c0a0b0c0f07050d0e0409080f090112230a0b030a231504030314011a09 67
    0x41c80e6030780c1d440e180e0080c140100501456603080e040200b080440910313235818031035400140f00445da884415a5405a41510401a07441540c14142c0300c01c11401d001c1d200041c00042c0050820049410030380c043c40a404c014005a0340b03a4041640702c40001e181150020202202540101c44682007072540d41e484105e0003070134400c0d5030000e5003e5800f4102d00e00115100060b00c444010100d0000b045c1000714010142c1000c03030784c0703800644500c14042c0140500150001084007002c000c0112948071a202ca0300c01c2e6581c1c002c5ca411519590001088804603800581c41c0c505424680109009164041140c5c0d25289140c03a81082d00e40200d04190304111140711800078909192088501c40d10382c12030710b0410104841120303d09040e000b0035041c07503141172101417149a2000150f03101895403001a0411220b50000c0c0d0303801c0070301d07800340c0100144100900060504801d5003124003031406580d00b4041c030500703040c081c03508041c00c2c443c500d11840d0b842c44403021000060003500f41400028030395031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 504508902 1250 504507652 504507659
    0x50c04092f190e060109030c051504050d140708060421020c03150a0b011d220603120311070c05010f0504030b0f060f01093203010f0f150e0a02070c 65
    0xd011000d00200e11008050014080c4040d000680f0042d50161003440d02d11940e5013141e5038505942c12600c41d1034000c0d8601d0841c1403500304503200b40c50162801405405050800d401d240324004101013551145001e02040403508400100b42135124a40040c51251414049401194036405050180c170071070151820807210350781c05000c501e0000f01c0d41e80004005041c6640324004660a600016040c031801844640c0856654100080e4201d412543c00c0d070001140500006405800744021500ca0304d001804001c001d00c1d00300c0b50101c01040c4c2c0c1e08210000c10080b42032018820f0510141c2219000307a0100300d158820034255489045502e044c0b03050030340d65603800c0841c0d140bd42c0d2200b8207200386804c0010341e0812440f8100802401d10385202007d14016007201d101c00754080001056601041c03940e00c002c401c40d85002d0b000c02c080e0013001500e44031602100144038008000035010300b0029042c40122010b1869415614103120080080d16000010030080d03018040c03c0795010012140003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 504510152 1250 504508902 504508909
    0x91b0d140109032d0804120c0510021c0501030b0a0f0e1e0d090e0a1a0a060c06050c090a140f0d0308040b07090e0103110d05030a0c050c04092f 63
    0x1035090301d03c01e807242c1d40c9041d00121680041c0d1079422100114902001480194540c010b445903001034004083c05d901034410f02c0101c07641031401030081d103240300e040051101d1000a50003410070f070400d90170108034182d00040100544100381f2024002c1420303940400c3c4520116880001100d0308008001110807090005904183d04bc1488007016958201d035207107610014440d00207481050719050540604040354251518406015036400c0c9990350b5021240c5a80b5860720303da110790003040454007a0340d45100900f08107540300125105420800450604450380d020340e4580e52008000c3d61100e428005000000201004034541c000c29181e102802e41e2112038840d0f80c2907010380e81d048a20302c1d00e400c121115000140c4410104002c10004000c80b58240401d141900c0e4060f45060b0342600220005540100b4108003a005002c000340e25030750180c2080c0c0b980400d40c818400e0350b1601410741d0410046810251000e4040052010024103c121603a00c102031100e1149801c101000c02c600031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 504511402 1250 504510152 504510161
    0x5030a0b041518020a0804031b061b02010c030e07050f01030908030405030705150114130f1104050a060203030105090109020304020303130608071e09090e1213060305091b0d1401 78
    0x500075070002e0304414050341d01400105000d000107140c09520342000c0c072a0080034400c00504c05020012000303c540b45826207616030a181caa04400c05001801061300014074071048840c03440007540ca450f1360008140d001c2d024603c20b0221400280c0000c51401091004d44001128510704066a88146000082c9030501540c000d40c00344004580302c9400f494214649079210f00c02010385203241c4010088410421030b52407016109460080c007101280c0c1080d406448500041e000007418441504601c2c0e180320050300032a141100c09040d1a41c0e250b030107a03202d10082c0104c5401c100d400340144034800c1c00f80c00071600648094120791800c80944c0d111020100e15400100c0010001c00605c000c4961090307414072140c0ea0720204080702480c01074082c0c06140c4074481c0b48401611102c000101280600c2201c81844030410040d07981d0100b074500803408150790242101092800c0301242000c000080c515044451442c1943c44c148424800c0289440724654100c5d1440c0d02c080c000102a04203014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 504512652 1250 504511402 504511421
    0xa1e0803070602030601081e070309081b0f070609210809090403020c01120509030712031d0c030f06060a091802180603011b0f0c0f080a020f070602120a05030a0b04 72
    0xb0040e00c0e410000001004032801800b020b000002610240d81d141e045072070364a4000c01e20b401d00255054462800304054000c07801000e6585003007a2240c40c0c07032540403030150b0b03030629603000fa901c0c041e8035007106850483d4a03001d4003c000b0b40450b08010302d000c100403041c00c40340c0128011400c140c1044000307451554120380440c0160030003450f036161942c021007242c428800309502849035183c0400c8283ea2801408006066030340d00c0d4441c280340f24000c3d4880c0c00700352041050080c141c4517001030a0b6841101100c034600a11600c044035030300040101c1d0281c00350380010b0004074414a41011074010700403002a10400c42030007102140141c0e40d00840045c0c4803100361140b107481c50900c0400d0708480304004442440360b509101b0600255010b03a41f0049404641010500e6180c0e03402d00e994041143da000900c034410001e00e5521841d0002801028403018200b00c541032515080102c0e04d89104c0341d400f01c10f20b2014090155002c2c01800610303070205010f0740c00900d004040f000070301554404071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 504513902 1250 504512652 504512663
    0x40501061808210901090b030a020702210c090408132c010501051b160b03090f120f31061218060b03030715020a1d0a1e080307 56
    0x79400c0000c00c0c2018500080010070041c103404403000c1400518100c021040308020100010030a5803030b0700900c0d121001d000e40364006501ca140c0559140000c1d400000709910507000d80810009500001c00444007038070240000c1d0908001c41c00602980302d2014100b01d65580d01808144509e15400b01d02c08010004400d00160390340d4099080d1100905c00d2032030409500342c890041c400769070418200c030160f80e840d9048a0310781c1c80380341d200d505004000a03041c030a403031804000501141e1070380285001c0c20300d05050301c1c1000e04000f88242c0c1d500c0c243d070043c903881c3e505220000c040480c05010380443c0740265071600000309150079400341340c0d80c0b2001d00007100d660280306200c11a80138561545150004404004610760818200140c4054080c024290794503404520f1440c1c8042c02554802940400080341c8158403401c030401031b4200140250000d6003040c1c45403480d244800c0b907068034800c0581902c10103400c00101c490002c540c1100c009105105100000340c004040008020309401032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 504515152 1250 504513902 504513917
    0x140616051c08010b0c060c0904150311190e0c07020609032e020408060a090204091b090f14040b071e0315050a050a060507032006060406060f091e0504050106 69
    0x108060309600d010780060302d0000060002d0400c030305d800184180c104200f50b044940b103000c1c001c001130141c820491000c0e65540f001d0000010440314003017000e4840300813165103400c0e504000c10f051148641d445260301a17009000800c0c101549140240413160028011503e07110505020070f281ca60100031400c0c0c450f0a1001c0c00e68510f1108400101040f00c0c610154a818a003940c566614900500121019580c030b605500031503441d43d10030340c441548079070707040f0b80d0007070b48200c10383d01c0011841580780003800c07d240c000c90003116100d510170003180b4441c171000c90b4941e900c4040300c101c80105003005001482200103059a410342110090032425940851781d20268200903010b050303c0e5111301d014043d2240c05001903543c032004542500c0e0585030040d1a00840e080458040c2c01400342484102c200500c8242c21036004030382280310307041c2514148172141d5640011203244c0e10021003a4000380408038144888080381c00c55090341a01c2e24404000070f0b8581001808440c002c1e48841c0104580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 504516402 1250 504515152 504515203
    0x40609060c02100e1c0521090607090f060c031107050603130c15090e090304050a14011e1407030c120c1e08030c0904150305010501060201060f14061605 67
    0xb80201207001162034058512003160b4141030483c0030000340e210086c00004204580d580c0703411106550100c3c0501c0414441c0d003440c3c404140c40305402e440711000030340b0000c2c0100b4554180454901203074015950605402480d4504445101385d9544107000384c000c0300400030f803990304c5202841c040d41c3c0c2e00220240007240e6103844052224036502c9080e5200010b55601140f641041c9240115180032a8032a295076600c82c00604600c190341005038014030b40700c004074061508214213a01d1080a80b07443c502a6041c1301000ba054081a45100c0066072010318803d006440802414425100742080b00c001d01c007560b43e01048070178404001c0c00107054113051a00f8845807010120010520f1300004644501039200c41159106c028041181030034002007240842e199640b2040b4145050700300315052544074601039001c0c1a0038445c510040d030800c0d40118060303035030340e1100d001c8480d5000c501c0540740c010400e0001a8000740d5840f031155001840c0d640c003060091185003d00340221002300c808055 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 504517652 1250 504516402 504516433
    0x81b0c071e090e070e1801240918020103020903010b060d090b1035030a020a0309090c1b0503091306180513030c08041203030501140607020303040608040609060c02 72
    0x10316602c0500c003a401c1500005401c000480c120303040c2c917900000100c0c0c0c3c2e607980060031902c451046505001358a08071034000712086c8554550000e00d80e51030360402c1d0035507400441054605c6404840e01d40b124044040e401907010358010800028090008154120700b01d00180982d001202092001912901e42d2002c1250145800340d1080388a030008035640e0800540312980081c0c101109460740351018240328400b4a2040c94110843c22403c1340d0f9280000c2600940b5260750400031000300380380000210b0103038901d0240080790b2045030750714849100410800521101c07000826031340350104008114854846a00405007000d450401186403441d200d4000080c58405907090a00b40c40c0009000c401064081c1c0703000080d8151814584c8400c640c1800f000500c299030203407905141030483c8408040d01034124078101d522130948810520005400e0050b141304101000394541c0007000284070041c002e242d11070f0402e0003150001400c3e41d003035680c3d00032150319968450241c5d0104010800091 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 504518902 1250 504517652 504517709
    0xe190c0f0803070c1e180207020a080c041b0e0919150e07020c0a170f0f0d020715051b01020409140f060d0c09110d05040c0305060106030507081b0c07 66
    0x40780e4060812080d100c5d8584050300c403018050030000742d4840c0e2a80c4c101c6141501541c603d2070b001082c1100c036540e141802e43c0c0d20300c0301c0ea203e40d00031070070001251040010701048a498440507150f40789402c044508100300c03040c00030001d00e1400380c5028a40c0e200e905503c10000708100510740005958140b2001c100c1e043d20052010341154450f5880b0700c50741e1100c83c012011581003004036403c101c101d80040303092010102002e8800e10603225410210500003c007421600815003d07642115200e0307a40f0785240c00140108000710301c0420441c64004072954108182d1100d9100050074152580c1c0f242e01a6008013407546880078084050150060902d4012034102600f00c0e0b408030800d0175650f80c018410714a01c01d050200d680c40524914564085003250728100100108001d180f030145080b41c100d007082d01003500c42c4e218980010960341d001c0c0c07041c039014030166103032107007260744504c4042c064011a9800f0302150310188403402d101141008614050921590000740c0c05100065141c48072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 504520152 1250 504518902 504518909
    0x50d060303090501080906070f2105151e0d0803071b06050f070c02030d080907030204060b040806060d0506061903050d080714120609100506070f150e190c0f0803070c 73
    0xd40201c020f004d4010f4000820b00111f03c078030b0400ac032070018010821069103050410130070500e41030004000182040320924401e90504403200c42441814051031004040d0f0700760860307040800d0103252001b180108010b1a03019041d450a283c03005685a0b80070340d040c450f140b08690300e40c0c171501401000041d03a0000750744502d40b468030448880c0c1130780000703944d11004001c413000e0014200100710706010902400307000c2c41d0043c0041c052943e40710003aa10561040c4940c468902841000c59014540740c280c210310a500070006054a844035070420501400100d011070804560f50340000c001102402601c0d01c442d00c079214540503242a400244c541c2085000110740d10070200040b041800c42d4003059500044240c13214401c0307988400101140042a030030141e07200744040f4005c000c00205c02c0800c0842403050900000c82070f0020030301c0050324652803005030305410034203052140425250050841c00c1c02007883e103041176600c030800300c8505201e0f0000a100e4000166000502c50440d8480004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 504521402 1250 504520152 504520171
    0x19030f080a05160c0611180a08011103150a09050a020a0e0306071d0301020c0a080403061401051503130b01060c05071a030711010605100c1103011a10050d06030309050108 75
    0x141e240400000c00d43c00521400b000922102600c1c40c4248001e1358080c0d540b00c00100e0f8415900c407440c103808113001d44010b07000b503c00c501c85d41d400b20f25514180511040c81035101051815511420a030000440320302c82c21b950092000003002508442034000c035401090344c1e49005135608602d68000301500c42441d01c040c000e91100040c0540142e10405ca5404071950b1301d4441c0c1c455904034002806842480034505091250100743d80a00c0b045070300034400c03644248801c0015444802e80d1000c01b800901c10b19510955449003032940180800c01542d100d00442d20301c0003510b00e551358450318488281c110100103134ac500940c0e0201302d410002400a0250100e03c03800408240d44689040c1c4801403101040020100b09090340240c02d411001c0549002400300703a058802e420000c007881d02d400004c1c0c0d584241702c01440380c5800e06104a1200d680824000d500f510300000c00d100303103008103800800c100304c810885445170b18154482c03200918440d43c1c03190540c0c0d01e000700041030310392302070100b218 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 504522652 1250 504521402 504521411
    0x12090601061b0311121b01060302011b03020a06050108030c010b0303091f2c131a010302091519140412030f050c19020a27050919030f080a 61
    0x8120b400181005881103914800c10681203189011104122410b1a0040a20800042e0004011000050200e041c581c0410071100310f207180d800c1342a184039202c0640801c1070700c2105001c450015420081c0d140c0a40111790b400382c1d56a9808c021250242d210b1444e94001140441c0c10b940d0a0103407540070386040300110300b4103051100145180c00804004500420310607421040c0c80e0117101c0907072440035a0f60b0700c004088111500301f99041d8915400c94400d6005540505071440c10b0310a102620101550b01e804907018800154001c3d07201100c46a800340014604480300076540700202511464007841d2008281c40007800b8007960b454180070b2032680c000f408148000e004541050003800c1e010300c0c003008103c0d0601016a4a03100340100700d8090f0140d01e14181148107aa00c4800e0183d209071420f005099032005200c14004006d4943c0e184112240c481402e001081d030040d54100c1400d00940d01c402441500e054030700d4007180d1048002c5600e44e40020103039504802c0840e8800d07001401400b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 504523902 1250 504522652 504522659
    0x6030603150b010207080d09090c1b14250306050105150a05161a060a090507050a0c060b030129060901090306020703030609050c1209010b0d0807050f07090212090601 73
    0x100c08110a101c00100325a9a940c1415244e208100354001407520801342c0391010030900e001400c026050240c0d0000c0b40c20040395070780380c3c0c1c80341ca074108103ca00034800e44590147c56903802c00b40117040e4850442449007141d003e85036440700c040da13503004404103a80c40700e40e803031442c3c0501940c0d01640000d01c02e0301040410400e03d914803003280c80040f1689440c80c3d03a403055410788500c11801d0280588074540c140c4006007600704d0500070300d0041404072034040c01e440d52403040b9403d8840450346640060414072a040e902c0e801100f076280c4c00c91051201040150300440070a085412110b400c072000c180c01583c68890542013021000300b011709032001c0b440c103400d0000203404810319120081c95143c0c000740c40b1061604c240d010b40d0203040900d00910807800c240c440001d1075000304508114101c0100042024140148074208400e00058140c0ca158082615041b9107500000010b45441c0551040c95040030740078042c3c0c501404c2040c0340180ca46071903901803a0407080007040d410305c6070b000d1340062 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 504525152 1250 504523902 504523913
    0x11e02071e06060902031509090c0102030426160e0a0209010504030f08120a1a0a080d0c0320031305030f0c04230c070b10121709031b03010606030603 66
    0x92a01c007040000c0499001840c580480104026400141c0b02440407061110301201c01003143c0b4a548100c803e40a140c0306c0006040e16126510406400f5a00401c400c001c0d03005118098000c1209061503002c3d541c102000c052706011448049045d074800811040c0003080440c0742c03032900810017440845c00d15030f050001a2051084d40005080c00b600303143c00104000e50201280d100c0031100d004a945801c000c4454409000c072041100728201e40d040c6d00f0061402e20300c01075001c0324030b80b03402429442580c0e0000d03901103a52410035801c0000300324001203195412040240350401c101c0c0115610f544004a1500701802904042d01c640c100000000c0803420001e042d00c040102110009107801081e1001c65000301c0b030b1031000348500e0142e0100a100c1500740d0141c07030340600504050500d40d8540c1c0840008a003280039404d101e44a6807070820101d6060360b20106a0300f980718000e4076045130000000e1070030303a8880da203060005410203072145030301702030041000512480c00d05210103030841e601d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 504526402 1250 504525152 504525173
    0x18091f06180306021b100b0a0302060a030e1507020c012d120e030702150702010c060c05040e010b0901090602032a160b130b040b090d020a03020909011e0207 69
    0x400c410400c024003404560303a0460180c000569101c102195502d5204190707094506a41d50520654010500d42e002408444d0040049580b0000c0000c4c040701d0941d030811425030030461102c01056602c84681c2c9000798200271400c0c1c8031600d88072124451600c0500240f41c81c41c2030803030a041007242041720380c0ca40c0c00c0c580da182e8480c04484968290303003403d001c101e902040c41050140041e04001400b0401d200200080c0743c0c0e80d000343c1c1c441c40d41583c208490b0b007151107a100c0003070014500d60100000700e00260b1054090300030300c1ca04a85015034658031212494070a03000400072480c00503142d22250b0b0040903440080c0318900145003005208050109594850000b00010280c074804000000c042401824201e00f4079981c40700c091074a4034508000c0342c000c40c0c100d480c1e8440c580780c0800c11120203001e0350300700c0740800c01310b40c58a1840c0050001000e5840422a01301307010700000310050365034281862203102c41c4000000c06002081e00c50740c00030600e1b07145408a5104004800200c1c03a44250b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 504527652 1250 504526402 504526409
    0xd050a0605091b0906010c052401080f070b0f0702100809010f1415130507020106230a0513020d11030618011d0438010902131a07060218091f 62
    0x12a01003541d194401030f6210300390100018428000c10222151940309d0f000c080c00618818010102d90f6038840c0c0c2002d40d2880820612007882e8010075013000307400e0041001300504070100707150360705003146d990200d4200c400589108020603842c0b4104400e901d000d100700b03d0a2558901d061240750100e03070342003001990181905d18400700442d0422056202c2110740071030910313030f104208040e10380b03030100900801c9680540800c416000c04003100316034021740740e540344460080c400c0111034070b0b007020840e8040100c5440760a0310340a10441030310006500c110980d00c070b4035000150b80ca140034400c20104884145101c0203a407040c3c8014001440340b1b0910070f08500c900c40c00b00381c641d1621705000e42c90410500c09100c8020b0344c80d81a100320a0400041c803000d044068140c00301e41d0b01c078803021003070340904100315901c000d400078100025001a5500c404405400320003030725042964590005aa018020140c182208048800706a040854482c1d601030900b88400802030017425040f041c00540c0e21 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 504528902 1250 504527652 504527659
    0x31c090b161b050601061404180f0e0f21040b030c07020301090c06020a05010c0e03030901030f110a0504030b0117030f0723061501090501200109020d050a0605091b 72
    0xc1c120032101d01074154403491842031034449030310100c01d1800940d6a1801d004140c0003c1606641107024017100d402d90341550550b00411001c0c003440800b0400030545240034140098a81d00741404162050000c002d2890b1603801800858944e181800c00c0f000102c00e10100100b020001080303500314000540760496044030619564003c00d000083c0900703500c05021307211024092000501640014100c1d01c2d052280000344150541d00b902680c240d007495403c1600f68000700505181c0d90b100781d0000303454903441c040002d004141e05140d4000c903040000802c01003400041c051050004d4040c103280101940203845000802d940038040d22070003a401f1120421034007103100001c01814841240c68200701b004030054411850548a55405051b584811204010413020180394815200d800c10345c0c50607107401f154122220a1460f801103403403c00c031407035541c0b2002c2c840143d85540310030002c14062002130800036001d041810032143c0140c00b5250320b500c01c4041d0086840d1180e405c1884c103e044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 504530152 1250 504528902 504528931
    0x1207083402041a0406060801060807080708150a0b04080d11010608280611031807030308070c0302100c0e01090803040501080a11160615050102070b0301090209030a080c031c090b 78
    0x2000401d22244181258414117150300429900e41c00f50300b4604803003996450f901503403110801034a1b480c2c002d46101d0001180c0800241e180c0700a031000d11300208011b4000424540d94084040742c541054000c80602c1e04841030f000141c6900502201c46500080003c01501e0305c1c00c00132aa940742820b40301a4001d4004d9940c0c0c1220700c906100c404403a40000c4144054100350740c1d4841140d000b02d4842820600801c0b05030841b0b603001070fa00c3c05495140c2c0303d0034000d8880200c00d071980030702072404404501c40c6091112204003140140f4041740d800b41c441c6098803900754005040c00b0a1500020510350003030108102e6603034840c8007150000c102d060700051841d500c0035059014410001e00406881c41002460304001140e80032002c079840d02032171002c0c4151120700480e00e038100da10031207848040500042c806541d19900a0074140002800c544d40004240c0c1c51180b190800310350387c002c941021496000b4840750010341a450607400380c04000c0c0c40c0b441ea4610031005006007040c1d030f521101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 504531402 1250 504530152 504530171
    0x30906010608041b140411160b09101503020901170309010e0a271802060306040e1606030606020d030603053403061a010206090307060e120708340204 66
    0x30b0740e20001d01403040311301e510742c82e0f250702e441e0f14907075000140180100d10784800620458038042c03e5440342d401c0902d18038122602503c40c0381800901402800041c05074211805210700c862040d0030030040794600f030058580c03842c0100f109000059003d21510014150b0074000d420303000c021074480341404d0902480503611040403417105602600850020184040d041c0d00b00510f0300080b821076981c401b400e100c481c8a83e64011440c0245507402074004800303201056042c81c4c142c203c0c8030b000c082801180e51802d0651b807100800b403200c2d071081c40483d959175001d0225603414001c80403190321604091104503d595900c55031403090080381c58a0848804240c9901ca0f0f89403d819031404c0580200c60030345440f410300c000100342e58501c07401e4420f5040c806000550011030458401c4a040000e0b50407c00a83c5910024220754401d1944070f004000300c808494007010040c10400f4010124541c07035074071a14840d0192074144065141486140c1c4900c0406480329050000c82c60307056038041142040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 504532652 1250 504531402 504531413
    0x1501210603080406050304050d050c210f0a080a0c0c0b06010507061e0e01050603010c05030f0a020c030703030902040c081014131a0306240d080c0601061107080303090601060804 78
    0x403508024041540043c00003142603201020b0360046000c1c009940030742c807007a40b050307030309220307480000146800201300750240e400301c1c1d0104400d03d080002d03030a140c28564083c01640e07512a56064010640301c1080c807010b504540304a1030310b5039050601094146458850601400c002418a030401000244000c1082010340195130034544041d03070a40410784042c1003101400150a09002030340c45c10b40001c3d40c03440e05004080401c800c584070145183c5854104500c40c2c000140f07801505da4007001403000f0300c2010001001c0860203075500041c2c1400a00c10401036603c42c0d00300204003d42c2c602070101214000e11401c0458002e00c454844541941d408603d0a1014054040d0383e1480c01d00000c1c1c0f142c0c091241951140022410b0307680686e94030b4003149554038013410781d0b070b207007440c404241c400c40c00c0c178880000c80c0c180187c2806081200c0d110102d4504a404d800150001c0d0440e450b02c0d44907d02004040050b1500c8005142140303001003007280d550205200c0c000c10803c01c880805c0c103125 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 504533902 1250 504532652 504532661
    0x10509060a020a0c0203011e0c0302091e0612010f050406080f0c010503061c12090b030408070f02040906050a0b121b041505090c04060e0a051e0103020927150121 71
    0x545c003078020b011442481c00708403100301040700b00c03000c4c85040141e0300720203d00c40d108a4004400041c145a11034402c081c104121440f41800700750011010804203489140d1009600c1c000c01801d00fa4160044c1040706000c1522410f50182c50550700c80341100095040105488080440c00e1800a440303a0b00c0800080301c020003d0710003526082c41c4401002445140690004404400d4071040845641d940451440f84800c58010f04215000c0c044030000401c89441c0510305800104041901c1085031a858100c40d0142c0700e00c00100d03540c1c8170f0701c4080d007810112460391050380006880844144200c000100d542180d045101e1561403e061102740c0b42c4458180241401602c0c40030645400b494201441d4003601444000c1130007030b00c00b100c040c0382000c1ca0b03800f5540d01800c9469140d920a90310b12a0003001d400071410301d50248100030386511015040502c0031048846403c03402280d46840740319500107040e0400c0d2a002c940c05100c9a44c2203140039011b80480c82050a008044110680003030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 504535152 1250 504533902 504533927
    0xa0204233c1c050309090f0f131b08030a090918080705030f0f030a06050d0f0b060f150703031112070804050a0b07030e240a0e0708030d1409010509060a020a 69
    0x2042c0703920032000380440040545179100013a103440e070b1240c6840020751310100080f9210a20340c0d0300c200003e11a24982940320451174030884909841c0c1c80c0040b0390b004060140c1d04102c6140d40045030340445035500c0202040204203030030081002c000c50540300b007402100ea02002c0e16a1100081540c1008420821200c503100d81c00c41540d2100d00c070403508009030340183c40c200b102c0342c200507000c44c1619041751451000c95100321982103a1110340d440c600c401e81c00402e52640402d004980403039503164092114842d42290480179501c014610b030180880307000d003001d800600c030709004e070903039000c2480b40c1c050700404030741040003c1e5615450814600404264000c00100c02032040c0455540c0607001107812903411016644e036040448c1c0e0900d202d00b090541c0021181d18840031400701c4041d41d002c02000c0010720107644c0c49a40f03c2010320324584c05080c0d41c400307040d96040746881000000b922150043c82d040004d100130b0801800d11030b626840905a803800640c0000c040314500c2c001c3c2072803401e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 504536402 1250 504535152 504535189
    0xf0e0915030c0402030f06090a0c0c03030b041b0908010f0504120806060f07080310121109070504080f1b15031b070210020106031103240a0204233c 65
    0x100d140140511590100560312580a225400c01091684002d40a2b10400200d240c2e02c0004c001e10381c0c2c404802030300c42140400d401c29510441114083c2d82d10080f14100b011548a035140b461500c0f60050855803501c14201d0b0a918140c1880006030fa100741070003030600b140c50885540d45608000981900c01c142c0d2140d1041c2001506030200252600a54031a0b01964a20085583c2da18852200325418941c010a0030041019068091425004840d0070542d6458145d0a003500e8a01c0f0328035064450742807004a510107011450f14500e4050544219503003501e030083c003000000310803003c41c00040e0a5140300480003c8100700003615000355280740b900145031031080c0304034a6001e03000300060300040e50403100301400030320f1a0400281034000701d81410b688030703802c466030505140c11840240107240540e4081000003840f0105d603e0072008441407206442c5460802820015003038141035041e403284e48002020507002c10481031841c001030441845a5a604035140090b01905504030403140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 504537652 1250 504536402 504536407
    0x3010306050a060b0d091110170a0204080d05070204200a031e06090e0601060905100e03010b060c161e2114010c11010207081603030216030c030f0e0915030c0402 71
    0x701c00300d070741040c42540d02441c82c587c81125203009001d440030000c006000480c030719034040390310540f1310310040e9405000c0c40070041c1041e80302c500d414107110ba0a0703031000002d0400300e840b80075490300d4841c030250f15080342c01c1c080340c401135000da219140c042c0c0e0900340c00b030650325100380c900d40361228900304804410f80810420540c6074003200e4010301c0c0c1c540403001d40d07124074000811240d005030901c005441e4014101d44051071000030841e11014031691054155407120321010303158403004080d0500c503070080007030209401f0030a18030740c4c1d51003140c0c48911000015191502941c004680150a45401e9041c9071400080c14400415003e14031800074400c00304925110717404201075202c0d00101c0d215550b24a0714500b10780c050760a038041c400028140c031304100b00800c103130304050300301f0701405110341000340c00d12280400500c4142c0342ca540642c0072805404803e000c1541c09a25071511040750304050000300b00751004a00100b80c02480c040000d00507103100d00207564104800030076040300500556 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 504538902 1250 504537652 504537667
    0xd0f05030310090b0906010e0f0301060b0d0605031510060311120f0901060902040506040e0711070e1909170c03040e0a1a010f0e0108060f212103010306050a060b 71
    0x5000070842d00c50050f15500c0d012011086182c0950300300e0181e02c05a5460301202103440400405140303460a003030345503680300c40028601a13180c01911413441c0d141000180c0505d094103050400d40c0f03d0307a8913081c100503901008600c80d52981440280c0310240fa00040c41400c424a5080b54880e032100c0380180056003003004410000b48000c241311700914002805000d0b51000d1202c02e034003071401aa03034060001d01060204052100c0c1c41980700103180741c402030491a43c054103041c10300307d4010b400306090b000c040100381d036012492001065a03d8604000014441e1100b02c250000001803500e010800900740710080410400d03a0041c09482400c0c607001d08081410341c1c01882c000c4041107126184683d0584191b00490700203080c0c01d05500c5440c242f82c00203004542c0c041c4018111540042c0d001607400315525000303002410030501c02c10901860400141051030000c0084076815001141142080040d1050091381c0c11681d002102050b103480b034402401c0a816a0b411143c0c241c000400c030749 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 504540152 1250 504538902 504538921
    0xf0204080106180e0d1e2007032315090a080d0902041d2e0c08011d0c0414061b0123010807060804061404230606100c03091509030203100b030c0d0f050303 68
    0x42084900c5003002b51449440c042040d65150403210a116042d00103840044d03a07000c2d2072110a6102521704180ca9100e4050703511108141c100c50f800c100c0b5107030381d401c400c0d045060a01c280443c000107031048040d41104030050641d145002c14080d908071100d20200c1c501d10310751a40c0c81030700c90103035803061081450380c810041c240301091048445c10142500948049144803d485002e540c1d044401841c3c40d040400170801c002c0150034480d04000e0420410380c51414028204c41008512000454400c58801e000c403950301074202e02180b00082c41e0010018020b000850307404030b85450070806159a240d06114000300f52000b602c40c2c4c1c010034101040200402c00101c10040500e0301070550380000c155000941c1c840045070604d4201015903c2001c82ea4060144d0340e22841c03003864450389180e141d0420a4660013200a1080800c00310a801c0c070031440d060206000790307500b00800b000b2100e02a070001e03a07940a0a083c05000340d8046101200b88901101d11008103900802201c1e56428150402d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 504541402 1250 504540152 504540163
    0x412060f050109022502060406180803070605180d08131509061b09031a041b0605190507020319050a0515040209010509040203060a0f0204080106180e0d1e20 69
    0x1a40240c1549402107003c011172103100008660003900da0f070f05080c1000e5081e01d11002c955074050289214940000c0c1d00c030b00030801080740e50710a0001080038101203001400140316000240403981103000081c0505900407500c1c1c2d401a244107615407000418145030b104285451003515055003011005001c0c03040c990400100d6080f4200392500b8038005140480d842d0115000003400304d90304180b4a10f865000365103054005024065008258400c0410100ea141c1503501144c08102c021803990781040800c82000380c01400c03413b10501d8244031b680040d0b2902d10342003150000d911695a80824020100980d1800700d0740700080310100d458003c846116103204032801c82c49000c0031000442e00f4100402c0441c000c0c1d6018009012a4075484255030150030726080110445901340030006001c2424083c540c000c1132116401c510309881814840140c4aa40c240010b150f48000c806c059561751246a140081d055492050783c3c0c0c2010039412180d4480514881800c60701c86485400f04002c04180d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 504542652 1250 504541402 504541417
    0xe030d05091e0a12030e0102070b0906012c07050f070f0c050f0d0201030b06090307030305120903090d12090b070813061b020d020d0c08060106030e01110412060f05010902 75
    0x12a00d1802c003000d4819a4506880701038015900701c41203142c0090001da003000300701502802c012a425988442980c03c90b006241c1c01c1d02d0b8012600244180c890301130041ea80074100101414040c0d9001e40e580c044401c150086d240283c1d07501e50001100340b4030410036100c42c3c1c10204d0410341c0e01c8207582015041d50300e08d010251000280c203000010246031a040c0c2d49200300700940200c8122040f0303001540240318034140030341c001104014001d0107036000d1181c5130145120340c907000d80741c2c41c40707900c041c00d602c1c40100560303c15130003040500900d45c1e070141c064180d0340d4040d810304030041801100700c0b01903980340e000c007110f40d030042441804c01030810040c2082440180241c0c02031f40d43d4810850382c0120381b080d410030b031101441c00c130005401e004080700751940c0094100480707105c0aa50319100c02c82c0650043c031084e0490750043c020164940182031040c2c00d80c41c020b0001e40180701d0020f5641c402c501c074511078424442200400c02a0a070010f03080781d0043c0404000d03e40c1e65095001c0603622005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 504543902 1250 504542652 504542671
    0x10510090b030c0a05130603050f1e0304061e02030f13092406030e0c090a09150b18180a0302030d0b04060e0103060506120a0c030606060825030e030d05 67
    0x8400000d10b0800103140743c85450010450a0003074a80814490b0340026084d450340e0031078403201d0201c041581004500c400404990003420b15442d1030592100034084004403c0c4070b80c008010410034a80e03c41929034910301070f0151408106540c09041c1d266100c0e0300e2403032a0b52100810000000031001c00080c0032100c000300180303d5102003000300800daa9000350f8241107400d5180b02840440c3c0710390312809400901400b00c600034084800015040d00e000c0315243c0c862034440d8445020445d4a03800c8020005080c00c0c1401a4100d600015a041c900e051080d1040c900600002d41c1030010984400c0d40320020409540d00c40445040003900ca51149030001312240c203140c010425030902c0d21591084410340412000e55900710313a2408040e000151500381e22410060b00c1505443d0180300155404d8410b210360410b207841c5107041800e45015501507018050910f0410031101081d0003140d081d03070780a401030081130b401c40000340c6c002d013034605182c8004e1001050305241a0042e40c40b640c003800011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 504545152 1250 504543902 504543911
    0x10c030b121c080a0b0d0501060609050a0803030403080c070b09070e10050604050607032a12030b13050709080f0102030a18021806010c08030a02031006050307022d01051009 76
    0x980700c079542d802804001c05120580080d00c1c1c503880e2241400d0b98001c41600c0c03021030181124400120030060040040d1800d965400b82005041d0304011080d009190136140c96450320315000d1240c4e1203000c020405414001d09200094200c0c4815048036805580318244010901705442ca40b40c0c2c400582c09602601150b11020500074a815030200e000c90b100103200b180390500b04014803040c0e800c40c0c20110b0038007900b07802104090092040192991406001d01c0762880130905000d2902088481035200345468108a501c1a48465207009100b050745500030075161110030701110b1041c00c5a00055139801b4008240300c0840d010340096004141b0000140006851102032090305500300030002e600c071017242c0410203801e490101b810f41c00041418070085010700b540300c258041c0d06c2141d540c0e018690010400482180852040c1e001d00010b00d0028194684641c000e5a2060303d191540320b44c0b020621024400d070782c015101da096000d4030b0002d2025040c0200c40d0140d90401b400380e00c004c103050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 504546402 1250 504545152 504545179
    0x1803060b040c03061a0c0319020f070911030a0e0c040614030705030d05041806051f1b0201210906020706060e130c0b090f1008060a0902070b06040b12010c030b 70
    0x4c1c041d070004e07a01c0d038911400e00b1050741043c80c50030364029a80c103807850106100d0302e00c04039400600c60a002d800c50300078100003080080100e00f80a8243c1086480c0c610344516881800b5202094a40c008000180001ca010380310b5040c92400740302e105100ea00a040c4900425010701c07a201c0d00d41701070300c194101c0c0d00862300e6008240d162a041c1d0a540005002800200498039014007403117442d940110700002c0140d143c0c000705c0c80100c0b50308114290030751542800c00c241944040d400803040001d44440d01d0600c610341c0000c0013148840c9012011540c0070b0340010618030300c1e5111031503580d80150115075540e01c514103d009010799204840101800d08006080b030805185260391007070b03015141c0405e09042060480064004442054100c500a040d0102d035485820807007800c9152a01e034010245405030801c0080c00540c4c21548201d0300510005000400e840051600034400700d074041017000c0b0050106403803851030300d6808565030070540074900c10f58156000045450090310540d050502 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 504547652 1250 504546402 504546407
    0x3031d06090d17071703010303090b1c020a0207050405150307080f1207060b060d051005010c0c03080729010e160c3504150c0b07050a1803060b040c 65
    0x110614540c010001a580302d00080421078010b1402d407001a003981000c4594a81c00c280402c10002c480d00e402c0004010f2041c1500849841c00902e01d1110b101e142002000005586101c014151200f840d00414010040c0340203102c008060840035000700002d141400310651300c3e40240303010a01902078110045044000424208021001d90f8014040c400300820550b119503c03542e020345819588400000060351620000c0c042070201c1e00011546c0c1c01c1001c039030041e801d155400b19051056105032140040e81e034002d0201240c1e000003050349c45102506085500607110035000c26104078030303002603d02002d000c40e400d0584000c0301a0034529520036090707406e0001c00b140201e011529000410340000d8000900c12034812041d10807200354004036143c1950680b840c03448124080d400f1500344020340c4071001040e550b0000b0b2405440502154032460403548001d403684042020014510103242d01511641ca5014010301200c0c3c000e03a03403030030b10f04001c0c01d200420342d02c2503050080000d201807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 504548902 1250 504547652 504547657
    0x2060c1b270f040f020a0b090427060e01060e0412090f120204020a0201060e0705090f0a050916090b0a0503010806071404300302060906011715061903031d06 69
    0x50610580072181e19480c40c0100039481c001e00c111400e001d41c150a40040c1c0341e0048603c0280720b002c0c5101e07151450041044151844c5001c40711100134108907440e0b03a10000000140c44c0c0b50002c07400500b00c134a101e5064050710054000346604031849080c80100903580d0201400400307540e82d50304407aa2503841c40e81064070244510b155000342990707102e0241c90140e00801185056000008825640d6004021269011209180460004030707400f462803d04a1004840c044202d52003e40b6031b0030700300002c0040c1405807101c0002c0c0e00418001c0d880c00d00a00340640071341101c000e480d80751065001c000302250300901031001e81e8004d00c4042601c0b24080c803007205a200c4060307062400c060901102d11344982210f0010805c035000c1840d15083c0034046a0604883c0703000f640904001d1400301c403028600b0106a00400c825510038a480000c41c1b00403490001d007004070060300600c1d899100001e00d0110181003c0d0502d4051203c000041503000291a602e500a1003070130b20743c2e005000100036150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 504550152 1250 504548902 504548959
    0xf1e01020903030415051204080d11030903070809150c0a170a020c040b01050f120412050a020c0108060109090524030d090311010c1202030a170402010e010c02060c1b 73
    0x1540284418084655103403004100301c00b1521b8803c0c18440800700c12500810181c0d0140c816480c0090404280401806541c0d03069418644440c41c60a05143d03145d66881144800381507400041122006070f510764401039100b0701d052041d02e450740f5041032499118000303642e00719500030245051003407424036441914054903544d0041c00c49010880c0c1444050441c8a044604101c0c04104a1140c02d031084082c0102c260070100c407038280e03e002d02c0d2a80720035220b20050b400784442800000c040ca42e0025954016890a180c4071b20513454020061b14241101d801c0003030070380e040c00108403410003162030380d03844941d2007412080703880e425605054840300c08080c490000703021118140701007012070702940c42c4540d041c900301d4030090040d01d40074903201d055403881c40143c0000581510766580454280014650720409014a041950005c2c0190042e00301d240e060144c00c501000555440000b0342c0c0d0452141401e540c03102010305c9030041f04001c8203205d18400c1a4100c0750008000c035102c0440903c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 504551402 1250 504550152 504550159
    0x3050a05070c02060304030c030e060f09040c0305010f1211040e160608060a0611100903090602010c0905090a0c110f010617010504030918020702041415040b0a14010207080f1e010209 80
    0xc46d12161022100b0001e020b50503003e1000c140c40c061450744034080101000844140c041c1d841d84a00410482034134241d0700c0381010141408014805244400c00b03582c1100d00807541215000c180c0d180030100c0703801e0420801d43c0140380c540300380781400c004281109110000a1100e0240d520348400740c0d00850700741e6506401c4240150300784819401421000900401c038000c46450034500c100140c150b580f240412000a4030f203910030007a0716024045c06601c1d007414180f20740c80310305000115108100045c48074513565143c0c2d08014205008000403041600b1030030984c0c022101c03070000740340640814810200d40041e02104280ca5a1041c4580d034001c952542e00c85920328941211000c088440140303480318640e00304140c10060b942c1748a0385526840041004506181c00c1511481c000d00c40c1d040f0500803810002241c8007590307005200341c16601c0e00304544502c2a00080100c1c5810020340040c100c81c81241803503c010a80010405010f581c1e039041048107036190000c032070070b03401100c1c2744541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 504552652 1250 504551402 504551407
    0x40f06050609150d0c0b0403052512020f060d1b121802091e010915090e071e2c070c05070b0a170a0f0b04090515090a080a03050a05070c0206 62
    0x81904d4078801d02915503014803040c21545480e1143d4882a503c07507070080383c1a80c8040980c00710b035030a030108034404c0c0c44011058540249001142150108403c2c00203229652440303050100303a654105443d0140d0820408000a0a001c180080302c0450104880e01140d000e04280030322014900649a006030f000d0421740785070082c0e90a12010140140a41c2a008010180b40702c1290b1007500030380c001d00358004049260340e103801c140541020690801c00c00141407411240e01441d0004402089030510442003902600c294101c0808e444075400042003014102010240241e200c8100c0180300d646c85da4908407903c0340002a19207000544009116400801003005440401d80140140340c00f1170034640100c25040503054201b160864680c000b60b0340d1044081c116040d18403c1c0721000c0800d0f0750401c0b044071103444140e03490303102ea0107000524250200248035101c09001c1440140d500245044d11542050740142c040e00c001c69000d40d5851070030001944031841402000c1d16150054150752 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 504553902 1250 504552652 504552691
    0x10f0e01110711040b04180305030f01060504030506041104020c190c1409130809090103050105041505270304050a0b040e06030601030c060e03010e1207140f19050109020405040f06050609 82
    0xf0217080b40c0300d103096000342d41e40320f900000190008040e810364030075500c43c1e5a174600400300c810400c40680000003001000d000a00014034005541034205400c0b40c00f0b0454a8001c2002402030701c038200b0072441c075000381c150702c0403412a0700307a103640584c2c4a0f1042c810426280e0842010007525004c0c100e60196882010a0b1442034042492048034000c400300c1d4a0640c4041c00308030820001c3e80b04581c0c03690b46404010034040c4c210407503040f020030ba45052100b81032200b10740811402005d00e0701001c0000110f1549016130800c11113000388005014440031350303541c1c50381a410f90400d108090320241c1c0200088c86c0c6150210700e00e03058a5110781c80740c4200e8101182220f06aa0110740d1a406650740c48680300032600070014501c0003607606010795030701c090700d14080541540014001d01035a00a035200030201c0f001040f001210481200003079010402401c0c110b025080c9140081e400c286020184014401600803500800d4040c8009111944401080c0700d00408102d608050b840d4540f42c0c42c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 504555152 1250 504553902 504553909
    0x3040501050c0a0206130806070e0120150c0901080901020a080c070204020c0a051b0109081207032303070f0512150d080301090207030e090c04091d010f0e01110711 72
    0x20b0009600d41c030200d42d1103142c164045515984a400f01d003100400c0442c3c100b1810404000c05a4848200e18000d114140c251002a06184c004d5400029a140f140380d9115074500400011000304002c03d9214490700b800c40c03103074205511078032078140003c0d9024000742030420140220341031400259210202c50b42c8a5040491581013504100d0b8025002c224210b204d0314108500078400b4050320290200050184241d2000d1814a84043c1840b02d0280c0c10085c1b401d0110b04060300d01001e0b26156038420321480c00322030400d4510200d0602401380100c02c00c0000c0060007452281e0a56101c0b8600303241141000e039094001d0360501303402040784000142c41e0000c0180d40f2514440301130000c8a101d5900d030303034031032054002740c0141504a902003564002e050f800007480c6900304041c1c4103103e2a0500200c128454840c2c0c1c02011100c5407120b0480450214883c400f0603c03465110003046000c60b102504005000d20038050802d642c00c2c4000f040110510000b1180740b45d5100d5200c1c2210708880003030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 504556402 1250 504555152 504555157
    0xe04030e0f04020c0f010f1e0209060906120403090909081602030709090303051f0b0a27270b01021b12030a09081c0f030504050c032e05090304050105 66
    0x2060341005901c6480440c40d00c4038000b9020807084d8401400c03913011040c40c501e0840c2c11040240b02c40134103203261002c121100c507051142903c400721015a80703500d0300002c80d5152003000f041c80c1d080700c40041e080300303803e18000090f0300035880f03035442500d190350390720300c020030b844c40024050903c0c4c4003003003141000c4200042c0f04881510140543e00404e030b4a8085d0400c680c211001070307000c00d85440800200301300088090000c002005c2e8118840d504044200c805402001040414800a0703103901c0e10007568000745c500e120845d0116900d0184c0c56818041c0d000c41d02c3c0b400f6007160980c000000d001c40c003c500604000c0041039005104002140e80068500048e01241c82e0700180c0200d1580011701c0184018001d00030705841d0b20014502c0c2107a01784c9049400300040c054080c010307810480c01030f130000c041c1401c1521460007140d1a2145d0924608184100c054240d0621070715010f80c0c110f60b00f40503140c07408980203900303d281c128001000710546e9400c541c082c0305074104001c244505d6019402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 504557652 1250 504556402 504556427
    0x503071a0c2208070f0911310e04031116050f060d06091503020307060e0105030106080408162117011203050f0313060e010209150c0c03030304060905010e070e0403 72
    0x360b20b030710b40f5501c0303101c20f007009030581044c80c100c440000140904401400303191440e0140e480b40a1804002000381d0b0740700c104641604010030000941c0c0000c214212088801518400c031a42d845400c1600d0060020030b0035000304400e07070040402a807003085a05c2c103200d040f01c50184c103024040300f0000821400d0b038401907100e6100c82e56640c001c03501d920240b103200c46810030310020141d01410340c0101072528480b0f61280c1c0400042c00d0441c0f61130b0340e0100030360b4110340703c50801c034404d0b4856181c81859409031045103c03002c4600344006040c8000c1c0d006e600c1888080407001c00c2030b0074010390101c03190028042c1e070015100703034040108507080b001c40d44111031368000e1030030908040000b01c8001c8a80c2c42520310070724410315400c40a007400300b14402d003e00156400000c614020328000403450f25031b13025070200005c200c08200308813200801d0041c2480000005c05895480c9401d1a0180060072868000d031003031743c6040e0846c001440c0010300302d801e440c81c04d005031042d079a0350755040b0317420b480880 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 504558902 1250 504557652 504557707
    0xe15130509100504052803050909070e040207050709180309140f100c0213020901021902012a0510060605160c0509161e05070206160f0503071a0c 64
    0xc942c14400300e0244652400b40d4881e4025260214010a10401030b41e02e892803003100b040c040c5007240000e5089021254242c0c001d0310140026a15410b081d13800c00c01d407050040c1c02c1070000030800100480030420130300342e80d05107800300209289035841d49481da266480080100e808c000c400d0003c0c40800c908401c440f5002041100102280c501084100700d082001001086001c000002145082001d06c4007501015104500389801000000d694a004560000e01c42501c0300d10503040da48078800c2c2c030180c902c3e2400709481071140c140612680211090007a60a07000320038103418070301110f024000807522503941c0c003814105026180c603110201d500c1d04440c07404540200240d552134009599100b011607080c807003008543c94001821540e03000300100940d41a802c4034940c201c1c0c004085da0380241d01598400e88400d040104030900d20000d50020b1b001600d807113210700c10404000018141107101d0441d00510302d0611003010403002c0251948075142c2c10a00544450a0b40001031900051544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 504560152 1250 504558902 504558913
    0xf0a03030515040213090c0f0c030e0102100213050301060b040302210307020d060b01020d020109080f0f0409060b1908070c02040209041d0714030f100b0d05030d05010e15130509 78
    0x810015040780e1081e042001280d09108003001003030120300c1404047e203070074140703480c000700d40e084024590015940014140104091304881a034070800541500c4002c40a08541d15050000e0707094881420380b051510960030400041343e4110304909846c00c80b94003030318071004040310066403821666004038154a91009200c1c88015076105008235800ea03020300d00004881d44a0800242041903020403141568104540d580001c1e40d11070460344400c4d606440d0544070454a01384401703903c580d501c40860b10f4140039004c600341324030b5801441040c01611085110816120041e200c02d84208d4000010912a0302420090309060b0000c1c00301110040000a0500721141c109814804071030703401044da4402c0c0c10502011006100105124804030010000c1c4030100480c90344e5505019998007030545c840211424076150301d0a6510a96404001c0d203480e51100b0441c0350007000b003480f03100c030100000d60214484001c0c41d04035842c02c40c800f41080342c51713400120300d071000f17010702410b840c00c2031103403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 504561402 1250 504560152 504560191
    0x317010828051c170408090a0803090d03110c0406240207061b020d0f031205090c03030d09030c0b010b070605310503160c030c090212040609030c120f0f020f0a030305 73
    0x4135401521652240b030790561540c1c4140b050003440ca14a4204001550041004402c03d90360512401101c035850b01d4200b0030f8007102d1002c14200450b0200b40c2c0e1b049800c101021032600d07940c0000d41c41000c8400b00708000052818000c0303035988940d104820110300070060601b003445400d0403800e1054006442d82403003443c1c1d66142024040c01c80c40a4001400007003d81a003101540510790b000300d400401050303031000310070000b81c480c8100c091300d642c1a55554100005c05018081d42803202d600281075201c0356070741d000300103542d91001a003201c16525100000d031222101000c0f2130b0b40041c881e40c605008056204012909080b0800142c0c2c6c10710082c8a1035055124100c11015050b20aa14917550f41c0d20b145032400c80d413001c540001807510b0040c131484002888840a29a020b41c2017000410071000030306080c0c400003901c040107440c00303a00c801c0700b000254021240305c3c1054882c0d0384000301c40c040c1d56000c0741c441030350740b1071a020341d04138140d800c020074030980160b5080f4080c1e0f641c51685c102d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 504562652 1250 504561402 504561437
    0x9130c0e09071d150118090b0301060308070308090106210b043002010f020f3414150601090915080a053909040317010828051c 56
    0x1114541c40400341c0c0d100d000c011842c9800c09040511300803e00700780140d0340d620403502078801058000c10035800e6451034001c200c1e50b025001a0000e6030401e440c0396031800c090030010030b02203040704d0600c01980dc01600207000107100b8100c8406860300c24100481901c0b80c1e4032005e19900151040d1001c03400c032500030020740c0c0c000b807202403602c50804180380ca081040c08041d017035803200038180c4645407043c070003040300c00f01002c100d035541e003410182e03074403000c0800f0000c0b0391031910085103040b4400f20840e120704010585032440b14a07100035084524210580e61a0300d102c0001300e60b041c1c00100c96007008c02842190b0b811048404502400d440c0c0466281c0f90201d10f0314007200c0d030a1f1000c8d031290a0140c01e40c00702024083c0060b003100c0c0110a501405480e0030040c154078803c2a001c1c221400014051611841c1e01115140c13032000c0208040d65155407a035a90500241c1c25014518a180040c800e81c0000c40781d040b4040d4400c014103d0f1054505450400081601404090000c21a18110a01c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 504563902 1250 504562652 504562679
    0x1b030a0f050106051c0501080d031d031c0b0306040f150b0303070b01061704030e010f03020409150302010906020313051c0f050609060c0c03030a1104090606050909130c0e0907 77
    0x20741990303480e0316042c0f0522542c101528400e201751500313181400501c01d0b80c202148800d8810558203010406000d040b00c0e400c02c1c050104501c2c41d00380030100b85640c0803128031701d142841c9600d01e082444128011404c041c3c4812007943d0081c80e0814401c0107000080ca500180304400b03010750b40005286c0c8038a0046811940040700840d1349802c600c005103c8560080d0054004d003410320b55100321454180d0307025040720710915106044c02500151211000e209030101e40140c60b400d00c09000c62940440e00100043c03513404200d01017440d0200c049015840002a142c0c129110030780c42410707616050a03c128801d2002640580e00340005050300400d0f039100e0319a10306072180c0c000700900d1401844040c00c04802401a06c21044c0400960035480c0000048c0e03500300241110008000b804c0c0c030500c485a2060380d205502c0c440c180900016020b42100c09041461f00c00c0d40c40c4241940c81e0041884040d030808401004480c4642c0c05011240072140002c0e40101d80000b181c400a8a4051b41a030340c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 504565152 1250 504563902 504563909
    0x90405010f0606020c210d3b01030b030c0609040b0f060f1305060304121803120507020108010b0f0403080a11070f051008010b0a0f0e09012c1b030a0f0501 68
    0x181d018910381c045170308048100d0301540900d0005d030746c0510141c3c401c068440d0081840d45007080401081617050b0742d42540c5031054082d1071f0305054100400000f030001480c82e07044009020a1520840001078240403401c0340340d040700144003500d40614101080018040c81c501d1036000340010300406881d841d802c1c010070342040131046040e113800c000c0c00e6080e0041c840f81c015038041c54040c0203000004130302d9010752400e2141820305d8119941d12a00400348030070705600c09494003002c008440030442e003090041408138002c2ea03400c2084c0c0e0729041c0f00e544910402d00c035400340f9a030030013082010440303040140c90710489601d04003980384013100c03503107141418a0300883e404859440e410401e0740f0f0400c20b03e024000f03060511610f15031500102c20643d020b80e940840c2401003400310300c12003d00c151400e60400c500200650182e584139005010044090815090401c2c807036803a80b200c1052001405108015415503180c041c1c044a0000010740c10150612008580710b64038402c60166500031136001c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 504566402 1250 504565152 504565157
    0x9090711060109060620150f071d0d030309020a0b0c0303010906050909060708060607050f06010503070828030903020409051005131a0c1b010b0a0504050601050306090405010f0606 79
    0x25003521050080c01e1450603071081268034030b0010100100f9801c05410840d450104461a1001604020f4141030500c0f0101402c106138a0000b003000503603540e0700d13142c020544d581e1105810320405145640007491070b1000c95200642d4503200000030700c241c0004400324400ba00201c0c07680e81e50301c0c1c0b8400d1786c0c000e0304075111a0f410110062020306544e2145a0080008860441003030900685040e11810060032210801024800042c07050301c800044800850b07000d0111480602e1494900340c6408084c01118447e015050740094186400038942280180d0f158800d0b005800404035007007001113203241181407005040d000070141c0e5031403041c0c0c40f010f1b00036405868129043c00c02003044410040250390120007051814021a1f00c2211007403980014001d4030380c15072078a0480134814001c107501100d141c3c11048040380c4014040d048014592000e4460b14101602d0302c04100a580c4100e40b418000b5005200288070340c43c01d283c5054200e402180002000d40c07944524a0640b0b045400c075102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 504567652 1250 504566402 504566417
    0x110307080a020f06040f1a0c16020303090312031602030c1b040f02070b0601030b12070e09011b0918050c03071b06060b070c0b160b0c0c070611060a0b030d03020d02090907 75
    0x34000303090341d4400340b00c1c006060000507290a889226290107212884840302960309912000c40d1410021a4200c0800a00b193f6806588214154076640b04440c001e0080942211101407240004144e544e284800d82c05415110913100b00c0d14428458855459405911289401040310745440103004090080d417003480c0d180362100c0003400b95182501d015006507040075020350140d402091100c1500c051001c0b208107034540c3c0301c58034003400d408115015048500303516a00450b4115036501e00315000200ca244503a501728a0020498100321034400d02d80384200009120107101e0740f401d213480c0703140610941d8200e0741601d8040c21030b41950003c0d0124040003440c2001d2101100340c1394010300481141074508074aa0aa50855030385000700100401800030104501050a10944030245958801c40e4065561040c00500301c01598042c21402e006020218080b200103004030b800f4a00c010b4000c000ea190340ca1803c80c001d6001002d0a00e0b05642070102640e04e540d40d0007010302a01080d9507114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 504568902 1250 504567652 504567683
    0xe0303061c02090a1d0a030f1101110f0a080a09050d110307051204060e06091c03090306180308070305060108150307030b090105060a060206150d0f050a061a01110307080a020f0604 79
    0x300b5152007422017030856204125940c006a8032544140103200341d840c2205416107850307006405889003803030903890b107800400c0c401d904c00f0301c00c40900660b0002c0d80e506d0307c5a848500c9090211444200060140d401031101c003038046004207500031490182c0011203142500a0b160541810501c2000d400c4030f2a002900300000c130303404100d812510380210380c1185082881d8002179240d02648101c4202d4541c01210740c01407600603c4031000031504680c00380002010703081010801c8a02503011404580401c0219089034441d20800c1c0c41004103844031800c64968118000c1d411011810f403950521441e178011001940400d046401091040004645ea0514104101000020b904010210752107401000108248140740049403202901c2c0800140203034182580300c01d407003a03406880d0384900302c0007000300140d0764005420079091100d030199844904004451120140d4050041c65009000d48000319040c81c004003502d2040380101e5251224000c3e4040c1040c40845e010f8800904485004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 504570152 1250 504568902 504568931
    0x2061605011d070f091505060f040f170607141308070e07080408120405030d110904201206030708061e010614030103140a150218040e0303061c02090a 66
    0x81c10050702c2c00003402c42e140c144400592440c4c03452080c0300103503449003c081c100000d0381b4000b41c01340602905003a03a5403c0c0d850108070940c0305105103000a1045100000c02c0c902e00d0f41d5950301c01441201619040c0c031005001c584c0564502c5058407074490802403507010140700c500c2e240051190074040d01210385040c0c1c11111448004141c0c40520070900304100020b21041d04881d461004114060016100d605001e4994060107501517500c0e40b40c864140c0c6401c07c840c014004c0781d10122028000640f42501641015080410401e00c0348401e210484c045d540411000ba80310030041c04803198240c0d2202c1503864204c003525040c4c20b0488503440c103243e02000180c02400741c8410f0a098400c8507104003d50741520051202521603049040412802c030402d01c10203a50700d41000c2d00210650210004000961004904520120700321107005847d00341402001803584568014500b503039911418000101c516040958241c160f040750300e001070340d0304e800185c040c404041c0e0002d15070101815a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 504571402 1250 504570152 504570191
    0x50c13090606081203040f11061206030c190b0d0f02161b0f03080705010e0f06060406061b0b06220f14040b010512010b0310090605010f1a070206160501 67
    0xc04a6034110f5013050a40c510740004590b003040d4400c0c15560fa21800342004400f40304800c14003540180f0015080e201485418151402860b04405491020740d46a080044046480303256500884ca00942000024680d502034180075900040100303c040c5140480e20880c0c0c8149580c10200d80d20342d00c00700a001950014092550403c03185000541c1009402c0d5220035141c4001070038480c00282d40420080c00f9006421116051402c60300040b40c0781074102e840d50421240140164940f040000da01c62140010b65113880480d441c0c110802110380b11184c1e0014024130310b0703401111400702203040c0070b1882c1145000001c56840051601c00403420001035035042501e4048052032101800b020420b100b403602d0456404480391321a0031407010029014001d0540001da050240541c2021784004540000b403240c2c1c410101006180c2e211030b0301042c0e40c21240251203034400c0701010700c212204a58002d203590740c0000c2c402030401c507403603101c19584249404103c906075100c540c14040310301352040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 504572652 1250 504571402 504571409
    0x8150301060e040b071407060203280c020f031c0f02040803190816170a06121b09050919150c05070b01060201061401030b0d1a04050f0105041509050c13090606 70
    0x10600e02c200c44005821b00d0602030510007403c1c1039070010204259401c01c510524403000568503103c00302c00c0f0b80c00700a00918000625401500030690001010385010007100c1000c1c2d6000e240c06010540f4180803002040542110b091943d420000410203d904102400d100c408010600d054000c1e1b1000003000340314064059065403a90102040c0700a4104401c5c001c840c0350300d2301c41e00060380e513808000080c00140c1c1c012152001140341d0703581070251281002c0c0c0905900c0000c00412580c6594071000c0b19021214031603660401e070035203001d1400c00d1800b0190f16002e44401103e40001921a100700c07040d219501010030b0001509a08110302c1580b441d00520140c0001c101545c5420395200c0f071128204640c2e81010b40c1d40b4418419691107203049500190020184800d841040d00084034040e01a607003035072240b090307411840b0000b10500603548501d82c4a18105525019410701c0c0c0d02800ca028421600782c020030f42c0a038085d0300c6002d00e190100d0312003040410310005da400c19808440322a003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 504573902 1250 504572652 504572657
    0xc180702010b06161e020a06110105180705010503100e010e180c01021213170a050f0105010f120501020903011a100305040224040b03070905100206040b040308150301060e040b07 78
    0x1120001074502c01240465117030300300204006601d000000900300480883c0000e501220300d003404561241e208c1c4080c040800080001c01554a03004807031040d4030280c0000345484da00504090020707500c980091500302c1030583d00301d03183d00c0d202c0500d801c0400d026000310090700302810821004a20380d82d4422140410400170700144a03003400001c2d111340300100c0800c00d540001070340d040519200800080188880c9002484480c1d10344c807129100c0f2000c074000c1c0ca8521440d0106a820f03c0188a9203040710402203241000c00c1ca0400341800084100500341c1e001d540c2400300c542261001c6c00740d580b0741405800c2e16001004075208011003404101c00c8842014504001c0000607103c2110f010070301d4000018400c2041e00d540340300324040c071580d0802c20728144044103204501d40c000e15904c003655012645824205040141260f41340c0c002c07500a0146d03000710b404078020a0140002c0b54101070022103c08460b42c008001c05d0a42d09550b010044c0d001ca900b0402045c00700814140d40c21040c0c52 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 504575152 1250 504573902 504573907
    0x9160210182906040e0f060c130e01080a0303320907060216030f02030f07090e010507050304031205060111030406080103060c0f020a120c060608031308010b01120e0c180702010b06 79
    0x38003008030b1681c006024a005681e00c083c02510b009082000c00b00b11142801151600d00d0078810b94002608050010b600303c2240800104071003102516040c11799031000000d055400b01a1001c0707000c2c148162000000e0310440e20601c8031801c2d41c42581005960b010502540e5050081180e460180d032580200c0849d00a292000002040c2102d160204c940041000544106d940002030400c2c4404448a4581c03051480010b10000150040007880301c080d8020030865032003290640301c512040781c0007400620070500f81205e18005600c410340044042c500b1040d4908001c124a1441e8030680000c0c0120304182c00400070000d0f140078011000c4228a483d22038039a103034001964a0301c000100401622080b000492941e00c1006181c2c1010b4100001b88002a03980040715101d900c040c080e0316040d8060b4a001ca10071605000303010008506940786060031064203040c00007040c0b032070440c2418ac060219844c0960303031665103117140410b01d1545076015040010019085410007031941e8080d070010f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 504576402 1250 504575152 504575213
    0x1140306030a0f15290d1e1104061e051002210f0307050d15030809060f09040905010c1d030604080d0f0c030f06050904020916021018 59
    0x308610000a6000e01607845405440c034150030b145801d03400890781a442d05d05a038128051300c03a204210441200f01c0140c1c4820107030b0500c5007900c0024030191624048500b00d0700a90541003000c04818080d042140309030702d9260001703080d240b107503101100034110800004146a02034412000420701103400d40445030003654040c0d00c8211820560740301c0001c0d40d0f040042c40c0590b00440703841c40500e00550380c1c1c0785400c1c8000b9200f600610b03141c250303007460131103001c820254406509056075080f0090781d007456a0b05082028a038404182c00203100014004100203851b14050700300c5582c410000400c0301040710000502d500602e115007413000c6001a2400c2560300e010448030380050708014841d580d1000e14000c4e03c00b070400041700d80c44e13151600006408960b4150300400d024480b0f6042400490303a94030401929043c142d5000e0b500c0140200891a100008183c0c5000243c0c1c0d8010744130b0160050980f5000c0b103c4400c80d54450381011200d4408200d446204c0d040c0e00c616001c4119281d900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 504577652 1250 504576402 504576409
    0x4060507121a191d0a0c0f02060622061202191a18060a170105030f0c0910030b01170c010804031b0323270d0b0408090a08030901140306 60
    0x300c01d404140518003615481c0081c0480840c0000a000258a558161460880f001070240803c4441543e0175103003003018004140320315440401d0079003030b50040c4902d88030707982002808141c86442003131841d110800841c2c60601402444000c0c100c00c9400300d084a6140103000c145401024408000b42d20042c09024825990300c00100b982c07408000c090301d802c10b290090f401d400040c0381d06507102c403002c0380240c0340384e500c031803038a8240101c0305640d6980e0340c1e02c006156484018405105903504059540e64903401d0a543c4541d12400e0780d40083c8050b40c1e2030300c07a490b0b444800e07008668000c1104c407003d1a003034820003045065030000e182c01d16039813419407401040807600900c503000e0303601502c0030501814415980f8444810b121a920026031030b8088684229501050400c020003541d10000c0e00442c070380a8031440000c8016003140784031015036a62403e07138200144100d0b4401000e00005440c3e44a0b40d20640103051118020b59843c1c002000250015410321200800110200100303c502e48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 504578902 1250 504577652 504577691
    0x2010807030e01141302030c1c140106150224250e091005091518090f030a050306040506040515010e01020f060a06030c08030a090b07060b090406050712 67
    0xd115280000e000d50050400301c0c090810081504031804802050004c40c00a4201e1070a856100704c0403101080114028410716100c5c0c0240388507541e115a0509010030802000d400e0390607103a800001e009611461030007038005d05503c1d50350040c0d000101803000d181e64440c2c13029200703540c11007505c818900031a40324002c2c3d10700314403141d41030010520400e1090190800251000d00200321214074a01544409184201442003500c1001e80c03001103000e450070111018661103001c3c5c54110302340d13060f0608994980b00034040000e181714000413108490700c03e00c06408614115510f007960303400d2803401c2005481d0f018150912851400050110001c50303145e25404245003800d048030401c10007401030b814421046030b001504d01940c020080524540c0d40720405803807241c50300d01c1e10700340c844465a07582d00414016a02044004409018241c01a4003401000344940c102092881080000c500d0b03402c0161800c0ba12580c40d4018415040e0f003007001003543e003108402c10006003a8000a4480c00e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 504580152 1250 504578902 504578911
    0xb0702040905010209040501060305060310020c032218090c0603150e0a020702220e0a05150c19020708072c06060c030c030901034a0d03150501050403020108 69
    0x1580d860301d0250030840290150369000c48002c10400c0035607074514000d0080c0c4800c640b200d11074091031000d07410080b107510a0710309039020800150f050034900000c045856100703003e50220710b00700d60800611100d28100000e02180c04c4400801c900106140505e000002c0b50490000e040c1420442030742003e800c1c880e4011511801c154101c240c0365002000c00038824a100a50000b040001944001c1685072900d4103081060400700f20380c90310640601d860b1300390600010500c0e0042d501840302500f044000300d4100307102400003881c00303043c04040c550480c02c4c18002c602580001008100c04030040c0f00300030003800c03040142240c00d80d81082030345070700706030042c001080480740340484c0c11a1110b0081c2e0303c1c1c43ca040000c0780e5446161024465994020b006403600003401c00c0e4030910081110004101001c0300c0300703038000e99025000391020100d40e00303020100d94500006900f011042c01005000c0d0148610f8900258080d0740320840c0e00a2415030f04400d051100811042006036030203254150300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 504581402 1250 504580152 504580159
    0x10c03052d0703151e0509010506070b070306050d03020109050d020d0c230d020f010b04090c060c0f29060303070305041a070c0303090e1806010b0a0210110309060708010b0702 77
    0x80742d451910a4004026641605405440003c0c02090030111012000c500c0d4440018403071405503164100800b4550134000d454001406001460000d60411941c940011007800d001c541c160300c40b07011a185ca03403001c6003078005039140ca40402c2400003c2c055840c1e440c1da42d201410306180342c080080e04015544030000e241405030036081681d9503440c005103000b00380c0001960003903500454003d41d901a442c4e083c0c410b42d443c1602600c0f0a190900c521060142d01015622049180440c16901c0c030703162040968280a08020640000d030140c1c00d29902d08003c01ca2100c251520203900403010400205094001e900c100403100100360000c1c15107003260840040d91002c00410f20540d4900d000d5000010000c400305200441010303000240c12040d03d840f0342d201e1466613200d128038121440792200100d400c1d0010b00040c44000c3c4280000c0c20281d2560046420600e11004200110303103c1d00e0360180700d2880413051212411050010311f030006000e1400091550400ca000c5000d4490100000c0c030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 504582652 1250 504581402 504581491
    0x6010311130902060408150901020403020f09090c1908070b090604090506011101020304080a0e100f030f060e1005090c030702070608280c0f0207030818041d010c0305 73
    0x401e0310550440800194041c1010380c690b640c80500980e221504080c0c0f050950600c4e00040c5041390500c20b07101125002000455641d000906002e480d0f04042d201c0d08541c05a540f590f482c4e5107450070400d40140b010b444003201c85103003021080c181006600421051042008441c14075a940025101900e0602a000410380c0314200181c1d41d0184900070384480d9400071080000780114000030f006080030075110348070b003000c180301000f10704480caa12010108030307041800c40803036101ea0f04c804554890040d002030000d8582482214200089914920701001c0f1b020901840c2043d13030076550020600f021203070840c20034100c003a4650340340c0d00a510400c1020000100202d880f0707550011b0382d070f18004d00040f604002d10904000340101c00801030110700c8008032006414800201281181c0d081041203091509236142e410300800c00650f85a0f10035220601c4544603000f0102203600c40050306c000040e00000260081d050b944010720501a02401c1c0241c5100040c0c000c100c07000400700142c2e00c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 504583902 1250 504582652 504582679
    0xb03060604050310050915070f080c0c03131d040b0411040b04020c0604030f020325060e0106081b18010510030906110c1e03070f030201020408010212010905060306010311 75
    0x8100d4015640481d506120700d10f0b4000282800d0f902a42c003c080303680c2036806c041c0c02403541410340320007550743c0c0001450ba6440d07551681d1103003903420380041204854518020580717800625580100c2151000086400d40400c030700092024544019160506040e5a5140946501090940c01000a809807445490b105081c0c2c2d0b4550007120105c90050045440d6400340e5515542e0380300403541200460410898815514000000e80d1841d149190b18400881c01c0720b10074107000003030341c0700480d5100e40341c540d10007082c03400780214000b40a2850080004034003801c0507480103101a1101c41c00f503071001010799600c12a4131751503070550310181c940e400381c212130190440080024800240205181c842d1051085040d4402030888540d40d60889034404401d1816034003035000f042c5049071650041200d0400582d01c444200d076541c3c080d00005082c41d0340c6e0254542680c0c080d050001c8120318a000501101d0071034480d050f0401810b600410a660559583c100358010014005200724036080255 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 504585152 1250 504583902 504583909
    0x2060a030f020403060b011704120e13020a0509011803110d0f0212010203071106011412150a020901030e0a0f03052b0207020102071d0712141509070f090b0306 70
    0x8120207000c0c082190f40e00d55900b05078000780704040025000590302024140e0b0500200b80c40c5026980080d406421014095001c0e00c410041d61140c40e00702c8058000344a04003581d00c050602c64060f9142d0950302c0021800060940042140c3c1041d94a05c2120900124042100c20310080d20b00b40c1d03001ca180595410701400340301c42c00f24000d602170f0b00040b07054064103064000d140076051a4075120381c4420b003048080e40342c80e001d00580c40540c0039079414180c0e510f40580086035880d1042c0130f41d41103c401c0450198038003030454550071080e8001a0f40c400d1540c2c1441880c9006148601070008044203a8a40c4203082c0c04102c0a01044000304519280c0005840480c070341c105d0b07a028030349840d50000384a6000e508184000c2e405405003c600141c0e0010503004850540c2d0313440001081a42d8043c01a41d0416100c0700365465903a03100e0b8039803000b503c0c181010703020f5072941211000041326003040054192001300003100b0801204c11707038000d154010078031805440c14001c2036500e9682c0c0c000070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 504586402 1250 504585152 504585161
    0x606070f0f02040b060408030d1d0601080d080609070219020a08010905070f050420181215010918030c1103150a11091c02010c050709151e0302060a03 66
    0x40d01002180d064142041981d10008010610903107007400090300c10b10422100d40202d1003610120381040100c2c942080c11540407106442c1b1102d6034403542d5109590702440c0405c260040d002513400b00f2920704405410400d480c0d403040701154510303003a180600d0000d482d43c40c4400b032058607002d0803d854045503910b14030f9101401c0381100801c108038881c1451503031202544115114100085004509401c2c01c0c00b600da0081004618481d141c030421200848550091006240d00d646208000c0c25a944003c80603040c64001d00052440300e08a00b0802c0301c1600c182c0c0f084401500d07080007541c0b11070304041c2d0b80c000d154050410443d0210982003100308112002c007101d601d40200da070036a482032403441040d0b018190201c02044107101c07610b0790f4400c038421030900c1e9074084010b01c980c0c02c4a003400a84045124418507007032408680f256107083c645551f0b034012804032074940300403040d10010700c0b100100a0407618402d40c50030000070180890307161280000380c0074040c005100c280d01c034000d801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 504587652 1250 504586402 504586417
    0x5011b1d010215090d180509040210050403020613031b030c060f021606110d0e0a120f0f030f121404260a0507020117060f09070207030218010602120403050a06050606 73
    0x1a00285182c0350361455281c0e22026407031720105401d800e1034401c801d13452070040b040d01d80141440506403181d400b00320500b089914403a0801c0420400803005844440c05001c1c0d1071810b9a440022900f186401340740d0311990400305202d21452041040810b011400d020121000350a00c1c2c1d09030a0b003008100c1c14844522000e64025403d00301c0020044d034051a590500c101c0101034a601e10366100c4100c0d03c5200c480c8006078402c0f4080b1044c8182c2030112014500c951082801d044446201c0d9a841980c1c840d000058011400b50b10400c261190801c54018031032000782000c0020001c2407422170503000b4060000b520b50128a002008014000064040300040b901106501c40d48184402440303070f400a60104e001809514a0104403403040d40c84034000e2400a044070a8030543c0e506114103d0700017054082180b140500002c00342c2c4034a201a88440100c804a104560503d08044e240c41400311010a0703600003080200046900480e0b00038481e5030015020815407521400100180280c86 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 504588902 1250 504587652 504587683
    0x20d05011706010803040303050909251d0303070302120304060905160801110306060a0e1306060e0405060d031b230d020d050a020706182105011b1d0102 67
    0x10000308209161040300c4981c070003008101c0b98107a803192011502da01880c071004011410900c500c0c10540b03846912207504c00b50a0404402804a041c0aa20350305607409414002c40c8a601000800d05014034501c0c812792030680c010342ca000310b142e0b002580d4026003034850541034400700110b0104041d6801951803190000c04440c0440c45020201494626a1256812640c80c01030164105594402520300c00d00004060380e08040a0090035592174084040c65a40035148242070815000584101d00c094049680e030082c051860106100848402030440c911030722180b07441a000a50000014014180c045017001c1c1d410850728008183e03034980740540c001e014180d0514030072403400088401d15607405038220765864030780b2036040e1418400e111a100068015020500415000311541003a00c0750380402c03803040c1e82d500d111605002e11000080d05102d804905240c0901409010300130118852480c000111f0a00c000041c2c03210900d8080d0102140800100b4040350303009121155000c40b414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 504590152 1250 504588902 504588911
    0x8100e040305041706070c030f03110c030403021507080703050706020c060712050a09051c090b07080703080a140609040201031b0e011103040b07030e2107030c0b2704020d 75
    0xa16000d400e0b504580607000d25a0707078083d250420381c08001045d500a4031580c50b8541084140d4404480d110b403100c1c2d00c501415102c907414024540324500a082c0c1c1040c031000381d47c440782948100900c60442031113201d0451303000c1c80300038081220242240c907240c5c3c0c1401c0841e9038041519102020f401011070320111801007030200401140c1008a61240b0348a9039002c100e65075074100404c040b14800340c4081c069622a920321490881001141500714545062002210b592440c080d403d65029000440741c00101082000806410031042504208a424148844030a500015043c4200106418812040540480d0959010350300099511007504102c60807806586000340c045910b10314118005540d50608412010000c0240c4080e038034016609482e2428a031000c0361008906900c0d5075200400c12012445040070841e076502c156402c4003e441d14502d142010020460207500685820342d080181d400080c0000b070f000c4071203100e246441500031220f00007140090043d800c03500282841d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 504591402 1250 504590152 504590161
    0x504150b0d090311030a0903020402091315030201090807080a030c0623060312070305030f04021206010f0f0f030f0b091608010f0501060f021c0c081803070506090a0608100e 76
    0x8a03000340c04880e010f61034010544c0001041c180c0e0b00e204500c2060006800c0040620042c50160010123507070000a0600382c0c0b450b15202e4820444030b40d00c0307a812028018090810031942c12605500040001c840070780411843c0801d56a180c000481000b010040d00020002c100a01580018041642c041c0449d810001e0700b82109107000342911014400c0c42000c684c0104861040c0448510a61655030b460860322801414a8007038800f42c82240e0060032014803460421707003005040e0080040780c0000e1247e81c80c0c500c5008054003242c11031000c0d81d94000091021800c0020032582607584444004007696075071140700e003401c061050000501040b00ca002482003015040200d9950100c0b000b0803050366101000d0b1808507058000d4000368000900e5040f400442d004c6800380c48045080003100f145d40c07030703480ca0030990041c40001c0303040da580b18441c00c0300d050420080d40601000d441c035a2605280c100014040c0000d88660410009103100041c0b603c3c0d1780b000303050010a11000c0c0e000c1c0d00d080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 504592652 1250 504591402 504591427
    0x212030f1b0f07080d020705061f060305060a0b07170a0512062b050a15020a0e18160c0c06030501031205040b040b0906090d12020c0315010504150b 65
    0x2019500300c00302041c00495040301148000c12103200b040b000d02e400b46060080c2d40e511140743c00c00c1c0c20a45032998240709110200b801808280e1094001030084048080b1401c0714090340f40280d040b201c01c0604e0201040b0003600d609d40c50400380c0708030148441d200c00151405152880100814144205001c90440b0859401802a06802c51441b403031080640d1203e00340010003584207020700d03078403000359000d80d20507a0042014280038007030803d80b401c0c0782c40e0b40c856440207800f0040b00008181e00080000502d50b002d0462040d00038100e0364040c20083c405040c3e00c00010143c100d81c09141d03210448540700340111907241506900039440c2c141f2598402c2d000d0020082407000b5209981440d80c488030091207a8200c4058038050b104007814a8140000c182c9542c003c480c015408c004100700070710032943d0f414564886580304408002d0840c2c4040030003030a180e60a418203000c0c0d480004207814800062000505580c0d090720700050100a1000010039100e10358880d210789a40041c48602111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 504593902 1250 504592652 504592681
    0x20c0a0b01081b090a021c020301030308010e01090c08070f031805010906061710020a0c2a1a16050712050c0306010b0c060402010804060b0604060201020904140f040b0601021203 78
    0x1001c40003038844900008561001d6103000030100c5921504210004000c07002c0b030380c0588500350420500b2481f02c001c0c0960041207a00a802c00d07070100f0407440041050641140c00c040c00b41507004004d1260114482c000f80007014090000300a0100f1050f42c800c0741c5109500c4100807403200080c00c1c0c03074845d080c00c1040c02404c005900340d600909004010558803204200043c20754030000c0100340100301c588061b4001d4101c0300c1c01c4410450f000c903092021a075555446400280311004030302c030301000280540d91004079a400441304100c0090300d00201003001c0141c81c40403000c0c4403030b0a506d180c2c6203080340c00c102440d0030242c0e5808441d002e00e400c1c04070010722440c950000394119041a62140c28455441c048c81807540c3d42c55215100040055100702c61081c0c015101e054007003070700e0705000000b506a402a8001d10010f039404030380c030703c0300d454140100b80304007011143c00307051414150a20350442e00f0040015022030804800300740e80d40d00c200290384810108901c4280c803400c10220002500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 504595152 1250 504593902 504593909
    0x2f030a0e01060b040306050a110307030b0a09151a0c0d02030c15013203011a09100e0103031b0803010f051315140a03050a08091302040f18020c0a0b01 66
    0x24034203050301044210510414094503000c01c05542400c0c61942e40401404005004050160311541c1009100340f201020718001d10700c3c0d840100718400590140b103021180c0d9848410003d003030130307283c1a044e015001c0410030780b00900200c3d094807c20390750b20303640e0f4400e000c10a8801c0c440e458112a40507404006070242c07904400a690072102240303105068100280503980c1c01c9650305000c0034071541800c0a48206a07541c840840000d807007000017908440307014180d6040e42240040a501518010b07108507400003449480e50011070070407213158507401c8140402410300c00040302e12403205030009491003440c1c0d84141000d41c1da60315088043c5000905106003805204408002600d01055026506040b40070300720114105141420081d481c203070720340915402c0642194003202140c4d041c01039041a501459800da6543c22500c10300120f01d030100c914020091052105010180003543c02004075400d40f140c100030310000440d6100207102f401e652001c288220040101001600c00c010381c100e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 504596402 1250 504595152 504595171
    0x160f03140a02040315060e0f0a0e0d1e1b0602220308091008040515060a0b0c010617030a020709020a050c030711010305220b100b04060c0615080307062f03 68
    0x1a6170550302182c080c0d820b0750141d50001c41c00000005c03008410003507030341d0b40403c0c52440822003400b0ba42c041414400ca80500c0000a00e05800e051200c98100b180c80d010180ba42c82c0c031801c2c6034050b100658a90045070740c000c04d191f80004000c5001e1402d20800e03591000990001c03c0d0b2640d89180c421030b82d5000d0040b0600802d403404441c5d144034004c038a040d00c503030b4200d0003804156140c1c9002103149807000f0040d55000c17244020100e80d15610a0140c84003105410002078560f06100301e001c2000b1415001d40d5480c2d1080006243e082e50100314003044980001009d03850315040c2d0402c1d910350141d002c48402503c03011031a0028400c0b00f5207101800b0301c0a890400071501e0302210040707511401d07420808030b0624521000000b03031280b40038507031000701c00c203211010684441808041d940182c1c482c0002485900242c800d0140a100700c0e40703000101e10140303800b245003054480e180c0c029108068451a0365030041880b41d81c01e801d81c07911a5981020010b005c0c042d01000100542041c0c819000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 504597652 1250 504596402 504596423
    0x302130b100e040f0225080c0f07170d020d050c1c050d0c031a0906031e0601031217190906060f0303080604060605091c0618021206160f03140a020403 66
    0x41124940c400c480c06031401c0801e00203c6c098421030501288850031048440c0c442c100000d04e100c04061003680c03581c910305070160420624085200d010740301c201c0d2820308140c1000c2c0c3e00b60715054000039048509281c0e400c0c6142c842842800240c00c1034007005540c00c0d01c058450524524541c814001d00b03d00388080010000c4181c1407a04138200d03134031240c07070500441c000946240d4516141d0262039008100400319104003a070148081d10a0703000f50060070042e03100e100140100040f110620071b20240d40d140c01820750040801000e00c190f009882c5c83c22003800e4030110003e40349260000302099420040038400c5c0e0b60385404400c0c1d1b07a405803000758001215107012451034907107170145100f142d40c0da503100d030301b000144010400c2c58030401d03410740989440344000340e000035014060391a803e030b2200709414181c052801805203840d04441d400b18660040b00421000c13401c894042e02890b01d0500d09040c03000e501e0a8254028901c0714015403108081c00100b20400e98150000c20699104108054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 504598902 1250 504597652 504597671
    0x90108042628080403050a32070203100506010507060b060d0e100609060509270a0f11030607021b03030d0203090307062003040323030a05060a060c020a0302130b100e04 74
    0x2202c2d0f05007034a004000070b500300000c0581c9403260072076004501e00c906070380716584a4044101d118851f01c412003501c1e0b40e03000c1150400e602d0144100c50405241c01414015840c0c400c0001300b0700c1c0328511000308402d50700c0b10f2041d1140c85880603102c80c8210f001c4104684400d02260fa50359101056a0703803d51130a040000c90900c810340592412100c000e0101d1016850b08110054802c5580082c010740d03180d406541c59443c041000054007040c00348840d044032040034100020300b42050102d140c000d41c400803e000343d45a0001e18a16402179000321030040d0ba001d0000241148107507050194080d002005000844002000030321109106110400030901032171450081c80188901c00f2034204828800034011900030545290400b01c0412002e4610030b10302c00c880025041568800403207a07403041001100d08122590390054150b500b040c01402400fa030006040e0f91050200a008513240c0030468070301100b9401c000070429000703080d42009040000c1c000d000780300b00040c943c89079043c1110034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 504600152 1250 504598902 504598907
    0x50301020c1612020612220f120503090a120203190905091f0e060105040e0103030c1a1017070e040506040309061d0402071103071707050303090108042628 68
    0x40f21103a40601054148010402c0c400c1c1910780045c8043c101c001c1085200c0316210014042c001e17203d10038440d81060440c182402900761141488000600108000344082010001000369410354010050490f04d020030000303e041d80228140a03102c02180140c0e00b1445400400c0c00013a100103440e00e00c415500c1c8078410903003003101111041d090403894410b118003400321080562206040c14464a010794514800e206c20f00242d005a00017030701001100104503114078004031020006008150a080c0681746038900e0285202e141d01004041b42d030b10140640171702c484401800c44030703191403041c51704d42000da464032002c036011400226070000102d1030301d00940d40d5080c1e0891360015124180030440911001394003140c002c0e41c3d810811400000c25540030000940030f440c0500b00d0020075004a0340719071800031b103a00528420341060000c00b88590340306a40d180c0c13054209520603003003030710340c0b01801114984141c10014031400141e0810641001c9010440201e0758003092000c480c80c00808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 504601402 1250 504600152 504600179
    0x180108160e2107030b090609071a07020d05010c03020c1501150c06140115110604021003050c07051506010e030c0d0201030c030b060d06090b0a0f03060f06050301020c16 74
    0x100d004282800440003440c20800312002c84180108502c600c14810100c501d0f1800312654801c03168180c103030041250074542804007940260b1160001e01b00c1e0750030320000322541c80881e0031540c508000428500c3c10b660f126000e00d000c00c0e412000030042c500042c2402000780d0700c4102d04030068130501c1c4850740740c068800c56080c1210740c42c012001450a40640c1111651004039040e6029031712401041001030402040600810780551164000071b03e45038054a40300805822846070740180381000090303155032202c00c90b1180f852500080503540c1500c54100c038000d00c1005440f42c41044140b44240c15001450350140b042600e4a448003034050082641c0c0d0040450400c0e040044003641d100154000c2c3c000402d4000a4180031680c22001d10202c2c005810155400313030700f03986941082100182074416445240800d403000101d60341030402a80c081f42e01740c440104690390b0354002c0c11030000c0550200340540310050080d03554021050b01e2540d10a6114406060140341c40c03030008620000b01d8070f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 504602652 1250 504601402 504601441
    0x803010305060f22020607061401060908010c021b03160b07020f040603080d1a12100e070614090a09020301090203090d110c06030a061a0409060902160803060114180108 74
    0x2100f8000c130300b080104403d05241180101d800000502600b0001461800f9a214800b80d40340e04210640c94110010000351490f4020842d80e4501a24040c0c40da81c0859108200c1c440410b8a12004000c000440d00c0d281c0e0008200e954983d00e054089600030781e607401080080e0080b17480c00001139540003040103c400d103101c010860b038020030442480e0401385c0c00500c0d894000041710310381070340114003265003084803121045d45600480045850212248101e5268100c06402800c1c09414400041d00c030400c690041c920095000c1100c481991f10551000040c04043c48295200c4d41c0d04c000c154065001030710103d200c1c0c084c019180c89602d00c1b600c0d400d0500101d0700014080401d42d4002d0001036480541060300d819100d2a000c50440c00c001d070065001400c3c40d4070143d03154a080010411201c054102461440c010002401084e0440c90000c81c203c2c0c001106030303503907110341c00142c442c87c0c04220f050508940201e102081d0507505107015a62620a8a446409548060904040c00c00059 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 504603902 1250 504602652 504602671
    0x30406080601180e041112030408191101080901020f1305010f08070503070509040603050604030c0519020f060a0e0409031e05160f05100504080a090e09100f15030803010305060f 78
    0x640812003001d1a43c1c4c081d40150040c665100b40400c0c4001040c54102d520300b903401641d100290030041101c003089004c404480d034400e141c1c00050a0307601e0545070010402c400d410003005401044a0071000c1d8111424804181c500c240d5903900d441d407076901d803203c1d807007075501058030011194805030064640f14440ea00c19039556186544e000c3c0180c0380e58101e04142d641080d42d403100480000c0003001160f02940c06a22103020418292420900d4206280c805038080104285101d0050b240c08152120004049500c1500c0f0024060308803001c240311000982e1240c1006a00d80c00d141c1c01c0300b0f1561120061465100c245c100301e041c181d505c1c7c132a2860500032540901c0420002c00e10180420313846902c41c1040e02d140c4101942400b042d207201340e45c00da4100c44002525110b654000030410024120704240902c9890a480003030f481d00c0811142417a12600ca44640240c04d0041e03021951086100403041c40b950f4890901410304e4109000c1200d0500c2001e000c40d480c480b640e4a524400c21165 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 504605152 1250 504603902 504603947
    0x10915061407021201051b04030302060708041a070e121207120c0804060815100813030311070503031501050405060d1503020901080102130e070c060b03150702030406080601 76
    0x5039003198408161903040001038414880000141c0e0345a44129800030124000714640c14a02c2c040c014907182440c030f19004550410003040043d4003c1342d40d40e0b000e131040c18912125912814a4003069120a282540ea40c0c0d050303080040040d040142260100010f0364443c07441da10001d00f160f603500200304c2c4040120014443c000014049801c08054101c0303d251108051089583e440c03110780182d000342c40452844002c01040f92080c441c4020590700450700c103866598070040107070555002030301c009141303212104031a003414005e030028001001e00a544d1a030b5000c007810010340300d03001900d945032030829041407520550700c2042514140d620040c10b541c40c0c050881c080c58001d12801c0e03401c00d90108004c070000b0240e65005a210b008003500d80015a407600c20010140c264039182c1c11402480da03098003406807141d07120f030034001502d80c0840005241c0000d41e0002c1d181410721450140c041e0300708420002c00c03a50100240003110025140d403117468440000540d1681140070b1200940c030020b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 504606402 1250 504605152 504605159
    0x3080c161a03060d08030c0a0315031a060d0210020d020c030703050d050a1107090b03010b0904030905241605070b09130f0905011b12110406030b03030c0105010905040209010915 78
    0x40744000e6420840c0101954040155540d845c07040e03070000c46a0900650020801c001000d816001d01c002001412201500040c21961242249104142025000c003902000200503464031039900c5580c540041030030301c11404600000790340311007040703e0000501a410f2000898100091004180d9078040050400b000c000350046072617402204e11002001a1650b00c10b1110005026100c007801c144880426001c1c903010034182500e9034055114002c00c45042040f001c80c0e07112201c01d054403c111200032003548004400582100c940c200c0d40d440d40760002e80040406040c10046942c1880380d02900e40855540c2c0782c03c1e1a60281401d4150841c07006042244e402840d9445100f480700030300c1d030005055405440d03917030846054040081400e6100034440d8442a0040c10a81c00c2105502c2c0612005504c6e00007d0310b0390080d480741c2014152113000c8038025a4043c03040e1044d5503822002003080b9a910207501e4040c0a00ba50141d000d185c1010020443c11580c2c094016104030001e00c00000924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 504607652 1250 504606402 504606449
    0x20d140d15331110140f090319140408031605010b010c050307020f150a031a03010605150a020a02092a0708030412090f0f1403030702180a02090a03080c16 68
    0x30050350361034070360050303040e001d07500013540c82226160200c1064440d41c0c0d1416801c0078070300e20009000d40070950b100340a9008022204191020925500d140020201e00c02c1c054200c003030301483d000aa0070340804500d40902010828040d600d185c022802404800310032030064644c6d50403c1000780141d00f0800c42c41c070150030b094461000e80900940a149c44403c010708a100c0da03008015000700003034441d81c2e220b0000c0e880022104507074200f100200005468000041e5018076400c000070f4030210040382038048036000384056590b840d00580303214a00c0c6050200112a466206180c6030362410519582e0103056003035040c2c40d00b0300e50054050f4034540740e5403038112040143da250842000000e150228101114441e060300521410071000e5000b410045900e45c2c5510082ca800d00a500512840c009aa620407280c0c900b54030802801c082038484102e1000139200e2459203a030489460140001040300d40300050014210180070381b280301541007181c2d2100c120078491085001c0700142d40840030903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 504608902 1250 504607652 504607667
    0x801060e0a05040c0314011401020307060f02090909030a0f020c090414120d0c08090c1f0c0219091802030c130b0a081609020a020d140d1533 62
    0x103900500c1e44025a658000240c01e07030300d00c2d1401c0d200094640412591912034171140b01e01500c0119400b420588c58500001e562313000d022405019203803540c100b40203940302da41c100d600c0f0072710161210b10706160004280395264000d900b400b001400141e030824000307201154080c070b0080020056011600c850b01c58000244207000000c080c1e001c1c00181070198440e000080055680e48103000c82c0081c0030341800b0b480854001d00000950704101c10038105c5950301c18194442d03251060300c40c00c501811082c116441c07002c80310300039009510f40040402c1d480665400300c0413208844000e000112142244120f6104140300094250b800140c000c1424600070b9480c1c034100c2117604001031000300316000a11203000c0c030f600c481070541040100700c0c2002031240701040900244a01940b8000d04403030025941c081d01c10307840c2c08000700c56a42c5110b05008a0481e0208502008248034100e202c0c1c01e83c6000030404d02c5408104800480c856035000c4031f07141c0b5140c010642c401840d408078451007055508a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 504610152 1250 504608902 504608927
    0xe09030708071407060909060b07050d26010801090c081b04020f0d020403110405090a0b04020409110301090b0a0b0109050f0906041401180f06030b04020f0a0819051c080106 76
    0x30100c0300c182c2c0564103400c1104d20000d04060f5500c2d400f680c40c040d192401c0329540d8201c401680b9081014102184000038402c2c0103901034904046d481d0034903502421054241e44404070607100c10000025040701c15001245032500404200c05090368903039840d80e0302c0a210f5505800e040d40c0502c850b00ca85040d9025080c10350348481480e00e4804800404d004036031180c0c104903000c40d484000c10319181440d00c20503500000080003487c55040c940c031124001080140001d104544030280c0341c00f00003407003109a4a59801800178004c0c00742c1403420704c4501c4821582813403800e01d4003c00300c100d9071207a6000d204030b501c00f4103040e0b940b42c1c510003444020407000300503640260f00c43c07104548526014414078020124446403203804801c00141d40b058030442c00c002590603007429018804034450310030071500b06904554078100c01181c43d0100c0c0000d0398a40c0414400d000e038408144601c0b841c0e22000c1d001c0b070303c6030b0251070341d04044c0b0038100e80384e002c12522480011801c00062080b01c2c001d09012516 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 504611402 1250 504610152 504610163
    0x21b0d0e0a05131d1009110a05060708070201050706050c03071d01200703080f0a0f1805040207020114030907060e1008180a080a030b12010b0f0103021b0a0308100e0903070807 77
    0x4081d030102184d441c1c84000019030110ba43d560079400d0500003a041c5040c58024100c801c0304103586808001101e500a040d405441d0341c01c0051a0421a07000308205e505240d800482400303140713043d1600d03030b05540040360148085101a101c11070315100000b440140402c050f122800c92210003850104100d4034a0780e41c180324400c50501002049500f070281c64000c803141d000c5035032400704a41c010035901b12807440c0414018040401504080405000300903104181d50050b113418003400104d031200e2001e0b11160003142700100f84100f11710041607607019200716403590480e0138940380901c1f0f09034003003009003c000354200c3d02094102d0a500120300300c0010b10003c894049400d9200d180071544040b50030008203555480d00f480900701003840b801d003440f10000801629000fa4089169207074104409810103a000890158542c1c50070035100b0003c0d075050484241042c2407802034010001501d40c91703c80001c0d80000162205002d030028840d0b000000514207000340d0341d864180c81d03003024508980 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 504612652 1250 504611402 504611441
    0x60c0c02120a05103912050c040306052205060a060e040b01030b0c04030506190606170705160b0f06030616230706020a0c0210111f021b0d0e0a0513 65
    0x40700b0042e44a50f142e003403d0b0180d07107290380c03840ba0070286c4400c40c0104a85100ea081c4410841c0303242c1400c003079804590700241c001c034141c0d442c0c03803500403190001e10240d10f61030350040308441440000240c841c130401000004020320764035129000507002c0103c40040c03980500c1001800003c0c2c180a1680d00429000c0070181429100d588146c10b007038003200c1c00340c20807090780c00b4603511482a0040000030070090400c1a0a02131202c1d08000c840710041c03240303041c0700000a00b51801240851184038580d04060000b5403420100b0080181c50810f88401c1e11030722554010a00003018039190915844560303c40703000c080d0000b90321240e4082034400740c2039090000d0180e1000301e40f1a000504500442c1d54458507000401e2042010030300d81c004820040065032513292440b01c10001c2d80301d4103020704a04401c040000d6500541c0030340710303502c594440040c1105281107030000000e1003201601d4680c403020400b2007010300740070b070f603900510605920002403100789848404650011021900065105030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 504613902 1250 504612652 504612701
    0x80a020904150e0a0602030708010e33060403110324010311031e0a0c0b1c020702040207050f0a11030a200d0c0b040806090f03031b07060c0c02120a0510 67
    0x44c1441d8001100390f40250f00001040501c07540710300300718007505482d84600e0342070400142c11014194007071114400c180c06503081c80c0c0c0e44255050100e0b44180d0051036541d0f5107899241030f0a004120a404030b0080c8200e5010a441030350582c2d01c0115602101c1864141380c4c41d646a203d80c84001d6441c880d014050505050404003064042040c140700003802850940c00030720741001310880300d500c0303040008030038051100c00d030100714110b11003908628009602ea00d01800003030001d02c1078480003881d510512003070078030404010a03861181801044507182c10840e107403c0c951501152a00100500c0e034145060101d5070700e50a0342e840e40040541506640c81c100c0c1e0f41d84242c00f8007074100301a0008003007020000304804009050303104100d80082e080030b21500d80000c0da68007018201040c0055080424a038072148902621207041d00140d041c0030220780304401514140d01c4900071390003424101d1640000100014807088010790009c01052046441500d083c0140140202c20040110304281079 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 504615152 1250 504613902 504613931
    0xb09041e031b0b180d0816110105091606030614060d020d05101401020102040f052e08070f0302070b0c0d06180e010e0d090e04030e10031401080a02090415 68
    0x5405840c4120a1001c09040c80120159513081c107842c000e8056108860115900341e00000311a044442d003c1e00b401c1e0354001c580e09882c06241c604840755103620707050800c00d8018000824026401440b01d40009031511050101c1c20303500740c0d01070b103900010000d81d00500c50408400825030321411440040c103185404d010203054603070a0b41e81c114160301c541c80c140542d21006480b43c1500500b4002180340c2458807200c1c3d5040340032485014480c0702e844071a502111000c4019a8102403410026940008062000380c805070040e92001c0006010100580c5c1c094000d108440c5502e8114420285c0303591010101c080b154004c1c5248507100781c80d401d0000342541e42c030500401003040348001091803280e07440c07118215012045507028a03030040016440094000c8583ea01741d4841a00721821540c1d03070f04094a0150302100e89940140b030555180e20110381c191f04c0100b00c0944100b0307855050343e81d80546031b51807003455400fa44c800e2100002c100000c01d0b52076034400b40c2800407004606c1101c4c06104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 504616402 1250 504615152 504615197
    0x307082b0903080a060e0a0c021606020d0806181305010f021c0b04020406090e0408070b0f1009051506090f09180d08010315050601030b060c0708010b09041e03 70
    0x5504151a00c800004140d005151541e0095030304c0801c0040c3c030301e040c1d0450b105810140620108950300c8110000c080d100b40b161054030340080c514140c11580d50000255a155103088100010303030300a0204a10b0b1415140d160040003440c00c070300c140380e141c070740c2850000031161800b02d03029135072400360300e08001160000d0610a0100c003000c851200c440d020f800c050300c40e00d0341300500c1903104100134405e00d50070803c010143c501514140d0b0050f9264600a003481c4500c8030701808110461080003d50020030603564800e946502000c050603580340006400d40e001034401d00c050200c0020300102038100000030301541e0340010f142da01d0403000c2e88003041003003800f40c556010041034050109038032601045100344004030341ca4460b05561440d112116009901d01000b1841e0341c81d40040b4016078403d410074450780030000d10280c1d4501c082d0b002d26945a40c2c0c0e10130700c02a075003000d04c0d140c568034042001c24456034005035032500c071202d200403a08413000201070032010b110040d030442c00300d41e80c0c2290 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 504617652 1250 504616402 504616477
    0x18100312030608010e0102070308010308130b0301030f1e030905010c1b0902070c08071202010e06090918190b0103020d0c0f03050c090603030307121a03010e0606040b0108040302030708 81
    0x60004000d4182500d00c0d0a5660711590745d20940e004100c81c1c000aa070041c0501e044a4000c0d455948401034018080c9056000d548115241c000103c008428001c085443d17040c490b10a46544c19020503646084440e00c82c0e070701002c0d02003131079994200f00c107500038450031202d0752080320b007400001039589094030f8001490300240303049540820024200110712210102500480000303103a40e925002d40d211903245da0345002810071400b0980081607469a40035204401c20050640c245450041c2004029121802c40511301c0e2051012821040503100617a18140b60440380405080e0300b950244043c219040b4000c460414220000040708506640060040c6101c3e102814003003821004102d280c45007d40228803d410400511101e16004031510102c0001007a01198400d400c0382c1c0c3c0100490b44544c02c640550030300c42c150f0306442010aa192107418111001c210407288400110f440400444008006d40d000b046003402050b160000340c40059080e4415403020800300b910403002554030807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 504618902 1250 504617652 504617657
    0x70e13060f0903140708030a09080d0e1f060810020c0307140706080c12071805060d020301030c06030509030a032703021f0509030a050705010f02031f09020918100312 73
    0x28100782050707071180882510750701c0c0344c0c0031034206101078442403100d200c040c0c183d0a282e551800120104000881600c014480c040400c20182130008444d80c0c0714811013514190592140e1051200d840061040304190303107603000108002d01904a60100035402440d80c5640c2d44414032507000040c1c00355800100c04000c0030050101140f80c0040940f500b8406415510900c1041c4a280c0d011107030545041e600410a20b002844450901203c40c4842a00d401050f000400010303910702c8014290001c40c1204d116580410005588450441c208c1d441981c0a04440d04104840014140b281c0c11039410070b60068000000d048400722180d1040030107010403405608517500340d10580a099040c0307050006682f0042c0420b01e810480c003510b0307208075209030050100124540c024050700b5400075118046a240442d503e05002c0c54115a000004907a011665108000451241c0c024000e658461001904004403803000d2080349140710710081ca520707a00801000000049990741891645443d481d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 504620152 1250 504618902 504618911
    0xf040e0712050709051509150a02210708071b0f12050c0108040201050904020d110301032402040b0405040209030c180a140103020a06050a02210d0b0f03070e13060f 72
    0x4400c00001d07102d000741140240f16403810300f000180c680420940d86030502c04d0444d9a1400c00100141922401e4100030290900c040f80000c1c0081d00002e50f03006100c40701d03d0341d04c419100d02d01035044912600b14020310071181800020002120400702d04106404200400306850721401621500c045642c00721551000c80d48002d000e00c0300c2400400c0c214582031800c0c0c9a40e14180d0006803162296540035802103500040884201005a2140d003040001c242c04079900c0d6981d0500044c00e140c6040f1024911302100300000104016108407011a070040340758600f014038040c1040020f4004405654250003130007502d000c0c0382d50300042c403500300800c518200e82c0b6040c055140000c44400c100c5a0480d019208014005070303403120000001c0303848926003155a1055005c0881c00c02ca110301003144a4581c0c1c0b0034207014051048060f0068011000d02041401d400300c040080030b05005030f09542503040640f060000c1c00720f4000b0190300c0304a550080c03203d10013955070807040b941901080e50000382d64 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 504621402 1250 504620152 504620177
    0x706090f02041a15090d020a031a010602031903110c03070317060406120204020705010b0d06061509050d060e01021b0114010e0f01171e030c070602030c0d050f040e07 73
    0x1501c10740c0411920000f1440400d0404804074883d00103600380d1100d0010046124502035540c01001e6484543c05858001259640d20f84800403075442405940d85918460021034680e200205490103003804003c041d40344000004250014282c0810100c0300400030041056450001c100401c00c1510a40c1c4400380c24130100b00004805002410161080e4104501080700c401141c0340500000e4040310010380e50202407400500500418040940120000c0314107414000c0650084044075aa0000a8400b1944d9201124840f0b0240190f640c45a000b104140c0400e24039408210744050101c001441c00144691031000301a808400703410a0791282c2901c0002603858810600500191070549000d0a114000e1038040105020701010640c0540088814030802c0245d1080e58850380c40800703221409050503600c83d170002003500000e120b01c0030006102d81c4000201d800c581c910201804d50311024841c200d07100d81c803e0005409044050101094042003240700e00e009420b541c8440010018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 504622652 1250 504621402 504621409
    0x20709020417010e0d0c020f0604091121061c03090e0c0403021807050313080405150301170a02010801090e030c070e0f0a0905100b180405162403110706090f02 70
    0x1144ca10b403165800110b120070410340c00c14901a00164100c5651550b03c0602d404245035004a900c440d500504180000c00c52154210040004502000117442083c01010205400d144141d54007500b20260030000400f0b004000200b1980310710038901900b185540720001d030701c8001c042e290380c2c800000000d0100114a44488001032100c81c03110101c00300d240044001c0c0040c003005213846a80061000648104202c2e40c0803a03002e030500400c1440079011a040c0079220340c009004250f403171b80b07021200f005d844c80000340c4040e4982c0d0594400c02160b00b000e03c0b1b203000d000200005030082c4004d02540d49514024410b10700a0411202c0441d100c0c074200641e40710354030000d08408072007494250406c0c045030000c81c40c0c80c62140340c501d020031070803420350105d01865010000c03a519110910140010481c000c41c064802e40350440714207080036283c100c0790500c42c503805040b40c107004d042118600d016000c0d030000006020500f070000d080420740d8541600703032021000103e40380f100ea000d00e4001c524 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 504623902 1250 504622652 504622661
    0x120b071d102601080304150224150108130204020c07050d0b070e01090f060e0a0902070b040b0601021203010302090c07020303040603050105040f0e0c19080a08040e1602060c0a02070902041701 84
    0x98208002c82910351401c00d40644a1165008074035030341030a003012080007402003062003a0442e012007203005252000c050048402020344601c0c4101c601107a11042c0f0b98071030385c0c03014050103044102140209444d820040254480500302c641c3c2e00400310006100ea0b92045e40522403409504502000d10340101c0003880030304d4640049044c002240403d01401c8030b1000c1110646580382001c0032498003100c0020405882c0307500032240345000051510401006100503401039104d0a401201500d5003001a600c51291b01081040b40c0d40034001000549404032050790824211285a807800304560040380c00d5a0154101e8404a40c40300300412007802c06126444a001d81072108002429945291549550100d140c09208648190060340c90075249603024009044080803540543c00500d0800f03615013080c40f40310440140302c070010740c2c00010f96409200270160f40e0f000d400559507401880559400c004c071208110b104080300420b203003403d4030052019100441891241d035610304d10711829903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 504625152 1250 504623902 504623957
    0xf021903090b0406090317040503120609010617041119060206150a0303030507180f050a0905010b09090a110d0603050c0109080c0121050f0f01120b071d10 68
    0x1881d001c0204041003850052542040e80590301144100c820304080310342130f01000d20407410807203001c18003003041400030040c401d40494601840c000d6881c03200300643c50304248a03240214100c0692241c9960f90b1a16660703005119225600c591454a008200d0004121102d10f80c8088010342c18480a501005140c1d888844004a4042032102501285424020348001001d05446802141e013150103000503100050f0302e002078080302d07595080344a0b0041072902c103035030141030300f04800b284120041c011030b4160303017440c80c1442c41c2205031010300816490060441c8003840d99000310050300709e1800e000b41150100000d02240a60940c141a828501c014218038148600c8240c200078040b004961428804024200001c1c440c0035050020101e5040300d01c0d0203000c600e00020050866030300c400180c0110206146110680e0f02c1c2c03a0718680083e1103090240819551500142c01c05104000c0d40b12111307861001d0400ea604014003261403407903000c3c14100890f041c0f08038020100d1144030b428041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 504626402 1250 504625152 504625157
    0x51306080a02060304020111060a0213060309022b0c080102072906040c020f010203190e0307081903020706050a0506091f0513020403140d0e04020a120e0c040f0219 72
    0x5894810000c1d56054003520090151602000060641e80503600115181c03523864281c849034038100d40c500000358802c080c090f8580c0c2e2265004988984244207049950354003400c420022076950403800400307001200c811030180c610680c01800201c0000c000d01c01001461700140e01c1c0c000350300e40390303007258a00c004c102c117505401d12422251440d80703924540c20507003d481c000ba8803100704400f00d0403d10265040880c540c00042485840000b10401d541e03496800d2000300700c141c2d018a80d41e910780c45460009070112409121301c0400d0140a0070000340b600720f5003001031405039603698a0003514011a195004141e0312002c01c901410074803c070642c49201030560441100741b0350703406040300c07581d405098041e441104100c032a00e41243d040710081c640065411043e420083e407903603500c900f405a481d000580d41080d0000c2800c3c28000d40b003051a403030701c1d004035000003501014000c26080084a40c14416070a00800c0c0740c40364490315050025003e009a43d42401c811458956444250840308 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 504627652 1250 504626402 504626411
    0x708100623100e041406030105100602100b130f0c181a1c06030507180606080a2013050109050d0206030415020c06070c05151b09060d02040f0513 64
    0x1041d50318400e1a0010307407080ba9555484a00d81d031084071240050104a80c01c03e02e020900705164844001c024881c4408800038001661407c850b042e58944512039070340960703c1107000910301080354015191070b44004d040c92400e14012000642620600030002140b56500d41c40200300981c401110301d800d00c000242c0c41040c03031070709140c4203060f4440003000c01024008244400c5c030b5840120310300c03503030300c1d0080e401e001183c5c5a0400689943c11442003100642c43c1ca0445401e0007003a000e62800c840355516030b120b00f0354806103641c0103041c82e2240500c40700c01000342d04066080a4002d0240303800006810601d090030140050301805542d08810b1150300340039002030069482800f200da010b6070107815010801e20321840f0b0320183c003c030002008076010741020050b901d0703804200c0d10451070180c002c072013030640f107030310700e881500802c0d2409840303208040d07034050848220000408510901502c00342c44c010b429806001240c01c0307600b007802d01e6490810300308881c1c036201c00d0304950710146400070803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 504628902 1250 504627652 504627689
    0x30506060a230d0608101a0904020f100e01030c0207080304060f170405012910081315020301030311060c090f0609040513030906021501180e07081006 66
    0x1622030003a03541d81d508201c0c0c6207040c0a103403002201c12200441035019650307211200401c0d6803001d0850750041104911034994103070b02c000054003805035402c2d07030741d04070502d0741d6040b0b0180b241c403600050060780c0002004c055250152207101440110000c0765582c010b054190200040c15502c03032580101c1107600403003090010b11800300c03c071401c0300c04904107500c0d10a05090295520980d01548444161074041000305110041d000b440c500b1954804032032010740c0c5030603458000044551601d81000c6920203038000e1a004500041d040062140d041003010710558403000b90b0401e039424034a1058010004104041c1c002a207030502c80c079440040c021030300d080141d64586000380c009092191450315101d4905464003030445005c080013900c00d0100c1d141640c51880c8081503290300302c0008010641c0000c0b0b17644045910300762040b03418201100d41c5d02e05402055025041e401d11524165110700201034017200704000c0c002001600090b2080b11108040b0000700d4015030320201803003001c205880c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 504630152 1250 504628902 504628909
    0x3072a0806161407050606010305010918142d0d050a0537020102070309140a06110f07080607020706030b13020c07090f02090a0b091f210203011401030506 68
    0x241d402010900310307500d9007441c200c0c00c0783c1c04114040300080c0514001a0308050080104549100340360a880030700240c0d9940e00044102c4150162001e0030b6103524900b0300015a0001d401c0c0c0440f17504008030303070440300207048945074007014910b08540840c2850621300c02204c144082c0003c8039490501505103050100050a00d22581e812600c0f0540d0811070000c064004448095400405070740114401640050280c000d60000364260081111a1400200440d00c1000d41040c0c04024184076a020301d84207081c1c400c084c606890180500551008000780d040410820001f098003200900c0b4608182c80080c0c01c10105070007010401d41400d00030649510361000b91500080343c50001a600c0c50040300490400c00a5000f54003407500b40002d2541c0d1982c50740103405a03000c202d9648051b55524203148030300b48505007003030b40c1107164840d40c40080c00820381106c00350b82c034905004600046803c5204200070325880000d140350380c003000521200c1640070180e4a030800c2802c0802c102c0c00d000000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 504631402 1250 504630152 504630163
    0x1109010801170f01060306061712040b180d03091502150411010c14250e010317040308030f07030501050d0b18070b0c1b01080f0105040b011103072a08 66
    0xc4205100b030203080c1070391420040040d081c40c800000000c1081030340f28502100603100904c9003500f504c04036440074075a10030100d21140c4505010701c4182c81d00b4507005040c00e10b90400500701c10800100c80c0d03001581e0300e6090f120300046229550300c40003141043c103103801c002c3d8100803d0701158400b00350b11040c04003048100e40c001360081c00038407480001d01c0049809101120b4014601207010710004030040d40080c1d009a00c0700342504010190804812101d2230003c140f068041c04c1c0e40b084c00420100d03460b100000414505065020326086c0c60b40c54174078283d40240c03581d00c1052845006c0081d01da80c14485c80f0b01405080390781c03000011079602c480400070f9001e0325104120140702c5043c1d485103810808c202c01000700828458440d1440c1c030380740d502c130038821409840c40020201d6000070b42d07203d0007d4a1088503c0c58a0310880d07420031042c00b00030f00c0100c40c002d050080400c180180300310300f00060710740d0074440d115040050a41c0011002c03c116071490181c1e0742100140107002ca040040351 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 504632652 1250 504631402 504631409
    0xb01060e040b030321090a0c0504090c05060304081201360e0f0f011d060c0c151302040b01110c0628110712030504091e06090c031109010801 62
    0xc148401100c5100000c008000388200c45915202c00070340200410450069000d03041ca0600e501d15542c0c1da0f4a0119881d4407210000820156090320b0078071803850107030300007109103000e41c1c004400c0c642ca40d00800c1c42503009450964103201d000c0f880c28401c80300b403c240f03405440c0254080380c6415103010b5500000102144080380c04120401d101c029a41c950311001e4220880c0c012100c48900030002c5640340c3c103244103007030303915401d2915940320f0a1900c03046105502e4007800804d190f980d44c0c03103008c0e002e821103031000045000350b0343c50000340303200c0144240c0241c3c2d01d035542206d101054410071088851029400d41800f1204c01c40110440d4041420301a0100c1980c0090340c0304540324404150401c8112040e0441c050320004600065004000040290121080316440341d21404400c01c7c03031b8002d82004000400400c414002c0e06100c0d04650000040100301401c0580c145d00d4071400d070f80b9687c003c24221507031140c1c08203074154940103240046201401d03444c94610780c0c000082c0395000501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 504633902 1250 504632652 504632657
    0x31d1f031e020414130e0c0603040606030503031501030f0605010e06250506040308130209270d050d0c0e132f1b03210603031c150f030b0106 62
    0x1c0482800c2070380580c2034051128000e404650320360300d840d00303680459180d86034103000301e00c803d031040f008039a0345c8034803900c0d001504020b081d090b401b2400c000c250751009104032030b070f1910780d400000001d00804c0558010f0503a40d40a080c08802d003400141203030444012411164200f480420190340c201250400110040e01c1d43e0303990381041c40c0c101c0c1109003000c00d01c2251090300b0350060300344040480c52030302a902c00c0e620f40c001ba48841e100c40310722450301840070b5408200d000c082a1040d101054540d00c270b00541c1400d9a0a1400c0b01966081100d511011004503500080d21074406010780701d040b0041c0100c1c1042185010020003240703600d10341e1500419820b40e2520803401c03082203070341003c0501c00310180a01107011201014246a0858190f15400b03410f0040c903030789a0342c008000c0d101c3d41c24604a540d0310380d40c5004820503041c103010341001c1e09070004214801c1003c02d02c401c100c00c0c080000c400400c0001003411003d414501952041d003000d0354908003400050480c80e95030b811a0b0048c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 504635152 1250 504633902 504633911
    0x9120105070c1a1e06150f0301140a060e010c02040f0e06040213020f070f03031503081207090e0609100807030317070807231c0b040501270e0f030304031d1f03 70
    0x5e030101c0c2e158503441001c0c0407036403008607801b0003001004008506a0b91a10880da0f4010111800e00c9026030170f5000308004a69187d1200030380f07510130440344400d1800280b022400030502c060207400c03607500d486203144039080002040294108110086400e0000050461600c03a00340b05080c0507014900d130080519004406030000d1602c69041100c010b81c007141d82c0c0002030f90340e1070003100d968409421211409034141c00211a28001d030518401c42d0b01449204408d6903c1c10200070f6800070003400000c0e03d6062042c0801e09950802242c800381d4030a0300c0d0b000000d0809034250789070720f60003000d640c1000f602804022103145d01c44004400840d8414051241d2800c0941c46000c80c00340d05c0c5240306500785042c0c440c100181e030360401c11501c0c505660421242c1d8807510618204803109403032003100c5803203804250400300c00340d0000212074841c0c1c003138a92684080420504580c01503400b9030018546c02690049141091107100e40d101c030071128101e0340b44800f188140031460041003c4203150340c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 504636402 1250 504635152 504635161
    0x6090a022403010e16081b0705160603091506080a02010c03050405061c050601090f0b0903010e01110c0601060e01020d030507050c1c02011410030809120105070c1a1e 73
    0x742007030340400034802510640c6a603100c040780380301e00c1c07021030300b400c0050300d016040717802680280a40c9025075410039181902050003e00f0707400c1e660090004403031900c9030604c038206015006001d03901804141d83c0c04a119029820194840c145030461000303440d2421400700b1011400040102107180e0a092028840f8803504003529240290f034007154103c00000f80b140700f16901d80707030f8000c81c4140c003c80801480d101d181c01101c8284040c00b51070003180c4910024880020500302a24458800400108010045640355070030f42d205100701c0307031105401084411520b0b400384001405880f02d8540800c60074406c3c00000e41e1240050040030516695101062007240718008442282d9003580c2110160321800c10307626407580000c925034005518088006c1c81180b04146940d00680034501040f4501c0d045440b80c142c5a8880980381d9440500ca03a20001c0031f00d4203004040c800c00312515102c50046003810441094400d40302c0107402880c0041c00c01400300300820003c0152020721070891600d964 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 504637652 1250 504636402 504636439
    0x41b08010e0c18060d0204020906090303180a170d030902040605120d02071203050f030601090f032027041103030d06090f09030f030f090210020604021206090a02 71
    0x55a0400052542440880c144080d000036211021800c15501e2030070b0901e4012440c07912040a4440d0f5901c20b140951070400342c641034010300100f00e4000e000034941080754000915561118035581881c4844880303580305440d195104038003d003854000f0080100200c0c1c1529110b0350704445080c2856500c000c0780c010341d1260f40c4010042c180c0076103400d04080c12680340541d03640600c0407040061145030720104034850311101007a5126450f441d01c0e82054122041c400a50304010710b05810004041000074041034103a00250046001e40d074070003030391411a8040c1c4840014940514020251103241c1e1203405c1c0001c801900759009881a80e103030362160703c0e01250802606806a602d4131003c603604101c0d6445901c94000c940d9000410822420b000b00304e00d0a503071020b0340160205075844100e00c2d01e607000e42c1150a82e281101380010b5084000d0b030001b6203466080c40b0250041e0f000304100421410705204d9207220315140c1c0003d051520b0600d60744c640d55001c0200c000c0c06128151a0000c00d100d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 504638902 1250 504637652 504637703
    0x90906040b09191103061005060403080d0e160e010e07120905010e010f0c02060f060a0611030705100507021608060a09021306080a17030403050904020702131406121504 74
    0x30f61083c40c0100c01c414140f81c20940b150000c480e10902824010806101800100104881e00600a01d0504d45183c66a944c030780c00400c041e01d80d90740c0710050b25440f04818410742c40c40c405884080888141000b000c5d01503844143c004010300072018052080041d000b203019038100710250300c00f007049045440c000340034100485080007150f08100780c0c11144030320754200503030001d007942c21108907640f069003842c883d08090710b0080d0007155140007400340301d1041c8040c14500c24803030200c92810489035213680ca050b4180b9039401c07135240d0346c1040c4281d40d58184180045401d80d03080c0e090b501401c0010140d16400c000c0c042d120101d540300241411900c0e405c0707161440d003000b160304100c103540d0740c000143c403040304130011108805e111030303190f00e8082040162800390342c050342d03442d0070701010500b0701000794400f07042680d1106407040040f8400301c6601070708428200089405a6606015060140c25801490440310070b40060802c01e800c0303003103982c0c0c0d079502c1b0342c20103841981000494042c40088 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 504640152 1250 504638902 504638923
    0x306120a02150301090e01051504021e070c060e03010213061d0603090a0506180a2d060f1802090411010c120f0e0108010e0f040201021c08090c090906040b09 69
    0x220b00c29215900e0845140c0186040b2a9402d1003031049041003d1010b0885130100c800401d211240d0495440d42d0034198081c154841c00c480300120521210310507aa1503400c40c4004464040074440d003403110035407108400d814648250003e5080c030085091496242401d400b40c40c2c100614121902d100c00380980f240e120140d0040c00c07059032800d10000c13254642c007192905540030f1207070a0204680b0312902051005103005200600101b0b000c0341d440d1076020080402094400d88060740451042402e01c14003c20907100d00000640c036040c00707041c00252140c006c40c01d802035017908004009a1907418440d94060f5101c04155221068500161003040c003905014140c0780c40c40080382040e507000208480e4004464030341d00d95aa50140c01114100300900421800c500380303801149840b410820002c0d00207105006039844000c034124005900c010392898100090343c42401e105043ca02130185804001098072001160b10300f1110140d80c40700007610043c81c0509c0a400519a017405102a01c0c4c01d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 504641402 1250 504640152 504640159
    0xd0c0e0f01270b07020901050a36050a15140d0303020c0703050a050f100612060e0a080a201606081803070b1816050d21020303070f020102030c0306120a02 68
    0x1030716118110000c142d013104204078052010f910000c600f41c0307044407030301d0f0458044850400e5469540d981140810040360564405900c0ba180b05c80100b0f480c2e070085610500300030b200010107540f8090030341c004803126400032144201102c0d4901054440b042416140f45e058100540e64188881c00740c1d2030a6410381c406005802101006801c10201291a00719140b41c0c80854510540c84035a030821074866101ea0b0b2503881e624071a080c0000c445800c001441d042703200654401d01402c3d1148500e0b580070307403000e0000a11010a4a80c10200341c10100c2104c540007006101442e45000c0044444009014110503ca102800900e1a00c000182c0041925091007560b0701c0d869180b034030001c96002524410a80c0005100d40100b0704000189998115904040801c50500d418180842185012070641e94100706641d00b02562a80c41d0340400d451840742d004603680c0c90324081c01424010611031503000c5900400920000d101e500301130325000344003111010070711050444070303601e41201310000130340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 504642652 1250 504641402 504641477
    0x3150f1807150804031403090318010210090b101e03020928140105010c050a0303051801020c0c03060c16030509040e010c080411040e0304090504140a080d0c0e0f01 72
    0x114a0b91004155010313900c60b0b12100c0c25520030100c600d8032800b003154522540d07401840600070314502a8411200403030180151010011004030380d60503210365a00035541152002d045c448484021240c1c1401032500c0b01d20b49080000194020324452030521029100d0a0a00c0108000902a6940201602c00046601e483e50001d0480c50040e145031350f0400d440c00c80c201c00009065005803184040a50301c840503040c4180540d505030b0050402401c00180c031401c5e1280818181024030090101d0741c4014020b1008804d035004040ca0194000c0044107610300074840c1c0031151030741e19050290b0540c0343c1001a114019a03000c00c004005070141c011156080585080c03c194026003100d00a600600d28201300304007103401e010660351101600240c590040008001424039070b0f20040d0481c3c407501120102c5e42d10150880d280168080c004d5400e0303400040e60319841e800c64402c06401403c14140b844520780c44034001007440c41c81d1403d49040c44084801480010100d0203003000e2a460000900f5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 504643902 1250 504642652 504642689
    0xa17040b01031a091e010605041a13090515060301020d02071a0a0608030a1808120d0b0f0d0204090c03020301050702070911030f0103120201110a030b03150f1807 71
    0x4103900c10030311003680c44601050803106510b400038856442100a4002001d180181004040c000140b41c403030700300655039441d0046a5580d681c003c0c0703150001b86140300c0c2880e850714002c10500c02035120480840504e80704002e000107130007003000c00f0807034070781e03200d0010700d6031070340040b03400f912850165105503840058180d0802440d46110010340224404d43c9100d0b40d19071601000312807850240303403030316403091010f403040c00d01c20102512200040d010703030f00110350740304203d900d406a0741080701484e180102e42d0b84001c2e00300388030303000d040e100c01c940b51401503140e280822411a80190041d0280742c8800a0b02d0911001070303043d0004640c060020410b0346800400252103d64601600e0350107401e00d01000449402802524010035038451400141c4c1d2868ac1c4079130400242a0011080d9500d44442c01c035002070041c090600320300d5548000c521013007103000301402d0290f0240780c403c095a42a0502621002100500d07a000700c64050b030440c1c0040c1d03404610714050285d80180b810810320316101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 504645152 1250 504643902 504643913
    0xe0a03030e090403050d0912021b09060d0c05040c08090610060f12020c0609251d071101050a0b0f0607030c02040e030c0a140d0c0812100918020f010906050304080a1704 74
    0x480c41d03008c580c2c00e503042d90703051503101116078003520021680610300700c021810900e021404002002d208030301c104003095948001c2415510320340540e0740420140c0b8208402120207021240c3d05c5138810302c18895090501c00080c0110b107403407419604104428002411a0071594100e030f098000400403120207140480c02940d848110784032048022903c460001c82942502495600b42c400609440040f143c00c1c0365010202c1300010241c400300b1494410502e40107600707115241c01a0910b03103020460314103c1060020840498000a00a00040001002090b03005407d440059030450f40401d60004a051142c918001c1803c4034107607000e01c1c2000d40401015030340d41000d07180b41d4000d07104010038400c1c1c281c520b5002c0303080281c580e910410190071403280071b103d450340c03155441d281c91b05943e4403020b003001122200d4002d1103071007244140150540c504000715410100003460300010607801c0c641c0c01807542c0000b8100a00d1488042505c0100c1c2d0301507000e08544030680f1031155041d01d000d0501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 504646402 1250 504645152 504645173
    0x2030a090807120e0609090a020306010e0d1121100e07051801030c0b190e010201021e0702010306140a1a0d02070f0c0e0402060306100903021507030e0a03030e090403050d09 76
    0x5402c00b16103044c11544040c00c0c880203880001400600120184d9220807da1020707604c01084a0f04010350060440303561b0b942c002407034216500070317000302c6a0011b80200740000d2000031207402180d10190514400c0802002070480441c030704aa4001c07503c050600607851420341203400c200c0d40b04151800032a464074050803403504030780c040c40c0320501c1d866944005c42c2c014031440502c40101548891106011801401d2815044030103100040c508007620314280c0709900800b411140e540e03000113046080d0761303140c00b9400141c003081502c1044206110001900a0203030b20a801c0444d60101d00017510314a2030095031044051400255a03c81b509c3c80c0c2f1960141a5445c11140403485034008141c0c0e242c0d0940d9603224940c090011803441d15000d08000e640d2650003400010444806408801a180d1848031036a14040b1803186455220314070700036105200091060380104910481000840d0740110004850701c4280c403d01d48a40311030904903141e12a200078041501e040c00c69010400102c104c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 504647652 1250 504646402 504646433
    0x9290d120203091c020109150e0a0e0910060503280803070801031a0105030307080d09020a0905190b1003022a0304060f0c030e040506010207031a0115170a02030a090807 74
    0x3880301c01034403404299040b16410704d4000e4002031400c4000c1c406103150000000310019941421200c5001d2403001130400c4107160881040300d103116080c010703900c10420a0b01900030401c4002e00101d801c2c0320220b66038816801844120440b4a09103600600035411482007181d00030009559030321701103070082d0a15000388400c840c086071031101c0d199541a90b034515030584000501442ca80780454640965035001a15407140d40766640c620f280050383c0b840f8448005041e09a0003003418a070412851446484043da02c1078a107003482d03880380303c5544015003002d40000741d00700141c554020840103100701c6444080c41c82d5904800b2150f4420300d000202400488204da6260002c494280408540030f0210f5017000300815290034840400b8a811340149a000c0c0c81841103c801a41d03179240c800e003144410301c12082408203440103000740300b140f108000c0042000d04000d240030280c1250a921120010701c8000e0256010000c200b030b6060701e800504215400540441d11207c0c181004241d0046201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 504648902 1250 504647652 504647659
    0x1020d150b0a0207060e120d0f11010c08011701230a0615050714010219030b03070e060d080d1508030c0607030c05070219030b0c0d050109290d12020309 67
    0x4000500c08030701c0c204075450308900c0ea000c0c20781140351a0090307408400e82d043c403562183c05030340e00000d07038a010011100117940b03d50f40d81c01d641e4455038014101c8460700209003280c0c0d04041107060300035003000d0103a0460b2548000e00e0703045004510342c1e0303004004141103c002108450803806031070400024241c00744c5024082000a03035610302e1350100c03640c0a4032007c8041542440000041012000e90a50703160481e4005071501000324050360103003a403a80204042591501c0e00c81150800300218000b0742000c0e080c00040303043c40000600003078080107009061100000d00d89520229542106141403446d02001d07003000d03250b08125481c0d422481003464140301c0c910005038007074401d00400303048050945038545044165001d1007001c03040c03205401a00c25030b4000000c00611911071041c8585102c860040c0c80e01c2072100741c40155081a0b100b40142d0b0b0910108003601000c10003008007019517400341400d00584500490490341c00a0405442e404031030500d0ba1600c0d0300480145050103084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 504650152 1250 504648902 504648941
    0x130b060a091703040e070804030c120c1401021204140f07060e011209120309080c0a06060305070b070314071e080d0e030403170f130b0a090506030f0708060f0301020d 73
    0x2c1680303599010b24407030341c41c1050254020a00b164021012540c21602910b800e03003104415407503003096141c682d40e00d280014905c08000c824031202105030520000c02000940c03601284040c01c80719110301500c0980f116511100501800c1d40401c4040c041481c0300d8161411250303150006460381e43c4080202e03011a0200c3d40d4040031940502c2080d0405a100021141d100740d01c140031030061245200c12524440104250003001e44104492110f03180b183d440424494107525000e401c02c2c0e05603100f00e40e201003d029403000a508607414400000c482001c0c25101c03209810f01e103025000024140707881a20061200082c0100d010042ca20000c50794014401800d680006954034400c91001400308216481c005290a4880000345440340f02c2c40320980c141200700c80460711540300b5510034240090001045501c85400ca202400100000c90f40a41589050071081000c1003005000c0c4081001e01d0001a107103a4071a580b8032441000030b00210b4449480760000401010015629010340c40321 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 504651402 1250 504650152 504650189
    0xc0603050f090d0212034b070206011811030a090c050a05061902070815010e0f061003090206040f0b03041403090d0f0302030d141807050d02130b060a09 67
    0x20391401c90107256004100100150040c03090035000607005210307d01160200c0990300d160840b030f01858468049081d02c07440c00c5100e400c400d040a1048001c00020b0721002c1010a136004580301e41140e0340402100624850084007100510f00d07030084441c03e03440401840a1300c4255803141100c64405c2ca24141070782d0316401001420321151044a42c0b20f40200441111444012a1081d011505004036519a615841c06030305042c1c0003c0c07112401c004402c01041610002c13200c00350400410120400c581c10504003040b004820880101d05042e241c940c8002151200400c903801040100f155205460301c0d4506070381c00e544180d030266480140780c084c54a0030303400881189c80e80c4000829660361000956961000090200c50070b40550005204504044165000b01c801d076541d030b100d00c2205450034941c5a0141c60004500c00c903103903c010818031041d110508101e022503011034401a20301e80c046c5502010302060110580c0000c00848e4003a43d42d50064222403e864008441401d0b1410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 504652652 1250 504651402 504651421
    0x6080601050a140f03070806040b011d01090203090f0d020a0b090c0f15070204050c0c0f0a150f02070f080a1b080307080a02090901060207180e03180604030c0603050f 73
    0x4080c05200c0c0c0c0071118030400c003d000f9036650400c3c0002c8024118420403651100000e05000d181c0c0d1101c03480c3d4001204100400400c000058050301100110f1032030411b00107112800b210b414028078103c10360000104140403010880340901e01101030840b54100f15030f100082d181c0f1005481101c100b11201d001c60390201c40410712100c00c9902424034800f03a0003030b504005003240c52203502015030900308141d2015884074050944240050300303ea6554040d90043c6d00d00d072801004001b01c2c01d801c88100100022001c140d240c0c50540b444c0000f01e00d08842420501c000d10a64100a1070010f84111401c10400780d00050f120700c24154407100b400e001c0b03144031840d004101c004004d040031010000500b500e8010b110f501e4004052010043c14565070700b000c510942c0c800c0c3c009101590003084104865107509110281100d020748050110b201c1c005030341b554034012405c09a004a0103c02401901e480b24001c0c1d03801103801480701c20f90700b5543d40380a001000261028084500070300005990120b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 504653902 1250 504652652 504652663
    0x4120e1f0908070b090d081c0b09090616300c020d020d050f0307030914010605090a11030a0c2f0d05160b07110304030606081903020601032616060608 66
    0x801042138580707400820400c00540c1d010040341140d407031905000c1100c0711002d44501e01c0308a0721804d00024056819001c01003810700c020015811359000320308128105455030b911100082003410165a005e0741d440c84200180203419404003d448c89554145000d4003d4111014610258080c0c542039460b0450032602c41c1c14402188000c51300c10403c00c04005a46001168042264500024444007a981d8611114800d1010903032680d1a004c1c1030000b4a0940714064210f5400d140820010741d1069440100d80802046540c29580e034641c401c000c280998107050f40002441807022009600d21701c3e8052090320090405c5403403240110314444140900210b4641c902da055000e1641040c996401d00034a0005220400300100030030080101d0804001400c081c500c0b40c20045030940c1002c1c4240d1a003000e5408240c1d00c146804030790700129801044050560303402c2000c1104158802a0f44c0d410080c400100d4131844000090f010001200e04d00451007a45c800d079414060959242406643e62 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 504655152 1250 504653902 504653909
    0x390203070305030a0b060a11010c020601270608010504140714010903080913020c070612050c0313080720090702010911100e0303070602120f090604120e1f090807 71
    0x168810000880803074041d401840d0b0215440c03c000c5244901280881c0d60354000b0210000814030700f094800d0803075800c1c0940078078100144000c14140d0314050060101074400740085003c5a00120440f90100323280c1c00040c094040c1d80001d201e01d09041ca8403007000d1030004d1811019000d00d004c0420010500c04840010200507035454410f01d0a548400c1c10613132008030324a600000702e40b216410100e0314000b9107002c002c400c0140c11098034245014000010949102103014030f440300f080750b00e00d003400c2a01e40080880c01c01c440800308a01d0540d41d0b070702c203d442c06030070034107414200d030200024407000703005103c03082d51125000e499041c0c0c143d00740c0d414040000c050364000c0201810303034142220a40d00103041454403003040fa08680100f4216413054405a07405900081c028201140c40017109801441c210b240c900186415011103481c3d03240904010302c3d200e503507a10400c4a501c21614040030000091031080c41040d20124808920356040c15103010400c1c820000820210200303042003103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 504656402 1250 504655152 504655157
    0xf03060a0f031502180d05030c15010b160804031e02130519050c04091d0c0109232805040f020403050a08030612100c120c0203070201200139 62
    0x6003140f148031034040d401039a1080c1450314100300d0314a05a0351042c1c0f00708424001c1c00515039444c542c0d4003a44c10810040d801c1120041d44400401850049000b2148030003100044e2034250380d45440c2c0202e03648204d41c0041c141c240700b00d41040000c1d00d1000c0c40702040340b02311106454820307458840710a450044034038a81a9020940c0020190510f42085901c000b00a080a02c1c05449284c801c00b107813030310b08150743c00c401c2c00032401c400320100b00124005039a090a04084140c90070a444513a9000b0362603640251082c5280403a282d00c03800211403900049541402c03003800d016080030701d14103042c441c940c4124240294581c03482c032140300300d405594000300549000c50703807620380382d80d180c0c00500426007200d44c0800080071240300307205440b840c0000400201c1c3d08c085a42c0c00511400300b444040a055250040c0074000350740010444081030740c2801d2040081c919910041c103125040c1c06034851550800d484440d42155041403a042d40c80001d844030400210410200c01a188907000d0001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 504657652 1250 504656402 504656423
    0x70b040b04060f0f2f010c091706040f120903082106040b0a051203091c030e0108010b0a0315050603010f06120203060609010c08090d080406170603100c0e060f03060a0f03 75
    0x182007000da681d0348000040f0400c0801088174101800c4820306c00c0300900150110b42c05102c2c08103c0e088042c400f00000c3c00402407030601c0e031141d140c601d0204030010640003c013050021041c2c010130019004541041c0c40c151120009608107681d800c3d6207800403880c00401001440c14509031003800c68503c0060007007020541020140001e4800d031402000c0035101c24032070101195130304ea00004407500b40382e6a9514080035450054034000300c100d2000d0500161000510020a04106503070240c0d40916000c03424044c5007030402500021600318603001403000001041024001c41d10004075156076132107258031030343c84040b24128002611225071001c401c10910100d5032284a5080c2554040c11419250043d603400081c15984407c00844640e000460104403054116604c1d0001c02c401d889040894509200025100c903d640309101e0125030741d1060f01801881460f0704400d04e640680362990720301208540800175081102d50750301c039004441001c9128001d001a21048030380c0702d8039104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 504658902 1250 504657652 504657677
    0x7081207060b130b0901140105030a050c130308031006090e010b25110111030304050715051c06050a08070e0a0203040f0b040b04020108010f0b03040212070b040b04060f0f 75
    0x10658401441910301d03030340798440ca842a5450320703091a601c3c1203092000407003209020502901c041c1c164440070103245c1610100352140d80040c1100d0f0302a94521000a0f507541c1e8141e072043c98050100a03480c042c0914801004000e04580114000c00e03c049412101c0e0f65500c1088820b44003501900d800001850010271003850440c015006030380010042c894000400702d20740030464035108040d201100303e02541c001a50300115803140c1c03407030340780c000d0340c070314681611241d036070300110301c540000401700c0008000514072400c2507454040c50f140700d4001c080e10b03008402c00504641d000c0c1038403810041400107030389980050224201e40da210305000c900e6588040d00ba00075000240280c82d0340c054404910300051840c3c40c01846580304103d0160241840e00004089940c140c10808104411071810b02004017250709032603105d23504a62200100302c664011506210190b4000100e690000c540440d00e110035034003901c10380e88240e0343d501030402e0491044070030441e0001e0038008650070001c444c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 504660152 1250 504658902 504658933
    0x11707030b091f0903030b0a050907230a030504050c03060106090605090f06120a060504050907090e030417070602011505090604090c0f0902040806060609030d08090f030304030903140708 82
    0x30b5400008101501c2d00f04650003500340c6064078810340702da07805036620084010550035201c0d14031500003e0710548006402c12022412000340a4100e00c20302c5010221107007030020244100d03103c044c0d020815500c81301004c4018026240c20385003180e4601400480d4540c5090010700746040f980346075201d807447c61030200180d54641c0907041d81178002c0c85c050100026902e0b041d004001310800c5410002461a01c00e07820000c0710740750340185100e1303403c01d4240a0301100015201d81900c0e0700c060005904181140c9403451481a54084001c100d01604464410007020800c00201c0306640c00a00103507100c282c2041807020140101ca078031141c1d25000c100b0b40e0410790f00c564920713882031100c40700640d1985180d411f4903103250b00c0401038079000603050101100600c4981d8000300309a491906100304040020f0b101d250703542183c020400e4041c0013403040d40c02000700090308101441540d40d40e0403c2e00740103240490b503000650720303084c103c961018807410006001e0b00702d81c072110180c020460056480f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 504661402 1250 504660152 504660173
    0x31e02091e0619081501091b210b030706081f050d0f02031e1e030c151906030302010b0406140d171b0c100c0c0506031b0a1701170703 59
    0x150070041078a0404140880c00304415691707217103031031a0b00c15958504031800f400c2e0341e50f03065020182d0080030010301c1c0c2c10f500710a411f407080b20310201e0414002c1107805204010080344e0b240d5a4584600343c3e0004000d508440e0a034055941c2c40f12040b000c1c4800018091081842d1050300e800c41c540300458804a024443d081803014402001d4650040541c001f08078a8240107003401025004802e07401d05010303491024040711211071016605028414040307507101d18a000d1612030b0980d8103000907104000d480125074868022035010400c0381c0d2682802402010105075460041d0301c1c0036404220708114621400d104c2c2c030300600110700c0701502c0d910700d2580c1c84003044264901d2405d011801500b02d4986903201c500c10000001c140f80c0e000c0500f0440e03407012003100704091102c0f0600e8600420104c15914041d203030280c449640c0c0703440e40c0b0700a0401810041c000803000c0e80c080b8811222641c05801810403100c1d4040d4031801e81d07206c46003002108181c0d15114080d5208000410018040281 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 504662652 1250 504661402 504661429
    0xe0a0b33040b2b020a021605040908041806080a03081005120604020d020604090c1e0315030318030c120620090f0f0a0b070606090911010513031e02091e06 68
    0x52895507540f950750042a07801459240c409a044a6046584502d8900c0d400008041c100e8040c0454000c50321614958861401100c6212100300c810180300902600108001d0215004480408100d820700814408083e2005603d1410314080051140360000104078280c0030007000e0401c40c3c480d13908001c0c010384002e204a0b001002031000007402c02840c840c400c110b81803511844a0550004000840d941c100c200d10410706140041466001d42242002c000307030f03a40b5050039044c0c54514060f0300c000c50501e500050a88a20080200d4840b2080d03200d2045a8030451060181c110019991690f5160128145811240610803030f00780e4940750703411681c5550054005503810360300d117000ca0412240f60b041500e04440008100040220610401e002400910801c000b03800c101d40e82c564100c06a98122070400c0008036605081a4003030010000655009107640609020f268048052242c1e60001343d204090100000d440741d140328078a4131008000812041c04d40d960403007085004131440b00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 504663902 1250 504662652 504662707
    0x16080a1a01080421030e0c04061512020f0301121a04110f120a050c0108091519020d0903020f0f0a080405100c0b0906011a130e0a0b33040b 61
    0x1e21600d5100141804191300402d550007007010303c00003030b007a07142550099a03580668a04103040040d03904011100c5001092440d0a0a0a455a1903c3c001900880481c05d12030306001000042002c00b1034021088030f88120518100000545c0840485203401c660141c10701ca108030380c180d002c0c58034145014010341d00602c01024910005456450404151822200c070b500004981c0035540c2c00c1811598062510001003400154000e100003610728045c2503c00c03001e18014105050803c250151b0741e4905820904010201183c00c00030360720340031805025185e02600a0300002c0000200340a0082900500910301d0b240c5403800740f02140400b11500d8082240c1d03480300340001404140000d001300c28010080c071080d41032104440380c000c00302c3d41c2800f814800b00a00b12011340001100342c121012200349240650311030040c03074060940401102d1780507000301c00300c0056842880300007180212032110b2400840382c030600c244003841680039102c6051818010300d01d80c0f60304141e01800c0c2076001d9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 504665152 1250 504663902 504663923
    0x130603050a06030605090a060b031b09040305040e040b0129160507030516030c090c023705061504020924120c0a030506030c100c1a16080a1a010804 65
    0x80e2100801c443c000d540104080c7c005940c90000d00c115030080a0740c02e401100600f845a0b008d40c284461501c401045074054a56000020241070150064074001c003142811010240303883d142c9101032000034040c4518215440f160500990b42c0042003015112034009103600c1c1c00b409031003d440d580c00c034050803207451058800110014109101c0303c8006041c030320107031189a003540f42c140c05c0743c2e0042d000021290719110702c007180f4139400203210766520100d010020f61840000d014a4100c001001000d1b8080c5040c804a01040400a006032152103684c1031001d10150840410090b40301d0742c8045039106070a41c48213941540b00741c1047c0e2402d05210101d920380b01d006a551001d0120840700d00800d0b000218115002c95014060740c4c0e400b646c21400b420544e51904c0c0000e140b06e0b450b8102c6c1040000101d25601042024449520110014124030526141015050365144155072442d0005400c0c503012684208941c05001c1007424104800d50b8052381c0d2000454540034000d2058807a403c50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 504666402 1250 504665152 504665159
    0x90a0b04052e0c020a0201080a050a0603050616020c0f01020303070503090c0a030c03021314180c0310060f0b03040203070e060d06092114030408030c0f0c010603030f05130603050a06 80
    0x402d01d40002070441c41c4414110180300e04200303412948556030400554204210f05001030b03038401d01490f8404005400003e503922501440c0c0e00504441e00014520703c156418840c64203500d0581001102ea590b0840e0b003603194800900c100e002215180b1800b503403061020074481ea0142020790790040f044022910790040c807000082d0114010303403054405e00c00c29101070045d810724010740142403804070300522107110301920710300aa003401803200381d20140d8503850508606003803160201d1000014100c03070540250022500081c8854880c07924030252600c00082c08080e0303841500d1040e9002405850300c0d910740a0144c445010003070485510a007203500e01310009a09225101d244d43c042d040305a01d498070100080c94401126005100340440203620140440f0f00701c0c212940150320040503a2643c0303034100540300790301034402840d490200c045001155903105501502c1101e00940e035107a5180386c4880e00350f50511509241040d240f64140c81441007078026004507070045011078002403ea0399 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 504667652 1250 504666402 504666433
    0x7050d080a0c03020a02100b0607020409060b0f030a03120b041410090b0d0c0302100e090a020a0201060911070f030e030114010e2d0c070618060f0203090a0b0405 71
    0x114040000880c0020003031266004440c440d0701602c0140e0b04046160092480010b0344d910405078100342480d850f1500760045840b03a4041e5403c1640c0a00141b040b21030301c0c9030000c0034224083c4824003c030415600f0400310300e00010700880050f01038440d19802254812880064561070352090b81050701c6541803403801818805030303442521499441080c007400d105085003540c40c2003590b14031a0302d809100501141c0c00e0800002241c0e4111441900c40318002803e6982c00400846140d00c65581c03c10085c400d04250010f00b5040f499074001c1003190348030304010086030098201e6401e640000d001d4180001d00c0505510410b50081c2403008010f2074903000a400e641c404041001030b0101c1000400c40c80344690700f46500005600d8006210309109100c00024144d0075400305502481100807400f081401421034680540003002480b07002a000d03030b402c10182e000c1a04132079440c40c2020b2000b84495174829680149418400703071081d0201c603101c414801170050002c1d42c01c0d00861888911140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 504668902 1250 504667652 504667663
    0xb030406140411120f030d09061104170c06040e040212010f0e010603020901150203030c1b030a030614010305040c1503020f0d05010305070f030b0f04081e04050a0519060e01050705 79
    0x144980c00010303c055403e018020040710601418946a00407a0200b00c0c00c10b0200c15190b6460611900085103411410094088e12080b2130000c10741c000060040f134030074072209551150543c100e04541085985c0028032030783d40700390f01c01c0440c24011400464010329014900c1c0c03000701c3d090000070030710b04103800134503003103440603480444103a548000030411401d10f8251240104030b4403036101045d90a52801a4980c4001803081303400a10014a030020745102d68200c1d03010601c4501201c0d1942c484e41c40141c018084d5009074288003c140308400704540c4240140f5209950002004460f10320307280d0200c1040c100c0c50344003014035409002d102c01b00030b1218094001c0341c240080100e061351440c14028200091500005c080711107001c000d00108103031030510b03900aa400b0200a4450391070b4101007605001c0e100d48031410440904102ca4002543d201600a0301c0d070446000c040d80d644c400800882e490b81d040810540b0002840811600340581a03e117003042c1c040c1070043c0350007a650344150604 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 504670152 1250 504668902 504668911
    0x20a050607320a030b1504030f1103010b010f12020d0e0a0309150203120408040e0906060310090c0915171507092706171c17010b03040614 61
    0x9802c46115082d1859003003260b03010016944401d1010a0300055048032070b01c11040204140740e102d44400e800703521981d6071040840c0c04a01c2940c0c445c1d440e071500340c84007824080281c4008080019594952070184910011000144c4400c9101e0f04510401d880000f03181041b0110141e080c0451940c44505008242c0400d100d000035200e0040a89000762040c045c40e00003080c1120009a90030b603060700001142e600c05e480441d1301c88160764600d04081c1900c03032a001190429800c105111802000107a620300a030002c41c1500d0880f02032600321012181074001c00381100c81c40c141d08000c0702c0c1d01a404503810b28407040924140d0b07074585100600006200308803840f9a0711a8a0071100410400203064004045240070b684551422002502100c00c1a40d00c00d480c0f81503584e00c48000d1280e80c0328200070403840554002815090781c0c55512240103d0290003082c0c0b103000103080c0c103803096441c50b40980c5060301d002c00f56401c3c40c12101079900014421203245664070608140c80e030514402c01d216 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 504671402 1250 504670152 504670157
    0x90a0f02040315050708060d0803220f1a0907141c20010e0d0221010509010b0a05090106090e0912030f01060e090705040504020c07090603030503070906020706080412020a050607 78
    0x951554155580480d40020702d49410020b299052001a948d03610120110940016959803241c561040c00c142c20060b07000744180d0b401d00b01c11031004000c06010904a41c42c06800d14000d1144040c2110040940894803903071143c2244c1014021800310030b501c1c0701d0928015050180e05d000da40000c0b028004420401d440010030703520072510076001c0740800c80e4850f000303103070400c1060329400100b46612002c0320024403d140440302d581407210031b5141c10680089240083c015800c01c1c0c030b047c0d8024039980344118080d46844001041c17505112800904079902c3d42e8903124098a03055103060380700809440c10480c0d01800303400003803600c0c1e1070f00a140155200b95402a040d490a60044c0070300010ee0300941c010344d8442c0400c0400e640000580f0111102a140940e840c2c55102d01907090010380c0c0c02450041d80307008401f00c00d040e0720201440c440c0200751290346605484a0007a40c1d112030620842c030010b800030001800043c00040c0c1d00390700c01c90f5801200c90702112951501d080c0300040f034101c3e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 504672652 1250 504671402 504671423
    0x1111501030516090608100f0f0510051309020901290403080d0b010318020103020901140c07090513050a021909020a030507030f02070506011e1a0706050105010801050f090a0f020403 80
    0x20b070080400a80700031301071118100021440c041707001b526200d1510b4051000f950b6090161001c1e40b80303401004c1c410fa0140d100b04502c4c42c1141412804980a0013010300500030444a450b112980c0e11403804182d400900f01d14060386024a441140c08070188218403c642074850300c106450310710040d001840c032130001c0d507413140030a012034403c03101a094030504250410640c6119022289200c2d90340702d0f020b20340941e84422510060310314849110b40c640c004400024404241803000c0b0354034082e500341c1102403000d51a240127500140a0b4400064a03c0e08900a000c0051400c101507a20300310300442000107059480c1c0c9803100302c2e000810041e000c84e40792410061000d03410311858840c0c0d108604218140840c80d00c075141d41c0c0710140561009250001001541c584443d0050802002a2040f1890600e034083c41c40b6855000b00d5021140b03141410000b00d07c07580a8460141694000b405d01803610300c8504c2000015003000d4480c14072244c0d140c0c901d10307a8402c1c500050002d0742c080c0c40d2000707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 504673902 1250 504672652 504672673
    0x7080d060303032a0e0609120105010305011103040b01180914010507021c050d0509010e070f2c06090a060305062a032e12060e0609010c050306011115010305 69
    0x20309071540d0190641c042c140d02d802c611001501c0d0402c0044501a510b48504e0885801c17000c9011403141882243c2d1280480445214100c015008907060720300c650002d005040c00003801c507a40b800161002026013502d0001813054202c50021000c81409569000c01e15446503128800c072011090909015651902c0400c070510b60100013038074000e031004900906103c80503d006041d80561421004201e465901140095030250014229200d001d016526210368901c48501d442da918400c4000c1801e0901d1800314203211080c00d60bd0049a081c0340c0c1006954200420034188401013246280e00c0e519280480402c42c00c004641c81003107140280008908048841c0108000d91039940c2ea0250080003084007402c008a400c0292454071452043c045071020400720400c0c0f8103400190807021426071324014400e5a4200c20000d2220000342d59454540003140c40c03ea440c010200f8020550402c0480e990754441c603c140d140d04c1902c02a210146009403109219081c207034400d030340540c48465000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 504675152 1250 504673902 504673907
    0x6030c070302010c0c0503161703010902040810020a0c030c420504020d0308060a0806070c020a080307020f060f0c070311031507020c01080408092805060403020612090307080d060303 80
    0x40c041c800b681801700c0c0c2c00c80c5641c0c2e0b03160707681318401159070422941d2007918200a9202242080042c010102c6914bd6868040032002900030303116044e1140b043c07070441c00a0040c24400c0700d0004260355103080115038951019181e6403400700007202d0195455130044a442d8a4a118407030040c21b401d08010140c03082d210081c0c859004403640c8032994500000d0000603074402c0030415202c1c0c2d042c00c0140050391a800041c0b0b20449691084031180034640030000780540c4240c1141c0030394400caa4150b8056240c5e41095602d000b000d100941115810056003040c2c50450082c044205840200c2450040f080f5402414900980c3c8220364110806100d403a4910341030000310010165645511301c1480c001c00001d503108646c510040c1071140b2a004102445400c0d02140e0b10344d40c0c0a4124115014011a003034a62801c041540f80c00c0c544140004c2400d142c000c045030100c0ea00100030608160152115010040014202e070700749201c00c06c801c100184140002d40101145400009a00345c60350501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 504676258 1106 504675152 504675161
    0x13180e0d02060601080a09050606090402040f0606051b010504021f0207050406030305071502030106020307111c15060807030201120f0e06101a0403030c03080c040506030c07030201 79
    0xe000d020350700020410300a01081e84d42400503a41e5002500490300214002001900302201098042c038001c3c25140d0000e000420000c0c00200000c40c81c1c0444042c0c0d4028030100310089a03d80c1c00c410442c0e0b10109040000740244450304e8036500060340da12140d9856000001c081c011055080e02c00c000041c00380c84003800400c0746170348909018000780c010b02e108450546800e110611650080e0094034102d40031600150b00344030043c0c6d0344500c07810010030480c0e00442c885814940d1a00140444468103004008040748114104606029100c450304047c0103030b48058070410044c2d0344000100300031195450005001d00c0220b0915000d442640000c0000307110b4001400780180141503001c04441c0300084450042d901c1202552480c0200e10000c0c021a100080c99004240103101280c1d0100d42200301c1440c00340c5810002e242d50700140d070ba1000071400070520004143d024840c = true := by decide +kernel

theorem cover : BRFrame.Cov 504496402 504676258 := by
  have h0 := BRFrame.cov_init 504496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 504496402 ≤ n) (h2 : n < 504676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
