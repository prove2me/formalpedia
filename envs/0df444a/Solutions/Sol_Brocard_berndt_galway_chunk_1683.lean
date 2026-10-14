-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1683
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:12:41.671478+00:00
-- url     : https://prove2.me/submissions/dfa6b31f-cdbf-4362-b6de-c2b6fdd8c9b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 302517985 ≤ n < 302697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 302519235 1250 302517985 302517989
    0x7060e060f011a091c020f0103020a05160f02030d020f01050604060315320103020907110a14030d05011502070602010e0c0f0f030d05040e150f060309010f06060e0118 73
    0x4a000540144000b0242e031100f00101d08030000d12600d00310132603001c0303110014521200f203891031800c0051003c0d401d06ca031030142d0348402481c045280510006020344076000701c0744034110101c1000f42038420824034081488603550000e00316100c1c5078090304025a40c00011041402c45d5082c80702088442c1005d003c3c04003039a42c01848080260b0505107100c0090002224068904030f59105100c5148001161038201c12080c0d01d8901c1c0c40d40c1140107009a030301010b0450400c1101c80c02c8800300f1104040380c0042c95561114504587d4040c0030501840d44c020000e044017001d1903c030001441841040540b40d0b0600329030295010cd9035185030507403c0354902c0020440580149481401d2450640f01c0f502030701000034801030100184c800424546854488220041007001405000b1409041d42e41d52b4840500c4000000007242c21011800500c0c241c4c00300380c00b030f00000c00401c00d12603083d04200342507106d080c01000700655441d4000c0440303205e8810300d404101c84c203205810b1214600d9074002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 302520485 1250 302519235 302519251
    0x30f060712090b24040c03020909010e04081e0f0d0e150601050f1b0f0106030b0a0b060406110a020d121710050d050f060906040c0815040303022a0307060e06 69
    0x3e06940c2d81401c0b148611141300381c0350211112441c203481e5664031440b4410945c1c809075401a22506e01c0c4050221021040e04010f058018010420000621407012034004080e500b80040d42d06030407a808400c14001c1c400008484840800c42a60f40c2c030040d440001c4d010070781001c5036422800010b110707070040720580380b09000660422001800510f610010f00c0044d40000000540480041c54141400300f1084016800d9454800420900c1403c40015821940401d0f08200c0b00c0340d46000201d207445980700714814002d6060b116034100009005403c007280c0c01402c5103a414540e45880210b040c80801100e0102c0c8a5640002c01704024090750340c49624946450086582000c0c1045440c214020044540c3c1c4142c408000711020180041c0f805580b07050000c014604062810800c440030341c1d00410110382c40190308198072140800001c2d0011780500700180d4035810620205086902592156504045d900c041c410300c810000041c91050f008440401c14003110324481c949440058540300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 302521735 1250 302520485 302520503
    0x70c0b060603090a05120a090b04060507020f010c0b04050c0102010c0509010509090c0708041707090e060f0709090204081b03030301030f030e0307090f09060b0303040f0303140405030f06071209 85
    0x3403500d08100c002150850381802c116105a002c1d9542c03e440d202d01c480100030301c21400304080c41c8032034100040402038903004460764113060a00300d00a1041c014540040e200b1f0904503a410413076409450341c0c04200344c1081c0b00200a02c3c060030415503131542b50b103e0324010342c03900f54110f0706a8411001c0e84c1202405940e11450005890100400810080e03d50b00e901d18080211200060f0100e00400c02464110b840742c58400d08840200e0030540a07520000c020ba00b8250607000208000c51000c0e44401c0078a00074246484141d01103415000c0f03a044051203610002d00429640400900082c1102e0003002400d0b911102e00140b40d22400203100c010008031707100d070700140060300440c0e00d048465000707801ca8400642d14bc10320300c280c89800140e5081c5a5490420f541444014024015500c10542c021840d0601c1c140e502c1e03242000d640301c05000c01954000e0001a00600c9080b01d0041100404541110082142031500c900059400303001040600c486180104d4050040b241c40580100340d81c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 302522985 1250 302521735 302521741
    0x60203040f0e04050c030604030c05070506040e01090e010f0606030608010b0d051c0513030f03080901050405032b0f021b0a0302210c150631020708131d070c0b 70
    0x40c24142c000a00210b0303440c0107400c110349058034200307c0d00344036a0207a601c0f03404074480350400905141150308000c1c05607004020a2001e001d0f2180320504480014400141101c40960101c0c01011040182c1d906141001000100309074550410070554500c08020006d03490942c0400980c0c00c54224010080e0308112020303810030301c48806c42e100041c2e150401500c0c0c00e85a8a103003c0401c00c98100b1100075003031440720760515520140351a40540c100008200500300f81d164a540c4e4081c0b0400840b202d0901030200c101d0b02440742c03098454006040c010f1145510a442d100701139080700441c1007c03100300c010341c145030721000140801c1041d0150050b04600325a01c5003003103440030344a00303421604070801c000194030904121041014210340400e000c03c0c14040200300c10300b416190814001d1890b000440c40341d98040f044090100c2002c2d10040c3c0e0b0b2140e03172070498080c0c01401c505000c40108610001025a200625900580140c080303c2e000c0c0d80e100802030b00c060b454400003070005801e174000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 302524235 1250 302522985 302522999
    0xd0b0301020c10020f0d1104180c02060a050c1e03010e09070f090c0c02030604060b1504061704020a08030406030501051f08070c080d0603030c020406141c2613060203040f 75
    0x20182c0d450b612060718a13145815606e003069071a0f194060a15410000c4c0030071640c580d48001b0001203c184100340304240c010303c0002d5948102521840050340e60310301207104c610040f01100c070102c6680340c40e6900c281000c810824150024400c2d0f40c00c11a440300010300d41c50340400c4c210160b410488800e0461070a242e202801441c1820085052010484801300540d17001c0040c944154415031000c1403030344d584401e110f0241c44c0f00c4500725540c8130500c0240322007508880f00d650507410701e008240090f9030340e00001c4c440301240c2e840401c0c5800006804994294190840c074143d500c159400c5015051007240c001c01d2800040c2c0b4040002c1003100454002d502c030b40c1000401d2402030030230905080502902d03408940d00c0c0d5108801080e0741840720703011401d040c001c1400815004884a6200810320040b9410758078600311400d2001d041400c05041010410300e960010b40c00b000482c0481550071900300381740d0700078030710380c0850380112000007402480001110140c610a17591080000d2a040c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 302525485 1250 302524235 302524237
    0x21609051513020702042406080604140906160f0917010e030c0c01080a1a060d0f06030807031709030409020f0403050114040b0109020a08191806020d0b0301020c1002 73
    0x1030480c0e40700c07448407045241d40c0c2c42c260107102400c5401c00603682c010074410002283c0741d0b00d5601030000e180c0920002c510420b01903040484000303007000707181750703a54900040082c10014640306c03841340042c05005101c0e400040403442240300f01c521700614071041c141980c80f695609512000a08038240c280b00c4808025490040b2918a81c000b084250700d50003143c3c150340010302d0b00d1004d130388643e010100c190f81c040031170358000300084c3c001c01011101140031014044800752040c001c0000007088000f041c0725502c00c0c822030511a004211007503d92034240c240303901c040406c0c0e001420240b80e43c0f2a49080003040c078000c00d07404000350307e000d160140105c040e4009480110b046041070000001180b400e008030300c50000e007000610740e00d00c0c01d890410041032040e002014014810710444406940140c00b55411031003503a0220003030f20a005061024069901100031f4440c0c8050b103807810007c0c590040c018507040300409010a500103800d160807802164100c116691080780c000c1580c0c0000e42c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 302526735 1250 302525485 302525491
    0x2060a1803031a130225020d021c08040f060e0306070c0228080307060c020609030702010302090d05010c0206090c010c080f0c070b04170d2d1b051c02160905 69
    0x10055200e001c580000003141d01a284e804803c01c00d0b00007403c1a0861039008810b4004070038503042c0400c5100640102c0c0ba01e1011010003400341e40c20b2a07603481e00e0070071415496500713079110032600d41d20760711414a056002507a100e40004034020030200c09840c48c020400a01c80d42280c1e9614804c540b0540800081072070301910803111070848040090804104510742c40a80b81da10020350740d4826a2800300100e6511400b540110b4001e0360034023491740c002000300d0303070080d80910300582c45e00c0045000500045640307800a0080d0b2829518580458001c20458400c00700b12050346c4031501d11900546504005a0006012020800c010100307804010003800e0440384e00e40403a9101c1d0b80303502c4000d4080e80320350401104c4007813401c500e07025000c04000640380440c0034500b481e020030404035801081400100840401c4503184449088103110340d190006a5881034900b425854950402c141c483c0344590300140f200320b040900d0b00702c0c5400007415085070b6281d2905114a070b8601001e10006100207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 302527985 1250 302526735 302526761
    0x102070e041a040311030403110f0103021c090302030405100c03091418090307120801030c060201110301051c0b01094a0f0313170c060a1202090901030605040302060a180303 76
    0x85c080700c5020031400c002038809140700d08441d9501038012010072011004080b5003038105401007000f103000341800303083d400307201c1120b41020415540a14080c0d0a42c019604160740212014262004190b4003c2603107100e240207403a9110f485484000d2052151080140290046601c5c540a0505094000010340c01200300303040c0d90411003507a81c3c512903403024840070000664a100140300f40920710107480c0041c00a40001c100305028100d1403052408144616881204441c40d054540c0c0f400f079002c13048440e405010001250b84401940004102e9050004030510380d100a400b40078105812000c2e1011404002050515000310301c40b840445002c0700258034040c41c0302c400c01c490010005812564094401008070300c2c1811a00010b6690003910042c141d4846c1c480c400454441c10110b400ca4000f6107412200120004c8000c80a0f1213070f0340714660407140000c0004240441a44810701803442a803c1d1090741d142e01c6509400d4034030320b140c2d41e81d117903000c7d10012000034001e0384003072100100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 302529235 1250 302527985 302527997
    0x609060f0c0e100e040e0a0c1d0f010e0711151902070506010b0702150f09280e1803030108010f110a0806040b010e09040f020102190b0c031003020d0c03020102070e041a0403 76
    0x150314047c0c10000078000031207208001c0303d0244900504a07100352064600380b408203041c3d01c1c1000110040c01818800d0300849440c1c43e003c6131a103072203070300c03050303003090b84074003210304050240540c4100c0314003c17110060010804003039600e11030418004c481025030010000c04544c0d0070700700e10318555408403d040741e0140c11142d847e0058100d600141003003008580131180c0718222134050045101881c80f901039916040f03460714558410f6800303801d0944d044141c1c034155958030501d00e410b0040105000030708038480400009106441500440340440522405000c00c03e00c20401d903078036025440b820f0011880c2c080c0003505134100395006803400c0c001454064209885e00c00803c0480d4420fa4080d14591460340c1d520b420b55804020741c041c5049500d0390103410128545901d800c101d0040c1482061200000120f41803000c121305150103550014a42e07002c644445c0b07411150000980f00881c050b001d640750028500300c04001e05c0d80318581040072524040030719521406202d000610480c1841a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 302530485 1250 302529235 302529251
    0x3061302120f061c030c0308060a051503091b01020703060f02070618050c0618010509150c03070605240103050702100608030a020c09090c120a0609060f0c0e100e04 72
    0x40c215a8030740500c4000d903031100c03141848014083c3c0400c10b248421130801200981000003540f001048071215010728040702d03035480f803100258400c911a400954010114217482e40e00c81c48140023035004080c171904603807003008202d840c0ba0b25211070349501c0d0b01503000528100003060964000c400c1d0b8058150005242c51003540c1c2c6c440031a0340500844e04c4131404103000f00c3c1000006c000072110f05604a4556041c52000002d00c0350554550307c4a504111000c20791000c103840d0000040388e0540d00400c2941c81d000c5072464580c1daa00603800584030745c0c1c00c0c031000c504080641c258001d036002e5620700d9815440c8010300154050a00508030900314443e400d801c408102d07091127070b0b8001c3c10603c0095a078400c12071070024601400c2c031034210310a0703001c5820f01c4207500c000280030854920a0b2030345050a403030456403d0500d140c03107401409041c18007000d001003081d680d000a00310801e0384c0c003c101c64642c074401243d02c21020340d0280d4005e420400c40d00b131082e008204810054000400200e41d0354 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 302531735 1250 302530485 302530507
    0x3011a010f1103130612140402130209040e0f0d09060906051e13080304170312060d02120a110a080a1502160f0807020907050c070902090103021b070f0501110303061302 74
    0x8a00c5e403084000407015007030910941054040c200a0017440c1c3d0706e01125040ca41c00141030010310790b0b03075080b500d68001a0790329207891781e8020b044190040e20036140c0010f8119609a190482e40c40340b240011800341e4040f4000e4002c160417816581c0542d5000e05040c40290007282c00d03806000e40f001d4001c010300010080a600100d0040545003ca0240d44c483d03180082c01c40d03c00c14280c80800080c0c20a10001c291144801c6c0313585e034042c0b82154031850114690010507941510702407603c80501560001e9018080f083c11002e040d0001038400d40d020310740c1d80010540303e4010410091103540500100c60340404581c002d0031403407450503d001290a40b40d554010041500c69040716400404680c940a41c605042099031000b0301c0e00300343c1d18011a50350580d4030b40c1c182e8080e00b03a007030f1ba01080e01e03119a4400e03815a0901c084141c0071600c040100c0003c1c0d507840541e0320071a40c40a103201408038403075108203000008400d03140f000b9411600d07008100b00e400480054540c4402d542480810250 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 302532985 1250 302531735 302531767
    0x806092e03291501020a02060a050f03070c020931020102070815090106050f03032b0e100608030a0f0e0d05060c0c010c02070b041e03020301051503011a010f1103 71
    0x5200040c20701440c20700301191441c060503004044820203140e40c51040c0f0f41c0d03600824020b450980c11a200d83d03885400d084240c5281c0140200c100319101c2c00b00401807099009081d84c043c05008407400001a690300c0040349a000d0301c42018202d075841060750804000c000315542603424814015034020036180c140b0075190021443c5050710120381c03130090005850080c0704901c0503000507070341058000c0309200441d03524460124001c10460109070300000407501d00f10700b210342d900003031420301c085000800306640d230345240200c91600510b8814001000d0701c0000c11a22030a003a40c8940c003548954250a603800645620b059800840b85581c000008000b800307100d1080c4400c240d03150311013440c0242d19003118050700c07491055501201082c00b07015104401d035000c03101c180c845070400d02d03150003d01038503424a80c8002c0d015030030b08061040b00f0303da2070350505c0b02c0704085c0d00800001c0e605050310364a50108104450104440790105091507124400202c942d00101c001c0303e251901400f000145 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 302534235 1250 302532985 302533013
    0x210706111804050105090403090b030a020927090d0905130605030109030207150503090a080a02010e010f0b0f06042321010b011202120f13060614010806092e03 70
    0x14000003400c0310191030184100c1c0d01401d400c0d1990070301441c7c250341c0a4221010780c0030351819050007000013114002c40b501115a2000080c0c440d01e0328003001d65005510340c0d2416460441880700200140100400140400c1810060759504a00c5440c00e002d00c0908200c80a6045010340c4034800880d040d1000d02813000d80070710039401001920b1401c2050b80c02603410000203030402c402041480110b4400107820004a80c0180c2ca05584450b0a80143e005101c1001c5843c0c4550070403914000340342c03065004203005442501c444403201c00e07010400070244503502810020241a81242c2d01c1002d01d00800c40c2c00200c05044500000340c0300143c8030314401c000072004020307911288090f142c3d50740141461410102c3c05025404d00100c07540484070484002c0c0108944960100060303820612805e00d0002c075504454100082601c0300610701545000e070303c403540458000c402083c86400c080104d6803084d90a42000b420f40c1c0250103030541c4404010303405901d1030010b0040800880c41522030310003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 302535485 1250 302534235 302534257
    0x90315060a0501090b090108130506090d0305070c031d04021309050610030203072c060406181403100b150d02180301050105100509040f05090d090821070611 69
    0x105498400108803041d409034000a041154040341006000601800d40d10300101c05d08200030381d540d90240c0d40217030002c0640003410764401c4100b4010912008200c52009940c03980d01070140340e890740c00070388035000031f07110050000d6501c0d00628070008000180c43c03241c0c64001c1c0003501d07200d0301044240b000302091b040204890383c1c0f401401054984002c2c0e69809215500b02941140380c81322002e050007142d00881d50b998060032540304883d100b140200041c188006240325102c540f601c100030300c4080030041c01c500a10b121003001c91202012080f01108140c014000d24080c0815240036000e40420341c0c0b004d070042c00c0220001c1500b00a03c015145242d445c02c00146c0350002591400740c100d020402986c000e0745020018442c544442c01120b510300742905002d6502c0300414045401009010010320465180001b071081c1094041004e5000d8031072035644890480d1114281a100c205c202d080002c481b9000c0440c811160881000e070038142c0c05a180061410358616034104151b0140460b44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 302536735 1250 302535485 302535523
    0x7031a090a02130218060a0507050c0a0302060a1202040801020703050c2109040902060c01061205060a05011d04020d020301060b031803090603070818010c0f0f0302130b0a03020903 79
    0x28925024054116803100d0018010640701640c1e401203450340501c40c000807103968001171103902840c018004051170900190120341c0e50016030000402d19000080211128004e0201210061a08000c01d0094a400400080c40c05131944030a5415100f0b08244c420300c0e40c1c003888002441842880640300342402a01e070340e0b554400022041d4200880f507031011034011011015541c1103091113040e00d640c0b20060b100044c1901c99030000401e14001e07032010b113095608042c0040341c01d00e4a5240301c11820305c00c40840d089500d52143d18800c0d0f402c02d000b1540d5949050740c010750b8101d60403206a4220380080c0014036510000d0300460b00703440e0b064000040c101c0f0000b040c000c2c0100748161180320100c46201940c1882c4544001960910004c2c0210f000c02000c00702061403031024007000480700407450001c101840320348001400100032400301c1d0010a102441495099000340210b80d03040d4900400100e11a0419004054075080201450f0806030f003801100501c0c0c901304034945e4031507196803040b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 302537985 1250 302536735 302536763
    0x40608150702280308280c0c08030a0c08010803270a15110c01090602070b071e0b04050607050306010f110f07080601050f0a0501080103140c0d0b06010816020c010305180703 76
    0x40c001c00005025070101803043c01150781c44107111b440e00c0110f250702040109109626000403900780f049240041c0c03803480c0000078440d01d005507511110b041c0b0301c20b403a04c0e5500e07070341d4107529a16801400407442121200410f012045003420b0b60b1a454168000c01d0292050b8981c5040130107941d9007075004c1c010035425911000f402c0c40c10800145001d10928005895604000f002512240144203210401c40045078070720401c00d0111461a0900514600e00d40841c11802c0454070f20106580c00d80381401003501180b00d141c03003181141e2203410180c44040340008400c00c2180c030000d0140182e005070060904220441c101480703a100108a0b400003031443c1d50410081100185005020714400c0c2e002103010031885c1d8211050b0b90441707030001218030200c03060080060034103200c1c500301948001c286150b4001c03c2a5405118040c035000c0c0da0741c62403a03582e00144101c60600280744005a40110320032440e81d032080d00241d50100c144141c204d00801100c80461610790a40c104544922000e060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 302539235 1250 302537985 302537987
    0x3050904112d0c0109050307060b0406140d03110609071409010312080c070804181b1b0602070b100611070b1806190e040b0406081507022803 62
    0x10301260200c05407074851800340503180c908018641c070089441e5010080d48a21500e40181058a44503034a0030001e0054042d10316200c1d840e41d20040040b02c15519240c0b14200c5400c091103501d090b80d0030802280320a0b90110200a00284207490480c108050110210200b603c2800403030300502c0f1020040c00841d0030718010b0054010780901c1140941071080040000c42d00304065500080c02c582024072080e1a0503034240018480c180c0094004030002800203400207501d22194040340380c075101041300144905c0340d90a0810402c9204000403040e4481540c445041406040e00520030200146480420764503050a01c0e421100214074410740041080b4094010300e00c1540044201c02505989003000442c0380e880c0920038089000600400c0510082e4440c24100c81e07000c100d01800d1907642140000080c54800d03801d0b140740c099402d1441240a90a041c00b602e030a4400400103082d441d800d180b40c8400480e03004128000310300c621110149070064000d115060b585850107501040186410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 302540485 1250 302539235 302539241
    0x50307020a090606021513030c1a0721020702010c15090f060c141603260907060e100503060607111305040c12021f050904020c0708071a070b090a0b0403050904 70
    0x42502010714100101f2001071100741c524040d559050900003041d100e9400c0c44203114070141000240d0070006014031040681004c400d00d4000950519004e1001509842c0400c0c1e00960b04024003103007103148000002a85084204000d815002000644180544a0181c0c03d00705074025201c669494820802150380081120158204041e0301751810074820100e00c020156050042c04100d07c0c1509c03031500d110200b40312200c4601c824416480c508103003480302c0d280c0b0101c0c4514004a134140070444528100000074001c41111a12901c0c210390f146418050260b00c19403048441004078058a100c591710442c030b070310b03c11500e606c0000b107905d0140760140d1081c206030010f140c1c028600703021a0061366110300c02e000b50b81440780c041d01412054402034810380210010a94021300110f941c0340001d200040440881d241c0c1e81c120388007150381c0c8016110800350345946804a5000f045004045454141c01c1030b041526003085a1250000d0340301d03002c00d2941071307070114005440059409034529040c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 302541735 1250 302540485 302540503
    0x103615050c03040b031504020d1e05010f060302180d0b040c0e0408040302041e05070c0501110f090d030e03150105030c120606010e01170106030204030c0806011d04050307020a09060602 81
    0x105000d45010641c038403069407406184583c00c09420008000742d09101043d0405c4004440a003055440350942c1000a0181c994403100340c041301c40c002140d4000f0540c60080c4ca04031900303100c039204d1890034000c044020f50300403140d840103651a490100320030f8480481482605004120f026001d0602d0301d842100004190301110008100c7d10602c004110780800712000c4942c1242d001511510414201c041e25524600150041c0d1901c000c1103203868020900e40b0501d48914001c001d4800c1e040122507541c0101490102e0641042c0403c003d1400c2545141101e280a0701342400340200c214000380c0391a07003064180c0d1203444501d0041005c1c0c10200f140c0a07640604070340c21406800c41c124010b41c3c40b20020045070400c517141141d0211070b401550030110190140002c880d182d03841e11000b501030361091004690038501110300280140000c1090780c180c4901003032208450800000c3d0750301090300944191802d01081000d01c005954428082d802400300074000300c1c0c907500c3c050020381099080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 302542985 1250 302541735 302541737
    0x18030f040303171006050405210a0501020a0e0102010203010305061506040b030a1505011d01030f020403020d0b07090e040503160c0e040f0b090a0f02040e0309090f1f05103615 77
    0x39801c1409103a80000907941071310010340f02c0b4042a103606403827000c0c400f54010800381034041c820082040c400c06400a0000e401c46850b91080b0f040004012800c07480300f407002411641080b00401e105d100185003000c01303040d000701541d08154a842c10581700358400d54130700e44100c2d170301d0348104210302c900c004d071500a103c2420312a10b43c4410324203000400302d11f48841c0d41010303070700c2c40e030644116210350640d800f95801519032020102141f4161030806002d650000101d0f00060000035003901c4070314124822540500918202010841503100e202c2c0e07003460403503096001c00000304400b24904540c600c03480c000c1401c00c0380381d105810b00d04046640580020764075003110025130049801103a003148060790544001070b0f03142d40e00d41d0307042c11070080c00f2000364000980e505200e08040400c4a1600070b4505045803148014200b981140d140c005118150300301c4251a0a8420030340500100f407000044852108040000c000710348002459103a80da0f070064903891028001085041c1c0001408161 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 302544235 1250 302542985 302543011
    0x3161a04240e01021201090f0903090b07020303070f050309040c0906090b160204050106080f01050103360c0f03050709181407050a03061b0e0918030f04030317 70
    0x80d4681181c0c2110260400014403001010040211210ba01c841c05900c0d081e80215100c4181d00f48a0461003001e02c209542141010b031161050703a1a481000c000c142c0c10348031820440c1c94075500b1141c1360090001139905000074001900071405a00d0360304001441034003d540d513540306008000484aa0390b0600082004c841c0040c40060781214010069a503100006a210902642116a0007001701c2c1c00a403c08d080100000300f654001080da400743c02c880d5008020f030fa886600460440b60900a03c000c14403070120318200c0b01021313840700b440d000c20304055102031000c0b41e1601c01c0ca0071083e92082e8008801e12108000348032050103004003520f50724805006000690b01c081021804100300a0000250b400d411102054100003110003410040d00e5290101ea89003040b5001300078044444440c0c4140c00c0c1700710b14071442031180a2286100030b03e8040c05849010380550688203109a800d00c912007003200300c0c00c00c9002c030050802103100ba621f0b825141000606034185901c0a4101461121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 302545485 1250 302544235 302544241
    0x307050304030f030b0f120a0503120615130504090f0b0118230a05100816090608010b0a09020a111911030604030903062a030903031109090a0e0c0303161a 68
    0x140b80c0c9030041b9154421100000616a680d00f21810300031000002080c9200001d03070480307641d0580b989e8900c28001180d030f1080d80380c00300303a8070b00252088040e2800b880300440401c0c0a1450a40e110315102402000f007091402515910240c56200030b803c52500904580356485a021007030046000602d50090480400c078075680040018440281c01030040507264400180c9880e10f01102e0743c0101820001c841100c01e52410b81050038001e070103603030038070b5042581c0402c41042c14014014244400f81a40e080d551034561544000c2d0401e10070103040005a55510048180411080b094454041c125904621051400d5241c20a0707d680840c00b80d003102c0d0400001c80d41200d00c144c00c981e04107030f0106900c083c0d110046102800c02d03110888520560310b4580748568554001160148251401c206e18030514420140a00400008a40c00540b0000103011002c1c142c02604a071020381301190001c0c1100c0c0d0000e81183c104040100c2001030132000ba00a100c40d20624800668012985981e141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 302546735 1250 302545485 302545489
    0xc051b09100e01031509050d110114091b0415090b1212070f061107210302181e040219020c040504080306190e10140f0306040f030c02060307050304030f030b 69
    0x40c00500c009411042c54034800700c1017081c1a0000c458450303200003030f1000c0c0000079002800070100600300b108290710b800c4117500620b4018050602a000b62030042c00d104500704000780b120060340342d10076046600c030b00711407001c04030003861080a4880c940e40820111170031014041300740300c181c4006020b90b00a06180b00c500c1483c0088400f40ca42107101e900b2052040c0c201a406050f6000c40c0c642a600005814000e001e4a14100344a032020303000e2860400f120510224260b000d1849800c20682803a04c90084030315041404107550480001030300e0106030420002412038220001d40e0864402c2c48024010325641402a5016000d0403541009642000d446010050200600e00c50043c03540c00e4501d09520381140d813800082201584fc03e20ba0300d0003a019010082c03052040d50025180c410180d10985007c28400700035100140042c080e17503917951034401404100744016018810882e48403405070301c07081c7c000c1d441410107448142e1390381854036009041445458981d81050701d0480801b17016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 302547985 1250 302546735 302546759
    0x31b1b0f031e0304170c0f06010909060506040603080a27090c1e050f2115010f091a25030905090112050606090714030901060608070906020601050103020a0c051b0910 73
    0x14210f1798141c1900d42c6200045a4540514408441414404c041c000600340c41c194100348090b92086c50140403a44802090100361012808018040c00c003d01c0043c100714400c17400c54003020780900f8403103405404140c030144131550036005800400c0d190049111001e400804618020b020310300f108640100c81780c2c0007071507405030340d008000d800e800240c84071540d462a58010641118a0303a412451708182110200141c3c4410341c0c0c6012507801c00b05d0480e000c0c050a000003c541c1e0811481c00103104410101c1300a40c0b088400194000084580164400e828010201000e03c01e440740d690070340c00d00e81004a4154168489085103003802004800501c0105400b9044081524602283d4607419816078186041580c070001d038880c0801045a00c1c18150001e0046886503103465403152145101154103c605014420162344414010011944241c0c0240303448045840c008034030511329030782c107400c050810050000200200000c0c3c8150718200a03869080600e0f01440420301c1c0c07802c8540510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 302549235 1250 302547985 302548013
    0x504050709300813030506010501050702130b030a0807080d1a1e01030612060f0b060c0303070e0f0909010f1d07090b040e01060f080606010302031b1b0f031e0304 71
    0x101c4400c042c241d00800c601038525051040c0e2241082d601c41484443d5520004c2c0c50340710070f031070b00c0c03041e5000001d0950082d012110400e4000d411282c3e0743c82d030895500c001e00542c0741a20b4041c031845440c5004100c41201910806200c4e00704940e45481b00c01040d025101e400d00c0454035282e40d202c16404541d6600d004104400494002e01c3d81110315800690050020354400503189a900d9403100400905501900d100b040700315040144020150a000f601c3c040c011413014654406c1020481c0703140250725025080b030005141022108118020600000c0c054550300e109a440300c10601c440704082c01442501084a85200510390300f202c500340d551031a40c411000541d6070346000891984a07604400319510482009021081e61526525883d003514442c41c0b02500407100818074661090084074043c0341e12981e0419401c40203005031030325501100403101c1e4440c2d0001038000c0c1d10070a201050103481010701858440d101803084000460071043d020420b24010010000001c0003031625071a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 302550485 1250 302549235 302549279
    0x105090601030932060c07030c14010605030d030506030d11120a0e1804021804020a1a130801201c09051603050a20031e07030b040c0504050709 63
    0x1040d502906248200310720641c3d40741c4e1449050141145913011116001c1d100021800888140f41e0715104204414060f02900070700041c002d00402000c294143c02c00100c001003c000010119501c40019181c4145100711001094807a42081078a282c103000c245000002414600300c00380d10074078016106c1280d06602e1501d45404103007400e07850f2048590119030100940401945d1001c2012011a1007089a080380700e8690381024001203d211001070b8041e6a000e01154012030a021082590122035480c10b0340e090024441d80c9900b9464407071120040804600001b0204011244100b40980c203034090340d0000001c01c051450160598201c548008078103000084e0b400c0645012814201404800c034003011000340c3c04030a004c00401e100241d00c0c4150316215481c403280b8660003a0f0f15001911550640103030540104216040d0f08070b800503100841551609038596440594005081e103081e5410803c0c0007090005080c184a4141c11a00d80e0600f06031162514102c0a00801c040340e03240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 302551735 1250 302550485 302550491
    0x10902011e03150b0d0c05040f061d040207230102160209091c0203091906080609070e15031f050a120f0803010e0a06050a120b06030a0816050601060305010509060103 73
    0x5001c06110f40d00c0007609104143c50090f405580701040070042d005a6016084203140103992255640554201c0c0c08440c0b4842c060007100f8a000401e44240e104c00980051295030300c03c0030186a503c0340700616580788541c42142e0300d00e40006585000301036510114030507a10410440d25210071400c5048c8509034111070011203595190f100d0b40c2044810140e84003488407212051040e650040041c140506042c1c612040244101040c1c0003c0c2c01540700c1e04003c030740024080fc0e158148505000c0d804280c42c100007540d0114a00440d0b00c030305009044141e409000f00a2254880c00c1d000c03003071000c9001d101c00390812403d080024484031716910520191210f410700307450070000d000c880c000d0841d410000039905ca40c0d48110307038500e007a002c69085042614110000c9143e1030050f17195820f8039240c094070b04500207140d0702c900c0310210203411558141b00354030304400005c010700e005081402d402626201e040403e0315185140c02010b0f0002c0c020b0504080060200380ca40200c1168822000d103408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 302552985 1250 302551735 302551787
    0x70206031b190305060901030327050310020c010f020f16110603070c030e090f01061d03010507030b18091902010e1906020d11060105060714010204090603060e01090201 74
    0x40d400c034610660780c00820810200390402c0d511004010760490341c0d06038406004990b1141d00f0040103240901000300443e0613000307080d5540d241c00485140019084801c2042d40d6100e4000074a004000d45802a000b600000c1e0000226001c2c001c5441c0480440010340c1031491030b0461080900402d030300b0942c0112400c035060306020481014010000300039000307030b03603030308220000a100b00710040c819000b260040d024442241484418644100b801052900e0780d6401c12108607202c01e641e0b084800301a24041d0303408919503082c41018080d50460700d000901d108c5140510500511200306e04034a4412001006030000e0701003410140a0303256000c20892003020b1005844400c840c510450300010254000405010000080c41c1940c3d115021141e11207441c010494103046009010030003904000010096030500e0400b5081c00c9114411608110704260366a5007280c100754001c041c540d80340c15082083c000144500006a4002402400120080d07000640310080010000c410010883c00d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 302554235 1250 302552985 302553001
    0x18030807051303111c0f060c051b07080c1f0f03020705030d0c0815031b03120c0615060a0206060904060608030a03020c100504030210020c070b0a120605010302030c07020603 76
    0x1181c14450602038080c070580c0c2c403400e100348140d102c1e8080c2801052404450402101400349107082c56070b00180f82c6c000d61419540302800b8040c8102c0900601c6014020361080085c02101501c41c40b4a450040071000e1500b040076240c25920380029000d140800b103034904041a254010318400c005003030801d40702602c030b074040b4000e03c0340c080050040d000111316124401c03140d40148000381c002e5541e84402da195181f809400c5501500c3c0700d64558000801b0420440c60507079122081d11000f02690140b090440400b0135a81c8240e10304402d9820000810801841ca0b4480020031003050b51203c2c240001c0541c041d5a07407201500b864494a002d100150800080d5008100502845800e0341c0e182c110012000c3c000c1e4010b050414000d00840e1301086038041948281485941c042d4002c08030601c40b025204d000b54010f0b030712581d8030300030110040b62108014000303017070302010b555032401c07c4998001c012045a1982e004941050b00402c20301c10780c001801c09a942da1901298041c1d502d40b140e42c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 302555485 1250 302554235 302554237
    0x80d0222030b06030705190e06120a03090305061f14030f0718060815010323070b120f0108030a110705030d0c050d14181909020a121803080705 63
    0x5410300030394288000c0200007250240c107025400550844d220207072600104440001d0082903034544d03540040041012034a9983c1d1160001000341c034450310902c0010180b0705180e280310060300401ca2010341041008400c22003145e00c49110001c040c40c800c0d0385062b5518440c0c00c2d200d2110765010040420220395010300422200380010710490b51915034440700005c040a90201489425151075000114120040343d01544c0380c0440983e4006682035a441d03044c5180700030440e44401800680c9402c403808104485800341c000c00a456480e480b00c20252240c8010082480701c45070990801084100301c0041078441075003890410108014a0440f2186406229807000b540741c444c4814401c9542e4204d881043c149006800350b6001000c17144040d1400c10b8001c84403200384004216011500702c101d5184600000c004200d410500422607a403004446241c0041065035400034a46000c0303030b04202c0781a10b40e1076141041c80030070030020b104a0510400c9801a003070007521400038010320700c200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 302556735 1250 302555485 302555527
    0x60c020d020604033c0e1005090303160804090905060f0a0b010e010509062506060602060f0402010810050306090c21030301090e1203100302010f030621062d1107080d02 74
    0x101e01704248810022004014030f40340021035028060341100142070900c507008607180703440050015441c100320418041c03024216048261441c4106000104458046000325402d4500803401400c150a0000c49040c069001510a00c04145010306e10540c1e6608848502595042420b003952929544000308105200707200c40c41081c0d2088040301d4820403c0e560840495034001d850802100e500c90800780d90b1484155810314985001d480018010740c8944256940103004104070712506585501091402030140d5040c04190440d494414044c140715036452050300040303100c1c42d1004e041c1d54640c0e0300c4e4030060140850b03150f21050b071a207074807400300b1244c030004034013845550f500d1034000c0d01001c4014090000700e0000700c50a03008003155100340198420384001102181d01c50a00071140179460709004411194642c90310741078500d1f500340403000b046080c040c011640d0320f2401c0d03041c9c85044440c08011a00c6560b03041c0401c1002c1000e510964000c03000c00c060059488010303a042c616081004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 302557985 1250 302556735 302556827
    0x6100809160801140c130b0c01020d0908070b06030615060c0109020d050601091a0609040f29090109091112150711010e01090503090d02010e0a03060c020d02060403 72
    0x3041e80001c40080551281d18091008600484c0603211a08510410f104a034945102c00240080c244142d5950000410b170b03504e0400001440c0c191083e0301301c01500c0740c072042582d14590114404040c0b201d0190030660050b0101c0c00b4040c5d43c688641031030313100d000c21502d8034042c541c0850031000d00b401c01d51140706126002011200310003880e03d0119a1744109000301d00c1e40905002d4989201e0310130140401c04080000e1015081c840504180300013071415409058202d0746030000c03207041c0e094443d51044400585102d00c030300706c00c0386411300210440692040c1d50b00e40c07030109040d000c074450708898180042c3c100c41640b5000c880f020505d00d080380c038807910200b0b45d5007034040c000c41c1070304400d1a42c04954034800074001c00c0a85402c8500302c4080c20300c00b9045403c10845000d051030045a40c280e001e1050412030b0300c90b103642002c5010004990001c88105a403090740886407078041142d50504640352000303020390715040c3d030014160800d041c01052080840710a0181008100e0b80010044c200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 302559235 1250 302557985 302558023
    0x8070c06020f190f1e0c020414070509040c050306030d1103043f05060106052110050103140106050f030a06170601050901050d030207030b060616050a060f0506100809 73
    0x3e0308141c1e00c20140105981004074810f0340421603014060900b0481c11803010342d000f84454000ea0301a5030b4082150310487c7d21035595004850520808200c15006003900c2d5201a11108918140821a8840c824420600005008002c059500080c010100030250302d4003841019041c44407d2131402960031021000046c0c3c2c03448624000421954040c1821030004011905a12121401a140d942d0000741054010344011700c62640200300602d0704070250b0301d804102d00c054280f41c001d01a0180c41500703000340d8080003003210b580d01d070044900610b00461420300703030b5141030005011445142e08080d0901c83c0407000a104002c40e44c0850b004040b885664620340c02510070260f03c0720801d024a42c03080b070090001040e107003816a162540507515400402010381140c640300c5084000405403a400b40c420401840c40e415038080041020f07126000920100c1030070310b485410303a000c07482c1030301000e8905000c120083c0d9400c0d42c030322001c0a80b4108581e982e12030410050034404001030310200d00038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 302560485 1250 302559235 302559247
    0x903051b0303040312020a1b14010e03030a06080d0c03030903090905040f0b0108011a01110a08130312030902100e0102010605090c13050609060702091504090305090906030d08070c06020f 82
    0x300101c02144614800d603151580542c510070a40704034054540d5003030000d15000c1d00c40a01c99440c401181805008404141d081c245488a0f2801e445104c054030b1030540000c014480001200d0140350003400e140005480d0620074401c0007031587d012408003404050312449c0c0e5006141c083c0034210003030458590140040d252034203000c204100842d00499000600741c0001403d900f0607c01c00b603408039000d469405103940300c40110340312680c58103040e000d03001d050141c0d40003c881000070084d000c0f03d50309a80c505451130615511300d102e140ea95200f4142000f0310b400050ba1005012100030b140d030b0901d500c400c504100101d00512854106a4108074001c0c140300d5030940020160100f58a21000041d00640340c0007440824018402d0094022809001d6100103251042040e41d03c01071030018500340b910707641e00003002d03901991070070ba02040c000168520107041604096500080036401003420142462004060b014028440010004040020010040c03550103c0b042e807208107100585a039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 302561735 1250 302560485 302560537
    0x403051905071e030f180b04060201052401020a0b07020f0610080c040b06030c0a1205040b15010810090209060c030c0102090301063215030708060a05040608030d090305 74
    0x1c0e114003001d03920121200004115100f002240d000e03100d50541e58003c2104120b5003d83d80c002d119411880380b0301454002050a00b003017405000100f08960011405080640026402004025000c51022031242c0d40303d015903000680c10550b150b0000b0b4a0510b5520450120308007000381110082034004c40d014400e03010025041c200c151841c01d026605446100401c1100716000b414000c2d42000c01030000030742d10f0038501d01800c440702d158204040d28183e00b000e0401261005c1f03030121012101e40051107a40380e045120098110b0f420308142c4c890781000d81c1c03271072599420391050044407600054416080e845407426140c12202d903104807911102c1c2d114641e4041c1d005090114000e42c640480050821498002e924001c036031441e50011508010301c0d000505090065040d40041c0061165803226050b0402184580916504c04c0d40d282858400c00004104076032069104500303040c0184200c640110440300c1911a40900048224041c9001d031001e0250210400c105881c401c5495118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 302562985 1250 302561735 302561737
    0x705031222120815010207031704120b04050114130605061219140a080a03020a051b010f0c0f092315041701021602040b040b0415050411030f0f0403051905 68
    0x2041501c521041d13545100c0c00030703c2500c42444490060384944420804525200780d21021103441300142032070301c0d841c1c080410301102a00f0080307030386405d20010402444000c3c815048408175043c90450141412100030034018420880a07019650b1480410140d550b850443c4041c2c403a0700c8140c2d4071007428000d0b1030780703003081c0e12400762a80c040b1400d2040d01e6100c04100450b42c6984003005034100030050f5800c40003500b00ba1404018404104002d0400040418201c1c451125440010440034004208001034401205880303040c000d0401e2803a000c1c81d00103a410094440140f001d1302085130340d00200b003804002d00100307a041006a0300c14050148058002c1040e11401c0381c0000042c950425098203d1107000030f9001450010914040140381c250488801e8540c000c00204c2c030340c50060300050031980d00c400008104000c1240421450419016000001c00580410b82c20751500c8034030240142c03801001074600c21072280002d0304150040d81510140b86c0240b8001e246581020809096 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 302564235 1250 302562985 302563013
    0x6040501050d0f0e032125030204120f020424050d03050d0527121e2107120203040b0a09050f01060e070e03010c0f030b040605060d02041403030705031222 68
    0x503d0108038104c080301c0c0786e43c41030203000b4403079542426001841514000080c11786204098201034081000240516051405c180c0c800d00540900280076a41d1040000311924401c0313020b0003e1031542c0c001160b4440d44104001c0745da05850554092040b840d048902e440344003182403406243c2000e000c00d11603800e4222400e091a03120700207860010305d20555481d101d10540b900d00035400c02040d409114034001c00c510300c1174070211540c241150420703c06c2c8010001c0e00402c002c0819031081001c1c8552100c1c80c240e13041c600c0d0f5001c6146040c1603c4404e03601600402da9518603464040c2c46040140401c5604444084040200302241e01d0b800301e0701001c0803c0d2440300005240c0310700140240b40c10711030340002d01503640b0341c0380220440000036005030a1075042141c1c8640c0d110000100c0f0b0301d03480010801000425001039035682010015603040703441240d860700030742c400d020020008030004112000b500c43d00240d01c046988000035441040c0c544014201c0c0e0760f070030902e40010031400d0301c2c000203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 302565485 1250 302564235 302564257
    0x408091516060c0206090307123b01050a090b070515090c0f01050f12100f0e0f070f0f050304060204050a170c0f01091403030409050c0a020f01020906040501050d0f0e03 74
    0x10402c8140003c9039100c1051b21111170700c0e0020001800019070b02040159600807034101240c8086402c880c03082e0010100c5199032008844c080031900034040300304c0e500f11032002401d0403414090455001009000d00780500902c6036400503001c3e00b80301080144072a4160460400d0403c1c0c40c0040c200c68882100c500b0b10382c05400009480c4500d5805402a20164003524004504064460703080008404015000f000000c11908001c25030307001844020b0050300325404040c4071401d00c0c84691072591380050030307042000742141050034900d41c42000c84000e10490310b03240b622610b4a0800000034443d40d4400742d4850003d00c0000703807030940f14814032201051441942d45050001c02801030401c028000580001d00000c018040b40d000401100c031400c0c40a8100e9042030386412400086400c207540c200000400801c541c0c10481d41000a103998000c21402542059100000300c1c003503004a025550500401007280000321324281d0205525003c540da080c030801c07020340e42c504d0300c0e544070416002d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 302566735 1250 302565485 302565491
    0xf05030c1e070f0b0d050415110a09050a0b0304140c06070f150e0309010507060f090b04051603030914041e0b0f0307120204051e0705210708040809151606 68
    0x402000500f0410102d84a2506540c40c1c2101802c060340240310041084452941522000c1c40c0c02e6031510842410014201e510b0f46e840510f06009490300b0715940c002807290711404024052410904240ea800a6010600d40341c1118040051410102c0f50011641c10a4001c149003051003101c110b524142401625009900b00540b846a0107443c8000244c81c899401000b0315050395100f5002010035074000ca8000841c42d480500e1401607a040100036103a41c92044180b0040c004103011411440c07181a10520041e80340d6036028200805a21483c444803072082081159520385030803089060941e4003e04607140c1480c84013030003d040d0f14881d1030060320b804403001100d040000d0b0700019169071004941c0030390025030801026000091104800e00c2c1031001d04206403040d022500e003d00b25580b60300380c13500300c0107203c1c01d49126188401c1500800c0c503000d0081701900410a16003242d00404550f589160150110301e98001c44042103441d030300e0014995030071503001e010402410740b09010034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 302567985 1250 302566735 302566739
    0x4080a080f0403020706050d090b18010501080327060c060403030c0e03150c0717120708060a060e0d021909060311010207030201020d11010b0a080a0606150c0f05030c1e07 75
    0x207808880421103005003da0b10400c82032124074084e4002d0300c001d950901002c00e0b00402c660321000305d50380c29100c092a82e0710028401d505a4001c2c0030b46809032070204001c608000c000081480480c004440049030320031100c00070041a205e100072501000eaa007012a050303400c180c40c004004000007054240011002d1801c1c010a203000b10b88014a800b801c0030740f6110f51581e50300d40345c0703a9002090440c1c080940051210200d2014400340006025040042816144c5560060041c41c1d005111611450800005100716600160304c12105041640d124803101c00c1440485c42142100700020100301c01110002801900390b0002010f881c410b410510a020451005a81d108140d000090158101118510881e0320501085070074000c240c0002c601041d40300003141c01d1004507080008a034005101c480c0030311125000d800c0c001e000f072041808000c0194640140300c0e03c1501c800170521140b40ca1070f442030100400981e41410081e1050390032081600160480c0e60022a6841c5842d0061a0300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 302569235 1250 302567985 302568001
    0xb0903030a050f011d1305071205070609120b06210c12010501210602041d01140a03021302130e130308010e07050702060903031201090204210f02040b0d080304080a08 73
    0x30141c12284580c003c48000040541c00515a1000400703450140c646c5482e180080788003000a40020700d0785c0c065030901d4040c0b50510301d042078510b402903000e1045071001041549200400d0407807190304180710004a2700d030b400000341151381954008154840480012064040c0411110078040041381c4000600c01c51042c05402c2c2c400903c141501c031040045411100400b0710446c10405104860044c40c1c030ba1143c91600340081ca4600754502c0c80315200050054072103a041038101d01208552031400740b840c503400644020000c0700000a801d0700071488186c8030400c540560040d00c0300c941c4142491500d0047e00d80320400809054000403c02400003d2040c1c42041c410300400d9240d0303071103140c02ca542d000c0c02002e50081500d43e4051104000044441c515016103d028200031003002d81e82d286810500705000160308021000c0414007003504000a01c01286090301d69419070340030814030128000500121045076024103c1d6a000040104000c5204004d0901111940f41d1460075255550 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 302570485 1250 302569235 302569261
    0x10c030b0f0f0105040e070203041701090c05060a0c05071d061c0305030c1b0703052a04090c0b0a050a0207150c061e0614030f0c011d030a0b0903030a05 67
    0x540d541c00a00c03842400e4194241598100024801810164039043d80ca04010810103000c40f05d03000160004603040c00704c003689000c4110b0341c0ca501c400038800020681c0b03171131002c400c1e144100b07480b66400081207038405024801d000105030700481540d0605035a807050400004947d100800f1010000d00040c21528142006407040817981c42d06400107982541c060390175500103801d0b0382000809000d441402c1c8070b05a0751440340045000540b800c03620f14500140790444403074101500c4070007140040401101c5c0c408100c03c411080b0340103d000781d051705207182021103603040281007160018900c0481d41d0807900405d512282c5170b084031901030f81e80b800405118820031101002411500b02c0c00d01281d11070b08115105070f04881010501c800c81e48219044a2040d40702c0d501214012520114500d0148420014000c0500180003000c800c440028160903007003100d201c1c00c0182000d0038215032010043c1c004019482042d00c549401c02c414159500e8200700d45040c80700d400c0ca0300182420701440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 302571735 1250 302570485 302570501
    0x3150306092901060305090a020d05011b02280f1a0f010b0702092805090d1101020306010e1215010e01050f030705300601030f0c0f0b0a050c010207060f0509010c03 72
    0x1510340c0105134280780e404c4010305000341030419107101d091004400340c0e581996011081d8454000050b048250140b04980080481c2c8204290340014840300440340401e05082d20f4082d008004038403c003c58a00010b1911030440060041451981c2c4a1344c85e21038100e149000b050192540ca52aa0382d03904103a00602c070b0540300a422610b140b000c6000914042a05008018801910800800b0300a0f03013200705d400458050509601a40c8844146604000420303c0e0000440007075246184c00400038003908085800740c1d00841c0c2040c1c400441c0e040034801507101641030035841302c155a44091213001d284080c02094481d16107400b20400a1900185140480d07c02402100b5828144120f21074462074034000000301c000210410b0080f00c0041c8620781c00303036114004030455610a400c05802501c20f540014401141500e01400800340302010f03105101c0352454003540c0e42c0a8038442c580a4058882e000301500c6c185010044504a203401041c401c00310700b002002001d050400460a481e188 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 302572985 1250 302571735 302571803
    0x80903040311101e0f1404050a1202120111040614120a0203060f1f230301090f0612030e03190314030703110c01060e010f030203030a0f0315030609 65
    0x80504421281000b141c02c0c0881c1c1d80350308041035075002c4d6034040c00e1801c5444125000140e4115448150340760442c02c203000c03840144402d075003403500700f5012800c030981d40d000300440081c051041e1411503039101c038140d602e1140000280314240c455450a0030360381080c02060003080417424080c0c4004040d000381e4105018800d040c80043e1611000e003030095002411143c3c0241411580303421039100c0c0d1380603103859141307483d11400d41100310030010041c0043c990124007408518801043c2400e950080e241034921408001842840880c0ca070001003005138042040801100100014990011000f0000301da058056508d09030011241e0380d8100c1d88108010007040548480b0041000114007940d070005060400044842d504001d030f0450340c0020100004980d1100000e100412400212038010321581c2055400300d400c6a0009450b40115144101000300401e00302c46100d120b42c00c540850410300784a191060746031700b00741015000c414826101d0514102e900c04c81401049414541c81c090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 302574235 1250 302572985 302573003
    0xf060c0106050f15180a0801020c0a0c0e040305121e16020d11070b0714031308011a13050402040912090305330405010605042d0e030a1413150809030403 67
    0x1000040259003082104aa0700800369a2000c50321f1482440100380c0d0480c0c440c0144244506440c0c21006070301140c1203051604484028440040d40000603034200140ca80020b240d00e580d06904d59480c0000a20100b0b54034441000f030050034400c8032032807001844203600796092400341c080151420009803460340c1c181c0d032100d482040040700087c0501160761040900d0406a81c0038020f207481c40e001a02d03c050321581c0c0e00303000c20560509103d4154561030b52401c115042c03100400241c4d840514007042c014141e200d0002404658842e8010b400716035000b80449060002c40200070305280f010b00007102c951041543e494480c00c10b101060b12030703d98039140d01c13041c1070030a2114003450001400448566481e00710206c1d640d034031802210400c034a80c074036008680d0100c510300310441000104500d0194504113000b04114408822651441c83c54209500e685440150380f07604c902c100c400328a400f80080802040404800c1e030700007149000d641c2e403030400751500741169883e8403c9100060003128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 302575485 1250 302574235 302574247
    0x130b010501111501171e030901030b030f0604080a0201061d16110a061401060503070e06031003021207093c09050d020a03032d0207020f060c0106050f15 67
    0x2c49446250000003180054490640082c0e0b0010410301081c0c008990183c4944500c00800f02d00704003164800110068100400c00c4141c00300e9101c4c441c0c60052810141c644241707801c00d440410928058480d01f804480030f07440e00e0308240c0c50395040103012400650a0402c001040441c0300403080e5000c00b055002c001c562a070a4036000000c0f035a04040c411312201c1e01d0304000c940c00c20301c0300e400001c0c083c00c0c02207500c10801b0448000306505802807014031505100784030307107264801140c2101e090300f550190380d40d44846a20b0031340c065840d48000d45c000e0201e036503c521500003140f00130803104034020030b0020030010b0001240303c048424803100b003e220030598440c4000303140303810001240c0b420000507402e821030b155175041074280c0f0072050240e0310040380c0b00c00b059890f101d902c1c403c0904c480360942242d0001c0121b0040401c4070707004001c09070003044150640d603030781d071500103e1030340107100396980c141584101c5c0c0607002900c6020b12883d608251300017a4102600050300c440349480b01780c0e103068 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 302576735 1250 302575485 302575487
    0x90b2101080d1b03030e0607080a14010e0403140c10061403010209060307050703031107060c08010512250e0f0403080a050c0702091e0a0e070b040e07080a0905010f0c08130b010501 79
    0xa51481c6044d410151501e07800c1d022032805000b458000c2e2003c3c0d540c10110300e0f040d5001c02c2600ea444161002551a283c010803d1004282280e5000360341450100d0b4101d80d441640300c070a000d140d61113142c0d4014400796105850313a6902c28022940424422040c0d11003000403d0b00701d00490aa0a810400801c0080c2c0100e1044005003209846424001100f22040001b02c0d6a40c00803401242c069a0b01c00b807156035039070842e500c280102400c41b46803808020012000d6126071000c01c0e03c0704d110340089681c03640e80c600340b104c50020b030030381d096110014505402d02c1d8551520542d02038011070804004150b8682090044900c45d0501019040c84c20400d903080c03013a5644020b1410343c032444400c40c000510301c64000442e0007001c51000218450b90500c9500303062010b144c5c13180105607000c2204100e2070901c0c1150070350004141c14018125030310010050003030210504014a42c1d403038000c408000805650006281c07070b080d56150311441d0788405101c074500c40007a201074628040c0100400140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 302577985 1250 302576735 302576777
    0x90702030f13080102070f1103120a0f050d0c2303040f0b0702010b0907090501030606020708120c0a1223090a090b0120241005040507090b2101080d 65
    0x7000050b250440b566580c0c82030b5003207030000c06d0704036001901c0d1017015046c440c141ca19681400d03000c40203010b00481c21000c03004648516440b00d400d10044240080d03c080c0114203a50b4409841101400642c00d500001001d050f040fa4800341d13400c5500150f0035030f03407001500f40c911541d400403840c08500102e803145d000e800801814442190b48030000b00c021030301c0d1700e10b1103030149515448040740d0605110015050b00e04a170040740840d480002e0030400c80310006025044103845520707555440388040c03981410b1508049001e0401c11145040340000c0342e106500303a00350f03040104c0c002c1103031043e005c2041191044510080d446410071609103c68406548131440000050400d4170301c2e6805000d00c0b414183c2c2402d58410690030100310300d00c00114401000181661800b0541c055140040449103408082c0c0140f9004550310701c0002c50701d0340203482d031401030002d05800381c0c1c560800d0b00001d40000049444242d500003880300005800340001146080c0940c1e50b11800c100d071030004010088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 302579235 1250 302577985 302577997
    0x106020f03030601050f04080d0309020f0315040605060102010b0d0804030b060a031211031605030c070605032e03020603090d02012f07060605090103120f0c03140a02010905070f0f05090702030f 85
    0x906c9405c01c00060030903070400006c62800a01c1d200803c0c0a042401040b03d09403128800b180240c0000035041c4602c0107504407142d006a0259000a003034031178a004078010444194419009901804e0038001e05c034030311000e001120f1145c88c4081207541c404080c0604006244030040c80d10140c5514414806c0c000c587d0b44459461003002c880c00c155004a0b14018000000380c02d50b450f810008144401c44024404c035000340c0458104140703182440c08104901008842c5c203950f150180386512207441019400c403100460300280066201e0811341002600c51002407212000f5610b0301074030f42c0c42404c10489024400701d1900b00d800c9810446d40860713120b41e00900046a440361340354000300d650303528004500d000e1406056201c0c854103121034042c086003101c06181040c0f1400d0240c00000a0384000424500c1c3c008610036501c4841c00f480c180d01410a41100810500920700c02042d1041c4000810b01107601c10344010700146e540342d045c03040030035050310f0400050704200480001130708040001e2007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 302580485 1250 302579235 302579257
    0x20304050f030a090f0e0c1b01021909060e030c0112200c0106030b1e0604090212100b1309120f0504030605010b120c1606050916120b0106020f0303060105 68
    0x84400001c00c03985042d58070003421100400c82100301030080c45503407441179010703107135600c0d80d0350746800c015441c1c041c0d070b001d403071007000185100003402002c8207802e4054034080030151201c0c50305000e000401510541e498001ca500182132742c11065806d107000030b11089a80c50603118041c5a000850900016094190b90b42800450f04200307201e10b900d0b404010807200f200d00e0000540302c0e0075883c0c2040f032100040c10000c0300c50b43c4c0c240c3c103403114092151a9600b02d0412200010309034000d20206a005000d400920018000e0100002080e001a00b100c42003640c01c40c3d1414169078648020001c441200c1d60240805610141c50bc1c001401140406000a000c0c188241420342c0da41d500c00644600b6004000c0300c1d03901080300145460b50540d02500000551070310b6007400543c0c1c2401840480099000d001c1d00c2d00d800c04100b100c0c0d81070011f5822030300c41c2034401c811a5100d52031440a000c0d001411142c2221000000400d98404120b0311130415502c0c010310b142d038903100011150b50700300400b011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 302581735 1250 302580485 302580493
    0x15280201060f0b070605062403040c0902120103020103060501050f030a0c0e15040603060504090b040609020a12140c0301021315050d1b030b01030b0d080706110403030c05060601020a1502030405 85
    0x403030100c0b1000e45079001401c200c00c03540e0343c41030280380c24800d50b40301410b214001d12404140c00414110302e040540740520f0340c01700d00d403280d0311814407804104251703000c40741ca14400188417900d142d040b10740c241a28001e0301c09000460307540c03004554510032462442d0101400340081600106560400040c101861414208180e54100050300321004146071600d805000981004400e07050300691006000c221000c10188030903440d8420212030003000200720617503031101c2c20704540e950100c0f4006840340561a20300680c1074a02210020b144c040382c004544140401c152040c9014000c60300c41c4540404400500d6182c68003035400b10401c9100c800c00d06c6000d010054800e00c0500c24075071800800d402e5040c85861040d0080c08448000942c1d504050a04080307005548503507203910055507220700900e990b1421400c060009005142d00c103402200d00150000505500400b81c41c0b602d030041c01170301c503e47c690000680e44c402c009400100700c0f102d00304082285000f07503400b565201380214151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 302582985 1250 302581735 302581739
    0x4050c0f0a0203030106110c0a060302131707060216050616030c0b0a2f03070e0a0f06020601240c020d02011817010e0309030a0215040306060909021528020106 70
    0x1254040d0007914050780168404001007154661100c0700c0807185610002604280c81c03002e0104914103094015201819000500c200402150f8007440f001050200c0b060b00310149100b885c1501c840782441140014814441c05004104c02c1c48110000c98400800061038400c200b0a040700d140c203042c006070300740040d80c0c41d584049540d40e030103103208062000000a05c2c40072240030051820342c50140c00144080415941042112682100c0d081585030900c0c6010208246c0090000c065a0700b00c1d9040321103000c8000b03a03031900040d1f464184e805454103aa07001c40c5840500300590002d600c59800207248800503030240c1858100d42d00c816006240030041c000c810550509050311075407000f06007001c25130a4107004002881080c07034200500d0051032070700f09403000280c4e23210704a60002c3c2c41560f0840c4000d1440851204076801180d100c20305008481e52081c5020040c40d08040c2030707028a06510004481100e045c08031340d208240c1c11081c49001419002101c0302240360140c0364155980e074000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 302584235 1250 302582985 302583007
    0x2030115141314040e0307020d02011b0c090f061a04050405040317040b0609160918090b01150201060e0402010c060b03120d230708040602071109070c0210020304050f04050c 76
    0x25030090000d0066010043c0c082c0c0f0240002c88925090380d2031542c10901c02000180d903212001c0c8140c540920700b1284051a6032806185240c241d8001420a251603800007030207100354009130741d10700c68624208240c42c0c2e40c0d00031a6a682e1101c044644a4900308030a1042d882d2662181f50018068607204203408030388000d1a01c854403c4c0c1c1c0c290781b1010502c041117164900050800da01ca41d901011140b107501d44034010701216241e01800704000c944101100400c1a1544034444903900701885400d40c1d40e603815400d0a465807580410019400c080d400305840200b102010b0041d6410303915103e09280c02c0d100c880013019a00140c40d4940102e001d181c0e045140c078009003030400000040021074070403064900d84501892502c5c040070050032000c1003961900245415400750f0002009660390105183c100070741b4400030800c0f6881984542802400e950240d400017849100792010520f2420010342607944c0e015500c0788691106520700584034a041a4000c1d6400c055001d101e64209a003a900c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 302585485 1250 302584235 302584267
    0x4081c0209060408010f0b0a0f060813050d0c0b0606040e130203011d030405040501170307120201150b04080d021513110618100302040e0f07170403180503010203011514 74
    0x101c621926919107000c0a0048081e10580302003031030232101c007a0040d20b00f03544403450600601c2074100b4003640d140090945410b40250f20040e42c2e2040550729412007004000d0b1045010031070540703000170002c000400d1410450101c80c2910004903506942c0e07075510b40b1003e4a18445501281c25540700c0310582401401031404440c00000c01014544482c20002031004450b81640031050080c40204002c0c108940801151851a000401c00048140c0400140d001d41444840440300c4d000c10380c1c0006082c4e500070301074001d591208043d580009445101203a65690b110b40200301945c1110100d205015201c0440c542d81d40b181c00c40d900d8103403800d40011203940000300042020302c00d03c0d075261502e00d096440440d10000600b011030410707080c030401460b02c0070021309141403565a0b0011405480c0140780071030340d620018074054801d00d030a00e00204001801040e06640e040720220200e4149018001e4a05a4059100da40d8012010301c4080f190000c508041c40340f03e0400300004031380d10441784 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 302586735 1250 302585485 302585489
    0x7020a0905010612060b18060712021c170f060411130f08070b0901051e0304050a02030601090b01020a06020d0b1f0f0305040b1501020c061b011404081c02090604 71
    0x2900001d155072604401906044480048001c0e042c80c09400380f0a48190070151012900181c140d407010000780030120f023480c40307000c40c0500515116407140c09020780c0041c0c1c030324100c0810080c07003001c001c24410039070320144510801e01c1000c1116000541b05c07091800380c0e0343d0103c0b005001240804415000c109070340e10128203c001d64183d4001400510312046040d00100742c00e100509865280514118440c019810711504006001810102c60214a0042c5899082a0f0607540d50b07400e151514507515282148100e000b401403200002c0c8040041c0320f60340c0c0c8040181c010f8803502c5515550380000394418028080c1c0702da1360301304c0040191900045040c02c44d222005448a09000e00009005440c0f03041c0c9030fa082500b00002c0100054804100c00d41069001d454010301450041c0180d08020703400380843c2d0084008684450b02e82040c0d000007101d140804001c014250080000c459985011a000780010703004104442c001046113460380d4142c039850702c0060800d00548006000741d8881d17 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 302587985 1250 302586735 302586749
    0x5040816030e030607080906011a1c0504030305090c0303090402070c030609080c15011a07030210050703150b1e0d110316080a060501090512030f04121518060507020307020a 76
    0xb0b02051401800c0801a19401c109141044401d603d44182c02999601c0140680d01d0554503200243c4855051101035442100b821140030746004c1003100c0d510001d160444041e40003908000104c2c03030482002c030f034200c0c1042000c2c016601e0201c0d10310078003010350b01ca0401210240c0c80c80000001054480c801c071903280d40314640050740d42080c0c0c98664034107501c400d0440b004c4816040104001c6445860304480d03a20745114094440c0c0e41c9007426400d10b0603003581001d03014100401c000e00030380d25a2004400e5091600c41c0441181c81e61201425401059141c2d000b010854022010004400000d06480992210041452540c2d00b20108064100366003521041e813080108406094000c07151540c41040140d081254514010000300700344120320466005030300c0064600c064400910456054480b44401c00da51107541e04800700b404404000165041c10440c001c0f00c0019040b80a07414101c6840740c1e845581025580761a4010a4041d20a600b5840100035807001a150300022000800c14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 302589235 1250 302587985 302587997
    0xe0405070f120209010e090703150b0a02070f0302060f0304080403080a020303060a06030507020c0415080a120f141e1b0a1b051f03111c0b1203070201030504081603 72
    0x158000c0903165902c02c42618480a00500181d181664880c0e456a06030b0300403036140d152030715801e505400034800403601c221341e074513000404604203030507600504814401303608803848590340722800d24040701d290000950100c41046406d02500110014540047c01442d072030f0329190b9240e07903240c1541d01032502038001d0f0308080100700035454001400340003800b1071305080c03003140380640b002911104200d51300c0b4031555403080b00d640072040903040c401c05001c030582222101c240078244032007140b52070010b40000078298084012440c0c491404c0c0000f8040c1c42c03a0315410b040039642032100b21010015500c1115800340a001030003500078644000d030040f50805410240e04506010f580440040261094450740c1402001039403201400d01424902c03641c007580001004000480180007040f01d40d0304d00210101c1d0326500f42c402c4d00130864505003030000c1007141140b0301c0c007405640340140e94002c502d50020f01421000d94020307041075620520405009180040c44191200d482d06640019400030368 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 302590485 1250 302589235 302589257
    0x206040c0504230702030d0c050903011104121e080f0306030601170a0206090a0308070506010e0907030c1205010b09010f210f030f020a02041b120c08160e040507 71
    0x420061580050103080d201405055070352510b0300f14014000400120a6400000003400c03680f003403059034611700601c4003d11034401032040c01049900411040c40c4254607002000c05601001803c032002c98840c4030201504010303580701d070140c1d0b480b118007240c50445014407410010780c60ba00100515040400219140d04043c1c0c00d05141c01c00580250b55000480703140c4031200f010004204036000e60403034000c1d545450f0040400c5038842d890b4401030031214046950000c0060105409040e2541203004840303582c3c0703800304140e0750b03030700c2d480081c1c03038440d02100c107114514490f810294864040c00011444c4910480400c01e03800d42613110507040204080c0030300001c40c4611208040788110070034254000426118601c084441c62401002d10a80444404c00503000f800000a41c5800030070401120000400031041045103500d0034000620680891400c04114410400a058159201802a80c400c000b07200303030255125035101404440102c3c481642e40d14007640c3d04c94000d07941d958000b52 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 302591735 1250 302590485 302590493
    0x30f050a1a070e010903080319020d050a0e0d0e0109231e03072309090a2a080303040f060e0f0a050114011d04030807030b0d05070608010803071a04020301020910020604 74
    0x1e00440c2844c100140340004001068810301540c2d00050381f945451541500041800d00901ca0b0102d0a119142000c04000360000d495120b0f50071401c02c54103030389a82680060413100035000b141d516022900d040001d015412084846042d661910b07268030a0555042000450001043c81001c400c0c20803481150080d04060092000414002060120340605041045040000c3ca001c04e805100d10740001404107508002d180b404580149400001100803103560130480764102d40c5200c2d104031480001070007500042224410354002581c0808801c8581d540e4000c1d258000080d0003034414102100a039042c2409a20100d030722031400002c141c0c0707001440101c40c0c24142e01000c01098280304a00c10380c40b1821050b6400741e0300d843d05d0784096652a0040e0014001d10792807075080f81c01d146030f110400600040445c10745406441c3c2d10026a030321000c0c540e5270700c1490710003040180c020a540150303104005419800178030040005d41000c9010b40403418103143c120b0044010380c80841440180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 302592985 1250 302591735 302591747
    0x9070501110c0102070b090d15020c0615030a020405151005040311060408070608100902030411011106060f2b051506030c01050403110a090507200313030f050a1a07 72
    0x85103010050b003055001080081d48a40d040d10409884100009203c04160703100708555410f5a404854007410041566041001f5048000311003098464031010956950a00384c2c3c07140020b0700200200100ea60715420303c40a441c001e0020705808841c1c1e0f4582003280e80d2810840030034002c0360784542d00c480c81e508243c008040d40c0c1c0e0070715001e604100b109101c44100402e6035000d940c000e0602103401d40720f1000a140800311680300c58407482c0b0200c180810408070700c000e407011aa090707076104204682d01400e15214001680c800b540204241e08500c1d0b681407000f4851510000b8000b1031100040b4462098a44080f0000455a0b034020342d2141d0321088c80803810079003020702a00244000c051201c00a080c506c618000035051001d41000d2102c144c0e40c031510714025003c820300030702c03950400110140c81c5013032148000807014012101c0c10101c0e040041515884100b000303031003011600d1521910640d80034507009442c1c03400380c001640049001c02681c10702040e2407003005041c910b0408401098 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 302594235 1250 302592985 302593007
    0x1202010e0c04110417100903050912010c051b030705010507020a1b0501090303030203061c080301060207050105070f020f0315070905010e0301052403210904060e161b060509070501 79
    0x124620b404100f4034070380c246006941c259100100c1c9400c0a0043e00380d014686050014908110350074400300340205507200001d0b000c000c0382aa00380180170004510b59007600e00306000040056803d000d1100d6100d241446075001c05030300c0341540c1c680a416296203081d14403c030350940260f40607003401c0080051000d16421600e452401c03c0d19100e040c10002400ca42441c030000d0101500800880c02e0381d036600040148030703490a01d0303071034008550f4030300381400d40c00034815030016009241c00018154003410440308056800501c03054030231080d60800c5218031041040d590544101082003100c40b88680e0074501840f03a40c1c40381408180b5080005041d480c0c4034120502a03410401441b6010140810319440c00762a01c40100c6c06881603000310b443c00c1803500a01c901190800211007104800500038000315600f9201445240c0d00d9080036081140240c40d84200a1030581800d05024030507901501e03024100c8541040806d2181ca07107009603001a03890010941082c4420402c542c0c0110035142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 302595485 1250 302594235 302594239
    0x31a010f03090b0c18060a0c03080402041b08040c05040608070302060d1d030903010b18070f180f14010e031f0204030b04060e010e06060315100902040f0f050306040209060607050a1202010e0c 84
    0x200e0555003d00090023441c0c070800c01010302c81c1400103c2c04566540e002504100c0e440c2842448190110b5001001d09200751016602254072030300105082c20a8010541a122814000e200c946e2541d0300707114042d800103038105589036903841601d14032059400d4050340f501a00c03000390b894103c10301c209801c40754104003284c410404162031540c0f0130b020b081441e030302c1aa036042c1140d13000c03800394041c0d44501550040c194030310451b0001141ca09030545c0b00c9401c1d18001c0c03201c0300000305000019a07a0018008032107a00d54420449100c40c030303114102403112848005800b5041542e03e9442c1c142c1c0703600c01d0341c0455101d41c485c0c00071a1091424420302c0c505c0311109004000c02e081400200b61298000341c1c00c22a2a0314200014170021100500c25008207001c640441d070742c503a640c220941203400c40c000c0740c4c208401b9000000706481c00080e142d00480c1c0041c010a40364540358100300c3c440d400100c04440d0b901035031402402294005910858001154002140c800e801102c50350428511000c424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 302596735 1250 302595485 302595487
    0x8190302030601121a0411120c090102070b300a0f060e0c0a030b031902010f0804050607050a0c0203010c0503012c0a05060a1a09010f031a010f03090b0c1806 69
    0x48143d0b0b0b07026919102c200c00b8900b00155000b404140d20b0100910f00300d205810600f090340b10140c40491100900700c001986c40301d0346041d00d41400b40a1184102801580140d00c040020720200c0300d060010100c049414162186519208100035040a50030302d12b0300045401d1b030200021036035180103220400c04000ba08012042c14095482d04842000d06488403948011941141e014060341c40210301703c00c010111943d43c81c021120182000317030a041240040c1c80180c0bc0d40c4d03824010b07003946010301c0d40034019142a903502101101c00390031101c8030f0010003030b4078942ca01c05600c0078411001601e4590750740c40ea4a44c103002c00f42c101d0030001b04903ca02480d000030205030703139600160300c9600300e51468030100d440d40b90307d40010004003844e0007030900320002c0c00c114403400c1d40e150000c1409801c281c0711121320001c40103056048034042c100000c16503482a01c0000c81c0c2d07214a0031506401924180000e04880c02c1c0c0b9002c86494003114441c1c240c03600042d00100185040109000400080b100c0c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 302597985 1250 302596735 302596741
    0x21b09040507061b0c0f0503190b0609060a090207050106060e030a030914060c070602010219030c080f040c1a04030203010f0c0f11010f05041b060311070807061104030819030203 78
    0x2203540d0405807150f8010061244218402c00d54584400140c040e0020a07040c6142d03180c6c0201c4055400c94418540700e8841c0c03003c04804a20f040c0d40406490fa0885a4842c0341e6940310203200c1000d20050200380d0000310300c14003061030340461001d00185405480002003403410550054514030707504075050305c258030851425001990003041380013920b005080c40c444015140d400704001b400750441c198540d010b1880c021074083d50542c05001510740180c0030075001d1284200c2074084403030065102000a5003070000440b5440003145464203d4458a074521311035030b03294050303009d03008041118005c41c040042e04006510b0240240c521b02c0b111181c0c00c219540c04010050701c42c0c40718a04c1d90301485508841940300b52420340c04501c0e001a800f409008502e0140782c50b4802c00301c2c84850712541d84e0086030120320144680b280c101d0300b80020010b2841d09419841e0181242c00c4810200c0d180c40c0c641e0682c00c14142d24074007a000a5100c0c041c5642c540784c0390f0468400c0c000300704070700e001054414010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 302599235 1250 302597985 302597993
    0x20a1706030318061e1909031a13020402030709181505121c09031505010b160203030c0f070f09050702030d020c03090901060905040b04020f09011808070303021b0904 73
    0xf140d5032010310590401031400c29801144241c0281140c00d0200703040c40400d01744a242e81001020080b401341c035a540207151084c01940c01d12140c0c000034102c5508844d0300c0740b1a441d04100b0300d400000d601100052100640d0016069074800c60340400011107a903001c200b4020003440843d03400c0501102440010601540311000070101d100741c0b40324585014840314080000d0001c0d00c8aa00002c48190446082820140c09552503200840d0001c420f8501c040c0c41d98000c3c81024180d46007140024500750641140c8809031348050301c00d9a01d40802c011350f00c0d12071010414510f14041c8100640304091500400b40703030b1528950b02000405080604104410380e0100c215007003000e0440005864650801c4c440c1c1c03550160081a5030030200c0407001044031608000b09800b02d032001c640070f000d4940300d44c0501081c0e00130752221035248102480a02c040c0d60160700c20001e84c00d005d08061841c07a5440e040e581c6400000c0c0c1c400d070050f800600d0302050303802520000c2c04030408140d40605980c105991 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 302600485 1250 302599235 302599237
    0xc01020a0f1113050a1512051c0302040b07140d0c0b0606160b0a050405010606020c030303010b1e07140c010f0f11191401050106020d08040b0709090f020a17060303 72
    0x1800400382114005022860358428240d420f001c482c1a07001c000c80e00c0c14220800040030f4550013074150034a00d1400003203400300043d0b0300b202d6540c031002801c0888900c4180d09440f18440d003401781495024000810901c00c0c0002601c10b140c00365148050079a0700030402d80c02c1a4001100b80d08001c0a107810b14042000d03070700820340065082d142141d882c240410448841c040385a4010304084c00c400600c143d12010f0b801c0907000d94020342c001c01c41d00340e030780c003050340e0b51500008cc554140d0414001000841140c2c00500480f0000112800c0d00509049000290703900c03c200c1120f41559040300301c83c00040c2080503030b081035002c0c2407031490444001005043d03504644052801c003c62480840300021083c05038030342d54051812024649003003485e2a070343d0004403000c10070317542d0318250001074a41d200003180706180d042500c1d40c202a4645884404190000038003d4007400411034000483e00d24078859500c40fa03c21090060f21500740782c500503da40c4800b8191290301e103610050101039030f0040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 302601735 1250 302600485 302600513
    0x60513050a050a0e1203041a010611060108071a03060d060c0f0905030c010e040504020d1b29040b07050f060709051207050102190f020d03020f070b04061d0d0609060b030c01020a 78
    0x4980503071291f84503d0700e4004100c04c02c400d020741c411480c000003401074005050741011501002902c00f81d80e262204103640d41024401d4200c009a51050300072034211403001941c00400203040071a8012180c0c8503401941d070000195070005d0061001d58064030342c400e0301c0d400604001c80243c9851041d100000301140360703004109204079503600c0410119910b1580959010b940038140142022100c0c0740302465111601c01c80442000d18030100c820040c540c4070000349012000009401d141c10039484880e15001903104523154810310030055a0a50104040c900c5040130360749038007425091505000d04080b244158106030b0780311400903c175583e00403d83c0e045a42d008804810030b50303110b00380b20b41074002d030240c0a5048506441008103169010400c42c3c0e0708080750040754820b50385c0c1c0c3d030048500e1080c6d21903180054840188d006c507200c1c0105961074103010082610315600c0207600d0f0101240e03010038044a03050340e42c000401803402c1c140130720b0389161800d0000c0c210700a160303101d401c0030701020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 302602985 1250 302601735 302601763
    0x10b09060715180b0105040e0703020904030c03140c011d010510090b04090611031e0f0705130b0334170c0403080d0603020301060e04030c0605070201060513050a050a0e 74
    0x1080310407418501c3e601000c8420341c280c698010300305041c00c04408001c1e0a005950041d81050300c1c0c0358117050700103403460480c0d5001e440e0740b00c25a515241101c0b24121540308404001401b00c08160005400001d0030345c1c42201d600004440450b00030b40d80003110340c0c0c540401264100820444c8c9544004010360844400c20004544070b00c29600044c000c00000c00014080351401c1c62060001c01c41c84040c1d13100d0381641d9400e0003422044244c131104040101c2c0c440f800d844407400002e003298440c1d0003400740110f90619000c26980c88401d0514144c008030341070301e00b070032036502c4c2c84160080266a09542c0b00041042c07802c1070b8044c22009050815000300c0b071014100440202d51101441d80480b8025a046080c0719203c80131000a80054511807000313a100398202440070643e1350411110600859150f11000030011199844902a040090014056550750000092142c0383d02d0f070103040b0380c50070620000c0d0f1407502c1c00411080b904080c2c404c01d8a85c3c5415000c2640100000c0d9585604400b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 302604235 1250 302602985 302603003
    0x50f0d1212020408013209060a020d02070b010314060f060102100b12150912040b09120c03060106021e032506090f0f02010e01020109020f040e030d020a0203040608010b090607 77
    0x15549181c00640305551114590350720303084042071100c00c443c1c219492205c80c60700416010210700641001e200050303446019607000031002c01c0760221030303034002c2001828154016060078a26220300c4c1646400742c0c0306540310170209443c41c02902041c0440c40c0e05c1200e103404c0407a18104440001d40d6071400c0ca8040c00d46566030280003056580310a1031354424045001211642181100200c2d4594030580d007213469885540d10110340a02c0540554040e42e0444000e00d06061030142089803031404036040324a54069441c00e40100e071401c1c001035001c0c01564008040700619890001800d80703001941e100e0680041c0070403408268130104251000c0102a2860740b00310302c2d410500014030084500414070b41a0161080401c9102114404164001d80b2011490354520340160f003070320501080254002d0346003807400000c1c41d156100125810b0b401d01241c0c10502c511100c0c03812640300300d5081d001b40e44046820840c3c00d0740f01c0502c0c0d000d861103021181c100680710012541034016580c004045403d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 302605485 1250 302604235 302604257
    0x52713030905060705071a0a12020c19060f0c02030a020d081314120304030f080603160b030a111201090b010f09061b0f0605090d030212010b070203120310050f0d12 72
    0x1c01b0480d51703014201519640c00410341058a00b0f00940c48100c0190104181d280c682d41801e00070310984904242c1c0e0b0300070b08a6100000c4a000b90004190740480c1c03003030f50303071014000c0c8503466105081e280e0080e60004d40d80c0f0040c0c400e01920f41107a801c0180208103502040100c0c0c0000000c00c5818598048241091130b0702e201c1000781800c010042c83e101711003000c81044185a480b02405a9101442d115802642c07521801c1c10340701c01e100c54019055101660303041001c1c0c0c0a0000569000303800100c001a182c88104070310032070ba4003c240b103442030050440148052500c42c03091022095003400d00e42140080f4040107002140d0501c208024080703606605209009490840700009a100c24400d40800c2c8514003000207040c281d507070001e64410109620a03141c0a032003241c22151808011040d2a880e18922851507072101c0c504a0709406591030341849102150061400740003102c0410300141d003030070b0500c00701145100e19244100f10103028140481c2c9442740b4000100a285820403030b40b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 302606735 1250 302605485 302605493
    0x61403030d020a0309050616080c0f07021009051507060e1c23040806090d140714010b0405040f060e16090c020c0a06030b090a110307180527130309050607 68
    0x82e41e1742d40a0a240242020072080741031350341035004040a5900d480c42562601a82c2202d81e01a088440d003164000304911005403600c018036400080e0107181491072180c4410201d08a4810710410080414001c100c4104100b03a5001d030032140c2d041c9600901e14010344c00c194054000b2032910b00801d01891441080a1152000c1d00000c1d481050000350794a69032445502e95402c01114811203a016405071410707490320603406091041285e100a909003200c41d1a490000356040340c054405650300c41440c0015121402024812401040d03450180542801d150080d510f40701d00b4128180c01c90545042d881082100600035103141c1d0030b0005205e000d05000348e2a02c44002141503214012180000c2c1032a0300d504070028440041e1800c020b5501c41641c00410b440641001c494250001d10000d00814400d50034090404542c1d10401c291954800100b80e0b02c00c2c1000f01d0000f0395100c802d0310640c03031141011154000c2d030a8a103400c0d025406131802007113220381d4001c051080c6030000e0b00c5000d00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 302607985 1250 302606735 302606741
    0xe1c050d0204030b070e04050703110910051b1608010b1302090310091412090604150c0f0b01050901120515090a020306150901050607031d01030f020a030609061403030d020a03 77
    0x39603441455100c9605001034040e101e90013014410381f08034101400611210321a00400003204400445141030111442c1000084804540c04808105092103401c80640003080891a101c0c0080c0c05422602c044400500006085806c1070446038103080507018640c55020176460341c00d48800d80161150741140001f0f00f050740003d5105451410074000341e080c000c0d900f4194420b030b4016012150040c42c142c0c54550140181980b60741e108005000c100007004098106020154142c81d044d080410259035060ba517182c44032081d18400c40c1c010040c007182c240242c40c58007426001052403a46881c1c2e41e91295103044424941803100d84020109020100810190b9003030381d070060940d4070518000c000001a03107122400e240c42004000000260740c01c4c014100e0720265010f940709201200c0065107200507107181142d4504065491403901c040111f41c1c4050000f0381c1c225600400c242d8600201501520b1450f08010244110310b006407440d03690010444681e007901d40005602e41e1040d200603801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 302609235 1250 302607985 302607989
    0x10306030b040605090c01140304020409020d050a0b040317041110030b0a091b0809190f020402120603070b190815120a0302190b040f020a080708010207060e1c050d0204 74
    0x18007010051000700300c0d840d0020f51151034581c044a000520f00c0c0300440700021509044205032004001050240c1059081a440680003808106506080b980c40710303c0d082141c0004d4840c0815007081c002019803005e10f1408280c01e20f41c0c00060383c00d280c1c44190300401c0d480f4541c2d01c00d041800140310414040d0b08081f0800da0020031600a06980c0c40b8008080d0050401558440405400c00202c550146000301c0c002c6907460000d004010001c0b209000700485000c064848152103102d400049c0d585000030841c00c1e62044826019090280505187c9030707071500843c580c803005008030b000c290b04030310314680300c0d60765494404582d0301d4082104118040020107142c10642411041072410070002c0d100c500107209a0840702c804c22820303401b4010840c5003100a10070f50401000c2400b041c168030355880b200e8001401002500c2e5100c1c2c1c07441c83e2034410380c07290042d41d401050031010310500d0301c6040c540302048009003981900c0f186d0302a00311600340d2040c000340480414500380c100e5540d815140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 302610485 1250 302609235 302609243
    0xb0106140d020d2c010b100806100c020d1415040b190e070b030f0106031806020904020d05012706031122020a0909050c07170307111603021809031801030603 69
    0x8100e03480c42d02c4c0310502c10310f074400c402490340c00c01c00c4018041c244960090080d880303960355460141c036594200400300035003001540c2001001100d000240c0e44081e0707540440d038420030b0000c2d661111100da46040c82c0c0c2542d2031391000d01d16401004080b45059030540da10102d000c40442003500c8401c1840014845202d041d41107114074040480d13002c441000030750003176600c039142c4460303030ba61240d00b10103a031050b41001608481c00c0703180c0d000141c25a00546030a42c0000e00140c10592a280c1900c1115401d0344004244006511218071800820103a911110320703000c002d002940c216107408001903c8000700d00d001d0b16400c10340100d048624581884c4082004606540d904651440200100d100740030f0070f02c560f46840042009540b6041c200c40b440303948442c464804814164040e442a00000c10315000d2100e8041e4066500006004180229032000404c58401e0308500600107404410312040c5900e01c0da080511503000b01c00020f80344d0340015211340a00c650301000040f005008140c2c4018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 302611735 1250 302610485 302610521
    0x70c080a020f0a08252406090e06060901050114070b10030803010609080d0306080d0c060b06161506060912081b030d1a06071e080a0203070b0106140d020d 68
    0x308001400008081c031010711804200141e10005189017242c000d035000074600c0032079880591003000590324000140fa400d40380000c8640d80c5044071070a951112164194a801c088200000d500e010703212540582000c3c6000031100b600c5030704a00152080083c094400c110520000300d4903100d035154035000d168030011590310b80d60745080c040d0150740c96014000d100e02441b420b00034801e109118220469000302d00401e048845e0500c19644400d9800056401648038070301501c1c983c99401c01001c1120000f907a00d5114181d6003403079903448140490613a0340504111041155552000320001521007400000c54100200d2030020380510801d013551401c0c0b03a07840ba40b18829280403000c0e0141a41c0e0500078058058240d884801399a070312a440c2ea804402840848082180f00071a465142403640c20040c01404507110f42c000d54114030070700c2006901c0040c4440400541c1500c05004000504103004071041203070400c2414000d171548150840d90204083c41c2d03c0003603401a003000b1030070031465 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 302612985 1250 302611735 302611753
    0x807180b0715090c080d08280605120d030b06030402030606011d1806030c090907090c02030903070305030702010908030306030a0311011d06101d0c1b1504060e0105070c080a020f 78
    0x260100400300d01c503a43c6280504081c54001d00e004801d0303203100322020301184004144203604235010f00c0d0542e41402640da521000031076182c4a020010443c591480c00508400801182c01070039070b4192582613000c3c280c2402488010b0f100000d07420b1b040701003428580074501c81c076002c010462600a20031580b00e00604504504078142d011280c2c094142541036846441c0c15201307020544e40d040d19080317007590003048108045210360380401c0007803c0714410349150a12000000b46810115001682d86803c0000c0d030800315070b040664034004001c000b0140d8118a4000c3c00252203410b03190000d07007808401500e42c0b465140a500c40300c0307903044000288028034000c03c20a0390310070f01100c00510007800c4000200f141610100840a140581c0c40714200e0750f65021000c480503009802d15690300c180c08241c2c007400a0040c03203203241c00c0c1818501d01d141403825003001c4040d00d20303c84004081da40f500050250599200e0303000034003550440500c0c1da03038102d07038a0101d145c011031180c0c221a82c0600008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 302614235 1250 302612985 302612993
    0x2180702101121040f170702060409020301090b0a0f091a0907020a0302010f0b03120903070f080d030c050304030206060f1f0804051006080a03030c0e040e0d0807180b071509 76
    0x682241000741c0c031088000d1005841c18451080103850160a4407081021080091b4020a14202c1180d070b502c4c042d81030008a034040b4105402603080001c05030380110050148030241c3c4034001a201d421151180c4c210b1412500c1008170725a0b020344140aa120b801180040e01410070041d00c000c07000d0272554040c60052402505da60340c0e10402c90040d4280303a10b20000440300e0046221600c4010040c101040710103140e40c40b2903100100c0f80f44c05008442e800a508500d13215400010a20b10000d0548118003810043c1110000100101805002d10074080440da00207140f036400081900c5503001583c00c0130014508800f00001e075001807403080088000641c0c0204810b000e240b04000703c85d14110185170610540703206e130181c03008a42c400481d04000c02c1c4a0742120b8802d0f02c01d070034066118000b0802007419613954000d06000d40d4003e1854143c13240d1306c000707aa54410503500e401200020041441144820117100300380c0e03007240205100c000e00404455080708200b0410007040140b9203450 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 302615485 1250 302614235 302614237
    0x5150904050c040b0a0e030a02030a03020f0c100e0909010f060b130f0605030610030e1605100918021e1204052a0904050a0c0906090c0c021807021011 66
    0x1005030301550a00001c11401c0c8032140985042c1c80b080b10040341050b500e1201103c500007404001075040c0310300c00c40782002d0b0300e050140003075040c003c4d4050002c050414145a203062200c00a0f280154800d502c0094020380c0001c0c06002443e04031a10585a110300c42d07620301409014082c40c40861400ca0002151000c0000800c0003282ca41642c00000740e0b1200388050b103013110b1040002003441000042c0700392402400d0b4116508690800040900100d82d60602d84a101c81007407403540c40c3d1602c107100781d24008595030101001c40c6070160801cbd01349030039050030030000007044086039008105803040040780c240412940800000240c1c83d1048000e00c901045000e650946480c050801404035a502c070660013050850400460410f20320000144810300c0c070010015140c03805240b11040010340d51040981c020301d41210b000c21410300300711a8000f140c034642c94180610840c00080c40040e19881054550100c0740c0c080c100030b61b40d4240c000da092503080e0a804081910300540c03e800640694 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 302616735 1250 302615485 302615497
    0x1140f1806030c0118050108060607080706060e09210a02150a0603021219170409050412021009030210090809060c07150804020d020411090d0507091119180515 70
    0x24101c83d02d280720040150b404e80d100b00400d081143d100d040034400c950140d062907070440c20250106203042c2c40780e00d8030401500304000403502aa11954100600c0550007040c030f40040110703025105075640e41801c3d41c0a40c50300c1803c9081c203400440c010f13600900901515a800a01026000b81881c01d101e0340002480355000c12031080140c20b06086001d08001440030342c1000c04181c031400c044050b201d1105c00f10004c180d54056070420000410050840e0148030b00032846184042ca104c3d1030003102905000f00c9203008040c00e03203445400008254005400303240002003540006840c012800c0040481c45070158841c1c024500180c080081e00300014550102c440c5401001644258642c003110f03032040603039011b50b004080109003005482c19502441d50a003079100341618164101020501e4a010600b05440a80010108000d1016540188200b65030400a52403401100066005840d0408060b0303008024110781001d110299172080400540b030000c09488011600d01103600099000b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 302617985 1250 302616735 302616739
    0x1b0307060801030503180a1d2505160f0506010303080106031b08010512010f150305280803100308030a06091a01120e01091e1e0302030301140f1806 65
    0x42400010341921038901c41d81a60b50150103145410441d2658503491006154003590000400c1c00019860800b8100ca108860a0620800c800c4c940000079620f01e00c4410890003001041d0480c1081d00c41c0d01004036110030321341d00400d040c18205424402406001041c00034124807407200080145030b0130521040c12034905907024884900002d0440c45040c01c1d400f0f481c0049060034005001c20700d403941404503042c680e6000098100803031390000c011788007041f182c3c4141042400042c424000c0c00d00010b00d1000541814041007010819101c014010702400a071100e0408004900c0c0c20403000c6500307005541020780a6102c1c141750324100014040b0744950742d44649040044071040c010110503092000c01612508a0b982801080801078041c10542454035503135903940900144044c11110b110391f4141030a00010403840c0b90010902140000c14800d021020507100c000030350000840b03041d5500000180e00707032641365002c030314021141d10455a00022401d000000750410b8080c00e4440c1d803007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 302619235 1250 302617985 302617993
    0x20d110703050919050904020f040e1e0c010503090303060906060d0504030f0e040e0a2a1511070308030109020d09060f15060f0c1b030f0605040203060709082109031b03 74
    0x1d00c4000d0081030084c032a00d90041d551b00c00040142c0761821102c0449940a400413884150595245040c640a24a0210000c000079100381009001300420b1139024000c0c2441c40c90341c14810011039807400300800c400d00c41c002c0e01c400101162602c0d82070303034100044200d00344614205460080c021541040002001900c0c609191401f03203058002e201e103516900000d402d041c5d4160321403000d001010030320303c070108200c82c020346841800c038020343c0b008000c04644840c1840c0104402070081c0c0b40d94012031300a900140c0d06002240b1280200c1c0c0c111410180016501e48100a0610191004c0c000c080c10051034065070840c0b41d1901e80000f903413908003024000b141501c5110680e046101c0c80c2c0340400007031221041100080d07401c0c8005074921645907880f000e0a41d00c0c0d1f01c01c410651200030803a039050310fa400344030841c00c041024a8105c40c4600f4201800303410954003640d41c0c01011005003002004900d8441e81410030030844001090145c1501d01c031442e0401c100300719035104010301d8084e1003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 302620485 1250 302619235 302619259
    0x2150d050c04030f0b040201050c0d09030b18030a030b0103110d020d0507030c0210020306040b030d020708010c031b0c1109130b010909030e010f09081b03010b0d0b0703020d1107030509 81
    0x1420000c40b02034070741c002d0040d804240142c1303400c003101600801c12414410100003413440ca5004101020000c40956210400942580780140702804040d04d911070200f50240310151442021043d55a1703110b45160003e004000d20004a0103045030b440044552117000600c640700d810a41c000f0f1840b060311030028001d540300c03c0f131f04400701e4034009011401a04000394440400500c0c0d0000c5070040c10040c00070440c0407509002904000c82310303441c140035038010b140c10080750500380106c8418101c81d0030200b1030040740b010005000b1500602c10002c00c500c4001e21003c100b45465224030502010b04010300174a043d105078921000c170b41300301b41c4004036403000009041c1040d003d110400c2d40e150f940e0071b41040c005401510b1055601510300140035035041c01041d145402c20460541039649028885002141c1c4141821640300c3e102d068000d614860311000416252120250040164500140e0b00d003204452880140680d0208500900700007503803006142e4840c001d480752003000c90f10401e4480c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 302621735 1250 302620485 302620501
    0xf0e0901150305060604020c07090204080607080708060609010c061e1a09130807260307031b091e0803040f080d05070b060d02040b040e151e130203010902150d05 71
    0x1d52000034902d91000c0001a0136007019000b500c0c0701c6d640e00040300c1c2c0c0141ca5195007070070703a017080c2c1140d4800e600040400070606d07401446150003006504000d6120704020300810740da8800d81422506200110b9a40420021a941b01119250744200030311018040e2504210140020248000c4400d0000300d00c204145403001c006400340030302c005800d06030b440f0380c0e9651f80b058111410586000040da6054204544074210282812302c03a042d0496891802840190458850800703400c1c5041e00d041c0314a400070380180c1402e05885490004400c3c962116032080805c03072060300400d409000208000910300f982060120640d24504190b4940c2c0c5165081100c09010b0600d0180850220b44040b031628100f6184003600d642c009400030401605039000302c3c0503242000b200d92002d034001003a00da074020318a140c0c0d03038104802c0e0300c0380c00c1c41121414100c1030141001c5e20032546602c150b45481c00710740d0254085882c0f030b40c1c040d086842096420302c44406680114500c07512560500c1d000035559 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 302622985 1250 302621735 302621771
    0x110910121b08160306090f1707020a0b070305030708100f030b01090509011104030f0c032009060f240d0507080901051e04080924071a010302030c09070203040f0e0901 73
    0x38810f55a0900000b80703942c4031900580886002503075070b030b00b85161200100751901000b6104012240c24203036038000c94418050302030900d900400007910184900e50000c1e62203130880e900b02200707180c502003a888201c0384052144403a44039060f6894903001c0002005a13148100303040f560300b03180c204110fa448190090990706009041c0c10010001c200500001c0d0b1014a8404007900900030010080d07100e64038442c40d06410003182545045018610303801d840c1111607150f00039001d451121105000f5400b0542e400508142c038100c0320320305029030100c04181c5003510280090040144000d003031444000d0300c03140045c0c41015295082070001040d402d4032040c03240e11030310201000c15560703941d6241c40d04150005c110352075010007483c203c2c1c0f00103020340b825400580d9440710080d075108075602d40b11250340304000341c100c00c00c4010301c010070159901064071511200c0554007002150f03120301d0103d065118942010703090030040a03002c580d080113181602d108011450081040c3d000f00000b007640c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 302624235 1250 302622985 302623003
    0x60406030c03020d0302030f03010b1209010903091203110a060b1c021f02010f0f0b010306090b030d032a0c0b070203071106090a030503181c110910121b08 68
    0x1561140c400e04200504084c10511401800b82c0305484c10311480c11400500c0c1d610aa00c10340c0e46101c01300b00320390403242403240741e80c024807200000c0107101540d66020340f001c2c45a21034005110141442d500c00d05004000c4064850140d40544002c0c0c861440d101c001090520801d03030060940c12a9a43c6541ca980c1c421070404c1c0d0003d2588110b08980c41c20801c030b426420490104554a0b90f4403000540000e024200c4248000ca501013124001c51000600700e80b1654422781280f800c00541c500e994901140c040241c103107901d008500b9981d850304400c5136800040d0510f141128920012411907030100300e51406a1042001a0560f100d40c502240d5078015082c0150440f014000741b140c280c6865001491046c201909d10144d05603a900c0d501d00350b03084240c115042d0a8060f000c450b040c50000301d54a0102c22280e007a040c00c4009131030320460000010807460044418001041d07040090082c208010305031140314038010443e62902d1078199000014004440e000010045070f081004904d841c0c3c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 302625485 1250 302624235 302624243
    0x10e0702030315120a030201051b04180203040f020904050102090117040803070833030609011514010302040512010c02010b030319200105010f080c030a0812180105190506040603 78
    0x10854841c4000f07090320303010381c9101c1940510341c1034203025401070a02001e40b44500030380000902e0b150058041c0503403c055070140b40d204404100612004803c48560111402c4e10a070041e200d41c4d0303500c1c008000030f440340e40181d8040c1074207040004210054000305406082039070307003880304103c9514420005006450003402c00c00c040c40080c80243c4503a078a181d11071085000305405482d200c80034101c5401c002c131003203070031845003400d10010b0404000140d04084c50f0070081001780d46c60034480c644803229016242e003144404035080080c0e803290301600c1c081d00c40204450030040c0305811040c000c1c4241041c0d00059400e01e440e00c507841c90701005460301e040382d0308444401c1d03856203401240e1140500900b030701e0401840d10480c515100900c05c99000e40b03d585201130303440e42045041454440130340a107a103c0da00142c1e05c500098036031070642e41e0411749140000c0103601d550380015058120210901417a45ca031104201c04c4c50300141001049501d095002c2181c0e4849000b4801a80d002e404050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 302626735 1250 302625485 302625487
    0x304031527030906020c13020a140d09020f06120f091606031a042a020102071a061309170711040c0905120f03090f0d0b090c120c22060306060905040b010e070203 71
    0x3850420260000c01038035252b0720f4220842920f00c21140340079003040148000300c03691405000304504001c0410112010202eaa09081c0089851489900e80c0001c04040c495100d0390b004c0364010108002c2ca15102588440d1a016a0f48411008005080303580c100c030b940503c00100044241024030a0300c4651400710310500200030000181a64030a00b800041c00f190760030402000842c1c2980e500084c80d081b140103030942c078100203080040d0704d0504a04148a540f401d0503034000036040c110b40710008003042e480e5507124001801c040f000c0c0e120824030640c00900385008507000ca580104110140c42c82101c100d20448007404040b9640c8020654881042c1c0c8100b101254520344904407441a10300240400701e41c074500d595800911005440b10001d50b4400102ea05440ca85800c010803040d11200045c110105030600052030142898552500d140b080d03132200ca100401034005901550700004240103003565030490200030041150269101c0c103d410010841e005140a02b41c040c000e250b0081d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 302627985 1250 302626735 302626759
    0x21e03030708010501031e021e030109020403030314070f0c0305210a050109020f030a0f09051e0d080610080c041a0c0d050405030706080604140a0b030f0f0304031527030906020c 78
    0x1f08000f9444002c00245806d2074400c40384200c1c4041000b1400ba00c40700d040540c0703c0e880c514016050341c926104045607c0044810400c40e580d010348122150880c40c58196040003c0e810142c56034401e854031229086244038115000304a03510103140614107411041280e0782c6c0ea290107208130300032040302502d008800c00200e40c80c6580d41e0402c8840701e000c031400140d69110396440d21b00d4400018088020380c48c000b070b40310302c42c110180710b2186414a0b5041003c51440c0500019041140000f45c110a00286a011a06103020141600c0150003050030550f400014203444412070f41003440801c4082c0f1a9404d104c2900303102d030060350212400503000b420407501f00380d07080d11048801096680c11a07542c02d05140030b40e00c40d01001c3e000c3c40318110000755a04644040c5400d110380c0e82800c09440d485092802d0840000000f201c080301d4210801c0070247c111401160090300840e441d07840d0300458140d122140300034540c0000c1c0414800e40355102e651b6502c803000da0701c41552080584d0701640644030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 302629235 1250 302627985 302628041
    0x5010207050303181219030801090506220e070f0509010504140f090102091e09181b0d02030a0305030610030608070902090d020307030b0108070b04030b0c0a021e0303070801050103 79
    0x11081072018010002031543c410307850314902e0094003040a40005403004108001e07d034009000074050050903a0910680c0381c51000f03d2482d44010342c480fa01c3c20000e20700e5a0003002d440d800090800a0042520303030840d556990000b40b000c0038044c07c0c1c4a4100c5800004044c9450302c40c44400390000a9800361aa07100c82202c101c450700200b58615954007046484440d0352524106c0c0300e4000d000c107032810702070040380501403d5040203007018009035170940c642100c92030000c1e5501d90400d03801c403d80b0411060b500801c860344140c4400079014428039541c407007099007040103948a0101650200800d090301c683c11802d50b601403143e41e0540d0441c020502680b9480e4004009003840170f000394903c50003030307404286010503942c000e51b08822840018006240188031100080c11410001800e03e821502e5803240070030042c001155184000680d051024003e00280c5150300140715000c1181a004031019200d45c81190201c00144d0003600206041d8024840c02c000d084103e088500720f43c0d80044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 302630485 1250 302629235 302629267
    0x30615080303060d061d0d050a120e10020a030609090807030e1008010e060d0503030a050402130902011218050708150f010e04062a050d0c091206091e11010905010207050303 76
    0x55801e905203900b200b4000003100030001f00c204103180b42e0311035645100030203006081031034001c100c2c2c0a007070030404030410b9007500003807140d40ea00c044800166942d02040c0c1c02c1d001000c0591049036000d040c2030f861428840600080d00d0120b00076140c107003a0700450005c000044007240d84d400085090240184561151440240e034030203030240100708101d0490303d600786107410440740404065220002c00c411030401941c410100c1c40d4843e4244a41005540017a04440c20809481201a6076000000250101ca00040d0406801c101031703030022500d415072103890700c0034a58001c80c056049008500c2c010101b4640d1812079462080c0700b242074882da9106405022400841c907548040807030400e00405450b082940341620b075445907a0b58211910b4480241c440000300f003014010003a40c20001c400d541e034450b0822035445080055034210394507041d601c4e12094186843c4030300e8400721080800904008035841100241c031885045980c54004a0b40c901e003a002d05078141c0c009102120b0907a9082c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 302631735 1250 302630485 302630501
    0x6060a0e040b160513080c0a1512090c0e011d0108030405100e01120507020307031211030402011427031006080d0c020f090a021e0c1507020a0b01030615080303060d06 73
    0x4c501a4504105410514a0702c034882e00001501d07000100d10301481d182507510400208060781550380e5410032100050000d6401c0213180f0380c8251200540002c00c010240c0f21400b41444400600c4156100c2c0a00f48410000b10000d842c0440c00c00008120344070000705407022160024a00f88052500c10000ca4109040d0000355050042c02c406003020340c4030700e010b510320410300c1d54004c42d100c48040c14020034800651400c0c1461500c0c140446684a20501c200c0e5407182d02800c0c41d0f210702122440308030b81849045000e1041c024840003800c00c5802444c0e04030b0f4410b60480407030720342c0219104c404044900303138480c0940720fa100c00002c01500703001e015580411800180055020340c40300b004900888001c0b107803c0006940000d484050040392000c00c021800b003011480c0c01d04451106095640d0140c40306406458034800020303060500c02c000785c05c2076030307070250400c1a035503564a0b00c00c014090203e41c040540d10081070100e05100000306032445034800500140745c840c0c00c0e450703440081c8014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 302632985 1250 302631735 302631737
    0x33a03060f12210206061507051b13020f03061e0d0b060f060d02070b010e09060a0923010c030f0b010518030f030703021605010807120f1d06060a0e040b16 68
    0x282c0d154403010b4615105203c21400343c014050311b1030041c003000a2242a070005070070f03448051203040041100015100740c071010b140fa08140403000c1000084810b01b0350b0780381c01d51250000803c01c4c0a85081000703507005100940b080c86c01003800a8494138400c99070445141c0001032500203001040130480280e030400c2c0003a280da0401c0b0600404500c440e03200e12016036616400284040070040b850b80e0003401403c03007100200da40d0401118490b1510000b6003a11501a15809281305000c02503402003e070460001f400f642070110002c0b00d501a029800900000c2440c1c1000318949400601600000c2501603403450301d4000c014500882d038203030001d0389580610402c1031410003080100014427440e0b00a400524502d8225041c4400442640d00007604100ca070310180481c2503004031110b00103116080001ca0b0995507000ba03400106031400c10422481a00d242180c0d8280010034158020f500c1076416030b000c3c60316200302c0b420040c7d0644000b40610504400a41492000580c07507480a00d9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 302634235 1250 302632985 302633003
    0x9070f030506060412030207030c0504020a020303010b030c04260615060a18080313090c1b060518190516030c060f0c061b1716030902033a03060f12 65
    0x890702c8142507217180240c100c01690292009200340300121142034000d1804913410b52400310750850007512400184942d4501c3c060110114410100c0306041d034024100400c5015515887d00c0c211008010040320805118011100850240a42640260070b030030ba000c0d00780e51804643d003400b290b0016084c6541480380001c40b40100b840349041c0f00414003004101402d9980d50705160340d2104844030111030005101c0c2e84540c6900301040c0c0d100404041d0307000440001c0c0e96071f840c0216100c40ca540001070580780030b907920000503144114100d6401c140120121044006000110040741c000d81c0400b0313003410b54101041000c0f80c4101051041107a4524041200f0390341a80c4082c10340d500c80407608641c1c003600b049605416406009465808400f040304a00c600b003018880400d1800380d1030f80800c00d5118020741c0f044d51003c21000310723142c44594180499400444421030076035862106d481008503007c2040c1c000920a00985082e0b40300086e5004641d46003010008200324010307000c81d00422 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 302635485 1250 302634235 302634239
    0x30402100f0221040e09030a09080a020a0902180901030506070e0102060103020d02060705191a160e100309150f14250e1809070f030c0302040b031617060609070f0305060604 76
    0x5d041c1040b6400740c0042002152204a920f40c00342c10f502450700b1405140d4080080040541e170340b804150121080300c40300603601c9004c04242c507890300c0c241c01056000f9101d0720000040002c00502d03644190002d980700c0030f02800038401261036000c00e1101960048191100b2070151a042c001000b103548104111105803001088110186955210076110660383e02200c1e03206240421401e50300c400c012000c584080404400608040110402c00380910f01d80c080000c44940282e0100e040503400c14401c550001c81c00c1c1000c8040d0107002014402541000c3c2c99901c54101d14207018020042140c56407a80e11901601d154a4801c4480c0c40c020454041415141a1107903051048100e2004408240700c1c42d040300100e1916034070768850005580c9411007000810300e084030500980b981203c0201d00d1582c00c1d00000c1c904803d4003070f04a0b002d03182e60300000e80440c04510740340c0340380c051a068030b10fa984c03800108600324208640c1780e00414040c010011234240309174002a8000d4005000c241895 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 302636735 1250 302635485 302635499
    0x31005030d050309010507031e0b04060b071b09021606051b07030f020610060e0d0515010b03040501050112020109031218080706020f0106060906081b0d02030402100f022104 76
    0x65061045040030031000420b000c2000c40a010792031f0300000508052010054a0880100b250011001035540d0f40d42c42c1c04440e00c43d0361f03c3d00540000c080340b110301902d44020781030007092140851000d440b40f580f00d0038001094141c60007990a80540e60844032080c40054a0b0400a032038010085601c1001403491548520403074406401664000d80d600b50102d064080040d16101001c1d0102444425202d41000030540c05080c00c10b110b401601c0903003800a01d40f07070035031a105040c013500420100601c00880c6da40c085001640c400ca001350001d0045990700c0c034008030405510040640013810b160f60900c08117200c0c0312045e966030351501d06002c209108581415800c44690041d6080f81c010f048108207a5038100141c04451601c0030003001000c0c54410701900d40c610718401c14007801040f8001031099003c881e070746e4a0801814440a99910a03840070782e00a41c0111000c030700c00c8881c084402a01c40c41800f00b030381d840d40950000e00c2c0c45400e0f19500080b110030441003c0c1241c42c2044013007000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 302637985 1250 302636735 302636743
    0x20c031504051f140a020d0507090b04180209060a0c170901200f0d03021b060108100e1c050301031a06090c032707050312031e061f090906051203030c03100503 70
    0x703028441001a07ca000c4090140282d0348040d00d000c0400171030040a01204c00d61b1000c60742200c3d03140c484c02c15140c8900c05403c02074010402141d03800340020a0622034182c02041c00890181320704c40c0c2d07140c07004080480c0ca07001d00501c00d00d54000b50000c183c031410002c0a6085001050314102124245a010540d1600d000e4548655200081c0c01080403a58001c2e8041c00352252203102000c0d20040d8144000e0710368403241040303960502920340d01c042450081c18040006603501808141000364420480582184c0c420b00c8111109007140707800100030720698485500441d4001c000200d5515194150f042e00d03040a0075820000c1801c00011402c0001143c54419401d4041c010f00001071400c1c00700350820345124003c8642c601e0420401482c0528081d40540d01c00d0750800e40b0b03029459036408280c10300344920f91448200d4000708451070144d00b014034441101c201e2603003400f140da21442880700d0201da00b403500d05154030030b001180e115058400a164402d5100e001c00321000e5440001a01d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 302639235 1250 302637985 302637991
    0x30f0201030b1e090601050a0c022107030302030a1b11040c18080a120804020603040605040c030c030b1008010636020f0403060b0d030e0f041407020c031504051f14 72
    0xc401c0c0c40d00c9600f1401d204040540c006802d0800c582041403075440030b0701c81ca40c8034000920800b4030401c0c1e1003041101c1000804041c1d100300c1241c840b1512458080d540303074008030034280407030030044002c04448200800c1c520344a81c4801a01e021004c0301d4248001707040009030320000c1c00304d00329000d81d2041e503c6030070600600011000b041d01a01a08200e00d501040c0c00b0100e0030031000302d0420000d0307242d000440350000d07400a40000c07685e44500b172801e0080c425030401804400211340000500080c8807240b03000c0d8490059040c01e156554800c5803c0b20201d1041d544040c4840300b500c102410760140d90b080310300000c4005444401c40c02c0b0a00200d9101c6c00403460120070104082c07090001038405c00100000a481c440454800754030081d1401c8281d40026100d204102c00b01c21040e1669000460141a032034854483e0781005c03c4082c3d1605044d9050300d0083c40b03145004541c0440b0000901e00564029000e02000c481a4000c2c2d29296000078061807550380750340700801e0541d00325002600c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 302640485 1250 302639235 302639269
    0xb04150609050a0b0f031509070c0302060f01050a0b180d0303020703082a22031119140103243b0705090a080f061b0406050301030f0201030b 62
    0x14040c0c100310010304058900d40120b0300810020700240144c6100b0b10444e41c2c0090000081c0c0c0e181d9485900402c4591000740c001c82c1c0000000c01440300c56a08003d03200d043d1071080d005e8440c1a610300d04444108803091183e158400140c90040010281c01002440e80b02c45481c982a410000c81d0b0105112802c00301c01100002e50002d042c00503d58400c58844e00100c0c1d8072000500c0340380c840844180400341100e05100d01c98006642100f07c00602052141c1d541d500c1454401c0e540d81c0c1c00c4c00300ca030340124000319020340030b035902c0324402d40002e214035800d0710400050181d00d4200030340110001d009580032000c2e417803424200706c1c00c00d1440d4154280201a9606140011101014140580c0b900c0390700e41101d200d00403410341d14100160075465440304103407810310740320380c80c0c200090412604d5910910032070042442c1040c901c803001c40c51030710401c1184191061624243e490a0321881184201c0c00007450610060000410550f40ca0780034500525000c80e0b2141d811000412610082c91111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 302641735 1250 302640485 302640521
    0xc1209030f2d050c0f0a0302120a05010e1f0b010203090d050105070e010e030a030c0c0911030a110304021c0302150106080a0b0111120903030c01022b06060905130b04 73
    0xd2800118805942c00365412a004600c209103a95039180c0c1d03032483c1c1c0c10041c403840f03060351030201544070030446100444c2c00038004c0360410801040c403178079103900e2103064806500b00128007101d501c0c00030b0b5414100c40e410003440440740d810b0861000810044007868110301040103580002e5451aa9164049000700b00000c1c0c14145a440580b400d656441401c1c14031401c00c001114a99000c1f0b1400c002e281c0500340000c14000910300034041c90f40f190001c10805140881c0300903c08050000f80d4820080d0304002c2203c5000f84103e00014001203c00951010450030700502d1030f000f02c01c4075000d6601c60b0045514940b400b030203102c0c410700c00360413120004918908100f0721308100d01400c20510300a00706180c2c440c1d1585072450301d0702405500c0348005800040d83d1300d0941c50070402c991003800000c0c0219243c54410001c4000c808a4140c0706001000041008c02c0c402c402e131042004030380c4242c6460b4505850302046c0724074101104400001a0340da400b03413507485d0711180242024603024125503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 302642985 1250 302641735 302641763
    0x80708042c0f061012110c03070b0f0c04030f0f050304090b030c240f0708030903030124020a0201140909010e1905090307080c070807120b160c1209030f 67
    0x400d215a60080c802d1914204440c24080107480341c0502e1108500545850b034000d0110720350a0f0040d181c0d2100c030a0089074001814400981d003c405800d110f80b055044030aa41c54813641214044130603903070306c00c01136000c01080002540802da03500c07034035202c0c40e031519000c60346840390750840d001a400117206a4807255a11f0507840e0070b1046490031141103070070f000c8042c000e06058070818440c035142d070b0405c4800205040f5208501e010790b01d04a92110280750760345042c007105078480c0c20a02c2030041c200e0b07895000100d21202841c605210720a581d0040c61807000ca0740044800d012601c2000002c9203017040b1241d4161a20300d4524007800403e075503c404c6c0d050148052610201200e0f44100042c42c00c806e0001050313003c01103800603074100040d141c07604080366030349050280592180030b00340300e11a00000c801e02e00740a100019402003003403070403030380e80c070010040b008450b5549a030005400700b003800c0c00100b400c0010f943c8640140b074001d8000f5107903a075612000307029102c144d4880c41e040c400c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 302644235 1250 302642985 302643059
    0x312050903070c081606110708010608010b010e15070206030c040e0a060626041104060e010801060f060504033c051e0c01090303050c2805100209010c08070804 70
    0x40084c031006000f00f002c420300158080e02000780d8000c203002c0240055404c201031340c041140d100544880c0c8000c0103500da60ba4817480c02000041c1a6a02050b07003004140503e1030715407800780411f40038004503841c0960590802c4000d50004001002950302488040748012000012910840c0c06000c0000d130f190605402400001c2d0f030400999001c105a040120345804803441c0741c5d0490760061208009040034400179000d8800354207e2100207450500010390040150031100403140400500d5800c2d588443d1300322001c2c45580409000d01c0c6100c20400103150508580b40f10a004403141c0312032500807000c1894200701c40e02015076040d030201a90098500e904500c070342d201c1e6045002000140505000600ba0102502c80036092081c00301e2a000090403d008413016400c80c041098540760184041000030300181405403800c0c441c0301c224041c5290301d442252075428050f1900521900555100105644002c400701c489030414400050b80000c450141c030180703459034188041404000395 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 302645485 1250 302644235 302644253
    0x50c10020d0507091a120903090306090a030e1f0e0103060810060303030501050f01021203070306031b2301080a0903030908040605041701021602010e030f0601090f110c1009031205090307 82
    0x2195003201e0206206081c80c0d034034007101d00902c480d1345c6d20400360380d50b512414214020000c09036050302544c0c2c10012551400326034500010720903110200004040428048000b042c410a865000e03043e0300640d078061300405080c0c6c2d0f980c805143c0824403035124240c950400b1030421490300000d4840109000b01505030241e540904000d9510040302d80088000075502c4030002e04610426400101203401103100b030308110043c6170880e01541c641c004980c401102004603105281045142e609102286403003080450341c00d0105a448000b00e4441d080d040c402050b50721011018150758496002c001401e80f80a00000c12540e15141c1c1c40d2071800d140901803505070b0280c0e0040d64410003002c50058601803c005009030280b03800300016260101091038210711090503407540c8030300c43c000036070301310b49420140c0c0411042100b0f101007041c0b002c02c084030780181172041e030542d00815800c1c0c260100740c0d8420381c40c05000f80b801c88007070601840140203d5000742d0703082d1342d03030342001a8650074407038401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 302646735 1250 302645485 302645489
    0x503010f0501050c0c040207030c0807031e08090a03180801050109020304110111031c090b040b10050102070b0306090408091005090a06080c071b0503011a0906031c050c10020d050709 80
    0x2081161038054801c0c20951240c5c900d4140f148115404100901418070a00d1104c144070b030b010900c180d442ca07180c1005801c202048034800c4054401c0c611151030300c0e202e0054a405510900e00a03c5403d00039641682e1244a1345600950b055501c480000e04400900503a402003215501c016a03074246030034084040b10311038640505200300384414200000002045441f2642d5020102d80c40140f030005d44000391150600c0508440307800c4d8180418051000100c6001d088910001501e00395108010b907180c5080788504200c40c82c0510000351141042c8444a034440d01c02c4900c0c624005114001450700700b00820102c000074008100000d440c18000800b40140050b8100300b00c0360311b4a41c40c40001071044a8009004c1c0304116942199200040014805000024028015000d00c110451441071008100301e124902900100b4002d040200ba071650501002d408074015442e010019107259110008500d030a1080e4203003501865910304c09004595135650000c0340d5420100b4001741240c0a41d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 302647985 1250 302646735 302646737
    0x9030c02090c1c09110414071205060f04090807170c01050106180b07021207090b040f09021c05120415080601030c0e0418060204080304151706041109100503010f0501 73
    0x41040f0f00b0b960800c1c5103481e0034140800c002180d88407403490140d40d90303a0250b01c1580c10505012070040b01110003050180300d2a015a19103a15401080ca4003041d41c1069a15982041d400044602c050425820200f03035076000345691840d0603000e545040054100341c86025458801040c0c04000701c60070b0007010300410385454003aa03200104a0401e04072061032044841c41400000d042d000c5490f46030814089076155400d035030b4a01e070f0381c80301030300980042080c0e64425032130f1501c503600340038640c4104030860703801825004a00c400c00b40d03580079110703046805440d10b100c1c0c460190000261000200050510803002c11000c014a0801401e540b8000c0d10242c149400d0110000583c4c1c1c1c082c1d41c1c2004000d044401045866419150915418402c0700103001d6074000580801c4400c0000300070002c8914101c850b01110450711022644622594080744100d45410041503044c80c0640000f6000f10000580e949442401d0380020041c5111364030750b40101d58003100400c4000b440016000040c042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 302649235 1250 302647985 302647987
    0x3021e03060612011b0302040914090a060509191217060f040f020903100209010908190b181f0c020a08030f0c070804030c09060512100b031009030c02090c 68
    0x2a46000903225a00104428010050b0341c00014003d4025040b84849030402da4060714201441035005000e54040d00604070309508100b41c0c001600704552610b842415580080c2181c10300700c1c0d84200141c20090b08804031841108070280104110100700d0a1252007410714403008080180040c1103011324440c541c007541072447c00c208454407905414001e46804940010f41341e0345029102009014611000707070107200c1c0d82852200c1da02c89070300402c102d0900362641e120075a03907000b000c0d550300340d84511800e41003004011000000c034555035107038020290b43c801042050548803c03600d0543c207284c0c0041c130920820b00103600c001c228460424603504600c0540555030742d41d01e0b10661448060150f070130003004c14001500e034195050513240003d03401780105a40d43ea5a09220210314070a005d018078035031030441d00149500e05110004410560b90002c0c10340e0114510024004000d84030070b45805000303003605c50780540140e00c544c00d0400d1194640f096903000c1401803140c405c000401c3c0c0c00c410b000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 302650485 1250 302649235 302649289
    0x5040b032809030e1e0f12010c1101050a0626072309010806010b0a0804020406030c08101802010921080c070602010f020a02031912090818030705130207020a0308070b010302 76
    0x1517100507078200500240c6450202088001c04a05108203106040405504c1c0411524056610030507219414017090000d1003103444840c0310208881040c450141d21049002035642e0750350403002d23403260741ca8007071052701d01d010b40d1858005203085501203000f0087c02040b0350500d040c0703446e03440d490141c500d1174000c0c0303455810b00341d00c04898402c840356941070004102c00141150b60b80c1c2c01030406503a000c0300b21608184d5512200381d80c1c1c5000c41c1001540780c2049907100c050700520320240040b0b60140c0d01e026216213000400300c05100e0802003601051000c44450b00070070a803400501d01c255200005048091612000900315118003c0342c00d40c00d801000b0900381170741c0c0001500c0c10f1b14850602c0c200420110704d000e44076286010092856217003001e16800900030144080c2140503092103151503194041c10800d0f440d03881c01d000e0298040501c00d54006240380fa03030b000c1c1402c1c0e440035040038004d50316900d0301030b89500b0414040345c100460200601c110704252a182e13105941d10480015110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 302651735 1250 302650485 302650519
    0x106030516081b1e040308070308070f080c0307020f010c050a0207091503110a18050f09030705060106051305040f0b010e011b02010c02040212040f110d0305040b032809030e 76
    0x100101464030f8243e44041800324011003128903524013400c1107030302d8590322a6240740580282e0441e15054001c03130301c500006010240a0b80381c40c1a100620350354254a41e450214030f1945810103004482144104005095109002d100700c00070003480c1d03100c1507250707882c0c10030082c9045c4840c0c020003001400c0c0084ca4920180719803d000a0380d078003000c140030300051803000c00d00c40800703544034141d5000c1400c0440071351107095200500032013040141c014555503281140c0d6481c811004003d0040c0d2000c0c00400c02c1911400c09000c4500d000c03000c4c208071a9a40e80010306131a80005101c40d02c503a03659100d44991303007000340000005c0b02824080504100131420306041c0481020180c14008501a03140456440f5811207c0c034005440f80300f681c6040a04001c00440010306003102d0f88140c0440c002030703504c0c1036113000f0811603050b66072902d02424540c090b925a000608200b41c0040800c400c3c10f5001c8a2210325800c0345070000c0009460304050500806100400342d61900a5041c0c18822001c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 302652985 1250 302651735 302651761
    0xd171e0402060f070c1e060309110409020a0b0f13120201170702011e09060e010e2a0919050a060b0a050901090e0118050a15030b04060608010203010603051608 70
    0x350102d92960310703084090b03c0c6500c00d10480e80d004040c0c1c6414103020817824681801440341502c810008010552580d80640c100c41c070324a406010400e0341000000b1900d800c3d00b22080091025091400a507502c0020880c0fa030000c042c441e640040205902c3c051170007050802c001446542c0e80e405044085070000307010030002509901c11303041c08400046a00d4003d41040c05081d0300540c9480e981948030365103e0003400608000c44119041090b103042d003d13014001d80381c0050b0001b018120b4854800b40810303480c1141810400d5101003aa4007280c81e0303650141c0c4038802c14101f4003203c0c405c01c40c0b103248401c03035000512091200b0300e86502406800100c0c4169400b0b10003230b0038010341c4e0308000310050fa00c156041e0b00c1541e42d50900c3c00003162a07000c0e266035090f660000c0c0f106011031340360021028240d5006580750002c0c20f040030020400300d0507419605800c1402082c0000e0040d48840d41c850aa900036004040440d481c6d505005242c050103034000c075003070840e2604a1007800c2052201c648 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 302654235 1250 302652985 302652991
    0x17101202060c070e010b09030c090f06060c010905060403030222030c140409050a05010621080f0721030c27050906060f030f040c0e090c040507030b030d171e 69
    0x140201040c400225402045120f02a1104103014480c541e55000103454580c0603030b1441d0700a0160a8481102e4100b844655010b0300710504031030081d40d90034091001507040100c45c05102c1d92101a900b010500c14401d85008501980d005a50382891041c9503600c056444010205407010030003c001007800c041501e0180e23042032095500740c0c01110001406421481c60207401401031465038000c0010541c49542254003c1d115601b06010300805064039001100018001260410010103a030f9600c0008104403841030704d6100c414001e100c0703507521429406440e070005c80e580d202b8a10381d11f44c001e40941000010030f001c006042c119680380400f420424070030a0300524458005c038080340e482d6002d0f100c0300b8515205940d1603180813100301843d140241c0d402d440440c0c43d00004660f40356820b26451181c541c0c03200901d148084c52040c04000c2800402d0081050394985001001e5607050080607000ca00c680d48414500da4080c0350f030322100e44082e1446003d00305411072142c0401900404580c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 302655485 1250 302654235 302654239
    0x21e0a0b1905070303090b07080405060106030603080f0a050f0304050609070b03061804150905010609060503030702010f081510021c0302040f03170c1f0e060c180d020603010617101202 81
    0x148031143c0f4901a03001d880c0c88240203040c400700d403041101f041e502000c514410380c0a40e048514507641e6107025400c0b0352543c0009840e2030130412079035003842c1071000140b20410f901e00e00302d86008008003d20842c0d81094130110380e583c01110512550300e004010071070107840520043c07072441c00c00100081d40000c9201d100c81801088500060600003200e02000050410300814404107039240b030b03ca40201260b015150006240000104840c203002095070100380d410307107504004c2616103506840c40140141441c08841082107084125215140c1c0300b00321880300d03002004400000107503c0d80044070307840320340308040c4140010004100c450b03014004480c0c2201d11880700e00c52680e4001150b1092203503d100a21401044c62881100605180d107850042d040070030400b003102c0c04403500c0d407a060f43c0c1440c841c1d40600c50020068095100c0c00420300e0002e002c22551181503011522581007644040049a460341d00400407003613012a05078400031000818240314200203074060f500d008880068 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 302656735 1250 302655485 302655487
    0xd23030d0f0c081303030609110a03060b0301030314030c070804091e050606030c0714070f030b0c0406050d0f0e0f0c04060504051e10030506010312030c02030306030a030f050403021e0a0b1905 84
    0x50500d4041e1f4000006070844810900640e0000c14850455500044000000900d05480000c160010b201034a0503a0782c03565030b84008040d0403482c194250030150002c0d80b0710b101001031100048003c401040145400900898524400001300e148040341c5d030100c00485040104100c005e82d01c00080741d9000c12114406505c50006040400802141c0c0da520b050394804d0702004900c0c02200b0348048101ca114003c842030694030001c0d09500c42c02180b1442011034020701520b02d0f04030507508000c0f0b401c20203503030010707044106c0740a42d880d050407048003000d40e41144141680c3c9040c58001e01000d0502540c00f8041d5040081820403507143c1c00b803d003108180e0705400b0544266403030003413500541d04402181c41c556141c1c146074021580a06952011a01c1c02c02005101400407080d64810034000740908080d0981e41c900341d61060008141c0b0301044001c10000c0016514114070708400c19040c0c0310715120b00c20820905c071290300150454040318030184001c0c081c101c0450b02480e070211003442c1c82 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 302657985 1250 302656735 302656771
    0x714210c090607060204080606060a0e012a1406070905030304051011070902030901150302030d18080d0806040f0605091305011413021906020c0d23030d0f0c08 70
    0x11800502a00860725840800000c801003880020340103803094902c1141980e00c0b949a032801c008207489030380324080104c0c188005102907503005070f81140060303d1a07844003000d4454000c4484421070b254104880101d865190300100400c10044d151303004445080c1b4403002070900d800a540d901a602c40c1c180328245208540f88400e00c16030f9209444140b44046655150301e41c0c0c0d043c0d01a400c100d0f90206507610b48005107a24582150322401100d401401609801000b008101c42c2d511200d0010260680080300c009010b040811070741e004030840c5d95030100300742030001c100410b403100540462078203410144280010b940c1e201c051600b00500c1c003100754098684c2d00d03100303016006109409152920341c10411425a8504c40745c204058421184207401618481070b40c4882e071101e0045500503842205032014600340000d801e515076018401d05000044400309242c40c5c28010050b0302d07180c2e0008645680c2110b2030780102050440030000900034001c00c070303d00a0240100405015801420b5107030303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 302659235 1250 302657985 302658001
    0xb030d120209030c0607050f0c060304020a060509041509060e09010c09061128031b0c060c14070f0807140f010f0c061406030c010212030a0207020117090105071421 72
    0x300c10444c1e8005820540c48134060704100791514410a40d900c100d02030b00300c600b07900f4a000340450344100c0c0d008141e001d04ea820500100d078660041892150800d646480d8503072003000407a412001401c85400210700f6500303207103003180341e603c1c003410041e905d030304056420070856040402e0b6401d4070031600c4c180d007280c5000d4000c0f07840d050641c0d40e0b0203819a50303180342c44041c00d46004030340682c030301136110b01000c03220728200480720302a03019000d0b080400c0403000740090707489071000c0c004090092581c4c4410a00150780e81c0c0c2030800d08d80c020805038101100030000090103201030310040044400c4c1045910080740445d10900081c0c02d40d5040055071450104014060140c8040f070135040380080200116074260308484440a0751802e20a00c15410203062561000890100a804803a02c050854941200240294020850880c140143d202148481003400d011181c480e19440d0004a61410311000c054403c1c0701204c40d0f4901004204021603240b4500303441b810300700b5030108d8017100541c2c807184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 302660485 1250 302659235 302659243
    0x30e06040f0206131e06050a02060109021c060803030108010b0a0e0408090105250201120b0a0923070201020a080109060b030f0414120909010602150a0203040206090904030c060b030d12020903 84
    0x40313200d03a000c0800c2012440080c0c10325101c140c0e0b44c2c00303884541c1154848209071407130f00400b145500141e01c07020040c8001101c58000c9c3c086418070000300c05100c0081400ea0702555401c0e0406040c82e030001c001000180024003070010321100a0702c2c03003c0d0980c240302d05a07880c0240200080c0c03400200165002507648114122602554144240c1701c0c0f901e401000d0005800c40c26038143c4c0091502441c10610302d009111300600b10600030040c6103411b14046d002c10281040704400304d540d100c10200c1000d000d02d281c0302c45120f1100e81d40010381e1000d07410b030081e02502c0180c01400340e030b520300318043c800601d074041241c1d0000021b041030149550b40e494410a1540000b2146c0d4060140c0d5195200c100c202001910058808864809a680e01c986049a4800464500c06120080303c404114000e665600a54003e80040c200a01d0502e4010108810306000d03181200040e04007140101401030502c540240c3c2d2008901a00d080103036564003c0555014160301c02e003a50b070018a429840d50104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 302661735 1250 302660485 302660497
    0xf030c0d050f0603160f0504050901060906080a0b090a030504050603270d11060c041503062c070f050a320a08010602011104120f240b01030e06040f0206 67
    0x1440a22032807800d0034801c00c1071801552000e0113031003110507410306030103211650030a40329081840b41b440d42c6801d003080003400c40038103401d1495694030070108144111740100009080f205004241480d40751800c40340c50800200b0f81800c03034000b1031055000a03840700c1118100d4500f21a595126223a00b020a040c9a040708940c4000075040d001c0c1c0c903070012011508034488807035511074084460071401c110b45c840c0e07030480d00c13025411000c20040c8070003178507524249101c1c0c84034074001401944618400e84100614107800c0110322815604030111017110b0308640d4441100c1c5021181410310b864090600d00600d196001401100880320300031b41074408032a4107070484101c03880150415100485030aa01c828051800a4500800484c4941c0140034106107140c03504002c41c50a403070202c03900707950003900301c0442c1c2e08418042c80c0d4004c40c154040b40c6a030180c240710101006884800c080d8104d03400456660f0615081c0401000d4450000c9200c0b82d0040e00132030303003d02c0b094036403000801d180309403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 302662985 1250 302661735 302661757
    0x80a05030a2a0c08100213120311030307021b1c1403070b0c0d060618030201080c04350a0308060f1807050d0b0a03200102030f040e06040c080c0f030c 66
    0x5552a014001c0e165000004c075a241c005035000d0140754402e04069104403c0883d0b1070b001400010808800361500c01c100d0b480c024034042251644210005d403e523841070b500c460040c0c0c0440710000c59030384c1070144140c104808a4801032440c4110001403a00c20490a000d452803102c0340c104180c10000740101d80c41c50341d1001001c2907614003117500551580189092000d520303d00840800c00741c1c0504400e2070215416003c3c407080c0344c510390046444132001000309807005e10600c4002160041d01410604003d0030520f445050055292942049074408802e8a4107030700c03420341100440d4000c403825811403010f5403145c1450000c180480d5406202c0804d0340406c001c104104410300e9880030160035046403d0300144a51144c2608104204240340805058109200b14544419500224034181500107005072420a030081c42c0c8245243c005500c180d000f40e15201c101703d03403860300b4800d014903030409081942450800195440c0c09014040c401000244008080340b01d03802048144c4000500c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 302664235 1250 302662985 302663057
    0x4051b0a1203030203041a0106021c0e0d0b040210080606040902071a0f040c0603060506030f1803030c18030102040308040618032103140c091c0209090c0307080a05030a 74
    0x10340b030020000e50045a003554911900120300c1402115410454100c511a41c001c03c0800c50004001202c04c114404040510039080c1c48148140c9445907180a054001c6007100020310303050040c081840440414030007086000002c02080b40d640f6020340f4180d41a551005132544041d1070030040c52070080525159034410b0f08208010381e5515011548910300c81d03030306420703210399920302681a01e510f8010b60b684010180005120249110f04450f4440580b4035030314541c0301c070044151b042d03600549400302d00c5540002c110040d40c0301243c14000303402040d0000c501d01440d50700d4100c9240128020700d4200001c00c0c0451004207090300602e07001e9600700c40032040b06140904058600c820b2525404086030a2014a51100e090759603800e105440e2080c45500d00300c030700310800141d04030000b508554150b0781011400541c0301c00440382c4c461020300d001402c00c00100801c0501d42015a40000c000d6402404541c0016a000c01038030100b060604000e89888442090607160010500c052013030400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 302665485 1250 302664235 302664269
    0x303170a09032703140a0512130b070f0210030b03010b0315010b1c0c0903020901090b09010b03060d0503191e120c0302040503031c150833010e07080f04051b0a 70
    0x1001b00304061400d01c50001c5075a04541850145481d00403540c80ba22a0103e00408200007078071440102200361042e00001d14485040d0700050b4a1740d002d80d003041c0003d0351424034034601d003400d204007001c2801c100c0082420302c5003142036003003c1105010b42c910154000c241d001c84007140385410000180d01040510910039030000c01040c2040034442a13118440c24800003d03401014810f402c10804041c01d0f20f6400c2c1c1c2800c84a40301c42d403010b041d0527003000c1c0d140da2420105001b4005048841000180381138030030700b607041c01445040142100340c1501d0441c44044d858581001c01294507558020001c02c45821103217080d0001d0050b940040c1d01400001240e00306411080076440000c4503089082102880c0002ca018401902d800384129940c0201040143e08405d5240164101030340399010107184613458201c84080000ea00502040e00030310b080c4044290040422075000c206c0720100469440e00b5260207a4402c024008040a0141d60100fa20716855012500e00680313004054400c840c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 302666735 1250 302665485 302665523
    0xe0703140a020d0503091e100c03090503031b01060501050c190501060b041203091a070b040501180c0608090d090501081915080c0d0c03021005130303170a09032703 72
    0x64401b10a1074402c0d5094030060346100c2c0c0741c1e90043c040030001380188070343da1517000d800e8030040d03c444000e8051010000d0300007070a50381040100030700c0700600700f260140204010720900b924000c5d00810306208041c0300c20b0214910002c3c0d24500c40d8451054941c82d40003600b401c07030060841b030704020152000010041101c1c0903240d400c1e01400d101e1b95034281c8040e0b0781c0366013518200b09005412034140080018a0110b0b9200c1c29040d04075000d000001404040c0d0300900d0302071054000100c80381c051002d01080010740002030294090030346e0001e8034000c0c240d0480101000381a000d0b042c10b01c500100410550310050b20310300105540d008040000301111180500845401d20603c207807441000a40380d40b6080c01001440710310707404250744440d90b0460303080200064603904020100304051042c40302440b2050500001140070380c8404500c200d41d0761314544941c48c02000b4400c4503086c1601e00000951081104040c0c2c180641c2c2c3d030002ca802c030400014020115800074040440e1400c030103c0311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 302667985 1250 302666735 302666737
    0x405040609050108033f060111060709060f030e19030210020715020703050702040911030f031914070606030803070909052a0d020d0510080d0806040b040b10031d010e0703140a020d0503 81
    0x4840903201d27000d441104c6091942d482d5401c850460010b40c4802003000050b000b0600c4001008940c140031a44441c1b6842e001e242455200c80c2205078440d120141c8289601401540490019160254a840c0701c0740c0385c0c00300c582c1021a04144499000914006040c0b01c1c50a4841c100c2c0d005009100d0740b240d034181100900e414400881c4240207994030340b03c6116000045410315041444204400101600103135002c840030200008542c4003040a800021124443c1c64040d40c41807000c95164101041c00510000454004004051414003400046c01200400000c061313156804801003031007041101100c0d0155406420a036400414100e050701c0309500240c0c801c2d00045402c44986a40e4440300d5620a4805140d00c0803c130b0038004900541000e80141c010706a000d000410018030007c0400e13044034040b04441c00003076503452050104400080682200c1c901c582c024403041c42c0c1c90224584130089803000420341c6801004002e80344000307010890016400901c0c01c0035686d1142020b94903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 302669235 1250 302667985 302667991
    0x618060c020f0405191514040906061802031510051602060409060e0415140f1b0f0a1101021c0203060409060c09080c010305130b07230405040609050108033f 69
    0x1443c103211186c915014640b128008803141310801d0580104d10307400b4080245841c1009603000c0d6100c60003c9180780500c0a104003d0404240059580ca044c043c01401c017074002500512030585c90301700d10408c980c000203440c403031062030103e00d040503003620000d01544540d5100d190024140007001524040c0d14052500c220b020318252402107076000c4450b8112100e0741c0007071111547c9403001c00c0125141c800c141c1c0e4804201402c080c80c0703020300a501c400d0340d081502c89986040000844048090740000a58441a4018001d506014200b10a400203000900c80b4414456005c0000340060b80c0e55004248842d03000602040482c83c10900200140c45d80c0c0512803092040401c103401c594402c3c42514031400b00014801407118059940c03842c64a0081c001608210321509080131000060800305415645002c0c156540c500d02801c0c041991801da0007860200e10b400010040e0f40004030490300d0ba2569541da000c5401124820050150740d00075081050104000616039200046150700b40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 302670485 1250 302669235 302669281
    0xc100504080f0724030207051002030403020f120a14040f0311030d1404030803060d0b0a050915040c0e090f07090b09090a05120901030f150e010618060c020f0405 71
    0xc0c41042e14403690b031003041c0c0c45610000844c240130400b4181070346840e440101000d14001d8a0400705844441c6030440201031000320756400000e100815404010b0b5503001034042010700015410340b200e200d154014481142d0600880b403690740e000f07016003801c0f079001c3c04e4202c8450451545034201265510a0540100d00922600c5904060103002d080040364101c06c188003540750506507622a8900d420180101d5003000358074802000003503a02c4410361080d0020040010b030744c54480400e9140204d90640800b1076a01d00c81440301107071075840307064251050300c441c07078085031a501941c0b49801405080c491300c0d401041c034003140d5901d05400c58650b550701241e48124a80307a000700c4640302e025403003000f010340e030110110400922003803018001b0b0100504000032040240400314042d00ca0062403240406103000041c45005500c410b524098040f915107511030004084040c203102096001d80c9050040b981c02e00811540c440301d01c3c1d007000c4000341c0203004a0401d00504004070700000d800744 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 302671735 1250 302670485 302670493
    0x50603100f110f13120c06030207080409050f1911120907030f050d091a07200a030302030304051209150313120e030c0f0609010804060b041b0908070b030406020a020c10050408 77
    0x30005c0c1075030302014140f90400341d04c0031000e00e090f50075030003944040c4044600c41c00900c0b0002e04100d451107041d110319040451444186080140c48140e4280740400c01c00c26490f0017001b90305c03c5c1403002030b110890402e1a407160b685e161020890315100c0c4603440107102ca05c1d01500c0c402081008100e1101d844034540b218842d040e02c40da0036054075000c2c0c0e50784200d0280240200c4010640c8148450002c5a1000c024480d822640c00400c1c1c2090140e0030a03005a4400014403040040c20080c558400b503103180d90740e003230480085c0010301502210021140b80c00d804004a40181608000c50a1455102880d80b02c201458503028040f681c14901041c461700038a40200160308203d200d9a4991328000d100e54a00802040159400c440150003624619603548445100b038580c1e101e691a21600c229003400080e00c560001017504000e0b401001c9541c014907020807842d50182c0075290010360102000d07803640a0078200724940750040c0718082e4801c6503050b40c3e00c40650010001c00036120810191 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 302672985 1250 302671735 302671739
    0x180d02150c0f0c2d01180602030a081003083403090501110f070b21010902120a0b090106081504090305030a0e030903100b060c010c050310060201050603100f110f13 72
    0x4807003130182400c8440090410140030101c1140080c100641c920f0504004002c1105041155401801500326001603071000584000c016000b002c4a6442450744418a4003941140e40e0318525001d242c08240321419501000000203109031810350750710350042d0b00e20f0001e80c480e040040001041e84141800b041c129815105041004a030303c03040c4011520040c64050f00d001d2140f41c00d9401071500510995401d100f0200c030201022859000f81166800541c40e40002e41142910030341c09410340900c0351824601008607140c4003502c0d41143e00d1b50a2a0a41c1d07a00c414810300740201007000703d030b801403501c4510401c05410030055400380078101d4042001701c0440d04101c0d640c0c8500c044841e81507000411060384a030140d0850448650047c0c0043c0c00c2400c80d04a950075079003080c1007400440c201104009480380c440b1600c0c001000306100038001e90608201094a5034102502000350035240c0503080005945504585010040344846558a50b084e2000030511f4118030482c45481e0420480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 302674235 1250 302672985 302672989
    0x606030b0306160e030705060c1005160c150b040f06090c020106050f10020a0b090d141204030c021504080a0b01050d0c150207051f020111180d02150c0f0c 68
    0x902d22a0840c400c059045010140c81518000c50b1306407420f5052203241e0011a0303d40b588030140c40304140400c018003001d11002044800c0c2d82c001091001c178441111804051942d0040c10b144c0755a030402c01269611803010204000b2b0511503010036009401c0c9001440519180d0303010300200c5000071010085803040310404c9098811300c0c0f003407640c8825105130f660860319203510b00e03c410136060300446170300014a99a12281005c101d4180d08650070581018102e107403c0103690144c81c04d5410b24034a844001d42e882c15501e18050005420001200d04c0c403021904d4540180303852001440d221a11a0783e14181c00d981c0300ca102004845403081d243c000a2141424100380115550044000c04d40350704081e10b400700110203210807011880f815000040700c4d21014400300c0b40c1d140b003102c08849523a010801a0070340d03070081c48500d900c100402180c1800c05605a94511443e42268508504402400010305503201085988054240000e0003000c1002c00030b02019140d10000c29603507942c0711602 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 302675485 1250 302674235 302674243
    0x100b0708030f07140405130902090403082a1215040e0313090203070203091e0405012c07020714041b0e150301030206091c0b0c04060e04060b0f1c0e010606030b03 71
    0x40305540d40001170000340028038080c45c83c50021410700710006035209081d000501c01c1c0009031003e6000c248924203009114410101e0880c0b20090840c0c059444509042000410f100d054407080c078400c0000e01040c045860403107030041f001002013013400000608480183c40750300800c48103220400601c000500b415850080e64402c45041e0082c40c02c01c0b080b4000c0c09001640503202640f00da086040200c0caa5030340303200b220301800c6101919804202d4103280c1c0c07a4440d40c91240751415044400402030010340c000348010640700c0e008038110355a0740b0384003c100039100807103509280b000d030001c4104079160300004d40c14541008450700c9040101c01070340c0032110701c000e000294105104000381d0791a402c000940351f9a0086642c401030101ca181e89844a0010050311007006c5502c0c00901001115480040d100415108480c04c101c00c52806200b11124850074400c0300c40c0400100b12000303541c1c88251031070000203843c1c0090201c480191240c80c020250380c0510004079140c5501e04030300d030070002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 302676735 1250 302675485 302675507
    0x120a03150302030a06151203051e07050a02060c01020f0d0f14130b0c09030307061d0d120c090e040c15030c120f0209060c010203010509010b0c0d0503100b0708030f07 73
    0x240184c81e04000b2a00c410010b04540040740b0480840f4120000e02003e2881390200380324040d0b92940c0d210721441259000a01030040e2488403a08148901c1c2c0c081000440d0f290720456048400554444160050311701900490350000c42240000c5a00c2d28500b0954001d41d00142585400300a100c07640000c51a141d2016104200584050494140040d448000b120740050340e4048580c2011513400009185034042041181c0c526280c040986100c060600c287c0c4150312000042d221181007148000c0030007034000d0704400c40039181d4040400031401201030b0000b82c400e0715050b031082d10b802e04000341048560321451480d090303583e19000c0d0040c070a1240a1203120700399103a018060b500c480010191010707591410b91140e082100328850f50b00c43c402402d05d8040c0a0015803298034080800206890582c05040e0412082028820006020890f0003688841e4104540c60303440751810540e40f1b00c9140c1003200c025400040003800c0c0421a0083d52242d0b00c6c00380d48000310350742c410003166066008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 302677985 1250 302676735 302676739
    0x21008070f0c050c0607051006090209010c021512010e0915150d030908030d060906140906010f17070504360b04090b1e0a1811060c120a03150302 64
    0x15040c0c003003586105400009206000b5011600e06045040000384190701c003101c00c80c1d01c1d900100740c07000000323550b000da6801041c1c0b049046042c281000c0c0041c1007925074110081c440d0070960300b0894020522015603503000e001c403031849010340e102c00d0300341043e40c41940c071168a80f081d03050700d65220410708002407288007003511187c0c0b02e8001000380040322600110884c140078481a001c0b90100003000580780d2104418808100d0340c0c42c00300003074100c40440d00030f4100018403415000c400d48522141c290064428a45504042801c6c3d404aa40c0440000c0f0007141500b540b05014250794040d02420680d070032220940c0d0082a8440c0d0301c4072046610249603051078400c80d8a85141c2101c0e400307203001400c05400171400b1901903886403200481140c1c1000d0f0403480141071580d0300c1c42069105e90008d902c000030049140c80c03445080810091000040840d00c02d4401d184423070700c841c000e4810b0080c1c1c1000f00c2d41c10022502c1d481103280c02c2044c80d00b0000c0d1800c24445482251304401c00704072600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 302679235 1250 302677985 302677997
    0x506090c0d02060d09200a0609030203060103030503060a080d05310501110f0a1a07020703030e1311030a0509010507090f0312030608030f0307020d090302131a100c02100807 76
    0x516400e01c07007650801c0103008549551085102c010071401c410007071081b485040d590000900240410604c4070140d000142008a00607090005850024180f41500d4260410700d03100c0c0d40303c10000d607007501560080401c41c05400d000c0908160818050503c0c07882c46030040704148001714540e25026038003c1040c0040720305010401c010b500821039458110020820703202d07114507941c4001e20b00011500d00301c8000303011174001005240800d94240d000800352020304805d528540b002001c003c0c005404910580004d4480c4205040c107501c62007940451124003070703e078642900740000030078040f40c440d03801c1d50a18002030340c540d01c5041c0542c2542d40c411084507208d4116211500d24484640c00101415503440021501010410282030042c0910024650324a080c160003030030007580c0a10042444066a010300050759010500e0601d911003140000c1c201c468162120a6070350580440c542150711400c403c500d05500512820205000b50354a4003458481a82200c204a04032074031000141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 302680485 1250 302679235 302679259
    0x50606010309020402090414010905010e060a03080f09090109020d0b0906100c140a0b010f05031f020d060f0f0501230405091905010905010503010e010902061e070b0703090506090c 79
    0x80a98400302ca03060025100500304074090010400f212100c1074824440f03007003440104100310840c02903a014002c03900240d140e9003804004942c0d00c40c00e501000303000584c041212460143c600342a1042d508000f848903c807541d646605070000d600082d1040303141400d00d808028642083c90380383c3d0289401070440b04140044010480e0119070301441100c00701a40d619604180f0350810417241850300440d0800b005524002e0ba082c7c1c0301500358004c900a80010008042007a46044423a0315030090003400b603a55040c3e445600d00505040d013000107441c0328048041070401907200c5260686d03c080c3c8407185443da001d0f041c080c2550000c0000d2507080c20402c4240808c1c140030030407a8105060000aa0102d400080c45605848090b0016210f0076680d100402c1180340901442181d001b43d20b0081064000503008100944a00d01220f1001100c240b40380f051141040c040b04c00ac15040612320881d400c100c4002005072015071b1040d6094490340c400700e04007910100d2022101400108040c1c5926 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 302681735 1250 302680485 302680487
    0x5041a010f1805040603111008090c09090f011b0e090609180a05010c02012012010311030c060d021206090c040e040201110a1124030a09110a030c06030f050405060601 73
    0x7182690007042c0110481c0b0001d070980342c1c1d0041c100610310a40003000c882c02e200003440070010b40f07040c0e00010442400140003d240000c00c0898500d00c003520146480d43e6040be0341e5241541d01c01200080b0741c40e0600c02d91481070315550344104440d140c4d4400c008148401c003080403d0f0010768150354081c0030800400d0302240b4170300d901c0165202c1c0200766101c0103103640f201e40c2194041c1e045080580d4440006000f0b0215500901c01500020100d182c20101104001d030a003c005000c0142030000010940c80035613410464801c504800500c82552944810b001c5400f9411441498450741d036420f001c64118600701002c9031145c048503424038100b51800080c26405c1d01d002d0000c0e030521415a00c0700d4003140041c0810584c090280042c020b040b07001c8030074000742090098281f480d002c1d001c0c201c140031446803400c07250000b132050408a00c0b1181401c02c010112040750b00d055000c10031250020821560b003900c1d0086034a1130301e0401c0303d0080c160070802501c6040324010b0441d0800301c0068841c3d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 302682985 1250 302681735 302681747
    0x150207060f0525020a0e07032711010e0301180309030b06030105090d080a060e091506010806030c12070f060807020706020d0c0305031017010905160602060402150c06010e0105041a010f 81
    0x34002030403421721a540788a007400741d102c00c0d15214002622010a8140151810002000e592203140700d41c0c0e034002c1d0350701c900c621440681015030401514030710620056809421034860a0780c000f0f286980d40c01c940c80c01a002d0050740c4421210085000b0005910389070620690344200e80038800707000611a080011076140c44010084a681c0da035511001c44c0500741020304500c2841d0380c100400c6000533413082c440c0c2d170b4907005140714100b00317842e41006000d4401054194003000f0980d180021510816142e82c10126142c1001c14511124000010502d522215180c051038981d02a9140940c40d84001c0b6110700340200300401094014444400186c0b0a0000f180d100b0507240c0190780007501c45101c3d00305a00840040c03921691560003200500400340a40100d0010b0b4080748001d152514501039100c000c01080a4441c0040f00c42811040d0007840071986118019015101150f0b1280d000b10311125003805198050707031810100c0040342c01c4880808406040503141c0c0d1020112143c2d041341c103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 302684235 1250 302682985 302683057
    0x110105130f03050c1605040b041a0d0303140a05011a0703020304270c0905030d05040302031e0f06011d060d0b0c090a050d1101031424010504150207060f05 68
    0x4000742040844e01c1c4960a1045101608141e142c01641074940410031017a500b03a241c0c120b1283d40342130340c10603500c04480c08034070080d2802ea4840706042140c0c1419401031640d650300401001c0c40d08100b110203506e980c0b100d4140c0e100d10340c50b210328440702d58803410300d40956a80100507a00c00c100a1061011415820700c0700080c01c0c4c154844455180c12900546425080400124054810900c441d203070522581c01c1030001840c1035410903166800007555540e00c00c8545103c001407a00380018600140501303003005140c0402c071040d03560746001403241c40c910300841080c0390401c90f000c141c65240412034050340541101100c000c0d074a8509100c659036200121284d4013126138403002134540ca1745066024440e0040f94618200c0c2c80c5940058240c03505190b061000000d41c00030024203150232455082e0345c1a014842c02c210a02c144010380d041c0c803544d00a1240302210040102100d40e000071070382e0596406544100a100c40c101041d50b09028280c00035592148200e51800742d685403003c2d0800f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 302685485 1250 302684235 302684237
    0x180302180406180b040b1302030d020609010c020309030c06130f08060402150c0a11030717011a0103150306021606111b010203010f050d02060f0f0307020f0601151803050d0c03110105130f03 83
    0x382c0c41d2095030009e450301c2004900350025812010400001d00c0c0b00381728a241740440e60020f54a0300d4603800019854150054859114060100b9400c1d0f62a900001c000007404c0402224100c0c55113411026a40b0307002141c040f840361104110078207003503064006580d02c0404510060500c039500381d030b03804824040c5c4009a03802d1b02c00c0810001d201041389500c209581811800018030784044406980202c0858007013a0502d07041070390380392001105407410b204907900b1440c0180c407405191050030010305072a4018043c942040d920200300c0d0900d4004003210a0031030b020070641b40c5051441b50903800244104041410100d04c10800340c10017066611807240700401d8140340c120000d900b90302c19044851000710618000c41005007464042143e170380100c000500501c020342c9004150142e0309007444007103040201c1050701503501c019505c0301201442c0e100e42602c50101a00600030b11f072041082c82500058034159074500e20850600c41c890140030701030010380d405401e41d1108400c0380c8228078210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 302686735 1250 302685485 302685511
    0xa0e0a02090a02040e13020d031b0206130501031a030709020c0f0303010f050102070623090f1509130e060f070504080f07230a06180302180406180b040b 67
    0x6001651a0011148160704241c40141c45030306044115045401c000c4c40303d0040d00310001c540c0e0150303407503840070401c1d564585400078076a004000a40d440403480e0360001c0d000040400d88801c00701124010f03000703562003030341c0c1080760043e202c1100c441c03a8900090280c01d900f00302014006541d20390000c1c64682d20300001c5400c11800705400314507561090303020100009803064203124a60307052003200010651071034402c0721050a078284980005164440c20380b155000201102c50f511000081906120018001d000280320001e01501c00d51051085070701c2a0a154500c50900880d480380c09062841000104aa13594503443d8043ca000007800080500009000c0012081803c020020700700480e0009002041e2800a01d0f00312840140301d0020021554020032480d51100003091007104d041e440e11385d0340b010341c81c03d40110054207600301075042000d055408194911000c10310b40034a2003100f003040000780340c1040c489002d80e076620041c144402c0710003040114107508d64007a04080a40d04031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 302687985 1250 302686735 302686753
    0x14010203090d0f03020705010503191a0315060907030c0516020406050a0b04050f010507030215040311070801050417040e0c0702040209040c0e09090c0604091a040204061211120a0e 79
    0x803040b08580c90700b02c035820941c1c2083c9040550600c008401800213007020b40c00d600304100380f08009081c903884621100e59501048034031640114503508486c1c07000c0c042e00d90600d01c25000d40000503045540c03074040c0d1085d402040e48940310744586200c081182d40d42506021800034200c80700701c9110800d84e80a515041c3c0070441c1c0c0d40b0b100d0b0050003080700c60384955540e460701c0b040c0f00c0c40c80003019466050002c1404078102080d0080340346d40c81d5045040b282c0070140e649140c2507407030300c00a010b0784d0a0f510410501092100056000c0d03406140504803456100d0f4a81c550711442d0b00c00c90180168245840d03011500700091800502101e500c020300c090f0a221105000c50110b0b460b0480250014180300000300007410708008541e0003002c800e019010f501e682c400403901d01c3c8201d00c0360303104440d521085010703903403148078014003110070080056555540d501e00003401003684481000100e4544161801a400090211a081c074100001d0035900c2d80d4080e000001444030b64080100c60203890b4035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 302689235 1250 302687985 302687989
    0x9060204080d0f090e0a050406090629041a01050c010216030504091a21010207050106140a080d09030609020103022101080d0e3006040f200a1401020309 67
    0x3600c0035000d960020a6007501c050001480c45103c04142800d11051400c10b1000310400d01c1c0e180e90081c29000c1c0440c058a0701d29001000f0005603101070400c2c0d107804444410406440150b01210340888030072050b0520b030108105c00c40c3c00169000d4052080c210300f042040d40034001800c203007401140010f04181108100e410080210342003280086c80004051050f0f202c030380718102c0c1c0e4044085882c8031820460740402d0704d42580754040d11514580710211036007104c00350100c503d441d0b4040020b20a00d1b940702c220071100c04035402d230144510340120700820300400000b15030300d1440040d69041340143c90364035800b00802c07010381e0903410103070200a003aa41c040010b00803100c03075044e00e52005466140400490500d4100704142c4104902920022503d9540070840030b00740c20484009215081200401000107400605841c00ca000300f608110500c40403c01191003e0300502404000c0314600004001c0907110502c04d45e402030015000707124812010144840014041c0102c80c500086000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 302690485 1250 302689235 302689237
    0x5040c08100b01140c0703110a051503180a050d08040c0b1c06120b1b040e0f06100c0210030f0e030403050703050c0d0f1b050904060c0207060e0d15090602 68
    0x2074054a0152a03a00c060301c2035921101000d091111030301300d00d00782860541c136170b6101c83c01c52001406440c01003116403255907414409000400c402010a80c4102c0000000106900101d501e003a00f52072881414526150201380c15240700e40c01400342040e0952405c0c1500d19000180c0261180e440d9041c01240d6801208014000c030300c2008004804002401c42003020b80765136802450040c0320740001d4000040c80a82110b800120f00740180e008000445007140040c01130364404c07014503140d00d0a101d0320f580e0652007035016407010745481200c480b120900740c4400a070298000d411030460300300c2411451283c0d000174112444808085480022881d00030b01d95005500140c035181c2205204004200003000190500310065403a29202e10843e250b0715100000210003418100c0c030707030449912006d40c2420b100e01500000306210007505140c20244010141c9125440241c0325080f40403070028040d00c4100d10711000204011150400c0341e490002c203205c44180b9a5003035480d101a0000524140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 302691735 1250 302690485 302690503
    0xf010e0a14070819020f2d190e06040612090516060f080108010b010e010c030c0b040f020315061525080a02072102090402030312012303030f07020405040c08 69
    0x43d45071802400d0110001e00300c03a15044040003280e20420180e240c401c4180181c072004000d804022040418070541510713883c0104032803511111000549105420300680e0120245c40255280224242080180724081c4194021a8045000c0c00d0500b0b9403400140c100f505503d1040043c1e070365140701d04074200300064154002001042c9014002048194420900d9004104e003030000d02000a9080010700039244000030360741040381d9985c50340207150045105814403644000c82c2e9031180746c64180b08807012070402c3d04911a01410002c00268850000c0301801340600030b182c4c8940c0507001c903c9803242d5002103a000d5002cac0c0804900907081300c3c00b0088500041c0503104a544d07a07848594000d061013240c0c2c020f9a000d103040b4100c000c0351440e21a02d40c20290b4155900300603615607000291850260341160345045440b11300128101e840c0b0b140b08526099030302a5101076040c0380081540324001c5114a428200c1d0500103840581b416810261f007082c0100d49a90007991219041030401e0210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 302692985 1250 302691735 302691737
    0x90117240604050a0b03100b15031003030c020a030c0b030403090b0c070e1305010f020309010e071a03040303020c030a090609080705090f0c04050d06090c0e070f2d09080709050f010e0a1407 83
    0x11303980c520610308050390002c0b006607044440c40d184bc580342849440364030023404050b04002c1240151000c54a0703800100c070155404c480d0554402d0b0343c480c0c403804150b0040701c086002803c2e078540015425903107005d5070500281c81001d41031550401808140a07213000704480b03070401000030b0307000c0416000e00c40c070141c00449000159492502826450070341d1b40c0014000138507845500204050b5050b00015000c0710303045081d0382c4d07aa8595086c124064007582c0b4100450b0300001480b4100e003034004510341c080b00c100c0d440c1c080c2041d80d40c00701c8a40302c2031144240c1d41c204039008006102492802031740d0b80d11101a0481909281e102ca000c901000071503c3c0844040340e6030000c16040c0403003901c0c050001c29400c02c0320711262401510080c8421846502c5505000b40d40510b01c0141c400e1030341c1410501408a10060120180c40d00203040008078401e12416000740800458900c17001d009840c42080c5651840303c0741d0340380400305604940010078251000303544001041c44814030500c040d02504507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 302694235 1250 302692985 302692991
    0x12030f1b1e12160c0828050915041203050f04080d080f13020f12010912030606030b060406020a0305031003082107080405060a0903090302090117240604050a0b0310 72
    0x24000d410481d0322005080341d80000c00c0c00c5410302003d81d21650301c011507640a0591600c1c0c03880c0304140500444c108041100380000d5a041011071584500605601c0c0c1d01114880400c940d5456146200e100301d019001c88400c0500e00d00020034002d500600c500e508141d40985000d0f5241d107460b040400040c5050700250484041c4084240c070340703091607000840c64080006c62080d41d0b002a14410021410030b026050030192070a28074429071240040d15040811480780c0c1310324140c000e0040c1801d0184101203071404814555606148042d103060700c050340c00510504030369890581d02500020408200400051b02c040005800d84003d0203500c141081b600c410746a02407a0355240c5040240070b07004100d40401003101142d00082c80b9030b00646034040002c0c010702681012207810701c00303400c0030350402c898000000d024501880b80c044101106401da412100c102c0c00441407040c448452204249103400200309030380388c1680040c0d04001d458030001070080c04440403900701303900c00d420503861544d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 302695485 1250 302694235 302694247
    0x5131701061517060103051911031e0f0f0414010c03090b09030a09030803150d0507050f031903120b0301091518150507050906040305010c0212030f1b1e 67
    0xb200000040d44014105461070446104107a5000b2100030201410592a4808100780d100101544543c034010300c0d10a10140780e2903018050560705c183c440c400129169003c0010114240c00c415000e2106540307107500c141c9420003070350128800540300b038902c05e50100221041c800e00348610305501c412501c010419111605010101800090034210140c00c100440710880340c0c03124850301525809986180c582c0c4440e910400900509510301c0d410082007281d00080c4840002d8450132590110340b2851000554000c0c10380790840c41e020031402010098002c0c000038051350461048404069000400342d41c0a00000e00f550344803001501c034506ca051448181aa00340161245c0c046070a8400640039081d03991600e403c4125100c2004003990382000c11091403103081198001e03d402809035451725203d08000340202002c65003100588900711448025840090a507440792070706910100c101e0380c582440c1c0c1d29828082e0b200080e801d00c1000340b079a000343d0042e20307154521209101907031615 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 302696735 1250 302695485 302695499
    0x15030606090a1509150905030307020d24020d1512030c0623040317011206150f080d030b030a030504120c09060f051509061603030e010603060203040303051302010206070513170106 79
    0x1040d40081c0c03404c1107581d406c14816a1400002ca62100358140c07102404034550b400e029014400001d1a541031071190303c2c24200180250300500700140c40c0035404c109240c00784842e00000943e51090f04c40f40e843d9100910302290117452030040e42070041401264504908018000a580000d10541c24110f02c10074031080c182c3c8540031415640c404c0380454055410000704040c0150100e9000f001d8940b1401032546212003251018014207e44100f044040e8031220360544070340a02903d03000181c94254124046d14002403030f80e0b00a601900c070750b8a82030808528141600d001e010503114506e00d52000a109600ca2007001c2c010441c1c003072100c05031070407e810848001c5007c0c19429042c8800d02006506030354140c1210a001c020740d0130301340703110094507040d4003400c40e01101c0c41c0c0b994641100001448100d8004521840c80303960b0400c02c9940b480041000c0707419480c0b003e40143e1040d000689284d000710001c050401300901201c00701c03640e83c184159200122800c402159442d500204020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 302697841 1106 302696735 302696759
    0x2210f030103030c151a04020f160302060105010e01080c310902180607050a022209060902030c1509010e0109030f03030605090615030606090a1509 65
    0x25a0740381805045130070104e0040e605110b90641a40c01e8052070b01c1141c003864040742d1405200301c0c0c03000510000b50019105159080e07820407009528480303508103080e4240c482c0d402032840d903040100041c90341c2600e4000074184030040003401420039141050781c01030402510180d111150f501c0c558081c0603610305903040010080d11010900c900507030010246840d2911104100d04215014030204c1d1298550141c02608604c15440051400c10100025902060a04070011040001c0d100859061000032503e455071200b0030310440c281840b011001c0340f82101ca00d04801048141d50b50207215940c40c083c100109090103841d20380c000c00c2c140c1d000e90382140000d49420824600503008000901a0500c21080c0b01d0000d0700600d0500380ea06481c010080304c6c64115214942031004a402442c9840e0b440041600040b8241c01803807041c1101030031a5481e00310780e07032074030040c1210 = true := by decide +kernel

theorem cover : BRFrame.Cov 302517985 302697841 := by
  have h0 := BRFrame.cov_init 302517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 302517985 ≤ n) (h2 : n < 302697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
