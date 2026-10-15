-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5202
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:04.578835+00:00
-- url     : https://prove2.me/submissions/e08de002-6dbe-4303-b630-461d02920bf1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 935431654 ≤ n < 935611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 935432904 1250 935431654 935431661
    0x10804051e030d0606080403141e0f09090a05060a0e0405010e120d0e06091f0908040303020604050706140405130902040510050a0e04110616060216150207050c01030f 73
    0x380c240181600200c040c00d407a10355281c0c0200d00e2501a1468180c0115a161003046030324000c5425039100141143c03003d180c0c4080c0d80c0715421988040e41080c5010a10381c41c0d2030081c0a0034250700030504e4440317100c0310a00040d84002400d10141c0da2a21080001550383e1042000a441607000c80100f1542c0300d2500c030380102942e40e002d443c9071080702d4181020000d44c100926011800310014401200314410305596007001790b446030100e40102d400d0360900c124030b002c08600382040507804510310303006845291681c3d001d40c00640058111404100503c502049500000c241c14035060721a5819075900099130f00072809070070310035200c10704800345d00003282c6c0003201201d400400400c50381c200070f0580c0d05140c8482c41000c0c043c00480c000000e4000f221100070348201d81114042a03482c5c14041048a503510030304100325452401906400801d0300c0c3e1015014422035908103100c15459820300117130b2000b0700d48601a0150040040c000091004514001c520a082c00d010803031302003410408024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 935434154 1250 935432904 935432923
    0xd030c08120421110d230c0d1103040b070303020a141603020601060201020a0e0409020d050703051506060703170a020412050105150d0b01031b0906152c01080405 71
    0x301e00c2400103100038400c0004841031892181005415480320f0018141c825101030b82e40701410381c00004007096101c0c0030322025044e11081840e07118060310440c5551101d900b0503070418805512406100c80125003080e021a40c0410f081c0085040525101c81d14806104415000302095000309007050100e000b907400f410000d03c00c00e2515101c14001800383c03c103045207003003030700180309900c000244140188221034029210303542d480032000d070000038400a026132510480e0410b0036143c0f42c801154041c0035003800b4602c110b014103c030845410451149090183c415842440e04010440000e500f01070044c1000e20b000348443c040d0355a00c030f4010000d0040707a200781d9007050b14040031002c2100640c48140300703c0c1c04420102e81c0808400500418000302c5900400004140d0018000704201c0d051802d03000542420266a541c2c030790601d181078070040c1e44150599104010303140340c2c1c2c64000442c1c80c51400100440200d8013240a46a2031610032442c105050003100f2011031b0a112050040d15030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 935435404 1250 935434154 935434177
    0x30a1505041e0b06041211030c03060705030108011401050603041b27060b030f06060d020d06030c0e0604050702071406070c0e101203050d0b01050c1e1002090d030c08 73
    0x50040c03660664512242e07050900350003490322029508134070705502920181e420068180c4400e100c1d0b540c0300c8941103a8040d146500d40b081c03920010041e40d00f002514800c0c00c43d036a42d01c1c0c0700d52510164a080d90550a0780c1400d0540c2c94006028544131642500e40c000d4110034403e0305244444103130788004481e504080c10440000c019181811004800410203201d1000c00700820b03541d0f003054001d54081581c0f01c1000b04000e4003c00c140d441d151000d84204070a0640061a0030519039100040f102150b0040b9240d84500c0b80400601246024040c3c2c4081b05444c24003c034070708403038005d48485481c0101c480b601c6000100c0b8105403166015100140e5100c111941c2c040c1e26070150030000c0100b100e5480c4040c4070141c01040c086401d921254000c0d40c036031a05800d03c0001a1204040c00803903e065040241c1485000c000b51810001e040b5007000c0c60b140f40c0d94040704680d0482c2000700d541141510280104507410464030f401c404101142d4240c0380590039810396142c18031403881442400a0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 935436654 1250 935435404 935435411
    0x150114130e031207180905070207060810030605091005190f090210110309090109141008030a120b040f050405010e03040f2918010e0f033f031e0903030a150504 70
    0x2403840b40d55000c1401404250212b0b0780d07403940c0340e6080b40c011030112090301020703003030b04001c000040142d0001034208420009990388007c0d184c1c00b00c4100c5100321108000740340400758a00b0b034405d0500c0f448022404d03045080c03203c0e83e04c2c0c0c2c002c5111201e9021542040000f00850154100d5080c07064070845880104442c0107941d440054401421a0010040300b80481030b0106a00e10307041c542c90011140d268003c4c50902c404104c0540300000903003c004155515100c85804581d901d21900004008a560000d81424030b400e20508668090080e000941e004000a12903100c503080100c0c126910780410820100f201444c503807100b6040c04c0101d101d04400b1420342003030030884c02000803a00081e40c4045500c8103c904005900d0091459550160454503250800c200b42500403261000523040c3d002c0b00c0304100d4022642c1038540f080001c2d03281000f10501a14207005400c2000a4144a00946c0340703007020b01050b07841e444046c00d003500c810390b21841d881a0740401c032025402010f00034002c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 935437904 1250 935436654 935436659
    0x30f0c0c0a0804031209030201090b03090106090905010507030606051c0504060e0d210203011a070c0b0c0c0901080105010627121529010e03150114130e03120718 71
    0xb22940e4015010442d07580d00d17403e1a9505071442110410b04130b0380c0595440c5500e41c41c207218001c1c3d950010340164601d549502e8003044944c002d002d40510300e440f0302c00015051402841c002c04540d0540c0000c010000d04114031840701a00740c4040007000400240001d140c0c5551404800070301071700242048902070031042c010310301c1c4c204150082c1c0d00350394440301c0c0c0c01c078810840c920100d00c400d020340aa10011416102c0030b01c0c0015020b0003107944220800ea603a9030300d07003205040542041b6034920321507001c052040914240b0034001401008210002e010f194101480600070180c02c2c40e00c28481001c800507840e18091005180c0004c114a015040010109082610b50f00c0c40c14800b0043c89420080d110607881820b40945500356042e00a50b0901c1c070668004441e9211403201c8158075118680203c250715a621452500918480c82d419810048280510421940b141807070f804403450050070701660390000c41202c035020b09168075403002e940d80709810350b092940c40030004400403645001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 935439154 1250 935437904 935437913
    0x1030c0309300f08040b04020111060405070501090f0e0a150b0c0102040e150d1e050313030c05030f07062619050901060f1a0c0d0903060b0f06030f0c0c0a 68
    0x101146a02c6111400ea41154020003520b058500d1880d000c001a5410300250105117542c484540041c8141f40016404000001e0245000c5040d201610345401550040010f0341c0c2181558006084101c0c400d180d0a00d401d59003480007500a21089256449104a42201800c030340c914001e060014038458aa4620405d6a4000d400900841c0d250459003408507400024850800d41e01c0308009202c4101807100d40e95045000b0342002c0b00c0d1002c4a500000d0100041091018101440c0d40034a8803003d1890b40c10164801407440d80951302940200d1800070002801180c2031050790150b0400c07100380240d42900d6100c1c10707008407400315180c00c108180140008014440400d280b100031003485251940b203d003500302d0f0b1946c80b80700c482900039482000b80940c07840c800356071022903060041c280820041d1312810403d0b1031002e0000918034540500800c0712070301c20b0110988080d0382c1a22040d45410200700349200141603440030034000c2c0c00040d503100c8014201c5a0b643c0c183e50640d0000f400b103151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 935440404 1250 935439154 935439203
    0x1908010504230606151303050a051005010e0c03070504030c1e17030403170c01141602060112030c02030a0204022a03070503070f030e0a060503090c010e01090501030c0309 75
    0x608480040d50b180c0001c400741e2444001c4140c000c0d80c0c5018182a440361010010b2580b41070714008207071310061207040c1c50041c48242c0a00254040c1c0041c00c088c0407140307031a034240700d90307102e007526101d01e01001030142d00290008903500408203c0c2d62503036071b103c200c0d0503620343c020b03540000d0401c0e07829000428402c1e000044144460590000308051035125a440c522482011506052541c004c0c481000819280190362003080c070280000c500e041c0c4000d81e41405d44dc0c41442e0101c441104109000c5086d0104000e411002c03a140b0151180717504011124072807007001240901045546002c8000755603042c00307141c483d60b600510465441d0030b0004c00f0021396213040034001300718511551018448a0100c1280e01a95000018614129a0b81d50310115194403000540c1000012500900c0c80c1d1a60250000940002c0d02c40c0d40e01ca24141700d00b05e29055500300d020b0304006a0814031012640c01c100c003031090759400d003000f10b0340d04040c20044008149206024100c1c462005101503e201a02c0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 935441654 1250 935440404 935440411
    0x504142205070e1e070e030c04020a2d080a020a0e0907180906050f010806102303150f0f010e04110906131e0e0a110c0d02010b030105060319060b19080105 68
    0x8001c12400e980303101046e038410301c1c100d0015406400c050030722103240c54190b0040c58441054200034078203d0454045804940103c0441c16540d0b00c0030840148468002c43c1c503541c03051591806515107103801500034001c16821307004600454400011840042c010f00c0700300c8034a0071803c04650031640c2e0f040e46002400d030b00d01c2100d0241040c84101510b40d445540610b11808024061015203081c2032012a403ca0014141d00c450503440007000c0c4154044c000114014052a0705a4400500400800000300131132000103202e424800c0d0000d00c2660490445d0a502504940004440100c2c1050798800e214a4110381d900007400120043c2d1900d010441106075500f030744081d52005000304141125100314007c465280001d80001030502c02d940d0410b100c4170004040300383c10b00201072002c0c0d00e031040c2c12030341002603511144070410a00782440344a070302100480007090400b042108038141030f01d0002e40542460f8a49540740490340310100d110100c1c82c6007013078000c1d299684815042c002c280070b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 935442904 1250 935441654 935441701
    0x5070302120a08090d03030603210801090203090604060e16030c150906050414010207030204050c030406050c0f09040b030f120304030306061d0405040c0902130504142205070e 77
    0x1500150a6000058201e9500e43d005030700364980b1342a8000c00450b117071034007022000c0540301c4070b001c00058142420402200d8446911044040030031601416101050b080080400d1042c010440c01d40700c0002c1454110360041d03c000784421194584e41e00f000c2c0c44d00140203040d030100200004015484c8221000c5600d29620b050740341111540c02c442c220750030701c038580000d04103000c2400b0246002c400045031210500440d10315503500c0d0301007002d50303508407030341920403101004100521441d805107130707405901c10100502e0a000c20300303440954004c008034203000303ea4031800e080450301c01f04040d040010980e1b003100c174040c0d4481d00c004910340c4111412030002e400c05000192031806180d807000024540c446491080c8018400d01c07008000041c000d032a004041000014001801e00c0140003c180100c400300c501c3d42000c062206440c1e200d04240da0381c2002e80f080002d1229413042c118a070001c580c10703184a85a060400510b80152a000720302d40c1e5092000f488800c04040003080c50390b8191 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 935444154 1250 935442904 935442919
    0x180a06210203130305030a2c160303210612050d120b360903130f0b070b040305040803191e140307030e031c062102100c06050405070302 60
    0x12404400d099001c2030301c0c00004010f54a84a000190040c005141c0c080c1c40b000000580e40c12a45030380e502001e400f0180d4110341c015461a04d4540e5043c41072510b002620000049054034603680240b11100d5912030700f481603c0310130600c00c17600c2a81c00002c002c011007181340c2d0326a00182461a21010344da000c6c0d03800300b0040c0c0342d0f0790704404041c02203098644000b010320000c6140742d0f007040c0e03040650b818480b07662103800c8400f060380c07030800e50114019280100156142d40e41e0100958501c001500702200c18500c034401003202c1d00c24241203d08940e07000d000303000300707846515040e541400782e82c0060384540004141d0f03240c030110303552492400888a80d01c11241c0c40d504143d10702072505c13070703804280083c03140d8841030300300100c020065400081034500018000369000342c40d42103400082d60b43c1c0f168201d80d844842c3c2050280103000c09401d042e40c1c018100611aa4840907101843e200240101c145452855019002d40000044950404014000e5251030f103050303515030f00c0f5800101e100700781c0e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 935445404 1250 935444154 935444207
    0x904080a0801270f0b1c030f030b030309150f030a0902090c0a05090108250306091416110109020a1203030501140f0103052517061806010302180a06 65
    0x1080310f103c07a4030010308026000b201c008001440054612140c071071801503100e2002440540b41c0140751000c4040001403401081c1c000d01d4000d00c0300755040c150340304160500540b00410394000c811254960400c84d5089081100c00552079924003030322400d040c4024002c8208904c4220355009001c405208072008003a83d030358a201d0221500410110000241c030030b01c540441e9500a030381c107a40150b404001018040315202810454214400300300c5d00003a21040100308800c42c50040c40c00003e44070071143c0c00c9103406800440110408001e060402c9140c03140682011420741c00081c0058020740740010080d10390840c000203145804c000c03000245804000540350020080018806200400c020088540da600440250102800142e40500c1c0070a6118602c1d800c844070410310110f07a110006ca08081c0300303641034100c6004101c00c0c0030301e089060900e0310036090b10840d03500c01c00034240143ca0b40c03240081a0345c0440c1701c52513150000450880030400c15085000c110360542d00740100888102c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 935446654 1250 935445404 935445419
    0xc0609030f0d350c0d0f18110904031b030e0a0609080c2215051206071704080a03110c0708010e0d0908060f040f0602071a0105030f070e090703020904080a0801 70
    0x8421070110424020800b01040c40c500b0071500070b24400001380b102040d1b603c11002030703100301c03100382000c2243c0490790a40c030f03000c1000c1505e5401c144d035801c40383c1055520700341d2000b908600305a03180c05e01d52100318001c94105800f810744624094000341c01c0c04251620b505000d0100c540718050100d261192080e81211840d1100b22016048025200500318151030550f0700c001d40500708003580180c4101c0004991501d0702003c9500c1d2900d0f0310000c084074104040f025105100c07000c00300ca1a0011714041001181c0700e4021a40341802503d0009071050440c01e010302603008803183c007074080c001c200c80015090015004511200d99000984841540c5c0700b0059036041203611070b9190642210f4001004000b451503043e601034060480c0520b030000b82d554100407030b44400b01c120348400e101d103014030755400703880c0101b805821709400404480d01c2540030b240c2d864805116048241c81c040e000103208000a002a40081d03501600380750301c504161901c0056500005068000505550000107030072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 935447904 1250 935446654 935446727
    0xb0c03070207170f19060c09080c09100e09071a0c0c130213030506090c0f06120711030a0915050918040f1a07021b030c0609030f0d 58
    0x850030354000780840c80c40d104440c51080c11220480c4400c2c0078243c0891150b91080c0a181d24910309410611108041c1e0300c1e0400456405500407001c01041036003c0c40138002c0080c041081c010121188126a070740c40650b511154100c0e002031310700c241c0c1c0708184260340030006807074000c0c1c51451b0708210310107c01c0b4280a0755400340034241c854076408451091805d0800f0903d07065101074461025180c1001d00c52410745a03101540121241e40c08001040307000c41c0240030043d02e4010440c0c601030703a03011540c0010418001d050302c03020200035590101d00401d000e40c00342c07402c282d640001e5075242c0840c80710140084481d4400c0d524650b04c444103480e0410f1055003106d00401004104101210380d1941c00068040b009008540784c4c040701c1c030706c2030100321000c2030443c1c410031218002001e07281600000f82492000581c0c4407646101d007166540365500482c5001c0400c01c2581c100b45c803094101c0000f45414041e007502d07a01809540c0d05d180680781d01c8203030304413845841081006550365014840c000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 935449154 1250 935447904 935447911
    0x304030f081902031803070c0e09030a21091509020114090d1b050d08030601030f06030c0b0d110c06070f0c050d080705090a0e100806010f0b07020102070911070b0c03 73
    0x2c0d01c900070500700e060780b01c9a01554118001942c01d0600100c1135620910b140c4c003c0300140c40c030544145040040003118030500b41c3c00301d0b2600103503060000d60b200160030000190907428840c205010b21854002403580101010b0343c00c0340c0100b420420b41076590004044003081a17001807061038082030790703003100821031780b01c008044c15078482406541c4030800480200200046005138000c40020240d4500388503440d194050801c070303582ea0a0000015048500f6600800c104608100007000801d0000304128125001d0b00303101070b039617000c048140c401058804000143e00502041c0344200c1d0400159483c800c030346a846020804409500c203036a040004180200700303510800f07400104610419040360416418203105040841c01c6000400c04680707a00480b00c4034280038100500004919520002030503a10050001d039414030580f40140c03502d90044000701350700016510b0031640300b0802c80d4010022014204247c06c500201d8200e154050282503884810700408520010b403000e003240d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 935450404 1250 935449154 935449171
    0x603050604110c030a18180522170a0e060309010b0f010c1e030504090c1e05070308060d020607050304120b0c0c0d0f092706080303130b0406090f06020304030f08 71
    0x2442c00038041100c034102e846c0020000700c4440000003d031406000c01203d0244141140401c0300d161a00d462007610801ca02551424a804220f10010503480380c1000b00101420900a0b40d5201108040e11503440380b8010742d800c81d600008002d0030213030660008400318802c90300813022080c180011152200000b02c00b400c09180e5000c00d55424000c81c044220b424840d04009003840d0707894904404442e032106004021a044d10007040c042481c2c405041d00188003030500d581407003259140100644c5c4c0c003c100c24011440d80c0005010755a9074410342d19215405021644c0d0ba64442c041841c4060f441c0404072944203654020030401401079040e40c40751108440100450010603404440c01d040262541003803018854000c9804181107521032814100603850900c940b416030001d40c00c468075544500d01a40007881480540e0b035501c2c5407500300b0742d01701d1181e540c6500c0300c1c18604010300710340400410500801c036000082050540145124901986892681d07000d1031106030390400341190b8011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 935451654 1250 935450404 935450407
    0x50903090901090504061107030c030206010f1d100f080a03030f021204020618061914070804062d0c1103010b060d0c090801110c0601060f0206150102010e06010603050604110c03 78
    0x104040303084d80601c1e071140c0280360104424005101011107940604e07415030024904110f148185501081454010010a2485443e840c605100d0309410000c50a200310959013602c00300b80e61003003c82c04a005001e1000c0c0000c00a55128095543c410000000310042820045100411070151080d902100003008640a203507a85d0303400c01629a001906989802041c004144803a4481c80040c1483c02409107540d008030101000103091180701100005d0204410042440098072220546084900d241820004402c0c006030205a40022104500343e10007407084d540030300c070307804000c0f10001401602203140c020f410b01d090500707990350002c100380c019008124000c004aa943d010101240551078036000c0c0a8a404801c1d00f968011080d01c1d42d406030108541c0c0702e0340f105020030f5004040383e081400b1a14020032020b5118200181642c00080720802014042d9000307401500300c3e801d0300c0050f80c00c50341c0c40e000c0c094001c02056846900076450050404103007006042120138804900c1c0046 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 935452904 1250 935451654 935451659
    0x9080a0203040f0807060915030f090506060406080f030a03090c0b0d1406040b031c030605031606171e0c07080316021204030c14150a170601260c0c0304090b04050903090901 76
    0x20410351585100080405a85a0ad4030380701d5046445081c4034079110700c0140010382818400c000c03d450090700610000d400c01885114034203400011141103d080d0700303010854070310600303006007030100c0c1c0d500511424000040710b9030034140980c001c500100fa811903401482d2194000c2c0001c48050f1610240c15600c04a44180090f07030300941c0358101d29041c54041041c5407a0404282080c00b01da042e881b10080f006014050107030170503001c1d4010b030100c10b0010f80398501106501000a410700a002441c5a03160100e00710a80e2501112070894108419039500e007040c1c43da28040c4180c0d0b4070000014041e000341c02c0b000000020440e4110398100390610035441c1001075142d5190222078201ea8801c042030f5090354030140d0075014100c0c10410381c8801d1a40e01c100d102e100c0e844c60008048604006001c40070345e030424408a8501e10031551000e214501da9a4245101100c1c450020040410b1101240000d1190100c0d003150501c1581902c040c4110340382e400f01e05a9074054521034540c000841b4005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 935454154 1250 935452904 935452919
    0x50319030c030e0307080307060b090112020604031523090f03270609310b010f050c0114090a060e0c09070f030b180126061909080a0203040f08070609 66
    0x1002c0031444004c0664882e140d030750528500c0c42c0d0115500f00ca041d91544465242850554040c42c014001100c02c03032070320a4a54002011481a804000d00c100d0709030220004103102c2e64010f0080290039203102c0c0009608204801c00c0f210100c600f0070091040d07990b002c2c0c0142010069030401202c40e5548800302c030300d0050380008415410030843d003105080c840d01000ea503a40c1c4180c0342e40300c0301c10341a101c03440218503003070425110f0120712543e440c2410240c02442c0d902001000881c0014030b0070a841c1d0040342c903d58050b040319140c0c1c0744156441d80030300c200180046280d00c1060711035038040048480d0b020042d85c64000314041d05a00500b102e001450300c90043c2100e0307407620300514000410000318000124801401d000384c58039185c40304010302c0400603801000418070340d04400009540d07100c0e00e0b4107540d82001000004800c02a1070300c0c0c8192000c1d6040280311640c070081d40707034440103908002903072074020b840b64024100314a000010081004180c42c400d545003680c0350900c5038100041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 935455404 1250 935454154 935454167
    0x6090f0d030b010e060307050a090b040e040201030903030f090605010810051303050304050307060507020c131a1c020a090b041508060106051b1903020f010b0901090b150c01020301050319030c03 85
    0x2c03640c10b0064580008503940d880000540c400e182c0d80d1a0075440d0400c0d240c0003041250315420913205100c0411040c01054041164242d02a5092a01050180551408401401d00b500141c01000e0034442640e0401030711b50000d42c1a01c045104a408203600d804c0c2510603504240d50310b0304403c1c1d41d5403104020910540056501c0f41c020f808581ca00350203540c508040f16400c46540f00140c111120340d000510305149520300c400744581d0700380126403182d94005400694050640e11903c80c65158152001064400625098006041c10700e440da4603c441c00103011304d0040c19100b14540301c00024034880715050701081d119420000c058603030920798140c410342d225039810f0720303854490301540c0b00b07042003000032450007041d0f0408415400c00528002c0e10b400e41484001280d64100404048207485001046044404c100d40206803400c0200214030540d101d001c03203000d11710340003e007981d03160415001035048480c00c1e0115240550445040110140c1c8500000c000070803c0f0f940001292041c0d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 935456654 1250 935455404 935455421
    0x3080a020a020907021501091103070305060103060b160204060906030512031e0103051c020613080f070f0b090606030303130809041b110c040c05040308250b0906090f0d03 75
    0x1260000c00d0705030005a0080400c9884c070005030710204418030800190b0128070f004140e441d10501c41000410074149541c080100b0b90001c1654030740c001455688a500410010020300041c541d89002c202000b01e21003984203403d901039403d0002c00134005290340715030301c01c580d0400003810380e0402e8a1340b001c0035540064501c03003840209030402451007056024140c002d61291008001b8406400c412412090701845000b095401140410500c1c9903900090200c20340c0c000c00d5966507003001500381c0603500a03000013a0101c044032410f01d04214100d1807450250910b0002c5400709d980c1c4000f003540d41e110803182246020301c0540752600148140c0060171202e28000c0000c82c045240d40160140007904003008000a00d40c03041c800c02040042c400b4031040b0b44140c40c144110114810081c142d489540b00003029010002840b8480c0d001c1c10b000180d0703210003030700e40c0e203002040c3d4117113149d0592050702c0c050890b02828000c1840601d000848104607041d41016041102004c1703402d070000c00c820b0303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 935457904 1250 935456654 935456657
    0x9040303060f06030f05070c0b130203070902032a07080405010e0f2e03050c04030b07050d05160e10091e1e030309060207081c1116140d020a03080a 65
    0x491000c9151000382c030042014104554000a02c000616040710580354090b00080c203210740030804d400030030201464150300c02c0242d100701c00031904601c0400d15000040c1d0050308001d1021080c44220425440103000441a580d6010010b20b840b000401051107104802000381400300000c0203654007884041d15040801003900114050300d602260112488000544040c1d210100000d0181403104020000c0240380c174041140e4074008d4414001ca2150307010151940307031100001442c06128002310b40e900c815941c81400f65082203400c0f40c800c0b0b00c500c50340e44c010888004590f0f1640c28944403020356080a80d4a1611091811000720901c440b8501000d550b000000c1011818030074600e02c26400c3c1c031040040c05001455400c00822441c0703070387c01c01300464010440c04c2000040000c0c0c1b100d200c04121541c84000003c0340019159259040050003180c09030b442013410400f95a83d10348102d40d00303006004162070f089410440007441820000b580094a40028000305411901400082116 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 935459154 1250 935457904 935457911
    0x5150418200a02074103010e0708070812030c0d090611040b030a0f0516050c0a0215271302030c04030602040b0a0e0d030801090c021509070e131109040303 68
    0x20708605500888501c00981c1c0f05510801690b01d21001e91a60180081340d035518000420040050034000001d41a615090418010682c1e907002c0d0310803512144407100308d461580d80c0300c01d2640c0f105034604c1035603114042d5207414444642d000d4203d0348602c0c8080d14080c43c0034130451030a00280500f03001a145503940394661a1440e01000061002c0c00030020400c0d12031030100054029900b80c102540512070510040c05040808440130600f8a6102d0800750348664910490520304054000044e603c844000c1e038817103103400070701c00030040701090303092003070714070b80b40c0c0407840081700c07600b441d00d90033440d00d0540c1092100c4075400745800100314414913140c980d80e516040240d812a801400c14007000140d404003040d00014911760b003803015904289442d002c5d0300c015100440500c54245040d40701c11110480a200780007011b2405090708482d200c3d8208a44440c0d034902144c01a00b800030105c1000c51801a0030b5449807508a501a4621000544182c24040b640d140904100c041c10307103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 935460404 1250 935459154 935459201
    0xb13330c3201110904060504060b0a1b080316020d02070b1b1507030605030d080c07020907020f060907080f060108071505040b07050a03030606170411030c0d0b0105150418 75
    0x40030b0280c15005a00036012031340f0f600c440400c120880f84140e015038403c43c42d065003084620903d00644500e41102c2c00c100340d11452440c8014414025803100400e856400010004c41c0700361940040c04814407030f03003124210b0082c10000d83e84e401c814000c0130106141444042c14400c02e11040d00c260080d6031007074429140091082c50202c8200781c1e2000c3c08a62508018011401c04020310300b807596607440c00300d400d824151400c680754851008041d000c0e01807200014503882c020002d02c0c60360140141103a51910f04074066a0b01c8902c0350140a045019020082012440000384241a6400c0e04040c100c00b0b881c2030805400300d5544042c94080c0101848001040b2140001030402d041c042c0000d0303c4828000c0c07400504850243d0400020700c00d013106582d812070340480c4102da0044d40910030322030143c40ca00c0003901d00806440304030fa00c0168125040d00700b0a20f49140360490b01d00352550300303820048510020040c0030724002d41841406038080e004840c5201d0b00404d00c0500496a200403409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 935461654 1250 935460404 935460503
    0x10306050a0e120910170a02090a0e0f04020a05180c07110d1a0c0a020307030c060b0d110a0515070f03050d02042601020c070b13330c 59
    0x2e81050240e05200780110b080d460702e042149113a03010750017510308100890582d0b020005809000350000303100715070200318506a5214841684050b00401858404a1501d0388600256681c200e800300d0007011100c0c000603050400b80c03140707489a944d08803e8807041e601c00c21320752004e0b0410f540555054100d0125510381d620b91210304819140589188100c0a90101e64403900d100c000d4850b0b03103520f40c1000303e04c04c0c0036804019184100c0d403600d4948001809801d042000c1c04050080961001240c51780a04021b19800c2c20701500000b620440100755491003001942c4000c800190135450341000b011f000107259031841d2848c18828100b440c180800c03d40381d00d00301d0704283c1200c1008048000d842c050300c804030b403a622020030701e00f0003540b40c00c48041010707455440e2407003801c0b050400800ea4088071a00d0440d07403000303400350340500f5940002001c4454201d4850400c3d035050700c2c01c3c924001361900d108404c07001d41d694101d01c1c000141080310400900d80703120390b6201d1800c8842c8480c10202c0342c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 935462904 1250 935461654 935461663
    0x5040e0a1509170a020106050a0b07080711040f06090b0a0f0e04030c0602130e0f04150b0105091203091914371d0f0c0f0712020102040905130b010306050a0e 69
    0x580381c103070249481d0340a0404c007078216085500514450100d01c0c1041102141c81d00890300030310740c4805c600703131941550b24209400700c60019055a2141c00e0113048c0b052050b15620101c12651300d0381c400e11094641209110500c0030074010003d0720280b1020900c0588081594a90014031034a040d480740352040d1188400c0783c2120710043c100d048614401c111040041d506035401c40b42207007a103822818035075240b6014141d0302c05d440e00101d484801210b02d9a02540a4580c113001c0646001c80300801d0000070754481d0300001a01e84503a408480284011070020204400c0d90443c180d011000c0800d0020403501e40c13080e0505c0c148036500a40710200c01c84900c403000101283d8002c1d502c1d2138900305440314444004c041914452600b45400708030301c218109800542050007482c880355906845140d11140d407246580103002c19507070754140c003d0550305600410071216411020004c9440f41d25445545079604000602207034040c01c01840412031030392116802a90701c2c1e000048044143c2c4802d03060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 935464154 1250 935462904 935462933
    0xc0a0c060c0c170d11070810020316050a1d0604170604030e01170406050402010509060c030a03111c1119030603020f09010608010b09010207032a05040e0a1509 70
    0x5503a60210004008242c18444003600141c1c40c0c1d10089004002c41c599112000001c1c001044081640070150002c240291000ba00ca1035040ea4407010603010b000e40698800e0f03a8404a5140d218180440b8500c62400e40d20302c440035544941d0448400c04030381543e02641150964451820400090340c2800c0d82c0c80c1d03c00460b0850044c113160310f0181000782004d03150042040c18402010319008114a0880c44039500c9507107d14000349076215400100c1e014055000119000392000500c80c1d0315034000030152045a071136072707400c0c441c1081c00000c001c3c203806046c1c0340303091416455040b0241d42800d9002194900c1040f40d2081c00c0041403041c003540c0420141c41a804a0780e01c0c54144154100941444040c3c00103440c107a0095251040040000c08140310340b200380c03400429015502d038030034010740b4019900020824800c44038a421440114498040c0c0300c199011100002460b0030036000d85040034020f400a855054030301e0300d401c20394550701d101600c842e540d0f0b8061500004c202c40410a030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 935465404 1250 935464154 935464157
    0x708040c0e01240e2112160b011a030a0209030f2a04020c0c1c0206130501080901060f06050a09080a0f02150909060d06020c150a150503120c0a0c06 65
    0x183d07402000b80740c6046914900d1040c08100010016542540b101180500c03000f6146641704140e00d101c6000340d00300240030181031603154002075046100d200010034095518040c00203801c90380da030b480d0140e298141e005c40b140000c100920008400904c01d81c0500201030300603080c0c50800300d0301d1001e141801080c0d5950030104000243e11403003901c075841c45030b10451045c2c0301146402c00c4800f00c2c540e2410303100c0c00540300d034101d495134801307201030542d200d100141c0c013800180d1101c0d10b10108081022482c081ca500246401002440140c014000c40702203800c2140304290f20b50030402c2c21036099000d4228107091203514400042d540c402000441a028012101c071420101b661041001e11035806551000c2d01c4010321482e41e440c0e03600080c040e00003800b02c5003e8400340713251a0110207030003584d540c510300703004100880004403d11b140d01032041621340c40400c80800c80c800c046000c617003c0d0080341d81603803200309500c1820015200600020195008903400c0c40c000741d955030401e8006800090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 935466654 1250 935465404 935465429
    0x1c0302012c010f200a0c0b011805060105070f030f0203090d0b060301051303020613140109050106030b2202151b0c0102010c08011404050c0904090b090d090303080708040c0e01 77
    0x8030344075400e02c81d84122440c030403014400e0600385822540080308100c149134040300000342d10141c183c001c3e8182c00c1d607a548400c4013111503a440340d1031403140859011b10304009003042c3c00030341d556110b91304440e401e50f480584088001d038942c0301200e490382001020800c1d0302c010010350078544da8070800b02a820744140c602040d1450726209050039070700043c0c0b0307020300121404e002c2d2001a401240c0c0a600280006101814501600308001b55408010010810303510f01b01da95400d2140640148040d070b80a84114000b64031070550100d40c0c04010f1344030200482c80e4822020040c90820304282c294a0700400042c01c140c41e407030091041005503000b6603616400b055080d113040d60203001b90103541e41e00c0e04010503550701d002640e00c4646030200045d4440c0356a50300140c0da484106007a6840280044c100700304580c1b09240244110b00e040e5213850700e41c4203021540d00c80c24402d100c400192a41075031818041c1c0c40b000415500e00e4800b40c02101d0b058849040800d443c09071242072402405030f4101c0a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 935467904 1250 935466654 935466731
    0xb060a05031b0a0f151b0602121509130201080402030307062406020d05090f0a0308040909110405010602031b071a1c060f1206090506010b0c060709051c030201 70
    0x101c0f6061540415204503211400300030380d43d2294481c1d0701001c1c032410300aa080b002160a02c2201c60a5100103001510205488203020203074400c41d440742840824824803028414104006c001c0c04640100ca2481d110041078019449640704a801030320240440b4100a155542c2c40c068a15180c020490000c0490310305c5000303242c0071415001449503002800d00140b0600c0c008020307106410f881d0f8000c04400c0c0c0e02d80b846440e82c2d15080004c503000b561054417036460399141009800d14031802e4800b030000d07911180c1145082d1040604a036525001145000080c030324800300142d058003640c40d01d001e00d810008030000b2030f01026110308020072000d86e50f1103000c00fa10240124107880740320b505141140a00560300b500034110309a410340d54901c03582c0c40062803d41e020302150100104907020303810001900400810150101c451138005907911980c981e10210f0301d500b114400e6a503c2051011861000440740300c00f4050540039200104203801c9034280d5111082e084852000c5881c440c1d16a07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 935469154 1250 935467904 935467909
    0x4080a030b0f0d0b0603060c090a06031a10020c03210409050613020d0501030b130f140f0f160501110a020616050d121505060714070f03120201050703180b060a05031b 73
    0x15075400308c5146c801d581041c0c0c0036004540312080c0da0080b0790515070b0ba410703040100b424862554295100007464142c05030a105002511344072a01e030000e00901c0b0380e06805c106820b20070340c05c01f0002100c00780941018a8040110040d00c40070b01025042400303440385c00026207582c00200390068440d41e01080d030754914581801314950080201080745041e48001c0005191044600c000c55007082000b01ca10030f0211034181406a0003010025912801745d14502601010542100d107070200d203c6c400740b440d030324401900c41d80840007d10380740e40c0011000c500145002c0011b8400e40c4005c0707490400020142d61541d11340301c1c55070300800100b030010030510084401030091402024403207884020f1140b0340b0011400030b000e03040c030040c0201a200b508e106a9030701003181c2c0004128811000c079019035642001c80d6070200c560810750055080c90006a021b0303001e8050003030140206c014440c0c6100407910b4403a00d16101604c410790181c591100002c003a0b0301001100440d0100030400001e101c0c03240f04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 935470404 1250 935469154 935469163
    0x10020406090e010e0412020c0a060201140c0703210609050c1308030a1b1a1608090304120609021207141f1403070908070b031e04080a030b0f0d0b0603 66
    0xc148000b04010b4010702c042500404001d8002da44140301c12041c0503c0441a41010340c0c00318400d801c4540d030900001c00e55415040985080f140309012091522049184143d510814002030042649a415011224601d40110078540310b540e00005505803200c1c514001c2e41c00071786100380803400224044000600940c1c00a0003005e00800440c903100b440c2d04058205e00c0141d0004005c0044c8001103410302c911001e004000304420a00b0004601c2c01c1c4400d10704106c030b841940b40010783d2100010390b40703000020444058543c0321001c07501590b0103a0303400300a010350003000c03604011220050041343c00100a2a0f001d00030644050050700c0010061046400111810140c0001d6100c1100941d0390015900e1030031000710f0b003850355299601c00d0195901c3c00303203601208141c4200c807000075240c900d00740954000c4001c40700c403240d018601c181c40380600d6000d0310043c10200d010400c10440303d000ea4041e40710010085c00f001c100494030000984071802d06030066a290081108001641c81d0501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 935471654 1250 935470404 935470409
    0x91406010e031b1504031502041a0306031f0e1c030e1c2307060c090e06010806040f200703081003111c051605150408100216051002040609 61
    0x20b000f0001c94a00c18504200c404822070b107940140d0072250708102d00078842044901a5400c500400390304107010f070310b03007000398010700c0780c030001d5009003440000c1100b02c4411030b40500c20080080c41c103802007840c08504175000d19184096180e440e545040304100c24850049008103401d4602c0d034030040003201a01392620b04200e4512a00045048443c1d0110601244080285413900d801ca5204405410800420964104030745020214052080013190b400805000d8504c0d40c401c5110303030f40e410a20b202c0300b01c00e07124940031600c07504c0001c000e810a68041c038624800740c0c0d4041035002c01c550b4647c04029150803802910080000d40d04189500858183e80188a03070080d181c60524584840c0e402c080f00000a501c61205002600c9042c5003170105e01c8001c81c2c000c0155001d85149542c0720f038456041e07201e514010083c03c0080c800e14107881c0d041d00d003142c0201e800b0340b12413134071554008000d6000c503400054002c18403501102090f0200318044001c41006401030351982041000360017070310944d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 935472904 1250 935471654 935471659
    0x93016120b1503030c070e040615050603040212240115050c032b240f080a0b1312020708060f07050a05070201141309050c090622091406010e 62
    0x5800031000500d0190285911214459140761020081400207081d48a0300107001410f100726040130942c2440200346034091442035004010b2400d65800c5002403a805100f09a030104003840082c0250a14813464404844858240d072000c0c10300f04d21890001181008216040301c100005010720baa05e44060200c5034010b00b41541496446041640d42c1d219141c64039440a001140700e800c41c80140d00300010120320544244491100900c90803446a10b00c1c0d003030342d00c0d00c40ca00400102401040b600d0400e03601148080c0c01810342c82d4813240c10b4017401030100d0000034210032828010074068444446001030315800307044414136007403a0710f24081018010641d144030801c00d000841340c10a0032600c2d410f51a041c0261a1285400142d8860100701d0300c9107040000018201a205d06039401d4a0a90304d54020400c02501c40502c09440e5004a050151f0031080400039052020028000d02c0004081c0300340e030000701c0d900d46160000703461301e140010717243d2080c810a1010668110b141c00681171001d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 935474154 1250 935472904 935472929
    0x901050402150f040f06120f0b031917030a0c0206010e0c0a0c14060a0b030d05090a140a0801092003030304030c11030a0c0b040501140f093016 63
    0x9400044030300d80800c400d5141110300090702c1501c1507580084e20010620080484001d035075810b409081c11100c07417640b030422807511b00304081d405407a210310301e511203002e00200301c2282402c0d0307003070202500013a068405050141c0c86c050440e62000040d4400c5040754004100706483c600301914121040c0c20082d090140764040018420020f82650340300089031506c2c0c25041c03420f08101d011400c8055642003180295800c02c01c008400c1d401c0803616010540c200c4000b4555000d0441e92405060001c95112010360003c2210680c0390300c01c800c281d500144151000341c1d446030410308540c0c000004464003013844985080d4006440303102e804035207095000d585103140950307001748120354400000f0003901000e80c40c90059142004005011035105030f405c207240c0e88a640400c426001845414001a11b400350ac10103c0109015202007407010310000e41446040d10411000c601941210b0000c0e001012045100109082d0103404806464010301644148225a000c4280040d00f004019860 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 935475404 1250 935474154 935474161
    0x12050a02060622500601031b2001062d0b03040c150503070522171005060105160b0705210a0506090709210c06050c010501060e0d1b05090901090b090105 67
    0x14000c000f0201e1030704e0500c440200395034100050b0014800a8055041d440040e4102007016800404424426107800c0d849052404800034290036103480d401882c41c040c0040c001802410b00c000b0303130f400c8103510301005179a100303440b4100e036215500221401e5035180b2a2032001c001c6090b50b1641406038200a203801c501d1450491005800b51182e00822401500441102c0040c22200d5444201038030400281014100035200b1241c0e83d410650501c40b401031801c00400d04641c0039108490307440c40d82c2c480e0703909095402d0700c600642d00401842d040c18000100821a102050480032094060003801c170007200d030070481c0c0400121480200076030f0040c0000014003c4094020075007004641d142d404012401b4440c00404401070b0307482038005c1c46070300d0b40d100209800b900f040c080c0640422142c000c0020360f0740ca0a0031541c0c10600c1110503040b66000c46100b012540c081c4032607509032210700010030640c0d40c1d9008510b403e40c0450b058078547e5074604085081000000c481500601c00000034445400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 935476654 1250 935475404 935475521
    0x507051309020307170405070312021005010e01030b070809030d11071509110f0d02130912170403081305070806060a050a03021302031b0c0a12050a02060622 69
    0x2e000301c4005c2d0310b001c1c001400c0000c104091005154030102085810401800280d91120300d4040240b040707040c440086020040079044504903604580308161302c0d250b0b44415100f8610142030600f10b03000801c81003641031406c3c0541c48210700c1005a090380c0d41da0a0410902800d181007549035424241028180800d840c1203c40c1420354017100c4a11710054040002071814045103002904410b04107034071204980340760300c42c031401c034051040c4180c0c0c4184c1c00d808440c1011120305900c04011386102040119214000881d84035414042140b041d140c0791b1078040c81c001055100040301c2e409003081000d40d0401000400003005d046d1a60500705065a001a9080d0b030075091003425564040002280307072100380810318403852092495941c640b000b0301030f1074407040c1010003610003601c0d01806010242c4600308451602c082035001d080c1c44e444040800c82a020040d0790121101d9202c04155581d010078414070440c400f0380b120341c18258142c03600f561030f1209049800109411182c0d0300042d0301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 935477904 1250 935476654 935476667
    0x170c030f15011d0f1804021c050a0803040f081c2d0f02210a1802101808010c030510151215090603030f02010e03030105030a02120f010507051309020307 67
    0x20300c021400307100120034003808618010800c1a90a60007071001201c5c1855003000302c0940c2c05540240c840724407180c1d10070b040b8401028019001880317940300b9280c11002c00c42e00d001544d0010310071268041c5035103041d10f51882640101c2c421820207000c8416400e020041441076164010394640d51500c40d50b60703a480800f03801440e8400b181303c1070303c400030624250007603411030307481020448600425902006918035640411951221020714203580c0c2082d9061040401c07074443d5004005041d8100c0300c80d0300300e8003910718802c05913810b09000c034007240d103400a0241744004891940d00041c0f030310300040c01d840c0c0712245900c03440320300021036050125150b100d040038480f41000d91020543e07102c2c00e2050343d405151035200000c11481d288000c810103500c031840480181d829070090088003103d64400e9102d20080c800d150b49540302c01241d000504100544444034048481030314007510003001050b0070360300202e40032030020f0f00000c2d0903040740040301801b401a00b040d032011815890450009400c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 935479154 1250 935477904 935477927
    0x50f01240e0a0b0603100614130302061e16030206060d05061605070602071101030f06050901051507020d120206160210020304080c0f0d0e06090a15170c030f1501 71
    0x910810800280100b031a03034101007040000a00865a24070708149500b14188860140d8000183d00c0e00031810088815000e48582c1040030300c1350b0382d650341365508002085c0e004540c2144040307180300c2030501c01d002c18005008101c005001c0c09035030300f10a107002230030118028422882150103648140104100040e03250b80501c044005a03c94410700c1015900d48c001d442d0002c0c180390000441d10100b141142c1c00b600010300a880c140202c01e6559151820b45a05008107a040081d14004021910b00644242c038910b08030014035161100c01e030003007481030516140c1522401030035041e2140710f685c10044140e02000c0c19560441000304542c00030348501403040000c0a1b943c0200101d414440103074120341a080b206011110501d0252401d151112181040b40021030384941d15060142400c01c01c58010201c01080640b07280d0030b140c0c082050005004a180421828940310152550f41c445c150303000d50405119161607141100b16010040c0d0000c2800c503503040003452098490b6000403070400c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 935480404 1250 935479154 935479169
    0x908070e04051b01020a05190c1211011b080d060f0803070c030b07091d09120708040302040531110406060c0b06040213060c0c1e030321050103050f0124 67
    0xf00d03210075000403490140310110251850140c0c4410203240c038007803001c907040248280700c1a00182d030f0313a2070540584046140081d1050180c0640c100c4550b10520946c012406e1b0901a03428400c07003904d403503002d504115400302c0901e56a83d400c0c854500902c885a00034103000e130041d450b00b4010383c0c450356540214031000709009042c00c00b1031100ca004010b000050680030010740c42030080e501c250f4409000030350f0026134038042c401300b5020300d02c401000c4400031504058250302e07240c41c507402d0100400004100e0124950070b811038050802c240032102130306058070442c1400c10102810102114030351100c1c4036100b0f42c64003604101c0c0d1604240c1844080341c100d5950403265884001003030182c8518048049a0b1419440c041103541d08441c0200340300380140740075160b0540f0380692200c0584e03032550a2200d91480b41080000910686c5459000708100d80341044040c00b1040301000d44c0c200781c004441c00d0300030b120b02002c00c510920a40014001d00001d51450b03008404150280c00698000c030403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 935481654 1250 935480404 935480443
    0x4030c0e1b04030f260703030501050a30021005031b160303050a0b040501080a14030a050f0309070506070c091404210e150a1103040b04150e0904030908070e0405 71
    0x80a014507056029600140500d80780c005c070f0011200c00d4001d90110204602013860701c2d00100c3d00b030030030348074400c02e542804166000a8444000d00344840a80e500f8140e03002c0d6458038164010384410304002d50743c1140d81c80340ea07220b08000c204c0035650b543c507a00300d40000905100300d039140f9520f40c681000b02901424000b4180e226012a500a0440c2d85c40070782d003080c1410000501e0040009546103094050404101c03038103c501b079143d44070b104a14444000910600100c10400c5003400210742200500040340c499507030303900128020340c102c505c09803460b0040d0750701005050524099014001e02502d00c8419034a0180c0d201141d049824600280c50b806400c0a5008203004150f00c94985200410b0145100714920160b42d669021040040018080080d03401d00c040c4000251000d41d000035405904040c107102e011030090084a503003104001030341810aa0701e03154103c86501480c069a1209111030504488500d0045154802e810031103082c003c00000c2203000c181b10300034420203544078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 935482904 1250 935481654 935481683
    0x91e20061209030309010b060f03040615090f050a0606020109020904151e05041101050423150a0e041109280503060c09010e04050613090c0b04030c0e1b0403 69
    0x15860340101c0c0d807046081c2144500b400352041000001e1072242d08007030007d00c86916904203200d010701a20851004c1d1072424000305000030069005400300c1880d500f0000d4801d5070b0fa005180036680e112181c04640f90740d9406010a02d0704600036075020f840307503000070300c0400d460350b011074003140c0c004201420442109450098020841e0032900c5142c1035160300f010300020580c0114000d000903a002c440c44282d400302a00a54010002c1c2d4003104c100180b1003a0403640c010040c245050040210381d40801070710f00d211315600e00341015001500c050b980b1040c0e614448002d01080f02c804200310300c40c0d60010b011076081c4d41d6482d00004203000c1403100100307800b1598400112448516048140e042c0101010481c055112034060000e41d0026a0784a20124084007808104c50041d210300d900000310f08405280d0721500c1d0000100030340b00e400e8044840d680d40c241451241c2054104a030384240c0c44604000303054410a2903908035010210701148500c0600b0050407a02c103030b00c0010b003140e8140b01d18 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 935484154 1250 935482904 935482909
    0x50d03030b13020f03011508092a0a09090b010e010b0d0e0304050a060c1a0106050301030615080106290f0405011b0b07030e0d030b101b050f01091e20 66
    0x10558040507882042d91110b803040c2c85001c25401c00d002d00d2403000c01c8444040315540c0b0500791030b40207101c06005400d01c52141c5000b201290507111100c80074010102c3c00801c4be0f1101ca03032010040144440005031850545020710103000113038018009401c030b0700018441810544121102580d103114001945881420110300318011580041d5000c400a400000c1d6907401c20f100c0c0560a1242003c0e11240d40880d0144403d424280640400500144010700026400b9409111001108903aa0494540c0d6500341800e40700b40350800802502c5200020301d51a1120183c0054914030403501418002d6010718441e41c0e0259115031030400410b4981032601d4600515000000ca030401c001582516212002030060b2840e803072411001c1c401c0351a42c6900c50721038485d00b0b50000c070041c218896110080f1085403400188042c10880301c001d100940000307542001140c500701c068500100380c0310741508100300f0303000b200d002200c45407441e0f41100b0005400c1940c1d100903600f03070b00031548902c00035070301 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 935485404 1250 935484154 935484169
    0x1823030a0201082e0932010603021602120d020c0307030506040f081e0913230a02090a091505030607020a061a030d03060e0a02071a07031e0609050709050d03030b 71
    0x550b0101024220130101d00e01100350003030010b00e81e000d99171b9420f1120204213204000301c0c881041c80004280001030000030301c00e03002070600780e4500c0c4400d8100c0b8003d8000600c1407407a03540040c002e0b0b0001c807403817a00c0764040c003004171491802c03405001010f146494250f145c801c01000206100100e628a400f048600c4c1c0965402c00c000312049208000e005180302215440300b030320342d4030851150103402032000a5000d1141c06200c100d103038080b40c80a54809040799400074000a121540900a0502ca030312800f950400501500c003010907900714440610140c00703015003101b40240c00000070800400d4001612980345503000b0400207142c80c02640c580c3d104a001840942e041c0103003215100344a9241d002002540e9411070081306545400c40c0c500100c0c8140342000340044007507500d840310071071030320402c071ba0140e0070341030110381071102510882403807100101c0c5490f059a5541c2c20300c28a049481400d500420504103683e182d410240000ca816144c0700300101055114902d550142e115074a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 935486654 1250 935485404 935485471
    0x30812061518030c0901060e04050a27020a090209031b010504030f05030d150609061d06041811120a15050909030a022104151823030a020108 62
    0x321210780b0341e01d8000010700c07500c0070025014070900c1003a0001103245406815281205c0441d281c0a803145500310601c0094070000b0041105c07160788001181c01d4001c0c1900c0348202d200070040340400d8100034410400d41c00c0035900191072180c414030a80c020758400003403008440240d1011488403c00b4800101d0b0944125007004040e45039030b041031020800004094881c845000009218560710380760102170005c114400c0300d0004802010401a490098488004030312810b24800d4161540001188459020b9170016900c45c21a41010404404a01c107400440300012441480d10100d026010401840a00320728005540c0798100c102d150620000e820050102134807404062502d03052103901c80c2c2285907007102500030f0b8213040301c1029501c0b010007080c07040f1406c580e0401d4201018501d4080620540c0c809001a010038544005044903402005010348010307030004102d056042c0601c004c0250f0780c18080d0340b10508910040c0c1e0400c3c5050740c00031080c2e418000c0c170142c06500132103058084c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 935487904 1250 935486654 935486689
    0x19081b09131e02030405010e2a01050f0c0d1403010806010501110a0203010e030a091d01030b040519050309040b03030a0c060509100504060f0b010f0f0e21060402010e060403081206 79
    0x421189a1641c94000d5482107000e000200840b0842400e05a00e0361275201a19000da20480d403003198040c164414400d00c0034061429506140c4800d1044165a026614401d03a0b90710442140000d90b0340201c0700b542d01c841000721039066502d0041011354410060080c60306000d101c3c00305541043e002c002803112150001d0081c0070104000c0c1d0303407036101d034480b4041c44000380e0a00710103d070450318020342d0603150403d402404d150b81c0c80c40d2140c10f2503c002420843e518003c0c01c40500a001c0ca002402e1035260064002c0c0d075840441c10b0800c01120020000c89009403c24010760b0101501305241c62040c50b00100045030a55511000d01d062500450090300d03010710b820140010b20020f948152800d20040c40d0420604003607800640e050f150f04802d44002514014003411124810700c0c401e00d071079101030700d90a8034804549805070f015107080b0032003601da4415010002550f90200d02c1005420095801500d8642542c84842c070510450a016150a40481c0800c1d0241c6802c81000740002c0007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 935489154 1250 935487904 935487941
    0x50c0604030807080907050d02060304020307080a0830040201390b06031227060f130b1903020304050a0206030c210c031602070b19081b0913 62
    0x40d00c1d000d0150802950301500040006000401403200000d0301029541e00501c0b42c0f20f00d004036401c010084e80014002ca070140150b01c1c0008001d002000107031103040c8980c890944990450410b5507445035401c7d00340704060f801c00345034141400c1c000396060300300c0d4082c078080f10703400035003550810540505090040c1c02c0204c0c1040c406250945c4071030300c8000d4400c6030404e12540b181f00806644581c44e548020030003104000c2c0354070344a070540c103c810602c0b508500811024a210018090b07421240f62001070368400294501c0c010416404403002d044440840b034100151145511600c102ca030404c0d80c103060f800804101031000c2081403100180e4000c112554034131f06006401c45076008601100c0740320f40c80007052542c550b9240031451281031013289960559a5203529002d94600e01803042c1d09602400401282400c4044010042c80694464100c003511440c039004080700802044410001561404049180c0a0030f00700c0d47d40c4801190a4420074034548e405100810021300590486220b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 935490404 1250 935489154 935489161
    0x70608130515130309080c030d180819021228080c0714031009080f0706090209040524040c170f031606230a0c2c10050a050d020703050c06 61
    0x8038800c010f040c400d54032404201ea58180841d0b98442582013160300d90401c104000105100720105090018a94002c1c400700da42c588100f401d11035980207008000e44200d90700425803c1a142c030584d00204213009280b0712540e19280008200d402103084c03544801142c0240c1880f1810081c1e916410030142613400881e80c1e41041c1124150903c0341901a00034480d420401c1c200701e00c100b007807003504030b1011490020900325450441d84001011240503030394100100c0541c45940409114a11a4000b051618002ca208111858055418000c050300e51810000003800c0701201d04100c499400d904100900b034105c03843c2c00c150b1a442207804e984404035808240b04c0803286c1da211032a0181c441042a009a200fa804071002510140c011096500e00402c000c203107260700074110038a1034a0b04a650004c00781c00801e040700b1080c0c00384480c680700c00e03411400345854010303010b0480e82803c15514001e507242c0c0c003404c68020308074428244c503408900301082c035020b00d00712150b0640e0342e8280e441070b10303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 935491654 1250 935490404 935490421
    0x50903090a1403060702030c0703080d090b0709140f030a3504032001020a0210021e0a02030606060901080a050429100906080705041d1f0c02070608130515 68
    0x6400b403500d030310034414100894041030000c000c88089140900c003030803441d1b095445140300e540c007511b06036019507a07034001ca10110b12003203a450b001c0e000726903414900b1440c2c00d0b40d0300f015220460b5014821003600c070036202960780004684400b594882008140b0000d80010300130091080031025142d40b4140c103644141d20b801c603000b4410740740300e060224101442852401c500c2151200c0c40e501513400500204050b180842c42c40b050211303d0710494055040101c41e02c85407008603030401c03c40c4e92141040004500d020300c611703a40201c0a641c00b03070801102c0070000b01036034809043c5545880e907400114092218054a804a5450003540d2024411884000700c102d00003c131414002e1105d00603011a00a1603030180504464080c401408002d0074142000014010500d481c00804031301c09105583c00300600a1340301240800340311004095520024000380e07815a0300703070300440d00000001d110982d004100242c00c4006001c0020102d602850300034600300314009080001e20000e001c101c03507034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 935492904 1250 935491654 935491679
    0x7020307150207150f0c050f0d09030605010b1e0a030e161e0f06030c0e030d03050709120b0a0506130f0501051003091208060102070b0703020703060b09090a06050903090a 75
    0x80c1425821100516500c2510100f88404569540002400c000071740a0300c910905540c2c190a004005403050003c00c003080c1481e24038508100c8000c260185070400500c0058071480b401070034031a9000e4075000340f188006407088042902c0030350420011030402901c3d4825800004070424070022101140e4128042404003011480780c1c00f1262518810407101d41d2080080004a8611985e5014041e081100650181543e0712040041080c4110000801d40e000c02401c0700100184d200004ca50604074001401e102980c0c02c400c00340703030700e4448400020341074444483e4820102c40c4005101d84518000070605000c0000720b9280606100f0741c00760b1a5502d1380040e04079002141e5100c101801c542050301520000b1130090b00707010300700c0c944214141c080c0b400140d0082d014410340e14400d480b072900009507003003c40240c0041e4400101130080040c540324000002404403580d0b041450705007a52940c483c5210001440e00362640045541200c3c00c1060f248203000c0100102c554544841548416 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 935494154 1250 935492904 935492939
    0x1d01061115131103390603040605010f1a0a05030a0f14060102060a09080919080304030501060503430f03050606031c08040b060a030c060806150406020c090c07020307 73
    0x50f681d0300e864003500d00000c00c01c1394460300e0160100c21480000360702d080d80392104039040700c4003000c00c1d460007030384e1324140198840c41c4194800182c550404810001c5d0741543d03000b040d05003046601035080b1059080590b01700444500e011507803a0340d69071030030019000f6040d03a482041d0815840443c0b00c2e4440001a2141d4000ea084890360f035540007240040d102c114a020304250410461100c00381802c8120005100d613a035084640241d0b6064140d00d56070007640700340d038140d55800060100d840e060080d18002d010415a0800d4a8080203501c4e642104c00480c500882d40c03418904480510780e003180c28014175010740e00c2841142d490411540300e0604403040c0348640100315200e2003503080c0d0381d160b401c0804582d441e11040d80e100d9558a82d5010301034031a60307100328a01c0e00000020502c1135110080c00c86652a600e41d4186041840001058004038084244c010311090220a42c00104005111000c072600401c5e5119142c0e8a4403512550790044e401d07001d800c102240c8480b01d902002c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 935495404 1250 935494154 935494163
    0x709050604061e0f0516020d2f010216170c042904090507060c03140712080612100c030f0906141317090402161b1d0106111513 56
    0xf00d4590080444516800502070b0300845c2080c0820b11252107038150300100d0034400f50039800e08080c95210845143d0040e400b030a0b0382c03504100b2010444031845903a00101d4001e0004209000d02060340d08421090380c007032140150b46504a00030b00d400308120745241900d015104110420341301c507282141c0050150850711051506106010130304107482450702c0c440d0454058142c5506003181152081c992180c16010021045104a0540104001480c6e034610600c07519101141004028040100c0280350b0f51290188880d4040d24000c0803c10500841d1181d100040044c0c2100e01a00180b0f101c0b00b0542c003207858055108200803056000380744600420000881550310303c0c1c1e40d000c1c004180e81d001800702d00b80605065114146201501503524000e101504051751a070584080400c2e4038825618503580c1e4119100702c824005800001d41030b01d022149042c6030304a00c1001420040c41076808000303800c910047c0101c07086c0204846031841481d03001060410301c1d40c1200030360078008282c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 935496654 1250 935495404 935495447
    0x203150106032004050a0902031e0c19170a05100803041401020f070311060f0403210e190314150a1a091620150a0f05010e010e070905060406 62
    0x1030315483c2010f580c102d440040004c0b1401d82020074040107904045e00e118852101c18840d00c44901130b03220301e24410001510400e80740d800000c1d51901c0040300c2d8490a040c00041d940c490003040d2450019580700e01203c0c3c000c59192585c0040c00d941000c40d07400b400c898007001c42c2c0422041a54020458029826402c4800300f03201304102e035450314031030700c001800003400d4040d130219414040050003003d0071146003c2d040030350b286c89001404807803415814051040b1082050455000f8500081e5084240c3e01100ca60400001d10304840e03405000c00ba11382102e882141c4030010f000c00100c9540d10040c14098998200401150003402041191031545100c2c1700d1100164202074030024414451000c0361900c41c04e03810030a03101d600c516030090910100e090503411a44504012507109403141c4000381843c2d10b402c0440204841c22103603606181c9027000010802d030050015114192003002000203810707102e000c000d030744681c200d602094200a0115000400716000051011008007441804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 935497904 1250 935496654 935496701
    0xd090510020c010501080d1b0b07050706091203240515071e03090b071703092a1201111e04030b040f150b06031b07060f1b0201060b0a0c020315010603 66
    0x40d15a0a6232410b0442d060890a4030840030407501400a038100c2c0031401d0443c901034040d05c5500940f03590610582e420b00d408000700070b001d6814482c1c00c500451004042c032041011059001883c0507900c210381c491201580203e446c03c4482041312941e80d0f0240c03500441c0510790400c1705c0a010842826000301c2d07816000011040c1d41401250f004a40c0503007101c20000d040904140740740c10142542c1018461405880c801030480300a0500320611070f40e0610300c0c0c0a03a00704010652040700134046103641800300e0b0710484e0503000c2c10b1300e140c052608840e50140e825015044054000c5520213090b0328112000d12041c0034100050007440d078080d0b40c114190040e03010244041d180a54442c6404c040100300090114201400c80421004d046110790305e0f0151503144c1100b03a80b021b48a42c07074429914050280d141c0d00c42d610308800800d007800288152450041094010b01400201c03d0601020100310380031581e0034814031002c240b41c0d5905014550715600c2c010014204075a95066084100040c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 935499154 1250 935497904 935497907
    0x100602060c09014505060c030f03131b03031e0c0b0601021f0203060109060906020a021e090406050711150103061a03030c0c030105060d03050d090510020c010501080d 73
    0x116124440c0301100c1480c1408000045075004050712541c18070302105082c0f00c401040a07810001c40c80e040400ea200c001da07020310588400640d5502c6144114020040c4550b03207d004001e440c3d2032000700150700d8980d40d46d4020300b00a0280d100c801000c2c410150300e1030254140010705102034074002d59442d0b01c1d01181c0410782c0c0300301a001010340c010640c507250342000941040030142d80032506205990b46440c59210b0014002d80080d40d6000250300801042019640005079a00410051410070885894a81c0194a6088035400a40104800a04003c0296030700c0400009000003130328425851615042c0385c0001c00041d02c400001030001007105001c544001410400c1c01c120355022049a4a19a1001300418007018402c406400542070640c1568051001d0004181c0110241403118103040801d821103200070314841c800e007507002d2441c001c00d41c0102550302c502c0d00c00301d002400c0da00600300743c6e103440d8803404020760084c00000e965200d5172040d0400da0403504840b00303c80300d42002050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 935500404 1250 935499154 935499163
    0x7060545030c0f030415090e0f07020c270a05010605030a050403030204030b1f0e0903092106090709151202040b130204090f0b06030903070f1a070c120f0e040f1d06100602 75
    0x765244d0140008007042580b0071000c02250000ae29004075429680c103c40481d41c400da015170003541c00400b8115007107a640309080c10f140c2c40404400104002d42c14424007415a000c00f030902060305940d000043e003014000d5045501964010a42405a00d0540801d80901d507022803032081070340540c1000240c4c902004007084c040c000a2001e54108080700d81402885440318011550081c0c00591310720029500780110350082e620b01014000060820406100355001f030001307541f54002080081080d1844c5103000d00386203078100c5000c10a09403a40012f032490f420307240340184081c8001000a400c100345ea09c0022141c10241007400580d01100400c0001c1c001182c02c403080707030010004e5400003800c1c028400c001500c11501e460710300c0c0c5003004007400d520081b203113600841c011a030030b00b050180e0300e58402c82c1c90f0101c1c64103000c0a140400010002c102c40d01815000e00e440d44255644142d0315084110b600e8000903501050046e400c0c0c80580d264400d586035806a518004003052a42c800314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 935501654 1250 935500404 935500409
    0x7140f07061407031202070506220512091807050c0c01170408031b0412020901170a1502040e0a06060e150711120307060545030c0f03041509 62
    0x1150100c4007a0311004409080d806000c0c11420001a4080207903100c176144041d0010320b0240008082c81e00d40503a41c1c1b043c07003840368030244404244000d80700001e50b00045d010b031806003442c1c0700741d240c02d490030104108083c2085d030002c2100c80501017115181d031000c0600042d1480c0021691500e10000054603203c942043d03406c2240420400240861000c400658003c0b1800703017401441c0d100c00b2945201504180c1003407441c0680c611007030096103040c0905a0142c447ca12050070300d5003420707801981d1484410b00c014525006051300b0400c80d242d66055030000e000c0c2c503442030594900400e031035004203a14050000802d12030b9099183c02c0c00c10001403071728494124615440d008154490807044d0f14458074080d4003852041803100e48a5007030000d0f0100310f100b03102c0400c4505009004030070341d505a0148031002044080c1a0101d0710a0204810f0354410a80001c4000c20f40c04d030520b0b00350300c1242c00003c03d92240100058403548000b00034401c03074203040d9040340e20301150f0714126020794051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 935502904 1250 935501654 935501657
    0x2010e061303020c040b062502090604050c030402090403030e010e03090301050f070f0c051204061106250315030209010b0c011a010918060e09010911100f0c140307140f0706 76
    0x41e0018130329040960007046030304c0e002003c1a0a01800c031190705c00070703070301e103114001000b9440c0030325400c608144152a4104408540610040c43d00c031039031081c64000140080c2c45480780d00080b03400e06010b58014003081590b44000d101442d644d0158035600d61004e03004600075840c240002e0b0380c510740c0560180c01041c181d40c5118108041e420700b207500340d641107019502402040c0100b15026803d40c002e000804c519151200e81038180c104050070404000c01c00404003e4442042013015124019648407500354280000d00b0000d03121003684244c46a00001c0d0000c2d4044008986041d00318050008038106100034840c44110f00b13210b40f06c2c0b038800c5444038082443c9a00070302095003451a42c1550404c00070000800703556a8100341d8103000c05a0f180341c0035965450110382030100c9008044101e200549014024408413003006206454030403201c010441400c182404004005841ea407600b13000314200c0e91103d8060038981603500d20305602510901c10164030760301d040c4c2c000c01c1810444805 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 935504154 1250 935502904 935502913
    0x40506090705071a151002060f01061110090615060c03020a02131803030c0e030303010506030c03070210020c030d0e0a050607230f0304170f0901030f0b040c02010e06130302 76
    0x200341d01960290001c0e0b400b01e6403040130071307202c24102144098403846905d04000342c5990804900a20500d080302c418074a08540022003004105c00d80e00301da26046401030310341644010b190607141824000703050185458181000d0f4000e0074803040b90005d0031082024400e08491651b01d6106036152045d0a5006001d40c00a0089001524001018600c4801000c0002ca1402c00c1001c50018500e12a00124082603036038030a401420361014046280c940d00360b00441c40d550500f00003d42d980070040c0000b42a400010000c0c61851003803000d1036080759206006d40d01e43e40e9a40016483c1d80003103140400107454280d014082007400a40c0c850410f400030060041da440350041201c4050903820758082c4412080120710b10f00413524002d01040c2e201c400d016450341464a0903480003010030344024940ca0007403007000400c840d00d40464145000900380085c01d5101c484600010708040c1c510b503580f162808841501c2c00d40c064010691a200d500706603900b80e51440344462121a200c013000c2c006038030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 935505404 1250 935504154 935504161
    0x9010905061c18140f07090c050f13031203020316030203041e05190c080d02070503070611100608030306090601020d05040614130b0a02070f032d150b0f04050609 71
    0x10b0503072100500b08103445194002034a1610790707021300040c11400b042d190b440b0038508448050280301e240d019041c1510144042d44070480018140d010f800540c800e82640000c1011002c0050000c0b10015503000d1001020304444110181c02900300b01c0d40703108416034069001514512034401c5a01c40c0e87d000140310000c00766039402c1d240146e50b072001120b56105059606000107030030b110381680c4510908400600f58107040c10281421084503088081d035201000a118a0b41d000c910341d0140c541c1403170884e044002d07000d0392070301d03042541d165008400e00d011400314141e100840118450300040d120201c00341c039850300490b41e443c0910b200c10001502413000b802014461104170b076100e4a20700040d803c2c00c00e0811541000d90a503801007001d280006001c20059405001c110018080b0314440140945503031a80451000820344410f00b4000303a002030b0040504c401104044560442c0016400b031500d610780d00c0c000c0100325071a034821504a482e89050b803500f4000c035486000086d2040f0080e84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 935506654 1250 935505404 935505457
    0x301060f020d08041e0204021b0c1c0b0a0f0504060e15010f1401090b03180f070501080c0f0c07030b0a180c06080402011119030f020607140a030e120901090506 70
    0x305805442840c1044030b0303171440c000da59280040c0c040d42500381400c880d22044d8490780e609e00702014850700e0055219040303900614450043c0c1040741c0f908902070008564514060350010700790400001c22081c500002d1001303008103a803001e04120751070000c8580341c02e15615070044041d002d210308607509410312428040d03d545001d0800748018181854558a81c8403c01b036034640d0030880c0d81c0030302403034006940c0222031001c21800070100e003010701604e142c034100320008121038001009041304c3e0000103410022903401c48116009800030000356204c0f29181c0c90030081180058840189260030100c144040d007000200f88071089503c980d2450030103280c0074007a0b40c9040010000c1e4180521205860301c620002d001d11448440c005c128410f559919140141c00500301e141e056007154407540802a071150400d038040800074600003c0f681700c0e03181d5032044010f0040300d14200d4140c000e01c003510b10800729a90280c01c0021090b2182c83c0c102e501e5400348402d41c02a1a012a101d20122aa100086 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 935507904 1250 935506654 935506673
    0x915170a050f0106260a0207050c01050c0c1c02060a03060e07022e06031a0a0c0806030c150904060602030c010f020a05120a0b0d050d0314091b1809030301060f020d0804 74
    0x56204511301700000e81c00d041c4010f500c2c02c08075005040f4030f40016054041203818490740a04c40001d0074024202044940c18a03034a80c6c800e105540520312014034001150118051041c00c50390003065266a072030510310013005000103105050441000b0707808039056500125131480131803050207000c07000000152110010700407078903100300c031156510808030108a00550f0001c20390031800c480f002e50f0411300d10b54022203240e20200401c10803110305004041d034002c5489000e602c41200c1c85c0302c50480201007440b00d4842c6101d2150700600e031010004040d50040068a00111414002c0002c0074000250400341d00c0750314000b80000e00e041100842d05c1030070400032a04450f10b032000040c4460004040740c001228180103480652016040c04801a40740c0681700c0b80201922004406041c10740752140e6682000d44174451120304045500b14648a62003103450685412604481600b402800305842e80c0c028005c480005007408507690246000140300034041c5400c1e41d44074400e6449894403141d8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 935509154 1250 935507904 935507927
    0x6050609012d020304060228060519050703060e01050d020d12120c091401140f07080c07090c02101109090a1d06100f0e04080a0915170a050f0106 64
    0x41c400d907002031109180344002c0701e08000072900103581d00c1d400d004d8007130301c1c01c82c0c4085d24100c42d510322104000d44d491260407081c032480d8401d2010403a034450440082c214299003040e8000b50b45050204441e44c0c0d4950885d008860202ca0000b8090741c9032030620032003800348900030350007580c43c680000c001588001e0700002034810b850140300da0001c01103007400380c451240d000c0000480f0a001880000c03540c0121a20106c000d08262600f50721044c04000c00e07000d0045c0031074000030045418014040c4003c01c807000c4001034000e60705181d0300c0b01d01e01030045c103125998000500c1200b880b46420b00561103590140d103c48403009040c01c0703140e0100103415070010100c032561030300c41505400e01c48824902200342d0025101a021a14100d00c1e1407250b207145500a1000720b28010f4204280c0e800800500e4109400030000e41e51498003400540380101140e201800e94480d40504000c2d05601c8046e42562150001c0850400e88964040780f09840c02903540d101d500000000412046020f50402e111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 935510404 1250 935509154 935509187
    0xe0d120608011b0c1a010905010e07020f120c0304182703020304050d021503100e0604090c0e10050607110102061806370501030c060c080a030e0a020a090209030c040605060901 77
    0xd88481750600110000c00b81d10031960a5241e2006008800b10000c09561106072840203050040004c010580d07100c113040041081d0000010700c40303a40403003c2c4200d6024000351141e81100c40c0c611185040113044405000c140100c0f42c3c042c5200e0550040d210107240d503010350080d4142420300c1c00b04141030149000490740034031310282c0d654000c403090340910b100e000080b600c1e44a1a241806650040000901c41031207a46006001400210b21001d0b60054034408401102c1960320b03021110a80039079504400e611120104680b81044111000c41a00007401c2c0d0958803191034840c0f54401240f800c0d581e032913158020380c00140d0224824a03101041908483c405514004403290f441446410085940000c680307410050041c0210021038100408051a2040040720b90f512560100d02590541404041e1640c1710380f1050781c8204042680f40e45c0040186200d150f480100b24000d50254412502901413000b4042c02481e00d4480c5d10100e610142c0503d00d80140e08d0011a20701442c03190000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 935511654 1250 935510404 935510423
    0x61e0f06020703241803021b01080601120f0209120a050c0a030b0c22060207260c09090a0203122a0705060a030204030515040311030a02031c0e0d120608011b0c 70
    0x11745840b0600706031541d58025005004130041868182224520358606581800714020130b020040e40d004210490720130400c24000390440b03415945070064442e111856a2100511802140b0340c203002c103d0407407141c499011076400070020000d110300c01005d4400506603a8200000541e1007915100801c0541100c4e0341515403484041c801a10761030351a08400010b91121505000d01c0e000d505c081203810031402100030182c00c0c0c902c1020340c0c40030807481c01d5014140c8038012484030b207000c00401400907401030503100b040548c52030f803c165400011842c0760348014107180380740c0300910019005038100380802800b1018102418005260320880e0740344101740c2c0c20400000422401c4c441198400349074000c5502c9801e00c2c3c03d006150700040b03000f40040e034004000d4440c0d03c54001003101c0d03a454800c8201c8203064101109540100a0341c59002072500403118155040b590204036101e4004900380100304440c1c465919500302c078581c0500301c0041c2015141401403500441c0d882007500d10529068 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 935512904 1250 935511654 935511671
    0x311030327040b060304050d0309050f0d050d0615020d030c0c020a031208100e010e04080c15060109080a030203070f05031306030f0b1e090a061e0f0602070324 70
    0x10085584080760344041545018030070b1070700d80200501d0240440c2e415003141403680303d603911601039404420615035210f100d00c003000000c7c40290140181c51003a545845480c5401410a500500034110b05034540640803e01349100d008000c0002c1e025401001e20703001042c0103070001c0440c1440201071107616805a001030303440c2610030000d14415a642e00c4030400c024000303404410098080907024407100001e2140c0301d456440340381124602004100162103d0404203070503c285041d240c00e80c010181c40200e00403070359024600800c02039a588080e9941c800e45036840d19100c02006005810070045040802c661461000f80a03004000756443e11214240f0038042d20820391000e00031a44071050720388004090700c5800e0303500c271003a50071191000503a18442c00401010741594800e444850104c0c042d8961030344440d01512006103e03520b4031030404514004c04900d44980391b844c0d0760b4002c020400510200d80c04080300d0f8043d0030040781c803450346e43c3d100c260501c030110a0320055079801803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 935514154 1250 935512904 935512927
    0x3050918040b0f090c1e04050604020301080a061a1e0f061c1a04060602060a0f02130303180305010e0705031209030606100e10050702100e130209011404080d2703110303 74
    0x100c000750203003000c8204c90301c001b00600060720001004548598418001000401c40c00729090444590080c0002807948980e42d0003031400400c60101504408210aa0503003140314002c00c0440c94410ae90114040303207281c04000c42882103804914000145044141c1400426000390415802010800341040001400316048461580c030550043c0e200c2014803c03250314500c250000c0c00b032060f80941ca08040d50307820010152042c480102046480c0d40100c144c00301c13452600340950391003c000e201521400c5802641c44e1004e000c0c0610901407042c00c1e80c04001c24604031009104091302804c419501c1008100b48000d11107000c1c01400180c06100403190f41c3c0b501c1c8401104040d40b00c054541d080d600601c02e8480e200c0c5000018004041005051599905002018000c002601603a82e20040004807000d0307040a114541d101d2003c0b4000c0790003c40461404205440d60340c13005204200d001c80c404858002c003143c01d0700729038400c20620214403c503100c0519100c0160480c0c2c079142c2150034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 935515404 1250 935514154 935514169
    0xa050a0f0519230f220b061017010807060210181e05030a0507061a0108040b1008010204180e0607051218030a031a1009050405040f0f03050918040b0f090c 68
    0x200701401c6000c0104210f803480d50082c208000301c101c6003502070340b402d007076440f5011180040c20852080c0c065108040d4001e09c40c81c03102c2e03050084010700f01115659151003a07510021801844098012402c80740202241442040300c660000b012042d901181a140e011024a1040303040d0894034011032400080365040000701001c0c2503560300c06946071903504100d421151480804d01d405102a00140710aa900c020b102d5000760700305206540030b80f609d468000a01003580d01c50074165001150000d02c40110280c40c195850702030000380614101807200503210101215000041041442800d8044500321020f42e805001d591014141c1d0710500035076455a082030400f10700185d206d2444981d00f81c11101c1000041d803059802c5140c601046030003403e501d40d18043c1034000d66a13000001c0511886200b0800c880e40c00a206141810482c107000701700f5441003002034010303018054000c6443c406110194815600218a03490316150310b00c0300544031070043d0200e0114440c00c107904030240e69441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 935516654 1250 935515404 935515411
    0x809030f15010b030f070807020c0d030801090510030203070618091410080c0d0303020c0102300903040b0a0507030c020a12060b03010218090c04030b0a050a0f051923 73
    0xa008200c0340c0074803a90701c06240c0050b000b1503030702e070414414010150b040c1028190018030a081148065440341422441c050300401040c1d84070000c1d000d03140500d41c00c030b900c8034140d80c03441c4810310140d5520250012982001d00c0002c1d010340c00311004010051060300d03840d604909201c4040800c99450b4000380a80e411481d2246458050000340300f41c0428000f8941c0003414800e005d003038018854030000d55036056146016090540010b00140b001c20b003907040300d014030800040b0301e080d800542036040d41c0b4100c040401d845000c1d48008251900400801d9508403545040c2c000d281c0520b6940850303294100d8001201401184424900141e44581d05007003d00800c0d203154085601500304441a13071220702007280282d20400c920203070030200c1c0340040c4d017420040e50030030016110725203440858802da038006040254548207005040700c8540010b4000e03996031405008480807203450000300c0c0c1c002c1d2440c0303007140ca0004519a141c040c40d08a8000301d0f0042e40c0c00c54000b108003a1a400300d48044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 935517904 1250 935516654 935516683
    0x2040b070b06010f08040209131403040605030103050d050910030209030c131e060b041a0d0513060c02012a0c05060a0905060903070c09021b0a05010606031125080903 73
    0x70100140c5591000c20780300344006914061003541400d03000700c0d21403c800303030006840010302007503e014003440c000340b503a81074a000100c0c2d5a6903602c4400400c0c40c0c200380402c80d22070103140b41c042134031480b13003055030081c0e0380082009189440000040d4001e501030150681c050060341d10282460380e80c006141c1c6c00070090b10002c900c0c000c0c0110320151499022020300841c905e490b0080c4914042101034800380c2e000d204102d41600d55145e801c40190284510460006041c00100b1480c8601410b5201d01144211010b100c6004050400d030709a5054552072010304201c2c0c00c19898046150403140d01078152810300092201f140d40307803241050390460b1120042501e801050042000411499520600000c05582042e61980e00e15201c3c54061207920005a0085400c52b4040701d1811000340010048045401100403482e00b680608a540b1600011a16245002c0508038a182c1100c007610490b200464101c40810002c0668440c400c02c01d451500051101c60b040d07483c10402250480c401c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 935519154 1250 935517904 935517923
    0x1090306090609170a08010b030a091b03020907030c21240503070501090605070f170a0810051009091a09011e08012a020f03270604050f100302040b07 66
    0x1c0b818050b0003140780074100316a83d03400b0400001699070000300c132415940d191441d09d6807503d40b104030714043c0c600c0080c054094141c89050402c0e400d51940c5442c01c691003a40c1c8a486d640d00c2d81016421201165000d00c040342e171540144110502498040c43d00b00261040060070b203103035440940f000c0b6580c02d8102d030918001401070009141c1080304000416092902600981c00c1800003010740c002e00100070030420000d0100f00c20052450040d402c00c4405a2910ba00c491800400902080c42610083c00b00164001301040710708015011881d14209030300d916100c1032408041000412501203109060054840d0b10049643d40900450080400d01d00308000404da2807014039441d0503e41c003030829603241521525000b055007a07080c00c203079003c2000c104295510b40061341005600300001c200b0740000100d06100464029003103c001030500303003903501c5103821403d00c04076100b1030107900da1103600000c802040f41350407840c000c01a002480c0c05414181d81d8040c4501c1074002003c2181c01c640c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 935520404 1250 935519154 935519171
    0x9073029130c0801110703081008061302010f031109130f09030908120315060f090301090308010906050d0507090c2a02090609040b010510030e0a050f06060123030402010903060906 79
    0x900380c1011001d031140b6002040005c40071248504688074100004062014401c00114132454600901d0010704c03003082550700700c1c03034454203000b0480c5101e81c0c2203000c621840e61001e290340c4a48941c403010307400c030702d8082c0c0303003218600402403208d81403051800d5503030311030019a84840c1a030040f0b408203440fa0325100300703442c00c04424900703104480021030401c00c014001c2080807160301282510788031066031000da90b4102408400040c0c440e9011583d003640c20b2030aa5400c00d41c0c4610418102c40c0500400c0044940f45c0c0200010b401000d00301610a91202c642070203980c04ca54031400d200030711424440510440c40f4403280c424004883c18504241000c80100300b0740c101556825402036080340c0c84070340d03440e040d07a4160540206001d001e002d040c05c240c0200f50a80039602c034082d0710a54804490f10030896140090741c9060a40050140c1d008034400314140394014000c8008100303002140410242244408461a8100810607810008001800400b14015110b007064a9000d07500c0442d4802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 935521654 1250 935520404 935520413
    0x18091a0307080d05040911040803121503070e240a27060501050a03090203031312150905060a11131d0714040303080a09020303030907302913 62
    0x30640d010007056000000300e0121150700104071170a99615100006280038a0100040386003d9500019000d01c000200c0c0c0b0011586401c4052003516010000c88191041c40c0915442e05406d1207001106400e80000c654a5002000c050090b00424140280941c0c45640003908d803112039480207a448000084407000304088141a10f080f031448241801224a403100003016407244211042c20140e0303034840c0004540d414411582c0c04941d2003522000c080c0c0714034035100043c09600c82250b030600801458000c542e10f40c00b42216564101001e818169107400048002c3c2c5010b00380c3e011415010002c8d00780040c0c03c200b001d0003500a45041829150320719a942140000140000050060313880301202007600b0b040880707041d81c1d8549406080780e00c850440720301400d10044025818000881000f91034000018007070215400410042080907036041e10340d0502290b00ca424820b0742c4642002c402141015500007138525019a0004880416031050841c05400351000020302c7e6003184580c0610 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 935522904 1250 935521654 935521663
    0x1c0518120a0e010305010e01090c1101062c06060313060204090c09170703021e0402040b0708130f0308040303050306190e010518271207060209090c07021018091a03 72
    0xb0542820108115410803c480c4482041441010078154842a02e50811031084100309920388085d4000e20945840e5100d035000000e200d41c00300c1080d91008c101010203403d141d074150050201500c070354a9a2a41c0c4d65043e141341c0a00000d07286e6a800f00030000d01d42c0740a1241c45441d141c03d41e00c4128403400c0640d100d070000c08a40703540c19a5413040e4000d0000d079465074a8552141c2802101824003034011020402900455001c00345118010030080c081c450080020071135500d80210400c000e90702e031502140468003d01011300000018001071001038090001540c00180040924607400d451001d40c5101191319044009a181010700421a40c20400c540500c226049102115649410150340741d00c50343c041d90340120703040c1070540030b5500d0005003c400566505920032a030749541d03d00b0890003a44c0043c8481b4000e1a901c0c0002b488154188180c481659000b00380b0000d0381c65003001100e00258101521280442c4d40000280040c6584118003400740e02c0c0d2007040a00c9489001c06050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 935524154 1250 935522904 935522927
    0x6010804020f0105030603011d0312100f18090b041103070b0f0915040e0709180e0a0f11040f0501080c031c080702030d0203090c04060801021c0518120a 67
    0x50101100600c00180c0d900141d82d07000072020b180c8180c9a5a8190000b405840703411158403548440802404100c00f01100910500850030544041c42e12280c030304c00c01d11503080c428100030f0144070300140301c0804484003030124281a42c0c40800c0b03e00040c0c85001e001803040e50101d5031f40d800704c80780c2041d03800c0c2070000d0f800400b0310705a0981401124100c4081c14894600c45d03e2244084011600210f601401510042e0903801a912040c0c50000400780c0310003103500400b40ac02c40c185207205040c0416000380c2d003480c00c040025002c011040e03603980310b01100301c07032084030700405600c13644c0ba1503221031084083d02012568082100d51410b00e80b07900304450507000031300a400070b03254101c00007507448003a9001807592800001c99502c4010803400c60062121014100d03000205003e5411070020b0800c00c0300e20125000c1040b15600c000c41803c03031007843c40c060f5a0002202d865134058120354091a0f20500000030812482c19822159040c0300000c820036441d03200114050040b01c0d44051065070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 935525404 1250 935524154 935524157
    0x8070c05061908010b0922090501140a1a0a18090204021602011202030603031b12161a040b19090203060907061103030103020d0f0f02030f0d02150c0a0e0a150503010504050601 77
    0xc0c165008022440300e070701880700841e0142040e070158000407c25070202d151142c20400030404d01901c0162680f03c0c070310a4841e1503520313007450480c0c0c0380c030489000242c60165000300306000c001e00e403030b01d06a007510101d40c5c3c01c24415915290000544c849000400800c0a080c00380c2d688080e251002501c1340c109a40c030042028414070400c440c4d0f48001045403c00d07542496075400b1146480c400c030b8903001600c050b009020074080740380d4081c2006444031106a5118044450002880050111a141e000c07107001d45144214004507003011788030300e0106900344030080040788030461500030a1030407405a8450541d40d00c001001c11489910404c8000340001c03802c0654519491500000d1516450840190a90b43d00003902d10130803d080d40c051101c0b40d4041d0a51b150b105202c0b81e07054032035507004403590241c068500c1411004000140c60f0340b082085843c3c4508200300114100d0f180560800c445800030950880451802c00d03904501c1015451039851a40e250b0404081c001a1000a4416130 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 935526654 1250 935525404 935525407
    0xa021006030c0b090307090218010807030e0606010e06070203070e27030a0311090d060902090604021317030c03030903030709060c030c2d0302101406030a08070c05061908010b 77
    0x400103a891000c02c00310741941c0700560700c8134481d034002818807169901000c111840054030b2980310740000406a1101e509889042a0380e503012803d9094480d04489c0b900c25802880000d222136000b54038902d0701140c060003103810303e540d503070200b440c000c240d8001d070100c0201d4100b004890641c40c0da21032107004160a07044070300a03c007290242e0700c0c0a10442d00043c0341d204c84025608aa050041c0c60f9103010040502503d082c090900000070448150140d021b4100c0200091403410700f8000c80f45440d88040541010914106041100e0700c02d5440e150244d0000700700101c403020003000654000d110b44c0028558a0030410406032126119910010600c24030702c0c0c5400c04260098040280d040e0081040e5000c1032032401c000342444040e140174900d0000340c1c40031405065000908240074803001400b04002c4880d0680703004040d42c12642c0542c154080480b850025401030082c0145c82d10580c00c00c844203031120b000400c5a04000540190191203c0e0740201c129403180c1414010001851402e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 935527904 1250 935526654 935526659
    0x9120102045414040203070501080903091c0c031410140c0307030603140706090e040c05010c2d1506140d0302190b01030c0e070f03051f0b0a021006 65
    0x4001c0c81d0b010b1034203505901810905541500d10740044050020703040d0b007040003081d035410504404101c059405174084d01c41c07610007145550040c1e584501503036084004509041c2010208402c50280d0702601d10110400a00ca034005541e00b02444090741c840c04003240c10002c00c0009034501000464a04035141c2402500a104000f100100d508500d40301c2030329030b0326a10781d0015406000e150b800101848880340b810102020081600c005a80d000d640e0000c0e8079540d900c0350640d115050b200035101018401041103150b0260101d0b81109104d200390f15919180c8a108403401c1072182400100c1c8244045c516040140300b02e41c0105c00c1c881c001c0c080142c40d003400c134220100304020070441d0041540136060010306008012a240c1d010742c010b034101c5070384054030301038050305401e1004440c019100400421091000c2d41c1240c8150546e60300c0740a5a805100d0032805050042d0040000c1803241281a0351450300004500141c100146071a036900702404000780b030007500039040c03142546009010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 935529154 1250 935527904 935527979
    0x516080c150f01061b02030607020106050a0b0c0312061305070e010806120a110103020f0408100b0102071a13120308190902060904021b0313061812021002030912010204 74
    0x514152580c51808510a464000301440403800c0043c5c040d42c18481c1d00108948564150018416114103440c00c60944d41d60382d01c050607074090b00030010016082070017080640c2280502241c0d200d180140048030114512100108544080d500c034000158210000c0705c695070040d0145810a40030b86405824154030081152070b100790b6040107003581401450304c0545e81c0f003034054802c01e0405101081c0d0300c5030b8904d465551010b80e40b1007000c105040c00c0c0117000079070010800c6000c1b5002d074072020200ca0301075031248010707600001103105101d0900d00d011030b203c60807038150310501d40b1a03255062681801c090b00741a840f41c8482031b00c501802c180382c5000580b2a00140c802016090703501503101c081500d280010410030307002c00404d520010030320600710b8000c068100c04607006070701d4400326010f81c03520000f84d03504d49020b09036000001d00c40580040c1400100d0318440f05051058a0400030b81c3d10000300c0500104601c10b032141c0d000b1600b481403280e0780700b4280007a038850303000758845600c0542c13 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 935530404 1250 935529154 935529181
    0xc1a04050a17071d0f0a1e050105030c040c170c040b04080d0e04050709050d050c19060f05090d080706090204111e071a07020127051b1e010516080c15 66
    0x48000c90300c1e143d0380400d52541903a0028480c1d41803440f03500080c501d01f09844001040c00b44291840f9200b0340070700117920f0400c0d2243c0c040f082c070603170b882d4200e003480013500a861003c00f502955071640304000c00240d03070050b14081c1002e046c209018211001160398010221451101180d200d185008113110510b6041a0043c1c201d81088d2a0350210014a04195003414031001c1b0440e0440380c0d100110640c02d2040841d1800e80b00d0700d4554004200110030202c4003030090040003604642c1c40b548003800301d81c08001030a0003070320589001c140c10384941d001c0340540f400c000b680c8626010100760850070321440040c01146c0c8a005200c541440038980310344020249041444100318805008249100d1007904000070501401e580110840c014016090300f085607410291040d001d1091024400074084201c08800321004140c48980c200304801d041900e03000c44156414003104111030800c1044225240003400c1c00ba1030b03c9070b166000d0740c0301c0c0c80c05d00c1509020302541c8070300d400c10032071021010f84 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 935531654 1250 935530404 935530411
    0x6050a090b0d0813081002090a030312240906290c0a0611090f030c01020a030503070e09040f0605161b15090b04110d0c1a04050a17071d 60
    0x1000481c1072820a00441c1c2019141d030302c06042c1050004610080240b01c144481c2101d2200c4100d914030880394205c0c100300d0003503114541d4040340060301000801d1182200300451a0000c1c40083c050001d0701d002c00036640100d25020b40044010410000c00e80a071080710014280500440344884800e001410b014503402c2440b10042030219074440403c90400c96408140c0d800a0100044905050000750541000114900c80c4803040741507411402c001c101d4900007101a002400390803a541c0e01520640c20042400342040060729500500ba5290341400e8002c502584076210380111600308a415280700502800300702038030340b1106200c6540030720100500c40c03d00100500d85e0800e85001c0d242907480080c034845503800c1c1010a014003185c1010140501e20032449540380c600d450b0244110101c14503409012441d00a00400140c807074940207001c04003451480a150a441d1720001c0c1007080590442c901183d0f40546800000204010361000b5196201c03010340040584050218030b200e008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 935532904 1250 935531654 935531669
    0x40b0c010212040609020906040603031b03030b041112011703030c0d11070303050a0506030105090a0209101707180504020f011b02092a0703020a14192406050a 70
    0x24820400200030740c1980d00080008103041c0c2d503801c05080c500040c00d00020140d21540e000800b081091a1510420040780d5040e02c402140c0c260f0341046856000f0011381c01d5050580350603001401e030b6142d11811241070b60240c200d503150321a071a85150445016007000508031001184924501c0c000802d880d8401012041745645d1424055240d0181c1865015000b1202d0041010400c145e01034128030711440c03080c4ca040165644071010142604c40c243ca0780a203d030440c00d095009800c1c1520440da11440840825000c5a030381c0d001401d11003050481152550007519040c0040e004500d0061081d0340020414011800c00350000b417694041c0003a081c1c144880c0e10074104075000c004140404064005010007001d01c1d091000300211198848001c032541002e4034000a42e4480784107551450b41c250303008211099450755400c44021441d540c000072031117002d802c2507241c4c141604454890303100361000907400c402d0400841e0341c0c42c1030304c0300d44158504122040c000b545a004002c000c49404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 935534154 1250 935532904 935532907
    0x80c0405071e1e08010503011514240703020d08090d090b0304031206140a060207030b06040b01020f0f1506010507050d0e0a240f090b03010b091201090b070f090803040b 74
    0x144a0594600804442000441c1000480610f8442d001100141280d40c00d50003480710812882c08004c2400042c0203207150003007040a0300070325050100010b0140401020305001d5009106940740081c5c0024404a006034030142018640e6944456000c1d045007850000b49400700c00c8a8002e00b4403011800b50301400c00c4080000b90074184030b80d050002100c4c01c50030800803d5140c4c01403c61041d2500a924050404500002030882c030009200044a07000304039a440e80c1c58000400000e0450f5101c550304500c1000c842603024081440918031241c070440090203500411003590800c000c1c000c00807030521505006690200b00b02284070011601145001e8444503001d0000400704440e5400a0b5aa146104c01040c0d0060701e103082074845040d1502c2e10800d080c10b5020440c4c2400b40c40c00350341000074080c00104564600310018115813040140600342e00142c0050030303800c44803e080165600c2e0f2400041c000c81d550440c8016500046d54074051245900b80b60056503284030724800c00200c03450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 935535404 1250 935534154 935534207
    0x1103040e0a0c031812030c020c0108130503070c090e10021207080402150a0203031f050d03030e0a0b15010e19140604050303070c08010605030a1e1109010906080c040507 74
    0x484e61050300c40c0c001001d105404030b10241804404054001582e0010901c0e103c031480126000040e2801699030503510701e0315650b91106640c3c00d00300c600c03a045495100034031503d4005541d9500501c098028603a000514000042c01a40380440c0032450520032441009030701c0c00340a020004907840590b50030308104d540c98900c041aa030000342c03070b0170101d142c8001c1a204801c81d4080010760240091800b00c030050b8508500f0000103500500c546940060501803c100084c00b94110300c2d004026001038854040098640c2c0e4580c0e10115210001c800d64541203411540e0020300100c0c400380c0c10342d0156034482055021042a0000e40200e50300c4602c140e62804280d41e5190444000c4c04014050382d07101d09003071410b14000300c0d140c0154003181d42440750215042c1000a0507100454000c110b80054607403808a902c0000c449400c00d66120251041e58050740e192001894004c00d56000005a8145440c6c622400c00d03056030310551140b4101070600c05000d510000b03008000e101300f10709910b80b12 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 935536654 1250 935535404 935535407
    0x5012703020c040c0509270c0a080136180305070b1302060409022d040e0106140f03061c03180e0c070b18010c0905121c050f130806071103040e0a0c 65
    0x110003a40071202087e2210402510300a12406004111031079160381c0401d988542c9400ba6515426071800c10311000e80c40e110000304124120480c07038020030b200028100d900c201054034040e840707250a0b07000c1400010748a0411800181d080e40c400c030000c00b004688001540007407068401c51091480c074940218842207607a0f03040c01400c2c00303506400c2c10711100500070031036100c80f604544180e01e090320b02000000745a600800002c01a42c0710f0a1010380b40c880b0666224405400c0600040d40295010f50b94424944502d08100f02d0300e07000740c842c6038140882014008020005411064484120009002d8600c4103581a40d20303c0d5402900704d02d10b030b0307a0a0b208070340950658401e03150700c1d8280120300c1c1d80703250800030200548000b91030903000203d13226020760b990f03880d80034107903032141c02a01c8010754588508098109040907000451420390000238850603406035401c00c2c401c54002d1401d201d038050f0400881081040840702071400c0c02d1400c1c908200488d001481101c1480c0c4035151030056a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 935537904 1250 935536654 935536699
    0x906060a031b050303040f05030f1b04051017061f14130b13140a020703050901110c131a0406030f08070309030605070203030601020f0105090a0f05012703020c040c0509 74
    0xf0700b4040d080303940351a61840d5203510611a4844c50780079024201c41d00c0400e0801240c20760742040749540c107888000000e010300004107401080e40d411260310342400304910740c1b0851480303210aa82002000380e410f00c5036190103010008030b0b040802a08904e0108115011400072403001c2100325143d04c4800100841e1001602c514414141d1062810b8403501141c906a44043c0301071054100c407010076030b22030300e40d80c0880c0708480d00a0301050f0280469011980f20f00e61001d03110312000151140341800401081500e500025030a500584888801d0006110907801041401e4122001d2082030300d10b8070b811080101124021b00910340000c0c1000034107000304003900c000c55114008010501d41603d000303460343c1080d540c5d6401409145009000c00c0700501070b2034002c0c500311000e408488215a40e0051040c60310300d00301d4079952503111155000001281d4140080086084c0921055203032400a0512030a00082031041d072030200c0c0d45980c00e41c084103441020000350307002c40034245018907410340c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 935539154 1250 935537904 935537909
    0x70510270b07050a11010311030f090c040203131a0c0406050a091509030b07031a0f04180b0106090e01080c0405130203010603080901110105010503120a0c0b0108070501080906060a031b 81
    0x74524006a004100440041c0c81030019010b4000c5502804101004405460b6030b14512112640140b01040b2000003440e0341d81d80185410703085a00350000070000c20b0070ba8004845800000f0401d0072020b0a10042080f0041c1f90094449500202c3ca0039808403130744c0780950b0107603004000e000326498000e14085c20168001e02041e44410b8042c80c12240003c00b91070b450700044542c10003070380200300c0e110f001e8000da405080300c20901b007014980c8141800341410724000c000e80c1c49501c2c0d00c01c40c46240c2120b07a0708a051801340341440c440c1d42c106103016100741c4403a8002d1000004900c010041c0d0034000c681c0b1805400211004a0141c40c0c000c14a0f002501081700a50300d9443c00400000704a802402004c600c1070070381300c03904c19221007500305003241c40910407260540c0044210f0700b04262020020a800304407401c3c94048400740f910341c414495400d8204800c01d510013a014480744d03821428565100f00c1d40f00080001d803500310046007203480c061100400009440c81518031010800160001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 935540404 1250 935539154 935539169
    0xc0304170409060f05010c0f110d150606091211010c03120e06101d0c0706061502010e011d0d080a0e012d06030b01140a03020a030305070507051027 65
    0x846a880c0e20003500100707241e11491a07a10a1a0702c002aa940601d1707c0484c07050b00001c4a03440b10320b1a03215800140481a68180d008060014890002d64502010074115540100000740e050400c1c10280010000d0b0300610710410a40c5d81000001e40245900350340d142081ca4442540340740c034502520b005800007001e881507400c2c42e8404030030b2080018511303c0b40f421402609030150395144820341c480b808498041034041507200055403066207034020842184070700e000150369030361804c2d68010007106103200300060b5100c565083c0c0402d002d01500d020310700640c4002c603002c81c00403d180d03a0f400c0d2003001203051001c004005808455903038024410b400704403009000144c07018181d03c1070705080241e00601200b84280d240108182c0388184070035260320403d080c200781d0815070f0304654410300011240d0300032190440440140c94113551840112b01c0b94035800d8482000345009420040703150802030007a9032a0400c0d1000580c07201d5442d28124000880e48070f00c0c5101c6110240c01d40150f04402c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 935541654 1250 935540404 935540407
    0x609090a0b0103060e071416080712121b030c1119020a0806070e1309050a030504180506010f1805030a080901080c030f0105150904111803150c030417 66
    0x3084681001c04a00400d076820810583c540304140ca00d032000341c1d40301c00040d4010080c000c001c0742100051500400c000c42c2094080069518040c4590100c0b0040f201031001148505141c0e41004070700380c040040400038840d0340717503416105c84001c81002150080540314510404214025020b003a001c110300000e5603e0b011109040c2c4a6031401a035040740542d0780e0907400240014045210750080141d41d80c4e042d09045030748100103424108207146402c103541c8095040010720100002a5014440e0700c80680f41e0f8501a02e042c02030142c43c14a20045080c00100681c0b0303070b84030900e145805800d051201d012540007080c2800c2d0140d039003029800d840340800d2801400100340241c00e20003426a940f010503607414507103020324001035890035080a048001440b241ca0a44541e00311000c03e02c15413406c1008c2c1d000040c0070303150480540802c2d600f0000b24090030841561510341d0704101500188080010508121115840180403545890012010074104000d044400350000c1d0441c40b0716 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 935542904 1250 935541654 935541661
    0x7020a0f020f09161223090709060806370c050915030f0702030c19080c0102130906120c0314070e090609160302030d030c030f0f020c01061d0114060909 67
    0x2c0030090504d451040401d103040b120350600070890041c1203902c52241854800908140c01d030a400040c0030304007900d00d001c1d40c04040760600d0f22307208480003080820010031003030505000c429220403070058840400d41180205414070036010810700c40032401a6400142d000746401c0480310760080b44400e0740d100c03407a00000312402d81a030015600034010010f002d41e2644403c501640e0304d10600c400d601442e0049028a402a000345c0d01e21007c0c50700400e41c0600e0300114049440c00c90b8007079041010341106031981408100308604c140c0703000d4070081040c1006010680c0300e10015203a6440000d2210702e1301d40c840052070ac0c06200c1c440040c240321490b2b00e03540c2010b000140c0c44400c126202c1401c0d00c100b0001007400603210031030f0821660050042c1404600303100d800c401130520502c5420916844454910b81019184501c0c1c0319412060740040c1c076242900d2919003500c0466001c800700803801380c0b02252014100300154111600342140c03200c14860000030800c04d000e25003080380d00c520042c040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 935544154 1250 935542904 935542921
    0x50c10050a0c0806031009050c0d0f1202032a01020d09050a1a0601090302010f0c23060c030106080106110a060624020a0b06060702040b030a1407060807020a0f020f09 73
    0x40c0103001c0300c0020b0140c900e102d401140c80d924200d441035071682c08030700e07485c0b01e000a80e400009164000e0741070b0348142201c50041509102c0c1c0030000c5400012041ea5001401014240c00d41400800e20117145420100345500c184210521451007014901044840c0c06034425170481d62180001002070168803501c1c2042e6885840790b000541d0368620700500c10703002641c0007440c1840746005031180303010b403401c40d001150303014018410071040c008501c5494010070408601010181c20711066142c0b4101594209414914082c00503440c0c10310501c010b001c1582c201c50b449041d9202d9180692a00404031006860406a00000f4280070716102d404654041800441c0c07510002140030100c407109081c01c02c9170345200c5000003401070790034100418001c0c0744c904002c03c1c00b540018004901103000b00300182c108810007104641c201e90322000b00ca0000c40910032900140307668102105c8510b803400001e501c039603111000402d0125040c051070115a1602c200c0902c4501c0a86031000c2441d08110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 935545404 1250 935544154 935544161
    0x6030a0b0f151c020f0409090f0c09050a0b0f1e060403061a100216031416090c0306300311030a020d03061a0405040f0b0315010e0f011d07050c10 64
    0xa01402004201808410043c214021a0359948841da0030f240782502d441410b10040400d4103084681101e58030741038002c103030b81030390013030140402403030014030303401c111458104491580c00024001c0188035540119551030742030080030482e0710b4071400200c000900025421388115007000b000585010300c0046800319090006040d044c040e907121015482000e403daa07540300c8c0d03d840e01750380040d08100b400040c52080301c0740c002210729400c49507404201828100101855000741040c00d03911082490215410b0058400900c600800c0e4141c001c0885007644c05046011004009100b0034500312040521511080c40d14403160341c01c2c0c036240d000c03403000207444084000281000a0901030003048403c0601191001360800d100760768502444c21040c13102800308015003542c10b642d2854040340e07540302400001c0c901910089200d41540c108104d1a5507003902812483c042030900006100c0103090505008041d2000008007180c0d690301c0300700b19201d104003c440020750003a80e608100c6901d6540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 935546654 1250 935545404 935545417
    0x10c080703110c06390a031206050907020d080c040e0c031f21080408062a0301121103120c010905010b03010b0307030314070803130201020d0c0206030a0b0f15 70
    0x1090b00c03c1c4294610800c0464001c40341c0a180405c0e00c0d1541180300428501110041e2582081d900f1884a031018800e06000300034000342c001c2800180103e0850481c0e1040102515088410004904200800a44d076880d4082d000b800d100d40d240128465111a909807070003040b90440034030551901202402003500b0a0362000c4c0928505508080c41111001005090b203040c47d801c060b45505005050200603503859090314107400400010520381c0d400d011080c452460701e80d010b112200454480d0043d000580800440c0410510041c00f0283d04650b06076886a002a480c1822880f048002410291600d5400c1b443c1e0400242d02102c0000640240d000c46026100800c5098152000d1600742c031052100d480d07254000c1d400500009000e900081c903908800f6411504015499030b612401d070303009880090703900c1c0c1441c2ca104110740e81007016509101052a01c0c8401006c41c2c1e011802c0741c04081d1225450640b2a9041146516035540d4070568607002002584107140c0044210099800007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 935547904 1250 935546654 935546687
    0x9090818010206150607080d05270109020a03060f0b09010314010f0b030a020603071b0501090b01290307051c0609061e0612091b0503061008070b09010c080703 70
    0x116503080039800072810074896001595194000da140e0420030120f907001d8039048441c1c4000303008001c500900da00c40d00d44201d1020200b180c02e14070504040d10b40480316807912610382e060420020061311028040c0b802c8030b502100c0440d1603c049034024018000d800c40710750b0002c2c980350001040c4441e21102a44070390358240208a0042d002c49510143c035040c1d01855019402ba02d0001c0041c1450300046a203c0154680f24100301c0e400f13020310031000301202054506a451b0358140301400081492740d401010ba0070150380c8401c4004812201c040a10310001c0e0701c1000200004810502841c211450140c0744001441180408103001c401000a40a8400030626021011407808036262002114514440310001580c3c41e16104a82e448240070302001d40f20703281e216140000e9550091004003400301e42e008086103044c141418a440c0000301303040750b41d0703d85d08810460541c0c00b2510a0942c2e120941981d0b80e030880c1001a0348a003c11312004182c030500165000c10307d5400742c1c005442842c007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 935549154 1250 935547904 935547937
    0x10c030509011401050d140d0c03120605130f021621080402010c150b0907050a030b040218010530040308010b12060103051803040b0c160e0708040c090908 68
    0x1241c403060b00720baa40660300d0341d18201c504018852403030044a074206951140141003140f400040c90241040c03200000300020440401c0d4210030590401885070500540342d6003003040d51b28090020b03407a101000d400d030110944d107842c20000c041940e012504420f092152404a620407450240c0c9240000122011148241204000311034400e4902e5405250140d440124190341a2104d44581c10070070201d1210365600d01401c9442c4c0c513207001c2c40748900c43c40d490b05600c2d082401e1010301130303900d490802446148101301e600411800d008080c2c0402c0401c0c45c010b074640c0e1603025400010700e0f0443d08000403402e03031200040841d640d44400c9108922959900e919a41c4c3c40200045600610038044610700242c00003030219403107940b0450707201c0c14079504407060120388402c1c1c13410b65210703800c0301c0c100c0c0328001000e071080907041003c40d8030380340038040b0305039041d00c0c00342c8541100601400c050200542c0740040f03020b0051101901000c0c0c0481c840401035003100c1d14103080f00d0790003a00c4c0c41c9554003d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 935550404 1250 935549154 935549161
    0x9060615031803020c060310120b0403200601092003010305070512150c0706140907060207051f200f060a060902070507031106120a09211b140a05010c0305 68
    0x4070b440002d076125896002081e801d4015020450740341c1004202c0380780003020010005011104d003030080e0019000d4100c0700705908250030010030701c00039444070003040301d4607400c0c40f404481d00150042c1111402003000a001622074000d8020444c0c0b82d11312042c80c100440007105002011995504440080b43d0202c2040308045044d500e495200303d0507440c00f92000d0000d001d0900d04401010140d02c6602c002900b1038001d50000002c06003a80e40d0341156200d528180b1180da01081403c003c0e1034100c4946460280b801c03051804424282e1146c0c0800065012081920f180034154003c08440036041e144c0e45001261001e82d62102201c40c001c5041c02c10100203402c03199407084600083e0000c0c082d000f00c40c00c0d51283c40102d00e00e02c540a812030001c000800c4242850202c15016440c0e048000c038001481f401d00b140c05450881c3e9444c11245134070315072489640c001d902003605d081d00c20784060f213400b81410301d0b030b04d5000c5508841c20349020380c1141104010341984150501d21440d10304001c20748 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 935551654 1250 935550404 935550431
    0x5120312101d0c09010e01050705031201080c012a03020a0b04031706060408030a0e060f040305030304051c090306150e0c0c0615010c06020d0204030503070c090b0f0a030212010906061503 82
    0xd400e90780d424010b00108802c5a055101d030141d03d6200e0010304049203054027664505245601040d11002a200c080d401400300110501c030138121070300c003460f2841c01d003901c8040010042c20849070920245444220313107004c15000340914900d03190013903040380c5075151605020b0580c84400c5100c203c02583d4000080742480d0034400d030b50650b5026402503082c4000600c0990f0684005250968810001d000e0450203c43d23000041010314880c03030165849061038a0802e190110000d00c2c8145041c10000079108030384c1c00a20942166080807000c940d40103413440c4030750244196005510555140d00c00c11040b401c100c001008680700b202c0440d503869032400d40d880200703803180503184e0014046000410204043d07401410f803529034090018503150396a03681c00d280d580404021100e000c1600e41c1040200b045114043d21410b05850041442140b040083c216255a000091242c0211482103126900075400b03070400e20740c00710b020019103440d6481da040580403030068100203401c00107105c6560 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 935552904 1250 935551654 935551709
    0x110a081003080901081b130302191d0c0c0a060603021008010620010213080c030d03020306031914010c0915023d0204030602030a0b12070512031210 65
    0x165048000d20b8101003641004407640c540c007810310042981b00e1009000701e16541002003020401481079408094a180f051154025961a4846003661401001c22840c5400300b0305480130500110242c0c03865840c02e000f49030501504030004000d10561010108006440e4070010a4038000c50b400c103c410411041110700703400c2401070360006001c41580c00c3c20340403e60340b14910300c240040013606101410501c05140c3c41c607503106645036030291181711603c0c01c081c00001c1c80001c09141c190b2440c40c2101c0403d556000012840000100600702c2900b40b00c1200c1e0305c10038600c8898000e01040112071401000141d950081100c030041b0742c010107001c1400000c0018011415a120340c1280d19030107550343d428141052809000c1a00c1903018514000030f10050010b940b05100041c1c80c0e00f8442c04800843d00343e00007081c000e06401d60b200000b06030024110048400803640024201125841e0134114011100c41c0d60ba4601c91006000700641100707111401d542c81c1242c28103181c03104442e0b80241 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 935554154 1250 935552904 935552909
    0x9020a150302090928020c0a050f071d01080309100905040f050405010f0b030703060b011403070f02100b0f28240f0f0503060a03171c0203160e030a0204110a0810 71
    0x780c4041041048017110241c001d00240484242600c1081c10180c4401d03090038207881c8034000700c1d0007000090282c05044001009500200f2450300c02c0d0398105100b4595a10441504600c41c0299000002d1003600c03a44c4000c0107400003800c10703c0f405441c0a1008040c00017940d046442d5402c003507920031500041e03c20100c40810090041802926544800000b81803810b110360400440d6540040d06018400065000d202103942d12910304145e014024140203104580383c8200781010a00f030303015603d03c026142c484500710307400c0b0031907003400e130304c3c1c070b403554141150704085440c54003000801040c00403488265100c002181700441c0c0f03c01038101d441c3c4844800c1c0c0e038007007018048003240d610b20a602856200401800b05080da6840c5d48816294850742c00482da201d42001444c4002445804805007580e039928a0550860800ba40d0100c140c600340c00400e020050340780080c0d0020f6a08121030341c0051307000b40c07080101013114440d45070558007114601c0c2c040341c80080030920384180038400700d04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 935555404 1250 935554154 935554201
    0x41e0b07061a010e1518040c110610030f0b0604060801180c0518010303211b020d0c15090203010f0c020c151e090d0c060216090b0d0609020a1503020909 67
    0x817007000c0c0074030440c40d40051811070300d801c0c00e1400d0001540c8940c4202c40d410030241d210060030141d1425414a03200008081e24078814501c1001c00c0098000303100040c0103940030b41d180440369a16008100144400da010a50030741c00e201c2c507042034100460042d9601402140d9072100d00d0303202c50600407900c03080805a19940200c10041021900c10441c8854904c0094240001c030013121a101d4140e03800701c2a9101d503403880700d010340d81058040140c0c06c40344000c2d0034130520761070207502e82402038107409040301d41c0da07500d961144045680a5100131030101c0b030b401082100254042d4001d5640804c800d00d2405403010341034808031800100140d035841040301503681e00d811a5003081383e945810a4a100b504035a0b4001d111000404001012024140540c020001c0d0351041c01e0211451002d94040c51005241c481b61680c10f444000041c0340c1d1580010b0701144034244d0348046404100160700c0004480300c84d05442071081d502da0000c240c024021600c41d02952902c4101281025103042403d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 935556654 1250 935555404 935555419
    0x14090402030a020f031e06101e05150702030616030e03120a020904140a1406040e0a0b0c1908010807150516020f040204030312060603050c041e0b07061a010e 69
    0x400525203070501426030301300502a50b0010310403045c03410000884030318046468010404000078415510200b1000740719141803845020f03003440380380310b030034050b800744a024076181c07580504100004011500200d50140440e6001c2c40c0c20030001c1d0080c500241160000390a003112114008400801d0790010b801200c014601500d40710480f0300254800140e041d041511507034201e2100e1805040e451050390303c1c94000c2216109400a04007240d402000381c0e00c500e00d00802440544400501d03483c0d51a0b114100d41c1e1142c945072214041e81c002c20190b8000940222940996268030840e914101c450b044200c5100540790040041c5901130324600c0c1b07000840500c107514034412402c80c01441d4500141400c0e15120042000c04c05980c4550025400300300030884c4911100654403c4200a2203e49800c00c5141480c90400011744182d2091049642c192242d020443c43d00c04240b400404a9121065440481d480c000015000703142102400e01420b5400099550003601c0160611600a2545 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 935557904 1250 935556654 935556673
    0x30d020d030b0307170c0405010501110a2613180903052a030313020108010b040e0609041a07121410170c09130c080a0201080f041115041409040203 65
    0x118010954040e000340c0c148981100050341c5c02c055030300d1102e2001450041d05004d170b0350340140010390b5410f034070641c10464089001c03003d4100c080303a884403180e40189000031020000c90003103443c0d41d00d803442d40c820308000200c23400480b1b030300c840140480d03016900f809220592000c11000300c46040c030028011640170020348951491701084641c41111105410302005201d003a00ca05d0740e08200c44d08243c111403492000c0a568003c140c00740109818240546405e003402c007020000e860140449024a80110200b010421402c14462921940341000c00b070614010f84020076200003200c05521591070900086484040b00c0044c5100b01060281da800300c40ca00708100103031418140f00d0781c1450149505070342003981c51000c0e040c02600443c41d54447c141840c100403c001e40e143d0320034a003d601c0840e5500060360441c13500343d44a0034050b80102c85039030380e003000030152001404440c2d100c1c09406403140d080c9080307c080c100703070780620002c2c0303542c8041c1d101400521041038501a605074800d1420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 935559154 1250 935557904 935557907
    0x160303240f300212100222080c0d1e050601061d01140307052701110a030e09040807151b02010923120703030f05160c060522050303040b06030d020d 65
    0x1624491840900440080d03810002c3c0035045ca0000400488042d800184586010748003241741e4100c01145074407034460318540751540d5501c1f0315840d1260f00408690404106002d0310036109070300980c010503039551000e070b5032078070503107409090142001050400b410b101800d080004440d58460060310b441107101c1d45a061900141c00c001c000c223042007020000792006d003180c00b40460800c00d04015514074807000c200050040036040100d0380881d4084244500400d920040301e251109084d0790181941d191420048a0342c0b20303011024042c1404940c0a425882081d8000483d0440c05030701e107200c8000c7d62108a090b29a60348010344582c24514074040300f0b102d85200c1104514001c41100c8216058000302001c903000110240c011030b50b108130300c00c0005c0083c0a42d9038801c0108280c807480031680740001c0c0645030950707005000180e031b540000c0c101524510014001300c02c646400c110f00300461600e690b0369030084030304030f0345601410049001c608002500303080700101c03900a08003103020280e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 935560404 1250 935559154 935559239
    0x3091905180a0b06070b062107330536040b061b030a140412030f0311030a0209130c02330a14060f0105160303240f 51
    0x40303007010303d07035600e4450710a507120382c0108101d51088420210610b4040c04001920b1003004c229583c014041035850030b07403900400d91038144d85071041007030a030038080d05121410203a550a02030b01a100303a04c402e0082c94100c4041c0c100d00e061050303130480700391620450520007014045012101100744a805480d841c00d40c008540302c082c0607041500b0541d5403001e52400e80561848440715400014540407895400480445880c0718040e40c0c9240c1071804007815421900d580d000f40070007840c0b80c08106000e200c0d030007217805140c03d905011740ba0f0821400d208029807111201070b1189694202c0c12003040305030b004411940000d50041e1003403008016050418400000003601901e5030b021040420f00004050039024103000e03240042c1e00e083c2008501004100070f07200500c18000d6071502e881c0d83ea400f00484001c0405420318805014051406401410020311060f039110005001c0401035105903558808036006882d1503a2119035482d20401c260f01010381801650f44104055103210340442c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 935561654 1250 935560404 935560411
    0x18090207141b030c1c05060106030b01020d0309020f01050a02011e0b100c0b06120304090606050318060412180e0a0c17040309032301020703020a050d020d02070905070e030d020309190518 82
    0xe200317000701d000c0e540e456007440e44c242c00603030120f9540c8e21402c0865034100000c2c200c14100e400c01300000c03483d03074001a007560744107078446041000c00608601094400e400115403031a5407450403c40480040d025006007000d8089180039218800b880c00301c0c0781c412448520803a4001422410316103c0c04140641c40c410f5508807a01c0c0d00c010040020b40042512482005140d196a0700d038880c141041414158500c0034641d0109030320034028040420500c605652858040c0d0524040b50b110440d130251340070a240e4400242c0c80104801c100500c11260001c41030541140d8540c00c0c03118282603241160349068030098001030031240c0900004604000c01d441001120101d903848070001c10380142079078860300c003c90041e04075140711420044200300700886e08105001806060006100c0296a40c480b031155449030350700c1e0b0003c5a9068012250001000009800ea800402421001940d01e5006945160250b0001c0e146c041d40310784600e11440c1511001014600c0a000483c2c40c0706110001070f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 935562904 1250 935561654 935561689
    0xd23010c0813050f0a06020301030c0e01081b04060f120501060b0c060109020d110403030e03071422060b04060807020d2d022b1409030c0118090207141b030c 69
    0x44134059000c075410460024160b21a40d03000da603d604526190104040d03981c410601e0b40000d00062151074408203010b00d0f03404410000010001c002c20008019240030343c000c420074030b00100301040d80d5819407a07984856000f54001c0c403840340c0e2110b00e0485c0f442080802d1010f500a800148081e01c2c25030002e100560304280040317116195241000c44980c842d038000c9002c5022030013801c1da14201404514001c1032480d030301c5000e034480c0801041c600c20000d0300d009050a0b2156002441c3c0c103050384180c000d04820815035403959290340d4060813400080d2039200151080702094030f607003072044c455615101000071110312081d402000b600b003520003d0890b142980034000503080050f00c0380f0300717401c10840042103000c440e0072141c0000d4610080340c070280c582c41c00c0812941045407070019010394481030070300e00340c110381d0351b01c00160001d52103540100e01c280c0d00015000c010b00015921040c6070394082410f45003034400342105015a461800308072909034020500f0ec40f042e02e00303101c0c1c0c0303888003408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 935564154 1250 935562904 935562913
    0x30103050c010c062a1b080f0903010f020304050a0b130807080c030d0c03240302060430052d1b010201020913060e06060301080a060209010e0d23010c081305 69
    0x180d40805040450600c1c1c0701e00176039030138610070501a60184d020100b8132100031407030340b2051154858007100d100740b000401c0000c80004c4c4075161502e003580a4541c1030f0001ca011501c0b8201858105d49841010b00c055a1400254000c24880810300c80c03035019003640054031515204081c4d8814000d9040110000014001030188500154450090300320860b031940d4000740c904401c889024003a1f045004180d02c40708030b40018001030f01d076138088405968500350128000e40d0020000003011600f440d031060821460342111741040340006501c280c4803d8404040e045009a0b420b5040129007000910300d241e20100b0505d0307980b841d20141500b88241880007500d0001800701042c4481c125a00d480f10440e0360f09410030070f08804c0712000c6e8104404a40031461549400901551114103941c05841e20340d0000b09984540c1c029121040764100c0503040418164042c105100402807103501b035502e0281210302c40580600c10720034486180020344a0b0045a02c4080401c25405034165048516104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 935565404 1250 935564154 935564171
    0x160e1512040f0605011a030109111303030e0a061e080411030a0f050d0804050a060510180b0306090105160c1703042001020309090f1f060905030c06030103050c010c06 73
    0x142920030a100302e00071680001c0054580c54040216041640f0041d589030102c48045401d80000d8102ca0440d1044200810080300d81c003000e40c100e01c00c0440600704000c0ba4a400010103030819569416010100c51200000d0707620311090342c0e25481c4420101c4030a2a400320b0301d000c40d010b560072a070010300405c1b50b541c041d003040b00442d181c904600403c0d500750625000740d01c108a410845550490960b2030f01031006e003402c3d640c45a0390445050020328641e1990005426002405a0034000708244190034540460f0b404554004044282d11680280075031000201c05140501507940214015503940280c141541000c503a8050890700031107080c010070642400d1a042e12010707501039400f03400041503008a0301900c1d000d50000407443c905641050100b0540c40e598072a400368484449418610556500306405403075204640e00c64400a620b14004605594011508000d45406800719006d5800001c2040801c0c0030910000380254070521001c1d001e0351080900b00700c080c0c4904408151403c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 935566654 1250 935565404 935565427
    0x5060f070b1b22080c030c280906060e0f2101060909140d0206040f080f090301110a031103060a030204020705100614010816270815010e160e15 63
    0x18407680790034000300c4002c42d50303152504403e50075900802560006000a11003180801d45502d2061251407003080804400103106400407101074043c1900100f4100c1310f52640810401408280582e000050318540c3d80c90181c10039070040c5408030b000600380c04242002e110000b0301480f41c4e00c94082d45540f9400c00003400c42c2540510140140704e00c020403005980e003010300c0d15100c1c842001720215880721007440042002007140541081c2c10054250743e904044079503842900c545902c50f0f80540ca03210a40060034103901c0a04480c0301a41da05010040200014001600040d5506030740101d412900b04014509640145440c034807441c00d480b81c40c0c400003011000c45d88694020720220140e43c1c0e520702250b81c422401540444003800510401e040410001e040340d0035841c0102848540741c01c0b10003592042900080182185422983c00740b00c0da00d044100c4000a01c2517260300b1400001040c00c15076120b100d501401140e0313469803040440c010401c2822081411318002c1c1d0710040001d40d1703c94 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 935567904 1250 935566654 935566657
    0xc0204150315090611212e080c03010e0312070c02091311010302070b06010c05030d0c021507020d171314061f1a091f120605060f070b1b 60
    0xb0410040001c0d610039078200b00099039072200e0b030b00c000c101c13040046504a04184400c90540e910400303a40c1e0b640d5131a6802c15070403ca032084034408001c4080c0d41150071050030700c4801e003030740e09003800c0c0d5a401711000285400d940e034802444075990420310000784c11042070510542e0101c41c0303240c45210041641c0100361005400d4902d80624264049940f00303005080a44c41c0680b40c0a1a0840c030f0315045031281104500d01810076410010709038600405c0c880c4c00c2086c0c035810007500c442004405421400656a00d010108000e83d000c032400014100340d00108568181a61a484203030036810901410b281c0d03480024082c60040250400d00004900103c0072503c00c0ba1039100207100c1424665145007180c54580c1a010004146600500c5849180541a071211014080140d00ca04151001407400904200064240541c80c2050180140d01c00108201107465020400503242ca034002d0004c40d00c00c014954078580020000e02000680500d4541d80c8241f42d822080d1510000c2c1541c24100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 935569154 1250 935567904 935567933
    0x3011526390907080a0e01110f13050a0305030403080f25030e09060a091a090403092105030405060a02010e0d03020307090e090601030f0312050c03160f0c02041503 72
    0x501c034000c403200540c81005001d00428408891240e0149480c00d0014142030b802080410740c5078540700360f15100c0c1c0003500003030105d0002d140d01c152a03201640c14001c6581014100540f0320391310740c10029460411200b042c09598206d400380d89818150f407101d90f1158407021941014100030001010320400c1d81400c4170f4000c50701c040c203615003081381c140240a0a104078000307110740b0b8414180a40c83d174540040500700c030b00000020900300f80400e0300000041000c6c00e003d4009041000b08020154011100030541e042c140441312020524075032458407801c404001407560f402000203024525054016207000120382c800440d08078428004241040981203980d00400d401009200515810a10f408060039140681c0c1459181a003950b40e039620381071002505809240b140320381854803446070244800c01d614014021828100c001e03200c65441182c40e03c03142408088500540f03849001c0c03983c46110569076407682e481103a02007100a01458400388141d615400001000540d0740096541 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 935570404 1250 935569154 935569213
    0x1103270a120f030e01020306010215060a031505040b0106050c060106030b0a030203032a12090d03050906040e0f150f091f0e1f0b16050a2003011526 65
    0x421102c0d03a4405420f688030b10100f00c0c181d900500401c14641d81c0003685001c603d001ca030044c00c0c40d0311010049080c010701904054055000d52005480c002810b0304803901403481043c40d11502da036203d5003110300b402059800b01d043c4d04804010800da41c42600f104c0e4030484014070602101c1e58a0b40060b245034001103040c1d000041004808403c12840d1003142d00300b00c04c00300a06640190002191103600ca04080c41c2c1c403031200200d03000d00b403500c0344064400900c40501425900c03615403888481780710088480700e84079201640012220202d070000f00380140c070081c08200c124400c0004000000000a024640300b04214041c101c0700303d00741d203501c00100f94400c000c1c3c100b13003170201c81590414030480d148242c41d0089103042150401c208101c9000c5018144000c0d40e0485502e00f031341c10102c0188002d0000603244042d0703403220103000900000518201d000b000710701c00160100c80c4502c80f41c46901d0103440d041040c91100034405050049600c446000e070307020716101d8030020701401c0000f00b5800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 935571654 1250 935570404 935570417
    0x90c180b2d010f090308030c0706020a020f1002040e01060c05010e030310080c06210711060f01050f03011109130b12060108060f091e0a20041103270a12 67
    0x5040240e0140399075412400b840c0000700b00041107400b800321503a80c8001452180000009a248503565040d80e891580c03103501550313620050440295659614031401d00d060013454044a0110311500c202c0c1c0c212a01c92034280070790780c0707010300030f0321a4000711400f5101c55485c0e40d14888108010f000561088070034040c081c40d49800d01d082c50b0315180d0b081c0d03480f41c02402c080040050b01b42ca9080407400e40c1100400c05c2803d680d0741c40301120b0010608207030144c41d1081c142408148030300c80c004541aa10309451030340e15800000100750a03200348074440c042c1c00c00b00f0011248a4100303017695500e0161000c5001c248013140c01c011420008514900341000e401160040c03085000030301206070801044011011a818006545911580345580c0030488040380701405120712001c0c0203051049420050f803419451030480741c08003041c0e0000c600c0d40304a141c540f4006041c0e1206007600c2c02100c4402c940e1000c01d1300d4068031140546000ca00b504a849202d05060018503035900800683d0740036501c61 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 935572904 1250 935571654 935571709
    0x90501150503010e030315032b0813030f030b0f06030a02030f0c0406080c1b0f0703020f180f040204060314010b041401030201020d140d09080913090c180b 68
    0x100030600194002600c20f0341080540440d803100041940e411000c944910741c00f1160344400030346008004d003d0000800120190400000050407400102e050b460700ea0f42165524220b010301649030122005010906048114800d0b5100350b2083e14074030300180200500080500000381d132500122181f0818580010410400c2d070003020300c160700103210b07441c1242418144000a40350600080c0a51041c150120340c9010301410307950000e0b0303d0340360902910314040041103480c0e02d4110500050b4042d40e03080e4100c1c0101e0810a2045000c0c500f0151442481d4507420302000341c0002c0030708140c0c2e000362100804030100d0400c1088800744942da400010700030300300c4400e000c01d640d28007152541c030458840c0108003503600802d000c22002071918240c14030414407038072450700b03018000f050b0b5030740c40c81e1100f44000c0180d414000c0c803e0803000ca4203c0c5c20501400e5541050310340305a4018402c40084c5000c01030900c6803d01280f03c020000800f26480c403012000c907003903081c03540400310040900305a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 935574154 1250 935572904 935572931
    0x210216050717100902010215010305011401292107080a050f070507030513092f0306210309130501031101020714010c020f030604050f070b0301060c06020f0d090501 72
    0x400000301206904141402c0c841e450540d16500550394040d0300a880380d02c4901168030a003c030b0f441c103201d03000040c049540c60341445802000000e41610782046032200101f48441c40904610720b601550031030a4094649181480443d00f06816400e6090f42100e440e00a410400080320700c1a109991981c58620708510303800d0a0740c4000e0300400010074440d040c030842350350100031a061541c16040950b80d901c81d05801c4032011001740c1c403110078140342603035019240d40e0301e114010620455030900480241c5801d6078080910003a00c04580c0a0002448500c01e0700c1c8410f00020000a40000c0e2070a00d0381da14003003100803240c040d07504401543e9100500800c0040a80c15641000038402001070710704000b0a80540580504003605128401044170119a60000d101314480d42c054160741c01ca040c1458515a074081d0180c0140745401b0700718021442801841c1900e049654540c3c42405800c4a80c450100031740c022804048a0b01c8100314170803144d510390040414540c030842c0001a451102a071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 935575404 1250 935574154 935574163
    0x2c070306060e0633090d06060602030d1406030c090402150c160902030603060c1606021b012307180e13030801050f060702060f07021201021e0a080721021605 69
    0x4904808030305148280ca04441d800c10300781100040c5410709517491100c1d00004804001070a402810503080140c04245258040090080d035400480180f00803140d0704000d4901c0705040315615003650003800e42d25002e241000031980c100b0b002a101d5200e0460501e4000c1c469840381400c80c0c99030703000d1007000c013010040d0b803001c0300203000040c011030850400700d0009489840142010103902801b08803000d100601d800030400d050341c0510300b155950741e045031020004440c50030721401546840c407280c070402c0b180005000000c5d0780ca9406c1c0fa859817582030603038486008403400800c4402804000c900010404410350103074207101001c890425040c07030020700368030058022502a401c0c042100c1c0e25915000155214154100c82e802d07103500c910300700011140a82c42c0c1c00307540140311180c40c0103640d8043d40108485100500c0300d0010907100712459100c0d214400410000842c442d00064541d485100780d108801a484800c40340e560110984d0b0042e6003110100729a00100103003180c0c1002001c11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 935576654 1250 935575404 935575429
    0x604090c2d14101116030614040b1303020309150702030d020f030403140a02091905090c060a18030b010f06080105270a060e0c0409050a2c070306060e06 67
    0x1501c1107102401d01c004440c4030074410750414003644000c045111000d008807413034004190b180003210355aa02800c00f0301c80443c000d12058408524240780009203840c04100315110766048080100070b0344800c00c2045103258843d40030380440c00305102844803a642c02a1034402c1d0074160204544a48240c01018246a0b1130190b10043d98040340100c20b030080c0c044141c40460f600302c9a002e03c07444010341803505100c5039130002540668510100448402300c0d00c1018948924081c040200790b1312282c0003680e0344510f4141c03690120301840000095031241269900c14045011140c3d0300954980c1e800d801043c2c281c10000382c000d0a01c0d02404102c0e444540d850051004940112004500600b402c1c6c100c000010f08020600c443c800080308010140c0101d030043c13114031100c0c1c00600e056084203003181c02500030716400c1070524010400d07e4065020741114049003070350740c505014140c0b82d981c0c0712001451243e40d06001f0604008085001807043d10010200c80c601c9035404d1901c07400f0440800c0700350 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 935577904 1250 935576654 935576729
    0x30f0c08041508060315060f01110607020102031b070b0103060f09141f1e11040e16030b19090b121c090b03070903170405041b0906170f0604090c 64
    0x200c1400d6006e10000c00142e030411801d9845200b85207171140100c544468103014010140300310424000707190f60540c001c6101d2801e0b04044420110108000075a901c00c46601802d00554a0011320104503d0352144204042c00c2c0000510401079944030017102242040c080099008070181c1203119414900b85e1a400a540304c080052154104440900100380d0541d803101a07a1b9410950404032107034100c0300944422105e94000307182c01042c604400d20380030704443c0024203021a09460341048a18408084400b80390f480c49142002007480c0109520074156034403500c40c01e014540400d00f4031a001c01a50300d11a4580c5142d00024098241c0c01a0ba01800300308104008101c0016803044120040d245d11182e20b0300301c1d000d45c5552120502494003d240e01502d000f0441d15151000e61901050481e1030300d907810300c6c9503240b030207a5034a84a02116071000d41641c2c0080d00503480032980c207510240050000406c2403c949542c158000c15170052100c1d0003200b45141c28082000c0e01001111444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 935579154 1250 935577904 935577913
    0x30b0c040b031f080a08040626181009030309051203040803040b040f08030106020a1a01081908070f0c0e0105041a040519230903070807030f0c080415080603 69
    0x80040c0980c1a110090848030030700d249041e000700e0320070b0020000c0f0080c040b401c100c4010110a040600361607215103d01000f041e481c89189a05452201450704402160490381c4950f68840000001c08031022600140f18040e00000d200000e20034424400464025640056440c0091401924241d0f032201e009011100500400001800c0401240d070300560000130440e0755160761505502c0120000f500902e107100110001c00c4995000072665409801601002e25009104180002c02031007800707440200c0d0400b8008640c801c0142190301d20203031084510a2a100e500e03250a9903480b102c16045804070860103040004241d00e8070214054002140e0801400b2030b0010910901c2c00c031710754114090b64407140041c00e101141d0b0a031071200c0c50401c2d014024075901e41c550894100710101220546403503440442e001c80b03000810380e030080b03901990103803804050f50cc082e945120081d80358810407000c0d0502c1c1001071020400f4000500780a00c0c0369143d03822002c0050308100004181d280203501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 935580404 1250 935579154 935579159
    0x60314040c052107030f0519020901150e191502070b07060c021e0c122406061c05040221070302010f120e07060e090c030106051b0f07030b0c04 63
    0x4400040490790308403080800c000c640001c10240280240002603e4003d0120000138401c48441e4007034a54410300603540442100f14012481200c0c04001a4120508500600c00800d801c02c00c1c120307502c014204018010400c400046030031701c540e0003681182c1d140010400503800030341803c038111a140c3c0040c1200c04c4c10060b100100d40107007140500303041e442c4c80985060794024813000800308018624250200341c000141590b84182c5201d15018446100201c006080081681845d000c6550f031184210703600c075806490200340103405641d008000f0801d6002202040c907220710350706000d120214161800780100088c01c10102c01d00e10b02c18a0300c01e0040c212440c045407503815241e090070424a0700e0300d01602100c42400e0000780040b280c0c9851071540c840c03080001c0400480306241d49003901c1c00b45800c24400702c05410740c0d020740100d20520040c00b03064001c2e0f002e405208021100f04c1303846030400e00142e103000c0c1146410354842e00321460500c184205070308404d500208004c1c42c10710707152 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 935581654 1250 935580404 935580413
    0x16030b010b030903090112020f0d0618060810050601031e0c0801060905030309040e1603052b080f060607020d030f02121c020702040207050607110c031c121b0906031404 74
    0x20a45e80d80604121800010595803445581904c40000ca00c0048070703110003180f02000d0040019014000404000100c001181d10030343c02604141c60741d1802400900a004450300d002d400040d029605061b1602021119491450940f1050481014022440d81c041810142039890183c01c0041081100401400691000402c6031581e0400352000940084c06288850401307556140f61318070300c030a001000040c8000003416200044245a549404c20040c84189074640e174809614004a140000022622002e140c0850b0340103e010b41058584001940060342c05010000224089588810805600da60400c80107488880da42405440e181080e4040c3c40c42c60070f1080000d000c00c4d000a080700441d101c640543d58895070210440d4414108842c01900c1d08094000c2d40c1c1251048041090071460001340c409442803140000081d11641c1d41021a00c3c14044000c100e000358170313048001d4041c5010342608004245d55910010342ca42401001800c0d641249035107000c22020380d080c000842d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 935582904 1250 935581654 935581657
    0x70506090a15050705040302090411042d0b0a0302060a021011030906130206040b220305030306010f0905090f0a0b09010e010501020d020303041a2d0712020c0c2116030b010b030903 79
    0x41c3c8d01101c0e0602181e5441c030b407040c454203542030103942080c20095892440804007140c031b0b40d81c012881c0114042c010300481241203c00d558104e80d070042c3c80c507a003000035003081001010107524520540e51030209031107140d01601c450010015280d0300c00420000c800c038080c0718031a00000c01c018150620007003500095180d0169000b52840340030300090f100010740c4044428920094243c1c0003821071903884c10180c0d00ca820884d101400704500c21080d1003418400d81d8000d06a46005240308070a40311030b80340e2251440003d01c3e01c2e4000d581c940c1038032031076a24004c0c428000c02c00301071010314960503d4002800c0840841c000030565105206010010308028103040200c4009032841d455980e4450043d034551500c00355080240100c103101d0b010803c0f200031114414017158807031040500d48071014a0491049240c01700994000e804007561a10700340320408200041e101d12504100c02c40380f0003d05010446034841d03000215080100104000c0481c014010070424407998114507090344441c5e280e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 935584154 1250 935582904 935582909
    0x2a05030615010f11060c0c070501020601030f0303090204090b04151b05070f030c080408070519060518060408010c090e0906060a031707080a0c03180b0d02030a02070506090a1505070504 81
    0x600400c1c0c4040f00500b8403c0e03c42075070010301d00c0c003203404908184080b400d01394000d5010f407580e0b005a00e004591540001030f501c0c12607902c12882d440080040d10214001e00d034a11049a100740c8407007000010071080314416014034002e12206820310030030304c408402c0714180c001c1c00d9003001350305054895141e04403066600d010303000310f0606003908013450200d420600c00c120060540d80c0214010401c840c00044a1090f5081682c03025042c000303102200e50300d20400d00c034080c001641005081048140c1d0291040b40c0ca030081c01090910780c803404001c2c2907a18842c81400081c0311080b041000704a411011600320700c0803c0901007504205001c2021b580940c027000d420760055000e0b1100741030000d01182d000c950420381c00e90319041300d0100180302102c00e6006400241843d658400c0f01e041000c2c05d28100d421030004075150145803c00b20000e904010f1080113040d9081c404800415802d100891285418901070041d04030207103004802d030703142e11101c0c42001d032a02041140007500402290103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 935585404 1250 935584154 935584157
    0x32714091b070503030417040b031512010c05070c050409020616030c02100e03060702060c03010618030b0103030203120f06030618160e16020f070618032a0503061501 73
    0x40c5a03a4964040c811003680c0c6400d140764050004102090040200c050b41c0120b1103400558182d80c91400c5a031880d00444c0680c030100300d810004100811030b412080003041002800703e4542074000c1c6034050841c2c2002c4c85c0c840100b48005070f10010000f0f44003140010f01300407901000030700400e4010550b680074001c0900e2080991040310001d2600030841418420b50040c824002c1241030f04000b0203070350205214601174031500000c03540c40d03030011440610030650310700d01d03505503845e0031000c440c4400c03080c0c400c070001007882001201007119481e050340070b94081d4004543d80d083c030302d40c3c40d03400407070007016951107071a86401d00505030380109038603400c0400c00044001e010009003880e82009515002994003001f500381c005090582c03519600e100d5900e90301c0e0043e50600c0c4542c00c1c0d8841000d5000e96060f60406403040c000180100d140b1a096000440501041603c960b19060300d03040c060102c6c844800d80b00540304145a2100340c4002525081d4050482420038810b001c2038440004d41260 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 935586654 1250 935585404 935585419
    0x9080403020f06281d0904060510090e03041a040f090c110d03050702061305062d011e090b0105070f060e030a0c110907021f0216032714 60
    0x4520b07554a00581e0701100c0d00042c410b1802101201c411310461503c0d00b8480821581c101101100044d9042c65070180800790481050350342d0360383c1d940300a01c4020401c010201a49802141c40651481024801148032004580d1507080c950882062480030401c0000020200300c280004220a007403141203401384040404c8510f000c04d41a100c4000c4010841e0080c0b10f070380c60355103007941c0c1500240d0095140f9020b071915038441c010840075008482901030030070752220012a404014248080181086060300b210041c40001c1c482290200d080e401414241c84242070480030011940c00340f002000d05900401040c0407100c000392142c015408040e1004080e00d11170342c03d0000c19004202060581c0003036980e83c4100500140035501c40980071fa42000b4605034540311414034489250251660b60000d01810682010000000405e8244015529024441105900507541c07040010703a21135210445281c00c50366040000c06004a40a62000c03c00c0b00c08010390020014121101076080c0d4046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 935587904 1250 935586654 935586679
    0x9130605190f09020414090717240f06031f0b030a050d020a06050f040201090b13031e0308090607050406050c070816080d091401030e1906020a020c01030908040302 72
    0xc20a15101d8803040c040141012a800819511a80100e8499108403000c002e1807915082c900c400c490b0407290b68286500910051200c0140c080055094460610840742e84099030b940b02e50203041c415103000703003c1c074a50080c441a2002400310f180e1280d8103030010b000180c00c0e4212015918400003404002c141d40d560369200545050002021807604001203419804400707a00a55074a510081925841c0c03803c000f185006059003040350013250140d444660740c609044204015910130384d01d180c40b8440030080000010b041c09441c00101d103600c080d8452401407820040c151a1000741000441c2d080042001042900700040d2402e071001842d08a455800e21110343d1b01d048101d803c00c1486204a0705a0742c545490514180151513141040e504080e11002c0c1c1692000d03148d0084030301841c4054092565035219134401400b4850100807141d60003803100342100d001c1c0d841034058503588d0b00081e01c4208640c0400c40d641509100f8a0204041c41041e00c0b020201d01680c04028072442406004c0e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 935589154 1250 935587904 935587921
    0x70f030b21031303030206070201181a1e09010204031a091f110f04031703070207050d060f0203040302060a0c090f03080309031e090f27040804080d030609060509130605 74
    0x40d01c802140f49442218000d03200d09002e5034411f030464680c00198240440a0001ca07000052007004c01d6100e924545075081c000078903002010001e006c108840080000c0082e400008005280110703c3c400c00182da13941141007417802440c4c1100c11f2100703001d9070414401d4640d00020b81d00215140c4207000f02191015003003802c05081080801c202d0454082070600d684a0408001e20440b841650040240280810200300038001112808090b030403c050070401810b2842c40314101a218580c001490400d040d08442241c100792030030380c016880801040104040c074811020940c3c031504140d080c1e2807402c00e01c0040c904982c000101703000310104c04201211010020340d03041c2010024051943d00390b44400c04541d812515959100303d44040c8482040d082c034841c08021407078200f0301034030a07a10403568103402c0316024000302c9132100308000004c1c44903000e116024a4144940d400f240b40c0d1302c0c0048c41c8043e40d0b02c0e80c001c1072150042209105401d00c0c0000d50803e0960710120104041e95801300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 935590404 1250 935589154 935589157
    0x60902060f040f14010f12020f0d0c0c11030c0307091104050901030b09070b0a1d12101401150503040b0a1b0f020d03050c1e0405040f0203070f030b2103 67
    0x100301c0c5008401081c04102c010305400c01a09503021010198040e00701c000c011074011801440000200320101c80d1a03246402c0c3c2e40050a0340c007072850282d450481079004400c01c992181000c00002524016000208114100c544482d018201c00a062134009035001070380f1a80039214180c19541c0d80c046070308240f0700132020b640051000410300f409543c0c0da4180445003210490703044096000c3ca40c00800d10442040994aa107140d683c0c640c01018014251422a600f1811105600c10f42168070300e10301510820a001c000703841c0c03610100e003d10440d03a2308103100406801070020b120031188c20400444d4424281c80e445a0006980140e503103e090750040105441d140c03440a41c14000000c10803a9048240503a040155600b00c40b00700c0900d01c011400c5480c103445c201c00c03c1c0c1041060502c0d200910000c104030401c0742c1100c0d1700d05552000014203c903219980080c0e00d64000c002c02c80c52540064104810001d1401c0034040180c80d02c00062030003800d0844002d0002d0003040c0d80c0300d200d40400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 935591654 1250 935590404 935590417
    0xf0c14030301030b0103210f0f030e070906150e0607020d0c090c0c0c061707050a0513080703020f03070b030621030a02010e0d210b19030b06041d060406090206 70
    0xa40756039503168141046a030380c00340420707141070a03046a041d50f4000200d00f102100d942c01da86072604c00e0040181160003501d0000c01d80c0c105621400806c0341040300380803120080c4070200300040e1051408545030008040f0002c03400600c6080c1c80c07110b2964607240102e030002ea5040723500341c150385040c1c81c009041c041d0300e0700500394841c500098503807031039080340000c20003500561400000d41e0750b6140072252074075140210308415002801141515000301c02400300107040341059414454000c0e61003046110369440b062940e0b1102000704250709000d076580c844280c06402620b10b06080140b805054400501320302d010741d240500080fa00c5070007684040000c080041a070f599540030b000024040c20580890040c0c6000359004066998082d10140681d041c01000b00c0c3d1010801048a400800440031b02640220b40d411086800d8800d107445000910b1103a094452a030400400784022210401903054000301c05050b0010700b8840041c2c1c03994800d502050102ea8a9074600c00304900c0c1c01900f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 935592904 1250 935591654 935591693
    0x4060e0607020d0b0a061d06010516060204091e1505030d0c02191d10050102100e0c120601031b050d140a1502120603011a15131d0907060f0c 62
    0x18800c004071280c0105d021504402c440040c40364410640d411f000006a4056010407010040030126a015024074102c20703001e5040141401d590308100760581c1c13a0b884040000c043e60003480b40298042c0d1103006d007410044a20340c910682040c000c80d980317041b02440e005c18810b003841d107042196520036000e000c61280316201c2e00c18998509046480c82c0b6501c545002d0a031110000420345001d03100d10a04403a0f059006008032007402c0c1e03003880281074080015070540a2803686200b251030302d44095940014420091440303600d581050100d41e0b4405521115480c041c903030400c0260f2ba6141003a003407941065540400c6004c0d03a030110701d420280328004114000303101b014140139001d40d001e4032a03041c800d5040f6016aa418080500301c480d08021401031a095500e100e03000c0c100074500b054540e45040c0b0709403400400c60b00300e4141e021a584081c0012034001c2c4d101c00d0b0034000c1b81d00d00341c100d43c80400a00030320741412000380c15119495042c00801c400003008009100001c091083c500f80e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 935594154 1250 935592904 935592923
    0x607051303060c050304020f04090b0c0c16080a030207080d02100f0f051006020c010c02061615021804230403080c0403140d32030a090510090201090b04060e0607020d 73
    0x103401130003e80049030242c0c0310780c40701d001d0403500d41441d0190200e00355000c00010791603035603008180034540040780400d03e2032181c5651448464180c810003000340c5442001044a038802d031800900c0e00d20190000442c5801011205401c3d58001581c114414070240003c5007906000079054010301e5001c2807208401d0911040c0b00c40201070701d4840c0207840c410790a9441c0a1015401502c0004082c070000f5040001000054100032004914040e1544681a07079043d4002088001d016a041824024840102000d00b000c16280c1441088000e111202c0f81c2812540c0d5000d1046002030020000740c18800d9a800080f082046c000803600656030110321503580d00303100f00000303a644a188000902086c054100c1034800e0814004080c6118a8010451100450540d680c1c910781c01c0a85103114168030740c42d4a03000100c1c00d2180c510803070407100f40020000d2603030000400d07a00c40b550003c00c0c10307203007044280907003a44010044120041900c00507030b2501b03184042014940e6000000e0603690301d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 935595404 1250 935594154 935594171
    0xa030902031c030c110a060905120703030e1b01020c010f02070f0f08010b0402280e12011506051306110f060915010803040f090515211509060705130306 67
    0x105049640d81410031580c04010f5050f0701130081c1d80c40c0d01d007050005041d6100606030380010310316410800f0020b21842c25160b108070941c90362b4040f9000f5888c00c030f0100b0344450f10549081d0f07081110610030b01005110f100141003c00020351107042c89140c05042040c00403120004600801205004281130304d840e11059541c1d408a00f2901e4890040100701e500304002175110389094000d4400e002c80200030202400c401403820b038202e0302822a06024060400c1820000d035a417455690454450380c0300203c3c3d02040070041c1102108542c00c00340500001380500c5a14460341c503901001d491141c1408044e8240c88031040349402502914a0320038440e076402c100c00d0f0100802e4070072084540300a0f010840e600c07000c80513200d00481c0160b1004520b00141007025030816044190481c554403110b04982800d1800700d00099600450015400500041c0c10202d00c82000704244d01e2000d86440c1080e0b04180300030710b80755071010b03040300200040402ca140d4035004500d455401545e00000030050b018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 935596654 1250 935595404 935595433
    0x2011d0d0510021206030a08030f07030b04020301121b0308091003021b030909010b12040b0a0e010e0c271605190201050106080a050412110f010f02030117071203050a03090203 77
    0x40c0030081c0744c0500100303100443c0b01414000b03095000d00e640018804e0441c3d481420281980000a1640d01010b0f100c2002e07184036101c910080d4080c028144845030481e1660138030201005115103c4440040c015030104081658102070b40e103410300c21142d80c0301000c802901103001c4c1c0a01104590b0b00600741001030b40c2e00381c0000040000000c1907130a10042c0e070b41c942c00d91a490180c000000c641002d6000000d000860f011503660b0b100c1c3d0002d000050801d651101c043c00c507055042c0081d076540c481d0801070f0007441d147c040c183c122104800c100c8003080e5806103030005208041d103010350b004242481c4051a80c082c3c020388210400e4071494070306440600100a02a01d000e20441c80402d4104000c15802507840c01110310a5401c21503100c1d030710324541c0084400800d0440048900d00554659841c8403074203005e026207005031020301603180d50400e0000c420200708031030740f0700382039120b0f80080000c080f040f815401c1c0b050b05402c3c196140c004001040e030240018100c000c1d4940500c010407801003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 935597904 1250 935596654 935596657
    0x190e0f1e040e15070e0109120c17160320090a0f05130317180717100e100b0d0609151413110310020408030301060f080402011d0d051002 60
    0x640d8200c40910030320035001c45954440e140f00c000107000a00306000244031900850145808090600d006003020740d86080b074000584402d84100c0c2c0a52080004111640d241d039250b00002410801a0501c10020107501040c010948001040900304076960400480d0135140c0f0a451000500b40c40024a4001140c00080c404000b07425001803a041c0440c280d0030b205144103021980c983c41700c06441e120300e0032038a101040109540842461043e0045d60003000b4081200201200c940b075041c62284080041c2c1041e1110a0290400345072440c1c82d85003003400605145402a8810001088204200400c0b52001c81d440050806410908041c0c100400c0080510444c54155400c2003905400344c0400c80c0d407001500d41605901c0100c0c000c01c0455200c0c1c2d000700f6403980041c1103030b55454640031400143d0700325a100300c0c82c94001100403c690f40c0c0102c800000c0e4072403032030545074600c0d080d170009c1c254140c03007200e044480390082c0b1410400c2e1240e20072442c0340d6800404071155444095a00c0d0085d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 935599154 1250 935597904 935597959
    0x180405070e0705210f130c03021e030724050d1b0c02040c0c0b0a021c050424060b0d020711030a1b050a0f0603020c0a0b0c0409050c190e0f 61
    0x40c0c160910b03002600f660000341c0c00340101c6501c101070b0081d80340c10104401e091b82c5184265100030030281e0010050341d8401844021404814203a116168054101410151954000c051030b68200c1c1032000001c0c031501c0e030300d403a900751810000d03210466071510307000400210518001184240b455107091175004451541524401c441c1030100a034102e40454101070402002460b0744001c0c804994500744940261400001140c1103025a20801c0790340004d0b24000d8800b91020001503140543c16480d2a043d000e5500c0c0703980091015514203920354034244a030022245006601056402c2000745034812003103c40070007000c40e84000c8560600c1c840d8408042d44107240710b0748103240003841d410400710390700886050250155102e0324141050b404b95001c18400340d80760041002050020b410801418000ea10703090b03106c0c0e143c5080c61442421600c014008940440d0140301c610200c80a045000f040822a480c0c40420391014030003090140140d00045544034411814191000071491802c540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 935600404 1250 935599154 935599177
    0x9062a06190501060e010c1e080d020a03140903070b18100c0908070b031605070c0b0304020405221104020f0c0307020a0f030807060e1e010504150506180405070e0705 73
    0x3d998a18040c0c072080008014107001c24002c0790900b000c01c011080c075105101418800100b0241c0e9030755100d02c0c40e840000c054030065070219400110b1039040c45240b82080d13082e5034180035400c245880b5a52402a40d07401085080d5070302c00100404440e074100d03e003103a16070049034880380c0000c1e00c80010300000001000041d030111800680f00000043c1c0404945081180381e1440e2a41c4007410201a50340c0c1c164030030700c1410094580001c104017040b000a104030101c50707443e800d01d03104210540d84081c12545c0b200c400c84a62440403059420340341c4c441c1e81d01c50b252500305250200494040e005d0411810480500422040700c84800400100512803080390f801e050262114901080780c40e941c040640646801d010401c002080740d44042c8440448404645500d0100d2140740403800d5203510990899450388142300810512000e407c5214031590000e02291400b0400700f4110300c4415224812428020041000d02c80107000f8a0003401320320b0b81d0b4607140d141c0385d0b2002e4041e0f4014040500d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 935601654 1250 935600404 935600411
    0x3140a03051509071d210304080709060b09010302090f0a41010c060f0609021213080a0311070b010308031e0c031b27040f0209062a0619 60
    0x1200349003c40c401842002c00741c98a95030582c80030441c10800365190101c41e0000c2500020f03480b01b41100300001c03980104d110086980d17900b401e000c5030030450142d0000c06c0c014140032090052031800d2060b2603031406c0c20710303005172160343c5400010f041d9400d0072170841d0003101d42800814003d440c3c60220b003e01280ea02024900386d4010712084489500070320031302501c800ca03250142e039984a03d080308461805500c0104840c1e04582d04d000489044e50300ca504660750002e88001d40042141080d070b8000e1181c80420300520485c5c0f50000180305100904080541d948190f400d440032040903294525000b560b540c02ca0b40e160724001125070f106030388141d20004810101c400d030000d4031f8030282c49206000705240c21a02c0d4172500451000c615810891610390902590314034440c414520f4105840a011907528181035406210454205580c29280b07640100a41062a00c400007285d00c00c0420022031040c07540b00b8000072032107000d00d443d10946400307210284441441d0b124043c404440c42c1007401c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 935602904 1250 935601654 935601691
    0x913050c0301091d1e0a1403120a02130b0a0c210206060307081c1e0201060501110f070302060f09030a0b0f10151404050607050a0b06030a020a1203140a0305 69
    0x90038411980180b405050f8429100301d4030b42c006003003010055000840c102c829440306c9503116622248003002213a02d562000c00c9048048289042007500a40780c00001c61400c91720142c0f2500806071030040744100706000560700306091080c00260406a000303000700410300c0c4038260901032a81c0f0203480800601c100308c080346c2580341c00704203001103800280c0100b84010b01280c0c4114008407030900c4609001e510b001140c1c1c80c8110039141803c0001c0da46c0000f84150911001508041c0781d503002180b030781e01c160003a40b02c1440c0043d40b0803d0302d0701107905980354018207090404600c07600d403140d900b41c041c24012404001c50150319030f0195080030f5440c1c1c890b070303600080720003e6485442280c4042800034a1200c81d40c1c010b00307a25804203400b541c00d034034250b1124003285507640a4501114190300c60b083c4d43c0b003442100700710030790088000c40c040c16404003d40c0015401d4001c0740a280088130103a80002c08060051681034014034800e4000c0e40c4440c400b0501500078030741100d00090300042c100c1d91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 935604154 1250 935602904 935602931
    0x50c010509130c0203070c090c020d030627150b182409010c2312032502030904090309030204050a0608030a0c0f0c08010507090e04020d0303020913050c030109 70
    0x1628492000075101d00e640844494102d03002d0542d050222080d4001002150003060f468041c1c40302801060703e001c54035041c10032000b49800607840c400d8080520b048414012030f5401c0c03100c000c0c038042c0c181e00307170344c400b03042c06243d600500c24039280c2402e0650800c40010f600b25128043c140e00202e985000350400c00907000e2203103001d4400500001c0244450742800126404000303080b804c1c10625180b0001810b940c3d9482c0640340c40350b032100001c031801450040c800420400c801c10080e288800604600344003800f0804064080e989800040e150001d10003814801c00c10313100c65090040c0103220540c070301d040c0503140e04028041a4022418400054176018941c055401294405401949001070801007180c02c0c030b42d402011118102e4403400301000c00e100840303901c0940000e5000054a04043e4030180c003c1d49558410001c41000030104000350384d07104110014150141809aa83d00c00b90b00011004143c0811400c401450003040c0559070011001640c1a0f400038a0100005420200c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 935605404 1250 935604154 935604157
    0x81e0705030601050127030c1703070215160501110a030e1609110d090501020a0e010c0312020f0405040e0d0311040308090f01021c03290d120e0616050c0105 69
    0x40d1074141d807103400108400c0d403041010f00200441892058003040c0340201c1070070b01130703020343c010341c3d80c034070801c40074408200184440021080014015441c02072a540070807071300001c44801d1100320f180400d40002ca1640d1281400030142d003c002003001c245460305444654000c030040350002850a520074500d0280007400f94081c0240706001c102552419100401800020005014180c02882174924940e0103010f00304c80796120707000140c1c44240034040203101040c448040b50402940700c00120129400801d0781c1c000006110340507a030380400141854140c801e83c1d2140d80c01510b00780280003405004140900e0f074101c02c0d60301748094120350016140038016030002a294081c20844402a8035100799030860685060040e542d816402c0c025080c41c54440c0c81e40c0d140032948640100e45178243c0040c0b1442c5120198070020900709010000c40c11741540803500a01039406c200c1e9280e4194003611042e840c480005100361340d03130001e40b144842c1060700860210750030722803401c240e02c4030b602403070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 935606654 1250 935605404 935605409
    0x41d0402181f0f061b14070b031803070308150d2901170c040e01090503131a03190510030c081b040c0507171303120e10022a0604081e07 60
    0x6981c10110080c02c03445007001d900c05c0c00200c5454080c134940d0302240b401800042c0040c00340d101207a461b45400c520789546140b411800c0c0c1c0c4550410041000040d82205160760041c001d000703501d030140e8021020947c0c500740454080c01d4520050707901c04403d4007605c0b0404c90041210490f40060340d031141c08040081c1142d001c03c40c5500503000114080c1000e82c440e4002e06103940001c511500c0585030107040d68403000000b42c042500e00d000340f001e82c0b6543e075580b800c0c8503244c0101e4650f140502c41e441c40402103404803514180c580c00801c8100200d0185032300a5078100214545281d69070458076500c5142407800400c00700708150001e8280b0b040e00c54044400700d16210289403026556400c0480001c1d440d8901c042e07041440204a42d040c01049074015601c540e01006070b0940d5814040c100101340e200c4a03205040c40d014481c5402c0c2e0102d0862060340306c01700f205005110311194110001c2c00c00c24650b80010700803c0c0094070450000b41030003000c1104004041d171020103a21ba07034440c8440d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 935607904 1250 935606654 935606657
    0x210c170c0f010903021f0207060204082401060207060e0f041d010c1409011119030c110904020d15020909090102030a06060504030b0f0c040b070506070212041d0402181f0f06 76
    0x14084401c0c0c0744500e092515921681b800140b41400542e03c200403a082900010110f5010b145070b21400d031841e02800c04c0020b240091000e283d0302d8144003d681d0482c501682c0c1c00c100d000c030750401d07982d201d00c00da80710035003001001440300c3e01c019240c0c4510340d94a60800309096081c0307400c503030905000c0c0e001c0c848880b40d000c401c0b52800070480019248501e07107825401852180b10700c40c89a01c8012070400d04100d120b59610000d1200078140480c4680c10801d045202e29a0001480b00580da080c212011007a84a004592400c3c140d01c1e00c40000c1c0207118100d5000b080135410405102030643c0114462078100a080024a0310380d0001c1340d02c0e01072800001c020344895000b04905500022680e5408101030000502d071589404e00b0130700503042900112415805030040c000c1440d01070011443c001d02c402202c5040900e4440c01541d61208034a442c04400f040740040341c00e44d103034062605501c8103000f0305400203041840c0341b400b00141c1441c44082d0072481e03440100300000d82070030007000c55034907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 935609154 1250 935607904 935607913
    0xc090603110915090414070608070e13020906040f1e030b0c0c12220510020c0103090f060612060e06060d200a0605090301050112210c170c0f01090302 66
    0x15018841d03008005009140403d5240c0035860141d542d00541c0c1c3e101e98130413050f80c8407082060340c20900d0138038940c000500b0300001204000c140c0b0361101c00c81100e41e00c11a0040884001c1849a8009200705014aa000100000c001c0394107108209504101e52400c000880040000c45082030b910390140801448081d0420104070b081e0041e13805005261303010700584401031018600c4030803582c08940360700090204400900d40e502030f04a1703008002c2005403440804569100b80c0291180b1303007450705605040d590050502481341c014071500c0e40300da214408000d865250040010100b5140380b003100ea4074200650f00300c00940108210f0b0182c44050141c480da86142c0da00d482d04840f0304000b40404a40c0320311440c580707945002d44000100340680300d0310398400e88001410300b5598142c11075030815154030b5008000458610601ca03502c0b0351101006040f202c05003048868056111000d040b8049003044032a031003484100501103c0e800d50100d829010310303902c02c9800c1c1c41c0741c0300000d000340e0003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 935610404 1250 935609154 935609183
    0x603062408070e19020c0a2d120309061b0908060a0c0c0b150d06061a0906041502030d060923090607050f0f0c0106060917370b040c090603 61
    0x110030001c0d04c070b81ca104100941850240e0400c54138061404030192118051050440200101c000031030742161011243d1903c501001e4554141c005018401d1108050b56070710508203105103980054048080701b0800c212a040c80c502c0101455014062079010380a650b004c903854a03181d214000c000d19180e1102000d01c0d40039240c08030201001400c10006c2d000b00c4443c61040d9854070348205c210b9108070300020302142070030840c034000c018200c0010035946c001c00010b22159600001c0d5800c46080d0092400e50350704881c0124203601a03840c40341001030900c80c0205d5902e10340c1c1c000005035020080040310b0181c14a00000e100002039800905c3d0350004004189000e224900a1020390b00c1001118500910005150000d0340a10404000ca9640c1d082c103000c26a4403000000c014120015000460314207284400e40f50303100034000e0350000006130180c1600a40c20f603603044070311710450400700000009042015500b0b508880440d24040e82060205800009100f1182079941014401d41c4440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 935611510 1106 935610404 935610421
    0x11070308011e140a0e2e03050309060c0118031d010c030f030e010b0d0501020d05070e03031803190b06010f090f090f0b030303040c090b010e100c060603062408070e 72
    0x2181b411007000800e200005460010710100c80d100d03034500800902034014025280701c03502840440c41c94109040d0014051800b9804980094000e040107900440d080640441c00a0110384015003881e112446a4003200c2810442d100010b11462030400242800c0b041c201c00321096900091003907030301203880c0074103a0420301904105d605092040006600e900843c5119000700180549010040d5130400c944520300790f03410306e010780c820f5183c1441c004d00c034401c6841d82c0c08601071104074241144039041c0390084802030703018602401c0c1041c8810016049010540c0d40250301c1d00c0785801c2e1507a042c00150b001c1c0340300e094204606c1e03140403050f9003035880500000d81071200254030340100341c441c110350803190030103031404140309007c62030001e0080016403c06400c840c0f9144560b4801c4180d0100c459114801505500d1596621021340d81e58450502804000d80e5800e804540c040 = true := by decide +kernel

theorem cover : BRFrame.Cov 935431654 935611510 := by
  have h0 := BRFrame.cov_init 935431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 935431654 ≤ n) (h2 : n < 935611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
