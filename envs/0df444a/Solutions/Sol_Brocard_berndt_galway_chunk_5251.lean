-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5251
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:14:52.293495+00:00
-- url     : https://prove2.me/submissions/ae1ed615-d428-4211-91b2-8aab711098c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 944244604 ≤ n < 944424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 944245854 1250 944244604 944244643
    0x190210140114100203070b07050405040c0e0102010e0714010e030703060501060518030c06160f0206030108010e10110702100207092a09062321100b03060102100b040b040c0f02 77
    0x103c079180c0000550f445158440107031040340d40c402030304903200d00071542b055030001c0c203042d044000d094102a103009182e030285e00804ca540d61030504541d8a181510590541c0e00d000c180c444c07919445400030074080301c0702030200e40c84036542e65600300440b4000d9010b00e0000d00080740100203580b50015407403040c6011001041940301c0c034000203100d4031900001c090f050901c4100e000402134003036482110560014219074481d0381d5411014081c3c00340075000003480c000c002c5000c03007850301c91090303203d540014100141401c06540c01e00c40d443e001c0c91907280c207510824170009507402c96401403486611b000c1c6628000f00002d012210030a0444980d001e081c050010818080654000e40354054540f04405101d112619004414518840c8104a062145103010b60511424490007024092090703054ec1d110256542c02490105000c107070f6140d401600722060340081c107100e41c1c2000c841c520008000003032148101c400101101e0240c2d545030040340101582c2c03810b4940610000c01d60700700b840c0f80b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 944247104 1250 944245854 944245879
    0x4506040b160906020606010e21010209011715010c02030f1213290d06030b0112024e060f010810060b070204090606032a060c0503190210140114 63
    0x69102d0400400150400510390543d0208d0f5035060409420060341d004491003004007007a5042c044d5204460707880c08204a180d4418155940090f11803051342e5012100342980b48142c0112545065880166410304c542e44100040382002e10a81e626036030102c1d8810342d07982d190140012110459403014800e03600000c01030159a0052601c0c0344448c03207801c225075a415200b80700030000c00585d00040c00c25607402c030020a035840c02500892850340220b90400201c460a00440944003030050b280900c01941c0e0a10302c40c08240134036410f17210005d814100d0741c29004034a4549005411202406070741c0d500d000422007410107214095851281c800d0a0060b0350814401c13017061b00ca0584028081d50b541c0110805003c4581e001501540e8445c102c9010000d05441c5910201311034512009441c0c80f0700b10015429010747e0075800d54541c048051410800c58244064502c0c17100700b401415802041083c00340702c116480740080e4444440035454071035040c40c01c0450781d08284482203000384c2c00300700c0d030303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 944248354 1250 944247104 944247107
    0x9100f02121218030c010c091d01180e030f07080901080943030302070303032304081804150e090d052515144506040b160906 55
    0x3198010403400311200d83c40c041c4100e0520f944148540044954644000c00c0c40d91070340301c0c00346d504442d1140b001100380c2c030170b1401d003c1c40c9031001e00c00c080c12102c411401d8103d8405a81042a03991891419681440c4000c0e0100056511881084560f00c0d00010308050030f60b0410400c54008407503400410280c8040000000d0b61500c3d071511421040c0c4280085211030000406240351250f1200034410651341ea02d0047e559000501044020078248070040d00f56921404000072220410440700729980c5540d200c1c11080e03804080c039512041550740da2561551654081d0707080903010074100524440c544114048454006031a6000581211900d514103d500109946180078400586440c5036801f03030100d0600d400444006101182d000355000b051151940889960740111100c0d8842d55104041300d0b08142c00381902c10342c0c0c01c150701c80700b0030000c1e01e00f0b003c600c0d804507400207521000b000b0b0348454504101150201d82d4208040200081c0705484584114900e5103424400b81c80c1e42801d40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 944249604 1250 944248354 944248387
    0x6181d0304091802040e0708120906030a0902030a02040c08010815061005032e0e0a18170708030405070510021b0d030905060d0506040c0207140d060209100f0212 71
    0x80829080e180d40ca290f803981503500c008200254000c01c20441d00b24162001d9890f46020701ca80b019a00a1402c0c0b00544139080c4200c0e056824000c0c8140d286a64040030f807070013004002c2c401d80c1c051141800c410300589603441115030307250709526030b001c080d0700d015a4207160602410755415111242c00601c4410744036030b810b42034160300c203050458580e59502e0b51100c08949505c2c09010b90718040303c0d4410740c40c0c03005070351800781e446030282d50009a42e41e11540003518030741031114484007075281c48200400d030710950003042000990896460021903444d82c075042d400a80e41900c1c40c1d041101d04204600c0d100039402c0071602c00740090320740d0f01d000341c0040003074140710f20b01940590804444142010310841201000d40300c02044140c607144039200038030082200301c80c0540900d1814091200c02400064800200c5030300c43c0301c400c00302c0182070a00640012400045412903028800c0024580e550702c505603401c015036840d030081038a4080000c0c40e1042c181c020a06801c4100000d107440c103d40034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 944250854 1250 944249604 944249609
    0x2030304060e16090212010f03030c060c0201110406020f06010812031f15030b011701050d11060d1d0d080103080901211a0f0901081c05040906181d0304 67
    0xc00020802e400e03894050400d409052003c0c01c000340d1603c00b06807400c081d0b01412a5071440382000c800c5a8850020440316040e50001901003a4890b10003000036a8680001860b01cac3ea5200214801000225114694010383c0090003d6080101e40483c03a5208009035030050020301c004151440c81042c4071002031201615176800e030002c440200318402e4220107c900282452540b6203800c5003c090300800a241c00242c050000d450f1072500c1d400b086548107428103071480200151541c807200d50380c000034002082081e90300038009010810b02444544034101c44022010f42401500040c5407140d4101a1295035180500c2414001480804c01d141d040d10106c010030b08000310b4a00c0a00305070403129503001c01c80440f442c00d000c22100d58000039a910000c030750042d40d0010002240c4000c100d01c040b001d014041c0d03160b0140c08811008100d0341603407409070449040c85880d058841903c00b05503502d54000002013140900740034041400381c4075107420700100740e43c0440c0300f01805203081d480f882540b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 944252104 1250 944250854 944250863
    0x7060f02090a061112120609311a010608090709060308090405130c0308040f05220c091211100f0c1502130e151905090c1c06080f0a0302030304 63
    0x130301c400c0400d0002c20a0b180d10407400d581c103588400c1c031112000c4030604101c420034001c240c0140070600041c0020565005100044103d0b00b42000c18000e00b80340c508920815108040807285040d507030b180c00791845020f4400355a0f0702c90240b500c2c00d1207520341100b41d4841021945026010000b20b1121429201d021908503808030351b6844420b039400303503101500d50150400011190010030803505400400c1200c0c4802c002580712940c4800300192019000349042c071941c9a0707400440354581582c0492030700c81c85401c1058100b0f889a0041442c21b551800c00c840384444c02810401d14600102c031505028054503040c4003113400041d0040c0b1040000348014007544290810051824082d015580c52110860031114090303600c2d80303a13001811041d542c564581400f223101d80c4290621040c90948003070f8040700d4840040c541000e00ca144140140156140e041c103000c0002040140d03d114510740180030300200e40e65041901d01c074100725840540d960240e100000c44030000340c01206407640f02e1f800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 944253354 1250 944252104 944252117
    0x709080607051e031003030908030f030a0902030703080c030a14210a020c0124060302090307120204021303031e0f090b0f0705070608010e0609040b010e040c0509010b07060f02090a06 80
    0x201e04618114850303070b94140f00d0500044100500c02d00040c45150889000f5980c407a5415502d103892512441100c5071046003190800000d41c0380c13052138000050b0148058122100c19a590b00d071401103800c001d0b640600354100107283c0ca0841e910004440c000d240154000d894135044e0340f45a0081294400c1104086901d0400160489803d50640701c1c070203070080007400411560322000e200c0d20340b21280c240144010320400f05000e03100f8800c1d01c0e600c1d80003400601409040040613010510030034400c03648103408020740307041d050304400220001e51107a160403031000c00003080b1031409a02441c100c4208098400030680e4243e101e04901d040b503900c804940e07510341d10b0000301e064034441d1a00c003070424400c44800161090340031210234100c3e40e100c0d49450365070300d81804010300c05801381d90241c49856002c00500c000c0320f00311591a00f01e0700c2803061051403075840300480c1151409920110340b11030085481c900340241402040c8140c51005411442c0c010118000791030010301d0f020f0b00041050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 944254604 1250 944253354 944253367
    0x9061214010908030c1c0b06040302090a022703011404120c030e0a1403190308010b09130501060806042403080f132303060402150d090209041406070908060705 70
    0x5082d88603441068000c000e559132498046500d200d940d000c0700719002110000c1407282c420764040d200302200100d00a12451a09145808000b015040034107041d56141e420400c20594800c0402c00001c40504012201011803106040600b1207110b4114681181c00040070400014141015400c2000c0c45e410200c000842c241000c4540d52220100c45400601451011070102d81403101d00000a03c110100c4a00c444d10384000084600c440d0070040101c1c840a00601407021020080c0c40360a001a180c034140c4900314030031100381e4100780d10040211300c24806100305410540140032000159646441c905c0d5400c807210101150107200141c843c0364040f50745010303440c030a42296a080948215520056100e80b880810415802510f1b10034200a07421001d080c01c0c0450003e21075030b00182503020241119108003c1580030980c1c0346101c1d640e5068030001603484010181c00380d805100908940c000e0540c00902e0004040c00c00000e0024041042020020003e41e0030386c404030a21b041f50304d594 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 944255854 1250 944254604 944254643
    0xe010f170703060305030f0d0e03190305190911040501060504050913060e1509070509010311010c03031e06030c08160b16020d1220030405040e0c1503040c090612 71
    0x8203541006005d4000052114020310380b4001904400303038502c07010081c5c0418480e20341d9480c801c814914130049001c2d44a540c0e100e0103640070652000700313010500c40c0c880c0c2040d40c01c400ca13401100100c0c0c07501141400080e00741840e10816000d8452070070828a0035040200045803000001c08140c4102c141910f840c080120f5034121100b104c20001c11125100115010742d100424211284d4080d4400e00c800012a4609040810b04a0f038121000840712101038004440034904900c0c10750501d919410302c4410b40b0743c84085039940f004c040d90005050303425071400e00d6241c80c10703910800c2e45912400c07649040e1a0b95000480031101c00b5112699a0b0441c42022500c0c0041240065404400000b00109010501000503414805507a60b41310807084840606803654040c00c1d180d0140d4030500092109007030991011245007080c800315204c1015503800141d45558420751a1812400842800b00b0803444014440c0680030400c01482400d0900b04c4844e0301580c221030180850711b00d000260000c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 944257104 1250 944255854 944255861
    0xf0b16050c06130303030f050708070c020d05120904060503030406050405130e010606091707031e05030c0303070c02011205040203060424060b2a030307030903020313080a02010e010f170703 83
    0x41101800301030703c410900b40c81000c040c92070720080d0040b904241c0c003191001014415580b00c2c134040c0e1205091920f03403401c1200c40380b580030700c00c90700700c000b085445020038410005044621010000c542d55207021106100c03e0b80c2c001c0e80701c0c41c0070344d10a101c20700c0307038a03000800c0d0750656100f80d0300500d08070b40301d103070440c041c0c1181c110b03a81181d441e00c4000700d44103500c20088000e5031840100010700c07601c1011603c0c1d54441510016240c0c0c6940c034402c129201c000d02880c1c009601500480c0d0070081314420007800c1d58400c1e10710350041102c0c042098210b503009152882005602d40b010071507843c040d00441e48031000180010854215008038542d02c3d03070031126001c000c9904280410034251214104ca0841d40b00381001010060140f010441603a00c07031000103052000000a54259203c02c8416009004004401c609501081c013036030b1080019000071800406102c80141030914450001400485195820b1410084489682e00e05250001c1e11080c0103100101d85038241e035100302048006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 944258354 1250 944257104 944257123
    0x30c040b040f0608071e0f02100204091409060405061306020f0c010b1507150b1f091a030105100e0a180905071203020a08031506040806100f0b1605 65
    0x30303110205000c103084089090441c01d41d0940c1c0c0310780500d80c4442c4070903078016140c030b405507901c0c3c41e8000703035001901d01c90586181c0c02241c40c011140140c100000d0310003030360426000790f24a1552030b20a1703c02070030340c115890382000701e500203805242800d445046e100c600041c800e4000d90003281002e410890103504032000e0720389035151940c40d01d010b855040e003e0300c8243c50b02c40c450f000c140c1d0000b8020554808545000b503108040c000000400501c6038040c200310160580d1100d010300c400e049000425503401024100e580d28500007908010780003002d85108014281801000d00040c0320580b110800c0c003801c0d07185414607110f4503c100380018058606034101500035440e81000c000c9540640c0c0142107914854015074080540b21148065105c100c3c5038080d0041c0e01c9407034404040b5100d840250b400015102d08000901050301c003280745644079a00011803a40080100282d1801c4c0d02c0c0d02401501c805100346800500d801584201c6010342c2c1c0d61000951601d0080c4000c0100c1088034401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 944259604 1250 944258354 944258369
    0x20d020d11040605150d0510030f230a1112010f18020a140f06030c070c0612050f1510020c0d031815350c040501020114040206040b030c04 61
    0x4404194601169a001007091880c0140d05000d004116850402d1107044807080c61942641850311444040014100285c00b5440c13245038414044085000013154880590054414500712085407445152184500f168000c864008800610002d604544179010b12481140d0940038038440368241c0c0d00501041044618080c88c0c41c07682c1c018111071143c60000c1c4c0c0d00869045455540d1140d9406002013040c040d140c0c13140d0428940710061421f00701858106440c00e44403030800140d5a60500f64001035041407011a94130b01403100c810340580541503001d0480c03482407815017000b8407441c0da13001d00170b2280c074400c14007414403a0a0038803c0014101c04400240155031105260402505215446c1c08007503076002e160f032000c50594503c40d04d50b00641e850327565400040031180f0096402c0d04000202c0c8141c200812041c82c2070348451562140900d050440340d03039489152200180c2101c5134403000c94840c0b03034003a04100141e40e6010a40d4111a54038000710303031380c1d40d0721a00c0c1c10b414442c0c0d412548 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 944260854 1250 944259604 944259619
    0x140a03091a04030807083c070e13140105060310030c081f1a040209010e04090803061f050d180b0f01090506180411010917010501060e0402160303090303110705010b030d030e19020d02 80
    0x100264009e40030550024107071f0340050650745031042e62003600c4100352001c0c001400000100941e060500c02154042c0240c1504e0740e1558599840114146c15640030b44882d50003100c04404c3c0c001221018182215881c20802501e84607108003d0740780c0c04008500d200d164082840c0d0f03a5a4020440c0d00400c070002802005403000c10b2410002c986c00c1520814040ca174404001c015000d50030b1603002900d04161510350810782c11030100d50141294182600120300c002ea80d603400a03070101c4045010b266801d080c0300c250b6040035900301c2100c500920041c8604040c07070300911b8100c1650344298100d070704444d00142d04003a000069504038816480310307040c0000f2030581c2480c8501944580e0585100c1e80d40ca0310041100303c20407041e0f0040c5680020001c462401600c00a4017a50004440038132038280070410f140d00581a01c05900311907401d4440b651202000c02041c42c2c180189640107a0324103082080d42442d00d10140c2e1490901080000301c1011080c03c015540c4280900003940e90041001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 944262104 1250 944260854 944260861
    0x60a0f0314010c020a0b01140d0c0e06032b2f0f0c010c020f0618040e0106140d0b0402060a0e03011b1d01140a03091a04030807083c 58
    0x440c0c9440741e00d144600700794a00221806840d1012540071406504a40c0d880190303400c10101e0401011010701c0154089820000c00d000a6201400350004000030000d90280e8905001414101903070303005010020700e4455000c42040c4200701c102d0000b52903030302e0808810924850422401151a00d2400b1809d907142c10100d1400c00c001003595220342d100f41038498105018006451608201c500258800300e07440110005041140103044040009140110544464000b08048071040382d881166a5105c0e2002d22031010740300d01d11090408203a4001c52400405e45580312511000303440248504000240116050f11840b0364210080e0020002c00000000c9944114090000140c8201241d0b0384c0c2c0450300750300501040803425420603120700b46646544503c00942d5840180360405242e640c2600c48040b880141c031860f81000903200780200340c00e00e41006030103114002c01f500c0c10081c903101000750360813480c906d10341e2481c08102002c144000ca01750f178038880562542c0310300018501c071040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 944263354 1250 944262104 944262113
    0x1a010224151c110a0b0a05071205160b01052803060207050a05120d0b0108070f0f110f0106170f0a0b04030e060c010c110a02092e1508131a060a0f03 65
    0x803903003e400880c1c00c0101160350f2105040a80038007890380740424000e10001003c40c96031040d410270300c81d0911301249030403c110708814903203001740e10a841a5501c41c00602c03282c04c1265002040700210010714418018440d080703c004a05400000e000503004142e00c001c222040200c0500694418142c41020490300e10860b541c1d003107a113105520130f08207980410194040d07112203002d4000313690781603070780348020070262503119240700d0340c20406c41c076080340d003043c030ba400d202c4024072445240000c210b040c6860741e290b0308002c1c1c3c2800110107401c141180010000005410f613810341e0701c0229000b440d540d81c103068414003d65084071341c01410000c0e84180905040d40b102903104110b8aa0f01c0b00306e00c140d08240d655440c580002508031503003c000c242c1038079602018601c40c185038024484030148520795420400610351180b801c0300254141c07008040d40180340d1342d5004602e04003500328002d00e07403107106a0a0ba0307816140b503100b2a08012a502d5224040e48002a01c1000c9946280551740c3c40c2c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 944264604 1250 944263354 944263373
    0x50901030612050c0f0a09090f1104051603050c090405070203070203010f0501120f23030a090b03060d03180f0b130e010e010e09010b041a010224151c 66
    0x1502400645000740204502080641c480840707504000148520030656040c02a06103c5148103a40701107040c00000302e00c40340c0c1c020080740354030401c84990301d1b0030b0328030344107900c3d80d03250355002d102c2c0d0b060004225170303610254040314064483d4540442e06407280f4100d04203600ca41e0300c0b5075400c6400c040420650703035000801010a82d100f80d0082010700d8440556404a13402030042c07102955000c0c041c80d011603101e1110390045802405020030642c00030b0700b80c1418408240445c00c454202040a188007900300d040700c8000c003004810b540c51803405900103458041e0401c0000e013071258581210740242340c0260782c00e0240500203030701c09a00b6290080d81e800e03604800d085c0c0301c0c2c00c580d02c4400708000c0c014012241c107e580d20030480789280d08106a4009402c4000c080742c0c034665a81003201c0f07550341c942c040c40c0c13405402036004c003200810340c000080c10b00701d00f40342e103810b240050500045c0701004c050a90b90300400044550520001480014000c02c5c403036050b40a02281d0f800d0031109029804c5c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 944265854 1250 944264604 944264617
    0x913060903080117070f150513170d020a1208041b0303030516090b040504110f0f090a091e051801020c030d061719211106070e0a0302060a020a080a05 66
    0x10020040c54002c2c64180b941c400c1240242146d03803514610801900380813a0303556442070014182a8103045a00c3e5008191006e19032100300000d490890160b00c039031040c010048a10903038805004500031070307140d9000d030780718480c005406c0052540000741400756582c402030100103080d203035000d02075072800e00601500c0c3c00e40d415407000c411101c01403842d5009145180840340c1c02d51000e41094940341c10000149045005006810300030440f0380d21121070880200202c1e4001d01c05161610311351000e00c1100d07215a00009040d51400e59445801e044082c0d02c207140910345580404e01e585c60603000d492144d00c112400940798004500054035050101c00b404079003010a00420078165950b541c6e501d00d2040b0314040c40a07401020b00c0c1404d004144581005aa006007201f9101c120701d440078284c071001a01c210b600142350014020007510040c00300036001030083c60308600010314500001c045c0c44e05480000e2094000080c5210091700074081801c001e60031159403512070040315005451607101c1e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 944267104 1250 944265854 944265869
    0x215180f0406080604020405091509070614030606070609170d0902040c0203090109210f06090201020705040204050a0b0c12040e090f070612050a1d150c1809130609030801 75
    0x1210915141c140361068100301c807400401000e154070360340c080c800240390162166241d80620701c0a00029907039400ca250142507454018483c4030302e004c0e0000c02401d00385200e0598040d0400611800e03641e031000755140235801080010b4010711510b0043c2a076002500e41c01c10080c3c02140030101100b2903800034009a000355801d10078107414802c03c03038491084240c0306000c980142d80c00d01803209090080842811500b881d030100f082075031a040617281c0320100444960752100c01c8d410441d40d042c000c02009000c10383c0c040d410103041000041c02140c09000b000703035031800816813441d0b260040002064001d4000c1c14039503510b48072421104814000c83c0c10200714030459400410000c0700041c0380003140c509070f0341d18003c00b04442c4950041d14025100d00d0443e03840d200c0610061030030203030703180092818400804180342c242c000c004c500700d0700a1000402000602c850100c40b5212000510800d004440030589c0e9034815901c4c0381891030701800901031519285803a0101a0031034034090581e90300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 944268354 1250 944267104 944267119
    0x1120501061709030301080d0f11070308030a18020f040c0e0a030b060102071202010807140909151003090b1611060a0b12030c2d060906040c05060a09030b04021518 72
    0x200c5030440e55a10082c8a8070200c0c8e80000d107001c1d90300d846090503c080c0007080c0f503c400302d02103000200340b03800300c26001518183d0002061104204080c0b240c2d100c0004040014a941b8205400041030418a030f400b250189440301c09138000c00c0e20600e1040b6104c5030080c03046403040d880c0c0c1001d00d06944200d404a01511845002042c0030000344034050384180d05035600034095035021000c8a900b5481d25107150115010700001c00156103407113030180700b200002081d1200654030000c12044400d010a0f11091600c2c101803040462150090300f0ba204410240f22126141c1c4820215004250301c0c440209602650081c804190030b0b5800c2984461400c455018056600d000201d0b2684910b9803550000d500c204810a1000250a901c565800300c141e40d940188109601d42402c0000440d0340c0d0f00e041d00414100002c105400b040c40c4040c1c1010b2f940182802400100544560f6030b60002401e0020321030300042c110f554805c035102030380c1d1b800e00f6030070341300c04800c148a0740805055140d540705400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 944269604 1250 944268354 944268361
    0x120907030618112b060e0706050703051225030b040b04060503060403081513091e03120f11070f021201150902070c09240e1b09011205010617 62
    0x6101090245290400120b81024001c001007118011030000f20549041e1500c0064019228041400460130300035100410034446e14040f030341c140403881d0005c1042c000d084c4007550210343d208041c0c83e03066244900300417107070b2501c5905400c622612101034502888071012907002d0355068200d240d03d484180c03000c0c000701c102d103010403041d0743d141d00915825501c400001404248030f0310711903820800180c14020f06425072800300d1004080008450001d07a240c80344c180030000714805d85250885d1b006240d1602d050707140e0b001007500380e1079144c4940310703920380c0c01603104050290302800d4a83c0160342c5071039459125160954100c4e03841d000c168803460f011442820722a506010320204500c19010078441941801840300c000e400006081d25a21001c05021520b82c4562294a0203503035030b040e040d924011b96500e121064040c541104002401c2d01d000c1c00303060400d1442600030824070201c0281c50313402034030049681c4404d02e140304034070300d00f480e00004216030010010410742c10160541c1d5440d94 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 944270854 1250 944269604 944269631
    0x303020d031a093c0a0e060417090307090c080a0e0d0f0329120a021011012004090b01081014180408030f01060806010c0204020a051209070306 63
    0x40040da1191000030607211020018030341000425400030884c2c014240400d10500d40300d2807030703a1894800020760f920351800340415400302c44040e070200b441c45050207510a00c4521585440b0b024100400381082c516801c003082141c50300b0b580e02c40b40081d088445003580d582c140c002030062035001c100400c03201008107402c407a11380107154161075540300500707210358952011182400c06210f0780041594405004000c41d40303101c02600c49890700c004000001c00c4600030408090b90681e15648190700060207400141c84596a02074101400e090044039201c4084030980906142c0c20004405401c0c4003000402904000140003501d04240c02040301028030741c01555110300030344080f00030b01d10f04681049002c2294401c495040c4000e00410b005420303052040c0c02d07410082e10101c40b1002c01104001d5039101c070b501502d004042d5890904000d003030400000e01000f0101c03801a004603000035023145203c0c01a011103003140b1800350001128a00303212076648a1f441070001b00e51290901c040c940800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 944272104 1250 944270854 944270861
    0x4030b010b09100f02070f0e1b0309190618030c03020f3903070b0a121112150a03030c0605100b030705070515010902070b01050405070509040e0f0303100303020d03 72
    0xb040060810520000303060360a64086480200e04000c42c4914200482c0310348000340f0220041450319070100103424441603c2401c100c15110480f115441802082203443d00042d03141c0751030070007801d80e03200c8200c1410306401400e1086140300540034541241000c241e4000380000c0c50b50301030b074262241c1405202c0c003282c43d040d8001400009240411406182c2020001c2d4100300711032629041000070341c0c1c280464106882d5030710400c041c030300100741c0b03c200035000999002a01c503540317410021700d6182400d000281c043c000701c1c40355001c400d000180030082817040116003004000e105002c802e40d00d03d0020091412060211a40c0c1d08050205071000160403075901074803010900b03a41180d40365941240d058204500030b031220b2158443c1601118454880c05004e0310300e602015035a00018200780d402500182d100c24003070707440d0400b0866802d6024050302d1180c04125000300c1c0b100a5021171904d480301040803900036002c000709110341181211084412a03100c1d4003070355003540d4030800c05e8049 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 944273354 1250 944272104 944272117
    0x50d09080318272a160b0a0b030f0a1104020310050108130605010e0a1a0f06070c03080c0607020d030b03070e07110607050a110601240203070b07030204030b010b 71
    0x420400580c07002103850003c184044102d400351200f0140c1440007060001048203039094030f400c550319113482c0241c10f2615400b42200348440344152905c041042e204a210441a001404900f03040003c2024140c05070400303c070f00f00c401011550740c1e160580c2c0c40f0b17031911203180d000c8030354224441103021316042c14001e4900c01c41c1d101005000715440e11005491440d0010034401101110000840004031355101e01030107840c014102969500c0e0810844040354200c0048240443d03080d95000000e6840e0a045c5810210644500d5142c60852034041c9a0400580009086540110b1000c4000d5000103206100d00000e41c2103d2700780200c01070503400c45064844554054104800501019a5100748503812040c5450300019840c4448010383c10040144c80305800120001589044568414070050241d100d200141c1555498503203841d080101ca030390005a1920080307030000f00c09009209903162607400080030012440c104030018000d41c09808110382d20601800045030390407400080d102c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 944274604 1250 944273354 944273377
    0x1503021003020a1103130e070203071101030c020703061a011b0506060d02060409050907060306090c02071511061024020a020906040e03120910050712020c0309040207050d090803 78
    0x100003511904030040e50041141c001131250000c41182080c50030001809034021078405200301c00d042c08103028203058003074540000c652090024102003101d020901003200b0090a00081607a4142000d0b4100305040c0d101800d0f20703103003418640145009000799012410260303542c170701d8000000600b90308403070040d401400c42c0c0d015100154490821414060700d0f0b0780010300c1e003414290b071049050152001203035412016000b6040402c0040e4260054101802d501101400400c1007804000d6a80071688903c03800300f074164080c42180f90044041c108041212015602c051412440c68511a942d84c031502c0d03149200384003440242c0000c00701501c00002182e01400b0220700c203408000203900050b14040e80503588000b816014503040004001e64040d440316000e41c0e20b883c0918074200000784a4200701c19050a0802c444103038051030f10284003400f0540180c540302f0108032180f540c0200000c140d0810710008420007440000201d55440c0e8406075102c40c0910741b00d0030340c15140d000d04600048e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 944275854 1250 944274604 944274619
    0x1d0102180f010f090e19110c10020301120213140c0a140a0f05071112011401050a06080c07150c09080d0f1b0602070203250b161104020c070810150302 66
    0x1c091110910150004502000200546d0040745040112102c501140410b0b035000540d500c8040c1c0e0900c0800035500400701d00714190340c034001c101031390401c21900081c89002203401e00b2103510400d501c951a929800d420208440c0382541c2c001c0441c1d03103c800d600c404a140b4200e00103104d540502114440c034001d669034039409080c0d85066440360881c600c2141c00c11400e0503d400c071030311840d02c075240006030400085040e40ca42c0d060048001d9041e04040d01885560805005e41c0b604000b50b2604682ca08078082c0e5184814108000003d40d41e80d00d5a003030605102d114928194084e8072101641c41100983e445903078100c0c02540c03800810114140850000920943c0098141101403400c0d400303032001502e08041640080d050040c100c011440c400341e204200d120901c4a840b2600240015800051601d001d86800e4440c80003404401007150414660289003629a130701541c030b2408020303048914854840e01010780354030700c02c0e4000c0d078081c1c58024038080d8150725104520440341c0240620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 944277104 1250 944275854 944275859
    0xd061403120f0a030b040b0909060105041401080c011b0b0903040f15140c0705041103011409040b270a060905010c050f0d1505060304080304030306090e030d1d0102180f010f09 77
    0x580c0170745003071540e01e544560390300b41d03a0301039403186c2928511440b928400b419003903042c0010001280c02041d00140300942950040c0411040068068132540090034078514400d0200c6080510301241100181290710346018003840c078000001605c00c2e501d0203032042140d2620b800840c2c03581c40c0c03000514000944540b80e2000108040300091081d0300d003420a41c1c5941d51900003050a07616001d0340707480c03050000030042001e103144903400c1c007602808a9000a541c00d1a480d80051040040c09808600710b0205015803d180038402501c40c00e07101d10b0549402c0400c5003040c03002401000400d0f034807542400400e03404c0a1158048a07401506d03e00050f04058150140800406140340c5009200c5031200000c05c51b030741c0e180c0c0918401ca02c90440075681c0d2410b841d008080ea10107600003407a0390b00b41300030060720501c084241c64003484204c400107007503030340044e039a2a03a104710034060400794400104a05070048500020f1440081960200c0300320324038000444100705050000c000107141100c05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 944278354 1250 944277104 944277107
    0x702030a0b0405161806060306081b210307050d0206010602071818050f07060c150213150c110909060415060f12050c090402030d140d061403120f0a 65
    0x1d01d50410f000380100d90300d00354514140c90116156810003640140314600e00d140280c66402840060003140c5000d00800e0300c2c121440f0fa80e00c2111820701001c0403540da51205540b1021204400d81000d074151580c84040d01d11000d84030340c400c80041d9900d00445010918160000528a040b00d803640d00070691680f07011080d00800b8191020b1500c041c0e00c403484045045c40e43c3c01e0400165002e40e01070030541850311450752a1503d5913200c8014441440c0c10342001c50200726540407590007060000d40c0c4c9210701e00f10461194000e401c01e00e02d402d200350401c0c0c000c951013111361418a101d60f54040f1034000003010040c2d0148212125076190380260300140005090402d80d4020959890010403030315103030010400500c0c040d801905110048807100c0041c0a8100311034421100280c2e505a01804d25402003901c1c3c0910211036020721a1502d00448800e24010443e104c40861b40010400b0300e4a5040050030320302c00c0941c052181c8207819104c10f100d44918210388803401da50702000e1401000010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 944279604 1250 944278354 944278373
    0xd0e0a0305040b0a020f06091e070608060f041419060603090209270f15070804030207140a2d0503031c0c210b04111309020f0c0a0803010305010506060702030a 70
    0x110304c3d045000d220310038584040100302481c09008180080c0402c01d8594221204a0f21807510142580c1c0c000c1104006468200c0c4649803c600162400c4080c0070020010401030700e200000015485820070070842e15415262154042a02d40041800307003c2c0c1e2050228140c0e0034031310000c5e600191020104040c0744106802d85403503604074a0b042e00c000e4200d550507060021000f600101c0d0341002c0804508940f2881516600c1241c3e0306200a50b0b0030a030710000d40e00c401c01c1c00b8614080d14240c0e41100c4c55607488000303c0040101c0c18009481c031600d001c10b50941080c0c5e5201103840f42001e8000320360b500d03001c811740c1c000e10742e580e00b000d10004500c80c501c7c000c3c0c03c0c1034100d90144040403000c008404142c200d46925030404801c003245220761101407200b00c4400c003800d100301b00000c0c0a01068420402c1c0100121640b000d009a160a181c00b00b0500038403450141c3e94141c0b28040004082108210245040b203001d480200607641c4e8010522045e4030a400d4000e44c1500b100e141036001490340c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 944280854 1250 944279604 944279617
    0x140f0c010e0d050d050f0702031b011503030302040e07020307021f210b1e011d060f07050619060f090c211a04090816260d0e0a0305040b 60
    0x140003165480c1090395840c242090b00032070000040002851003540d076018000c442c1c20100f0a50184842d00d000310000b03403a40654505500031350198042082c1c40142508424191b0b00380d02140542c05a403450043d000794407a114020082a580c3e00241480d17002100362606290040c0144815090000c04a90b02c030542c0b503001e00034003255010202e056050300c101d00303000c2401c0d01400240b1158800400952840034440c2d202003075101d0501d41b80a9a1110780d4040c04800001108185110b21001400500030320500307442445001c203111040c040001412402041d91544400d42c5050900d000300940d4040c1c020a002c0c04da80040c100160b0000345e0091170040341d02c0c0382000d000800d542c00c64502a400d1039400d8120780e191401c000c02000084440e04103100b04440400c81d00c2002d0703544085c3c1c0d005041d260410000e85810b0705060140c90081c071110718500003c00031200a2b00c007514605900403519940b601c906d03003030326104401c100040007416260191281030801789408540c0090b9032021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 944282104 1250 944280854 944280877
    0x2010608152d040305071a071b020102070302090c03040b0a021303120201020d1d010c0503040b13030c050312010e091501270f09031403100b030429090c01140f 70
    0x1c402103107980d04000961800f0354800c3c1e0303072580c0c0d80080303051003540500382c5002a40c09044280510070600e4204c4e202045441d2900c44448960b02180010303410480345074006034200d855a41000309100c1c554004510039482200c0508264440300315100803405410180382e2803020f131050900c003046d42ca0002e80c5402c2d0180c400980350280314107048043c3c510742d0141c1c64010412400042001e6400c1c0244059403401e841c02034110b251030b490711140d2182c042c1003544c486002c40d601340d00b0300d4440d800140c45d182e00402129901c003007920012620440034032551500305811008100005000305400c41d0401d0821500711699003072418498440d82c54029289441009405003020303800c42e8045e0a0f4014000900007900400c5810080c0c0b40ca0003020f00d0080e07008041080003104110210200103a41e0070180780c4d605c0c0c0c0c1e514948500c010011404d42c08100c0644011114501d80d02c945942c4501c1c481d1050300c0240340c0c241e0064607904500d1000380d125a00520a0801b507441d01c0000e4580308666 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 944283354 1250 944282104 944282161
    0x20136060b120c03060c09060304110102010e0a11190e041506050d050309030607090f060309051005251d011107050904030f03060b0f0708031509160201060815 70
    0x40400181030424822110000b0b500043e450498515041c440968408020f00101d8684a0040005003d0388401003004103103d401c0c100d4000540d1003507001600030190f440403075210880900b04001700001618140d8031034500311190b80c1c035213968403010704e0444100c22000c1e10039440e0350717940c9881d040169103000c0105a0358100000d482c1e131600d13400010180201b0245a031244807109250a100b0024012003e008004508203c02c51000306804202e07041341c60000381c8007491f03107042824400d1170488041d001d814002441000100b40380c0000f661031950501c0b845000004005a440c0b98210b100681030380d0280b14401d03481d501481c840300c00902620240c541c070a8032000001d818100a440c00c1d800200c20303c641c1907015400d4408d210103081810649414103202d070361404981d00c504c420007415200c0201c0400c503281684515443c0031100104a03205c0352601000c4034114100030b420b12001503080010029060307401150207004203038009032a009075a5005440480248038010000f4001c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 944284604 1250 944283354 944283371
    0x904110111030a0f090e040309030b04050709090b07111c030c02160f23031b040b030607030515180606030c0f0a02030a110105070905010305091501080102090102013606 74
    0x2410710060240d80e003291038a019440d02c0380001480c5d015150821444580311100b4000443c0d04070070300a080300d03400034048006680758070b00603041820581c04a02601d080064440030001d08610341d034400c4800703582e49420b01155142895440d44580c00000d040b0200c003d6240740b00f407103a00a418030345200d00448134101d800c40c43c0c0d400a442254480140d81c0b004184c14050002c1500c002640c4424680449000b418070b01c0010707450f01c03514000c84000503a40c026210316a02c60f5040700d1244071004003524014a0600d03000b0300686800c0303440b248030389070f0140d03801d800d4a8114081c05c1c040c0358400c080b050959541d414000700e5440500303555580304080c8050a9a06180001011605c00903805192101140740d809030082c3c0c41c0d6542d001899042500700002e40782d00c111440c1c01c0792024a404200c58947e2034130305040c01c035800216102e0842402c0045841001500100900700e0207a00810032098486d0b19002c4000c2001540c00d00381c2031162031504401c0f54010101a01802010f00164561 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 944285854 1250 944284604 944284637
    0xd0b04090c0e2a09030d020a122115050907030603081602060715150b07120f12060f0f080708070e060307090519150f0302121c05190e09041101 63
    0x801031603c480d400b0000068011250800340a4104510318a000811401050b40c1d1408900c2003c1042da80800010032a07202003d056001080b00e40011340c5000c01030000000343e03c0305508514041c41c0e009145007008981c01511a100f00c0003240d401c489074508102d103007600f08103d03415070300c0140d901100501000300070a40100c100004000b14400c0029004480000885c10110700d60010403842401d0061102260b038032204500844001d16040c0b03500000000c0c15214215250710a00f65646003010200d0f510300440d480c141a500c1e466402548140da80c134400b5529029800781400c103802101041019468092040741c11143c02001d0300d440340d444020503401c0340e90031900245c1c15883c40303801500c07c89281c8140000002140305000f030340c0f410706030a401d42d03000c64400213000300303048003032091500e609100c642068891075040030811072078014001d226800020030b880e02c4216041c0103081103400741540382c240140250426200c1e50355612004030300050b07910002d060068043c05003084a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 944287104 1250 944285854 944285911
    0x1140723071511071a10030311070906060909050a06030503071e080d02041e0f060c0515010e091605030705040f0f050903031f0803030c071b030501020d0b04090c0e 72
    0x740140c884444c0c48110b01e0802c00c0040101c21711822241002d8014014403402c06070001003030381d0301410320001c105010408039140000f150b0008412030301e044c10100388554010508402c0b1150b0740d83c248003c0d00c6035002076040320750b14031001f00264020460308001602c00e003c00c0d4200d024000310903410b0305641e10707070f181180d01000034204c000d94000380900442c800a80244007075505031104283c40c5050000901995600313000b4003060114028502c3c04111082120519180c4902a645e056503912102d10205100c1920241d01500407128a0445040241d89d801c00329040280240380c0d240c80c040c1800000d10100c407200084c9074640e91052011140d074003482c0e002c0d0706d8503802542d403032801c13a409803401403195a810b4540e41800d181044203080010660390000641c800c500e42d10003072450941e00c0c01c824907a50305044e800b4507200006204c01035000d440344030802c1070244010407080041204640071204020060102054148456040004032583c0074040841d61031141e2412844d21100c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 944288354 1250 944287104 944287121
    0x801020d0204052b0308130f0c17030a0914010509030a0b07090902090d0b070e03070f0306050f07020d0e01050d0f05060a1401120b030a0c0305011407230715 69
    0x1641d800140401c95401d0118001c40b20060221074500c2d030b600c10b40d0340000b0000303240d5006800c000070761020680320403071f400030709004540c024030041255600e4070302140001d4040c81917200245109882800408000c0202d0765241f2850351400d80441c1003c10101c200c204000400b810030206104503400360314204440c50016025028621140c40e1844009008011035085020103a00612203040c0b951105942084031070390211940c074050b51504030803140805520102541445582000501085440c110206403801410184019985c44c0c00404911800350f4100300142d00c02d40b8880c0466200d60001440310300c051509078600000e080b03c0d4ac003601c860b06a80c03442079a43e14103000c100d103424005040288040b03043d1200080c03100c030001c0e016508000254040c162112440f54003581c051101503001036010070003281013074680c10900e009082081c8595846200c08d004102050b00a060f441c0800700171b9103c8103030000d102d04840c00c486d000355000312a03040001e04004048001030042c0d041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 944289604 1250 944288354 944288377
    0xa0f05060a0b04060b040b0d02070f2001020c212505041409120304050a02030105040b060f01030b090105010f0302040e070f0815060711030a0f0302070603060b121807080102 76
    0x159080c003500701070484030400c0640707200300c0c41c240b01002041d111206490854803840138241d00c031200120181c0203480fa041c4014020220484180d0420600140000d100e180c541c140c4d100307548403600166551254641c01a500020025641d03062816038010018507405a40a41d120344501e150040e441070702005040d8a14580114144a981800d00c070300305100f0b1541c030301000c2da41010100301e5110100340007013036008000000000c00303108080181e81c01c0d682d4050001c00882c602401d001d0100c0d901950401c0c419050a13142829541c4030740290000c20200416900380c90346000d00541c1c42b5500040242c0c2410f809210018038a01c90858191240c00140c030342081c44a00b8440050010900030400594558509041c00d1952034000984440c10b5001240700d07030000380c500c006890300510107030003000d00040500721410180d010070400100c0300603403018003446854070300e5406a80a4903102da03800008520001e11a04c072101d4101203140c01c048d0076103c80c1c50f1603003421400e907030204600b0007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 944290854 1250 944289604 944289613
    0x2108090f0409051b01051306111c08010303030e0609060f130b0103120201150e16090e1509060406080c040209220509101109010f1b051c0203031006110a0f05 69
    0x44944d0300054142059a02464450300c0c00c44031920b142c5c19051240a0001004000401e07001420401c0012800b03503c6810340e076001c0034183c05e00c0105402c8007404101c001070300300040c81300c031020000344150142c07042501074002a031b19040122a00c40c001864240910b0785070075400c0210b203200241e180030358051101c91790700d000440e0010303003074504d14100815140710b00308041220a03080040720f5040110b140d002020f40e80f003440100c44402c090f4003d0b019030405401800604007000c005800a648280d4a200d0305503200300801c012281c1d644074200c5039410502071030700d1500d481e600904e166070300141620a40c0d200144160f0728602651940950035035140140041561700b080100458241d49034203004132084020040014025898031034103100c40c3e0f507201318040e4012100000400000300448514030040d0a029a6900464148807600e907110b948204415201004482c812914002c91899161408104803891482d10270700d900c89008150360000020894051511014065030040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 944292104 1250 944290854 944290873
    0x1020a0b041e14150402150a140309030a140306030d05090411031609150c02060c10150e0901090c1707090504030302070b070e090106120b060a0503102108090f040905 73
    0x78035242d10481c0d110240d40f101e0003000010f1f5165508000000310300d04201d503e68455000c01e4038480d59082515040080c0401046a40070000028000d062031a985501035036500c14176010300d6100546034503806801155140f0f0f54240104000d2102003406800016458907003001001642c00580d07808403840050000d0340c2d00c49038440c2c0880081d0806403042d9030600c000c2c080180c0743d2016000005d014040200b501c0810341c80031300c06180c100c0007940c1c0c1880000021401d2140030003250103040c88400e000c4012900c1c4010504c90f03511140e5021516201e0700381450410000540d1031010f8801c0b52203001c50100d066000c034051390b80518840e46000d030310741c10549030005172120000e1005080081c0d0441d0707000d11ba40e40815940c1141d00d18141000c5070f445080c060341c082e10710314840d0360300150000307841b0804c9030380140114031410300445038401894488c0b02e100e8044806810140910340186484000706100e00000c020b106401402081a48812804907041d9001c110081d1038581025100307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 944293354 1250 944292104 944292143
    0x206040e011a0a0c020d1122110c0601050d02130c050310090506030c100c14030a090509071205060d0f050c10020a150c180b03100b0901020a0b041e 65
    0x10301181501c000312442c01c2011a01e001000e5056400c4e001e44903000140c044411f10004000401d42c0f09006013003002d03100ca034090307050a800c111882200e0040d06d00114855000c2c0402c0c00d58210380181d0340600056481c003001c0000340503500c40103a80c07060003045c0c40741c804060391103100c650391465241e05032207141c0550884685a40e0358440e410303081c20001040381d103940108503420901c03c210b80000c2a4404408101e03450100d102e4020b18110200030b04800c80c42d000005042c1d020140e91714808001e03100e80601141010540b0a00042100b9242030741c4c00720400c0c1c00031a40100090b0031502c1c0c1d1400c61325510762500b0081e10a50300e0b038021100c044c107c5c3c1881e40e4103080440060000345201e50b90b903134400c18010107080c4410441d41e43c4403120340c00280308111000c000e6502018110000752145000c0596500c25500f03803002002001000903112054429241e020f00b050300500b40c9140300d6201d03418400d1000b001141c079100b20039101e094070701140d1110220a401441c50b1041d8000000070f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 944294604 1250 944293354 944293379
    0x18090f0318040f0c17040c05060c0a110102070f030b07021f0b010e0102061302090c09040905030c1903140318010e0705091302240910030b0f090403020316050a0206040e01 75
    0x41d03081e2a400d140d8a181c556400241d402c8805c845500700c403a4039656410031034401d2440f5000356510840008040b41d08080000d10021980e000d1125400a5460b02005982d1400944110f2142500d040e1080002c40c5031b08107565881034090050b10046410751803603e5240c101c100302003600f40e41e501d405403190f5030710040b1001c09240030300080c400b6003050141c0900300c9c0300551f0002c2c4561407240018035004100d0b01a80c210070f0015000b40104210703880c1040c0c50750029079681c0094442c644400308201c0501030034108054142c2c0704c414415041000c10442da40c0020007440c0c6004200209442121092242400c01d503000070240000714101030400203502c4d00076280c0340c10142a4520140940d90f04520b142640349002035a0811039040b41149000703000390b11820b540f01d83c8400303041900079010b030003138a50b0071003c44201103420082e60170800d075900b064074060b0043e44148003240e44015418409440d00e80074008490740010241c2c00596560300c2500440d0344041b44400401018000c1c50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 944295854 1250 944294604 944294621
    0x1060819061d0709090c050603070320191b020d06021e0937031b050105070b04022106011d1b070303150504020a0207060e0a0518090f031804 62
    0x10030790702d418100034401a6500c1c1c1c180030b20311020b076944016404100c2c0036040c6400401c0081c0c17241341c6134a03000d2800742c024050000e0300b180803003844403105062141b00d03046440c803030800480207000201c550400c8030014407040055003050b0713145d0812409a41c80052885500b48030380070140c1d548070704035155540180c80710f50702c4003402c1051020b04025070760030311805044441d1902580e0b8902040c003002c190b192254040f0b610312070070301c0703008000d1002c041d43c1120f002c0c2aa03c00d200035035aa420044441e0301c03c1380c0b805414221000045001442c1a90015400d108071940a100b01820b04900a040c44c10070f900640d03800c46500000064050321900351a80b22502007a070034488510502c24141d9403103011001401c155640001c11203103080c7c108000d0160002601c00c548074400002e0280d6240d000d4000c44003c140780d0240c100e481d140c1114180c05581c1c3c050082c1301d498003240d4041d5100c01c00a440941e4038002e607101180e449004001516039442a1185102d074480301c042840111960749 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 944297104 1250 944295854 944295881
    0x408010e012f07080a031d01060510080705090d1401021b0c0a06080a0203070519030e010b09160c050a0f120e0a03030f0f121b18080703140106081906 66
    0x40c4030034082402c2c110709070b58082d9000340ca541d9a404000101320001c18015400d248100304259011410300070551000c0c080e18401e65000d0106010309030706072060f03d001c5681c80001036041014004d1410419002034006e44108012086c0c04a4400c205003aa0484840b00c1c03841a04070003c0704070f00a00700402c0d00b80e01c0040d210661181d042550052a06400a150720182900000450b5a80d84200d04852220703102802c880c006c02c0034403000078098101c60950351190740c20035210100c07070b1030400c0c1254001c000c40003203251440300c2c030041036a6904509100f501c0d940501d035001004a010b0500e07010b400341c030402d00513403004000c04d009010a10500645405a0340c503400038400a5089809010619401c0c1012002c116003504210f4010403503074580040306c0d0400700082c0040300340b100b00030030440b0252105401d84021503001040a1458400e008050740030110400102d0400b0110071007541d9040d00207d04a91142500c0b4541548810703194a0000b8140e1880e007840080d01c03801000751040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 944298354 1250 944297104 944297171
    0x2070605100305060708150621160f11010605120105010501110115030308090309130b0f010e0a2c070905040513050d050d150b04080712080d110408010e01 68
    0x450312030b10365a840040261702071000040200d520004601e03149801900c009005a503101462081c0c2c1c051242500e104020100c4220040f4000c0d0040e104050307041189581c42124949202d034003101c1c3c0e06840044c400e00e6568500001c240c0b0345a94560707400e0f141c86140081200d501d131000040c00b80301180140940bc0c1d240010326089281c6909000c0704585e0145000c41d515205c40c40814203512401440319804035100b0304614036440c22b074024031a000700031210015021189001513800a94021070341c0d070700101580042c8051080c0306014000d15920f49489100343d8880284803400394016603141c13002c07031201d0300d04000c1c030f01c0c0030f0080640c010001d88441c0d48101c21955507940c0c411a2003003503002c2c441c001c100044090810380c0032004840c6540d41801c001a40c27054007200c1d41e44140281e4245002e48040840c1c0f00d0291021040716a074407030806072910740000354810081c901202e88003140700c810800010303050802d018140440440c1c0c000026000c082012540e0504241520b06980001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 944299604 1250 944298354 944298359
    0x712021204030f1104020d0f0605010f0503010e10050d080d18120e010e210c010323040501021936050409050c0a151d10052101090207060510 62
    0x240c040503070301101e9101800d00c2c02d406480c03600458203040c050000303030000c2c40414044c0c1c0d044100d411000c1c603041c14035810480c1944030801165001208801800411070820040020002540005600c400c1c46061100c0b44e83d02c0e40001840259200710a0303864010100e04c00c85401201d10440f4040205e01d011004001040da491000801c140d40048003400416140320070310342d004682d4003031400001805640300c0c2110030188051106107051904061185070040d1f02c00c0e50081c0314a45031070004500c0c661448001050481181000401c104d070155001e100e9452545c1c1c0d02c1203010b294211945500011000194950216048111400c0c00d0303402c0d44943c0d00b180c084600144000e464003a07401081c25551070405a2405082140154002c0075408000400301d404203440004018a40d80302801503041d1007002c4074006203281c010b41c0c441c1c10b146418600342d0180e001024180c142d01d00d00044030400c0d042c600071042003640f01c01542e603000503045003004003500c10140e20203050034030020b00740e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 944300854 1250 944299604 944299633
    0x3270a0b1012060509070308130e0c07030507140f0706050c010507020705010936140702010204061409180903220b030105150f0301120605060102010c2106050411071202 74
    0x70a100000c1d298035511340218550030800e0100074061030b00070200541c0c50340d0340a0301170303ea07440318410b401da00c01c1701c1004070b2003003281c2400710b540640e016607516041405589403001c04130803203450700c2e40c41c1c86940340c505400b840602400005003030301d4032b41c20384884e0100703405420342d08000c1501045401c094803c1c416030303030024201e10540b02c084c5540d50300c41c0d4007080d0303040c5611510100103031000d90484c4110900412900102d404000e0b030f04141f10152103607481a4280d00540c010840810880d01000113842c0b282c8002e0f00418400030241010908024410360348076006940e41b200039000010100b400c125040e02004a42c80c4026140103024070b880700c0c50143d0700042c013a05106003c82c151071080c04d010340040d1451003102c040f900c1e69130359680c0002880a0484141268a1424200020000c2d1300611a0a142072010b44072500c071101484441244481810505004507603200717030104035500d5904c10300303105080c82422180d880e8142c0c1401500816030512240866200c803090382200c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 944302104 1250 944300854 944300879
    0xc0d1701062c060f07050a020109061b021302070602070b150621060d0c0f180c020c04111308060103170a0f030915020304080306041514010503270a0b10 67
    0xa40c1020030300039003810b003000900d0600c00e0741c0341c0340705105011403000c0600c200411754206440c03013601c0350341c1c0710369444000b41c60100704000068508801c92301001d0150602c2542d82001c0301013000014a8041c1720350b0352a00321f0304840010f9808102070020000c107512400e000c0c40201c8012030310a070400e06440459070a800c030104803100ca0030542808900d090711040c2102d102141c3c0600d039001019103074050810200064818001100c0c0008806108403009200f00800e1002650141800c450000203100c0501218040c1c12101c000401c14221714800d0504c0500c040c208003000f0700700d05d52550402c01c480703041e00201c05401c01010480c0d00c6140d41c1060304030941070940d040104452215042c03628034200c52941480c0c440340000104410016010003c43c403481d000c0705d080044004000300260440b281d03004000c038805030004410050760241c4055540022400046040c03064641e81020010032440d0703100215a200e1624a010000035035051036002d200848075928403481c021814921 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 944303354 1250 944302104 944302157
    0x1a030309190302180a0506060f190c06052e0e0f190f020901020f0105040c142b23100e0c03061611030315090603030c0d170106 56
    0x1070036102114881c0e040c400c0c082000110707001803120000d49030111060302401000ca988581041c6070900241c1d80d40303070010581c0c01d02007403101c505050100340700440441200400110b03052224070383c5a000054030034040c00303208480c80320405c00280e048030303480c00c110422201c2800b09030060082c18014000e03807000c00c0368812104840c08035140c41da54a00410380031048034499265060810001c61400150010428400b01ba03003180e01441c9800704d42400c80300142c0b40207051200c6c408041000c9450344510842ca003d00402c28400740c0502030903020380c07110104d0440c0ea20300c1201c003281c0c00d10032906540b501040342942001c0255944003003194661184001c8001055a40c100c0712810a4040049040f13446c0043c00721040c81c14010384040801d2688000d041c009640d15146030010407000c4180c034050b5040c1c29000c0b00c5069450704211070100d00508264141c03005004000110b00200421081a0402d4030781c40038460010a03200080f560503044031007800011200d0120700084205185071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 944304604 1250 944303354 944303359
    0x91e0c0e0a12080904020f160506010e0105091b03060102010204052706272e05121203010b300604060527071e030f0c021212071407050a061a030309 65
    0x2d1f20312140b600b005144c000c3e000d10500617a40032120b034042040000e1241e041e6035100c00001a10307a658410041482021144036240074110780d0003200720b006c040040d64019005000260801e40c88401141414400120a008842e039040384515a12400b00c421500040141c0786548401841c100c43c1e02d9040c0f1a401d140c854241d1000042c603060401800c0e1028089445c014102803880c400b0815070010704d0303020b6148a88241049040a1303080060700d04080510203909078207503841d0400369501a00455621140001d02c640d08460625488403000d003d90f64205140c1c203281001030910040f2602a080203000f145944500e05201c6010741d000c4071441424446111960b50b00241158058030607400b02c45910030f0125596031094141c0c0000040c0d100c5002e04210102d0f0202007240e8401c030203c000212400100a014001c0c902c03400b42a0303000f2400c0c10807041c2c00440b13807440041a07101080c10348031904040b91540070044036001b8080d0350304a5014854030441075100080d1248102c1e5060751 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 944305854 1250 944304604 944304607
    0x250e0c0c07030803041b030f21020d0e0a0e1614090112050a0908030702010e012708070302122701021501091d0f0a12050f04091e0c0e0a1208090402 65
    0x801b002107a800703851405510f2074025440307543c3c928000c000502000011901f4035680c3d404e80120800d0461800e11080e0681e00a0450054801c0103950b1a41181607640e00041210b901003141d08000e00058050070b42303084c0d039400c4c81c282124010501e801d10056101c0907001004082096a403008404102c03007d47d10001078a0345412480300000d160500000b0190300c008010408850340640c0f00c9214210380400a00501800000303c08811010310742c0c0310221000300040a001c502c078040500902032003401103410004029041c51180e4000d5031502c100d03a012420745038484071001da90a02c03442d40c01e00051540032040c0700500031050b014002c81d501c0617036419500d903407103258143e0300e18500d101c04140d40041c00b034540e503181c0395a06c103d02a9413031449140380d41902c030f10a200303e407007141c1726040d1142001d0400040f400034040101c0007000402c100100140d500c5858414180e4420301525030981e8101d031482800070326506540002000c08100d045d1401148803103040f6a02100101c6005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 944307104 1250 944305854 944305861
    0xe1501140705070e18071a09030f06161103090102060414010b0405010f091407020325080d06150e22020715090b1612050702250e0c0c07030803 63
    0x261098003401a01400d10f1080881c001078440c4a101c000d401100f000301e2951a03a50380c0b00c0925a19001c92040541d0f5000d02c0e280224240c8140340540060000103080d18000107000500030700c0c266091b070780c90809a802c820024101500302c1c6810520300c9403030010310b0500601000113512140c00510142a0f07904095428080020a40c070205809134010030800c05940c40f203141d942c4c1107456014140c3d11920b004030032265140d107000083d110703902c194010f40c0341811040451041d502c03900d982c10008005540180c00044c1083c02a200720880310070000742c042d29003444002d800041400c1c0030b06018041c1d01c0300743e1649810300b000c2e11032000c1c0f0f4031514410854800020092247c2d0360007502e00d001e202c1c07a54103d460960814030b4820f01078650040b8985030a26540034a42030010508041591071181e007000000c6a081154400030a00550301c0d162a0404200c039103221204280028400114041c810321107800c4259801030000320149051902001c072040d55001513000c040c15856012001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 944308354 1250 944307104 944307137
    0x22050a0c0e10061d060f0d050916050306041106120114130b010e0103020f0409090309030501060b09090f100911040914040305041e091b0f0309020306060d061409060405070e1501 78
    0x440b20310440f14044641d41f880b505800000402e010384000d10f603030161220750724410120048910680d200200600400d4449a44030f905641c9510446034001340103208000e041ca103c0c18802e8000d1501c089a44210100101003015060030030007603251461602c007100405903840a4200f03500b40782800e0043e138422500e44007214070f010f00c2d8441e40403603040001d044205684205aa000c8078842d03c000c0c01410740b2403401c07582c94080c4000c16900041b41e9000100740402420200d500814161010402e2584a01681050b15003c018242c40c100c40050208002d19075407240008c0f03025507000c0110141480d540080c400e1160f44152090000800301b00801800b0002240e0b0007001c18600c1082580c1c400b411060740710014007688008541c0385680c14134118001d00a4410480d07000340603081e541d69910800001c3d00c030b014400c3da0542d541d00300400052080c00038260141c4500c0e00103010740e1401d4644103290150382d0b0800031960b46200240f0049a2054102542d05502402c0109104030000c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 944309604 1250 944308354 944308357
    0x1b1407020a06021e010b06030703091538030307060c1e02011b020d02072102041e050105060a090306110c0d0e030c100822050a0c0e10061d06 62
    0x8020307521050090300010125000981030108064000389240c0550110880c03c3c201c404601c84e480e0842410400030360070b240300e0b0b880b4000030f52054454800051125800c00c040711910200e86200c90826002004c00c0810010000c0075625065861005030103208042902c3c0d00824400400e202d4445610a65140c050714200315100c4140b03d01e5030309445040c00c002d020f0007100090b0140010f21301c4500245034401b1440c1b0781c035140d8070740080c0f103e240380a0442c00d03003038410b115101101030256402ca005a0740d9005d80c0100d5010408948100300780b8650705070896206034040c0c1d1003400208001c5e003d4680043d19401282c0d003007440042d200015101024252003940e54549503070003a88132407074015030080303042615804c05804071020412460244101128024082804101000000342c0100c0c42d902141d411505001d0044051079416943d162a084402070f00b00c4e90982d0b01c0b05d0034440711a4940e90141d01c090015000306009281c0807000c0c0020f8005003400d080d09005200b204016180c220 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 944310854 1250 944309604 944309617
    0x406021b0a0e0702012304082b020f04091107030c0f031b051c0206270f031219050105060d0b01021f0e07050303030c0f0c1009030c060f1b14 62
    0x2d03150111480c02c0c000084c000c084030400f40d41030030a01c82e62990340b02c1c0d0f0b106029100c0c950100070303a454000410901003070000400d541030000c13090b0040482d600c6c04140042c0c95403e11146c542910b076400c0c050850250340b40d0102c590100c20701804a00c002c21b510030b04892855801180c228428045405d00301c526404445403000c3c0325000e600d4103010000006000300f8012031044d0452100c0c03d1401080340c640c0e809480008481d914407041c03800146207040103944d503480c820103d44c1542c2499240c3c030b04680100318000907101c440c81c01c202c1100050f41e5500750340483d12a04002c69030604d00000c8480c0101c2c0d0b07000e40c1150307546041290a03402000b0010202659a0101c2c5000c20040701d810003034289a4440552801401c01c0000d86040010503240500419a9940d09105500c101d40f02c540c0c000008079083c521810040c07448444040c86941d4030300d130181d907a004c0003025034207101040e02c007000c2c1201c04946c64482c0d1201040e80c80611400743c490240780031ba030720400c03c50340001a4000c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 944312104 1250 944310854 944310869
    0x1121a010e1509070e041a0a030507061101020705070b031e010306020a020f060c160f06061e05010512010501050901032a030e0a0308040f030c122001020406021b0a 72
    0x10010600080c44410103101e10b407200e41100078024403400380f221090050340e5a0300800d071142034030381d190319098010705800a052550401030303806040000e40041250b5005465a400100080c41140c1e8002d6841c6c00540c540f00084d0310b0101075075130741e070743d0382100d8441d03000054030100c0861401d064110a4003241c10340000c0b425040d50b101c3c201800258000e04405015101c0c600b403803a04118081045449008140d03d4542045080c0c0401082c103868400102c1d6502910400c01e00010020301c00c05c0098040e4130041420101e10580842800d03503250050780c14460140b109107508041003a041c1d064820030700c0c00c030751501c841c080142d0280c40c070310f00410b40c1c100c020700c03604903031181d008502010722516607070074000f460030506000d03150f40a828000d170001d520080003d010811000800303840500c00c0c41c1580b041c0405807110407402440c01e0400001800b1070110b119100521807030130300703495995070007149050704d0300c03002030b5a945200c0103449086071510522003d0b50b03034001d80c600080102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 944313354 1250 944312104 944312153
    0x91504050c22080105070e0d080706060302030303090601091d102d0b03010506060702130504150204060c1b080c040e0109080c0d08010f06090315091b03050708060c030112 75
    0x1441c80201d1180b059000762a035541c600000104405e00c0b4000c0580071b104050302034440c05080d6100c10000da4003a0300c050b2145910380c00c000006880400043d84204032500140515505000b031140603102055030320f07407000c1501c083d02494148040b417008076011030048001116070290900c4a20000007221603000590400740301408162260440007510000b20004c02069860804210b03031030003200e10207500f003a4080840500141c442e0f1041da002806450000c0200f0100d100c85070a9a2094106000080c204800b190070020881410300c0c21400c444015042281813000c0245d03a03100d0170040d21b1095444100300101e2803002e6100c884025080011550b80c1c2d08d845513503507545c894508000700011000000018481c2810030290241d403050369821481e1455519101c1d03080d41c401c0bd010743c030140d482995000207924907485040f0480b190000041261941c10110704142050740804a00e8211004002c405640c3d14122810740305440c8000c207503020241003100911541d6143e40384a40038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 944314604 1250 944313354 944313397
    0x313020d080415080912070807060623040f1406150f030106090f210b270c010e010207080c011107030624093c0504110f091504050c 58
    0x8002c41803d0790421a8650116645880c0d28240e0703968034000005500901c280312403800215421300070406036008a42c00f080490f00c4d00604e1101c0e100e07100c20440403c241c0c200d8845242880e00800201445024042007a0200380701101c00c0d500005000070301c581804402c0c8110320b0648419280a4200210035a44039a110500901113400d01d0107581c2003040c0c00d45000509003860380c1c00760383e0060314400c000720424140e51080c1d00300d0b030701400360130640c0c4c081820345d500c090b0402e810400b102c840ba0000c0000001d10000904000081d40000e0b045400c184010b000d407040000fa11040490700f03280095000550610890601085400c0180000d00706414081615442008204182c0c48461000b41c012340d41c95042048031080d070380d0310100300302c0030121420040744d480f00181944042000d0b195145c036402225001c4034400c0301e040710b06122600701c01d0002c4c14030301c90182d10428181e40b00e506500341601c28460100344180420f01c45d54841c000500c0c43c0800c5020749000080c542c010540868 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 944315854 1250 944314604 944314619
    0x9090501020405211c0905030f0c100c020f0d05010209091501081e15030133050306100905090a0209040803160504350a080d0507090b0313020d0804 65
    0x6210340703d05842002c1440707188440d422060019140d02c11180010075091210302200081458842100070600c50480b9000403151001c0c440818505240c0015003c1c01d44108200500356400400f503400704020300031400010385400100301e01c100000c42d107100d540340c41e030718000b406481815201608a0205002d10136802c1c205055401100b0007601d0307031211030b039608183c50500e480c031101c40301c025500c203008200c03013400f014141005448040c0001c29030300c0212020030102c0000818501108040311013204300c10304083d0061000c0d00c0114054892420044143c13041d4407194025840110740e1035001c80c800403030030003501c8000f42c0d029041c01481d16207401c007404590001c454036068031058040341d00215100d88100c405542156060001d0303041c1510a500c9507010038080808100420040d103c000c440400c061a0302c984140961681e0b00008642c0c001030700c030041e1048040c00340c0e20304140b02841a800a803075006e4180d0300c0e0290700c81442d000003100c0c0400d01c40b0207424013600007000304094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 944317104 1250 944315854 944315857
    0x1020f0f0a020c01030b181005030d020f011a0612100e01060f1d01082217130b180405060402090d03031b1107060f02030f03011214010c140a02070909050102 69
    0x412042e003e40304200800401074054400402501c2d612074407588100c1092803021415507000744d203090708407a41d6912000481d20705a4040700c0d40c0050f0740078070350300c0c00341e10401d001c2d4031481c0d0200495a0b52017a405d1000c00c00c2c50080308030124422100400103980b59103c00745c0480281020900d611955a580d080a0185403602890000045074040b1240064030900311582c2008010f070340d400c01d165103c000034080d50440c401d01c0112070142007a5030002c104001540c1d0318030070710b00700026030f80c02141e80d042103090071a62112a10072420b200711442c000a4008a1480480170744010540390394040003c3c000784600940b05a0188100c0029814954103900c98011030517640d54080ca443c02499040c1c0d141d554018003680c15500c5000103004c210b11032107602803450b016004403410292003000000e10741c2c000340c00c042002104d412003407090040c0041c1d03c00e08800290020000300441d03400080c00e4820040301d03409800c4000800203d101d2080000ca13000744000300c010401e409007850024080d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 944318354 1250 944317104 944317117
    0x180306020307210506102c01020c040e060f010807030809090613022d0c06180705100c0204060b1812190c05040c031107030e0f06030106030203040b07050301061b0501020f0f 76
    0xb42e1540c1b003001a000c2c01100307280c2c1010240c022510b00540c0d25103440070001c00c1c8296560450291488415041d00c0328001c9051545c03546000c0d00d914981500c14042119050307000c40982d0b4000c02d0100081262141118509441965952b100c2d95402012a080e095100001131b0503a20015607000d14200010002071000018412502e10112140d44c014650180d030000c80d1054020748046511220307801591506080341005030344c015652400002ca102d817035440040081016044030380b00314505031144402400d10001d8060500d14000e01c03d0885182410907940204078018403005041404c111001410203c411814502e04c001c1c82c0002070710780c00c2c1c0300d424019801c150100d562180240a281c11200b0020708080c04c0c02115241154a55800407140348c1010203504d031891146c607a00700441c040c3ca8692405031341c0e418186454081030000400c0c8004000052005003c045e51280c02615407010207454081041a5401d046009110b1103032103258181c0006108c0280c030340020050f091 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 944319604 1250 944318354 944318359
    0x1a0a030b0a050a02040f060818010207050f010c09450c020c03010513020105030c040e04030e120109050606010522030501150e04020d060e0114040506011401180306020307210506 78
    0xc2515040007107004c1e80914001c924500c00c501006200c8144540000c0d580903141e48010031244510030304036400c9074001c102c203417019000b07441d4605210f413003402140c00b0811240345c009c81c818074264988a5007072010540720f2640c0002008040d02d03080749050032a40c00038102001590301e440300c0100c00104000c862101c054000c542e02281c4a2406114203445017000195110f03007445598011501d550004000c04403924003800082420a440c2890602c10f41c4030352610300041041d60100082c18404084403c0541e040121070700000b0030104200ea0810020700744192590b2401d50350315201a00c2200681540c07100c20400028020150017001c403584000889044c0c4d103486488a80e030749442100d020b504091030740e00c0100002d54a5101c8003020344803100000b8081040c01c0c80380001c08054030155581d603c14030042c88502d100740044034a20809085c03840d0404800141c2103140812440058541940400000c811501400c40e1a002c008000c00011300364030400c1c0b50000400040d5941c50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 944320854 1250 944319604 944319611
    0x1b08070504060e1b040b07050705280918300801060207140a12030e09010602030c101808030708100909020f040c0504090f0506120c131a0a030b0a 64
    0x80e80e030800c0d104140c2640c1c240e4410410981d901c031860002c80e4480e6a240c108400200400500340d2400b10140c20300c00d10038006007240c01c1c40e100400800c00340988641c01c3d101d11444240c07100c0c001c1170008001702c0b10940c05c007007070b030242a4000d02c600b803d8140c009004504580800c030500003919103c10100a1011413060a0569205003102c650200b4064000035a100d0a030901c041021074121011814009000c11100741d00c0e460b400090100130301c011030110b2280c0003030490920b4059000303409400244025810a290100b400c1d40d19034544228250301540c075490301c0c0c00c00410310085012103400000c1035a581c1407500307009290000803a201680900e24040200304112140074654020703070003e141441c04200e6204105c010202c0c000700c5002c0c040708210000e074840c1a40140060b01004400004071450600103024502c05546000101c035041298816102d5858003125403000140080000d0301d100c005840b05420014000c2541d80310354150400070410580c400c01a2058a04038001d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 944322104 1250 944320854 944320859
    0x7080106150c031d130e0c01020706030e0a0f050705060a05031e151905030d0f0318021f0509090f0103050c09250c02130209180906010b07020d1b0807 66
    0x111034039012848001c0002e0f40b000c3d00390161412a0310000d0b50240300400016100203014150006c40d495903400f1041500403060a19040da014040c58000b0035150a042c4500310040c49003035111a0f007508020f000c00c005035441001d0100070031845010b010302401d05c3d41d80304e181c160b024049800c21030700c005c5103015452840042d003000341080c5000f40200c0800e64080e01c0c803002008006004641000c1e0340c1515190b0005059900308801e0040041c103803540400210064002000da5a141281c1c0003540c0150002c034005880340301c0e021260020030510306410f00b0004004545a00c500080160b001804200b4081c42c1c0e030301450a181264031a000f12503800ca80503040c0240c0c14001c48030882844028203100000c401046485100300d080340c035003a036411a031980041d0701c41c2e803a0900205520350103d584640343c10701c001d00d17107814003000d0514080ca1800d40030480c1e640c6014041e021f203692000c42d07460110745408081c440201e0b88401c0281444100c2402c040c18a01c551048169074402c03081e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 944323354 1250 944322104 944322107
    0x20910030201090b070201020a06060311040f052a190302090a09201605061303080606033705090d030f09020604170a0b040809010e121506120708010615 67
    0xa50040303035410303121000a140741c64203c9980780c1296030241e0550007015a8800082d03a54031074400a1403042651051810a03c07003480304880040c90003803985458807091190619100c0d002100f03001c0c2c40076158040c18026400d24086010f00001602d01150070100c8030031252309074020300103142e801d9902d00703800c1d43e030b0b0451001a10340070045510683e9107031503c816040400001021a0141014100002c0009a40e0346107091804c407142d4228059090004c420541d100f00f84980082e01101e2490070360804442100c00c10721200c011210018071466184016915580aa0000c42049200700001c0c51f010031042d80b030b1116401c521000a18180c0960740c1a140ca200d087c0c0040d8014045504081c10b04408502c0700d0341c1852154014810018800002a8803588140c030030742c880c103011921448040005041c100d110400b1522a824262645004800024560003010000e508072006900c0c2c11000c00e5410401455024140c0110310380410041d105402610466008540405001441c100c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 944324604 1250 944323354 944323381
    0x812040330091115031008010905060a1505060708070201020f1603080906090316031b060c12092c011706060d060227090f10150509060f03040209 64
    0xd00d0104151107032034940307101941d0380c0b000410350322a14801c241200c800d000240b0702c0c00a5036000032102d034004100305e001982e9040701c600806040000f03001410503652019201c4400a145080d42c60342e9a4442d00c100f0034411076100200405013400380e0b0384031142071490185e880f440007a8007520070803450310044180024549542a64204091550b500b035548118030303644421120350b031201003406500100d50382405085e1007070f001c1001c844815031452a2080003205104580c010b00c00580d001007090a030000c1c10130320b01a42c8000340a070811104c500984494590340c10440b01048903032055210744a403015054540d11084419215581c1d985840365010801b0a40c41c040729046100418554148040c29481d540c0c4218009030822a8a8a8489035510600e400c48120402c0c05208001390800580302c0b50031001346240079801e071900b44a0180b450b5180d00c45c00300e0b0912090840c10b125072250f0300781d401503078004164596420607246902c590307400a4070142d114001721000f040b801d120301c0c403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 944325854 1250 944324604 944324657
    0xf01050102251404230123030c0f0d140d180b1603140d1406010f09030b18060a0e010b062506090203060f090c0103020a08130204020708120403 63
    0x40ca0060002d08006002c9880c0c143c0b4500c6070340142d1a40f0020114030b00e00041c000198140c2d14101d0440d62501003001392000f103802a0707210b13508004501c045070b900c0220340d02a81c0d0600b40c42d0386100d5145c01d030114410a1034108042d12800408038540941180403888000c5a0400d0b030300c002d95001d40c43c1c00615035003840d01c60707040851820031440345040f0300c9913084c60415000e800c081011031a4005641c4c074960206a02d502e00d159280c1d0b4503060340c4000b4512540180e020310f08a040b8a034468800b804a41c498040605508450000101c03110484000e100d108019207081e0b4800d800d00c47e0100f80942590b0310034905c40d5080c000c40300d00310700f8408259110582102a46040258404a2190315024100c01500c00580b5a200328000d0307101040124010307040141005424509945441c0c1008410100035041500400c03100c0c0c0c1c969480700b100e0b1340220b01000e0f40030f42495180b00003402482280310003441a1008183e600c03201110f014114801c0e07000b030f00d03108841c1d605c0c1d0028045800c901d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 944327104 1250 944325854 944325913
    0x12031814010e0d0c0b07120207150e0f12030708042322020f04060e040f050114041d060103050703030f080408040b16060618152d0e0f01050102 63
    0xb031407031186520300b014030020020301036885420160388544d010b10751503000d094150b620512606100c0e01540c2e040159600821001c110404560442c900062a002503050203900c5484c1d12001c0d24455a20401d10b114644440b80480b175550a25140c20212900b141c8643d1004140a00240c4040d40108285140f003070342c010a4000b11304082c00c0b000c6d040c940c4602424001c103030b013800100c05182c80b440040000c0c1c0300644620102002c17810410040d16000f101649660b410301c8010032450104c203a007042c080200f2540860707100580102904c102d521826440e07590303c600f0340004140000460a442540d00071740d03402541041014050b00c0c2c08105980003800803074108810804404240058002c104000724460020401600e800701558401d40040101d01c40c640e242d098005458459560254040c031808034800b85080036102140000c442250402e01460217401109401c072600b08001d02071220074803249061090420207a41d40034090b4a01511588600d01c480a105820161950028 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 944328354 1250 944327104 944327117
    0x50108070530221205091810062604021e09070504050307060311041e09060b0912030c060403350912130e060a1203181401 54
    0x964108480d50350004900942c120420000841c1c0165001c2c511896207a031101e040d501420300c08501e0b121071a42240b2681d1890724100098009500c082840b0064066401c002e500c45610801040154007549041c6c40480b813280108500142c04044410039204199595030f406a90214034100c0c0c03030355405c440302c04041d042d000680103103003d0700180c500e2034140b20080340a4820300003040106005271a644042132010a00340301e542020019540280043d140038000104048183c1c5818890f5000f9491400c0c40110754803070007254908008001c0c45000d900300051595403108246a401c50018548190b40c1104070841a03040001a26802c00c4004007034000d40c2c985640a85000d440e0042805400d401f0440d204c003102e5175044500c4129007000864004c6241001c005420920f04e40041241c1d641c0500080d805166100504029980180c0800589481d40c01c009040c02c0b0082e445000091580d4200c4010160702801e8429032000c0c601c91900b10542b00c0300c034054900800c040701c0d4009a403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 944329604 1250 944328354 944328361
    0xb1003030905041808120612070e0f090f03040801020c070e090d080619030c0f0b040b120a060512240105060d05040609050d020607020715052209240b0301050108 71
    0x1400d60152540c401d134801d1003040002d0300d940e0761901c2e8100700c100c0c0150700082020814142011559807211100b4000900304c0c2d941800c0f015441210042d0080030700c0355420780000c1d00c01d1803c1210100e1a081d18080784c1d2160399031000315000c4c1d48074010307420741400792500000700d10302d80000150181044401600300c0d1090082c0c2150068001001e05a0004181517002081c1c0d652001100141d80102a01d0791141d007400364102d600026940003100c40d000400082016441810544021203000075108120743c54240c2800041c0c201a08040d5100340f080140c0600c04c5d4001135482e000031421a44038040b280b841c0b45049000d5800d2040d2604810200601c0782c5ca0302156024560084c03045100240001e52600d610303107000500c64000300540d22500034007468130f4041150000900b144000c481c100c6000c7c0c0e00007084d900540e0407190450b01742c8946010048001415040a0007402400300070101803551840c0110100514100a0400c40d003c0230414004107412641a54810f8488100649 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 944330854 1250 944329604 944329609
    0x17090a1b060e040b0d0303091104020d02040509090c2103120f250e061e07240203100501080601050c0d0801050a0806090d0809070e0103030c120f08010b030c040b030c070b1003030905 80
    0x100c08c48211213000180403e814183c0d1144060700803500c142c00010b031681e08060901038100320141c0f58200980c08a0b8150215039582d40161340940d00d820220400b44c030030b51625a1460041030008000044280d003048581e1040c07280c03091164140c01d684140c100d041ca6294601d0311505a01200000e034000c4038100d95050107002010107050903070300c4074594080c1c100340da011500102000c4881240030700c007000c440c0f2a400c1e0000d94a05440c02d0071469801c2880900c4000300302481a581444903400000300075a0243e0151828502c180095481504020707000a08102007400380901c500c489682c040350780000024440d2003442090000c101851480405440c800402003204029124620010071a40c915103c1c250082d44292203801c00a0818680205203207080c4101004000c0107494191040e680302e8003a5044071592080e040da070f134541201d078500601c2150081004454004103106a5048410080440d180280c7c1481c01d543c4400c0200e1500312003510014000503404d2a003400a807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 944332104 1250 944330854 944330861
    0x120e040b060a2309030a1101030b090c0304030c06020909150a0603330f08060121050d0e0420070506280f27050601140117090a1b060e040b0d0303 64
    0x200e08150443e8103212058000038907240c00d021044840365005036500300d103540c16014691902d181261030b19017500c1c00300005003007400b0090002e010810360f1080d8400f4001d080d4129541c51102808801c80c03032525581c284a19801003d95a008a65410b000983c0324828850f81c9644022044942c14200c0300800c030200c0c1c40c020284030b2020440b08400061461030703140c00c0c90000e00c0704030054100c56240c9800103002107400341c2d22103092500c01010f0400a4008035a4034010091810f260f00c520a0910214000308150034019250b030107407900014030300107094090202c0a100d1403c50700c4542c1c64010360410548280e00305055100080d003460315601c0250050140204440d100140d442d0208001803146800c0740048211020220414028000f09004042c0940015100c440782525002e00003020407200220300700b030420f00c0d00046000a84280900c02507103400c4903100000180343e000d808041c944070300c203801c00f240c0141d0341029203003414003c807074a8903001000760000c5442e988007503024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 944333354 1250 944332104 944332157
    0xc031006080613020304030f030b01020307020a0b16050102040b091e010207050616050d0305190501380a051902060907122415060314040206090d120e040b060a 70
    0x12242401808190040f50301c040c510890099481640d07880c4182d4010713084510104100d03045402c20440c0102603216605040103d0b103050390455503984284128042040307580c00000c0055000103070024803a540c040141900c8001280c00501c000c10410700d2030f800c20361101c14640075030400a010481442d00320040c2041070b030541c2e24154009a035982e082e01b0190b5559a09004c08e40d11400d00c4401f0420301c0240a00b0b50001101304020750500c41c0b5081408858400c900e40307101042501c1c144500e211880340703c021000c8064136140d91551601501980105030b600801c48440320040309000d10000c0c4032402070740c0d000701402c0d0a074100554480e000f14030b00b80a5035100e80e0600c00d0300c1306018001e04e039503400344201400210348a000380034102102c0035070720031807c040c1400400b642148e00241c0258000768102c1d80c55a4401d444030214652100300a006090301e540c03070a880d030145402440f5070050b24000c590400c041c00e10102044400d0090250a000080346401400400303600c411080d01e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 944334604 1250 944333354 944333359
    0xf0203240d1208070e040c0801051203090303120601030e030301150f031d16140913060b060d23070c0f0c0b0c1501050a030f08090604121a0c0310060806 67
    0x44a500d0386840c036006401001c0308000991480c1000409030f84000c045c0c80b0720000b114140000301c4143c40c0141440018015184141d080c80030020801500b0070440c0c038030950140031b590f240c8541981601042404072075071400310b800e000c40c0c0c003c0040003008507070585031090030700300b03100b079038540700311034040300391440c138091650b240d048903890b140c092040160082400c008008861101940190402d03e030391210019001200211940f541d4154640f80d020f01440540307141002c50b402c11101500d104c00d0604d40207040000d180d46074081c217070813000745800701c03020032032241e07080112036401c01d44115080703c0001c42c1310448c200010344080582003440c0c028000803080725254004d4140a03844018400c2e8241d03c65503400e25690062001c0c0c90051400300d489014951540d10341048200c80c1d050020700c1d072311000801d0b03941070751030703000780d401400c4804407102109140b4500503500d0b40d1501c0184400350700050000320060881d2045074440c40461685a404c03030f252072801e5405000142501d82d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 944335854 1250 944334604 944334619
    0xa05120604110f0904080c0d050c191b0b03010602120f03060616140d0e040c0e01050c070906150e0d111c0f1b080c090c0d0f0912030f020324 62
    0xc1c0700e55113503901903000720301444403241c1d90111412001d180c070010721011014401c05215034003510f003000c18003805c1001c005c0c0e000382c11422103140101d1000c00c014140b00034610b0240e004208454a6000355040c0c0c3d065800319419800e011007003c00070701406584081c00901000080d690f0f081030000707400d281120360003591030440981e580340c0080580b088030194642c04500c40041c0d031540310424001d404002c0c0c03030400101000e084020203c94400d0310182c1031210004410f001e41301e0401c00200100001a820032086071500d0b20003200242c04040b100c00541001b0b0012280d140c540d41442213141d0002565000700b900006000f07100030460003020b180385c18040d805010a042400d0302003018411051400c102a14011001203000142c005529903403014500c04d245442e40d40d480c903040011410070a4031140b44d0150301024080300500040705900f0001c1000800c803180d2070901b1001415101403009241040300b0f00102d020484a04441560413180c0f450b540d5806138004184540250245 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 944337104 1250 944335854 944335879
    0x60a0b01050903070312200c01030e19111509130b0a03051209030607090e040809040e03070303050108010b040213050f032a010f03050c030f1801060902090a0512060411 74
    0x90030113103907a10660b181d4030002c0407280140c0c0e2180000d08800e4451401d01c22003d03071315184e260b135545240510b84c1816a94174440000740300400c20b41440c2840655824140300f1356280071281503840c9400d080c0561000c82c030342400d00005009807070845078082d113409a0303030303600400040103095021003080d001181d8074808804500c06000f034800003000c0401596503002104141854017600130050004c02c5080c03001801201c0c132145249412a40000d100340d150111640014020444015985e21031b100000b01c0c8810160180c10880c1241d2551000300240b07a003071410f1000f070788211040010100b188072014801351405668080c0d240c10007808a641031481d070010700c2c3c1c00010343d103464000c0c840408102d08056902c02d8280320316110500d070034071843c100080b91070740502014003001405070b00c110014405030200912030488412042c0240045561440300070029171004021034081c8802810220701c5041c0701d940000d8000b00c020042c10380d55102e1710340c200c502000d510310310b0303002c0800a8003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 944338354 1250 944337104 944337109
    0x111190c0f080a050c01020c0306071206230901060809210f03040305040801060501020120071a0c04030c05060301050a060f0203090406031a13150b1912031103040305060a0b010509 79
    0x640040c1103400028a01c45400d410054544034021417000e0440d07000158045c0c3d1518003150b0780d40c016906003808145121042400c0c00608240d40201c260b030880d200e90100111307410400d510f1034840035070f46a00c0720b9890f000201c91404040b56002c10983c4014002d00d04007008020796003507a500d41c44024140100c0c2c2d190700b8280e1740192800e40c0001d00105040c86500002e104e42c4000b02400d0001f004901007020b410049440400c1e41c2084065001c86c002c018880c1000c5000c44100c1d66001103106483e00e182d070100f458110740010f4030103007400314000c10303581005030440c1c0c140c4a006000c0407619241c54411948190710400050450109000c803220544450150101031485420005480c0e80c20266100207481c0c001d00c024055085080035001150508500004000b21078001141444d40540813805211060110030000440c0400014001c0030f202071180180d4032035500e5134a8200801c1c8256900c0c0a54040605207411000200f407401d041c40d80007000c1028181402401d05030000300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 944339604 1250 944338354 944338379
    0x91c050706051b06041a0c09090103110d05011e0c020c06030604050403022b0f0329010912110f1e010c240c020f0f10200a030605040b0111190c 63
    0x10106c40140c0c42100200700c1d81624640181c0c040d880e81213680c02d1400090008040350030610028000d014116841481c40e1074284900440c2a0064024400803980c0c2174899140c50780813056900c080d01e0000314034901480400c085030700c048024202c1e801c0d03460304803c0000420000e80700b20154481d0454408030201c0c94103103190808500070b49011164142e90010300560300448200c03040501c0d00c01400f00c0b4001e040955010b2507880c2e2990050409104016134012040e40c0001c8980c5407902280400c00003500b108010081e42600c0944d500e40070841801440d5000340d06d00c50002d800707c54220303541d5103e06010f140c014010790600e01c0c0025040705019084a41c080d403000341985480c060200b00f030301000311840310000003004102030703604190190345551860f010981003a403a083e002c001c902c0f40f0301e00c2403000c03001481400c1e550114064090020060380c0301c0d0600860911008611560040411040c0280100e02500301c40200d0140088520b0a0400444e8a130352820000f29843c2c2d00800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 944340854 1250 944339604 944339611
    0x3011e020a030c0c031e2a02030f01050c04030b0a09061a040515010c0318090c05031e010f0905041a090c090a050127140a02091c050706051b06 63
    0x910059860401480c010282c90003656040103102c034503c00207001a0303110000340d1490704440c8050303010300402202210700403a4a1100b90081000b040d440081d04500e0a4209240340708a003102c104041259501d401d80302d0442e40d07100025802d00c410004240030141c0e640e4416014030002034079160668884048a454981e041e000b0074000d05480d40604080c0315440d0020b01118204003c030b0341010008008100404c401001c1022070f2445030402d100402d0944042c01d44408107001c004000c0c3c100801941048aa640319100700c8006401000e2240014505803000e61424400c1d181c01c100b07a500c0581006030080f6902070b0030003202c0912042411940f4043d200140142c40140f0051040180340440501002507151600d00104003240e1004441c4100c200a0324010581245114286004040200c415000a5a030200b00204c4403483d50091550300000c035918020000d00c101502c450002c0d5101c0107202c0d50041005104080c00707031002e49041d10100481d0f080080e48410241d08103c804d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 944342104 1250 944340854 944340911
    0xb03030d020711090f0a0207110a032103020421050a140708070e130311030705010c030b0909010b0a030b0a06050d0c0e0601080403090303050f0c0118030e040b0a03110301 75
    0x46008010403000380ba10241541d01203404d41d03d5420101c459507600400030307088110150303000401d0410046ea0500c00794001000401403032859035a03044ca4113504c0c400b091100c0d030408201c0000c0104500902c00c1c4e405035000d054602c0000c800d03400211022008101c2e0a4806219040c840e01c0001d00440311000c4040d56031000d0a041031a08071400c0c40e140ca1030b0408003c01e2101001c000580340320000041c04143c140c40c00c009428494480d2505500c51800040d0040d424410f450b880c4a0700b5070068212003500343e820341c00340d507600f0410031308a40c13908094a0348505884420070208421424076500072a90640006900d80d0f1440000c4001002820844501054200411040d604d8500c965030040b000c1c207254245107400c3e60014600c0825000c003c05120001c1000d405030440441a40c1c80a8100c00080144800c03441e05082c07a0100c400c2d0840004124520404039420a40140d41303034048081c00c000350590a6a68280411180c03c0305a5019035a401e601e802c4184003000c20305184048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 944343354 1250 944342104 944342107
    0x507030f092a051f170f0f07090524041809020f090c0307051e03130c06030e0c1323010306060b0301060818160605040f1e05010f02010b03030d02 64
    0x9070449182d503600c800b9042551486500d00b00f026403600c3c0c4d2482019206041500110f070400c3c1010740385821407801e0344901e0b41c0310b041089400c81c004c0f251a8000c0e00c4002e406016940c80b0101128903030035074085c46411080b8003a120b81401c4c00ba202101d00c3c013201950040c140740c0c488600e0092a070780c40404d0003017035858030030450a600b8803941c1d0310401d200540307900805151400002c60a403001500c9241003040008000c9010b11041c0b002a00c00e15408296590304e0034200300321241c00320144001d40d4602d0400000240c4ca0340248249a4600e01c05030203000c030300180f181007062030701c460b00140c80704645900300c2c10f40f01c0d20020364042020741c07051110340da15411400c1480c11164581c00074000110200014481523800691440c2c0c40b0702241c45815011a00498190820b604254202e1031131801d1400424000c2c0c000000d031098450702091400740e150348100c0420030b00b041c1d0b0401d20007284d01440a100a5105030a603603142e841e07500000c0b4611043d400400e1459102100c000c42042d1b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 944344604 1250 944343354 944343383
    0x53a1106130615050a170a080d0501050405160801050d0c030f060e0f0c01230706060308031b0414150f13030309050f01090905101a030901052203030507030f09 70
    0xa05105040c5103100f1880d0f6070015070f0910000c103540b244540120340e080f8152003842100c0c540d0800001d00c12590200c4955240e44802c1e003c030000c0c01c400e00071148164106800600b400c0d480c83c00303580c038400141e0b03140b002d0707a4a08030910075401c08580301a9071980f02580007001190412801c0d0b000c8920411001491100d004003450509050b0102c52403660021103042c0160381c0e00c60714914001e400001c0300d40c03030b0501c920341d05006845880382c0140340c80d003014000014800f003540a184681c0d9075150859000a2000001500c2d03c628001c010b019a081c1d061180c0b2801c2103040280401c16602030f00f17140560104040c4071135041041c0007114040102c20910400d54003c1a5030002e11003642c809010b8800c050000e041d07903145004d50408203070384000180044080c686403070f0080c8150a41c80801e9508010f004107581d104440d40103456003000c020481c4445810216221044009041e1240000340c3e901100a04000792108040541710020b41c88500054410026098842c50942c4508030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 944345854 1250 944344604 944344613
    0xa0302090f0a200301300309050a050406031725060e0c040c0522120606030b16020304090207020409020a060e01030c020303090309040e070806040807053a110613 71
    0x8410399400d080819507410740040c00f0400506490545008841d81038030164120f05c035a0304403600080c2d0b24000e0b55012808403e158104a450082d20400c3c0c560181c0107840d4003c0c032042d526140301c0202505800c884400410140304003501000000c07000c620500c1181c4208100d60040f8110b0907585196a001494280c1004128224001406542c10702800d00009409400c9018407404104200030750300c240f4461401c80310001000e07040340c648001100c034240c149100100680d000c2103230310030301600101d01707c4589002c01031041000c50707000314549400e144c506806500700703007012a0001d8903034081c14016034071360a0280203031016544440e86c29055030001820f481c1e5070080030080d50810400c2c0f21000001001310380c11440152400302e022a205050240b0b051410350095516025034018072040100f034100a0200c41d000f101214082140075503c04282031908482e0011141c0b5030701400c54904550341283d05582b05420181011a81d11252a04000d41140c4020711010045044030401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 944347104 1250 944345854 944345861
    0x2030c1b0321061f1e170a090803041e1203090515060a3b0402100e030d122a021006120b09030d2a0e010804110a0302090f0a 55
    0x800c6020b0307180c2c480d8108a804100b0585041407410f40c0e5030fa03c181d07101041c5004031400032000456a0216043d11040000245201803861441d80324251110110701404414041d814040d07410181c0d03507140d03840d580d8600c41c480c0d45003403e00c10324003000400e580100d85a20481c0403120240c0d00c01042120300f0b450040d00b048200d40c41c8520703040c410342c1404000c1d1241810a01650340d8461a00800130444015661890b6445504840c01055400070000d0480a12020f805948203035001008449445000d5960000d488640360300f42c1e11600c5003480f0b241c8180840e41a0344250b2a00248040c907201b40202c08034075003400d41000f070001c410008182913040042003030f10708824008021701400c001c011513194100c2c81028200c1c02040340800c01d0b00c08284215004540314200c200882d16503401c90b0202d48031001810900182e882e00c50b0601d25003d40300020180d00142d648190580c2c0341d03640c20082411199803180c00c2019100301000503121005018000c08061b1b1118860340f6018030302c2001d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 944348354 1250 944347104 944347147
    0xa03021312050a03110a0507090b0102150f1303111006050901090207030c14030909070f020607030c1b1106040603020d18170d180609200604060302030c1b03 69
    0x10400e1590820301007032012402d0340b0360031361500d003000c1480440c8115602e80440d8400141090148400014101e0443d03400082103407801e800b130304e0034540c490000c1c150107281180d0848048101000040b071007404410541c4169102c1e0820f07000755280081e41c3c5103402e112151140b982d030742e99001808946440001280105000c1200394a00b0001c0c0d6801000d03c5241040200400b900310348140c060f01303050040d15030241001e00505131a10740342c80300034140035500030710401600401010401044c841c0c010003c9500040c1c0b01c0710452404200f03e00d03058814100141c5400040c3c128050f07440c4c1d2a400140000c202c80d60f00541c54a0215070042c003210101e0340c00042842e039980c8a000051191001d07a001c80641244958a91240c0c00548014040c801038040d14802d120040c3c004101407036008410b101e014038200308000310042c4a03401802d0b1100202070340701c4c0c0309200801c5464425001503603c9080f4030412400e021143ca00b445200c80c01c6805d14640703420126030005c115940c200010706 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 944349604 1250 944348354 944348369
    0x14070b010b1e0a0507110a0806090601030605090c1f090b0336250b0d1e0b150a2001142a0714250b0702060f1e0a030213 53
    0x290451041000e044d5215004006015900200324a005c0f5640c00040c4002840007106540081c6400c007149a22000301340000c88a0b82c1c50003012440360503000030800401100a0701c250945181051955117010040c0034035810402c00c03000210700c1e0742c5040301075406844d1251414070f0350101e20306e8032143c1c00c400810345203882581c80c28000300c644c0000388103425100840e812800303407044100301904256440c0c02030652400009114102c81340c059104c007440c0d904c000107000340625480f02220941c0d0369070082030303031081221120b42142c8010340014006010740781400100017640e0035032010390009412008104c0d940d40d40c8400b00d410801000c1551102c0f909210140e58003040f00300780c04032181c19000c1c2d00c0b5004042040c0d4200500003d4008451f03140300d080b00c41204122084000c103c54804440507030440c0c2e2200061281036a40c107451005500a2013241080100005d803001a004951804c10329028a0b9025018010070710090415040b523640250b1307120380701c0581c160030780005c1c2d2102030b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 944350854 1250 944349604 944349607
    0xc06020f0c011d010509061e04140906090106030b0f0405010b030f0f10360f0605121f0b12010f0c0e1f140c0604290714070b010b1e 58
    0x100307100d81c0383c50464404007003400c0c03072602c1e0603605020807114040c08101c0c1004c405034000032401c800c0350f030026000312525268071340072107180304050100d5400140d640700d070890b0300b280043c444640a80c11034000e4144c05410040d400c071281d4001002d48200b84d2191025034000010701c007201c8001d2748180d911240e451140c51060401c0708440821080c144101501c90800b03040e81011440045d450142c908408140080048422032441c030080a103c15501481460300c00001540e04150548034070306200840a028481c62840342015031001800d04007100c0f83c2e031001043c0c1c955443c0b85180c80d525100000000303100f07c0180c3c0d464203d9170315208030410700007a034881000b590343d444c3c2000049000c00d0040c3d00b1034503503500e096a81c50005800d065255901280c203210246c40001d1292141b40221005040303141d150b603007000d0111442d498010860401e40c002840c69000b1041100524840d04241c1c0c98110745440b840404074003a00000320003180024001111100101117000552404080303e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 944352104 1250 944350854 944350877
    0x70906020d0e01210b0102010b0a12030c05010b0a080f060a140412090b19080a02031027050a06080609070609090e0307020a06110d030b0d0803130c06020f0c01 70
    0x1940e10036040304404100b0800d1072000b05542d110f0549540d4064480702c2c0360301c404405070034040242c034514072843c0c019803070f01c008003601e031420580030400c8884c000000800c000c0a500d044403000002c000c02d85207503481e20441100d41d02d803440d088006000c940091f00703c040c440c58440e03042080190085440c42e06060f040d41c0184030030251140c2055100c0300348000e01c050440305542e6035005500c40741c640e181c04079034485400c4202d5882e40e2400d03008e54403a6110b5545010312003c0380016280d8070003d1203101014030909081c0c5545a842e8200c1d031a0042200802080c0c1500396541110410001500c0707041c104102360b010410560007043c0e80000e04000e07402c1c208000d08503031385449156802170325034000c11003001e0180103c52501e40c0107041110015191400a48104070004010310140710320140046041e01c01d1007042c3c0310600040c0995408421034640c01201d400c0946004e0450101c011140700054280d56072200616a0350050800300760b4180e00b180c00c001d4100c2029052009107000c2c5d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 944353354 1250 944352104 944352107
    0x5061614060f0a02040303021207020103180503222411070b13080d0f0e0a12120f05030108100209012a050d02030a02150c0906041707170a0b041103030409060905070906 74
    0x380d5809c200d0320034a95440b810b036400101c0c0a03180c800c035804401d06609400a05001000c0b00030100643d400b078410840c00d0264460021403130451040f02e84186000f4000906915104502c2818424914180036040c40c4c800f1030301c0c00c2c0300e11079001e0128510000388400303071806003490703100003001300c80d0183c04001208071000d0308074801c0c9074604c000c03c81e40c90984e09056440320340c0c0f44068004400103218440d030602d0700110030854108000041402c00010031041840740301200e06941d03081d400340c004102c6600e80100603400207070010341482428800001070344407800100200d44d0a804010845d1a0641052418445034150000c1190000c00081e044150001400182e11400030640440e9966142030040719028901003580d0000300010005607815040541851130036a080546030f80e9036940028551040a00c0700d20710264000e0300703d100104035030264955001c1c0c001c40251a0a41c8010700283c159030087e0040d4811507036131341040c0200359182c07103503d40c015686d040404655040000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 944354604 1250 944353354 944353363
    0x9090b0102060a0b0402191d0904020d3e15160f02060403020925090e0403121b050c12030408070f030311030103060603050d020d0905061614060f0a0204030302 70
    0x2c0803d9a202c0c401407409480300c0c1d0442e41502e64050b08115044001c1000400c0032070740030100d54030504a220705500b9460105649801294010402407403400a40e60303a515041c01c20511140e01c640d80d07009001e40082c80170b960181861580e902e5a0369414280410210507034802c0300d040340040038442006040b000780c507844001d94000300c0d00800036240f48002a6607104582000750400041011301410003054401d03203007012101405121315500716030341140c8140d074078821500d50032131030404200881d001c2c503d042840960b5000c042072814010030001c1c285800c0c01c8000000400014050490b600240b0000e01d0001010760708a01d18140b0362140d03c07184c09683c0004d00200c085250403001c140c003a41c4145505622030004548035070b541d0418000074511403000f900e0b107009038454418032502c0480c400f8007138481c68450b16040c5003032505002c295004005c081c400701d2600551071022402488201e00c80c80301000043c401c07890300030305036104010090280d4800741d00501c801e2002a03001704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 944355854 1250 944354604 944354611
    0x414060f0709121728080402030a03350108070e06180712050a0510090c08070e0a050a1707080d0518011b0b011a0c0601031b18090309090b010206 64
    0x541008110003800c003505102003403404440e10200018a1600010301602200c56601c1038442d031608041740c0c00c0003a540454202c0b0000e603d9004845104006800303800c514460000713501c0c0748010395204484072040c10305c40491480742603507120010402402c0412040300546802c070b6141c1100c3c00c0c10000b2650302c1018850740080002c0c0d40000803031892148440c4035240300b5480d018441801c05484000003030070705540e9021030102c03c04010442c29024040c19803001c0c0c083e501d100142d61118821118111800d10050b449511101d000a4075513071201d05a01400c0c04034011010f680b81d2164031443c01350740d980829141d82101c841c07004c02c1604207080d1481007400403c11041ea003443c00048400c10940c1c0504c0c2c0103550807103500c0c0c0600c0f810020b89410303512206401d040364041f0b40c51240f154020301d0b94801040c0d11003001400010603280550903600e0740c2c842030300841c0b0384961030b1420080f80c0c0d02c40562110f96500d00380c400c0c9940480b8581c0100b09200c42080000e8030040000d40307443c0000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 944357104 1250 944355854 944355869
    0x90f0c0105120a110712030f06050f041a13020d050f0f0a24060f090e0c041a09030f06070801290a090504050c1c05130f05150414060f0709 61
    0x3440002d070145000e1308040c0100500540e1550b03291051b00e0105141c881140312400024541409901000d00d28899217050b0744000304224402c20b42c001c2084043d2000d500322030407000400c1b00e60f11407521800700c140c03100104c10101603195034407000c90384106c5800074241d1242c00d0828040c0041040d0f085080340e0016011100810811000f007045400002405144003a2444000b000076010fa0f200c8a440d2000300f1300e550701d11101d0380e150280d0310403040540302105405000c0000b0810042c04042c0d0703100041c10f0b032000704c1c207004d9203500280c14480c003176030b49114035048a000c2011580d400b40c81140508402c01c0c0718001414506c80274a1012010410342c40100380000300340d2038090080b5001c0005060042051105203030401d044103e5400030740302800f15510b000400011050035000300c92150400070303042c8402c4000b540b00c80300c09d4801020290349501404031550f07400402000075a00c214021000c3c04a4092410700003442c00e4401090055841160130038400d1f81a0301000c00300454204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 944358354 1250 944357104 944357137
    0x2903010b120907050a06050c010c0306080d0f1403010e1006030c0c060903210605030c0a0305060601140705030d1e0b01140c070e0a05041b0e0406050a0b0612090f0c0105 74
    0x815110500c0d000f0142c01c02d541c815458100041e4071503020b4008d044203207202c5c000b800f14040d96803040e01658003500401411780c000b000b0020095200781c0700d180095405181101c2414001c0c0d641f00c3c1e41c1d0b402a04200c41c0718030224104202c040c122a1a4001000c4a281c100045002e810005240c4038440d0300080840d42c4802030380c2c06040c8100719a4001c81c4520f450f42404081c3c084140c03000b80440d100e00360180c000c0aa240b116840c100c0e2004c421a034101000c3e107015520040111074220101c212203a402d0b10500148000ca002040581804089440005540c2c600c02c150341c400c80c034000e84010001d908084e40704060303076440501c10800102c3c60342101d4403040c114884030304102d0346401c08155942800100840c2c5041c5400540c040e43c01000010305503081d0800750f0005404601500c00d030b0840e00c5000ca0b00051a0745c0c4190b0740480d42250000d420355a410000318a64031166000741c0752200801803103018042400000c400031341180050a86401150028219008030030400801600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 944359604 1250 944358354 944358361
    0x9100f09030611070b0906011a0f031b0f040b04030c0b0f0d0f0f0e0c09060315070e03010902040c0503040212190204090501061509090e01021327062903010b12 70
    0x56a00580d050305500580c3e040c046e2038148241a6211000d2092014040c00d020031044482d0210741190f0740001d17450b001c245965207d0140b0f4807030360741300048004c01890400011909000d1a00900060031a00180705d03603071480c60a1801030b050384d0f604a0500e03090100070051402d0910422100400c80c0c401000c500700e803500c0c016030018080c406104503136a08080740403d440c81d0204010800e102c0450703030005584c0341c0105050303443c400c0a005447d20340035a40420404c6005441000901c1401000492002400d5012a0a45288240403008164044140401c506d0305050070f1075070b10702301401020685031060b806032243c0100c0310064016a0f4500410051040a41103032019000408081c2d03442c99074544000c025582d41d21521403000c0c6405903006000d1b4060003229200b01003101e29107121030030300301c0c80741398010610358003046401c10070b03426004681d0500500c0014080902c02002c2400c1c1040c5e4005580400900c40082100800c01480443d00c4c0005445544a030380f0300c0c1c0c03240c2c3c1d074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 944360854 1250 944359604 944359631
    0x90402011710030c0b0711010c05120708190c0314090109030602070b0105010f0905030c13020c101d06090d030504080c060a02070c080c0a18180809100f090306 70
    0x400c1c606698140d030049003000b0801d140100100c080380d10a003501341140b90340e9801549039000380718004000340300c0c66280052561169408008190040041d101c80e2240c0002c20700080d407103140e01300c0740d00d02c0200d01c0f0545110158101813902c85642031400380020a0364004010742c0d0200e225400044011139441031991080d001ca0011f13513400304003155500002e052980810348248a42c0c0e000030001e001d08400ba5200d2031600084400242c020300070756604104119000113a034040c0780510343c0c2030006022900080280b018009285900010820100110380c41c40c041c40446c2d581d000d81c00f90003417020401d00005e206481004600c0c0c00600c50f02c8038907086009106031190080725115201c02e2101050469004140f001d05c00c4800000081d56030700f18988030505101c80070717842054414104208103421504c07102009068400140c501c0e142c49010303180f2004c000301901d240350042100c1103103003080844240c0d041c01e0343c00c10a84803420100000c2028409000042080d40c44901208041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 944362104 1250 944360854 944360867
    0x2150105300c15070501270201030b040f0c185603010e010504110d05060a051e2403070315050607080c120a0c03180806092407090509040201 62
    0x1001041c11022595440c008a0303540c0040320b06617115443d02142d50044101401680e595800c0d150042030043c10940040d07004001e22001c1a41054072006440d1072100c140c482d100811300c3c55247c0a083c58104080f400c503000590700150000c1960104074104000e01c0e040222007141c1550070001c400007400c1c04a24541070301002c002c003c10303030700316180d0003119041c014505031000009403007856a40d034000c00059451090141151282c00c010348101000c040d00560f92214001c0c0180d121680c1c2d61005c205c0036080061910030100f240d010b650541c0ca418401c011090307078141c001138001c1c20138043c000d101c2e102c00340501c2d040c5951800488000c405840b40d11004080040409032140d02a0401942c594060890030000740507116031591a80e01c40c0c03050b205240c01c4c2e5600d0144054650fa82a1018020171860102140b084e1000281007101008074a204070714002c0500180c00c01400c0710b00d240e600107108202c4800801342081101c91741301003440708880f001c445511042e181c600058564 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 944363354 1250 944362104 944362123
    0x1b030a06091208060604050a06030b0a0e070f020c030120070f050607031d0106060f030b1305070e03150f07031d0601060203250b06120f0a030215010530 67
    0x8030309001c01c00c0c0a1003124900200481d01549820040e40e669004010301c2d8491070042941c81800420f0070300115101c0d510021003401c000d0b080780c0001c0e48075402100049002c807100c0d4009441401e602180c194140410200a1410b4009202d40304032080001704400c90185465243d60740802c40000740003422440305002e40c0c00c10f0655003241441b090040290003008035050f0311403071140c200c60034040c051140c0b07401c841144c0d5035201000c0103107400b200549110641964003010080c031030042c101d140c0c0b18840c02200a80c0326542c00c0c01205c020302d0b0411003040740c801e00d501d41c08020081e0042d098602903038419003501c0d0000d130107050038544a40266041c003a00e10b00c1e1180701c001064090f000070040415031410000d1003107410b1100c480703401c03003440d841000382012000030204486040c00784a450310314043ca0191011140c410311582c0c0b800b09285025401a0300100c61742c018103840c1c403045405005d003551401c08107205411901801d500307108072120002c2d00c081c1081040310090003081c13072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 944364604 1250 944363354 944363363
    0x308130b0103050607081e0c0a1101060b03060a0e0f070f1704110909011806020c032110090905061807050a090207170304021806010302071a090f010209031b030a 71
    0x30296100e0402913660303c3c0480d188000b1075403250201721420340860900b00a4118403001002c030390b0b200c200c075090070b0b000307500c0010a01c424550440802c45080c002d03c0302030304900c7c50164507850400100301e03592459920008600c81814148001202c0d50320303040d507020b609030500c0c00042000707203c100d0b01c02c1c1c0c14044258800e24031800340010030601a03c5540101030484140c100d5031500b101e030500f00c034a96096445c1e04088007c1d41d0380041e01540140c03026000d0314040d06d04107110081003403a040080703004a0610002e00c800c100390700305051409005400e641800b0050194144d54656071424080c241c14400701c2e6505140002580821040c40500340250405030500d6541e4000c10107500031a0007190881480300d034124280b01b01030185ca00c00c0741c0090681110701250296a0740700d82c40a40442d042540821200c0c01254050520504040240302c00e1030403031424000e440d08065499403d68642e900405c1103810380d136000525035200b20302500b00c003a0710700e500070006031809594500050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 944365854 1250 944364604 944364623
    0x108150f0d030c0605060108131e060507020601090e0d050d0f0b130914010c0206160201021e0a1701260109020910230102030d0506010c0609060501210203030403030813 74
    0x41c201503014000c00811403048500380242c0d12000b00540d0031a4045804e400d03001c0404a02c82c020800000303500020703c400006040c01340c1601c0c0c0b100300941c2c20880c1c2c0d2030702581c00040100b0041c05c09114400c90400d1440c050650088810402412407082e000303018003c6440d68038030a508034103a40400400300c0b0040c11241c1d000003d90182028001080f41a5038400c103156100300c050a06000300c2011034182c0d4081c0000b640c60200d086208804881540700f190360900100f2000b00c20072103440c0c0c4001c1c01c0d0381c2082d01c8540c07041c0300600044410354071007007024002e4010803604010304084c1d14140d85540c1311180d04e0359039641080c018908014043c0d4020001420b000c64030286c400444256180c01000200841e007044001c3e001521600c9408d0041e80300b000781c1210b41000b0b510050304000305141900070718003552104000e07103880d16007c2c0c1d40580c0d954010040d040d20081c010500040c107501d0410102540d400103030b2640200d1102a052000d0000011003211041000141555011180a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 944367104 1250 944365854 944365879
    0x308040504092423060a030f0c2c07020114010603020f2512020a050c09040611031e06120304030f08040b0f03061804050c0d081e031f050108150f 64
    0x54090032107548051000c4428500203001c42140c4103136244505009082c2100f0343c0c2c07a540d5400e05080601303806a948100c41200843e00c05018000d1450005000034050810315503000100040503000c3d1500042da80b600511260f003010011080341120b01604005032520a07000b14a80030b441007004240c400c3c3c04020f0702000c1c9511811500e0b500d0740c0a00321299000445075001c0ea0b4070014054050308031b070310104628006240c01004c0560181c4141c0340030650101c2a1450300007030b00180d40d2040305103220b11a0403c60099140c00507400401120308a651091103104130340c5900c80c90001400d9007140081500c00e10a10500701c4000304208403c5994031004400c00b244907400a032172261040622202a03c2051505d5050b54040d54103c000303441c0700350203801000b0340000280005c803140c540521000710111084070000d40e8000480e459183c0e20300c1c14940003c243c0540300040c06056020603024807a5980c46081164080880d203c0e80031501e55100015080c48805d100190340102c006502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 944368354 1250 944367104 944367173
    0x6160f051f02040801060603060f032006030c030f15150f120103050304140d02130c02151302010e100c170702030307080406030c0908030d230a06080f07030804050409 73
    0x14800c0351329071802082080d490f4802181643e80c0391042200c84144039030103001207415243c200c1c001d418643c0800c02020011008514250400c0b504034580c01e0000c4100a40e969009804035800b40a003120910740038a41c0d000140c5801c0d48600d10300e00c80801083c0290701502c0c0a04444108025203510480382da582c0c90042c7c0e4942c080d00400300c10740b041051401c0300c3e040210301c1c02a003135402001c0510311882d030f0300310340b00501325440180210f00c82d2035080420b000c4d010482c6406001c1088928910003200e00024220080f509840760050154200800c0350790760200700c0d1601c035541304080c54164046c0c1c0d200c4032002c0c011140301035810f0100180d21010040110700800c125511518180b0406803a6481070307a5550b114410080e0030341041045110a444036400385500c034070f2404546c194000030b003074000c4940030202c2d6608811a40d8075020b106a14080240307007d10b42c6240001c1510900b03503550400540943d1050b1801503884071200c0d0f04110000407010462b12600c14010102c9805062 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 944369604 1250 944368354 944368357
    0x12070f0c26010203100b0904021903050a0c0203190c05070f0f031e0321020f0409020d0b030d0512130510060501080a2702041407050306030c06160f051f02 68
    0x41d050410203008070740158070078042c000c4c1d911481655040201031482d1020000d6580d214100d840d900650070001080c5414226081805d503400b1540c00203070915107485203104440701103079640107540c000d0250035105200074649400f650583e01c2c2208504800e85803c0d45440816003012000c94450400402d01041c1e21904504403130013000403400905002c1c83c3d50f182c610300b105014000400f0046407010f01440030501004000c0c42520044c81c01c04442c0d03012100d07400a8000c08061500020702c003444080c03a0054100200e012000340481d50203104e40980341d0301c00c82800d010004084800560a0f0388001d40b4061460340000c1a01d804030102620307a0001c2401707000305804180b0b50008a0003940491050700460707150382c00d4030030110b02070800300351034042c0c04030f0100c0c4e00c00d0321344403c0d110030200021071134090340b81d6441e00c83d240d0074a0400c16041c89480f50703001d80115014000a01d01d0780c07070665200101500700b41220100746481c10000d040c00c3c200440c031181c5002c1c038214007130440441c0c0e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 944370854 1250 944369604 944369639
    0x21602030712120c0201200c1203070209010f0e0112060f020f0909090313030311010204050a08061012110609030114071709060c090603090709090f0201030b100212070f0c 75
    0x525200f04480c10340f4040c2d070030700114a0081c0c0060040400f80c044002c08840201300680308004850f04001418002015240b5003c22910203410101d0701c2821400c0101b8414050652100c400100e81d007003c1402201d10ba05108620803045200c1c9a032060007055400441454a5900c0541da10b441c1e090440d03806603c40d0003420b000c1ca040c10700190a030000030050320102c0e5425040014801e26680f0100c030800c00c000c400c490f6955080000040070b5441c600c0d000000c00c01103014090300d2402c0c0c0d10841086c0b005900c5190b0036003190f00e2480000e0701c0348102030007544040340c409840d1140500400c0c014118149820f80e4024003106004659030070520016191600403a0001c80da9254074142e0780b2840c05841015411106100c0b000380c5207800b1016541c0101c1c50001c450b40d20340e0300c0104200340d4641d00b00c1555043c2c2c140c8104019941e042c0103407403120100fa600480001101100250703510041c030b03220803042c000270031400d040102d080f4031400c02c25002441c20b40242d85030018482c1090b0b044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 944372104 1250 944370854 944370863
    0x303010e011d061e03120d0c120204080319021005010b031506071a0402150d0b0114070b0f07050403050f0c190621022701111f021602030712 62
    0x5102c6080740e41400c40700e00c10040a0320907040040105800e003042045600e51a5140c02103c2c0101b0507250307074502a058907a0b07102c00208142a02002c00b409001c552450300c100940100018040c04800001b140d2a200c1c2c0082c4107401c810340713090120f0601034039002c0c5048007400c140c00055044c56907809140520207658003014144002001c05c0700c58407403920300a0607442e0381011000350a079003d200c29445400a00208040c01101100c02e80c550300c1004d03040303111641c49828511039640808840400243e01e04e24600d00721603a1900c81c40040000e100c1040c2011110001e486240310308107650066612030101c441c551402c040700d80e111092840503600405d42070007c502c140414144030000c450302c03134549410341e12001e000103942c000d40b0304620307491540800042d00344920f004100424481804502a07084031142c000510403010030580034500e5106400ca080d0815880752402101d207001040180d803050503098010340500e1901020303526008034203002130000f011010f00c60040d48107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 944373354 1250 944372104 944372129
    0xe1302090c0703140a05070506040629060712020c030a03023409052d0906100f27021c05130f06050601110d0504081614210303010e01 59
    0x1c1120385103040c0241400600020494595203086940100051884030b440d4a4120b240c024161140c518054050300c0460b02c8940d10b0503141d06030400c00c6849000d0790714540c0d8142811144500062031401201c402403c8032020700481c40d45103000f0403403440c07016005020703645c041c403440c04e001e922180e1030881041348240b007000b03180924540d4001c040142d14000b020028160910180c4c034020030b0000c11030008278000c00b8840c0c1030761046038503070303106800318182036505440d002516909284d0043c020144550300c46009100c2d08144095403820790b4500b01e4010748490000341c115149102c80c240001490b4400100140b05854462410b150749803040c038240050784610003800d40054040c0006000e2200015044c00020281c1d0030a6801000503d070405034803c0410a45d4204441c03004200049080010100071100090000d441618040c402e40c4e44041e1510304298039203610944010f2180e01014020210034200c1d22051900701c1510003100d88039038555407804400c003400e004541c1c48411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 944374604 1250 944373354 944373361
    0xf030d0b0303091f0507061514030604050c04200a09051021020d0f0c031e06081506190602070906080d2010021210050a08030702010f03060e130209 65
    0x78000103c40c1c8541001d000d0801400c088819103e49246481500c02000b03802c2011201062007400b488980514170124505030524004040b20040d608506040c0a900203000308004510701040030b1028080598010a00003071400107000c00e0201c001190b07881c00702c089045907005a02071044030603940152116410007904090540d284000b0035a140c1c25910016580c800c0f8803469009450310204120000c6049110072546200f40c8a1000440e0006980c03400c103015800300c04103080312280c1304050304114441c02d000415480c0e0218110740900380c8402c0001c120701d0b07110414421034200200b402c14200940b01c4038029194a02e610460140d0b07414000080340328000401c17952440d0542d6100c0d08030804500700d00440e560002000320405000e40e1103c101ea0b8001400200340c6c2e02940f440c400003910f8103403800084041d403030b00880c1c05545110300034020048000200c403581502424a0307940c1003409082200507040a030040f048030b00c004c4080c0040203000400584543e80308440c00c0385281d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 944375854 1250 944374604 944374609
    0x30409141e01030f11062104060506010e030304210506040308010e1b1603021e0610080a02011202160f0506181f020c010b090414160b09130e0f030d0b 66
    0x702800040d00030424000d441d0005010030810310124500a0061030410070741001070040301020580003640000000f04110410505d4440d0310391004d000d080103144102800c000c02d40e64080d50280d5103d100902d20701c40c3c800d6a64241900160381d0002c21a0503d00d001e10380144843d8080c49000c1c5500380090204252007000381c070314401c03c80032003100c1d42031888080b848602078098440581c00d600500c0ca1580801100c5281413400421070310051056080400b0001c040da80580d00281e042c1c0c1150b0b02c10b40040c0c1c0d20469240c034803a014003001da2100c2407052000c0b5101c0c8902002490380f240c492008007084400b0449512404048041035190300082e0341740707600c41004450150a0400703015030105040713015030240444540c098000075640e0642030100d1030440d004e403019200300107541e80c0a04010000c00990148560002c0c00a0101e07250814000300d074090220018492002c21090440702a03a542c409070005401d40b080300e48441024082949a501030380c00211000d080490144260 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 944377104 1250 944375854 944375911
    0x92a0306010c0609020f060408071a09092a0a090e10150c03030f1104031e050c060c030c0106030803071803021003110d0c0504140409030c060b0303040914 68
    0x800c01078507503901c070342010341e1140010709031404100d03070084010350001650f40310701d03010344050214400140240350602d9603100300b4940600c40c07503160441c10404408541c81d1501e129401c89845148885160503c80344034254001c0c0418640c04414041000e04240e03510061820494034003d40720300564440640c04449580b443c0144910b01d04540d180400e02c5205144100c01580645000205811038000020581c0d00c1c0c43e901c3c407440280440e052041c85203100403010712940c2000c65441c61040380d40da540d21511380d05038042c0700340e8021910344814481070040780c0c104401071000700b00c05a00d03446e04c0c2c0e1840c2c00903201100000c0249034511400e90764001c65000b0303a40c00404041c030b100403200c4120080c10041c4412703034001c0d00078032002000301000d02541150a0042d100c558844d81448001d40b000421840c4551080741000707d01000301c6d401c20070004c20150003400c081480161500841c0c95480303590301140041c0c0c0740c11650f80c00340b0b803803c2c10340d0f0142c8541209036407184140c0030020500c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 944378354 1250 944377104 944377111
    0x19050921120d020708030a15083009032409070602060f0601020c0d0503030103022d011409030709061d091e0a020909010c0305070302030907180605092a03 68
    0x11036022011903074050208202400ba181c184410140c54450716969148843e0020340e0050b00d000d40f210391b48112040070101d00c40103000b07030314010500900f02e403a486641c0c0c0d4916080280301800703401a12004481841144c569440c068100d0714000b01c06e0900b80300410b60341c100000020240c5001c94175651003c100c490455180394001c1c00262908071840c00015405007405065218090b194451521081c5001681c03c2c059006540c4a600d1401803102015100002010f07034000819600b00340c20203c5e001e4914400d00f071802d02e142120500669a4074456003200641c10b101e0303400000f400882a800c804280c0301c603000700b0b0110061560f212030210f030b01540c804440750032080796250390f01017400c42048084c4105048030120551500400e1b031844041d00e00101036511000b4040ba0150180105504030f9039a180c00c5145281c5809541d031104224020007035078004259880e080941e054001d88090715005240d00c0076802e004540900985a8450044800300380354142419a03a000d42620720 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 944379604 1250 944378354 944378419
    0xd05011505090f040f090f05100b010906080402030106081204091b0807080c120708060102010c08150d05011104320d060221040303020a03060e16080c190509 69
    0x42110200802c04209404503c190f08107a40b500c10010320038883c080c0181c40b5000c0c2da4803054812140c00c080b810501343c02c1c144c040c040c3c02c00710024020b0364000c0c0e1000480c5d503070340391010044d19035100003405414660310aa040c0d01c2080c1d480c0c128078200200130f00440d05150b4003080020007141c0c030b0091400c0100d02c5c04022880f1000050090ba020b1220190b00c080380c207000d10715284060020041c1c2140560349000000c440e0010010196024412400307040c10380d0400c0c00c0c4502e0000c910450103480d0070170a600441c12001180308103c0d094011200e030b0850006200d07140e5440326101c1c032085221100d040c4041c07420134103c404c2d015045156002c0040d014000b004034800540300d40002e5480031038001403c19000709030364800d4402025a6002e14403d5a025a440e0380103940242680c2e03040d0400c0b84a8020403043c4624088a800511000304003400c01d501e040e5903014041c140b81c06026038144000324031101e00e40045601500400f034280e811078030000c00d41c84240c0d22021102e07014100ba403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 944380854 1250 944379604 944379607
    0x5010b09100501320306150f03010f1e05060a050c06090a020a1e0306020a1e08060306010933030f03030e010606051614160305150603010b1003230702030d05011505 72
    0x240522480c13401540d101c400508000240c18080090756141e41c0304a00b03140c2e00e554040010301c40c4004042000e8005c1c65449090080b4140100700e074142504184101d81c45102c2c00240c89050a0055040d140a070902c40e043d1230591074810812a21354080000c201d00c11040c410000c039200041003808a0001c2e24000c1001a5034295940c46c4025405070600c0742c1800031460b1a02580070401e40c06040101d00f030350303480c01107007064000d1510740032040c1c20480d008c40c20240c0307070030740c0805144283c60880890040590440d240301c150180800340398001812140805443c02e09068060300315440321202032000b003281d0b0b50303148001c84680c002d00030500070b441843c18158010982442c2400311000c68141a502441e1340c040c03800320300701010303481260550000c40d201c0c02044000b41500307a00c00815002400060640b40001c0c5c4145200b00c0e0140078940d17120720703041660044000b0000c601e095000417807000d050020002c0e5503901305034026000241428004104c000c0300200850034189203842e0f85 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 944382104 1250 944380854 944380937
    0x20321040302031e070204140105130207020a0306090b18070e01030f030201140910110304080909071b0606050f0a0b04090c11030706140c130e0405010b09100501 71
    0x1240014000340090342180300c1444243c3c01c01001c0c11164102400c101d5810350b41d1102407050100b666050301c00c44008400c2c8500401407030300c54070352103251b903450800700680d141440e100007100301045800c007400180c6000c05d0603003003103440480607024501e860352035520b1815100d04560f44240600179001c5043d00d040040002500880110340b6261080c000840c1c85000280c003484500303070441c0e0703005d51944101c5000720654980c0c441c00000d88071000e4100d15600e4103032a03071140e5104121155008200c030b2000980e190344902040c2010710141c1c508000181814105000030704800c1c001c1c18030582d20262001107601c2c203002032904172140016110b0805142c2892540104000100e41052111501c030800e0b40c1c45041c402014403078452400014050389410031710500d40e500402045258101708418000d140b0200500402c40d1104030a81019035200d10303240d405441a4650a6040650b41c0207004030b0014400f00300c0103580c02070f6146414601069800307910503080c00c0c1401110b65800910 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 944383354 1250 944382104 944382157
    0x30320010908070b044805090c090102070e1e130b220803010b130b0c0309130609091103010507020109030e0d02030f030f0a0f03020a120f061806080d0203 68
    0x141e660140c0100403400c206d4030729210611000c00d4241d214410b40461039021035545914008640ca00d10800000d054aa400d120115100280292480701a44008622800c10740c2c4200b0800d001390000c5e4014030038908209400c43e44205480c2c403105c845102c0c1c0400030303002d5090712944244464100380c040003603840701c900e4000c0011451540303c0001580018102c04107408030700860080c0102c030102590b45c0c2a0b04000c00410500e03400c00c0c0815641003020901554000040e40c40b4450200c4003000c0e184c80c14102c41d40108455805508810304088810084c07103c02000400b1080d03041e0001c5c811555090012401c0320108980200441d10501c4d9480c0c182c200310180d207104500c0517040351100c2c032000e0003035880c64000c107a44545003034002031280754a40e400321005418000a003001e504180c249000540207401d215400e0885c503070707200c1c41242c00c240c5036013054008040c40c1180e0405001552541d030040c2c60b05025a030b0141c03145a03540d45116100004444041c801425807002c1e00c80c1c45032a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 944384604 1250 944383354 944383373
    0x70503070e0a120308060f0301090f0b0702010219050c0c190b0c01020d1b030b010504060804140a1502040906050d08040308071113140f090607141303032001090807 72
    0x401e60481c44908000c95240540100e00c0e03011400703601c803101da0f49410000c10191030503c3c50000d000e64101048440000c804514441c0010303408602120a99204181240240200344c2c0e0091400020503e184800e41c21400610030b03c0361030000d0b624402000014804082c0f403030504240011104001000103a4004d4041e0488603004000507160103800101d19082e00c03101c62035528481d400e441d042d200d254051080385001035080c00c003141410300d0110b0151005c18000e00280850103034041504545d0018007507510034641c4280c0c1d52151041d000500c9000350050f0141c05121132411401007010f1400c80b80320840547e10400e20342c545403c0d9907030f0141a402c00d2a044070f03689840503c0d01d80344c0c0c2c0c034900d01c0300c00c8140c000d10002e00304d01e0380c204000c2c1c000c0003d40000c4000d0600f8044c007843d0309002c500280e2003151420716030720007080c0340c030785091910803042c400740750703044102000c01016400002d13070b40c400d50414030407419004200d1840342250f03e079581c028201442001008002051800d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 944385854 1250 944384604 944384627
    0x2100f081501030213060509130c1e0c3c200612131509030c1101020c03030c0f0105010f081c051b011e02041d0405120c01060501090e07050307 63
    0x500036007001c050502811700c2c3c40150b040b6501040000c04c40071040e080c400e2240c021b166070500e05100101c28804090710b001000ba1a103421040ca0308000340d82c46001719000e0646135804103403040803d0300c404484843d8141c03501c1200700901c44042c469070f2503922400c0c2d07003d1075030444001b041c0d80e80c0321500d203a191010040701542066050082d0035854038a050301c24420750b422020250189107034944990929400c1c01c1181c1d115207400c0d40c94001c20b501101c030f00e00d6540d1003401b840401c1c0c071500051746440c150042d4150b140c0b00011b06141d070701d08003040e030b040701d0f202d20720092010740d88521410414004a0040c00e00350341c40302c00c400400f041c0e16512820074080d00e0401e01d00c2c01d07a10301c2c041c120b20450107401070b500369101d2100d01401804c400c0c400174249442c0100310305050800a0700380c07010551090100348079641102140a1020600c55008006010500399540741030a0b1101406001a485000c0c0829492400003d96444440346103101d545507503030341840c5540707020041e42e102a407503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 944387104 1250 944385854 944385857
    0x3060b0d091113021206010c2f100306030b0603190327120b010f080a02010c060b03010c0804170703090501080a1b0302041802070803010512010e0d0c02100f081501 72
    0x80301500c1ca1920b80303180b240c014902024000da030b205c0015188684044000d0041130400c00c600008102042000c0f1405810312480c059007400d24021490105000d44800041c9038800341105902c40e0842d0107910100469101d00b0451407259035403401c051715500c0124080c00740d402c01926036400648107100a42a004860b20005041c0f050100780780c00e003207020f4104070562a0214000b03c24044804019401045400300011007241000d40c020b407501000c0030001c2c14003003001e8030f0310100082170704460900b24002e0000c00203801c4003180140a01130650b4203580c3c5000d00c21091000603171100c200c03008180c0640380c010800303160600445162100070500108180c0e2106040c072600303100f0f015101d00c0140c5a6003d600e4038107010045149100903158005500d20400c812400225800f094a04484044640340003a580c5514414050f25240c10140103034000c5540c4c08924a402608032503a030b030b000755401c11002442070400d6440002d820009030210b0360440000e2040d03c044c94500c020410107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 944388354 1250 944387104 944387123
    0x6050a05090628030602040603050a06050a0b09060919032612070519110f1f020f040e0103080a031109011d0414010806180a03050f070f05030c010c08060103060b0d09 73
    0x1100c014800030f02c0540c000f00e403159000a000c11409a25005032500504010400c20002e4501070004000ea40d09100d42d05010001007100c0a5507a911001d880d01d0b03040181540071451325400808612a800c0d000c2142c41d80b0074002000e152440d103914160041c100c404078189040c44030401161003c0d4001e0641e010042c0400044100303500600850b08030f003541e40c84034100d0580c0c880c80203040000c0100090650f038002c82c0e942c100b552512032070b4845800340560040c1c0c1c41415241d220518401c503040f81c4130720103043e800003041050820040041706116541045149684e0269135400d00c030301c0c108a0700141803503c0c200c4081c41c51181064030940d0081000400c4030034280b20f010480b50176800550707642c1040301044440704030000400c0524244001811790041c4641d03010303019006154014070b40d2000455071000b04000c000440a03084c4d045001c41707407602c200c100114042d11042202c1400140094042149035010b40102c50580740c01d8850a800c0c8070781c3d100d80000034100c4190680e9403544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 944389604 1250 944388354 944388409
    0xf0c030a23090c060717030a091e170306130f0219020a0507060f080711030906030901150e10120c0312020313240309032c0406050a050906 61
    0x40c101803540401d840384210550525082c0b03812410911012189405070b0f6007003160800041114040c0040700d100c1094103a207035210b250f42c110052a03021002049a00111058907250711345102e045503480c4242c80c50180c2c245050800b200c58003050b5011500184662444420304900d40c01004410700b08003001400c00d00070110380003e000341c0e90344140c0036821141007001403001c10302030700014000e1814550903070101500300030410308000300031034100084a00480c0310340a041c003c450608400130041070300c904025000034000c1c407072941c0b40d10a11200c4440001d151100d424047d05c41e20007909840f80c00380c980411100c1101d001d000031244520100b00201c0018a9903441203060040c50b0700071511144000d050700780b010025000b824040d9640c0c0285075441300041c80020001c821442d002c1b0310603506182c03c3d90a180503800c00030107428522414007802562020040403008115030a0140c103589505005a4042a010b03598004140400054041c20625442c012821440c01455030781070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 944390854 1250 944389604 944389631
    0x3080a120b1c03020609030a0c02011b050105040c09051303022a040204080606010f0908060c0a0c0b070203090a17060703020705070f06020648090904050d03050f0f0c030a 75
    0x1069001030700c0100d03002c001440c289641048600da11a001800851810030040f40150020343d801000904014140c181d1041088030003c601428903840300c020b10a0b0b091030b25059921842c5030190441c6a8039260002c0e200092250000d4003030b54142e0041d100c44131010020717108110395000c241100f50400341c400062a20355100900041900c3c1c0003401c0141082d100040040c1c0c042e042580070411204030610003280c002c9800d5030080490320101ea0f03901c5c0120382c1030319a40a050710140c0340d00c0300d65040007160f41d0044000c003408502110a80d42058480360121545682d5691803241540054001080180680c1c01032000c2c078084c60440741000e5a03011101030318029500034a0042c1c012a007072100000e045000c03800ca0803001c0300c5148004a42d0000c01d44500c41643c040380c08040c010182040c40d646503011070758020310160100d1003038a01340c10070035501c801403010f410019103081c00084a2a00c1c480383c840c00f0318191890103025481d00620802290000390410249681d030750f49a6003800f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 944392104 1250 944390854 944390869
    0x115090305160f060c050d1d030307030306030b010b0a02071404110415081e0f060103061a0304050d020601050310020702010207050913060623090405010b03150405060a0603080a120b 80
    0x41d420750300b00ca0700741084204041c252a941c805030500c50181d001e03c0000d840410084241c0813640380905207400c0b011000560400003c10082d0140000a0980b09143c0c1c540c1103801582d00500c0c403400f441c0d03668001a50f072031003010070000060300031344000d01441c0594039400707045010080000c680c506040080c801c180d03010354408040e5022820403060302c10340080600b580700c1030340d0420005030001c40603014114000180440f06008842c40081c899030b000e03510840243c03a01c003012480d00ca81c1d040c0c16062a81c004d84095801d44200c0c6009140c0500c0040c0044c1170f21405000b60115030300f035100000107508541c100724150700a020010605403110503440c1e101ea05641d118001c01901d609028080325015001074003030311542a0500440890041489d080c0d5000340c51140665442e800e059004048108413164140210000d5040c0652002c0c8450b002d00e008200f034400a4440c41c480a0480341a8400244084414002c0b01000d50169800300c2c601c00498001082841c00040043e840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 944393354 1250 944392104 944392123
    0x13110f03011508090d08010b071505070c0b06120c090a140703060312031505010c050c090c0c060a05040b0402010f050c010624030b0603060f01201e0a02090115090305 73
    0x2544042e00402069661001c0320a4000c40750001800c01d00d0750f00c01c0005c1c5820014010700c00c144d140000d008040040074070b5a80342c40032401c07404010328104000010004410080151001c10164010428919080c400b01c0383e16065000102210622401401803100006051020f00c2e80e03928950b50a401c070340c000b80c9104080e0755030009400760846c50510303d1304202d90500020985001d000c040c0521440700703002c09441c02420038913078240b00d40c03820a10700300c3c50034400364105040c08140a41c1340d08130001f50a48010104c1910026950043e6040071030714100c8014201c0039a000c0881d001d9402140343c144401c103146005450706c0701010034030742500d40341da0000ca20400703840c20101000071200703a80d081c400e440f031609002465807400081c0490201034100303441800500c02c0741c1c14a0707000f08c150100b180c00441c4080401800406665141e15a07000c203014031108500744540718000108410aa03194000e005170101d9003401c038801e11940f40c03114400c0c04d0010400c1e002c40402c604201c80d0b1078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 944394604 1250 944393354 944393369
    0x30311120406030c09092c010f02040f0326040e0709031a0a0e0705030709150e010603020705061e0a0e0123010311040c02030f0d09020d080903070e0613110f0301 71
    0x13254030719280e00601c5580c2990014200a2030a090308404410f003084070030384805480c0c5a4180d9441e0a481c007801010b8903060103801c00c0c40050000744a012440440e000ca90062041810004210f9502c0d55810855020511141d40810007844115030030000c1c1504035200303190540c5480c0d02c0756248000102a2030b01400305200d24410099240503d00800000814800107401c000745040007095480100d03021b103001c090380761340884000c80080150a0700400c2d40d01c0a2011a5a4600c009002588905000d03a41c901603030b000192811281c03c0900c0b6442641650402d51750741d41048440100030041c0310b0826035481b04943c0c07070101c0032280440f02080c1c2c0d240c00a107042d40b41d881c04401100500c0c41c614050b07410b000070032880b81c0d00882940c038484d040000c649d6803920342c24402c800514195000130b62141c140b41030788050040904c0580304e2200c041e0100c0c0c2c00540c9809030380b401c008080b1909a07003d0903184901841000c0b540000120b1240c40040d82c1c2084414100c54105800c260000c80c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 944395854 1250 944394604 944394611
    0xc0f020402030c0304050f0d20010f15170102160b04020d1203020903012f0a021501141e150702010306120609020306010608010b0f0c16060206010602160f03031112040603 75
    0x610005216000c07686007007d004200c20140000c003e840d00b0800302d040080b001c1200d6031b000e26440c0139084040301c4c00301c101c41040410440d08441c07483c1d0700c0350302a00800001d84490904854814400c65010300410f940d15034035403911703a40e0f012a00702d0080003260030428606440c0c0c00980100340180e481182d544015803903003010070516003101d80811000035180c0600480710518440c02651114000e092180b441c0d0381c034000f5400342c0c074205428024207090009000001801e4603414442040580126003101c95510300300c5254100c444040c1507558040e038161080000a640b50008007186807060501240d0281e4542c001440e60405d00400d45000d5111408081103107030610145000d0100f0341040d030f2039035051403540282c0f4003074048011610100007898a451140230008603c0d180900c000c8181880e0306c03580b009465a400380304100151140511440300584541c0541d01541c2c1c081104800591568904460300c18051641c00807501400d003140010100305001040501060789010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 944397104 1250 944395854 944395861
    0xc0f0302100b0d0f08160f050c12061b1b031b070b040303020a0204020306010915020d090b0a0203090d03031d03130605070201020c1005090301090b16020f0d0c0f020402030c03 77
    0x100309450142d2841445a003400310780500240103c041c903035409401902440e140c005034840b0341d0003418414005403007013192130100001c0260001e40a010032406032000543c0c896803807001986c924003a62000d00e8155200da00c1d100c000c030844050070741191211120840301204258280c04c0d94420325804052507840455001c51240030418040100b14a01105281a242d528001d459001c8618000c0c4516000008511184c0c802c02c00340001d080340c214890807845529201940d162680b044d8040881c041d1880014541d0300041501c1280b049d6802951030014090708004500c8070445003107050640ea1480c801403d58901c250b5040041e04000465845060350f22001615803198060010043c04100080051740d011035900d0703214005482c9007200b10181042035940c0c0c010301c403070319803d5882e05c29118107008400700c100740500410741944802501010080780c44131400d00210350268802030400b01080d214000180103a4000d01c262007040702d207540018281ea00583e401c03100c2d0203020090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 944398354 1250 944397104 944397133
    0x30d0204080a0c080f0a17090a080c1e0f011809060b0406090906061e020a1502090108090d080106080c04030f060504050d0e0307060e060d0603050d120c0e100c0f0302 73
    0x480207040070724000c00310900003c4555544040c190030047c00c403c00c040d860344a0f04039110580c0c0201c03c1c001c1c0340900c800c2e140d01c0c0455981c0d90f00000b09214030621865140800705003581503a102101820302d030419004070300150b034024104412403001c0206006c00040074200c0b481a4006402d601c00c0d03e43d40c4610f0408001c3c00d540c1c19801004003940740450800245401c04040601c2030011040704017800385412041e410000c580c10041e00b0b0144000d840652810240d000b050400303403d032583d01c0c00362150316880e43c0d1117503040c0400307011480d6000140100e50040118a031310040000205143c030341c50369582c1410081655044520945600900042120500c5103a001000f280351980000071081d0001740d0342d503000d102e8401032007496860007986841e0402200c0d052000d441e428803880d03641b4601995114400d100e00d80001d44c406500341400b0f0514060404800b0a43d51000340a4106004014144802440382d40500c41d4810391680001c180c01d801d510014002d40140c400300008409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 944399604 1250 944398354 944398373
    0x10c050f1b100e0a0302130902090c19090305190203070b0d0f0e010e0c04020a05120103150e150103030311040305060a0b09060102010c14030a0b0904080702040f062303030d0204080a 80
    0xb910307051210400b0900c0f050386400c0032a004403a01150301c1070f190720448942c3d100512040380041d40110100e02044038040d87c41d00240380310015007004540019926404803003012481c0402011500f00c255132100481404441c1925180001c00b6102255a500c6880c40c941d80543c000d00001030b100c582d80810400140710340c000790f903100c10081c088a180300000c00e1700c41200f51310b0035101d660302059400381944030704103461078440c00058000c1035584070b042c90b07161010346581c3c0402c12800c0001601c6a608085948200e83d02c10080109181e404e50354160060f1450080300309d01003d040c00b0010114404202145c0102d1140750000740c4801c0e058140134106130001c00c151705582c100360322911455804101200301c80c4c0040881c0c0d46940303902c0158400751000c1401c0c6503015142d0320a00c018070a0520041207007038400c0b1b07810802d11981c0003401c81a10414803c500c8584110182881c04403070496503a2131744200201500d24045041400100b00c4e0402c0d009080581e000d60324031810010b80c0d15 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 944400854 1250 944399604 944399629
    0x403020c011707030903030b040e0c090c04050d06050910020a230a050f03060a050a060f0e09040c050f010c052a060309030f1e0a0e01030f050114010c050f1b 69
    0x41c0c034803514102c0031920952200060a40820107650701c00803001d040c4203034421200c401005100b0300024403002d0070aa40c8030031401d4691310541d00c0e500410740c3c03100aa011034045a1018180000050b6180c59641c010140140f0111a602440700340034056071840c4002c00e408607d5031100610b1140c1130340358520805281214103482e200400100c1c9800f03030441e00359100410003403595540d03503135100c012800b4205954441d64020b034080c90f000c2401500007507002d401201e1076946032410a100010404001e0007501c010b412802020400d0107181030411204940d01c80c18101001d0100321503450074640301c0204814034010026110b840000b0510590741a40b18a0440d0414194100460340c1c1e900c1e803141e5050a205120005440b11441e00c14600650302048850005038035491440805002e1a10140545001914000340d050f6011614450141601c001e4075003940c0888607070005548a8400b500700750348601c1400c0034020b04d41300030032820910382c60a07241c006000c0030503002c2c045440e0f00031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 944402104 1250 944400854 944400857
    0x131a1e060d110d11150c16060c080d150905010515120f060a031202030310050102030a0c02010815090405010605100228020406031506030c05011407170c150403020c01 73
    0x801149000c90380c01012101c542004803625441079410f46080c80e40070560300f01298101341c10140c1034200402e24006001c45035100030070f5544810803c5035078144507c003400b802000c07841600085011408003c05002c810203c81c00002d04420007010206a40300207520130081d01d51504018404c030304200e442208141e6040002c10304064912402014004000386807400800803070000940b1991400003800c025904600c01c04111041131000a40b00c0c0e0084885103501c0c0b043d200f000419510003c122801c401441d5500b40900c851580111040c181c00741c0754050b03d84242030005a00e503106060b25000e2841100001900d07440d000606c00207121906121065400000064100101000c0e01c103105c0900a0b0310281090003510004c2c0040caa42d40016055008281c0c140102240a51000007aa8000c05045940a544000445001c514040d40c9010024144046400a2030900306100080e6142070043e041a2240100500c0e011542004414460f21042400141a01803089244c886002e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 944403354 1250 944402104 944402119
    0x9070303110a0305030f0705040b0c0148020c030d0206151c0b07020a0b0f0f09010e1b030c060a090e0604020f0301150c0c0f03060515010206131a1e06 66
    0x42d41c80203041800024004504560740d2000220081d1144044402600301da2619684514041c44124020440d09a0184405820b1480b000640810031860000440f021510703100381c110198140d60701d0003c61420a00390310078905008400c0c8c1d0300740841c1040f011242d00402043c54003001581032a41210740043c01140d080c19590320304060349070682a803640003c001d47e11511103a1080385007445015000d06800d2440301400011a11030a00714020007402e503d145d41c0b5110444a94229140a40c984e90f01d644440300c91140d0050010040c4c14000c402010f680d85084800c000ca07210f0351010190314002030060310180318500103460740503041441550301718100149545442c000c1d20040c010f118040001e0320490090912030720404180d00d5000005992035569080004446501404107e907054241030024007c10500355080100c0c243c141d0003080652200d403148140000302801c00d40350340310b83c100c2d444109841400814001c0d40005898022800c0c01c0c03e590b500448040c1035648103101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 944404604 1250 944403354 944403373
    0xa0506180c060a14070c170d0509101101060603061a16060207080702100e040c0215040f0c15260f06062a010e010638040902030907030311 61
    0x40040c0c500c812a006890b403030ba030380000724021303100c80d250841364800c50b01d80000d1180c00c000c3c00c01590f00895000f510718a4095030103816043d19643c0d00d50a18000810074040031042c1d150203000d19040d00d58a080c903000c6860000e109078251a4541c00040200707850340c404203d5003103440750001d000709089a1140c01e041280703400b05501900c142c40500f08070780104010081c4030ba2001160221a40140002cad6500c0d040300300170b800000303820700d443d10891603c00c100c641c1074000700e40c500d548017402e040700c8030680d210b40d5801d0ba0100440016100040e13020004a40c0c1c04203860401d8051461303407500000c0c0e10703588005104800c03d00d0070820f601c040c4001405a10000d00700001e810440071940b0b1500d940205030414504030a80034410151300c0d10851080c00700070103500080050103c0c500920000780c0b47e9141404104203c17081c0c0c01c1000c03003003155408402007020480c82e0724400300e24240c42c01741d540c02094140d03041510064034982040b50200209900002c2038143c101e03011014064619 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 944405854 1250 944404604 944404651
    0xb0909010605240a2115060f1b02060a200109170a0f030e010f06030c050f042703090914180d0f030b030c100815041b1b12020a0506 58
    0xc2d51040b00107000070480d416203420071350001c6000e03440074904204110021030b176418602c4003041c8200004038523242000380c81c140c4a0b2009084200c000c0b003d545007210b0903400d201a9a020301590000c00410f1a0b02d007034030b0391600c01d41240003480c0c1c030000301c2e0180460410b00c100142120a14510400402c8120b01681d000b50320016841d9190600241a040240d001409010b10f1410401140d1810340c02000f080783c1500040140c035401c1c3d904040310859401800202c03201c43e10041c4000103045404542c881c022100c03104094464a8800203090341e0340034040c15203400c0760111410800f41810890480d04c3c01e00700d6031030542c10a000740080d01c9051800740100306040050f50030984c485801060b40c0d102080400c8010101404140c4480c1040c6001002440b0586a00c010041010040140c91a243c0540d1006070444480030b468440d440c0c20650b400e0160500c0e40681040e00010000030980380740d021100e0186a40140013540400d10f0310b5801e1000041c00c1c07a5844040041031407005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 944407104 1250 944405854 944405857
    0x20123010509190501080d0809030a0e091008060f0411031c050912120703020714030d030e0c03010f0c0e09010806040602070812040c0501030c08061f030b090901060524 74
    0x64005070b90080d01070315200b0360316422265801d011000c02e41004c00003d14902c000807010403c0d6655030b81d4034200d869285610303071680b041c1d007081c0c0005503215902110620f810392010303401c5a400c1040e0304440380c0e01e8200c0b0b802d08608032403091282006804100500080304460076012000310f000e8080d998890780c504003501c1c0e17501090420014040f59406980c1c5600d08101214131440040300d203030b90b1444950040d2136101e2041180180039403480003c030b8440149081d441000002e001c0c0c136008c0398090049000b0030700c0c00d40501d035074402c50070018100d840a00c5034088481507035501080240007808044e000c0034208100c94081e04a00d401008017a4010401c990000d91100f80981d49000600701039099010701213000003950f1440040c1f204000140000c18100c45c2c0c2a203060125030309210317040e551f41404442c169004180c0201c001c1d00c1103044607806252800718100081c58070460000b01d2800c080881c2c08503081da40d44c407024401031505405007504506403200507a0303088600140c103c582d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 944408354 1250 944407104 944407109
    0x1202120f06040209120d1404180b0a0b03070f1b031205100e0106180f06081302030f01020a111b01021c031103250207060c08030a060504050f0702012301 67
    0x201800881e00c00e0303a46030121404281c0080860245152141107551941d0158010b4000b1600071640a0184c52065013074a084618408045269803140000d000c0903060b03c8a909030b00400324030011034240042000ba5020710340c142c0da5104503541444002d0a090700c03d00307000703c0f10b04c02800d0760400280c0c0f100301d40c6100200c3c500d01140da0307103501180b0ba020151a4010100c42403040d4000b040050f40400ea8100703510704640b440102640d01c2443d0249504240100400601c0c0e090014841d02d180606c54180c851000c2c045031b421400301020182241c121082200004030005800425124104840e04010014000c5109008000300010b50390300400c1861040782149401c450041c0c070300a500601d140f007a04054241c3d2883c0c01c918a1030f0340e8001c8240794100c2079410703200192080c400908401035580c0c07511141d00400713080c0c5910440e50001000d1001d04c81c0c403004041003503103403401164000e40c9c0342c0403c000c00303041000000c0d007585d500d844908030058200d50402c0501ca42440441d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 944409604 1250 944408354 944408371
    0x30c0527040230060f010903080c07030c0609090f0606020d21050a02030403170108060604110f04120c210b090a1b0503190c030308090f070b0a120212 66
    0x166403616001040c080d015400410314a0300301078814011020782c000c40c007545030749031660800c6256614010440c19070f0060400d2400121a80c00910000317804000802d01c0034860812601e03550b6403a40c4509000c3c17250f421103000542214030400038552103000d1200c0264131002c06201442c14480d0003560381100d400f0203000c010101d41c00301d26500309107928403c0c3c41101d02080c031444c580160004007a40c0f050f2011000146401d00c0c5150001810b00014169001c0901a20b200d0302c07410100700c05844e442d03224002d104c0c0e0030030a64000ca02004020401403000e0b14424007804400d0406240c1a21030740c1c4805510784000306c0d02204007038406401c0140350303442007040e0001e032179425817140380052b00e400040400820790b0f80044a070741b981140340102d0f202101150703600001103440302d54482d840381d0000c10032288403609100183c01040419400088007007107030040f20071513403500d2a0100d45d07401140c0c100710000d0281400c981c0415240002c0b00b604105510b004907200d46e1a480d080001c01500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 944410854 1250 944409604 944409667
    0x504150504030c050303161e0e011d19090c05030906270109060501030b09070305030d1a03030f12060108010302100f05210f06040b1309020a05150901030c05 69
    0x3000c060003040050010f03900b040442e0384a2402d002040c0c1c003440d44000e640d010403005000c045020782e0881c5140500c4200d99542518401c10728015240500585c040500344048542c00c00403a89500329035000a01c0101c020a040d5840c0005100889410401c0c0d40c080200801c20072805070340004541d504402000045000c02c44440444029410703205100c0900b9400c000d808014810150000c0d4162400b4444030780498641c000701079941c070b465100003045604180490040840d5680c01042061619005421890038081c00241140d101c1c194401d081c0001180d0240410891408254044020308040d5211350544c1c0008281c0200e15190100b04840c02c40c00004840c4502c0031740d004294100c014004648040b0410721450404890030603c0d91098400a00d1030702d020300854101c050003605e1081010900c6000801030200008142c0e080a085080000c0c1c6031242d141c00749500d10f0100040307132582d07080d000060a540c1040203600810100b40030314011604a080155518001340c82c811 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 944412104 1250 944410854 944410861
    0x5070f0c030909052404050105100305040f080a050c0c041505130e06070f110c0604180b03030a03090221030d0e0f01020c010501180207050d051b0a061e05041505 71
    0x84941040b1600411821402c0c4004d000b01d01500501401d8040400d03200c01c0a050102400e000403030b00240f09003070b44603c416000da200b04c0e00a90000790090701600c614110000162613955065014000504c000740c000076000401520600c40100d80c40005c650901c10f09401c44100d41d0b405d4050b01409104402c601c01c07007000c9000d0b65100c40080b008210944003e483d245c2000b41407100401c1c6070102090390722095000d4164003181c00644030300b000700200d08180c284464100b01403003140d03201c0c0e240c45da51188846140d804002a04520141c8c1d60301207583c05040c41802444c07081c01e40603d07190030880c15141442c420100558420b480f4000c6c00103000802c21105521700050070350310701b0080d407002402091103081900084d0503555682c09030540c041008e003c000891094000140c52508a042c1c0c0391421889103004058589804800e43c4040001012a906182c054041240c01035a00c092501d07140d0b000707881c2028840b861030020089464180c9480709804815030744070320300b02c2d0303500b000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 944413354 1250 944412104 944412107
    0x30b060f040603050c0117090a031803080d06031205070b0601050c2b0905060c0c2403090703020109060e0306060904030215100e010911121008160e0a05070f0c03 71
    0x48031030050001d0007400180d81d2800e24945401e0428840c90026040c9801407c82c4410308210300c0c01110040d00400201445403001c030341543c00c0c00c18a034406501042c000007c103903500c0182c0103101c41031200083c0c10340b45161098080310341d41042c2e001c2c440e0070311100c40420310f4500c5260340030b034007030805070360710080d84103114200740c0f000041480849900c10007902c1c21148045929540303001c0c2d00c54503045a205e00400c83c080c0180100d02855074080804e40c1c00c40d0a260fa040b02106a00c0742c00010340300005000305001707400c1164001c01d6030784181c2c0d0410035580c0c040c1603800184a81e041c900850010140070a85500d4010315047c05069004040f504040c07080040120000354243e45444904104c40380c0e9030010070520034000b410301c4880000c14aa40f00d4865910744840a840c010728111116040d40200c0c2c2005042d52004d83c4950400644010140b00c0700d007142a907407400ca140d850504540c946034820140601c2c00e1039203864108902213030071100043c50040142000641c0314402c4c40c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 944414604 1250 944413354 944413369
    0xf0305150a0b0d0f060b01080c07120e090903192105150603040326010b07110420040501090e0f1b19080910090c051c12081f0f030b06 59
    0x2c94a403c030f02e20907116810311405013110b004681c41400300b400001c651000440c0c400c40143d07401c02510301d003041100005509640d5150664034141009400303146603074001484400c0c1101c080400e908001000d649214001909050f002d5482c1407440800084901c41201c0550704030b07841d20515601c402180403c500c1070141080900d000b081107940b450107180c010b00c1442c101e00140302e8401011005001415511310103410f03505849800760404049844520612080403407103900156516a5562144130f05482640142c4050148643c1c461074900010700c0c01085074000e07010342c01c0ca4010301001c0280340788140d401c6135012040526184440c681c003410f5100314062140c0010040d842d03910300c0c07a0400080d03072041862100380c49100d41c005190805441d0328100c014031100a07000300307001030f00d01910045694500703420540f10100640c0e90b130300b882060200110000c00c002400700444c04202c94581c0407590000d2240741107040c909000207090b4030081c000186140355020000714991101e24 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 944415854 1250 944414604 944414621
    0x1b03081b12030703020901091a09120a030203030703091a01090c0e06090d0206090a2106111c05091f0e06160509090c07060f140705072307150201050106090f0305150a 73
    0x427100b0b521080c04000800a9611442201d80a088180407071104c040020841c1900c2d540c054014502c0c694429100320000c0c44170440842c0c4540400092403204248505a04d029103080080060130000c0d544018201c0e0b4071041c429803103180100401c030016283c0280c429403140d41680c1c415100c0028100040d0440c64542284081c200b20b04800c421000780400e444410038000c800c1005000340e0325a410320144100c00704000e02e0099103081e40200304065002c503500c0240b5905488003694400604501c441d02419a00e14454440004511300c000c10720209800c2002c168844c19040024800508107002e4110310601c42c3c0750050002d113030164414216405d10303500a6041010380840500c1000070031030b01c0030000684c81d20400042085003d401180c004c16000a14a42100707240c4a90200501007140c1c8035011340a02000060b9031603440000304484940c503000400c266041090060540403503511034044482c120390100003103200840d2030050050b55402c0440950342d0018800003420996 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 944417104 1250 944415854 944415869
    0x62b0302011b0f030b090112020d0212010903020a1205090d03050307031d160501140f031803070b040b062b030207180b1503150d1b03081b1203070302090109 69
    0x18400508060744003024120f600b40e591000c20146030800203000016000340505810209003039003080240c079109448400c854402000500c4203500403000740d0940b01e21000841c00350744420f0307240041048176060800c0000491138440c1c01e01441c0c42c0000c92140007010090280080007001c0707040c040c4260400702c401042800c8480603403000e900071554984e58598141521400c0900110b484d61081c145040c20200e82150746050900602180281d40e1015020f0428819520b29a1031804001e00140131254010110080240b4042c208841030040080c01148a5254940c0c40c00900f452240c00440000156903048440fa1042c5401d910306a030640200074200c681c2200c5805904440e00a1110400c0a44034146104102841020f06000c16284040c03800c1d0784004500007800c00744104030095005d041170140f101416607020818598070b40007507901d035900140000e00b90340300b465035540c02c1c40c0742402025081001c0e0600d012500020300301904044e00040c603281d40307a22440e4404040c0801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 944418354 1250 944417104 944417141
    0x31030c08040303200c150d1404080702091506070b040f020901240905060a0807050f0c0d1b0f0318080303010803031806040c21050f060a05062b030201 66
    0x26030501500701303003210000d114010b140e6106808802c41c0491100607a140152000441b40402540d0312042d4205940703030024a681c900e80c64914024402e203550090340164030041e030320100d40c018801a014010210044d500400310b01e80c0e8a610341904035010685c01180c4001d041c0c13141e241014020881e40c2c4082e6110140c040040b03000f480442c45140c1c0c41a1400c00da00804407203440503100240e951061b558000000e0019501d03407401b40700042d601580d41d103130152500c7c1041805003060780014442400704d40c010b1400c02c0c59160010702e00c4508810031030911035401d056548040414600c0302004007000020182d00745181c4041c000788000e0100d1000392500c3c2d603110801e46680742c1040310801d4000f240440062250b003408184075024540040c60041054245190011040842900b047c02c00400b0403900340404e074140a209403501ea004040c206504280c443c00c07082d00d6024204034402c0e418000c0c900d211031604000c1034003607402ca00c41c2c400c00ea003650400303a004200403e101c666400f603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 944419604 1250 944418354 944418359
    0x1020703080601091203091e05130906110c10091509060504020321041403100c020c01090902180f0a080d05070b0108061005010c2103020405040531030c0804 69
    0x80003007085209250a0341c440000035a241c11040002405400107408181c1041080c402c00c03042c130700c29140e4080a0181c1d000340940d694082100d4400c0d8402c1c1071200c1d55103201030420001e0038010903451919031801142071110350782055071611000020304c0140e591b104406810030248010b03003000e42203400750800400e0400e041c141d01404040310100d120b400b030301000d0746106101054444e440f044026041d414503060610106000003201186030b494810044403800482d082d0092050020b000d174080c1081079541750001d4121030150708090791700c0740180a500c1c2003001c46000b0a4444004583c41c546601c101c10100b03507212000e070000c00071030046603404200b042d00100180188c61284140b150107070307659601c0f55121032041e40c0034801400f800e01c0405c01d03503120300041e5800c14026441505841c0a06642070352544e10110401c011031740121f0200083d03c1d0521400360300140000c81150041c1d00452100d040340f5840e0080c0e606070105c0104107041c54070be26050109603601c62280e50341e1f80d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 944420854 1250 944419604 944419607
    0xf0a0c0b090a03260609070c050109060e161512020412030207030201140a0206010e07031d070f0815010905040c350f100515030a060c030b1c080d02090301020703 71
    0x2001072402c1e0041041c40050b00003041940c64035844004000030b4542203a1503003020441c3d406409483c0707d0800c0440100040031650038071440111600c1001c000039050710846041c1e0800203201c805c4859020500410051960300e0326068401d134181d071500445840044000034000d00864004d007088200c1001000100343d000202041a00e000342c032070f056000c140c0c0e018800030b44240c1580b0360058001800410007209440001c0e60003440e181408192040401a8454600200300722841a54080c85080040d0101c940300031010f442d0302e10140032200400080e40841280603c01c80daa100d564a000406001e80c04480350054150101944030400d00c98184042007880ca03040311440d4031188211007507480c40082d0103821140c10388003404c40e0454140c0a036008142c018001000b18202d1007094400741d4040c0304d150300301c510902c000030300015a400010210b03400040c0150082054100050f03242104e43d00907d0002e80c0300014035682c4101c5030045019010704884250558004a022010907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 944422104 1250 944420854 944420863
    0xf0806040b16030e07030f0b250503061305360319022802010e0402040806061e0409081b0c062d180906060f070602070501090203070f030b010b030103080f0a0c0b09 72
    0x11f501654088001c4e85a506030454800008802e20740c03082ca0491507550040d000b0f03005540c0c00400189404400c0d1004109002510b5044603030514102c0105e10024401c00e424005456000011004e54140c8610100e141e5681c803403400542030442400030480601b40c804c002002100c0c181420003030340c1001034080b40c1020f0000c2c1004030b0100701d6004001c641414188203a0f404c43e41c1100040800303403500b0090024070380914100078408440c1714164a4141c489000780030f452482181c1c0e25030786040d01c0c22030b010f600241e052075908542045143c00c03926547c180513100200120345e050351250028000c148400b800309400e01c02c8071000480c02d1400d6550407000d18400441c01c4d1a030882940d40c46040000c0392181074020320041c401405080042241a409003203510701c580000900c034032050300001e241540f160f00c00d0b031000e800e6500902c00c01c60314030000744c01810094070990865056035142c45207800344c0501040152000b08600b80e0061081802d41803242d00841c0520103401d025103040d859 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 944423354 1250 944422104 944422133
    0x6090a080f1207020d030518030601080c0306130b0f070903480b1b0a060c020d02010e0705090c0d0c030c0f0504030f0204050c0f130f0806040b16030e0703 68
    0x40c00307030300301002030b03440007004803080d141e401802c540c00d02900d80c0d000c0c0c40641000d2250200d1605540c0c007681561010401d01d40030b00070800003440000c054001b098a08a801441031f0720902d100d2030068002601e04100c2c0e904040300c80b103030340519580d00034200c8081c01c49a00180c040048580416a40303014909040e00d4880074005100385108114240790345e95622036420360101e50b0a100070000603904801506088082003000f40e00542902e640e103150501034507044e14115a1442c02000d0301b501007040d94807450490009001100201e0026030b210506803243c1c1d4010700401000564a40380075084800301d503402c180801900c0050a4003c00400340340b010203000c070304000c0491010720301650941c4d04503544024115070801155003448054003024003070100501c400e0003013159420055005d0400c0c00304003007658407000e14110b5001030b131044541c04625540c200000388408030342001440740e44802140b1880c45a10035a01c0201c0c0100090042c2c107109000b641000700030400500f030300400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 944424460 1106 944423354 944423383
    0xb0a02062e0f0f0e07120b06160b010905091906020906040807031103011401050d060504051608100e0102031306110409021204020a090c0210050606090a08 68
    0x7024441d801540c01c0b5041c45005108112000220340020f1241154002042c00d0280e4050200000c107210000501d031107041089194450400b11503540110070350140c1c40480b1418495200c030b400f03004d4184864101004144100c0740000c0350030300320090345498000401d540d580d100c0250310614490303800480c148400500c0c0da006004282c01903005684035040144101c08060071500482d6020103050740744401030209031122903240b20b006a20190000309034580b405c009190a041c1141e07800721b03003a050008180624003040c4040604d035034040a0001088041150b07090340012901c074001e41e04c00b015894003140b401c0d00401500c82118001d0b81ca815103980104050f40d016a00c000c0800480c1c509020442c10007010341d10003410004001c10000304040742c025103c3d0220b8820300210b0b41c499001c03c03410369806040300c14140d001020018100d580309002900c0f81e612400c000c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 944244604 944424460 := by
  have h0 := BRFrame.cov_init 944244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 944244604 ≤ n) (h2 : n < 944424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
