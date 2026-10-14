-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1178
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:37:29.459907+00:00
-- url     : https://prove2.me/submissions/00f77c5f-79d2-496e-913a-c1af06950298

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 211690647 ≤ n < 211870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 211691897 1250 211690647 211690657
    0x140a050405010c1119031107030f05010f0203010b0a0320031e011e050d0203030903061602100209011d040e010e150901061d0c07051b01020d0306030309120203010b06030a0212090a08 80
    0xc185d40c480e21810340c90100c030100e40301c4010090702e01821b2804010402c440c1d204c0c2282034094002804008104d4038981c0c200c0c0f00a108040011104001100b03200e4040e07000407070102424036154100391620740c0854115070084403405403a51004000c0101c80201020080c0900030a14266501120080760381d010040d01303000d628441c0c4c0128100c40c0c1195020801c840c8a0300300941030b0f58050400050300d00c2a074050009400150241458441c100c04c410b00c03c1d203920403030503500c507030548210b8880c0e600b00c02144051150444c1d00c41860020400713090017002d5101a5500042000b086600c01c1c00c0758150b4040c0c011500303a4144102001180c0c16400410b004002a103003d45440d25044191503085c03148040c014254000e10804030300c442410b8100000101d02a02640c91520041070110100d60303070b9000050105958070030034014000400c8040007110701c064000a00070030040009a125002100c1d0020110b4001401c3c00010708201525a04401e0301d01c02841100d40300d40e50200c15000b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 211693147 1250 211691897 211691923
    0x30706091b2d05030307050303060a12080d02030c220f0e09060408160501290904120e0307051503070e090405030a081015020a06061a1b01140a050405010c11 69
    0xc05000c002c0c240300c04400100c01481e00a048a969101d03501d0200d40713a800c201c1e9024402e80c1e04800008034451800a010049603010000a02d8105a050640002d40010b00380d070198503410301c810311503414012905510925003034040b51106190015030504030703800350804c000700800c00c0c0501136003800000b569500980d0002401c1d8030390300310801408041890050150070b5600f0280c0d040609000e503104540000c603100d01c403406281c034080034170944443c281c6000f0011a61040c07030b6118244104481d0401d40300c02403d50f900190b0300c0c00081e5210080300e460303030551940002801542908294035942081c010b80e01079049140980700d15882e405010510002e204080d030016100f00c09a901a4001d0031070181244103101344040002e6035207050701e0080715075903c1e10b0740109122200ca1034401852000c42c0510703241804100090010113000d00014201c3d6403211803860070665036803e201e221b00400800040e0301d141030f0400c42d00350b8007500160000e0140c034800d14154460045440002c07820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 211694397 1250 211693147 211693199
    0x905060619030609050a08030a0212070f050306010305060126090c0406060c08030703020d090807110105031302120106031a0910050c040302010507020d02060f070506011517070908030706091b 84
    0x3403542031546c28584c03401d000a0441000008204601e031607907003d00030070140300358100d495507078408069400140782c90300c00c00403840a00014a45610a4002e550300c207006162500d081c0709054410742c8600c00c0c040140810150303071000c014011504200114078000219010702c2100d141c0180a400d0b0680010040c03c1485c0000002e503072680240c044802d501458201086000083d0810b00000d4201ea50205d8049408028442c0300358805c0050701e015608611417071040c200d4940c00c010540200c1200c2c40e0b225500d8480000204080d000f9040c64002844030f590f0140c5800c00320b69050060802821203902c0c504000d005050300b4044c10303541070f40c2d42800e050b80d80e9020350000441c139181c00f50009501000004425421400c6c0d04050940c031403203001103950070f9803030b04004143c1006c1c4180080c00154000c0302450040d4421108540200c0e0904040501c540c1744d40c80103080da884140265000381d1642c6804040003a103c060301c01c0f003100c0c03080760031140c0d0030041d07075068800c030322201545014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 211695647 1250 211694397 211694411
    0x50109060f020703020d0b090c011e0e180f10060206072015092a0d0f08071707020111060f040212010b04060e15030a080d02160f0609050606190306 65
    0x740c000c03c41400a1600180f070010a82028039100300f50240c00c4540644902038010302401e29402041c1c2c40380003400b0384600a000302803011048030402c01551415504c1210000603039550f0b1040008227010340e14140054801e442d02180c5081c890400ea408402154803510401041d940d104403a41924000b00d030802200800340f05105103054072004030803030900c21801c2805000c071000242e510110341c0101754545c0010200d0b94041202e9010140e19030481c50b68501c0c034002405840d84841003901c11040c0c00d04040d460385800502c0301c2d803c0c502d00b90b00d4800290502c2550707001303500010425011401440d2502e0000c08901e140303c00500000e002d540d00051601c0e600324290030803000c0a1025204000e80c50b0b56083c0360f20201c43c1070324a500828001c024019280c200454400b002076000310b1214a805541080f40d402540003040e02c07500e07900c0703115584000801d105c1c039803068140180c1001c1403e215a041480c1880e2018022920920003d4440d04099200700480c004607034014030700107815 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 211696897 1250 211695647 211695677
    0x60b0f09041d030a022d03030f040c0314030c0c0a0311010c06020c011104091107020d1e020a06020102071103160915080109030903030e042003041401050901061d0105010906 76
    0x4a0030b40720b01004207002c00310f0302084196000550300080c01c902c40d410190b4041c9100c00018041030300c0008081e54000300001a0003580c1d00c0c040540141c41504e4034542e06960303844440340d1040e0a46115896000001d00c8038820f10100500c070102c1404a81500c2e54510390341d10006202c0c4900f41c5135051080c01c20025080c0105941900c000100d00f8000b0700110b40300c1104107240b54824083e10f6040707442d2040744207501200710f007501c58295014121041e400c0035925104000b2a0b10b041c00190004491003a00058645491034002028a03030005a01c416081c03904a0184908420080c02030b0321810300140940042c0b4002d0081701e14040c1e00192068128030b40c418a80c026822039501903090880038010194841c07000302c116402030760b400d080d05015070104002c0c1e0300045d0303408034000304c91382d99014400300d140015900729108450025032420540e0301b5a0a68104030b604c83c0c0c85942d610010010b044201d010b0340100c843c66111400b1640c10080041c20792480c80c000c100400880d054040c0300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 211698147 1250 211696897 211696931
    0x90c01080c0d0c12150e0a0e0312100306060308030402120d120b1207030c0512060c030402010f1101061e0b040b031816032103020a0e01080601020c061804060b0f0904 73
    0x880c122000244400c517004007105210503c1c0b4400c691350803030030740005101c0403030b90b1055105807103440002e1840c0022804d40200c0304480648801114030011130008009009481240011449178440640382c0c6402e0040001d02d242c1084268015006081946d00300d50b8840c1c2010b0200c540c1e035a00007040140c000100d03031034000c14050074035980302c2d100010050000180b0076004480c3d00f222205c07800c09080c6180c40d00c2c1c00c0306540600c510380c0c091020800640c0035001c0e85900e0f80307003071401c8503851464014150035a0460f030300c4054840ca141981010304003c4941002c080c080d107058043c549403409049101303030300c0010302d400395510450500c242101d000307014088402d14065000e00f42261a4140b19020f1444480c003880b0741d208071a645d055490090080e0b5003003081d20349480c1d00d001070700310041d1407944000340024110701441c0d1058150390b9034400507140c1e5141401c00719402c003241c10305000c120b41c0d164112003001d0300c0c140b088030f04404042086a80210040e10041407035204440d00c0c0c0d0b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 211699397 1250 211698147 211698167
    0x21606030c0e0a09141f06080a0207080307030905120c1f06030507060e0102070927030e0607030210050601020606220902060708030a0b0f100302092403090c01080c0d0c 74
    0x54040321400c800500b41310f0f5900318039000d1140e00d850ba0581d032118203105841c0070b0708407002d078208065907030f041140b50b02900400da0321415009006d072804016030b44810080e8011242e11000c00e0f540d8000c9404d111007000400d0b40c3c6c0c6d042c500150f01e02101e400300590307a0b20361140c020f01d10011034201000344880c260031a90055a00204480705241c590002905a1050541090040c41001c000260036038a41c00703070711102e21a14110150100158250040c0c51064030810717000d00045d80d0701c088068964100030708046000c1da01600845503814200402d4510280c070b00c604541c003032403c4c0100c59403820f1800c42c0e5083c400c400001c0b8100c001c01800044c3c0851007001e9440400483c2c1c21051082181c01944102e044400400c000f0178000100812224407184141d04204000041d40ca4280a50b0080030421002000040c0040c54030004403a19500c010310070746440c0011042c00340205d006c0208600b16002420010614075150303820b0b039a503001d55071602e0355244d121340f0118105400740c0c10501c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 211700647 1250 211699397 211699399
    0x270c0607020f0d03050322020108060f0109050307060f11011424030d0804140f030904090302070b03040501060f2702090f04053d050d03020717070e07021606030c0e 72
    0x3c00143c850078007030110f420480d681880f103081c04480640003180c540c12503041d194141c44400d110748030b030414007021a220b0799140d0f044c0902200d02040380e40d002c100315030051060f951804900300c2000030040001c50b43c0024454240e04040341492481d01030554150300400b050400340c05140d0740706c91402d141040700036240d014001d03210b0340c0b10f050f584900442d00ca03600070840030402c00c0100d9420382d074400a9041307485194105010016440ca0300742c010400c10ba00901c100d51115031104081c4002e0b030304c01d074ac003124541c2d074803142040024041c02d080d80040c2480c2d080400200b030041031b61383c4501e1402501034030346076000031080807030703a14609090301e0440060b00811039450720045800700010782d03038034408111600b4110941441d49080411141401080e901421245080c09211110355801c80840030760003815400709040c8000108031039070319070f150018003d05242401590031428007038030038030464000852061400143c0135508080301c46e10300e070004045001c10030803a80f10940b0701170700d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 211701897 1250 211700647 211700659
    0x6040312030b0a080303070f0e060715142413020f070303090c0803094902011806051902010b04020a0207090506010801052407060c0206270c0607020f 66
    0x250392800c0d4103a100c080381a10030b50380455540d899245040e541e020860302000014884a46840d03d9445481e2000e4265005000181051016520b0441e0b0100030a0765240e1310b81d0711000071076041410040d50307421407054114820300404101a00c111940d6414803d401408103007101d80c000369082d4100d98400e2040840b050300d0700e110380781c01005002040420303968101002004a44400d0200c11921600d03002049000e21f03503100d510700c000340681099068180c803801c0c014040c03900d86c40500918008002c2d48030506c0c0e1482c600c00540504060348121100d1127965801380030031904507003140c3e140405000c044400311200b0310b04a001d0012034401542042c0040307000f91149400150707000039074083c1e0701c05200564031306004640391a001d10030564028080304c400030f000114208080240d44405458524004882d1508800d8502d400c0c03000005900420070400003282c82c1900840304460200d424002020004a66a42c0e641d00e104141c80b940c00064848215642c0f00c8101040000c041d00c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 211703147 1250 211701897 211701923
    0x1109010b030406050c270102070803030603030a030906091b1502070e042a2304020c1507020109020603010b030609070c050309010f0e13020a0801151d0f040905010614030601030b06060702060403 85
    0x1100441c0c41c104c0030003405031191201c0800c2c0c8800100c1607374461030000c0d0040d4201100f540c0e00310007408180c101550440d507184075941c00b0a251700c04440419410300503801400707107030040603424000c0803801d0b0411508401828014103440d5403086400c150041000350a08040f000d81100607814201100c0d21440b003034100040d000344c40da4941003494050900c1801040d0250284800d0344582c48c2c0300e600503001100220804c0740044001600f21100744000191066540e003c070303a055000703821004403141e0120401400d80740007805258050f41601c2e0401d40070500d960341c25980e003c1d0103500c0d41404400369001c075006203d0f0301042e045450090002c101302c0e40c03140071140250322070204003002440340c07c0081841080407284102c1d098403580c030f6250444c0680c00d0f00ca5861a411600e90380a07883c100b544400d40e40c2c0303001e00300b40e00740100c000090071440d0004c64200c06100a135690301940000d001000411030f200042a0b0081040d1101c90307a410b850300c001505c900c1290030081a0266511b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 211704397 1250 211703147 211703197
    0x50a050702010c0c0f0308280207020906030102120c0d0b041506020f0a15051302062110030209150105090303030a06030309090e06060103090606211109010b030406050c 74
    0x5010300c4003a0020004182a03400440d007a41c4050009400c489140d5500d8002034407a506071a804a260750000313000080e5410055607001032500c10b01000c82d0003281660951401203031281d00302900728000c500e0030801c0d2032440300c40c400c010082e0440c1c1e00041048405030407680c00c8040d0700400180b0800c10403034000c1d1003011400305402144010b02c14032a4030b022291f000619850480d800c43d0f000b02d68160b2152458010b0302e001440f02201800800040c8016214440548400e428040000d540303881c1984500a008400800d0b49618544043c81000980c94a00030244c000c01c00c2d004107200309402c040140c0e143e116000c007041d01031000000b00940300d2000d13440441078a11075070f500c2d0307050344e42d41107010190380d0b44580702200e5400c880e000c51030660081e448411100c1c0300b400041085c5d0f5440d0510600714064031842600311140d0310007a42084005880050950802c90b004c20840d4100300c0500e0385404018401095540ea40002c1030013400e00500740c4082d842403d402c1001351803080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 211705647 1250 211704397 211704401
    0xf110d09050c0a05091503120f071221051e01080a1101050f090103051003081308010506121f020d050103110f0103050603210706060806061801030b04110402090301050a 74
    0x40030a440e03a008030b40381010381c0d15012a0a8040b29402000c40f0a41d450b800159034841c0c1215407015418415100254000f00700070002d000500300e038005050710b81280b03003408624899460500010402021102c0d0006a036807205140c0d50074160070000345640d195000100d580d80ba0441d02d160040ea1a00005500317000054a42034052049a83e003c0340c89449006486ca4050304941818580c4107211030350155101e9440075500c404038403141080d05a8030386919040d58040c131450314404000a00c00d219801e424080e19822600130303500950f07645411100746032140c409030711b820100100303013035981580c00703464041c1c800d001640c850401695a580c940306410400f8050003a014054580414030250f0191144500c2044c011f005015a50458907260071558002c0d0b00c40078054205111244c04a0038030311951001e404108000c00300341c28841d082290034010320f40146440d454060061000903201c860352908a50b0040100c40d10501100004019010321948250590328100401036107009035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 211706897 1250 211705647 211705661
    0x90402040f060908070b0414010201020d050423030705070e1003290705090d0605062704020913030516030504120c060809010e030403020f0303130e0f07080702100f110d 74
    0x3d4030340b02100c503a81c00405896901c0da1290752106601030000b0001e1a0300304054a5a007001440010310f4545801c1d401c80480308142c1c1d082d505800290644240440440c2017603134402c0c400710041d4205251030f03441c2c3d90303a00d083d070044403903035034101004c2404c42c1690079002e00615441401180c406010143c0c281110801d4500078591003240c4022400081c001d4048a4103101d001c1c00e1079400f071501d51a001c0107000c0140105130442c9643c207500c494600d41d511008090580144c03011001d06040c0100401000082c106118441c6014080800030790814121040030101c2c08058015006038141950140260f40c416900c2c0b61402c1340500030030100c00411015117076903460f004055214904c81d14221084000100801d500c1040140003501c0e000400007010b04000f07040300e14028800624204400700c582c4000e0120482c0c0d004c0c03049250102e801680c0c80141403825100b0f6141c1540c0003507650326100c3c4201d14441d900d041c1c0e14403000d8150005840058541c03800390b50345510040755402010390f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 211708147 1250 211706897 211706909
    0xc030706050d27030e01120e1f1512111002060901060f120f060b04020f0a03110a1e09030c060e0f030a0807150b09040609110102010b0303030a0f02090402040f 70
    0x50010b40c01ca100c0007210f00c0c075518454001c1249040d00940e68151015a02c5050050501c0080c402614000d02c25000301c0310500e0600c0040c210902c0035034010541040800e800010f03050070404814005001c40f451102119421424020b895601c1d051042602000d1f00041c3d1f000f10001e0070042c1074540002c0e549015410060080041564034031040350003110300d0203003020415200c0540c1010858608a082480d8000c000000d4004c2c01a00041d040b40d118011400644030301061520607075030144503048411800c60700e40b52401201910040c69a100300d5646090034100e0f04000700524032480c1c8140245a005c141200c036180c442c5000340c94600c060b86440e04c0780100c2c0703502c101d0354100455200107aa602107604c606142e915030ba14a0800381005a10000a0f41c45a01e42c0283c3e4030a42c11130702071801164001281c10341070500c4030340503c04481d1141568104802c44a103900c0c000112035210a00c0e003000a5441010841c41c4040d12881d00103a40c807a00202e0080340d10b42e0350085a00072108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 211709397 1250 211708147 211708151
    0x20d0c0819050f0708060703020901021603142a060a0e1809160b030106030903050c0d1205060301020315120a0215040f061706040f09060c0309120207030b0a0e0c030706050d 76
    0x2e683c2034032a0707242c40074024011103801101c042071515000c0d8000e00083e107414016a40c1d011105c500200103e40756520664082c9000c031122514600c05200c84450043c8000011500aa401c0300b4a010000c02903d4540201ca000401c2d04416100d0619062142e00040c500402004001100300310b0a01c280c4440002e0f00a14400384180c400c000801c20464042d50b0b0401c0c190382c030382002030b0000d06414105a052050401c4281072884061042001526a50326141c0854a045003c00100c0700001c1c4003a020368810001c0c0148026480411180b0880846070700240c0b82c1c0001c0c4007420258903050081d003101e9250341c0340401403040c0025105469440d4071a40c03606944130011a032603800d152010340c0e09010b12021401e6418a07030010842110710260100305c540b040c1d51100d00700e44d0031695103000a644c030400f00c1d04018210722020f00c600b40c5403005080d29400d540342c0c8003910302c026050030941d07956400b8150b0300400034001168101d0b801019600345541d142405030903a0701002c8400c111134 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 211710647 1250 211709397 211709413
    0x171302010905010c030206061c050304080106081905060609182b02010501030b04030e04020f160c0b0c031c110703170a050c0a05030907050a1502010f06050d020d0c081905 75
    0x35104e160300c41030b09609640103100d26207408041c42081c007501c401035040d180b0f61555650216004000400092240b8000011f40034504840d1a00f0010700700110114400c403800c400c000709200003282c503000360f030032a10000180c88004500400b120004803c0015000c3c6501e480100035035018801142c0110300510103c1490383d4800324221442400020702110303100300443c01103440744103880e06040d009800145480c40f01440030095030000e605c00007803a0b8a181d40d0000704141103200d0802001844011414a8203401849850f8001d0b07482c3e07803200e000e4014080400b175120f50040020078410301c42580d038600740d6040040c54580072038490500c60700340c900800c3c000780e50703441014422219401c1903030038601159406c8030f4560000e025098648100d00001c01c81da0340ba01a410000c00b0350808490381c003116800041d0945941a012419140c0390480800a80d1141c0c034806600c907a044400d00243c0c1e0041c41c0c80c01c011101500180c1c45c520402580100758800710707000284580c095421503081da = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 211711897 1250 211710647 211710649
    0x10c03180f090b280b0d09020306010906210c14040902090f0f090304050109050f030f0105010e10090203010b1806120f060f0405161b050f07030605160e0d0201171302010905 76
    0x7104200c4c1070300030600140c1008105104250740602002d074211800422411441e400080c5003d80a07080800030719503554080181101380311400102945041080105801c03a44841201c8102c030300c00d812081600c0c1d080010140d44503845240b01907401818480c10b400c1c407480001c80d0789001c89031702c4580180400801c811540c000103480490b83c05a6842035040d080005120759421040030158051003103144113103540302c01303002d41c41c064692012401050b1500b903034820150103083d804202c030317284108010b05c001d42d60b01007120311850f200044145001500c1d0041030052044c0d045174001e1046503018010b43c1e1003208075040c041c450485480003030f464000d0410080b1041900c0076000c0382d9082425031030450003031080402040d10103081e0341c0c0d14001c9858181c100040c2166080c002d81009070180200111803066075003003040c85090004041c0b610502500c1c620101800601c50800d60f4500c2c0216885501d0004400c07042c050a81c5940c1800c44c80d2140d84c1d020701c14102d000c85c440700f0b804105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 211713147 1250 211711897 211711939
    0x1002120601090b1303331a0612040b1f0b07110402250204020f0708090a060201060305192609030f060c041e030609050a0302010614010c03180f090b 65
    0x90300c01520901c060344c0b0b196540d441c0801914aa4041100c0d8446191b900c1009802c0f41700140300e90122000308500d000100b004c40300d1440e4200c01449440d081c403890740100c03200798901d40e00c00e500049031541034a9007044490300316a0b0040b0021160030041c004504002c40c9000381c144d95100300107064400f8415010070007a0b00420300f1000081c03090520400c4c03029046035680c41c1c15400607100518015400030b070b65109501104083c0e69001c0d00058210950800d542420300400aa00c000c015160841c1d440907222050b112030700301040341c800d01c0c030b40901092640d40c3d11b20700c12099144a12030780081c09107885400c0a02007030f01c01d0041802103c808103010a1162081001050035450300741460401104450014492181080d6407000800000c405100b107061103801040180a4400c45203030003401d580490f00303c1e50303c8070900383c2d440c0910b0360008140341d0308035418106100e409148200982029038140e205084850904000282d904a2540a0407100000f81c41454021400804081c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 211714397 1250 211713147 211713157
    0x50606030106141c0507120318150c08041509080f2808120403031508070b090603070e190602010b01030506060a080601090e0108070f05030c030606121002120601090b 73
    0x4020701c11011081024600301041d4200044c000740580303405201d640351545002c0450300204002e50426034800c0606801601c598998521420110091410300104000707440500c43c401c0c042c080107032000000c11211070151005400f0781c040507203200d41d160708020700141039489400000d0003000c3e214002d215010a14400882c248141010812404807841444090002c4240d5050400b400108921828001b00b58010b41c003c0d680845c90340d00c081c0c0118005004c03548844d13050744c000c000030040b0403081025603070410000c59910f600c83d585c0007000c2c2d418841400c5a07aa00c86030100c070004001069007014000e41c1e415a00070445103000900640407114180d03505a88030342d060000707401c010301c0751807020303805403040c5802024295200340c10581078000b81c001c10071540002d03009005450704d0501460007400120000e11304000d02d900803c3e1281301c042c0040740182415503007d211071900f00241c0c4000446003038110344d140081a202001c518095800c0c03800102200d00000c0c03c1031504054036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 211715647 1250 211714397 211714409
    0x2f070e130b01170f0615010e1906051b01090b0f0604150b030a060509100602060c0301030f0b04140d0302070b060907022e0f0516050414090406020c0a0f050606030106 73
    0x71141e401c1c002540800301d00300480c1503242c851906081050318080c4101e500405162040c4840b016103c8005018517004540c0035004030076003c0b5607070342c500305907072200c00b200c00c135040c100c1c1d94900008901c02010212610000d60390b003007080307490400101c4210b4610801e08100c803c83e0b2911110200310950b2000342c032030000044011000e1003000d8010b001580c208080e55000124680c0e1100032410702c41007110490322000d031054081001c0ca40620002d50701050000b000b51640d07065540b1080b10880a600290001c00389100007010001a044c4490b00000c4038001c4840145500b140240030354072481c4216440480720001c04c503e42001e00d41d0900464942d005130201c00140032002c4000c050344800c480d400c21ba030905000c950039a92013021080c1c004117a01080700e144ca00c00c0c01415078030480000003001400c01080100d0a040d16041c070f98144102d030007000382c1e103035418814040d00608285074041e002e0380750070f141040103003401e07240c0c4188240240c1e0440d80c0c0c0c0300f0400d400c80360644150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 211716897 1250 211715647 211715663
    0x402151303021c050d0801030c06030b1c060b03030d06091401050906010503070c0f0308150d02061e040315270f2406030c0512011a012f070e13 63
    0x500c01882d20300c0b418003c03201c1504003449640b41c40e4892134170784905004880c011131241e200500070311403030345c0101c00944901d05080c0708840060340800c540240e00850011a841c00c441c0e000c041002c83e405c54100d54000904494039840c0c1d0000d00c1d00140700f0b901c1381d800140d1500d4118000c42807610082070483e01c0080c00001542d48480040d01c10360320051115040004040b60000000c19020103856030602036551128585005c40445130082c1c4030100c031620883e0070906407070060ba10042210300c107044900001d101108a00c0000c1201d0080c0c0d0001030010b405090b1940e010007065101c034011721103090701d00000801c0c2c0040c6070301410401d000980000603454403800802c40e81e201d0f801100143c41512031240c2848114401225659002110211880b640c00c006038a402c0c40c000d40c0c04030249000304980c0058002195084501d5001d10381800310242c1c40910350314180c4001e18528802090900e00b01104003211a190110f5002d100c0e804040701002c1102d544400810059080e03200403a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 211718147 1250 211716897 211716899
    0x209130e030901030e1504080901030b0306090a080c0f010e030702090f011a0a0512070c03180806040605061216031707020f090405010209060c011b030c020d050c010b09070804021513 80
    0x1100a0a91a810340c80b403846196a0034440848080411f03100c1c0c0e000d10000f5403641001c034001025500340c6000c0ca4401d41c4603000b031010800000c60000009030f4881842640e845001e000a824a08051002c820552030294030fa510000c0100c02081d05e94070840310b41100c2ea84406401c05556028080e00c1891255114294000481ca0340217000501e22804c0c203030300300b258100748840d03201c8080302c50000151340710300c15004158116036180c07040b59000c4135403095241009403145e0b41d030030000c001078459500c640110384170703440d548400500c540041056603023000501c61081000d030314620040301d03202e946214035107146c1c00038019100c5c06540240107039070a070410780801101d801d001c2e100769a01c0d5030030000500c5a82d02c0758014060039405100100d110800c3c9651021009403185071502490308003c2d1248500d0b50208010041c004a82425501c44020501881c014081c55502c6904000c20b0340502c000f064002d0b21a42c441ca200f103804103102d4104400751071070b901030889001942504014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 211719397 1250 211718147 211718149
    0x60703151806030f080c0d1e0320070b0405060603060103080708090a05130e0606150301030f0f081222020f06070f0c0306020702010206071704021c060f0209130e0309 73
    0x8500c811141c02001c0100e4800e459031030f003840980108070200c03007004d4002800104403030103000b20f001190903400c11400903016080e00d0504800c00400b11001c041da20298469803032a030380b000304d03111010350b100759403105420324046815120a075400d903028445d420004115240004906060701c9c0c0c032050080c201085940c031640244c008411485d404013503250301003800c3e10766031265003138980107400224411500a41030b6003401d2000e007e45000e0302024440c8040c012281003160b04480e03100e038500803140383c1400d102c0c90000114038002c01900300065100040d68910700031a0207900c0d100e00c52082d0207403514a20340c0f015000c0f00000d41080c1083c942258030300c2d088014006d001d0013280c1079554444150307598400041140c20480e505c035030100e081004d41d40d040041c1070380032815040c8900e9040c494a401a80c840000380028070802c101c0c81c0d14603840c01e06d50740c1d0300c1e140c41e07100f2810700030a02d98400c80340c007a4101c110101e00421224403150040141030060700c1500306400c000e50315140b1540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 211720647 1250 211719397 211719419
    0xe070f02070906081f021909090f091a09032205090f071d010909060806090123040807021309111f0905040203070e060a05072f01080928020306070315 66
    0x174075540f5496070a000c14400c194001003640d464220341e980b001c03052800c0500480480d13241c244102001e500c0e000c0008000f801c1d001c02c49d40500007000e40700256548050304180345100c0c00c503d0480f008106180300b0500c8100107255011756404460040450761040b2005400a100311043e01c0080d54049141403403201e11118000d070a4011f00d810500716803140340c14070a07500746501401080d0711540812180341d40c280b00b8052071a10000f84001401d140d08103c6400400207040645400d200150840c11540c030728a100341c1075135164100307102d40d54860521b0034000c0880030040f4041c490b61039030f519110f0491000c64000700780d5038440102d42070501081c0002500300070040e40600040314102c81241d51458003900c141310056403803d5580700a86814064100c07042da82495034080210342007003c10030f8041e40d1940309401e107000643c83e0746099007c3d103800d1448140b1081e84404107100e1481c00d90282514200354001d5084410790303100c0c00800c408460012500c015a10007006050003071100302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211721897 1250 211720647 211720693
    0x90901050d240b06070b04060c030c02070603050702070e090607020c011103071b0302030715090b070804031b05040e0f1c0207030f062d0b0409080405060d060e070f0207090608 77
    0x40200051183d020350110303085601541055484075111002c00c030801905002d85042c4108614051010040c0741e0b4010b5078030007250158605143d01d4800081e541482000010010140c0007504c500700e081c140131840d1100d400795442001405158120701441d40101e41906042c900d10009615200d05d03502d6403110a8245052406011140403000000d0b0790104040ca000d804044110302e0082800000036203a03489940c80450304000510068002c1000a07081d00c1c1100c0d00306115224400c0001c041907100361181d0460341d8000d14040c0110600b0600190300c00b0380e140b02408650b0350720107444008184c02c002181910059008110034000222a1107101c05194440c240120701d00420031501c86440240600e2000ea24440d070304010003815442c024010140c0c400e407802c000040c0d00c1c0e02c640c9001d204178003030b450140c400002c0c0355410740c3c403a605c81c0c0010500c003500d1145ea0704000300001d1900c400750008100510540a0105c3e60001c9481614200c1c2c10120080c0141070300c41d41035140c03220031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 211723147 1250 211721897 211721963
    0x308010b090d0209151002071203080910150503011508071a07060204030b0f010603050708011502070e090a06050f1302040c090e0f2d040219120602090901050d 70
    0x80341c01c2400040c0c030780c554260301460b140b004641710302c0b1510051144916010005400f10750215408202d21286008124246900742c85d04040581c3c0b001042032a1890080d07029600e5842e1101d004406041c81e481101640e0b000c8000f48146041c603081d445041030180650003c0350400c0c030b000c06c11080e00031140340c00c0c0801506118201415619101c04a8100303a00907a6600104800c03c1401414021170701d000d0700e482e007002c1002d4104190010040703401402a403e035455003a00c00301500340208425802011406504c040c90710b40100126120351501c1c80c00c40346103080c140440c6241d5040203100e8070400d8000d030300840c0f20f0003540800c0050540700c0049418400140c901083d41a2104c41407403040c10078881c1155941802c00c52600c4410311090061180110381c0c009003030020b070828005400a804031428420f4030144c03a452074000049030b000e070a603882410303940700c2008080e0300070740207400045440c0c400d26030343c60f4184411020078440c02002070b40c410800e1200d00c0c84c880310001c03140070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 211724397 1250 211723147 211723159
    0xa081501150c0c12030201090813050906010f02190c32040c0c060c090905010e0402011d0a1a0f04060903030f08011404020319050a02271f020c030106060e010e010206040308010b09 79
    0x1100d0b841d27080d490750148080401c284012902407281e410150700c010f4104400b80b81940054003078003002510b4992511201b0000c0040e2410607090010030403922020703000ca4046000710341280b0f940c41810708074980c12100c8201c2038916104130391425200d500d655070070341d440d0401c801c451541c400005000285c1007a00344004a031020401e100a4864640605441e404240d00c1d810035000140c007000610b401c401c0a0007103a802e11046072155080130045070110010341440002d080d1240d1103d0040400c3c004041c1404100003035900ea00441d1328007240d0007034464048020031584100c82c03401090050080345007002e0315101603410035900a582c85580b44041c006650b05140e0b280054900648804903990b40100d151800f4801d0000b42c031180310010001c000c0d40001407004210750313060444020641b00080c0c00c0c680c030980d000340000c040e0b0b00b02c001c000b00a080d4807403001034074029004071910f00242c000c01084240f5400043c580e801103401d52140402a031030700307000c2d202590082c81c03900c0e0401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 211725647 1250 211724397 211724411
    0x31202010e010f1e0b030705060a20250b160809040603080301090b0405010e06060a090801090f0b0a0b090117010207050303100305010b100507060504020a081501150c0c12030201 78
    0x112003845005000481004007041c8a00c0c014a1808500c881c510813003203443c9000b0349404140d80010380c100484105503090364442e40c02d0340c1d01340c8a01481d2004940b4100c09204031016003140498410310711101c41900720410011000d684c80300445500481074034980c00c0014440d0400c2500442c40620710078002d10345006c541c03601181c15110558821600307078070b01000520044d440c5000d401c00c08082510b0030080d07903240c90607442d444400a40041d0140100141e0003609030720807401355024080200c02400481c0e902c3c83c0c8600004805a015110011800003050b0002d0050080a11609004104240613403e05007501041030240e01d905090f59803c020078000a03d0500285200e10740c901074968a0f00d266042990075108071241691040801c4641814030940240684030740d9508010002a1982c803807005c108084416006442c09100d0816039500f001c241c50813280c1a110941c1020007100c80c4003009a424140d02761004001d907a106000b03009034005004290201c50003840003091030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 211726897 1250 211725647 211725671
    0x4080405060a030608010b030a08030412050702030d020304030317060d02131b030204030507080c0901031704090e0c030f1c030905121308060106050412020607020103090209070e151303120201 84
    0x154014020b00e0040794407040c0400c0303056003e01c503d49121100742c000c0c26404070250361b800c8182c44002d100070310110318a803c8040c014461003d8601132035029003140c000007074208002e03690303030070500c03044001030a0783e4a01c0c2041110424a0b5000701d101900b02d1000b91040e41c00c0104100b46038150641d82e9581c1c06a0f80300d60840341d03183c00781000c2c260f00c00595483c10360504505002c80e54008810355440001840e489885094500e41101d400c0905811440c0c80c02440110034401c56005101107030510f00d50030350304d007000b1803001c0c40058110300300c6245c07201d9400820f03140e201340c081c407520450180e21400c40c600e02a402201100d445002a00c44117622004408039603040900501e04440e6000010b0000d2041000303164090065401c003582007a29100000140d010b00c00d800a000e0317035000c1411000c590094001601e1164000c04034032035482c1c0352000800f1084a041c1d114440c040c40300d085950080b10408484c44091140038942020303046850b041c1c05801c14074481d40c01c542d641c12010203e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 211728147 1250 211726897 211726909
    0x806010e1c0c0504110418060b0301090f050f1605090a05100905011412070e041e02250503090d050f060a050f010e190b0d061508070803070b0103060504080405 70
    0x812041d00045031a44041d0401c2c02c46000d80780c02050040c1c0c5059001c000c1c035421442170b1412604040466140503441100c01409020258400c2702c64400100c0085410361464001c92551114080b00700404c2c1c0d01c0e012407109882c000e4981d0007902890580150006100740018845040091310344046695120086020402c00c1c6103982c00048001c0028002503900c035070b05000440301e005529003850389450303171082c00d504040c1c005401c2c00b404158105054460740c1124800780b86043c01030040c007a203100404043d40c452508032220146007400c2500100481d44040e10140d013104c001d41c00c2804550034400c0750301c1c0047e0162018410101c47c520011000c200700d41c8074a010400103e96401c004030151010281a04140349400c010000c1001c4501c10701c00b1003003041001e00700890300b01e019030045030701c3d901001c0c0041c0c2021b040060440b82840580e01c18821910000101e0744410760342d400c915244e0085000040140584400400c081540c40c6c104c0c82d006400344e0700e61803a00e81e8400000d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 211729397 1250 211728147 211728169
    0x1c02010e0609150d0e010e06090d050a11010c11010e0d090302060310080f0c0a12020f090a020c1e060108010203190c021207230304080a24020a050705060a09080a0806010e 75
    0xb2107545c4405860301429002c0c01208134a00d034080c010100c13400c1100c0710648a10f02d04c62030004121000c03c1030320b1281d200300c0104000d94911788c02000103902540c4001e24045694141100540c00d22207440c2400b90005101901da8802e5a911325201e81143d00300a06c035031019040b68051800200e01007089203041c401c0c0c1403003802400040100c20740d101c4c02d00003107507190742c480e01014180d01700000143e1200349608544a8080740c14419940d10911100c000307000b9000c1000c01171040d0a407a1040c03100950340e81c004015002d08480e01d80c4c1c5d9615515090b84001c03121a0003540561140070f225450a412000d060980d134010342d0404401380c031032420250000d81081c0c4000d5407140d4005c003103402d092a000e90544010b006149450b06000c0d1280d80c40380340c14002010701d1224a94403090b4811110045020040c804041d940c44120400003481500210700640741c80c0504004242c111030329100d40c00240b9406003145060075034200066850007801001c59042c0100715040b0039982e520410800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 211730647 1250 211729397 211729417
    0x4020406120b0a0b03180106032001030e010501080a1403090310020d0f05070e060c010603020603010e0708070306080c06090402070f061a1207090b06040308030702010501051c02010e060915 83
    0x1800025840a01c00c0c1922040400c45001e110111802e210082c020030440340e010012030786205210404400c614014181580050207a0ba525206603604205d0501e84036018070003647c0070b02880b03410b217410a08803071080c0300b00211a4419804000001c0c03030f0302d42e004a040034140c02d80e8181001000468181001a8055581d82c0c1e40020402c2c079000d19131007201e49104a201040109281a00300948290700284010344100001b08a040701000b0940243c0003441d030142109480b0b507541c0480500c042e00c15a1404003050483c030005217464401d00c89c11088900b0080284500c00301d080910619501c80b8200341c1d00300c0d800700f1002011074412461b02545034412080080c00801c900502001d1400040310f0030321540482c416001d949100040c850196038802800088180c06200011440d00c0741e0344c0700420401011040124054040d80001d0484100382d8914050100c0f0001d11909000c40000c002c1c082142407001000c1414620083c080f00140504500c1036001d052500c0c80a40c0c021072092 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 211731897 1250 211730647 211730657
    0x210020d02041d0415320601020d080c070807030302360102010b090c0d020c0a06090203060f0402060304060c050903190c0b0702130203090319020f060603071409060f04020406 77
    0x20000e811444100501d90f814000c07885005041c00da035403010100340ea02c3c80c80304054680401c0051918040c0400903d24011011503000e108a0420401104000c0780c481d03026004c1c6140200e1101e0050407020b00c40c00c00196074620b0086207a03100c40042c1c00140c0140d040660910020040b01e01d01c49041d5542d00c2601c04000c92000c070b0250010306d044401e05d000303045904240085210341c603140c50b0103412000c0011840d84400030580360f80000d00440407101c6461140c403841c902072290313aa0003c4000d038029415074a0f01c2e5070351001c5108400054500a405c5031080001401244a69000c000f10007142d1500328035000344a000685848505041c0b100e007201c400245008010310030003140b0007014030707038041410001c2c00d400141c280e4004c80500008550000300140d00b40d00144100d03016261085c40310901c1e0400710b24000d507100080303000210310b841150b0216405140004405044690520b44100103a13605018440c8800003d0300e142d42190030308550040e141e9840c005400070301020b0f070324 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 211733147 1250 211731897 211731899
    0x901080a021318061a060f030f1506070b04050f0d0f0801050a030c03080a05160b070e0301140a0c090305030a05091e010815060d050901020414031506010c030210020d0204 75
    0x100442a465200301d030301e003180760031125040381c140c0309040309602c3d40180b000540c0c5e2002c1110200061000004140d02250000702da80f81800501d000d540503403082e100203603040d660300da1141c04603022039032520750203503052041e18002203034091265405803080f42647c0c03d0389810000d03a440d091760010a9400703d6a6920030500517035101094900516085540041180ca1034940300300040450102408a80303000400c0320450380508100c8407551444400d031842004541449540d03e4425503d00000a400001e103400c02d141c14003410200000d143d1680c522621801145402080c0d050b01c2001400b41100780000454002c1c0045c02030f2180644030165900084c0003000940307e500203034030601c032241c3c0030181441c0e42d00180150b4028003e40d070203c81c010314000041d003a80200a404020030f42004208084498107401610441c1c045100e210240400c1c2403c0503151102640c2c40d4a04600100024400398450100780741b10070b0103070060b92002c4881d164100243d07808540281459a00000c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 211734397 1250 211733147 211733149
    0x9100509031506091b120c070c05040504020f040f0902060d020316050307020d1d030f01090204110403080d0b1915021002042d1509210203030304030f0e0901080a02 72
    0x4441c1d4804000204007016140500004400d40e20103400740b141c554200d844428403084c4174040712502c0b80d02580074681440d1622650245921441c400c80f0040c02d544000102d604280c005c0d940110350040c04000c1400301581480001c3c40008800d19980703841f41c680c4405a205c010007440c010b0781c141800359807454074903404074a00e52101d2200e001c00c003040003085242c07580441e81200804480c50094036012030040c04c640703880c14080c03080c1c0c1d040c082c20f030404c1c03c0000150b024100c0c041c403d640901c030380030072642000c07a140503911020304084020001043c1d00c2e0300c0740e404140d01850082880e00e00480910107015a540c440e08960000b151410a49020b20b030100030b40f01d0301000612040d07240c40d04190036084110b03454900d0042080040e0541248404100880000380001401d1400b03071000c015802000b480191040722607100004070020a02115007100c502d0040e0094021465500c0e40e90342110300003210340300c10341003004100c60100550b80d143d110078007d010708070044c001c40d82140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 211735647 1250 211734397 211734403
    0xe060901060503040314070303090c0e04060507110309010e0303040e0414060901270f06050c040f090c020619061203091412061b12010b03160201090206070b09030910050903 76
    0x703000001800014010480040e40c002c10f0b1321062003450030f4050300c4100f2440d0070342c0980750000340201042c841c0ca501040c564100000075104a014203001d20944c3c035225400d40b2400c40e00103491160303400820000c4050350140490026070640030302101d1406a4404c8840130044040e10708844000c0790100d007018020080000c2d07070b0882e407a00300802001e0480f00c00c40340e441d9804e990740894040d11200080a003d19007040c0494145c00040c1407000d4640004e8204a40c0e2180c080d070143d45038061380204d01303960325105071410990740b40c009080c2a22611815461a1401c8140403031103511010f0103c0c860f40c9d80055410704600c80d45488040c03030300300b860032000040a07601d014000d09200c4540464040001f61494000c0c0c268490b482d00160540038a02c0c0700c2c841d84030f1460703204095100019a989605000303503c42c0d03080c11502801d1a50000c03089080c2d03482c070318002c3c0d4814020701058011a00307a0303800360b070000c001c081281d01e4109464049040950b01c041c2036030205402046810781c0e41428 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 211736897 1250 211735647 211735649
    0xf120702031006050105120c16080301091a060d0203180102070b010509181509120424020703052109030114220503030a090602040503150103152f090a0e060901 70
    0x40300d083c460b03542001c000030014007400d034070a80c00d208942c01141e070320f030f4082045844090040d10008000c400504082e44641d01c2071260a43c072a00e0100b0080c4424216422510a800010101460000c41c502c02102030b400180c11400001202039941c44004024401804054859198840c0541c50402005032844000b02600e0603101c080144641141c0c2c0460098141009418017844540750340046501c4c0520041401480f040002400708046101c1c1400720400350340c0f458200c1c0701c0c204511003242c0710240c5100c0141160b0000d000c0400c00b4030348906169003031a55442c07040c20710f201c040009094440c00c0784401c0440340c0c40028001c060580d59010501d0300c0310640000c100004030b90b5240d9407440020044422150f540c4000c40c20408250120f6000348002402c4542200401d001f60540703500a11040314001080000d2150b00b03d4140140c201407a60110001c0381004074030104160702d0190b41d404ca01c109800c00103607007580d5552411502030034000c1000c641d507203019820b00661040c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 211738147 1250 211736897 211736923
    0xf09180a0c0815031f0204051302070203070503030703080f0402011704110307080d090e15040606020d110114070810090617010e03040b070201051c050106080601022b110f12070203 79
    0x12482c0b5030550304c0004144139075603043e09140c07140100240391780f0024091a000594010001e60801c06c00c1038907500904603c134000c03800d883c40c050381d6400301a900e22070600c00901050f100070010748845800108682d0050044c18084c0e101000c8100d451151403040f0340c11240000c2030749425242782003c001c1000900300c030341d006060400b040758006d407948800b4451002c03800f8051001070381031203190f10328021496018105010803030311140043d41700d01500340700c1d10005400380c1e41120b034101d05004402c0105098440c2100315142c1c03070002c49410780b00514404100c0800c0d0b40004480071140310b04401400e04910040f40080c030040c165003511402045200160b0007444140010021042125846a4242819a6940d9070310300d5483d0456880c5001200c20f61601d0000601e1a8100204a1050b01d090703003038981e80c541d034092101200c00c00c803e00045100b00444e031881464054030031070014840e01c1c02203034150441c41218034503180c3d421460405c6c00324007203030603021410200035200c14014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 211739397 1250 211738147 211738171
    0x40b090105090c130c05041206051e0c250b160e030601080309010c05100218010e0915040f09061e0e030a12021803030a030603020a050409080f09180a0c08 68
    0xf010034000b901c0c40071546418003031103559a0841c01450f020b241110010310304101030340e015100720304080005200c00c8800042801c0c524240324140c001010340580300300d42c094850381c20403e00c0d04540c0aa5141c03803060450b030301c000402c003101041580e44213074400e80d0030303c00f8400b003411862801003280c903242d040301d40130707038411301c01444004000703c01d0740d102ca0002c1c80c010a0700c15803828440d10f01144101e07480b6500744002110951001e0740e0100094500307013a2100d45203001d102c0280020300c5001c4508280c20768465850080c0351030203402c08803214841101c04540780f201074441c40c08582c0407003031158000410480c1e000c050600d500841c40c014460030051420300800c07a0000d0030212110b156081c40f0303a40020510411041d0070007641d281d0720090116502d494101002600500140c00140c0c45100d680400241d18540b07801548071240c0c3c004000f42c100902c403640201e094121900c243d40c405030303252000c8c11040b9410280340c400c034036101c80410001c00091001e07280e44805000004c00070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 211740647 1250 211739397 211739413
    0x1209040603211d06030a0506150706021312050a0f110a14090703050714030c1201081006080c0604170f01020c031207030902010e060304060b0406082803080609040c080105040b09010509 81
    0x25a6404c00e6a9202569031000700722985c400001074481006004100340000e0046545028807815074040c100c104a2074131500400e0352110052005a902814010103030760000d20b0007070000da601d121040341280706280e525400c1d400c0c20001000384410b40c00c15115000481007041c424603103502241d4125405040c2041541041c0303c0040010128400800507940000085101407003242c00b103413100300c40c00c0c00294255856100c11902ca107a52041c0030520790801c0008200040085101e5100310030080c1400e244c64a45110642c80e0940030000c0344081c007404071804141c280c2070004108003054100a15138902d5014107100300d100f400340801c000c16141258800050740c129082c440c0807901203c40d6a200d075039a10705000034103040c2c2e091642040c20320100240300040020300b03044140001554010981c47c048007500c44000b52003018002030400c2c0f01017005802d0a110480d00940a10300d8441025202d12035582598004d40d821604003000c40e08121884c6400c0c4551a040358424002d01101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 211741897 1250 211740647 211740649
    0x30b040905070b07110a090b1206010f05120c03010c0207260a020f040e07080610080313060507020604080115031a1b0307020a02090a020a17091209040603211d 70
    0x414240c003c4400801e0000742d4030081c07000d002c1c3d0a40310343e0b0f03008100000f40342c1c4a6850074042c068440081d4010f588801c0e001010b46d1001c12950305841404118400c440c0c41e0000b00150f0700c00488400d107490080e0791a0040b80d440a02440507112070701d80040c402c6524040c0d2000746442200f01d13090715102d410008881041c804245013102c5501201c40c0080c001d00c040c006001000034800c90380c168441d186001030746000114145115180110783d0106166940300d0031030702c0e841100014882004541c40030310100340580301920032280058002404c1c907480340509401c40350240760507031a41c038000380100100034844002c1000d0604840d816005410040c00042c10100c000d449108209030220001d070005100f001204901d540080400b070b0b040c10422241c0c0c0095211801c4000000c1e644680140b8500c1b150040314060720110000707082c03601d240840440c154000410243e40592201c00000110b07484151a0060015802140c1412031000341d002e8104020101c800000c540762402d00961 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 211743147 1250 211741897 211741903
    0x1051614030c030705040e041a07090302010c0212030c19060b040c020a0f0203120406120b0a0806070c0309180b0102011401051804020a0503060702071e05150a0c140d030b040905 78
    0xc0070b000c1e80207507101d80300c1040c00d071118000d50b0481002d1104000030401444120384403c3d5158055a030088140d803600881145c4200340782c00043e02040c141e0110700700500340700c1100d105c03441091b0203507418006082e201ca0b082010600c23100d1100e007660040708041c05980c0c40355000d2214111800c01140c404600c01075100d445440000d0814114141e407001503403400e2108040c50200314015030790b20340c1c8814001d440120791042030288145050b204400d9400c0c41502c40081c1c80741c81c4021314165840c4a02226100c406c00c40031030412a14080000381500c803a2404038420545100104400d48500002802c449010314640c8803400302400400450b215105607a00d041c4c6a000d850280350340368004640501210b07809290140704c0c08040000300c0b07034089040701c1038030025920341ca000c101d0340782c00c00c0c24001c50b800341941c0400315109586480c060300f4000e11f11100782e404e00c061412840d0311001d14813429850201002d130401c9103c10049945846000400f40302250100000d500d10b13214155 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 211744397 1250 211743147 211743151
    0x80609160909020a09020f0a0e1017180a0f0312050f16030608060103030c05060c0f03071d0a080d1b0503043f020103060602030901021507120e0105161403 68
    0x86581d980c21034401551268000b81c03000e0017074581d066541340a84143c00006d64070054028001482203030040d0141e251240c2640c222600c0c6544607141d02c01300c200c1950452201070305003015220b024aa121030070b20284030f101c65280c010580c00e01e10303070401c1c00c0c064081c64440c2c1d0f408120502d40020815103840602541d03401a034001903196141c01011400d500070007294100d424a840b59100005c100f650040c101d0001034481d0007642c00300c0c0c55514054507030303010307800f000801400184001241e00d0b20842c840d001c002a01c658000c2d00c4107a00001c070b089280190007000c1da6800c00781e0032140d0103030000403034105d003036001d42d145100c00c0c415111280c44c0d0041780510303032000481503030aa190300300201084030716030408802c4040a5013088204000a186508105e0100c2e0034160006580d038008401c0d140c0d03111040e009010314450340121241c0d01c403001400c081c00d112039120200104045c1e03104503110b07006c44000005107418021210781080c60841010010080440707900090300841f6802d5076 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 211745647 1250 211744397 211744409
    0x40e0d0f0207030803101703030403020303040803040c09020714010606180504200a090f0509010501200f12070501050606030408040b090d06110d050708330307060908060916 76
    0x40e2545081010490418045900180c441c410203c2449403d800f240c04510071503103444002c070003200890003200e0703e80c041141c000d40941c1080c800240410125001964080e102d030018108064031006c4900407030300580ea050302c0c030510721603584109200c00d102d201302810050a2280403841c00f1124201d04000c90302800e800343d40c84410f180c9142243d025540101c05520100b25120704205034024942045072103001c0680f410888000354604141002605035181a0754641d000c81220050f48540d00301c44002010300e11901c0044894204e06100240c3d80d4192025032903502c0801c0c0c184070342036038409805148220003c00520000681000c1105c040f5421080070a4030b40f1400000900000300391180500a203003410701c00620240500000d1143d00c1c820042085151160b0030100e52182c1e08550104c591006159454101c051103110f00104e0303085000110400140d08010030300341525a80101c000c00d640c06418007242106001095104000070001c050070510442401550502c0344229 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 211746897 1250 211745647 211745657
    0x20615091b0d02040807180c030209060322020901120b0906010b030402012a0b19090c061817010c0f0f080412020c040507020c0a090e0304030219090e1506040e0d 71
    0x3080c82c03403096010343d0000e0003400c0c2502d02e82c2d40c0c3c62a58a182080000812108034a451100c0d1099406482a600f003118050030700e504660301e0201c4601d844901b512015003c01a008036000140d403001e140b94060515031000c500740740030901e00140358840160059090760090303401404117808400903291b10640910740010b00f038482c0c09143d59040004c1130000f190300100320504041c4401d580c0854058400300b00c0c0c18022040d0f84071024119030001c500203119540c00b42080146d60f2044009081c1a600d185d6181c14040e602c1c44004014116044214a0f036510340641011094010b101a161444281008250701442c600010090000240b0003412422603150b0740d240640308100c040c150300c101078001c1146050820f0043d5460341e0300e140b803600c41c05c00a44080752003105401140381841403000154109400c581c04c000190085012030350320103c0f450000580c0c0c90f0540290f4543d1400701c00a0104003e500100b498041d8000707108901450400c1c144007400303400090100040c84a501c0d00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 211748147 1250 211746897 211746907
    0x40605040c120605060906310b091503010b06070305041a0c060405161202062d0708090415080c0f030f010914070e010b03010e040f06020307020615091b 67
    0x7a035282503030856848180b034010240c0400c5180d07406607024042c12981c0c042140c0d607031000c1042960202c4584401c50b4660342c0400302660b078103156442806651003010505040d0320380880e00c951021103000c03c0d00702103400540401d00342072040d00a20081920140c1c51704520392070142c07207441544a1041d0740a6120715500c2010240000e48110a0221040d2211414507081080c2e44c0c80300701940310460012020001109004101140e070420b50291400d030800c6a451118050703151070741416000c00f54940500031408040c00b0040c00028456280d060b100d403550743c02d20048407425101500c1c112600401400341400006074a9503802c1e04455a070320410792440400d0800c4d19590400c00c40c1d40c2082207071010004010400a482c45c0d6030021030301c0b2540d4070301c03451003408828800c0282c4180c00b0401817140581e04201b5941c483e0064500e0680c0b404a60f0f2044100da00c201c50a0006820640510010a07201b1002c501d81e00f408540300d04c1c0504140c40c07031200314410b050401c503000d00c00017a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 211749397 1250 211748147 211748153
    0x150204030c0909060606020304120803060a03050d1206050102121206130f0c0210050411091b03010608060405070906120c03090f0605061816080402030109051c0e011704060504 77
    0x12100503640c4050341c4030085503503611000140000c0c0310103c880a0400b0340c0407480c14400010f40381150300002d003125400c20182ca4150303aa41c00900390980000030008040082001001130010641d01c43e918090710b001c128030800c049911940082d411074000c8000c01d1a81c023002c2040d0780d4859200c43d501a150f840e00c500290400708441c00d441581420305810310001942580041c59090480e02500e009005079034008044036403c0303500070611070030102c0105a078140203080f81da00100d03903c014420618803008641007030300241e0001c000628482c04101890405024685e000801401c207045003504000014260f41025007040d01c2c0d656170764070f21144091182d017000c25005c0e0070240c190300c2c280e041e003002070107400c0403542c0600a204a4000300101041050024071560190b944d484a40c4080c03481101c50b1031300640140d9040d9260410b030b2010990511007901031501046000c001800c0341c12015010000490307080e818010300e035035013011400804000c1584580d02c02c40005043d03981c1e10f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 211750647 1250 211749397 211749401
    0x30c130b1002010b01030e01020f030a021e030406051b09031507090b0c03092b03080402010512091b01030e120918090a0b010b03130201140c2d0114010315 68
    0x4442603920010180c228420682c042d0300001e0220030030303a4148170030401c80c038281c4d00381c1c4140041219000c0b030400005a41b5442c4e54094051204101070005016402004c0328075180c206580903290140c0d200c042c403000810101032204102410022107080280c2480000c2c2c0342d00381800550849010607002881c0303e4071480b07180000c8c3c403510400944031401303444d80642e260003910005010705c0329070322094044101d50512100c07070451024043c0b40c1084540e012a80000c1c0940101d05200381800750000e10116817010b50310520040c0c00a01040b44154604e806c1001d0b081505414189400c40e94000d10030f000c04c420504540403050741c0e507100383d00c07804680c009401203018402c4501e03100910038102d50110302020202e01440c0005071503621540094001e1100303441100c12481042c464400550081e40402301e403100118800d0705000072140c0b504e050000b251701803007080742103003803014501c105543e542100300782c404000c01c038601000a400c28100b1040c04003a00e40c01000380e01e00f41c1c400c0c1f07035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 211751897 1250 211750647 211750661
    0x50a0f11030d0f0507020604050a030c1509050319050307020c010c0c0905010b0d060501090e07081305010507050a12060e04020105161e110d02060405010309060204030606061e030902030c13 83
    0xa402142d640b4103200382c0e035800520f2480c05260203542440e000c24800d83c07000811a002e0b42e0440c028000c60501e66405880032041c05000305c4803040d9043c24100307107107035a01c180303002c050246000e1035031520129020000c0081011035041031010038003c3c008038541c00550042d0b07280c3c4c00c3c207007580000c2d00790030065016006503004116840c144000842d40e00000c50240121001142040c81390907103c8006640b400540d01910701e0b0f03c00801d000446c0140f01d810219004140002425002582501c0301c1d4250342d0100c0e03107080481c400091380403910b0f600600745807899114000410003281030402000c5c00e41c1e030140c0080c2c1085400706010003415001811004500da0012070101c00c0d20b01741000c1c515009100c0001c8d201082d0749140c1804a0400c1031100c5c0c04c5c194000c1003945000e051400540c004c01a000d400e582041e4248800300004201d4402d00015040d0358540204e01e08140529150b1000f100b154201018141200c5d5401601c2c001400e160823942100c1921a480600e5020002407803c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 211753147 1250 211751897 211751927
    0xc150c02030f030a0212040518060d2a210609140a0c060f0206090c09090102090409200316030201030209010e030613021203040806130305090907110c09040201050a0f 73
    0x3a8190120044070004010425a40703136030241c440c02100b08036550047e000b18415141c00c2041c0c04da800c81200050b001c215032140004050942c1d1220503201c01200840030080840e00070b442d200d100300a074102ca480d0308001c15130300f540000c0058402e81c0196601020000040c115501e44002504000300e12000c010007507a1841242c0721600355040c003030301421a0744284e0021900c1c2c3c1d1003480d00c2920115800f8464260f2170000c080c0c0f098880700f4440c41c0a001044031000b07540c240301c6064030b030303981d0f000303a456050080c1c0e036080a6000c0200c1205864108a4031144254403d542c0074000010000881301180e1302400c0050300c5603040c1006807409021400c805034140616820005a01120b6404100b91402a1038840d600742001065595a101d54018144075501050002e05041416034031030400b24400c3c500241441848000f04080900603200540450041181d0881b540c0d070070800354803021011140e45000742030680000c0c0c103d2040090f80740400c080442c0d1320080d40e000e4100346c060006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 211754397 1250 211753147 211753153
    0x611070b0c04051008041112120c060f07020705030a080306150301060309030e190b0d150b0408010b04050c1c27060b1906180f0b190c0c150c0203 64
    0x90700d81d0110800b64043c2c0074a80c4958600c0710b000c1040d901c01d00b810f51040713912017600d50410b800f0500300440129101d40382480740c0306050b03c041ca10106180130b07203800341d200002002241014003150300000d4000f045001150f10001c4208031507600006c51481164000c20040d80e261190400324140e5024401402c00c001400800045d105130b1560040300d095000f95682c51a5142010800c45007a20200c800c0b25842c3d421141408450f070100300400c20408036410002d14680140780c4942c0b00b801c10380c42607000d41c6000c0f07801c10820500307001d22441148102c0307081006181842c071412080c0100c421a201c030018502040e01c00342655440380c03500c014645010180c0c0c01051a07104003003e140001201da4a09040700c01c034050500d44040781c9103585001030003100c1804c101003140d54800b8540001c2c4000503001e0005210b04081d03020340c002c0c00390303800f0703c595a11038a850074048400e00900101000544484000490030205071281030b01d21500f4100c0d60b5900c0c04a084075502c440d003d01030340c540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 211755647 1250 211754397 211754401
    0xf0503060609074e090b0c0d02130e040210050406050a0e120a050606010314010b070206070804120c03020907050c0c0f061c060e0105031c0806041113030605060604050d0611070b 78
    0x206203040b1804c2c1c0d0112500003c28450070100049042da00c24400080202c84440041582024450701900c0c5842d605d00006060480040000250702c0f001c0c0c0c040c40381500c0b4001400203500703046c07003407880700700c0c0340d00707040d868180b401100501c280b040c04030540070404000d20610fa580e0b103040c500100d0382d80320003c0b1803c00f505420b029444400c19203429020900d8642040011401020110304a5074219101800e0032203e40a000c1300b50f010032400c9035406001c000228007a414094080e00c0e80d4010710701c5c003c5880c294410701031003520107018a07080c40310500c030302c6032444000240c00030f00280a0701d80d0140303100403002041c0d0701e000743d0f809260221a90307020350300b0002103a032182e41200c3e40041054080c0c0da03202c044c140c442c02d9102c0b01680d244c40a0f045024924000d4241d140c001101410010b601c40b078a460010854011008209400e5071001d410001e00c4640c0c05500e4102c5d00c21201d1514081c44c1100082e1a030040460041032140c4410312840c186401c00181c949107504050310440714 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 211756897 1250 211755647 211755737
    0x20f0607030902010c050d11010605011704020405040305040e07020a1e0209041203021b01020903010c0801050d08030402030a12030e0106080c03071e0906060c060e01110f0903010f0e01060f050306060907 89
    0x885888d0030200d01540c60a4030020f081d40c443e48901232181c03006018160182c8a80d000e200190100400940602600f0080016079400803100d2a100d08181d0f40030749421180361a0140724216103003d8250000c2a01d840040507994041401d604207a02c400c81c02444a4408020340103070060a032606010f0204410b0030f100c0c54019002040c40c3c0b03404400801071400c2a42054032400d1080c0a030780d070841c101e12115400961060011a003085c00102110104541c6680b4122491920300d01040060f40390742e2a91045442409074002421564015021412460010075642e0701c440c41001d041550301d20501c0802185275840b400030b40910101404004e456000150442c0c0200e00b01322042c501d010314550030fa01040c07280c580c5200380480700f42d00e441c185004403501504130743d00c030700d270325543e07410040461854038452160b1004244002151007031030150b912082d04c002ea4030090280d001801001a1a070760444695405030003414585021541440030ba41040f01300d489080009403101544949 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 211758147 1250 211756897 211756907
    0x2010b040e1605090f0601050a030f06060f11012912060403081b040b04030206090f0d060501090b03010e030f070c0b0301080715020f0a08030a2702040c020f0607030902010c050d 78
    0x5841c0307140c942c00c6101a640c10a00401c0d40080350b22032440082c010116815601c0780005000c0b0700414600810925201c50300c05080b20385941c00640402c01440c0c4101146800104071010080600005c004444c2c1e0640c4031f00f5003400303440d42440988643c09207030245a44500540c0b01005208048641c149014074002d4141c01d02074419040d840c59665a414010020f034040f18140c420001c091410700c1c0c555400d01c00f843e0001c4030a26842100a001c0715400c0d244c1036203034241c05000b40d1021606524140940044401550903d0302a9041c1440b010900600000312800c080040b412581da0b0b07a000d0403c100043c03403c0e00100f6034000000300014143c0340000340c140940e50380c030180000180320031000b41c2c1d581020070051010b50304007503103207804200d2000c055036000c403d01e0400b0800290316024400071410300c1109121003100795007a0815810284240981580280001c2404500d20048d440d51450001c06000415450728800c00441e441800a2600681c2c0142100c0d40ca00a48001070300d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 211759397 1250 211758147 211758163
    0xa0210200634020c060d02121306060504020a0512090f03071212060e040b04140a0602070b061912050307080c010b100509130509010917130911040b090102010b040e 72
    0x542e40312011408961000316070300e500900b9140c0d40080c8603009065052100b0f6801ca003e44650740b03a07007409401e40521418061b240709507018800c0c03c106c040f00e803030887c00301c4d2003d42003540914814001c040c55260400202c03941e0720816032000c00280d0300d60a82600c4c107000d030700d410019808007192103030400c411070080b201c48400301d03101d50300340b006014403071011a8464030400110b03a11400100f004100bc06581da5080f50003443d20350761404015443c94606003c012080761402d500081e61418050a070800b02c4d006403007203907864061914095103060003a500d004806070f01d1410f5600c4020080100101c4180c10743c4401c030151118110000140204500f501c0c0900070b884010380741502510400485100000003130808000020b01a058001048000c040729440d40da280511300214225000030403800081e104400c0c0e440d503441001e05018100341d805000228100700c8146d140038020302c241c41c269088800da00781c0314195400100e026005022000e40c1040c505082d0040892010503100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 211760647 1250 211759397 211759441
    0x3050129090c040306020703020f120a0216050f010f020a050a0606090b010908030307110a02090408130b0405100c052d150405070303030b130c030c110a02102006 71
    0x851940886030520040240445004581041c200420b10014030036034042e280c03103030003032040320203035076181c91424609207010f10000444040454401c0002c2d80c10000a6035a0025410300580c1d1480d04c0c0200f2015000d1040f9141840031484049200034800c20600f90780c03a0300007003114800d1207603040c00c1004012a00940c0a2181010342d00202d950003884254116180c400c0214515907680710111400786080754140050b0241e911150050303580c045109000ba409148010b9580a041c0c00b103020300700b801e9020042d680740510041000380e48045014400d0325160030f122001c2c0b8074500c0e007182040248038035040c846801680d8122400301c42c840350030318401100211500c03082202507640039410700f03c90040480e030001070140006880380d04011003042d4041e041400f4001b41c07103d0754096422281d03060001955031566103102c158004800c5081042c00c2010b0000004642c0109a010440d81c003c1e000344907203801607070404100c003161781c4207001c003030002c5d03501c40e0034154000e1500d400b400c0021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 211761897 1250 211760647 211760711
    0xc0a201c050c010809070302031209100c05030d05070302090d12080705040f12030c0b0c030f07080609040605101d16140409091a040f0302060109021804090c030501 72
    0x1200d03000303800d085019032141d0050010180101c03940011101e041c801441054203014a020000058900300440c0056200b000346207611004840c0078441550780503070100c0d0411122806620111b0004400c560807280310b440041080da039440c5080d000382c814024000c0e001000440180c040c44071a19881035640c40700e55401d640c60301e940a045515021354014124201d90800c401c00c900b52203e0311800600d4440d0420340113050740d5841324601c20000b118254903100c2d0020402c1340c4549103050040d8003c039182032201031410301e80c1c0842c04020000740018040303652800030803501c80021a4070402090b0403103100340006031541e00c0c0c58a07550b003aa60300c0c50741c102c00c8401043e4140034062081200106481090400d482c040303244029061030841550803464010030012402d020034805881240101015261000d451130000d1130808142d1128480c1c503c10300240352000107220014140c10f20440b40491a040f6078140030f821881154030081c41d41d80780a0842e40c00707070300000441104050b8403a02c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 211763147 1250 211761897 211761919
    0x507020103050a020306101d0901060c0c050306011a0d14070f02150c120c0904020d1e05040b0619080a0321020405060301210c0f150201140c0c0a20 65
    0x3c04143d001c1510300f254003514000c00b11101500c84c00207603039441c9052000600080348007011401e2894286c01c5000001d0780c017040d10050101660028008000640040108ad8501101802c80000301e600c0c5042440c00084c0d10500400d40f80c00010a805101111140718248018040d280201c0c0e41500c4001d40958401c0050514203000454413070740440e100d03149415078104000e40b0314000145941c0406000b4411000c0a80f106e1001e044030010302107001480921524102c054825032403081c900c05414201003100103181c2c607003e640c006801340c9403030380382d1250780011016540f0560130125072846210120f2083c10b40c002c1c1079401c24120040c418a1303803007410340c0540c01d034426406121340000c010001005242c08144004034440400021410701c051299140f214101490b07000601403d2415802d00c0400c0b1055481c0140094500003008449003113959004542c100030400c030a041008118203049410620a00d8003d50b80031013804508400e05540384100310303d8141003400340c4140b00d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 211764397 1250 211763147 211763161
    0xc0b010e0414072c130204090c0e0c04062703080a0c0204020d0c14030103050604030f030f0c020109020a1d0a050424091502040e15030f1b1201090c06052206050702010305 75
    0x4000d40501486004a0340c0c17810182c0a1002234866401c2c206c40c600c0707405200080442803041103a028621524209907200d1814000800f00c0d58000200340b90140d02c508080002080c90005004803030f4407040d4580c81d208060402d840600d495140a500680005101c00364042958400c0e50f5003561030f140d40c0d41e0320400c1e0495412034042400003d02030340c4041c01080c0032038080d071009503802c4042d28010403480d01c1c80e41c809040c2c0314010403800150307441d0040c140c11480e2940a11000d04028140c405041d044035800c40b030400409051290510380d1200441c061182c40c0c1140080a142e102004071200803426982c00104200c20095a1804040047d000d4544043c002c540032a0444940c3c40051b446840640c00b41c907000200c000e03030511404003050030100090001040b51400001035262803111300d002d1040c6102c0d2031001c1041d1344d260000300c00008000c6107410302a10800c0c03030170603203458405013809403c902000394001d41c0080c04070300241f00c90b0700c5002080301a00c02c0e80d05004a8a0b400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 211765647 1250 211764397 211764479
    0x21302070f0605060a03080a0206071e020307060f020d02070c03061b080a0b0d0b090f0709020903030319060506030a0c0f0c0c120309170607020d0c0b010e041407 71
    0x80004000c18811001c0401040c6103401494000788020003185065a8960b02c0d2809980001d85c00c0015800800400c00b540b43c001001094030b4947c401c90006c41200444029101c0c0704540b0300528181d9505401e40c2c030803403583e05852045c088030030115521240c5041203c45003045100480c0c4642c10301d010003842c41c025100801060700e081c3c54204041d1a4050203201410b140429650405509a100000b161000c080f007405003601202405c0d0f070003940c454960034030800d0340100306170500401482003a0745001044950016030101c00342803075000c80b2174400260145505c00d42c0d0040b03000c0180060900c50f42d0140c0803010194580e40d031100e10303503d010303510b01e800a6005072804840c00d0b000c0041410901a0642e114803038030b05151529100e04014400002c01860556650b20040c02c00038255010083d102d80600f0906004000441d507036941581202e0501072031341d59440d4600810100642244d483e002403a2180503600e1040d15551080b45800780c4c00809502210f2040365181558205 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 211766897 1250 211765647 211765657
    0x408060403030920060301050f04180818150403030f0212040e060f0904210c051605010801050a0e0c07020d020301020c2808030a02070206041508060108070f1d060d06090207021302 79
    0xb070045c6045a10341404c2110b540901d20042d50050303100e0647c20720a2000c4958404228031550920b92628200b5a203001c0c07d52684200340e0242000ca02c4640010075003400707860032240e1516010721500054041241010340da041204108100403501103129550202018421501075172044050034104040084942c000d4030050204002001c4000080007209a40c000d41d803164107140300c1088041c0c2d2203501c1e21401d00080c03101d50302046400d01c890340c0c3c0601c156004020440e040c48c1c0e49070610003a011940f02c00f501c22000b030640018510115161464103146441c2c00400864685d23142008050311200d40286400088001e8194040c0c200d450056880520b900040401e0075542c829800c00d0003940f2010099074000028040052400c003038581c90044486a0f5403138080c242030900000d008100e018021009002d11062080d102e25400f0020310030803e03041807055107030100000420102d01c00c06141c1c03e407683c03d103a0007080121280d002030414038425584c4090690040446004030300030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 211768147 1250 211766897 211766899
    0x3022b050601060f0201112a0c0a0305060a14060907111203010305010b0a1509050d11030d050d18020f010f09030503031807140901060c051c030f0506010819020c030408060403030920 80
    0x2034840c180d00404920b58101c201908d0308a40601d0f504000251040017030341d204413203650040c030410481d41518000d60002070156a143d56140c200040040d800f91001403c00c0704001d400e03c1604c2c0f0f400020084121004203920001c1d0f5a5612814200d010b03229680229005141c060320016180301c50320656941c101c0c0c986d0394041d805013400d007000300c0301454990541e40240d140000640300d580a00c4019040500e58807001d6490182c03440c800203450420340c94001c00d041c8031800001688450700283c403c200240b822034501c2d82e6001c400c1c1ea0310074941c1c1015065200100410209218201c0309025844c000001c41d900d44d0303500d5040950280302d91801c1c5070040100001003006902903c08174494510a03030070f44900741c14015003070711088552284240003984a036040c260900c420311810790092001e29108145103060601e0078151109000741c1c204503076000810720310423803050007900c02525003a0161603c60509040080150a041d070040c0c80c070511410fa400a5550111030350050140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 211769397 1250 211768147 211768177
    0x108090709020f0d2301060e030601060f05130f1d0c0f1608030405100f0c140f0706050f0609090d080c0901120207140c010903022b050601060f020111 66
    0x801c0c20350110107500650040d01007600103116406038166540185000c844038290604990400d400e1908802d02040c0d000b042401a201050351258402003100d506550050a14040a20760a1001c407558803a400d1050141e2544240228088034842d00310001c5480400040f445211324407848001031100b6600080c21280c100021038060000d04050301c40a2a0354080c0d000107007558071903101960040707804644542280165240c03480807848bc4c8542903c11207001c1160715445d540260440841c0e405052070850f020070100300d5582c401382100c1200303034422401c0c04981021030501a841d1015540c541c031a491484c005120a040000c0000980c142c07aa90040e15840300f100492107640040d04c164100480b40c401030352007100f2070005010300b91040303010440112a07101b01d581805642002e00c0e0410818681c20009a980c82d80d040c185060a100c90107460054038210040b40196080001c0650098800028400b50060005511240c85800030301910020700100c11040c8503105104032044d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 211770647 1250 211769397 211769399
    0xe0c032104030b090a0507090f060b180409080f0f040e07030504021e010201021902030703020d2c0310050f04210c030818030c070302030c040c051b0a1b0501030b01080907 75
    0x340702c006081d13030051126810ba41081c9401e86440f0f00303241d156000400b010b0348510400c0b007100400d204401c001c00600e601282861a1505401c0f9450040c402140c4a1a25a0403803801d120b0340700308441154038950728155841c00715800350308a68005204180e10014001c0c001100d09000f40100392040b540140300c0d915010301060720004007100d014403141199030078800904200c3c00c1c05145290311856070011510350b000c51800924080d11240e1620400c0003408030510451b03603100c0c0c3d21254612289410880f10301c0040400c0c07030304000807603103110142090103002032142d203c04254041e42c052003c0b24118801007540008800248000303100042c4868811400300344940740d032981119208001c0e000802e02d2b09002840c5030400c1d40d150f01e080d004504200110721f000c0100e4054814180c40c00d10142e10f04590160160003626406001460b4810005500796001c0c407c03100b6180d4080741801c4070002c0007002d00b40d40451030003114042450410120943d40c001c40640388500c1002c0d00402c422 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 211771897 1250 211770647 211770653
    0xf100e1207060e0d090302032406041a0a060f1206080604020402090102010905011b03060807081b01090806070c2d020f01030b090901021312080904110702040e0c03210403 75
    0x550301c000001d660156030b451100008000034015200182c0b195070b1607095403821030041500300242070070040d000402448003840c049a15000841d440380084400140c1c01daa4540c18000c20034207600d466031300c14038121001c900a500100721581d0041c0582e40c001040500c41c00e5003080718514050360301c8030361040c40040d006207801d030000c002d8080184000303e2032040039a02c1d203003942ca4064510303161140f10b64040e00e15551500ca24030081807803400801256191414580d111028048590400d0f40c1c1484011350340d2b4000c07058100101100303402c444861401600082c481101d0314030441c2c07040580001150504400348038800149180e0b03800c0d050b520b9030341e400c000c0c03200c2110054505041d11403032810015030320a21030900c10046c1e04009a5030300900035001c0d2101c5000d80144c40c1e56040b00c0ca00c500850112410307a03815441c150703000181c4070403e0885aa01e4060110002d5115042178107221540a001c41c3d00c51010a042d000c035041829068080342540034450780c413168182c0c040c8810804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 211773147 1250 211771897 211771933
    0x603061203091a04030506040f060f0605090c0d110f04061e1709160e060901050315040803070e060703021609180204050c04030203010518070e060108070f1806020f100e 74
    0x43d01104803c644c545680c0e5981c450501a0031036007541c12121280100c000d20501e40280421584001e108000090410002808904010b08024115580843c40035501c07280c545c04464109104154642c07030f110403c0301805503a0050203000300055000c032900248240316041c07079202c0b403207640b65140c0c0701d03254403001c1c1a0010024040345491080084140e01c100107418480c0c0544080000800070b8038008041c0301200c4810ba104d2802a4003201d04800c40f903444200c00b41c2c0240d400310700981e07291030349034007201c0030a28100b0740f41d8490b400140c20820140c000561a011001c4021100f20b040e075150010012144102c2c0315610242d20344041c080103251030390115501000f1417032003e0806450350080303401c4590484559040d003001c2c0144583c08441080a9001002c500c1140c9002d0303d400b000081020001030036074001c0c0003450120101641c02040c0103819250100d00405040d6a5001c0c000e43e148100c08a8040d14028407420b500010442d01030f2482102c000f0004100b203400c0c039205022 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 211774397 1250 211773147 211773179
    0x15060807170a0603020901050603010f0e101d180f06180703060207030c15020307020d05250302060a060f030203070b0306011809050a0e03161b0f090501060306120309 73
    0x200115040340070200c0351000a4103004440074180007520703c0c00c40c8107210074042d040e04107611403441840104038102c28500d60005031074059412150075201e1342498503c06001b50007011601304000040f60742480e20300961031140340c40c807209614800c0600250340d03c0e51020b4605d40000d4105c0c400180d18000101e0554602104c0213044a004503a241c45200880e041000708a00103144122500180306403901d868030600b10300601145182400c49019540b180441d5022040c0000407e4520461070041c0e80e84564212200106005d20f86610340291036440444500440610708000810184110303007500c0d05881d03024001300f052a04044035455107400040103241001550280092401c1813486140d000701301880300840d150810501220a450104142c02205e81c400e2004e0b4071288504180b000d04550481500001e50011464400e4a403410742c2000d0700081620900152410032540458129102d40c2d4013003002c0350b15001c030281206070301d405c0500010107025091041c8110410800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 211775647 1250 211774397 211774411
    0x108280c030b06130e030901090806070909050a090819030c0c03020c0d06151502100902060d09020105090d0f1b180b030c100f0206010b0f040620060f011701150608 72
    0x134040982c40d00000c060b84c00340030754085a0381020078984072558101940710040c00c503950207020585015000109a20f00341d20a40c20407a0b140c4001c41e41001541c1d011200d0207030403400b00d981d41d007d810b0100420702080707a02c42e0b00003481c210b003c609503440354400f4440c255240e8090300c69928200c00300312640c1280c26064440c240d40b07000c51211a091054054001d003094078002004041c42d0801078100b050b042d940811240c2070030f03004030041e92500b0131244024000c802c002640d04150004a83c0c1e0f018043c4d09035001444001c4140503c0012030a911203a48203140c404c4c0007030000003004026000610454500d041203a031407ea11151a411000e050342d006401c1b0342040022500181e000c4c0900d1030104045072a100d054001c550b13040c0000c6014100600c88246440d40e80031071406244212f21481c03007000001c45002c0401d03001ca150060700c0b1003500b0120f8800b81001c4541c40c40100086c8112400040350b00c100c1042880180200d94918080e02141d0f00e10a241c004150740c5040300800312 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 211776897 1250 211775647 211775659
    0x507060b03100c02070f0902030f0c0703020a06060b04170703020114073f02070f0b0904020d2406080c030a090f050a030203030a1508071401050d050108280c030b06 72
    0x2802c41d02d59032103045490b4070341d54000d010351860038039428071415480d0403c0609a0042082010b0104245107064004401359240791b80e404580c20120704111201c1c1c0700800c01420b00f01c00050300035182000d0b0058075000d01f1143c02c1526681c0241e81d6411480c4002408240984003010301100f520300074103140c1d801541d0145214150f42c1400b4035104491480d60800c0b025101400a14010650b0800d048500c1e40001c180060030700c4200c4030329403554031549881c0000062485180d803142d4047c1c0e480c009480d01d0510606041240940b03c241200004201250002100050705071042c00c035030340207102c031000107491a00c82030020070151100700f0003a01c41c07600068156001440c100802c0000078066400345441c0d081220380d080070340d003448403202441d1400d0740e010b00000c40013160385d10071510382117058103007019140c00581e41c3d8003600c10603503051454440002030b13440c004540c04011182c0c00314160101104215614100b130a94103025190b070745141020700014907900c40681c1c203c20300070300c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 211778147 1250 211776897 211776913
    0x50103050c1213030f0e09041b0506030c04090b09010e041209030b0403020615240d0b0a030308041101050705030a030b060d020a030e0c0907140706110d0207030e030606010507060b03 80
    0x4088201c0c1059a03c0b01000c50300c000d2034000e1581c48255500d040c050382c81e041001d6410000043e411801c090400380c00002c5d120304502c000e000500208004000c050241c9443e45000114964190064412002c03043c0c20444503503c0b9280080b9954180c400d075101c008150b884136254041580b07117001206043c807030000c2000c030101c1e4000c0901c52240c1d00c40d600034a02407814600d041d504d4540711080c1405110500d000d0b502044801d2402c40c84000390390340c06501c03041c030f81c1908005885111030703003500700d0005040402450341c4000c0d4035110703078001c0c19081c420010308801101d00b4422188040c00c9a0000d000c644031640c405d402c2032503c41001003601c0d05025560f52a1001c03603110409100c01719544014661202d5010f2200c076005072800c032000c1c101d0749425400904440346071000a1080940000c240c010405268051500240402030190f1221031140040000758010f000640100f403c007002c0148030f250000d5042e100c0c1c20180d4415042503c19560003014120301d00640f0f40c54002c1e285 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 211779397 1250 211778147 211778167
    0x111c09030e04060b190201060602120310030b011e0602060613020304020f42040e04050f0a03050a12060b1801031d01021b010b030604020d080c16060306080105090601050103050c 78
    0x43d183c0544114006199621000040c4403044051410b04a00356410101c0030017902d600811041c44000c00ca60040e640d80e03031010104160314420b40c00041141c0c00d0380c000401c251084c007051044500c42041010800790304d9060a980d1b41f18202c0340564484130340070411030214119005541c02a20240c00d9003c07884911380059107450107500d00c24412103004c414000843c15101d15820103940c001c0921a80d4030f210b100c01b0300203100f1401201c08003445180400e082000030080311a40103405ca091754012101e525004020358009143d10700060580e601d01c0340300c04001e11528003118202480140303000740d50720705a450082003869050501d81c1d0785944040c4150101d880150011188000581da405000c188100c15500e24510710f5183c0c0c5821544482500c0010304030740c01039012035000101d041c00c3e191014551040c0c0c80080624000c6000f201d106040c1c0409000598603d62400e1040e60345030802c0c0341c00c0303413822904603c0503800b400040000394029400b81341c000d0f0640702140d140c254005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 211780647 1250 211779397 211779401
    0xc050c0105160201060504090f06020c030c0312060109080d02062206110a02010c08090601062a0606140d0302030306191502060f13030807030b010e03010c0503060301111c09030e04 79
    0x340c99103848040c004140d1010b9a080c403c100141c10700300c03010800030986440340c0006410000000301000d070b0005403031480c92420000c1d210030108e0a41100c1d44d0b002d1343c5125240096040da01c031808900c0c40360010800030000700d91824841c3c082d600400e42940c1c5c06040c4491905001200d8128a02d8840c1c4400401c0f140d004001d4404c40625201780e980600010080c21501e2101c5100d080120510500009003004500641110b40350f01e811a42021401900d0b82000403100b00b014010703000c03001c82c10400540390800c2041b0340301030014501c01ba04650600105803da004010300503001000011014a41903a030201c0c81d42c4421800d10000c1e4132000c0500410144030b000740c000d6800030b002c11040700424061aa80318001722881c0c6e0f00054555006052220054808401e05848070011051a440f49501014501c0010000d10844000d5072026140307600c03e40d0024040d50030300b01728016070250740c81112030a054180c0c028410158134440030009083c102c000b2410000d2888030034115075624 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 211781897 1250 211780647 211780651
    0xe04050c240d090c0510020d08040602040e0a1a01022d030f0a09151704030509012f060609040f030f0311030a020901031b020d18050909150112050d030c050c0105 71
    0x1022000540c480c20381480804080c07241e005e180706110b03046007001c0c400c0d40828100d5107003503103060200c42a03c2da854524040d010f19044018001004003c0180009003070300109200e484034220041600c3c41103004a80310194408400115642c0000781442807600301c051f00071a040000c11b407800c2403a000c440310015403140129200041c071b0b17a042800f54619134241000d058140d4100740f01050b41c8104180c1140900420240900c00d0100f55180320364003500780c0018989141411310002c9201040703084035a2141001010303980b2544001645900300a007100b4003640d040000180252110f64085034603032190460301d010507460350701851070240101c0142d4041d4403102400751701c03401510001422030700d824032002d54550818401c803200c1900807552003140f65a0f450404009502d001c1080c0c007007500f6a00240c0c02100202c108410300728046110455031b2400040c2e1102a40e9400c1c1c1e0440c3c103443e00340041d019800c030401c00550107000760f0248650619908050b070602401c02c1c0d20900b11041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 211783147 1250 211781897 211781917
    0x30613020c061819020904171b01150e040b0103020913060207050a030807020a0c051003021c090c0503030a050406050304060b190602010e030f07150605031006050a0e04050c24 77
    0x41208880c0007610203000400c0301401010310b40c44c000c0c0e0307180c001a0140070050400b5200003080d00e140e94405500008a030008005114880001950303091007038020640c1c03019809000050100203d90200380d004000e0080d0b8010003020785590940c0c017000381000c8044c110410f80d46039210301d84002011800900180cad802440a8030a201082c02d014022940c010030180442d0019040c0b000000d000c082810140ca0041c4c42c02209400b96040540c001e215428032495141d1101c4c42c50320418900340c0100d00c1d1948510a85034045039244107160340e90060300d0680012036014002406000c0c03040b0301641d4018061b8001286030021130000c90a80f800184841c07448156600090100580901034804030308503d4004503e032050100d100400360041c0c0500803d9421481c642c2e4402c0040b81d0000005000001c0c03c0d650361690418a03c0001d051602c00e10740543c81d52040000c05801c480d07840d510868102015100005a0604021104400107032145a104c0b00100c540b40d00380140000c0e20444607 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 211784397 1250 211783147 211783171
    0x30f0304050415170c0405010b0306100e12010f1e09030804030e0a270b030d1b081b060403030c080c040308031312120e0109080906030c0c0a060603030e0114030613020c06 75
    0x5178400344001d0301c1050700400f100200810510a4035183c0030820301c012a400d250050411160400244031092075105050b001e6080010a0f0840440ba40c0012103107503014032886c1d454564a20540d0a8a96100c80500884d0710080000c0109001d08021070543c40c0040030303000303045e440b4600c4100b0710f01707105003030241d03180305000c50350001c07401e0701c035101d11694210020107800c080c407a070081c10003421513050030220403401c4e502410403001000355a40a030b203265520320807040300440740e0340c2c07a0822981076000038205860135206501a100c15402030601440e8185800d0440d15164420350010317285090960403846130801045c000c8182c01c443d0282695044840701200109609549004160884591500801d0300c0000c0c4645c00301e8407030b050b040c0e603e144c03281d880703841c1180207004046c640500d07409510800c0c1d007049100c1d407216040c0d9119480d5000c41800110044a00144003a40b414482c4800c1003c902940307800081c58101c1824404094a0001c3c41c90089040c070300140c0750710f90018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 211785647 1250 211784397 211784413
    0xc0118030327081906050a05060a0b0c0c03031902101109040506120a0507060e09010503030702090402061e0d0e0606031e07050d110420092403100f05030f030405041517 74
    0x5c100703406002e401100c038000a000500300b250000f0000151442030321800800001d404105140c00e0000c110840401006e885c2c03140360941801c2d06c243c11501595005000d08610602d00740418410808240109124242003032034031010b020050201602c0c0c564042d40c680b4000400303400400403082d0142c810030140210301d03d40900503007980c8807046068494201140140b02c00c0c0c0340081070f04c1e0110f030126508280303900c8500100e00144100c1c00b491145030b84075080c00c104109048000d2050b034030000420001c011127448005d0711a2010751716664107800548c2d00c8250100800498140042c1039800e4406031907513400080d13540304000c0c10450320035078180903820417803401e0700c10343c50f005070f800e421900c140018211200451040464942c4650406400020407007020565645400d5010052955a091072022001c0b00800c0d8031500d040b001c20300f0380100301c0341404281c06500e594044010b40c106400d1800f0400981541c101210256080c0d036000681e00550840d074000f06004071018210340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 211786897 1250 211785647 211785653
    0x62d011101060602060f0c040302090405031806121314030d05060a12020d0f0507180203180c0f04050a2021061c0501110c0c01180303270819 62
    0x324800c6190486a45400d104120b615004504680e00103044040ba100a6452080041507070007a038002a4100240303001300010000004000c25060f5621520354001200420801c41079200301a04400300807610710105401c51816040070354100d2280c1da241c4009104007100d2450354000a1902c1a00c580f00c6062020b54142590b0060180503481c10000c008811500404d00101030404000c100315484694907003801024081c4002031b013080c00c40c21002c00c00705070429020350030a5070120502500c0031a100302c41c01c4001011080c4d040c0107000100c0000540c0c0c10000108401800001340b00d4a070500ca5480000004400c08047d10750b000080d1a083c12590200f0000c40c8042c81d46030f1a11b0503c1444a2075641459249000d41e00540b0f4201407003862070614058405800d0083c201000410090a41d21002c02c0c00c0041c000f00780e0314911040e9818031030102c030425521010340451143c40f110b42ca1000708a500b2101c440d181e2843c1e45406581d08801c0c0e282404101c8103070712031420042c0110070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 211788147 1250 211786897 211786907
    0x40525030201140703050406050c16180e07031112100e0601060206010801020306090613181112010915050402030a0f05010603170a0f0302130302150309011b0f08062d01 74
    0x8000c0101102d031300303040e2513070b801a08900c680d0160209012010681c002602001c12140c0303165542e00d03103030079092039492099280400e01d400a10070041d04042100a010030000b515104494000c005042070f1803604040c0044150120100000d40c0100b856041d007500080c002d041c400351885e070041c03955615200e002428854181c0001c40581d004009202e0281d850b810101c3d040042101d100b07404581e2619903000405010180d8a00c5030054481d103410301c4110b208600549005a41107482c0d485036801c0642200d008940003440440d03006154181700c0015406994820300c0038040320700c0c048050b2140c003d8141c0e400811286030303440745c0c801c2c02046104005010b003500841e92050400701481006403891180c0380000c81015400315450dd030521035030047e00d008640140924050b084180f04503c0107508c11120074003951b0030318940a105c141c00070110024858079035a1844030104a12044501c01000703401a6841f801c400160f52081d07404e40303840d24040030a60071015071400f0340400500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 211789397 1250 211788147 211788167
    0x90c03140d050c0c01050901171006090605070203071202040e0f16050406150c031b140114100b030702120c100507050f0f0c0a2f040b0a050603040525030201 69
    0x41044000d2140d610f4140002842c158014001d0806584032150080100c441109280000c01c899401406003c0342081100711030061320711a544801c40e0381d80fa9203040c0d9040c0300e180002500355114000800001d03141c003004400e210720003030000c10b541001089aa02e000c20190724642c05412224501050807182c02500c0c00800058406020300340c5030202d900c881040a8a40b1418000082201e1040510a808035000312a40c0d05419140201c681807032002c03410020306d4445158038082c400540310704500c020510a540001c176684441c0d052a800200541000d8800c1041d4895103107009a89000302c0007a06040710454002d00c0c00b4901071140f041510009020302003442002c0202d4902c1c80645421241c0040b6440741e15540c4d440b001c0002441c160813241f010f48072841c1030400100a59400d501000c1d103001400b11349801d49995410071045806c64607515912000000c402c001d1810144050359001c0d004409440300c0d258a4030b6400703903160724401018404a03944109108568000c4da20078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 211790647 1250 211789397 211789423
    0x70f09050301060e0423010e03040617010e0106140705030301030b04050607080402060a1d0603091534020109020a0b0a170f01052404060513090b0f0112090c0314 71
    0x80403442c500403003148504c1d0094006414145a1507540f0110030403d0784480348420444020040403080600c0305489400c54060740001584000c401300c4184240398020b8181c1d01401003c0915903c3c00744103a40c1d07015490a4007100d590700303010f5500403030414130240d0300860103800c0c050103d2601d840c059003130040c01844001440383c1c00c014003000d41c803020159001c1c6915400d115840004440d4140b009200c80e00c442a4401400800c00080c91000319400700038030210382c040c607c144c850660303a008450140c00c510250000000d921200038503071481645000145000018034080f0030740106100f40415000041205000101a081c0c0e40d48020360300120800405900701c5402c28031103d2045980610441d4420340e031100f2041605a200c03d80c08100b82c03d07030042261346a80c1c030b0340c01030203a402020308aa0b8189060200080c004154013483d030310920028580429051020015245100040c1070600c105566620160014507520303004005140510400c281858242d403100e454650141c07194 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 211791897 1250 211790647 211790651
    0x30e150402010e0a0f12051932010207030e100f0c0b06041e0506030634030f06030605060f0114070f0302100c08060906040c02030a0c0804030b070f09050301 69
    0x2140551104018540c00c50740c2442e010b290408498001920002c8a41007059502070702280012041520110151114480c50a8840e84d803a4000404540c54000c0c10190100034464502111503800f4084440000303401d00d041c0c1592180358003c81e0880e001142c04070080340011f0004a0640b83ca812580c000710307884d141800d42d00074445070040508000703150060900200c0000301d801c0c0c2e51036030803e6041e900c030800312050300102400e00002415007654202d00a02034107002c96200c9580b02d0078410822a810300700072841d59a0100d2a20300c5000e00351032010107a5420401a00300c0c201d000e90401180110360108280c24007400304503043c844403440380d0600060400c80724810b02c045040d2040c5607042661030109940e1400c0917400d00e40d030b07808140da80c10300e40074502413001c1e0401600c0303000e8881540c641071160b54400c140b104640d10b001840e00945e00070700c01c421a2500c07078481d1010403442400441e0400341e49503107444a0306d2064602a011500808440d400a035105069400030a000c40007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 211793147 1250 211791897 211791913
    0x3052d04061b0605250f211e061e050a1806030602120a180203031801050706020c010506010809031303061d1f0b04020339040603050601030e 62
    0x15404903108900c905001d00044211a03100e1000c01000c411000c3d0b0060010302c103a21381125a0681180079001c52041a6895110040e98911807420202030040507111071460088040c20301e610482d949504031b0009442e06a00d445003401d85080080c14500c406001c22001d040c43c0003084c100004503001d0b04540c0ea11041002140d8513440c141048070004a0010034407a440909100908490380014101c1d071b000161a101d0b10b04441c203058032801005408028804031000155100202e50901030b500d1b9205001e6124010000b03461481c4081050400b60300d003804540c0d402d42607802000005c035103a5900c90030002556004500789502075640005146015403031241034075080018040a0b0900744e450b02142c0038661068105d54403d4a6602120902050800c40c0802c81d03404031122007085091841b001c0c1113051a000b50b901807581081d100100780174a02c0741c40c03800d030990070401c015407640300c20f4140d0902c0380d0070082020307181944d0082a5440c11300000740035120254044011540101d103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 211794397 1250 211793147 211793227
    0x3070b0904270303091b0b040504050106020c150a0201021e03100515190e1206010f0906030c14010e0d110316082d1b09090102031b0901050409090305 66
    0x1280500b0580d06080c000791400507414038600401e507048031451080a926000300d428003002d00500200e60040300c0600690fa00c03840101e07110552080b141380c01078030300d4030300050300301024004d003000c0d82d00380c4001804e00f02c0d80969030f6103d00d17541c1c15030b0190081c00014021280c4021501c40e01821040e511480403044441105440303100c2c000045014800514035854078910600800800070b40c000c100ea800c061400c88040d489100a20841401d4904a540050f4202141c0640310407640c014010800c00b902c2d0094842d0301c1004405c0303443c10403600003100b003120340c0d4400003504458014490b942c880d0001005141c500240d0729110141043d00f16802c0065480010b201c040d00d043e11001c1c4640548103e25101181459900c50380341405000f140201e150b4181d1508a4691000c4483e51142c0e150840600e080f88801c0c0c0d02c01d052a440481082a1440c4400003018014010300d0401d1509945070303071a50444044040c1180000d400103501001214400002070000840e004116500280f1503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 211795647 1250 211794397 211794461
    0xd0518010f081501140c0105190c02030d09080706060b0a02100b0a14120f010b15180d0f02060304080418051017011d0109020a0902030106020a0303110903070b0904 72
    0x41001100c40e00221107142c2603403159400c1707012074004c1002141c0304d040c0d080d078140c0a00f508441d01c141c0c0b00142c0c0c0c0c203568408094040c040e240030068010398680302c81d0400c054094140c0d036005890090080240354005200da224100003010340d0229103403500c1d41000000e05013501000303604200d50410081c4a40d5940f003104540840d6503800345a1072480e800d5000c580c043c000c01403840701500440000300c2c00a50190480c03680410201d41d082e000c0591445080742d680a80c5802e002e1880fa0068080d0513814041f0484282c14015010310004841c1030b800181641d03c01c64085442040114003009200740e2a0b100c056400c518880500c10303441c210003406000358980c03091032500003580c41e0051540300c00394000081d207030000c0880720320700f6101c80c0c2300c1e4081e114948080b40641d584403800070b550580d138801e40b41030700c000f54090b14807a12a0781381140a407601d481030038030766041003160318036030b6904000e101c006000301071426840f10804010001110f852100c0c1c107400511201815800c8100c41c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 211796897 1250 211795647 211795651
    0x90111010c1b060b0d05030301051801030503040e0c0c0712031704200402070203011a180f0118020408100501030b0a06050a032904050304050405150d0f02010e030d0518010f08 77
    0x40c0c901d02ca0b141004005071480e610480e0f00918001070782d4040c860040011416034100307660352121012100305150044800f44070180c8140c109000074090300180d2805150003840342e08507103040c51807e9048a017450300d1580300e10502d001c55003444040682100c000001c80782c02e0a880307029842c1540798045805089100c40350000c100c200c030300809541310750590320143d402130700030040c10008425606205210250040c401e6041403520102d26031030500c001d00c24005080b40384020b1340b81c0390b48425400b022105410001c0d4007031101090a140411000e40d24540240c8003154075495800c180800c0c12000e850b8400d090704180040c4141d45801e6088021260301080404100d40244080c0a1101d1506e800040d40300f145401e00c002d10030000040d10a48004607820030076a19165040d01242180d20616038005c1c401006010100d220103200511603801814501c85c102070040000e424005001c2d440720208a0100341041403c0300c034000c803c0311010a01300340c1c0c0c45521160f0003820340880 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 211798147 1250 211796897 211796927
    0x50411010e0a1701020c010e010c050a03111611012a0809060706020a08150901030c0314100c0c170a09260d050c0d230a030b0603010b090111010c 64
    0x4950003100d0756102d4115120040c801101c910070f0a0210242c014040e60042c00c20001c150b0038101c0801441d0010300c034068080300141c942d5450550001020b0f000f9110002810310b0200b0140464460050310101a2003814410b040c102d003410469070006d044c0120f81c084183d0360720104210080c1c40544000706020070f58000300d8041d12041e075480007880b144a010401030140380003080c1f41c0c24442d04880050700501c5410942013040f05141d0500c411000c0c2407001500001854000308089104409140801704980003500c4c1c0341c50150070a5010748801040076000200e070354000e00140400000f420422000e00c88110740b4020310000e004040d04024042c49543d030010a1030084410240c1c40100c0410400702d00340c0e003802e6a081c002501c0b0b60045160200f040c00b50000207640d861207050900111041802040c00280000e100900d1680145401905250751122069416503641e00514000e01032003100c140e0f01d11948000400740c010303860810096030705001c00b68080c2c5800c01c943c4004819 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 211799397 1250 211798147 211798157
    0x503010e091f020f04121109010b0f0d02030c0c071509091a010302130315050117061003061509060f05010f18060c0f060504061a0307050f0402030403140a050711010305041101 77
    0x44e401c443d04600340b00e82d038004010070402c11413040801503d0244d64103000c0d030460300e1180980c0d862010079042e00c0f075000d8400046608128162414615502854200030806201820300c8801806103280c07468940241c592041441459a4682d601490a502510710000144007500b1008400102c0c54082c9410505140e0085500d40c1c0341c4000c0210303a0021b5030000307800541c034580c101e04080280710070301940540b06000f40080e0184000094094006d60300c840080504a1840c3c880d017005003c01212001c894182d468000307500c00550166001500b82c800340400e04038588400501112108201c65080c040c0c1030b11020381a08644109008072152401c0411101e0110300c0c005070310448a001c0108103925160030312040c0001c0f5409003410450040d800111410b0080c20181c0d1100700384075003680101c0c4032100c0c2c3d1035402d1030703005150014403d0405003841da8120584c80195000804114001080483e4902c2031050034002180741c44d1007070a00f0003c40c00d080e201c0981e00784002154a040c49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 211800647 1250 211799397 211799407
    0x90c02070e0912071103010605060f030a050601030e030f0d0b010903020a060c050703061404050d0201060b070f0503090a0b071110050306041e020d14090c0d20100503010e091f02 78
    0xd1081c0f104001101010840e65900c14244c031380b04003c2404030314a14000d41c0380c518041341702d00f005070445540358942c040c03003801d680c2c5844c1000c002d420000e09c0d85040546940c19040201003c2010300317504602441e00c2c076200d1040c80c0d42c40c0300705c5907030041c801c0c104401c8032010005619030740500000c4d41c9152829890f1200780c3d06145140a8040c0d10040c18180b41c520704119101c074481d81c00740140d20a02c240c60599540b05002c1742a43d165015044107400d04114403000030740b01c131002c0014244108107481c20031204800040e1200710542c000c9404103030000d0000c00b0841202d6000000e08812900f06c24401c02402c40104140002404240901c0e130314541c501c0c41c064400e044400c0380701400e500359030f102c10b024803450141944ca0386001182400c1c0e40801d0a010700401d11204107400601144800c01840e00c41ca12822083c201860071254181150702c0e46465908022069994a4840d00d60b203525091201140b080d0040c071030203854000c090629844201030152104005c458100980c8030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 211801897 1250 211800647 211800661
    0xb2a16031211190302160c03051603112803030201022206200a0605010323010605130c050409051014010f0c0206091203070b0103060c0f0507020105032206060e01090c02070e 76
    0x2d2060701c9070049400c6d0b02d004014104510612941d0540348600e0941e00d00341c004a0301c0c0d00314050b040c04000c2c0701e181c840303000d84201d042c04194019443c7d8520741030201c9420340d02000f0040c0009400030380c010717500058012400c074036001c03440c40c100ca40b0800107100c0600c2c1400040400118100c0d50340030001d5409200420785003042148401a040841006113581d08d1510351213101c40d40e401ca440a500d2000c0b5509540c40c10700c81c84046400c094501c41d840e05803405458010100310b9a52070510030240404504c0412038031401c0d1154914401e145a01810091506900003070650720034100104403200480740d5900044d018110392f03050f155a80c43d0340c01d480005d02c1880d00da1601104511010440380103025000030340354100c1c1d0245404000210000c01c0454000032041114000304400b00500c1005521841c01142c0c0121003890107d0120120096103120300e800f072005403081500d5000038030a01d1100420365005001051080020500041c0080d44450b124400c003a20381049400240c45 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 211803147 1250 211801897 211801901
    0xe0a060618060e0f060d0513060506011d10020106030507060507030e062502041b0e0f0301090b0f07020312040f060606020d21022101091103040b2a160312111903 71
    0x41441b80880130300051403c910250907809880d00259800d90038600414600d5010708446000ca041000400ca02d0320180c800780490521508142c40840d0350715030340040032420911241010700bc15076207507980c0c2d12142c140241541c0c005035101307101e610304200101901c8011407150a4020380c500b440008415280005401000c00304e0010401b41c1d800d109050150340e00001c0001007043c100d482200c2880b203041810b080360380b81c1e0070080c4940c000744049140c850b5001c6446900a500307104880c03500d5050107080e4051041541c08942d65140c8801e11707402c2185902030640940081e10042940501e40100100340b605a00c0001000030341c0c8680341115001c16030102c43c140b011070b8103d07020304100c049207244018000d01c10340640c18580a607408156000c1000c690003542c00140c0141c60746c452410828440c02c40c1d550f240c0030b103c00419059100ba00000c042d007144484624488511506802c01804040340c0c43c03042041203180c00101c0142250100940310900a208004032009080c401c0a42c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 211804397 1250 211803147 211803157
    0xe040606050a060306050918071806033002161401090801020f030603070902181e28080f030f03041a01090507031d06010302040b0303040e0a060618060e0f06 69
    0x80c1000d402c0d02c0208040c0d4064104d44100d900c10746050a0075911081c428090084600d04120741d50442001008a02291650b01690081124000800360756a80c0c55084940701160348400450380345104040c0d980c4c240d181e020441920b40080c1200c420015981c6005035414050300240488003030b00310519074800d05804000d80391050085540345003c004004894108864080c401d01c00c0d0b11001c250450319009603882c07810b500b2486009292450304110755501c0a041a481d0359210010500544e5524644058280c4410010401c40201c0c18641a0b60103001c6e0004000342e0f00100e0340c05001000002201ca1004040c0c000341d13181d480d01e1030041032aa02d082768840884000320000b1802030820380c407036801821a03841c104403184c00600c0610711502c40341c0c1c0c10607241d0009001007004d030603e5000b00841c44001800c0c2d070301c2c280e21800d2000d40c1c810140c4902c1860741da07455003806400e40285040340194a4104103845881c54124003c0190340845200b030701461010085e9012600c3d0201918 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 211805647 1250 211804397 211804399
    0x507050913061d071e0303120f1e05160504120305040503070303050408061608040605060a150507020f121b0a15020a05100612142401150311040e04060605 68
    0x8032407104080140243c0c10707820422800c0c1e03401030050018404001039003520300c444013070180c5420035281da201618051060040890000d840781d034900002c82c528402c6030448002c9144c2034419081c0102e507182100e0000349401981603c0d017218000098200741606c08484500003182c2e04041075280442c3e0a00442e40b1080e0140301300b90003c01010381007005001a40c00d50411a5841d644140307880c1801d8040500b510045050400480c000c5629500415800701c00580748075900365449401c10141ea94420f10180051800b00d0340704114a05090404101c0000301c40c200c0c19000009580364882c2c80300c00c4043c18941d00c000070384445c0d440c0c0c01c40d400003c01c00084001ea00c00c0c0c5520003e5207410003420b0407036842c0140602ca920b0305019210b001c0035141901c4011403500704070755603400406002c0752000058801d03402302d800d0341100e5070607050038a5100c17100c81c035042d4942241101802038000044c0181420300b401c03500d00e1003588060750101c40d51503c0d862040c3c0c0741da0500e03500070021078001c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 211806897 1250 211805647 211805651
    0x405030d0801080d08010e1906150e040b030a08030708130b0406090605070f05040b0c031303060912080408070201081509010b190c050d030504032706140304050705091306 75
    0x540c9400e03002007500d4101c501520960b014221041000c84030060240181c03c980000300e07002ca2510740380880e1120420710502e000003130094031640403090130020307005102e0004032846820f04140c00c10707000d28010401c4c00d070010700b4003501075034a8881c540002002c070001c2002c1e00b00002d00d002c001680d405202d035000800c848290526042038030203415040d0081e54054109004582040c0c8240700c8100c101c1c000d1380d01c541c201800e05980d26010f50161002c580da0303100c280b1034521300c06041744031200154894000055001ca4a2a103044c415019910308010b01c0421400c01010a4003141210441d07582441c02c80200c3e69020114410720400c03040a07a000401e5070004241540d45c080140302c4e484002d400703141e00e2008500c049680312100e0100030000d41284203030b605c225029820140e000351281c00c00324084c01e801c492142008401140d20011242d4200c02002125040f101c1088111040308021381355140a0300c4082d90f80c011441610302440c02400020360302e4240c0184c0ca4040740e407194007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 211808147 1250 211806897 211806913
    0x15092021010e0a0501120308041b09020d0f0608030a1d011e08150d02030a0803100b0f19090b09010c150e0606090a0603031434061a1311040503 63
    0x42c9400301441101d4a030307a400c1c500b1002203802905501541c0708035034903a40344501c95446aa5545104500304640c0d882242002d5000c90300d00c6190001c1c5c0b04001010303d00145241000ca0950160350349544250415041008101c0c0b01070780c0480200c040008000c814910856141c00491712844106010800306046030b059402242d40401c0c00c034000c1101c00c18104e4a00c1505040104248800c18001e605602c1410110001040b6001842d40040f40340c41d007032401c03035442403911408d9008095000c1098000100c1655850200216403202211031a008400c1d0741081002d05e081d200f44884241402003200b49101004955000c040300d61600440602c125401440030036911201515924424100440040c105542501c2518100c0750103076650302200d1030040c0c120100380e02090224031902c99050031400d0255807204809081d14401d04401d0074024281170600440350110410402c1c1c03c04c0d502e11034050390310750b034030001d007483d15031000605210400700034480e0b840341b41e01aa0300b40c024a22 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 211809397 1250 211808147 211808159
    0x81809040f02031b0d02011d030607020609010501150c0204020310030c090902040b040e030702011d0d03052203020609040f090b0403020c01110a03141b010f1509202101 74
    0x80580d00e54030a90890f180c200da10180b00e6101e08001141580004010354600c000d581300d2a080d62511500d50f442182e04d0230b1600100c0d00b4402e0495465000d07a00c890f0078000c03102800d02c6542e00520340c030066109d030300529200c010203544c0d004501a101c0d58021012641244000046c04001c0d0740c007042d41020360359241c48941c09400342e11810381c800c500c0c1c206640390500700f5014640e5112822409185080c08a03801501d2480d602c0c0c0d03203c5060110303141c004115031600502c40039881d000b07849051300c41114900c080c141044415114051024031241000140c852400783c422181c0c007160040380603411981c2110080083c0c000240002a40905000c2810340100f001c02c0040400e0744c444031000d84244505a5a01c850800100064103074407190748400700080c050205481c0040d6a406400441c07200030707094460001d01148440da46180c48915407404454002c020301c0094818848128518250310401175102c48110303c80c1d0001a0303410908a1075004a04840c00d0100c10184ca545c6540c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 211810647 1250 211809397 211809413
    0x203030a121d0c01110106030f0f0f060507080f06100804120c02131a0a12020d03030b09090c090615030f040503091305040312020c0303180316030804050106060306080a08180904 78
    0x210b0400c1c003007030017403030110388103c01030145405a0390460410781080c01c0583e04c8002c240d48800003030320f07000010004a00010910f0040303900a4140d6039072180141011640e4000390140903007100d10580742000511b50741a0084806075115130042100034a404d01000180c901303010294009501c842201040480d2600d1a4070406040c5050110009500ea0782e00601603400d400340a42e05401780c090420f0001441c05014103484584246400f00320301c103103c00031550b400b0040d04d140c03909410420654102d400d01012140e40403000f102c04440f01c10901c0f20f842068480580b402101c0d1360014002824442e0410858000c0b090251450031400b245060003001045c0079281140007946c0e20400030700340030700350099840b8280301c030014500c0c1d0f84070f02d030001c1000c48062100c900c45000901001103010100941205954002d1312901c24610301480e003a0b00710364507908200c080c0b40c50400c007801550310028161710390591042c4940d070f4402ca01e00811050400d00c02c6520303803140700001004104000f02c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 211811897 1250 211810647 211810663
    0x929031c03021206040908070f11040e0606090f06010c03140705030415081608150d020a09020c0f010204210609060f0902011815050d0207080a08041407030203030a121d 74
    0x40862031104c3e2191001c0200703880c88910003900041050050030f0120b503020f030820350201d1194a29010f01d02c0e412020800b5520703041c8802c14160006000c012850404000c55680b1040600b40d441c1d071840c14800281a200118002404014801201035040c0c0b000c001207030641d40d0024100c98440762f45203a8030802020352003410000231004808101c3e03420a82034858200c1035241c07125a11079982d011002c0c082803600d21169840000b102640000da251810350b100500002032003d40c0c2c80e83c402c07a1545c81d010508840705035036881040200125113010303400404050400c03a02d5450440282084400380540350000740201d4038054840c0c1d50032585502010000380301780c84000f001c41d158107203442045a05e00c82ca21907041c000001c1e10311144294000c01141040c0d480c01410040e071615210384c035400c44055040890015414030080c04001c05940290b400c0000040c83c0540c01c2d40d0200384c9034002c0c03641810501401d401032071882c10320307600418a180050350024101412444606944e4414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 211813147 1250 211811897 211811917
    0xa0902031812040b07080901120c0504080d0e09060913050d18050415091d030715110403030207050607030e030a0b0115020304140d110604061106010929031c0302 71
    0x1072070ba0695060107028054070104c541100101d41805c0c540d455144085d4444000d403030420406084115509c0c01511a04002145540d02c03aa01d03241002001c0d440e220306008400144022007894131625540e0f03010169018400750342e551000c0e1103c00460110620204000b0450f02030b4247d121080c5074403584541c003601c414036103a000140d81e0b405000891720160f010084000d5407480510038245d540d0030200c5611801d80d50031140104440003141542c00000c81203941900c48200a510500c080c000d442504130701c80f016602d03061841d5406035507600c00748107807802150003141c1d040034903000c3d401001c001c10024054940720079980c64001c0d03a01009010304804d07041c005074000a003500c00010ba8080c1c40516000922401d000c9081045860903908200d4117103000b0101200340307450340800751000b0300741b54840c1701c0d100003504900c9051080581101e05e02e6481e0071103000c851013824142d540b2060115140000005100000c2410040d40c41c500d02029410590210b1040758941e0013030005d140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 211814397 1250 211813147 211813153
    0x2070b0c09040b0d03020a02012a0b0a050c1603030f09021f030f0506031b03120a080106020d03020315120a05031803100606021509011509090b151e0a09020318 70
    0x110f020200804540c0c1100d000d4010307030280c0541c1d40107502601d03880e0150f0105044100c1c600c100c1102020202e9408042110900d04c5042031080720036031402000c0e040255100480d080c000400504540b1104160b03018003010349500300d03451130800301d5000c0000350382c000e03144040351180c9900240d0440f54040a080c00249090059144081188a80d0f4082c4a00602400308800c861030048200c10701104215418040c0280c140422200c8000814000703103d511180b400d036151640190505400c040d0180c05e00d8010010001070603d0102c01d48014a01110051b08240003003031020b01e40f00c07072072100400600c0000740c082d904221180102284074070803401c940c3c0341c1294403042c0c0d060b80c849100d15409a4040d00c0342c1200000211180da41c800c2181000180f00d08804540396a00d04160f403058403000c1d500c501d0f02c01813145407092907070302c03500c500c03880503005503040e02080c0d00e410107201c00002c2c403038001c0d417982441e80c1e540e021600409140c0400d54990420a00001100c40f0403408024184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 211815647 1250 211814397 211814411
    0xa0c02010f17010504110d060305060412021209060a2c21030d0b0607051b1f0c110d050105041103160e220f03020d020106090207081c02070b0c0904 65
    0x161041d0000c2c00540e0440c1021070250b4603160900000c1e00a0901c181801c407001c0c0811043e80d0268402d08004502800c020652030410f41801401c0108082d0488119007200c80200d001cad810b60012aa1089400d07940071f6968400c6a100316031702058800b40000a4808030680c0800312150205040c8140048400c01403c0200f03210040c0b0300d082d50300b82030380c66030828001d500024425522524007d4809450a0710b0840143c1d600360401d0100010a0340301c00346420000c429090124190000c04100c7c0c000502c041207003071000c0c024081c04040209103060040e2a0003054540740055184180c0c408020300a07410580381c2034007a00d441c4620b941c000d20480c1556251101c0e201e403080f0448041400080082d12445000c0004a003000041c1c40340c041c8030509180010791820700019603500036400351200d8007188500070709440703a03980180a240c0c014496280815030610455aa0b8420030201f92103501e0141c500c10302070301403142c001c4d003440c49074810081d44140c1300006181d50f080c1250104989 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 211816897 1250 211815647 211815677
    0x906030c08150117040c09050601030e1e1e100b090f0a0504061506031e1a1e030a0c060f050301030f06050414101406061615020d020a0c0201 62
    0x2104021035020000300c40001107104804820703072001c0804018036007816001c000c40000008440e094a084590143d00942005401102d2182640080c1e09103000d0260400d00703d026607441d00300e82984900d02810030281300d0100c1080041c0034150a04200d511203540020001c0d0b900e590900580352442d90400c2410540c07440c200c44018450002903113429001c3c1c032403403110002000c0081c0120f510381d40d070b8520244104a115140300081085940101e8104c1c840030000003881da00b68200c0100070b040120b03155912040e41c0e12030000c001d05490652034140b0b0f00428000c3c0c15405460705425000b000c08910038801d000d508182039400b00d4860b40918828078004a0711488240320180c4804445140e032000515550850f03500123016502c544410701c044d9103143d081c10075849501209517070303c010b40021a4070011002d544468115011343c286260401e41d03852808070f1200c02401400454071032503000910b503060f24203c110300001151501c44240019000e9410503205034082481c0703503110141 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 211818147 1250 211816897 211816901
    0x7060e03160b120702030f1306030b0f01050306010c02010525120807020c0609040f0609020d0608010b060d05071b0302010614040b0a03060c0210020c030a0906082509050d030f090603 80
    0x3180c01c80d001c002d243c0b0024080807900f6000c058000401c40c0020013440c900c04000c0005001c001d174104203000070052610001a0454608490781130190111103501c440c10f0ba00101502e40c403540c203007422004980c035803004031401e04c240a5102a082e00d0200702e402c020040c126100403943c400e070042e00c40281c2648003503c28ac0d03030884506005038070415035081300c0d09061000d01003001c4e004d00040f4040c0340e03000d44402138414542140313421544c089000c40c0d1240310f40c000c0800501784940204144039124000c11070341d04c6103950014000380c83d0404640c1185c414402c0950720303101002945105d02c81443e000340a4410f5100303441b40850704a9042e2080c1c6840e11412004190041580c4407061665803a000a854086240300640c00754184070015520140014100d0503414030265550318885100901160100e82040c801c2042c0182046450b00c802040b1080c800e07520801040480090341044840101c02e40205400c00d02c04217000d000c154004040369910800358449602054548004a003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 211819397 1250 211818147 211818149
    0x60206090715050d1d0610090e15091504060b012607030905010b040c1707050a050f0c011803050d0e0f0304060e040e030c16050418121107060e0316 65
    0x4000c41c4001c2030360210b0f4090002400e5003000e1450125040411081c1594a8500c00020f441d0580288080040d416580300000c006418110010061904550141c0c0d80d1465014a204844404400030945102040050500750302030380c10451080c1c0703420300d032402c007800c1d09a4426001c50443c0010010361514403c43c007002c80400ca28074126a6141e1504401910b21024283c80a5580c0c00080c0c039a0744640c000d180c0c0051568542d0041d961004400007104a80280040c080000c14070200200c03d911204a825000b0300700300171604c45030306a043c2801085020004c0700b03400d42040c2c0303c1c01099000006005038a1051108210085e014a0000d0703d034041829a00400d030010030050124500510350790000385005840000d004107000c01c1203103107038059154071000e5489040803428080640b028070002d0f107015142400b035a0301948040e1101242080c2c000c1411042049040300e440c0325607403156200044208903103115135154006840640c0c108845402802103c03c0d280c034041d41c14401c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 211820647 1250 211819397 211819409
    0x2160c1410030906240302091e16030e0a03120b040b01120207050705031005010e130213022104230a12030c09150504050a05012c011b0c0602060907 65
    0xc0d01100305400200d004145800e4100c544681d10300b00d070480d040320030141070811400740300b1445c00b850450040142c0c407c4024000c41d18051280d01d031203000150090300c1d075000401019428054242400182d0252600d421000c04a21440c02c0010034554050f00d000d0707080c40481820000000c00c0c506001c01d17105026001d60224001c8984d14051107000e6004000390360080069682c46520350001900340a560383c079910420391140c0c0140300b940071a02425401508107554031140341d400307034045000b119250f81da6401c1c680d40400d0000040e01e84102c20300c00c01d00351409001e201d242c28503090f01014449a101f04401d144c2c00788040100c4000100c0403209500588041c1d00c4ca048568110040e006415070320040010031100000e405d07200350f1030f00c00c80501d1a00c4140d01c1e24202810301c4406100c3c0c0d4085410014150803041d403400c1401c44203245180340840b1040009041001610201c030b07603285030f100f4030601616082c1403040c2009c134102a9003065099070340c0d60700c400a8896030380b0000d00500e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 211821897 1250 211820647 211820659
    0x90b01081f03080c0d020706300f0905150a0b060d0b010c0b0f01030201080610050a1202040807080106030b011403030421060507020c0a0f080316020f0402160c14 71
    0x715000c00190300c000110081d511850610564803030740d0300c4500d80c02121070741100358416a05080c2c11601448448060b0610746800049002d03080b0051000241008890701c12008421b40754042c10b04541083c0d0b001c200c94a000e12070b1880902d42656554000b807010b000c1802d81001194428140d40541d59840720010042c80c20868580c94a50080290f10b506505210741c40b51854001060071513854413641c1a070102c507506602d14000074001c0711008003560310509580daa1b09012070b402900f0b44e5990005494103908010b5501c510400078420340d080711843e44070300880041c41080c1500706609491207613400030080d9a889403a1070103107501203d103640c150000c0c030003030100c40962200251029402c02d0300024204aa454150803190242d40840058102c40b11040c3c49080c1000894024502c52036464011344c5410507080d1a402225000b4009044001c218019903403861041c0022440013403046640d002000340440c03c00c5c2c0d0b013a40455015410202c0082c030b1450748885600b24200290517 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 211823147 1250 211821897 211821901
    0x1118010315050a0608090c010206130f050a02060d02040311060c030702060d0f0f0623060306121c0e1f0903080d0e0604060506011b05070e060307081b0406090b0108 72
    0x54015000490291207004100c22000030140d0f02c4180b030030300410550301c4880c000c6c101074949600b8000c4905500c0e0565012900748540ea04020304142c86d5180c006042e0b91004074180380840c201403090b0806940703c4008a900c900e030300721030350092003220300c80c000c1307c1c1040440500740100c6025400111020390010700024025041c41001440d0201c40c02d403002500b2510301c0320a50480b00c04215021328165603e10500010451b01d028950510341043d6030000b9400c010001fa10b20303c00202414090749012122406808042000044000c1c1001450070b10f030781070040042400e090381c4481c03482911b250102d05454a11981c1e41220303007007035070b5030031100c00c1c119140c11000e035001078440480c10342d81d044c85d15180b400920100303000324800c050100d40d0b403c00c540010310851940341c1d412100655008400f0002d100014141c04481e1020702c203540540d0b1710000203080111585c044800d901540003803940600c082203106d0317020b4800b103800300040e544542540301143e40c07103031300035000c2840c00c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 211824397 1250 211823147 211823149
    0x303010306020c030c070605090f010503060d06020d0b0d0f06050609070c060c050d1b08010f080318060f0403030c0b010e040308070c1403040602030d05150a031203060314060702011118 81
    0x420744503607420100c0e45803212615005c0e15140704c6900800000d03c000c00d0b0120907151a5000c80c02d141004d03c0d0080c00c5007482400240b508000002c002e081da54001420015550311360403010704258010b002421b5800030f401c0000c21502c581c00d0403110300e407425000415928000c07101c20700411140e96503150100d015605d5030f00030031a00700401d0901ca0240600b611082603405611a40048403c10305002403280d000500b81c61010f0308288603402001a0510800000200741c7d01039281c030a00c06041d000c06030001c19424410b446482c01b440d400041e0200505411000c0c1c040c6040c410058540705aa81e62505010300c58140e80040c0060052004240c006201e0714000e001d2034090022510702e410302c42445c5255601c50350080015800218440203414901d01c58240d02528101081180b0103a03400010550f403030300d000c003d00c00b120200300c00040718403a5102c00044c55101d034000c52041c6214003084d542c1c40003160a0700045d03080c1070502d481078084505480410800304141669140500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 211825647 1250 211824397 211824401
    0x120a060605040e07080a1413050601360204170a0317040b06042301060f030e0304050904020d030e0303181e0307060c05101803020715170613290108090303010306 71
    0x15001c00406d80d150540c1d074014220440449025414100075010341c845070380340081c1402c505034004400e034044030440c0380d1505101440100505c80b078a1700046000c81000d2030100a0086410201281c07c000d00041e500d40000a25100e1240c000c0c0c49081c08010101c0c02c06124a0040340d00070640006030000c2000c1e810a608500c01044401d81007803001e608030359182c20703040f00c264010000100710752a562256501440383e014031441e0000598602410000414200340018100a000c0c2c1c45c0070301c04800303251040341414100c81d0001c0076030740c1e030f14450144003030f55200c10300b6014454048a860401204c940e40c2075000b50b070340d002e8040c0910314505203040d101c2c00380c100001c0d100c1e801040c01e40d041d20794151081030016900e0030070410020155041c001e1034040345400103075440d03d02105454610741c00401c4001410380e8003c100300f541c0e4940c000f049022000081d900a03032420b00c448000340018401c0c1c0a012400040800a24540341e1001140d100f902901c1580303550300100014001701d8220303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 211826897 1250 211825647 211825651
    0x10f090203040618050303060109050303030c1b07090f1a040b030607030506030a0b040f0b0606120c0a030219020109030e0a1202130912020c090703050108060610090902120a060605040e0708 83
    0x50000012016004c40030541c0c40808480219181d0708000700300706a560300b0580380000b500b03040d0001c43c258a480044803996101e1440883c22220602c80320f09000c5c00200088405004200028440c41d4440104403020b00400c1c42d9042c0110f0702005661818145441440d500719070090041c442030b04c8110b0300703400518016120f5034040c080e484403c40071400711040300703000314410004450301500909004818640c0605610300c114010000d55801c5c43c044103403507800484e03010005540e0007201406030000d01c41c07180201440b01d9001040202d45406600002c03107a4080d884028540b505c40c0704208190119000302200b2030052044000942800805003651185c15040080c2d034226588803002c0003c14007100f00e006034800d00c413184050070412102038000039582424001541054040ba0301c6240080c6524081c81d0314090110340c00748201c140c84020b001400046640d0081c8910000c0361610403600440030b00d00b4a140094814865004c640441d114030004000d26280c41c80304440030800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 211828147 1250 211826897 211826903
    0xd030504050d0807060b0103051314100501230402040f531b0f01140a0f090f0f03021201020f18120a1e050102130306020a02060c03010f09020304 64
    0x911010a01c2e88800400b4280b450194010b03944030311240c6801e1068401381554241058208824403843c010702c080207a00e8103910008498440da0580503881c070b000580b110b0251694123000000403d040e44002c0001c1600c0241840c0d904401c4e840c0910003a4404c034450140354180d012000c11034809a0000300c0c1c00800b01203202502c42001c07141c119500040f44070340d003034414104001c0c0040e2803286410780c041a118903020f00450b566001c00002c01d02c3d16028004d0099550f0220700ca15a80710701441e5001310150821f840d02e40041410040c50f106030521200c0200d1041000400c4004131110484100e52200001c9401c050a690a00400b842450703404d000964003480404418100c1ca03003d404142940000b885506a00004110720342504170007050154100d44112400328403042e20225010810301c0c2000006c5a25140540c02803050b0742901101c110380030804000c03c0319540040014000076403c6683c0c58803041c1d0011aa403200703102d08d0044d0510000100506078103038000c1c0d903100340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 211829397 1250 211828147 211828157
    0xc0c14030708010212161706010c03031503030f0e0d0506060f06070602030112061a030601051c050a050303010f0b250c0e041b060c05100906090c060206091207050a020d03 75
    0x1a41e442c280d03003640c004c0702003c0d040f40b130701c2010071122011107644550441c4151500032402c0705a508080030041d800b50050341004036404c0c1c000c040c18000d40000d0440c24003002c00032501c40d564100141a141100c50b608000341c000c807079640c0c0e145030801801480c0d54000c0003420840c3c94040c02c1000c01121545501c0d0489418032410011845030309c0594000e000140c10300d402100e047c034148044400d00324141c4140c54001c0f1030403c090303e0000703030141501c00540302d404903000d10070440c0725542e220601c0140148641c1698004024000c0007550403101e840d0351a918050b00d48000c0d900c03078021300780030f034403204003041104215a0b40310460161040c001c619008146803142c1c0c403c805031108607030a507070951001c417101d140d90760a802c2c0e00e0020030041c51710036016052651581e448484488500013580d4403206914180f051940c04036440036800010803511941c0d920001e900d8aa00316002c0384180581c2c040301c2c001c840050308449140368024040c10f00001c840e4204950700c030074600150b08102c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 211830647 1250 211829397 211829399
    0x80d08130f050604060b042003060907031b0e1c030f0528050c0d140a0305150a1502010b0109140613090f0b12190b0c0c01020f0903010c0c0c140307 65
    0x22000d004039070044e8042c04012826126860030701040c0c50340082144440031800c410590700e41e1403c0d0a80750021001c50301d984082d22840f40890242541d100306043c0d2903062884140c0007504080100000b0100344c581c500701240407909400650505507000e4089200140c981036002e210f0401401d031010500c408100380d124142102c00c000782d108180300d021503c00114403829107420451a80c40c00030743c0c50802e904800d200600d09440c0a294202c8080c1a120004201e4450800040c040d80d69809488800c0c015950f18448a41e0b0f91b6907010318015520f0704210102551040d01c03000207898074001c6000b00e0750890014058241d020341c2514450000303e1002085011450040d003001c400e12001c0800e80e14104030030800000100d80b58502d15a010021104044a20803030048000b508181e201082c2c4d956064180070b079218442010303400303501c0016054910f00248000e00301c6208158020040c81561600580340c2034640c010180000100c2a02004142c9069045280581b000340a9410301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 211831897 1250 211830647 211830653
    0x7140c01050f090f010903020316050c030a1a09060408030708060402091207050102070e060a03030f090b1c0c050901080a05070c020a0b070b07020a1101080406060b0c01050709080d08130f 82
    0x542040d1030380e900c502d5901c0c1c103103c40104104480d20400e807000008000ea002907540207984d03840380b44120340301ca142c5400007205015061182000c042005415640490381c07074a40000102601d20f2040d140782e82e443c6c0031840c00d00d07000680c2c070300c0b0719841001c103450344d00e0b032980035640c0d080000d02003a0711940800803151580c6496520512031400e0600404070a8100800681402c4054102003a0f00001904104040e500d0074040c1d0f040781d4060610000c01903400300d084503942c4050300041d4001e030001402a2071a40340d88840300d407007a1300182c10002000c0340c02d01150a4030803044000e000590400203e4203c0265a01c0282c001d0614104141a040203a0110f000d410183d40030140d000d90114564042c48210311825610503e58400340581c80002d581c0e00c0483c002d544401c03410804074400040c02c225480d804140074110003602d00e80c07220b90746160345000c0c00c0b04503a880b0004a0701c007000229140f00043c1c00302c01903040c0e141c0440555896205500402e2505400d8480340c0a011010001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 211833147 1250 211831897 211831901
    0x306061606140124021f02040305030c06011505090d1113141009060509161205010305030703020c010918020f16030f080c07020907030218040f0b0a140907140c01 71
    0x4000c80900070300d5503d40c0740110501c0c4d50120718206058510021003001c81d0a42d02065aa9a8021901e068a4501c4000108000a010310740009200303200010b007519140200040c0c50341202c2181d00c07841c42c1d5101c2c03020700712070328003641245a410111620708080091031000740c0c034103c0000a040301540e02003100020080c0d60301440b41014015001d01804209817640b94840d014104851f41032103400c0c500300100c1c2d919070004010202e4903421b40300c0b03228540c1c414803004900f00f192100c1800196101d0070070940b41e9105e403004801501c81d4550780c103155401280c616088a418280a2154041c4110040040d51141c1c1031150550810801c8081d6a08100040c0f09407500075624000104900500500b400f100a402802280401c2c810000143d84581400c0d50040243c5009600c0f1100d88415411002010300e809501900b02084d01013019003070340c049040c01d03104855502001e5500c2c003102440c1c1c0b104105091308803010a0004000d14051455540310b007403401c0045180c04030004070b10703007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 211834397 1250 211833147 211833161
    0x105042403110d1d030306010c0206030c120106080106080a050f01050d03050d0f05010512070b070303022a0d02011103010815061c0c031101030c0c110a0e09010c1803080306061606 79
    0x199aa204003010f18980300ca03050300e003582161360081d460b41c02e220002900703821308050004d100e20000000902c1281c0c101c130a840d6500f11107180d548a950b19a4005440803d09024080c00650300303000041142ca12401580c0c0142d03149000d00707003580d00740014001d0820315520309806000082082e0803060b40ca42c07280001d181d280d8440003945505000803c4070b50000500080e401c1d521000c030500100544004a8010aa06090050361140302c002d00380c201c0015004100f11103511040910120400400d04040901d419402041012401c49086690380401c1c02402c10b554001803031814003540c04080075400000c020085094039407000c0c034041c68000100e208440c880040001001001500001000844402d08060100e49007040d030052441e041900044d240148008250505071030300304120010b0065a04166010b14000ca8954083c00b12a0100400030303600c2002d811105101ca03a4000503280c1c0728449600d580c440d44200800d070b0304410711186050040c0c130f540900203411449415 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 211835647 1250 211834397 211834417
    0x2030f1816090501050a060c080d0207021503090d11010905032a100b03010b040b060313060f18050d08010e0703020a14160c0504020c0a031209061d0705010504240311 73
    0x100d0250705003418058103026071f91060090007900100440050410025142404c10a50700142c85900b14000100440011305811f040754a000007401001034001c1001e0046880360307100c200c809101d200060f4225451130201070800e0b00280a12076070030704541d01031801c003020544900c1d28101442c80407400c2520001065494640e82c041c1310107641002c0c0140ca100110840c1c08000307029650307010640d14400113242000c1d030440032101000f00a99a40403a66407014a00c0420021144406240310031101035000d880328403842c0b80e01e502d044e201c0c42c1864169010602c2c0415a9121403030280c0280d00086800c1051049250f200c5c003010b2130010140801040c0e0007110b445080075400c0206450360603400c80c2c0c1c000e6004120710300030801c000901e11000d6605291514640c280c2c076031010010301e0910002040c85003840f91041070821840c9900e1460b81c9a00281c0c0d990a640700015540e520941c4a080c113403107a40b01d0f56800030207403203903030220050090401007000d042c101075080c45607005004030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 211836897 1250 211835647 211835651
    0x30c0806010609150504050d03091a04180507020c10090b030705040e0a0e2a040207060b010f0c0b280615030f02130b0f0708040f1802030f181609 64
    0x402c24264442d01240c010b01c40700d10010300341219a50003d08901c141d0069034051600300321614105445080010010461504d440f810201110340403440b070b510500c1130280800c550040302d1090641440350a014510315001840031040003c11b0000c0812214038035001d101840000240324448500198441c220036034581d55114140100082c1662026107040b004a00c0e01e610000b01001c0080c40c0405041ea484425108540710880e100680c1c0e6190307601c0f0b030081c0c00416828104515070304440304405d000d8849400351022905c007100c3d0a0803100380900b84030784034400302da460031142d010f5030f8030202d9008504110980c11644031040d41c00c1c0d603000310a07606011003558422580342c45070980b00c80c0e1100c019880c01c100260300540c075801d58014007a507403600003180020501c4490403a02c07016030007424661500e503240801500301c0c14a00c01c1e02100c10f00d80d113507201800c040c1c0c401c480c03040d111180d00c0c9075242c858891181d548100303003c01c03012a00c10505c00f610f45141180920005203458540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 211838147 1250 211836897 211836899
    0xb0d0902040c02010902030a0803090f01111216080a1e0207050f12070c15020c0307090906061710110903010e1c020303090d0302070c0f06030515030f07050103020310030c080601 78
    0x18402103488030b140d0402164541060100140d4010402602d0f66403c42d401a4594440c8020f1905004080400c11829840c0c12014408a402d4901a02c0c110f182c41000d10a207550ba40314400c0001501040a800175110200085040c1ea0300d5200702c2c05007409541c00304030064508000c0c400c130780c001c02e0103443c01c2e803200400c61800001040f04104810314141c606080c500140e58004035207005000e0b40626044e6041140600c0e4405c0000000d001d000034102e070803660b5120042c0b002840e019505444c410705000010a03003c000100400c100b42420b40102401c15001458400400b014130744422180020022040d103a602400b0354401102d20002070403040144814180b200741091745035105542041c41085000a008141c00b0b002c000c40e4103026a40f480d0078907000d86100107507004032815400d0020f000c120107034180c7c005441428083e080c0c3c046203480c00c04150765100200b060020551040409020304c2d403084d000f560700302c440fa07400700f020103450b0f135120420060243c200108a90180c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 211839397 1250 211838147 211838149
    0x921040e040f0b0115020d03020306120703081909060905010c060b0a080f01050a0c08160203070203060709060e01020109020a09090602070203010501030807020102060c030f01030b041b06030f1103090303040212070b0d0902 97
    0x140280c0109608020b04004170034840c000380d144c00644004009140d070100001c4d825444a00320400000842001c0d100c1c655240e00d04218141c106d03c101c0f040c2948a242030006490051284405443c41c0740c46825500e0b00d00401103484240d1920100ea002d61a1401281c0644403014040050310303030480682200141005060308440e00101809400b40c20040c032a4401a00701821079007220112082c03220302205114140d20314403511200a4040c49044100100303146c0c00114042500d00756502c4499090780540120700740e031024100603600404614040280e00302d1a405003101e644610005401c000301600040d007145c000741d000f915802070001c0c0c0f1704110740c1d041c03104a6010313a1041d07109085080c040b511600075001400001d00d255a200b0101d000c0c400c2419540c483c1d85007124461190356220080200548101c1100d440d45a04086440c0c031003614442c16644150505002103040d80e60719000c10002c2480d051030319585015483d00031481e554030317200a1182002100000c0359118880c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 211840647 1250 211839397 211839413
    0x405180d03090c1401050f0c0a0b07020d12051f03060b03070f030b0109020d020d0c09050108090d05160201090f090506090c0a05090409060e1902030d02060921040e040f 74
    0x122200401d46810400400500e004031144196040c211078010a200c0c1400143c94600c40e180810455640200f682c0070500c0d0300240c00003c5500c14110040192201d0b1000e9990701d0361042d145020910710203078040da840c102d4bc070185c0c6c007400741c64402503044204943e8811407481a04162121900c4c1c40700c50b102410700300b01c250014021011200022444e640310b00b0522081030203182d003031580008484200702d4854040c0c5610441c807400030852070b5034202c8003900c0c100c0e1a11440d4041503003080096044280410340341e005a006032282840c0080b4510000c1d40038500200484c10b1181060010820600740804c000142c0024480000c031410074400704130401d07200801c116a428800c21604e4241544034060ba540d0344020389000c00c1c017512a180440261117040c040300a24458024103554041544240b818003a0099042e02d88183c5000003c070f0b141e2a00701d4114003030340d000c1c1c03200ea0600844ca2220030000c945044c1e00038146901e8500c042c2074207500351011b58540141c5525501800054 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 211841897 1250 211840647 211840663
    0x210105060906031c0909140f0c0c0a0b040804090c02031806070c050402160b15010806040606080f040615060305070215040c05150c0105070201020a180503030702040e0c040518 77
    0x216203000312450b080c0b000982d1214810740071540210f01400e000c1079580100c88841c0540403050062003a800d007000401240ba2040b11516141400c1c600402c88030740c2814110780145203d0b8010308002c8245031144412804050000c4401a0003000b0000710744925210b0782d90030342000d502071940d45150f15000003483e20030150591140c0020000a8001180c10003c2d4049910669004d0313141d0122000300041e4403008070001d4443e5420314204152000034903800407801200341c0b6886031039112001400100c68241c0940c601203100f00300819002c507618405075502500c5900e000c58420034041100172006080d034410804a900d8000b804101034041c07280704805010740c980d048442c641074444183c603100d1071061030701402130b52000490b40110f000c112103140807040f000344842d0800d038030300078000d50114050b40300180d07044640136403421004100c1400c860000b00214101401502000018609200d040645118012083c401034070f641c016544541141813480341c14955804590342085d070310b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 211843147 1250 211841897 211841899
    0x160609200109180b04090b1e0105060703050f0705030706050115020615150f03011203090e040317061f020706091d01120602090306130c0f051008040c0521010506 71
    0x3540d11001a644581d01e0411280c440c0314003005a80c101a4000c014a14480129007003820f08075220280540c0100c500c0c00792040c4c0354841d0010b000c2c4410a1100f003c00e011780d65000318100800000310788100c020700407560503179001340d141100951b681c1d803440c0c3c060f40044940715100c3e0010051001d88a4082041b441c03d0300103044a854090000c40700d001000303071035501c40c40304020043d1000c0400002d0300e4492a00c9084a40e59503140c5901700505a19808110005910014045441c412201601d03020300e0781074480d0304411608048684281c4401000203400c200058100d000c00004490b0302d412519181d000ba01b003950500c1401030961200341c00440d07140c040d42c5541c0c243c030ba50070042d072030445268081e0340aa0003500d1500b44042e11410f041c06516100c0c17001400320300c50041110f03c1c03e0510400304070f941d89944080c00039210070f0f1846030320351054241c45809d28403402170fa420b56015104e440134021042d142c2c0300044405090140c4910429030000c4548070400302446040d8002c50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 211844397 1250 211843147 211843193
    0x40e01080a061b080f0c04090e15010b0412170d0203011d06010e0109031103030d02040b1309060e0601050d0e0102030108010b0307080f060c130b0a030e100903081605160609 76
    0x500f004080e014900c060314014107114410b002421a00c940015034010f000380c1142808818038103002640c0c0e440350440b85012400d407003800014810b0310700085408a41c00e18a41042d07102c183d44542c4102c01346407981707070004e010402c245200e0144520003140a0400c42e80980704644c000100141300c801c000301501e040c801c0780a1240403ea8010140000f00c0340d0000c0e00c03076041004039022a0440c0101690001d00724008035003c42c010746540f0141c00105524840c600516035201492416240184144081c035038980000c62043c1d446100204041240c18130007282c6840321424140c2207a0090b40041003e9642d060b05424074603081c044030b001401514010007484401d1003c1a80b5240080e1070300d03036000e1000980203032b80300d680740c81000140019610382c0c0d191a0344200c00f40150018107641c2400c0d010760364103450024040e204202c012500355680035040d51760020f5a850420300d20304000140300e401c1c4140042d5100058070a41050310984c4081480d48580c40d121040314900800301820030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 211845647 1250 211844397 211844441
    0x4030b100f140111030c060402100206070e0114090d121704110f03071203170c120a0c020c1c050708190605060a030212060f01050a08030405040c0203040e01080a06 72
    0x248074014260940741400b800d15982c0c9208801a03d5034019403010300381600010626840400c40130400354800d60080d144642031215501080380c4031001202c41c0c80c00b141300754030800402d512408038001d00c20a1102c040d03103007902c00c10015200550266044034004061401c0700d01c03581c2d00c801c4501c1d6951401c0728001030750420f643da40091510800e070380380c040c2e03101020f840308640e4104400c04c01070400d81c01040341c0d6105820010004480184407005845404011461076800d0720101c41040e42030b1030890045c0c1e00c4d0910000e0150600002000443c441d0500488565489400510380e402022101499003c040e00c9c100d420008c09a0180d409500080c1c5840c046901900d000010681d20840005255940400140c074149813904040c1d0802c01b4103c44503841540001c0c0140100301e012407802c0240e136130707800b0007241e0389050040c01016001404100400e05080d0800d401c0d80c01b80b801a80d040a49843c1c034120080801d920103812684000a408140500c51050480a91910b0046800b003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 211846897 1250 211845647 211845659
    0x130b060d0506010c08120610110d110709020f041706010501050a2303010b090406090c020a060e01021b0a0605060402030609041101022a010305090c030d050d020d0603060204030b10 79
    0x140103841400a08585400004855038400e21200483c281c0c06800103444518442d82c4a4100e2811908280030f500703000d110200c490301403403040c001708441c04000c3c509d00302e281004a403411840c4405041520455070085840559400030f00070841c4a4444241c4031440c0c44000e540b60030b0440b0140304607800c01001405039903400800c40f914075400707080c090586000301c3c0380084403821101041e03102e52070200c00490004040001858407040031a02840002e80340c00000048074040914100560f01010280b00002c200383c2000c4007640d064000181003400a4a0048200a8103a1000705c0c50708140c0040082040c3c0744201a0850420754085042d450700340c0206106800181024200d01c1401c0c15201450384204000070001d0554803012144001c486104804880e080f84660302107410b1000040900b1400160016000c00080003008038020140b806c0d152a03104a92141c44581c00700015860383c1076a0280d031004602c0f442005a891785941030079068441e01820300810003905000c10448 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 211848147 1250 211846897 211846909
    0xf080117060c1b06070917010605010207091503020a03080a11010605010509040b12011401170a0f02010804140304030b04060507080426090a080d03050106023705060a0b130b 76
    0x88a00725041d083d50350341040d40ca0030000072081100040d14842c04c07040000003540070781418200c8114900704150508140c1003942614054019030340180d1280c40b04118450080d040008105c84c0c507540007042c0c54898020079000c20b516002651007000001700c04400f1a0b03c80a258036681e01038000300b002c00d0601000920511980c2c0407907100f26200e84040f042076030341c4510342c006981e00344003c12807a0542c1841c43c0301c8501c01d10940e0030404100660424913500410703060226a4440005c601814035540191954400030b40300303a80410070788503602000390040000308042c40c025051608a8075251409070b0580b03800900003400c1102c12001c1c0000211301092210186408510200c00c1e250014030b08102c2d070084802e100e40c080031209001881c0e86000c41d00507003014055409105030f0707032140c034166504c030707031010a4400034042e0b58202c04847c4000f00e40c85641c0c0c80d241004004009840e19200d10703011059416447c801e649003082c6216203808001107030752a1402900340402c42e0f8540026003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 211849397 1250 211848147 211848151
    0x309070303050a050f0d0e0c0406050a091a09090a0b071e2106030f060b04050709030803040201020106051005130e06030d0809210406021207230c030d0f08011706 71
    0x424040b0102e85020300f940994203484030000209206500c49070800982805001c0c00b8848076505e01801d80301920f24102401060107458001d040d2101b40751404100500a00c5010f07102440e020b90003600c60020365882c07001d0341c01001508001d1144a50500704010368407000340582e0140904001c598694540c009610b16215a031410310002c0b580c0400b28020403407100070364544580303191030008410011003a103080c2106000c1c3c64200700c0910110148400c680f026521100400d0003640100b00144002005650040c4184004070742c469035400032030300002040b40924081a000310308032082c010044030b03420040c10b420b9460096403c02d000400e0700c8490756510319003001110f0002450301407041148801842454282d00e1040702c03131102c0740c1569001030047c01c00500456154400a181c0c0f541500d41c0c1d00e0300280341030f403059034a050070303112155006506c00060144011170200c51350148040018002c3c140c45e04001480c0c0c5c46402095a48140c000110102d9070b42c1810a1894001071516 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 211850647 1250 211849397 211849403
    0x7060921020609030703060e030706050f010803041505070209040f110d0305160501060803210108010b031902010c0212030a230306040c020a1502040e070518130605060f07021503090703 81
    0x207603880440350b0104c2c0c1400100d1b08060240c504129280507000c00000041a00d903004000400c40e079101e26508100ea40001e21031140c140d4406c4c0000d00c89050b120108549001d20303130402c1c07854041103602207104600110303070540b001c1d064052040d040c00007008041c00480d4080343d20101019290760058101d0150180b001c0803c0300045400c0b04200d025030094026010742401c490301d8100550b01360802158002000404185080c0009000790b0140900b41d08600300074040c040c08bc06040303028000200a0784260304008102108201680740c10b1401b0f00884401d1000d5a0f4848012102801c3c0c01c0c00001e00d8030b02c000141c200503040f511030760117a0ba040070b0300300c8000c1880e207e10700b022882c0c29090b841c0540705200115074040350440d2a4010021a201600550075654981c0c1003940c090103900250040407520f803440086910340920000d02e0390390820030005060f078130b403404102c40d5000b50381380f10b4240b0800205007041d40350030a004949540d0340603001d40f40d450314030b5415407140f60500c401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 211851897 1250 211850647 211850659
    0x22141f0302030c040f08100b120316110d0f06050601020d0503010902070c030b0a050108011a010f0e04110706050603100e0304060e01350124050702060c010203090706092102 76
    0x455410f0025108aa0007802001100d07845640c803028416261103184080600f11494001002c03414107181d000640d560403a800070714100400c480c0300301f003c240c0c9500c040390b5018200300303a10b00070354450002051032030060388048401030092410504481020f040710341558066100c1010f00c7d5072100440b03041d111152400f5803174603e949001901c4185607003005002c090b40104000d80e80b1025440141241c50b50002440070340104403c0c03052420304181100d0006003030400c610311883c028031840d1441180540300090100e294001c03a6440d40008008540082c0c5400c18040280b03010007001900490758401040207240154885136281324038800d80c4107214034802c00d002c0903805404810603103441030b05002c0c6081038451004007000c0d034100c455410102010300100380d9503521401c0102d198942c107501140e841c40041c060320660409a41240e1000003000240c000c96002e0010314000c146000040c041c0341c1c02d2420160034001e4540080e10500070202512028400b0424038040190301500d41c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 211853147 1250 211851897 211851901
    0x60405092d090d1d030a03050304111503070c0c030510020a0210180b09150a0618090b150a0b0403030905100309020109050906060c0703050d020111040e0c03070522141f030203 77
    0x60324030760400c0313038140907414010200d4500074590084000d500c602c3c455400e50007a00815802c005a18a21500215140f6070500000d810103010b075415882c028040e05819128650b2560303100d01e050f00610391184603a030085500014981c040000b18001d00010307909002d003610100003000c01e81d20712200074240d00b040d50081841854280032020200c03210950008903864044d4540c1d0190006114900310512040c81c0320701d444409105503501c06600480303100c119100c0c0313401c04081c4101c10300c02552180d0340b40000218885404000c00046100341c9038184030604d40010400001d1494150038145070500d801100144e030310100c0e079400d6071802c0700c51480c01c1d00c80f9400310710b05015180c160303803071841080000300c140300d00003400e0300b0b1040c0ea0b0760080c03001c1c03804d04d400e0f0303d824041c611803101e9400e0781078041465a1541c1000d0340e813081c103a10305503050103810550444421510341c03d00ca26624900401c1c0000c00c0140c2004501d1641030340c418407440b4180700858070140c20384143c0000c0541c0800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 211854397 1250 211853147 211853177
    0x80108060a1119050909010e0f1f0e0f040201031413120309060c030506040c090b09060a030207120c020a0909081821010b040510031709060405092d090d 67
    0xc181d0f500c0c0e0034100c940c1c400d100795001d0090015403080e040f65109a100800000d500d40302070138124451441e00360b404951b03485078100d4651107003004007489040f0380201d401140d6001003654280c460940301621410030700707180c0009011600f60340b0300b01e0401c0e01d0180400001d60503080751521016841540c0c90300500d95501c0c214000c0c00204001401c0c0c82c14030312010358103540341d000766004040448013000b148078515001d6410507c507201d45440d0030030500207805646042c0000d05502130590402600c4c25000f640c603040305003104000200810625079856080d41402120034010700803001041084c58080d40301c80c0983c1c051801005e0803582e42d88512070031500c41c020061601420000610300003003e818080e8040e001c9070100302d024a24140010745102d00703281c0c0071012250011980400401d0045915030a503004881e41034001c242000002010341300d1800c02c074480d00864407000900045001364540e500d080c1d607040b050816141c4c0074400e40010205103965502d2444c00c16112030a0115 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 211855647 1250 211854397 211854431
    0x20a0305180a120606050306070c110a030f0b0a061a030402090601020a23061b04051e1c02030d0c2102070906140a06020609071715011e06080108060a 66
    0x554515080b503000a00010000084215445002d10038070050221680302e40a00d81d55507021200c0d0000100000910404a030044040c80d01c0c0800151500f00c0140e100d880d1981d600b800b60408444401e102c10030051a070f0414807502002e80680c0201000c100e41c00c0c200074a240c04090310103407040d81c3c11300c045400d5a0081041c4401980d114801103120a800c0707420981c500d10b11002e03100c0764066400010352115000c086410121800706c60b0a003040e00386400c2c480504001d00128442c0380c168114440b10356140c0005005101140c15001801c00c0305205044c10f05809040c098207100d2200d001c000000c0010703194042078140d00318022020300d04100128a880b1842d4800a900d030b14040012030014502d015110401c0c1c002d558101c200c543d2400200d0f44d40504499000300f40d006010103001c051411070242000c04641000c6400d01541180f0681098400b81c0c442c0106d122500340f500d8840828a40d050000c00031801c02e028a9032610060b940c4a0741c0c0205120704840c0d407500b40c030219140c54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 211856897 1250 211855647 211855687
    0x1303091502031b0601060e060903030328020f0301150e030705060306010203070c260303010825031208060126040b070201090c0b03040b162019080909090607020a0305 73
    0x40310700040c203c002500c1c2c0c0e6443d480207006010020f40e8900e14416903090000403070356040000703401103256559098000048135040d4a5480114001e01c0703920030a5240360014007500071164004550301c1d40740980c4403d5944103041a8014842c5144149034540e82c003085010465006980c2c03141e4030b41d54000100e007940700c0d0444c000d1060442a1022480c00e82c4140075140036103032144a0240182c1004825071b8900091003403090380d42c8202d4040d1002c0540780720724014540300c030303408840c000e491365544a41d040c9441c14140000d51001c003008115a07100d035941e040500e0410301030010700c0c2114034109013241d0080001e05000d125102098000f0310035800385003402c0e00042c0d0850070641f60703000d040040d48203460a0f90600c4d2644c3c04100d44085000042000c03080749c0d19148803035070125900c8900700000c641900810f00070a0040c4880b40c00e01c050000341d1074806e4a0a40c0d90700c04100800500c054090300300c41240c1d110404110109400203201c516083c0c150510f59290410015405448968 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 211858147 1250 211856897 211856917
    0xc09190f0b0702040b0607080d0e0c0901080105090105010f060c020609190608040b090106060c0f1b060309140a0302210408010615020613030807031509180308130309150203 76
    0x920040040c90100c50400b4140052007210b0078040d00120394204030315800b5940e00607000c0d18041181451000541d4001c81c44100f4410584081024103070000b61069826070100300c043e51a0f5040110301c0e5020b118131809000a0800500b100341003003c02400092030880c001d0040303200061111071a907403004540d40c0410703803000054003107072034070f03401046201c054500b00c42c0c504000d0007081d107100c4180035408c1a1402551001072107040c944403107071400c2d1800d0307041d9103298404000701c681750144000300b405040039413400704200440b8035100001c0000c2c4d858001c038540040d41a10002503010600004489211901d0019800507942800c00c52040d41d202407955880c00b00c0000350800c18040180c40a4615020743d81c0740d0f907a6041004070509041c0e0000c00080b0f220340050704140c040d0b44420030304e01c80300c5814010141c03120003600c03c903099140f00e85d040603256240b040405501503049075209000c5284140b001e1615900a40400158050209144094809400c00030b01c20410707501c3c03003c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 211859397 1250 211858147 211858169
    0x50904061a040f0f0e040204020f1b011d160603020c030412050d120207030c0326010f080f15040314070f030e1e0303031501020f0a24050c0919 63
    0x1c5011200c4003640c864421803280c0003a1100c000361400766070900f982200c20380d40210110342d445a082000035030100e42240c520340400e11a106202440c1c1c1103152081c0300c040700000c2c0c24182450304002100e40140c1e0080107030703c10b0007250f5180700ca04c0c0d841c504a40320740c00e0158507070111601003420b6000310b4001c0e000800c1000400740c140040017842e40440d0050b5200c2c0700c1c004081c144250140e00c240440940072030714405402d80042e02ca0301401000308400c2d0b80e07041031107000c0a4912203034082a0700540800c12000002e100340d503400d009001c09196104010440484584040c98001c10001d001030300340305181071034042d1b462003041200c040c81d510258654050301240703030103044010024601406180c186005001c0030039001058550308100500450640d41e94070100c16042850f011141d045008142000c4900003040221a04240c07041589980327a02010315201541c010201506407041e080c0760500603407404420440300241c170151240c85d0607000f6404090501c2015a0116013241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 211860647 1250 211859397 211859429
    0x609020f16050a0219090507030b03030715020d0e03030103060c0201050108070311061b030c0f03030127060e010b0a031506140a1e0f1d010801050d14100902090702160605090406 78
    0x910305445c840030348803802d008200700e4584280440803100400700182d0958020492132011484030f10b10407100e03021009001d0715210000e50803100b5901e4803a03080c40b40390310100040c400c0040f140620325503001544000c20003036260590300c2d66601d0262002420070702c90880e152a690715404100e40d40d403d81d0790700480e0119500d0001550326441301c84400228000c5e01c01d01c000266010007101d04031117801c50714601004407000c3c1c95407140d180080d0b210701d00342d031000e0019080d1107404005000b4140340701100d440c1d22040602606545101c0b401541100d0790300c2090140a03000032034802e040350082d20050311003452190584089946200255001547c18486001c465020480000310707480e65480411864041d800c5600070044080680e01142464005101c2400d00b10452518a80a0002c4140052440311610b05000c4040020f2031003544039840c480c103608000300465080308070f03480248104c20030b20300c501c180a600360080030200640010480c015a85642243c000703012010242c1c0010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 211861897 1250 211860647 211860679
    0x30b0c0c06182b14040f0f0509100807030311160f0f0803091e0d0f03080a0c021f0f06030b010905090115060905040207060923010609020f16050a02 65
    0x1250b01403a000c4594032801e0b1403454490181e01c0f200100d07440c1103000e01ca482451600c103131040056100c40201d00c500c1480001130207000c0d07144600c000d0169441c14100e060030901400305e140d000170101c804c88440d81408000100340010303440c04481c1c140c43d00b2500c40c000c00803594200341d202004152643c4900c1004140c10b0704c41d0078070f4012940000c01124466945415098490107401c140560152801c4000388002c90300030740080b5100801000c3d09902c850a5491054004010b002540004d1001c801c1000c1c0174442d00c2030b5400d109283c0010a9800c130124a00720050401e00c11400c00c040d140c08290300c5203159604040d000c3c690220710050f5560b156455003005080440d400c101560800c032803500512039901d1102d060314280d545801086050030103000c0690300142c802c440c0e45036915000d10119024401c0e070340c035018400c0c0408032a180c5400740d05003964900d401034203036180b04001081c0302050300d00440350048405444900400c00d9400e205080c98510b40000e500322404080d5207000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 211863147 1250 211861897 211861921
    0x120604020f0405090f0a0b0a140d03020f06010b03040201030b0d1509150204060203070b060a030b0106051309110c0d030204060c0f0212011103040314040e04300f091d01030b0c0c06 79
    0x20500511000b001803400c054104045440b45100e00c2c51b00a2027011513041030304103003400000c194007070300440d00304051040b140740c50224242d0205d0440200441031000315a030502600418070400c989c184182d40c482e0300d030403501f580d0340c280d200701107a0742c0c4034540e040000750030503400c15018140085494071f90329140a03440707901108045038101d0440c2c00156941c50450f200e082601d0b0807800e210202da0901c102514503900c032001003a0381c156a503c00282d09030b180d000e1264400203070450640c9605103200311915148801c0c02c03103400c0c140103202c2806515400344940b542a6008010511a81c00c140049400042d09884c00c00840d400c0070141d200483c419001107008030321030f079610074a0300c103040d08450041c01140145580c41e40c022000c03030f01240720140a0442202c005e070781e00d012070400140c880f640001d00201000803406044080751110740000c500030080c4000d50185940e610080c040d1241480c050100500e061a02008074418002a07029998200075010881d0b04134281300144001e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 211864397 1250 211863147 211863151
    0xc050106060903110405010b090d0c030203070b1b06072a0803010902030117010c0206160219060501061211070204020c030d06080a060501141e150d0b15120604020f0405090f 76
    0x102e84044c94100c90403818513120303141c101d55504080c0750620852004105000b28106800d0307502580780007009c009650141b14580040150b02e0b4000d40d60300c0c0b8036041d0484180000c011179401c0d0002410400d9203600031422b03002e0460340304100702076110051044d070b0820083c2d0b10043d15007003000c0000301d00c1d024158000c5041ea40b580b00100c075040603403ea101d00369554544050016040b1b040400d000207810140c080e403410050058400e14031a81b050f4004a0001c2002034031041d4032400100a041e41000e0580d10418802106002c28140b49441036018400c500c0024015030740005c103110448018400c1e9044a41c1024050004640d180101c6039a013860100558220b4605000045d2081c01d01c1e407421803924010702130744118072055400d100c10044131040c0b15081080000000d00c40c1e00b000c1c1c0100440320b41d81c40300207a0812084c081c8040c01d0b4889002818030001017064082c520f55901485500c40c004860150f03840b21215440c602c1030003982d02c100d41001486091040e0b112400c00101c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 211865647 1250 211864397 211864403
    0x3061505190312120912020105060f0103150b0d02040f141c02010806090903041512051b0301140f0607030807020c06040b090904021c0b07020d05030708160c050106060903 75
    0x300007207a00381c4080e4040d18441c032005009035400040a0300e9035004200c039100c0241405800070b81c1c0c11003901d81200091070100c80d0300041c0d644108010803071401c041001a094028642082082c402c3c103400305601400d409052212031010a80c04401c020a4040ba4090301c444840c107010640e0b075030b41e0f4420201c00000440d100d0603803140c610301e644008400f0481d6540e016510b60100752140c81c140311a201014280d01582e000801c40820742d101004003c010383c203143c0d078400200805a00241080390703406440440f140d4010510610000c4440d01504d045d00c002642c00844440b0000000b043c080220000f1500814003169101c24981c0050245108200540985a0040740c1604001d268411405032003149207081c00402c10900f09541f400e50f000b80b010303208000116842c1d51413501c0c00c20300802110306103280d80c1040921681884007101005142c140581541042c040185c0744180c020700b9082485041792400e80118424083c0c020800d030010000c100f015280e0100800a400c2c0d0b010179 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 211866897 1250 211865647 211865659
    0x40b0a080a1a06010903020121020a0e1305040809280902041410020d032316091a0415050714010204150207030b07050a09080d020303060f0d0209070809010603061505 73
    0x1412040c0302c166940b107044140d4078220464115801543c41103000c641800039050181c0d4400c1c0d0041040c401062000c1194641582d5a230000003000300c0d48509440e940c620764108418040000c3c03074030301540c2040100720350090700c1600303c88180200040000380218100d6000744009480401640104140d61040080300c04a0340d140091000c92812420542c005034400000c2e411f94a200360f0002c0d20180c004804880703200d0003400b8141d0a0502a02c6d6043d1444c1031909140c001703a00032a20380c0c0180700d6820051413240c000d1100043e01e010718400c80c000d40c01c0c2c071708038070700124410012985040d43c050810310316108850340080c000d42082c01104d0003a0350a04030100080e000052a00c1120780c401d802c200750b42c2c0c0da020201c035150403000c0ba82d000d021ba68400400c02c50070a00c81038403460381c640d000b10b40324a001e008108401281900590198405103e20005621341209041d0322101d0360608240a0b100c01c44c000740145050382c07020f1314052505103554031200040315110100d03081141c503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 211868147 1250 211866897 211866923
    0x1c0812070f0c170d0b04051009180b0f151305060a050d0203120904020408070605031603050609040b04031b030834030902060d09051509030a050d020306040b0a080a 72
    0x826100301c2603100c0050540102e49412800d40000200140000b6004600104141d4502d0b404101903c1f000d0702c4031030700d43c42c010b64140800d00783e601c2818030300415000a0342d03115100703444000c9034001c007900025110121000082c003d440250340b1560000e0b0240c803104c000e07040385800c20000c10080c0e0305144120141d030400110313840c00217819044590024050b150000c9180350950466015004991304560240400554090113100541c02400350b074850a0352031408240c5124900b60701200a010b0528103005e11035145c0310880300941c80396201d0700c2d0082c50340b00d50406603a422041c00190708810340d50b4204d441010b034000c10407806184148641101e00b000034201b500884108140e0300e5580240d4500607416500c6500448000c90002d040f4501e4508201150410340b0b6411801f91265484000100312910001079516800b00c4c00f0409541001b0841c80c00520a11441c45a003a02c0c64011022512613502c99002d201a41c800034008040300342d0f0303103954686032002900c0031356100e860214 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 211869397 1250 211868147 211868177
    0xf0b040204050f06010509010302090d0b07020d080a0207110121151d07050910050412080315010905030706050d0b040207031707080405060408032511070618051c081207 74
    0x40281c01340c01c05840341d070700b01140900110025000700390034550040008800740c0205026100c41d9004480550191007038030203001c1c0160183c0b501074401d8500e50305c1001104003042d0659100d03000402d0902e4429003400300c000b40e80451021489404441c00d1404c5030300100ca2240d080c4035012684003154882e040311103026441e0320b441c011221503000c034900300302000701403502a034030304505e0b844d504000f0b082580760f02c20740340c01d40c0445201711030220001052052140110381000f00301c502c240b03030201f4803904000c0460349502c803d11508051040100b4645e0074102540c21079407003804060011034482005060003006814504021003602c051080400c0c100c0344903d8443e48941e0f00a40100b03019160395032034400c241d00081a64001e40c81001c80001000e60503000d0114401e0b046d0b0b50310700c50108502d00b140c1400250741c011414060311809842082c3c02002a41e0b00300c40d4110350040c00c02040d4150b80d001c070035003080010244100000c0c0311292182c110f81050041200e65114845529181 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 211870503 1106 211869397 211869421
    0xa020d030501050613092d060e0c04241412060108072d030e12040f0e01060503150f150d0e07061b08070f0b04020405 52
    0x18421216158940200e5024250407940c5a15100c400c001001c100c410921a03007500301e484402031030b801084001d1900b06054201007403403044e0303540c1002600400b10390090b10a804140004aa000c0f050303101901c00351480b102a440b0185061038000d0540c1c80014001c504004000c014410300c2c0d46244060300034000203510107050b03420802d0025144017001804070301000054004d002c8454808070711058111140082c40340711040c000310840c00f074611414088403920840d003660b00245070080007032088412110f01f80c1480350700d9107003481890340c0a106100c00540e00307001281301420607118603031800e80003d1210703400d05500400700e82c1154042c40d20219002002c40e00c071854020b00d024510b4081d030081d01900070b00703060880c0504010440c1000c0b0030300210200102e0100b0034000110ba10027a0000c14142e2403841500e00f03d1018401203c04034080e074104401b00d03000c90880 = true := by decide +kernel

theorem cover : BRFrame.Cov 211690647 211870503 := by
  have h0 := BRFrame.cov_init 211690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 211690647 ≤ n) (h2 : n < 211870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
