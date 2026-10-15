-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5352
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:35:09.065535+00:00
-- url     : https://prove2.me/submissions/1973216a-eec6-4eb1-bd33-90c51b6b9285

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 962410071 ≤ n < 962589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 962411321 1250 962410071 962410073
    0x506060f0406180f14061b01110a110a020306062206090902040c0c08041e0302060a03050405100b010801060f111c020f0111070f020604080109080306010f08090a03030f0f110304 78
    0x40c0c1c142001040e44801c011216171400c00c16913400380b01003145c1d0b03005560010314000da03c2d07081c0c00303500c20090840000b004504100004c40000743c2040e03d40100140101c103452180540020b029a030890f0020041c000d940c6401c000c00c0035841d0600800c400480c010880d0002c18000b6209000040694501c0803070894004d00c10081115500e20180c3e09018206140310045041c038401c5c1c6082c0c44000d0001d603c2d8982d000c03440000e1081c0c035070009600110000740850500d90581080b4001c41c407a5040b14640581c110340071003a909188039131800104a400104201c1c0d00c04c5404a04485050805004071f451846046040c0004502001c2141c0202048441a190704004014003000450001c0152340c000c181c101c0750f1445580000381503140341d024a80300355910b8404641c006c01f0940b00806c01c3d030003245402c002d560021115180072440d034000248600e4000c4001521036010b59014200c2102296025030017481c0b903181000340c050351182c0500c1801481d11031034040080302680c0b40c0c0c40e0303d81703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 962412571 1250 962411321 962411357
    0x315070305010f0b0a08060105160803010f051c110103050c0d1802032109151303030c0b150117040611130314030901090303080702101a090703180201030506060f0406 73
    0x1403039001074584d40041060148140e4044d175500d421800074038115550307034442040b030040880c040c600a0303e221400800000c003280c000410b1400c031001030700c070100c0103440c582803541401e002c8a400342c4120001e480b0840158425481158019800b81d046800e11810507044000c81700038041c8030880e003041007c89425850104511110615006501c0d12a011551030a0720103020b4980b50b0b81c0500301c0c427140e0490800365036058540084c01c01d29119200c03030340e0f4100140b0301d0f040b40e40c06403040d840a1000c9801ca954a2100500d5802e06864803119190350b10203115040303000500603603205036504107107002d516080c001030240006806041c015a030450500340701071201000d1030034080d4000c22418880e0390b04280c800341100c0c0c041c1005800d07681d40d064141e0808842c0c0600c142070600e0301d411007110a034240c0c618214100c094504034481c2e0388080098045600404941c1c3c40c00742800e81c41401984607401060703000038060325403401e201c0101350300007080d0400d405c007201050f20f0900100620390 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 962413821 1250 962412571 962412599
    0x103080304021219021c080a020303150604050a1206110c0a05010b040e060123060a03021902060f0a0207111806121609181a070e15090d02031507030501 67
    0x50300360113405086000b851101c413500000000078064002e650b00c0d4800c100351250511203103074229440341c0c1e80340000300c4000e440303600444000f10381c07000d600c1c2e2194050500600b81c8060f070b0740141441213581d040c1544501058102c84040310099101d2020b0401081486c01515102c05400300130501500a8688682521000d80340c1500403450b207482d1f000c21543c0040c141d81101c0840c0300346a03184160600308140d4105240e4030982110000441e82c010039407690040c40810f001604101031080e00c041d041f61204000c1d24031590202e090700110b50345441b00d034010000984038242c28100061104045465000c1041100c084d41d00340104211031424814011440c0e654444042c0c24010390359903444060356414003988012907650000e00d0300116004800815644d001601d4848000e103442d8200d80c8103108550400000d02c00c11564807250401c04142480c2c50a108001c2c3e06080040c4240210030f80303012400c1e680342c0704001501242201211090f40140c0c0c641d41c001c80d4640c101a12125261 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 962415071 1250 962413821 962413849
    0x151b010b0f0409051221150a14031b06070204140a05010b030103030f0e0f031c091512020d060e0906060109061706040e030c1518071a090105070b010308030402 70
    0x290924034903c0c0091000700700403001c0c120051180b9154000c074607a400040101c01e0000f0441c0e0301d4142032002420005150100c02c0108880d012501038450f03208503a036025402184c1e4250f0700001c075054005a00b00e40000540300301034445030411030147c00107002d94186185408504038002d041c000c00a080d0b000c1c15024054041e1050f113154516a00200041400100d0710204840144050103d544904054520107001411101032030301078102d03004115000705240700802c03c04c8400046502d140345094490f85120f448515808408030300e280c002e980100088100941d8074040403d20480180c4e1541c00b9044680040c000c0c2e00c0c001c00054070740b00c06078000d03201b400149500f0742080c001129680f81d000009072400f00d5001c4a40100c02d02d5405502d402e100d20f40a030303448002000400f002c080d4412080f03603501100041c0392942c4182c070361000c1e004008080040c480e04025140c4050700902d050801854068a418802d0700c5841c20803500303800032918180d00100344420b61818400742c0c0394503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 962416321 1250 962415071 962415079
    0x1a0105070506062e05042103120213090c021b1009120809030d02030a03180206090d0f06020c01230f010608090a0501150503150f0105150706090302060f0c0c030306151b010b0f 77
    0x3184864230b0140c10110640b5244c0001500000d0390742d201b1054000071801400449070034411680303d854081c2d1240b04000740302c43c021242e2034915841745480c803000c500c141c1c0780343c40c0c003980b903030601c1001411100d0a02c025910b42c40c04101804450300c00f000803900700c3c88903070b010f542c0310402c0c0c590040554030000300c23001031281d21140702c0e40965900c3d0200d81d00d94000712441c0b18030301800e11304031a40084400000e08074520109103020360354019042122486e00c40d107529030001c4412140e0045180d420340d0784805041a100050140e1405000110340101151048482c2d00040b961000d0a550350500c02010301c0d20708860410081c00d0402669440540d1881c0ba4681450055079502c40300e03038141326852103013031503680700340c0100113030400c44943ca500f00c5028000740801e070030083c1d03980c041640d024003205c460300005001d000c90b010030f03036203194400d802540c40c1d07072266010020101c9a69402c0c80e803480003081040d040b000c2c0160003441500c40c2800201e03241c50000c0c108551660840f25440c06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 962417571 1250 962416321 962416379
    0x3040302031e0c06180a0b041d0c03041e080c0a030306080d020a0201030c051606020c0c0108040b0403030504140d1206080f151e0a1a0105070506062e0504 68
    0x1282c00100c0d50071009041607542e141c44104852030305250020802d6680d8002604400100f44401181c000b40306803048454000e00e03222001e01041c0c4103090031146603450140900119001448007084050111840620404105040d4030740080c203a00510070180558810560a000c0580500a0b0303001080004051700f146956010041e4961a440900a04140d030b50200030003410300078425074144582c41e14001e101380c9030038a000d50080d488404102418840c0109004030396100d800d84512030307940400300107501d8440340c0d002e030007819024100b21150005000305510026082020340c0a0460350350707038180e11400e640040f800b1548260011031007a0409040d0a44101000070a040800d0407506480f0703881d1b85400a03410326140114001040603030500c284010b188041d000116420300c007840e54a003840446005540d00d1046000003001d42e00440001340452406200901c0409075003418100808002030200c2008940e07080f0400c0481c4000c6824000c0e0121258120014542c108003080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 962418821 1250 962417571 962417623
    0x4210210032a120609020403050705030a2001030204090c03090209070e01050a050f0d021b010c0315141503160e150f07060b03010501141c03120e01150303020304030203 74
    0x2d071140003111098014031940340c0745250b0758420440202c0f02c11245604010340b0380c55014481c06588244070907507043c070481034003054601d800308041580c0f81d4404c4000c2c007140d40785e4110305842000c2d6078409051550034400020200c5080c014102414115a4000303962040d91041000385d080103030004081002d402c0d0f2018090741c0000032505241028104651112a8940800310310b2007941c103c1d00203940003040c00d0101e28100039010352038407101c070300134800401e401c00101e0031603600200403104d43d10211010010151440114105078401511165030301050300e0103803090f41c1c8280c2d4400083c189551502d918141e001169080d407180480d0300901f078502900700d01400340941c55180d61448800209541041102e40c089400b90001500901581d17958008450010220905c4140101c00c0c0302d200040d00035980984203140b50345921355001a10520803504010081d900d000700c242d42d6214441c0410101c0d61690800461003035000b1503881c0d00f1481810f003001c0341900c0c1000b0407918172030100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 962420071 1250 962418821 962418851
    0x3071707140906090f0a0303031b0f0507030507060212150406210201081936030807180b040b07021c05060402191d15030a03091404020421021003 64
    0x6000a8003c03100980c4405824001505480b1042d080b05c0d40a58079200000406415800c80380c84052918003000300d01c8040c402c255040e031101ea050100082c2d081100c10000380c06040541140c0d40030700300044c01e04421092081110000ba60155240084580103681525150003580c0c0501004107804118161402c08401a400c0902d4000c0c140036a0348000f42c492050701d965402140d0340c031007040c4007690702e61aa04480910749400d441106a1b46110105135500c0107c02018490b819aa0810f0543e03e90000701c0f40030701d00d44010316014000d401d0005440b00741e800540058010609415610f410520400541784504a0001c61541c1c411100e580031036000b0400c01d50054050318001d13a135030304035401c000b40d500c115040200a07a000da0b5480700c0c00810700030a03503c42d55606003031900e0000b54034201350355290100001400140754000c1480100720844a4440c0348070060005410252031f600891600e090945500c00184a114070a1055107801e080c00b5101c203240b41400c102c10401d0800030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 962421321 1250 962420071 962420077
    0xf090b133302070b1903090b040b04020414040b16050f04080606040c030b06071101020a080a0c03090503011b030b061204031220040b1b01110418050c0a0f03110307170714 75
    0x60325901c1030043e4000341c074a006c1c1c0c100b03180c0c10b523000e2207580892a0a1512580c5204184c83c240d000d00e00d442c0b94803203210502180356010301c0e04040c1d0045240c0e00c0810000c1d54514600c520010010180640720703100114002038406041e2035009400d2900e8203c041c00200c03801c0c1a00f80040508040c04a0000e031162804c6441454210251120440c2031000603884c2000003a401404100009910301400ba81320480744c0e4210f1190b41c90307080081d42c500405099900841e2210600d03018204a042c19030b010383e0054000c64000b8004600b44150307131000c448880340461703041d400700d092a901903141500a20841c03040c04594030343d09070340314080b00d10186036003c4c1d03000d000c0303260000042281541d101042190440c100080c02484540e2241c5a1901c487c1c102d44140d40c0081c0e06480d103044c0094a50088030303c610200d403405d5080018880d4111113076440c421119060507a1003010812a00100c2c00461103031281c0c3d2a0072403801c05069940c0281d4100130f0010301040031940c83c200411a5110031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 962422571 1250 962421321 962421337
    0x1606020a1511160c0e04060e0609152206020a080f1e0412030216060204150509030d0f09030b070810060f0f0509120f0d0f0f090b133302070b 62
    0x1c2003803a031860304d0214006400360300414880d40e178950030802000050340140c0c2d680c5400109a441a8841c00d82556032000002100070304034a081002490700482840b4141c1e01395000d400700c0301d002c00d1030b40b240d10403644140d891000140500c1c0401030507501c05480550172900c8000c85da408404d0100d08117401d00c80160008003c409000120b0b2141031103030b0141d800b51003c0c0c182c0c2d00224049443c000c0002d501901c104c43c645814a078110004901843c203540b0b80742c1c1c01501401090703c007508101d5404041103107200510160403004000b1980225219100707900320b44070b600c617070b00704205060b40b4410750b60303c0042089160340c45100001d030310902c3c40c1b8001079242803c50702c0b4000705001030702c0340001800d1418588074984150907400000107008188031440c0c0c0b0780c2c070305e0603039070400880f075040101c078104000c01e8070740404101c080c007031200412443d10030314650000245c86050200009040d45120b500380d58081411048040120a07082100c1034540002e20500c0d15000c000c2c44036029000d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 962423821 1250 962422571 962422597
    0x120804030b250305270a020a290309190308070e06030c09010305091c180509011a03090a0c030813090c090506070809151908010303080a0903021606020a1511 69
    0x41101420b100012411508801c071800241003181c1d030341d843d56136006e4a07090380701300d26a131340020300528071000000d082d100c0c6070b8141f00d030f2034181d080e015010342c0081d0400350248113050070914840703071804480e620148250b58000c6203080540b8001d1031007a000000074410340d0300700103200301110940210b4800e04400c0c20b002c2450b41c0c69880c101c0c10708000c6400980c2280410204680070340c0e105044400c1c00c02044e0b062a17041d5213030000c0c04040c44003402001c1c1c0c40b040e1039042d05c20340322050000d0b590024181c0202d840c0b44035142d5400d030a1043c254400c607070491001c40c011850301109040315000d030850000401c41e80007411801000f00400380310707080c0600400a0039001f80035801003280c104aa010303009490b03000040040e203046500c01048160b1b55501030b0385d010809845100868100c0f601584c40b0080754032801c41d544010b0602d9501181544100182e007991010a403003480c0052803980c02070121012135040c8500c1c20070186200310449450081140461040c42c000e1b9242804458 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 962425071 1250 962423821 962423831
    0x609010e040c03050d02211201061211130602060703090209070f05130f030c06140702060903100c050d0b03061626090705150304020a0e09010204120804030b2503 71
    0x10070024181031243e000944240544d0040307001c10340c2c0014850f02c4280c0302d2000c00c103040540f50b04c140d0590140c030f001c00b5184d62103100100611441880501d28401d50650b00061103480c03008080d031241d01207a0f0b241010035590748104019a014004144d002c4264181030000305810f9000940c01c41e001407072541400a1981e035074106034460350569500400c0d109140c9800c0f9200c3c01c3d166048101440304a40b5900304490200700503204851030030071189644095404e042891f4208921a08250510340d018401c00000e502d103000d01e4040c1c0841c000f025258a81c0d1818201039101c26a6400540740b4041ea004c8414011464010382c0c1900e60000e80d45013240760075580c21108a451040c04404018580701d00d024402001d00124440703040310021641c8a110000210420350b03140401c95002c2e61101d80d4490070403a84465495490b8422101400145015200c640b10021440c1c6c01c5402e03a2901e90100c1c2c24020006034100c01904500c4103050210314906103200034000d0060403400808140d16030f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 962426321 1250 962425071 962425073
    0xa02010516050f0a020907050c030901031e02070c0905060d0b0f0901020c12090a1d0402010c1e0b090601050109051c020f0d0302151501020a140c060c0307110402030609010e04 77
    0x15980e24040c60b03074070600b90f44039044518540c031340c0d60010b20001e0344691b84000200b040386000f001140d40b0441c94001941c102032280c40150001d209130000c20081c041011101d84004000f8130003402c42510503100584080e0a0914802c1281d000401041c020702a400c2c1510115104840581d40501c01341c00360340c01c40d0f94191407140640030307000d0120b481d88203440080b941c0d40d007020098644200107030713180c3c5299950b803224142c0d6096201e080000050b0b8800201e00554030a47d01c006100b402100045e88036180c0b06c900401d040c0100c9000c0e15003486100034024042414490030740100001d20745000364a0400300011784481100820490071140210710b81c003103454031006040c100c0001018064803a0701400c021b51602d4580074001816941e03030300000e1540c0300c0c0ca580c0340e4240e0f10682c000e048841e041e5454409400425044621601c1038040b11080c5070754030401411203250020203192564000d10b40158146070030804584558018030802c003080c1c9460600178112803c120f42c0d40455151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 962427571 1250 962426321 962426347
    0x15050607020a051203040801150e070807020a1b05010908010507080c07140706031a011107060f0e101106100e040803150d0c06090b04050918190f0209180a020105 71
    0x203103901954100d01300340e40e040c044440120140080710400c074024803d5032100c0301c0a040c44400c6020b442c01c502407400101e680280300d03010081e0303c03000030b004482c066201600c0d1848100300b49008084804a2a4018405941d00c010b0341c600502c030540c020f00050a0001014080c1f440040c030303ca00c0b2007008600603080c03064054030752007000220010340f440192a24801801307042000807143c50440110341c0e4a03a15403142e811902c0205055010b000042e00703103c021140341400799100010081a078080c079076180e80ba01601d00c1100101c3e00c80c415511025000d01c0c0c10503400801041038101501010450706051180303160f0301c194018110303030303490352140002d008000c40c025042d0b410049070220304081001c0c0466142c00e880040d10b40c0381f021940ca9100d17003e03d11880c0030340c84c0c00851460204070302c60741003c2c0c500841c3e620b200030b4800c1810110300c448804903425500350303440111000324000b941060b0328a03541005171a403044e80203005620071190342c1c21303103414002d04002d40001c0301450201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 962428821 1250 962427571 962427589
    0x90c0510200313120b040803070903020a0e04051c020c0d0305070f0317010b0705100509071205061506030103020d02010c05030f0c07150e1807021005040b15041505060702 75
    0x1c40460000d00c8400015440396690420441c0301c003e0000014082981c1020081c255802d50344114001140c3e034031a507901d285a00013800030f04c2444a00880400140d540803071600241c4643d0401701c074507240ca414250b20b081000c030081003480d424000500c1c13201d40d0202d0503a00055054074204122201454101e5542c4141d00003c0d116042c1c008206003099401001129005c02c900802c05169807203000303420984c403d070900240580c0c840168040d200307a140d0440e941c03146120007912a010707541c0b421075422000314442125282c01901c1084405000d0700e07500c040d03000c000d0310ba0900315819a0701040e00741c01d03800c0d07010341805405040f0f001082001c004844060408005681e15542482a0696903204602a06140c034602e07030784603d0706601c2240c040310210f100170180f20001e501000d001040e41005020350085005611480403044c030300e8051140560711840c0100f040e40f409104103801c50441c102803601c1141000b2150020141001c40d544c25590211185595206203100081c0404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 962430071 1250 962428821 962428847
    0x2010914010203040b0d0e3906130e1f0303090302040905100204080304030b0c0901090506160b040809090f04051e01021e0319090f12030902120f0f01090c0510 70
    0x11700300080013100d043d8240c01082c200d4000208a403185160804d100c0202a240c0382d9402c18001701410410a2030344504800540d840c024101c149445824810081c14244680102c070750760b64030100744091020185411103406903001d140b0704160341503a030001e120070920301c80a03105d152500c40101c203001091002da055003008000c115910b90313884080b03d0300c80d085440103841e44c0c1d642d1000904102034050880d4000384050b5105501c0e90304090410a0a4000300500c2d00071507000721109000888801c5030b035025038003c4c10031a860b51a21001c205c020040185403031100240c0c8024000000c1c40010385080b04900040c0f03035180d045841c1d04490090203855a007000e9488144982942ca03201c1310300440c09080078101000fa820400d038400002d5450840c001030003002c000c0001c4022402010b445401c944003450040303140c1e1a40d400149998041049901258001c0001c1c104d10341e204210070032003000c1d46c030000e01040503907485013000307010544200f50141078120036286e9200d104908141c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 962431321 1250 962430071 962430089
    0x130224120910060602010e10182a0501050c0a08030604181a060105030408041401090902031504061401020307020d03140f0409182001030f0914060f01030201091401020304 75
    0x5160008180b59500c8098038460880c80c03810a002c2202c0b07206000d911484074900006005070312030415641c00501c811084500150f4820007920009400c4414150141a09c003c0802214211004602d001d00c0705d40e00440c10310004000d10390075900e0100b0000c481903005070460743c495851030b010502070711040c909075103004000c107160010041d001070b131503584880300c1d1001106681c4550041d6074612091785d000c4d100800500081080030f0b01c0c00d041455100c0189131101ba401e603070380d40100c180e80059408900c6140442c080344a18117140c4594002005045200c40071041d040c070010303450b4030820780081d004941401030074040c540940400007940e41180d003007654504556031045c04c1e079006401552f50460804007002800c404010a800001d03402124050403500b1300c503604410034449881c16814540c41d0916004964841d106159000303018a13540340f0700c900d008404c18100341d0003e080f00c2d1025121001400541d038020070440503103220100080c038400030310740149e246001e00d600c0b403561 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 962432571 1250 962431321 962431357
    0xc060e010204120b100611030708071b14030c010801060c020f0f0907020d0e0102060c0d0507020a141b06030417031308040321170703020703030608030a0512130224 72
    0x4c00401c0500d035031080459907281084284c58001c111201203111000c1e483c950700910000d004984050000d04840c1c1c03040c000000010300782240b0b0300300a1420b5001c4640d4412490807480780f0300703007400a010424802d280c014025818400e0241c80300e01080303406030250810010401003500e4819a500440d90700034903c4140c1d10303020800a60710503408141e40c001034442050955254000a1450b006000322032100f403e2603140801b00006102c02000401140b042081c46800318801c800850455038000300904440240215070a2401c80d6840b0014000c80c4200704110229071880d91180b460074225014a560707884503000402061000200a0b0041c400010004200000c2590009014001140f2a100320107248001d480b05106503c0661000c100400000c180380c2c4a54010555a4440e0500150342c1b0303100e4402500d503810008046001c180c00050040c055420400103d6000680f19800303040710120b64041880e076581c01c0540184440501d0904810556131019070f010f0014090303541c20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 962433821 1250 962432571 962432573
    0xc17072601030f05070b09180a2003100602210309031209030a0e040902180c12041a13080d0f23041515120f0b15030c0406060c060e01020412 62
    0x8184040c00f000300c2d883e01c00c1100c00a01c001600e4143c818000006103000300c4100c055003110200301000f13001d200102e54a03003c22b0408988102451441e840ba25285600d030301d425038060403030528540000041d50b10038880189000c0303641000d640c504508601061712608c419402d41c1ca940140020118074240c84401c000d5090070004c09882c504007580c0c0c4d286031005e481002d100484160480103508070078043c509018503880c03001001d801481d0300c0201031070205d40c26841c024020b42a10101c40c0481070f41140c0082c1a180003419821080c09003506640b080150355400052090320b41d4407003040e445102d1f403580c1c540c1c2540500813494a4449074014200080ca1030340151100300c80440b0240068610514802c2c11845a5840010764001c000460390610035a41b8074032543c0381c012602503407000c401038005001d0015003802100b40012104c0b02510401c1054105450200e40c0d501451800710100404c55004200082e01500100005519126480e40c540a803150b50802e040420f0b01c100048 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 962435071 1250 962433821 962433833
    0x41a0601110307060e03130b27010e040b060910050d05060102070f030618060e0f01050a05160309110a060906020c0919150b0415030e0607051b0c031905010c1707260103 74
    0x42040c2e0782450004102180000e0010201c2e4201d403027050024a00411102c910706203540051070b00c03a0000c8c10b460400b0a4000044c0213103018440402c0003880100b402c1103807218a01074650055000d0001d04906420a016070b4108401441b0180032a511040b0f5131414900d501d01c0c00c41e01c160046018400840c0c10743d4032030355804002c80407a1640d07192000185100e051132043c0c50044191410200b04440f20b08400c601620001038191003024400d040ca0155545a902c0c60000381407079141c1e0012145045c001904104042c01d002d401004213404010828145100e00031640e41c0d00c900001e012500e208642103001069040303401c08080000d008a01d00484920520042c5003d81d4240041c511705a001d64982c071003603480030040341c81031041e01c0d03174502d410329040c030200350791411501c001210780c000910300030074030703594900c0c64407908901414040300b805170b0031126605050a8a14040b84003030000710010040c8106e08120719040008580c1612440320101c048502c104031502e961681095 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 962436321 1250 962435071 962435077
    0x1517062d130827010c03050405042417100c0c0f03112b1b020d0f060204090204150e0102060f13060515032a0603060a030506041a0601110307060e03130b 67
    0x44043e0403904514001c10740c1704082141e8010f6050b61441e0074039140c44140801303052043c20b8502c5062030200590359803020340150304010304100b51607030031803110f07074204500b03000c006074500c22a6401c00b0100e600e86904400044005a4000c550003414803003400d0403540190707015080641806500792201910310019003039500d02025549182d000340350381c4026240b00b0b038484e0013000e0203000020340344058a8008072100d0401d000f02d000200400141e680c81049900a40107191195130104003400711009035803c1d1a02c00761141000f40c403103840d8000107561218020600711198411000107511115265034842d5043d91141040c4100c0c06d000b2441e4000d0b094a250f000e000303100f11607611a80c2001c90001d401154012902c0304034801c02070080c0030b001d51001341019008804048000001181081218030a60003603074003d881c08000e100034800c2d40e40c054a018100a9102441c0f0250072000c02201c15195000c40d0008043d11141d001c24154003078000d103207041007402c0c81c1c000340221900c002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 962437571 1250 962436321 962436367
    0xc020604050606030c0a0b0c0a02030d050d0524090702100c170c070c0b0f0405090406050a0e0c2d090108370201121517062d1308 57
    0x80d0344450303483e441407554a600c5d2020301c5502c480408020401c455000005003076001d80e0500707032007641c2081c1e000700c2d10703009411415200185000a0384103100300c06120380307174000560305c0114041c11a001e00f002503042018003042e100707204000105003024020000f10200c44104641400150401e4902900b18845000320380f51a0b46800002844107803003070202d80445034801403881340541000384070450351704283c03560f1030300c803204000100b03003641c0f03000032544201c0c492080403c1c2c0d464002d4002c425030399100e80b4401141e02441e490342040d560700c0c07a6840521310b5040035442c0c218091030365004c025800c80100f40c20480c030070008900780f02c010966040c07044541280740800b000c40b0280035010a0ba85800d40210940106020010761007207010918a07400042e022441c4204007000c180c8610755a40001c48042c07540c10740001640d8203200c080e074082c05035041e0341800b40301ea0500c060801541a0700c050044202000a5072346802e0080c0344118a0300159140d0701c8611182e03060103e4424040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 962438821 1250 962437571 962437573
    0x1a121f060e060f012304080303010b1c0606050405100e0603040f0b0c03090c1302070b07030b10080c0f0304021801030b06040501150207060819091b060f1d01050c010c02060405 77
    0xa0702604002596001d1180d041e95120a0007031070610254051079502c2d407000d07540345c00300300c0044c60310000c00c06540605100c0000c40c1ea00c02c4094559080c41a4000100303e01904184041140b0b94009043d102190010390b9400d05410004001b1074140d104813205540c42600441440309106000380000e2030207201e003a060100d52501c084e82041c9000c01c0300c900c0c12641c0041000c09050070700511a010010403000c0260800354580d036004070b020000c07628040042c0d6a443c03185d10601c4e09a03d003624000d100e05114445080a814521451080b015019558140080401c00310b40f61050f00d080104c2502030b12a40550b100e28010001c800b0940d015445642800c001040a050070a81c13040901580c0e0020126503150050550380702d50002c20954102c1c220303500c2c0300f5502e402c50190001c650b01c5080607604200d0f00f44905110340100790030035010001c000074680416030704808044c00c038152a40c0c110860000d0350004880740d10a202900e4015401c01202011054002642a0050384548 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 962440071 1250 962438821 962438849
    0xf0b0705163c0f02010e0301090501051b0c12130e2a0405060328180b070311031927050709021c02071403040602060a0c02011a121f06 59
    0x40d0102404259980090b020b15407281103440000c418000310646240706041c00980f1180300800a42101c01c159401d071030f945d440d0010400c0070803442c40040411808224064141303100b00c2011070348e41d640c40c4c10710359092800141c4032007c1c039840c9520a0091030a1403105400345003000c4034200e88455102010300070680440b02c184225469000d45081c2e032030250500d41990740d40c80c0c0e0340c00303410109840c91304840c40407040910300305031901400800070280e9501d01031020041c900740d900e640e00203100200b0989014000074001c8000402c4a0f003012031440b551a0601c0c0c000b081c8401864402e50b0900b040100c40440411034440055901c1c2c0d003400b410907a0441503a802d4400183d1141500c0c165000c245402e1503210800554050031105004105403034001680081403895584140c0044016a00c2802000302c0c4030f816020303d4140040d148001c0c8003804045105841c40d20503442c24921516683c07011076250340c0104113403910a9801d05800c0ca49420900365140140054081c850041244c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 962441321 1250 962440071 962440133
    0x3060b030f2d0d05070605061306080a030e030312010605030702010e030a110f0601051507111005031006140a0f0e0d030f2a0f0206070822120f0b070516 67
    0x4124414070581c1901c420341703000d121ba0340360002800020000c035400985000702e40c44084a40c0f10b05409860a28024860302c0f0250074050001003413800110f200e58820029000100301f00710807541115064240517880351a016001e1740900304103920019144000724060791010340c000d04007540d0245080076599860300980c903541e1105002d0040c65013050031041c0e1035580c02072440081100c80c1c000c41c03c03104400544000506024071050183c4000355011041c07154040c80050f841c4010000380c141040360003540300c00c50307086015404c0c01c01d080c0701d5016203950f12070b80a25070842c1c034a03800400340250001c141c90302402c1186009014400200c0000c03c500541031160800200700c141165800b203000100d41c0d480312862040740d4100e0704004144072030303800211350034003400c1d41841c10703002c88415410088030944080d4456000245a40000406201081d4060351450315a50481000e505a54400c0700c2980c1c644036422540c0a520380001090052100d25030131012021a4100f89484460003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 962442571 1250 962441321 962441323
    0x100e060904050d0f02010e10020307080618060f0105040302120f0111252d02040b0f06090d05010b0307120501050703061a091804110a05060f0403060b030f2d 69
    0x2110020296441141e0707243d0303c203024051101207410944000700d1f03802c00d0314402500b401c1c600342c07981148940110601c52510780140c40b456220324241d403804120780c4100b000d07031289600a0201030141c031038000c41c900c0c0ca9118400b141c000d5900030f040402c000013501a41036850010b038818000da5480c1101d08450240741d0b1003110340580a101c0c1003440c0c0401e004881114000d409400c564224418102e64030a4410070146800a60701c0758143c28a14000c2c014132081c0c804501c0c10b00e10601c464404540142d40300380c180c42d60b15034151100314490445240081c0100461100107a0601c9181400142e5400c501c0c0083d406030b1080000344510748a40000b5020f8a049004000000c0304d1440040d40307140d0b01d4000f4001d08a07004291056007560f00b000d004058105482c2a1040c0305d20320304000075824164582002454180c680c1841d0181003000c0c61100d00a901004000030744402a592065804002040070004241d00f07890002005140e00d1001009908c8180d8204c0311000031140310f508 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 962443821 1250 962442571 962442589
    0xc0e04051b01140f0c2e0b0d150603060f1a0d03090e040303060e0411090709050915040603050102190212030108060a05071101091415090d0c1a100e06 66
    0xc0c103841c1c2c90b0310012500b42040803038000c0240303035180600521000c2c05c49202041a08610440440d80c9003148103100d2a88034000109500840250b003810303010480da4442400300c0b0051030308401d078083d003803c80346403010103050160b01c0503007080c2c100001c5000c1040258440d42c0c55101d0a40e14070b808403044410300102451541028020031440c0e0404c004106002c1d03096540300748a4078001610a0304d600041342c517038005072000d5441496a515040a5003031240950b82c1001107420300303200d458544070000f610000000c1c070b1080c0c82c2d081d1440c841c241d500d80390445070245900c40c3c000c1d929008495205c0020b40404031a1800500c11a00e0b8503400741c82080440703040c0c1e1500f4000c1e0401d941c40360300300c1002d4400682480d0130041e048246203602e14080c410220503501c0b40b14000181741035250f0b10341c80d02605226817420808440284640010300190b1040c1c00c070180c0c20040114110350400d4514031220402e24640001504100400c140001c420102551000e200c1007900e501c5134001c0c01040e507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 962445071 1250 962443821 962443873
    0x1060603060503010915091a160801080102090a1406120109050a060608090a0b06221d03041410030603020a120c122307170705040b01050a021203060d0c0e0405 70
    0x200c1c2902107141b403000c1e01d8000da40510f00418214a1034400100782c0c9102406c200c6d00c081101410024803070080d581309030700b2401801c40d60025820a60603200060703861003144105008540d07802c10300303101511b442082d1000444251700c100d0056a50f404210060202110714078452440c0c035002040260155909d20700071400038000305540b110301c0d5180500910b02415043d40040ea07540c941d1010003100440548907184030102160b130400301030399810004244c00e003030942c607002408207002038600701002014a2408882c40120301020910540c02000c0580010390496020b070700110f0300d944002d04d04600740788620100300c42c103035031200308449070360b4440002003814030f00034500b185680851058002e18803034641034400d030b01d5507115140100d010307040000f18540c012590401c46407034140325003240400282000d501e0580d2011009448826413090b6805400c030100c04115161140b60300030440356484051840d149803214484034150000b00e408958074483c9140c0c1241800507086150000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 962446321 1250 962445071 962445083
    0xb0409050a0f051b1806030c07021002010513020402070c0e100609050a0605030105100e09130615030803160203040510080103120c080306011211160b1008031905070b040302010606030605030109 85
    0x83c4c61411085600050759800110700d08000c0341d03d10f0b070f80c1000444c001d20303030089120342d1041244180109180c80c441c040040d64544030422180400711524440b040d54102d400581c0e486040c0307807603130740c03076807141c10242608601d03900300059000f1400c1c1c000e040d640781c1d84070b0644040c0c0e00c008000f4100294001e1000203102840100f140303081444509080702c619081408031b140c20b0201180b540b18007119103020025079400ca004c2032040038840c4260f8200c800400e0b95044d410f548807411a40f002408070428803105d03400c4042d0712482402941d0240600400030131a000e11101c005045010030301050792240c00600c200c0740c0b0303280510f100404071640310311010b04582c0c4000040d00d982c280f4203150314845498404410750440000020113004008580084103541c040c20640e5000030300529440001344c00e50b10510400d0030000954034071080783c0d1b901d07074410750b0b5203c4215410f010f00c480041a40c0210b0b0180000c068043d08980140c1d4050317030b82045440d03980c00c101400c1c2c0f2801c803806030207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 962447571 1250 962446321 962446351
    0xa080604030e181003060e010f05070801050f01031814070b130e0708040c0b090d0c080f06130c03061503020315010612180803100b0711031b031f060b0409050a0f05 72
    0x58030580110081040b280000a041c00c81c04070300d0402d0310b40c10bc0354440022640b50052240b45866005508581003c3c43c0401054040710342c9201c01346041030002d403100d00044d1b00030503e09070030000350001c2c00c2c90b2880181c072900d040e2000c04201d03c075400360401080e00040000c0d0300d00e105030030080c072498018500880180c54580080810f502000fa11f40c0c100b00c020100002180e00d04581400a00100c0c1c000c10000814001c1c03203041200c054812803075095030508210128046034016016a038225800080c045c05c1868458401da40d2680000c0d0980580351040781e07a000240c0840b8122140b0f40c94404079107070110b40d240111891640c60f8002c000308400c11102203440100916030200c8010082410503842d08050b01264000c4002250441c0b8000ca9a2640d0b040078041c1510700340c850044c1c103d18000b20000651a500910344901d000b550324030b0f20617421507031500440001d080f04c80719680d0711510340d01c01c10054001103910000315801c011002d403004646201d110321550708503403d044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 962448821 1250 962447571 962447573
    0x1090c171e0327030705180a0b010e1f0f0203190509030f01020c0a0c0b0313020f010314151207030b0f040309080106090507030b0307080601060e0a080604030e181003 73
    0x5554039803400212898441844680b03d0f9820810904000c0007240440b480e004851000301841d04405800560040011000c20040140c4040032039411900998001c03c1a81c540401202d400d0542c0d003041e9030180c1c11020400c00701c2c181844000c4034100310ba481c04d0004002030f40a0703a5030310030303190240159609070818100c40d0348914080c040114008050721000030690b2202800d90304181e020f1281604000801c4007040500403240b40200a648411030440c40c05031109e80c410410748a01078090405075011215980c0300b41e01050052402c480742c0c54181c00d107086100040000f0240481c0a600707800c030441c0d081c2c0c9000507085d00701c80d44506012480d44d1508441001c84002070012420300080320700c0450740e07242c02c0c060003019203140c00e8001000c3c90001d1004003500c02e0398103024021f4024450a100100b80490902d041d01ca0b14185119403901c52070100b07542c408143d01c0b05c000d90080c541030008050b8400c1f4154640c1d41e04a4803035000103994802041d9400b003c1c2d03801809000320b114100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 962450071 1250 962448821 962448853
    0x120b0312030a0c170a0b0409080c061906081005071808061515031503030412081c0207020a140d06111e16031b14060a06060c0b0c0c0106050604060201090c17 69
    0xf0710700e40001f510129104c5c0e030700d56848205810645c1d032080140c11582c100107c405450213209882071880006000d260301e4a03001a4944000480301d032042038943c8000f94500d8040c03540440503114111045401c5507603031440c96207906054600180d00054140c0300308507450306d01c2295018107051100c4500d140c4448849605035149001c2454150000303200002d10041070407046000340b402038003041d65505810544400a80100c102c00015600c18040000581c6468640030709440414543e4a001c80980d00007410818403034200038402810810280410b10711807002d841d00402041800c8454030b07124905d00303001e00920161002000c42070b2140400b0a100f1561115004003c2c4c0b80403090341c07000d0301c481c3c46100381c0e01800c40075588814240412080709100d241d008045c00d10f0300c021142115a601e019200c00548603400044010807500d901000c01c0d403020f001410000e101130396465032410701a000e004200f600340c403000f80c000b80c00076402070f130140d04006003084100a080810707a058029 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 962451321 1250 962450071 962450081
    0xc0c131521050604050f1207050312060a0f14090117100f020d0c080906070212040e04020604050603040c090b1e01030c02010b0a0605043201120b0312030a0c170a 71
    0x203600c0c40c1000c0d007401c1c8041041441441c1c01036003d8030182140c000c50140c0c60f0300d00036880e4114410084200031b0200442e201005484461f0040c1c2c134182ea240d00c9840010b40c0210aa0b04810541c144400000440d00343c0000c01a0300b004003a88c905e41540c0c5d0780c070701c003010032540007e50b029560461a04a00381541035448810540784408005003400441c9564104444003210b1144c00b1039646814002318020400c035550384015944010282a03100b020940d6050145100340404000c0000100e411507407640309640250070050031041d202e10345414410b03004002403050001c6079242c0080c1e140a8180542200d003148089150242c2c00728444c801180281700c0203c0c018115540c6030304000159032460700f140d0080c1204c0e66202e071101e0134054507007018840c40354208268124044269608c1c031804104208541c07090071b154001c010b0080b002c1c3d000d060740000b01756050003010700c44185000500091405442d00d000c040009036002c044c2a10b0002340c540041e0818101c080011b51512015000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 962452571 1250 962451321 962451359
    0xa123f170c0a170421180b09012019052a1309030e2e030c020d03020403110d0203030f030108071d090604170702030304030807060e071d0406110c0c1315 67
    0xc40c841c6d404118805c41e0b09405180c1201148150000700c00c001507034440f805142e0b1070489047c102d180307034841d003c00f07070b40d83c000105000403002041148018000e061011000041780e10b0307041c13aa500148402c2844d98044001e81074824070001813a8508542e061155144041e459140c10402d4151401007104506210103001900005900040c03002c1c24062a0145c03d21442c0d1000b1075a40744056020703041110f0603c0d50400c040c0306110400c00310300c1c01541c0e45c006030410b82d2480201142400030038194843d0010001a2410000c00082d0b014000624602101c00c020b002d1200c0c5c4031050860a00780b40c05603a14001d030ba1050380401c0c04514108000700d82240c0000b45686460b01540c0400c0c01c40d0001d600503200c002d80410600d00344559030081d00b005c0e44403d809040790506150306a142c20510842d007202803508080040c003008003c0d8000d41c626840204043c1e10741c101c80c0358069894400800550081d800c820329a24018181d0041c1c0c440305004021182ca01e50070410ba280e500028030380 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 962453821 1250 962452571 962452577
    0x10f110d18090905010c030b06091e010e0a170d14032e08030912010902060a0f020a0209010b130f080703021c020a123f170c0a170421 59
    0x1000580103601e485403c1c0000d1080001260010300710320b000c0c00f11034030101d031903001e0f080030007140090350340d08d030300420107068010950207411041c8401254000d05c416009504045134080110303400f0603074026000d595801e8004c0307540498100e60100d0f00402e41104214410400b80045280f02e20f804103440d08261070f030101606c840e112200706801c1c10041380d001c548c107030700005090111400d0982c0f00047e42c3c130440000307004000c40c1d41d001c0740c0709100b481030100810403014000030303035140b003407155410b4660000c01a00565031941c440d548140d100b81104d09000a0004d00010600751241c2444111500c20300a054044d195400b44030030380c01c038070241d041000122880d0200603030391406903401400c0c2c000f4541c0c8100380c2d1450407913801c0340c4201c61010084507141c0611109040340e00c00d101e6001000502d0700390101c00001c103884c0c207404a901c0000d42d0a0712810801900124005007000c480d9985d1801421882039841000c10310055401600d0b684111358021201912500f51300c00c070716424a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 962455071 1250 962453821 962453867
    0x101a0708091c02060f09010305060402040311011409040903050d050a05040b15220203010302010207140d060b04150816090506061207090e15090c120a0e030c0f0606010f110d 76
    0x3500065040c0d12000743c5c122199030100d0390707000c19645071281561212040d83c00b1803030142140c44e040e070302003607524a041c1041140c4a02940c1c044148081d00c121000280042c02800d00030315025006811040b00051803900e0100050111b9249001c0e0f58043e51f00321840030791036210115011182c00c051310b21a5009510484031020078030503092840040b5588841c011b8981d411480020700384401648903503ea1401c24848040d0340ea106154850499840400010845110781c049006002c0c0f0b820800030014000030001103c1a0105542c3c20603c00c0103040c02c400c40d01c0b0700040d0100c0c0c4013070b511190050000e00084203604100c44a55810400034184400305507030700c0b00d8400389104100d03030a911107411582c00401c6400c0c1052041d8024180e42d000701d00303040342c0031104003241d10b006140098003926400c1c000030684052044910544641040e15040000960003951350301066401c00e0004d01c8501e00148030702e10582d41960112039010281c114043c0c2d001d800c44200c54858424188442e00f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 962456321 1250 962455071 962455073
    0x50411010f030216050105010f080610140d0609060b040b0406060210020705030909040c15050901020a02041109030712021807020d0503150d0b0906010b0a02070b1c05101a0708091c 79
    0x2080000061145c40081025030402c1040c0a1900d16a40020f210750700950922032214440c0c078115081c1c480100c003207003518450a0016280914945000d17110901c1c0003503450510070302d5005018080b07400d43d0b00b403000a00c3ca40510045480c0c0b40300d400010f81080c6000e131207482d555001042c8450061045078207051140d00001d01d064400c0d18225058403807030f0b00400013901e6010f6426810042400c000b81440391385800030f5259907608000a22965035481d01701c0e010100070054940311040941141c05079621441c5040c4010514074059128000c0b0300380c0c00c1c00da11490303a425489682c95a014110100c01a0015100c6420180c02005552038440a21005440d5050f1844241c3d001e8034141c0780b40d080031340700c060030702d10183c0004e42c01d8a02040348044a90b00007558404480300909101d65801a44114954003242c02c40105845070030541800542444000d401c0305a40d5824800a50341584d4010034901c1d1040c06002800707200103210401d42c80c030300141e401c008510710b025103040b14155 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 962457571 1250 962456321 962456347
    0x3160e0f041104030c061119030903030c02040609051303030f05013005060f042f0d1b0807030c060201020418020a050c0f1c08091228030204090f050411010f0302 71
    0x1964001c10b000488035190f44000401c00c01076001035036448000d244610b81c4542780103082c000300380805824841700030405130454466500c03071001011100c50411560a0102c8841482042c1c2c0f002600060f0501e0078106541145104141c100d44486100100c80303281ca4070582ea030328000496500e01048444810404a4424032010348200c224005011f281e00d070600d0100b448500300441c035043c0021030380248a10548401c1904481d02d0200c44001c0f60a4807032500011202c8443c00429600b070b405074001a03c1c00700000c0c1e0720b00740da00c9925520720380f03a1038180c100d00300e000b6840f5412a2a160f0244900151003660041081102d80d14080d450300510150861400c451400b2403651035000c2400a000c280b010800340d4185000c0d85811078007410110034081c2e840c0d103100b51101d80f0420020b02c10001801c400d01c81c000200c1c2032400301903d4114410040c00a401c580f0a40704002d0800f00b00044060b0b8038030805100b15403048101490f00143c100451b0111103c041d15000d059080140540001e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 962458821 1250 962457571 962457593
    0xd0504080306120c090106200715020114070c06360203011a0102151005130603031b080711030115030f11030c03060a0911100503160e0f04110403 64
    0xc080d00c032040e5a8100002070000c403034110880b8034000c1e00030741c0003048550382d03030703c52141121a41c1c80d14840041d26402011030f403c0c1182000b0300e0b1072080701000210f148050a6861b0081d246030001c2100c85000c07000807450b1282200c0c4040020351a060300c8000400070ba10003401140070181e440c03400508a04130281c500a40c070700307000c20f183e103200c10082185000d0003031110345985045c008100b0240b910010756150b00c2c00c03041601c56510600040c00e0101801c5202e801850018102c448600c0300c031215030700404045c0815000264820401105c80401d0711540315002e600c4280c5074a4022031341c6940000c0c15030150280c0c0c0c15504c4428601c00c0c602c1001c10500034600a07039040261495500d0300642ca6282030b603049000c1e03080109082c1342030398007180e11035110a01031804200a04585851170310382d10440c0030a6440505080f00c040091b5002010754814161880c101c083d0301c03000c0609442c11501c1d00c3d025940711180b89641c40050805800c880341c18140c2c00d440c90f04081d00c80c0e0740d00640037 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 962460071 1250 962458821 962458823
    0x1092310060909121b060902121c1d062d0310050a08060106052505100b03210a0e030a080a18060819051f03061d030c1c050d0504 57
    0x103601c0360307002020300414480026404130301d400d0002d0741d90080c0520072481501004042c100c031760388185000c1035454450b540c40a181180040c0e6000c0701d042d43c01100d04030144824074000400c80c1140b41e41c8144180c01942c2035100017081b5a00308002e48844104d0400c070000000308241002080022082000d006140130324100c3c10f4400000303040c4014082483e800d64485032541e4007441c010003400e50403038222040780d40300800e8014a602c000c035202500c0300030088001c1c424030035001d1100040c4129403044032490803c9058500f014207180c00503141c00751754000c801a80400304491030300c00780038041c0e502280c9000b4055507000092a1250700450300481d0301e400c0842c80c000440801040d0220010f0054040c50800886a040c442600011040184c4041c0441076481002c4dd00b42c40c1c40e0700c06d6001c940c82102005a000d902e0345020b002900100d10105100042003400d070142c9031001c01558a8100c104000f04041e000c6200984d8040d09282c2c04181408400c01c100b010b412824001d091182d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 962461321 1250 962460071 962460089
    0xb0a08030d1103010b0403060b060708030408090405070e0f010f170a020304050d05030c04090b0d0204020c0c010905180604091b0b090a12050a030e01030b0418140109231006 76
    0x60100041e020082e20844034401c0345802d4100014800c60344103406a805880d0490b500140d10342000700810800e100359603000d07250300004004c000400088400900341030b03074155400c2c001e0751074034181911801c0d040702c3d09580c03140c032094200216510814405c1c030100018503004c59a03003408a070790400d104055130040d205580000c208018451704118040c080000341c58000d10f585046041001c2a00407030007040c43c019290304804039184d8075000c030b98100070b40040086642d41400f035022070b80d4404d0901418007003501000b0024841c98001c00310310000301c541c42280150362318003080200428034234200321a03000c2c0605402da40d4502101d40c1c10060800300b1007865444d0b03e8007003000b10100042e80f0521a031604070f04481c00285001c02c8040500c1e92504241040c0946540140c0140030fa070f00455070020700c1d200301c60310b007840405040c0354000e01840d10105807261031142c00b4240c7e450544050300e6242c0049401c1c0c00003000e42040e210314840c0c50300b55800b0409541c1101e007030701e0240d130202c402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 962462571 1250 962461321 962461327
    0x1219090f1407030507062f0c010e06090a05130608010212010f08160b090a051c110d0203070b071a040b071101060303140d06080706090315090206040e0405010b0a0803 73
    0x10460388502001c0c03810400801401c42c64610707607929640b000680921000c100c420311440c003041c2d280103007501e03c1d11001e1036441e4800240c40c10380c6948601030900300d40061105010310101d4200a001c440980b00050b10b900d40283c244400e10108819031903c01502e00d640b40000104040c003803001e09616809005400d00c1945030498555418202d6004152941c201809058040a5001c280d0044450703c241c11900c400030103001a249070941d83c13000780c1100c1d60b0101132018031000300304000c0042c4949003034a954241034040c4024180f80750002505580b00303400520002c010400541a0980310b4168000251070200c85c40300e5010742594115140304500082c0721815070404141d1010305050f200800401d451510010010034504582d03190710031000415040c8003105400110191442030b040340c03021a0b071200002c0205150b84010303a984545952007030300201041c000c0714084c80d00104103604150400d940c1c40e0001401520071213582d9640c20b071000241c3c54002034407009001940245803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 962463821 1250 962462571 962462573
    0x706090c030c14060703110c18070914030312042405190506130b0d081b0d140315060c1005060f101b030201021c06031106030105061219090f 62
    0xb00082460b003080c0c0c0b14120f802d500100035110401aa0903a90705443d20240c80044500b40d51300b0410a481c16039041050080051041c0c586066954084d41041e51141502c0e07039074003540006243e0f41c4041c5e542c150002c203e020b080380c0d50f05242070740040c040d24148840c01540582e10484003040516888029181c604010040312400b003103000116100d00c00b07000030310705900001d204400a60407032241940d075400518072612840c10302c841c00e560101c6d00c540d03070b403442c5c4d9a4003000c06882c0381d10540c0c80c4502c040c0f02405511590111441c80c2c100d926280c01c540360050324404048004100a13004507081c410300c04840c1d4108450031001d0305640f40090b041c20041c0c1071010760751007808160702034200d5804019a0a40c450860140e0201700c14990b01d00702010b01e0104e02912500f154181110042651003245650300c0d84114101d81c4a8800c0032400c09910043c4079040c00300340304080e0320078000e0101c0d601030002c819441e0f5008001c501e0b07040704184880c089400721203c0030b50070f48026140a81c524 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 962465071 1250 962463821 962463833
    0x601080a021c030819060b120103021507022101110a03020a201915020304050f1005040c0b0304110303030a0f0f0501152601120b100e06150706090c03 66
    0x2000d1003101d99080d0b11007002524083c101e61009002031107045080240700704903450541c000006861200b0641e5510b1440040d0b00640d04800e0005900c52204a410350354280520400c0b01c2d01603501400d284060502c2c0581d025100607085400052552103842800f04141d1a030024000040d6940700140c0701c458000006014200e201510000710a252142418a04002a840684080144100707080300d940f8940036040002c401d40000e01c0c1e90020041c04104880413a603003080d070404108503200c046052000005a540540b009050403000e403e007486080e8503d0001e590090088010011442056000c83c2c5543e0003240c1a1003125075581100420702d20901500d0f00142c01c00c001400154100341070881c0c244010612001840001c1010200c032204820a403c4001c405040c039915643e52400203440840c1e400404a070b560050034005503c0c034004816210585880500200c07040d07071200140040c124054200d09a092000c0c80084002289400344a405030302c943c800d441c02500d145045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 962466321 1250 962465071 962465089
    0xd0f1b09020d18050c04020f09060403080304172502030f06011e24300516020316020f130513110102070b0d11090907020a02030d0903030203030115110601080a02 71
    0xc1d5190403e11690b01001c034a0004501800c0b0f0800c5800680e1360307a0b404042110741c896812495008800070138008144030007074010794844c501614103285003101c001d4100f100381c4074000d0b6070000c4003070100c0740b004c0704003c1c0d603c80d031042c51000c0d0440b0410388401c14243d01d4042c00364062002d031105410514030030611060500010404101c11815400700b140d60f01d04036054003901d034410040e9a9510300b07451601d2014503105052102000800d4040f50034115000d4070003126001710f40316000550080302c5100104880301080c407880713840146d231615400c20a64130001290309138444807a0341450070304e2a1030300c251805010824640d80f0340f41c2041c504184451688100350341950441102002421958411602c00c424407d00004584620742040c10b440d005132072141d03070014444800c105180c0d4000908a00b954001c40c1100d140c0c0d0041082180c00c00382900006005810520040050501204003070111502604226140c004c1e420303e8035180003401d91082c0c401c0d43c084526403055003425510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 962467571 1250 962466321 962466341
    0x12040203011a0105121003020d080d050105011706280e090d0c08031f09020d140f19092d030909290a0f18050a0b0d0f1b09020d 56
    0x800c980100b05000007a00d0382c05940070980b0703100c964100042c900c00030624410061680188182911042400c2481068101c10f01c0f4400700e5151100200c1d0035802411000d61010504140641a540d104103110810f00012850008051405801c184a0040c1c04101015242d404240f0506241c0400304516001107244400107005405030f010000c1500346044950100d01104a0a0501203880034a17580b00a181c0c080030304248086071001c1c940c02c041e0040d0340c1d070b821420348080fa03503212404a07000b03450007a6480c00d40203c2d44400403008040a070000d40c0443c0c040c601014802442c000c019401d8031140d40040c034020003c2e4010350400da0009920006000d41c0c400400001e10f80c007803201608402c00036002010840c003401c1071415601c2407031807170181484e02104900176944101d0300b8240081184450751403030400000400b100305038400c000700070704018400403156240b83c507526103038a01c4440984802545040070060710104406c3c0c8002003042c1500141c0d6680b80030142d030704842d100b002c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 962468821 1250 962467571 962467601
    0x30d18050a02090c070b0c030f090c0f0d02010c020a08060103021302121503011508030309010e030903030f1309060806061309030923090115030630080f1204020301 72
    0x10041011550005410140302c2e41a2281c08054442d251000100c0c00f4020300185400480307010012103420b13080140d4082c1c000c0140412a584400c021152600028042c04e81c0005095006210300d160441c1810b410f00e0040c1481401c010b42500469000e81d01c0d60000102a48210010411401c00c7e58011001031a090030031400d00d034009604813007410000c1e080e03000f425119580c2004a0383c4c01e40c80421f102c1e8600000070360055461207a10307207d4100725002600c0754601045101c8070407001c000c94850480c0103025610302030359001d818405810400d40ca4141000500e00490150814803c000c090300303101004007030601d4407000304500d250070300021442c6541040c540e84006038100000c442070344d0740c10060100c80361441e04244440b00d00c0d103440030b038805800000003402d9002c041a401e84914207903000e001c2c494903181c400c0c0074141c10030a50f8860002001d10800b8103424400d541031110700c580361803490141a069a080280c010980c0c0b0001c0800180c103110840c54244502441986400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 962470071 1250 962468821 962468861
    0x30506091e0d050d0e0307200a06090e070e10020c0a140d0f03031b08100b0306131503020d031101270209060d1b09050c031003141e030d 60
    0x50101d80d1035803070400800d002d0010201d0107040542e001e070424200c0c0e4a00d001101d445d000075081031300c138102c0c1c3c00d914a000d41c06c48941a912508016500d002550110349922891500d4004030412510005006e00104030303088241603407903a125000304101110750383c01040f292242c402049584222540801038104020070304104513118107286800715a041512442006034504094010741645080842c12841c551001c500700c2c0c1c1c11401150040c1c0c030450561030707030548440c16a0f480384803d036145a40700000d10350503003116840350402603020456400c0392041699030fa001c01c940f642215802c9000c1380c000030400c1802042403207004500100c00c00d0a40c03451040c25100242001d403000040d00450100c0002459521400310790040d10f43d000d1749444a0843c4001030400c003440d01d001d800e0b00f2609283c0490b072840560780a43e80900141c00c200c0c4c0c9003d24650754100444118895407000c1c1c02070800c1d070311945000070031554040014030095a510f020050382d0302d04031341c1e03200d00c170000e680041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 962471321 1250 962470071 962470123
    0xf060c030912140607020a0302010515030a02060a03061806053307050a020603070807020d03050708010e07121109041512060c111b01030e0c031b0604050a03050609 72
    0x104401e03046490310040c900c10407155040185030040500d2419425205020520244e25030020344428014000d500030006604c503032900c203003101d1035402d260780e26a0010003820007515018000b07191022940c200003400381d82d940175821081c0c108440e844030035030f550203040000b810021441c8214104001140c03800820398607524040044c407558440750040085400000c00c40100b01032440c0780d400030150307510b91604c100d00414440303080351040c006000c1e9020003120700c4c0c024050140900e6154980c6072040e82407900071102d0501c000d00210400011a413112075205140c450840303180c90f00680e003580d914540c4180400d17542d40a00c07002c00424141010008d80340c0321614045810351107400130404503c0b416085402c82196103441120380075210207c4003c111507a0201403c11080e2003e00c01c00302e41d40f540c142c42e03444101000d909034002440800703044241c070043c0d005000c0002d10842c140f82d2668040b07001c000300d5030411502d03580941c0030b00106140410803000404108081e054001450b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 962472571 1250 962471321 962471327
    0xf03030807020f10270b040c080706020607080601050706090b010e071b12030b0306010f03050d081915080312100b0a021906140c030a0c030510120f06090503040f060c03 74
    0x80c4c04d07024038459a807101602691060641c0d0808454031411156000c101c481c20210030f2040156001c480842c0554000196001d000c90080100d480d6034024007055520708606960007a0000d0030070b0304110080000000140f02d40c4a24446035000e04401d8a103513042000b6410b1a01e009000300060141d00c01000d4000c181001c140705c0c0c0e0079407120000d40419210030701039002d401c0382294994580034010001c038594882c0c03205842100d010380201e450300008040191800381c000d8418294540c802c01c03d01c1000c25041e046030f0040400700702c858901c10380d01c0005c5411b41d00031002c0d5424030107094043c08a01c4c00030800510281190310042d51901e0a411006076445111052070f43c48144042090700906c0402d600200e900201000c14200c01d14014000c0c4299500840b480d180c0076141089241200c1c0c480d21135184680c5400c280380741860304192151f4085810810116941118012284001502030081c072882d188950001c0d82c541e410207092507600c1c070f0f1a40100c4208034003103c01e500841e0b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 962473821 1250 962472571 962472583
    0x901090212180d110304030507121a0408030708041b0621060f0314030408010203070e01020f0a0b22060213050a0e060109060813020a06020d0e04021602010302030c070b010f03030807020f 82
    0xc81d505018007912003481c0505d0441c01513500103010750103684000a030350708808001481203441005040c5041803101e8141c82c0c4080c0598002c2c2c47d180003400000d011310b015079401c9400a0003081c4103049101104d43e4000200416000707200040c1800d418408540b20305011940020001c3e030081c4442c60901007040c03101416848051709003070084020f40010441070041390301402c5400c00956584c41c1410002d0011a064107416005101d4002c1401c180d56020401c0d02c9041d60003c40e0410584030010f00c0f0040c1e800d0301d48181800081d01c3d03034400000b14584014030490980c00c00f0159482d20f441c00304030448002c0d9100c05110b5406104102e00f681e800f80045003916418181143d481d140e0000a0f0307411100168003d4201c1c001c0c10021a609800149807100c44855560301001d180c064010300c003ea008030071000700c00c040110b86020042d8041c0e0040d40d4402c280c00d51a6007805116243c0119040c17081e0b01040303c000c03031400180140343d400701c502a840070380c038001400c3c0d400c01c0c00c032040e50b900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 962475071 1250 962473821 962473843
    0x150b04050105150f0c0703050618160603020c01060504090b0108011d060412090305240a06030302100b0609130c02010c0e030c041d030f0409061205061f05090109021218 74
    0xd030f00011180c0e2030386501800c0d541071803550000c689400391240f602582d070700c800340c80014142102c4000d412082c1030010b401a200000024041255032501000703030081e4115018069555407107040114543c1c80e0740c41603401c0d42e4010606414554541683d140c210b4220480f0414a0482c0c00c1c0c4041c005d113800a40a81c00a512411b8240c10000f800401c841c1a083c0c1d800040039800b0300c108503d10900004503c610031814200b40c000547c5030b2444400072030380c00e0320009015800076141c11030045480d501102000b103000d00041d103031840f1030000800064040e00042e40082d61a100049055030900c5424000c92150030710100ac025000000303666403c114500c280310f00d4540864550b10118444940f07c49891901180d449252246007414190001e000b0b032409946440c5c0001164401980080701054101010303721580b2040c100c0560640c5118901c1c0030541d00b1080000c01f40c9034030600314000c058901006840f00301c0c900071040f0b50f041c007508120b0603080803001c542590070003180301380400e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 962476321 1250 962475071 962475109
    0x1d01091209080d08220609021e0d02041a04061d0903040302011202160602160516060c1502160c081605060405010c03020a0203100c1b080f03071704150b04050105 71
    0x1651a5000d09217007001c070482c440107801a4013401c008100ca50f40108281d94800c513001a0203070740029100d581d0018900c200c9911921810565015003003640c4000b020b0800c0600c03004202460300d0108017036030029803201d01a503108000300e4040202000003141c0042c20711001d0351401d851900020240100c600c6c80b05a1242c0c00240b0030000130f4550030f1901c2c00e07075109409544609211003051041e036100b10041e140ca0060080b038044007801411840c00380c2c8c44039100c010804989072100029010b8920207207800c2030342081112643d40b94a000441e4580c46000103010145c10300405a041c424000000d4040c1e0a13958002e1041340d0310001600c09880080c640802e0f01c0d0381c40e09049181030200200030303426000d51100c049000c08035400100e4462420b8170344105041c43e10003da00e121004440241000c1c405010010104030312783d00941c2c115655160500c81501004084c004c0c0030410740341116481650035100f03540ea80d83d40600132400344100c80c10030840d890031010481035030303289186c00c4013 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 962477571 1250 962476321 962476337
    0x9070306140618041515030e03030c070c080708010906060e28020706051003020418150c1103120a05090304050a05090402120d0804060b100f121d01091209080d 70
    0x32105a25080300e00000c4010001d10403ca41d0100f070103200b20090107a08428046d980d84e441c00c56000e40101d24401d8500750003503195070380d11b100510030b50300848411a01c00c200c3d043d00140802d0100b0010f4081d000719000068a4031f03c61600b00c044466030f6100401c102d4595080040d0354030f05604100da0703803030004000412005550820300080c8201600101014680380500024040346148070703003170301c5c400d440030007200c42025100500ca0320f446000070803051004e8510314110415402011312444070382003198034040c007020b03514110f4000003030320804000907004200c541c000c03d0141c15044a89100514905400c00c00400c039050003501406000f124104007250031516104a130625040c0308006541c44031889850050030a881620309444031401e2005003030707441c034110244008d07861580c0c444c54000180c00750141c400d140ea00d012512200d03500c0704194001c030800f0610b0745002c48445d0001030b10344124038101144200c1103081d070703040041c098020700c03880400081c0320b010000a8105006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 962478821 1250 962477571 962477587
    0x2070e04022d3102030417091302030903090a0f0b040603021c0216200d0201030504020f0a09090c12032007030510090b061914060d0515090703061406 66
    0x220360900e0b240d8640142010004000c0312486403030b095030040181403000b000006901e80c03541079003c1614054510448200360000c00c8480c0c400030064404050415003d62951002d4001207800484035000742d40c10000f801800740c40c051003100090482e804080141504254117a01c0b2406140100818076500180200d0040088040c50a500850400a5607a0444010b135170004100010040315605458480061042c0d0510260402107001800700309032000141c00440182c0340c05032059802c0006103c120900b9165428940081c090f2200049a0004503143c540b8541c07007158440610804403044003000664017048014000f40650412603c07046501960381c2800c003642e000a080c1d2080c90060744195100d034114020305401410108800e41d5818240034918101c01012a4043c05071001031150b51284081074800c804080c01c06814812070f190244111402618401041d00340c0002d21401c40c03501110003540702e00980ba06102d203e18010342080580d0804180500c14000070070401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 962480071 1250 962478821 962478889
    0xc150504111905100f0219050d08040318080f0c01080402060301060825081005100210020a0908151518131514010513020c0303040f05010b030f060702070e0402 70
    0x100c003800000700344d898922a090750107409045240807150141c040c1043d0314070030261904020a86a80003c040d10718001e12400403291044002c0c0f048051184004020840b40f00c1c103030000d400342000c0c2008118005030300018921b0b140c5a40d1515040003a048108001238032150144c90440f592800c045160781c80d4031001c4038103044d2184071400ca0f84099903001414552008000d4007581517689c1004105407030b035090108641c54031107140050380c4282000d000355071013940181840c0b001480d01c08080c82e02c80369044d08000000c030210101800d150240840b450344211a107414a40803614022a000090140c1601c0320004050301d64545040301c40400380b0011551010001d8020402001140301c0d49840d10202502030240074081c0c003401654161318044c42c400c40d0000303030303200009605540e19030781d810420b0700d02e80c082102c40e0354036a81d0187c0c3c2a24200680d81c2c9910b0a48054281d0746001d007402840d0800a510128a2141d9001071101603294900022481d0b0343c440780050101c1003d504030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 962481321 1250 962480071 962480119
    0xf030717010603033509160602011e1e0e0109080703110705040e0c09040f05191a0105060901030e010b090705090411041a1c020403030c15050411 64
    0x85044030355255150624004107601210036070b88039072120168401c04030042c032501074058a60070142c00e0f261843d113107501ca030301c80050761081c009011101c1c00c1442880000301003200c0c0d44000c0140c0c0d150200c2074040103425a8540c01503038108802c00041211100c2c08a41070303d00030640301225030394404c4002606c000c0d0044124540c204941c079a80328040c0c60000d01e900a9110145154016081c01244bc5d180c18004c410108100310b005010490031030042100c00c0c04050030441d0b040c40080c1400380050341c00c1c0502a80150050701038078008205003040720440ba505c80c0d040e060035800c5030060003242e42d050300381c0360480428030380080d074a0107402070103005000058840e070b0301c071140c40100119294410b00404610b402900c061206880e00b880149a80c001c90140741600781c2401b504500c182d900d100a41456100785001c28806c10a058004040b40d220341c0096000511601d44030050240000a2141c07442090404000da07180503211820314240280c04075204003070300402000107030484510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 962482571 1250 962481321 962481329
    0x8071703040b011d091e07090608010c11030c0709020a0e0a2c10120f0b090c0109140108070503090109240b0108070c030c1403360d020f0307 62
    0x10390301e06060511510488092043c031400d904104d258944a8100c81805802404528002c05120300341e44195003403001e131400945d0041c40780510000c0c4030500c40c020038005000c08000055950308000005280a85101841060394003c1042030304440e0700150702000c44525500042e05c60304000002c5a448295950107544074403001004916500700d925680100600018400c03080000404080860b8404880c000319441074201e04003d07603001c41c401c3c480c0c950301c142000c42d01c0803a00e0b81c0340d070f100380001e48206030315500036a0a4450b5580003030a00c0c019100c414041042c070800240000c0a000c0c0007007044003007090100104034411007d401c11a00190b100040d007680c003182800b04c1221401d00c0170700d2002c0350705001c20b0110340d501805a190150b603003070343d41c801101c01036142a140c648070020b00700e9030030742d02034081103110b001400940404440758280641141400960314a0044214207200f007000d100341c042c60340c0ea902c1402d000c4200c1da0550340300801002100c00603040882c00c0d40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 962483821 1250 962482571 962482613
    0x305010c180b2b2f0711031f090c17030a030b0a080a080d0f0605090103060b1f080a05010f181d0304031a0106020105190b0a0503031b0111160807 64
    0x41196429032154110303440e0100416240300c07812007001d802c04024200740c540c0b6003213610100844030124280c1400c00440c21406022a8035101245803201e46003288406090055a030740c44005007041444141c02c1d00401c911030380d242c444a0f080c08100c3c1ca0b0300c29814070000f895620940d83d0301c1d94881c004a640206040320564081d01d815081000c10703030307015508102c0140e1411840f90580f030028400c9505446000c0c0481b40070380c0c02c40c3d503280018059040415400300e60035a004980500a4138021240201035803045d20138100b211041e029208103070402c2450ae140c00c402071004d401c102c40c0c0400342241c00ca0012801001c0007030106a00b5211015a0305c86020001e004020321845c4076081304a20803103c8401c240703a0381c03036504a003200c1d81510007030b900e03420210220079203000c0b81c3c203c1c00d5000383c014404000389640c1d0b40000d00d190f0203c5a114030010f4030000d0f03007603003450a12452002c10302084280e4a003014514007401201883c10b002000d580003c1400303403e020340440745180d4000018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 962485071 1250 962483821 962483887
    0x17070201050a200303010807061b24020c0615010f0329061e07141504060902030118060c0314040b010509100905010605040302120c010e150c010203100305010c180b 72
    0x21f81c9050300e5480901030140803c0c4075824403007900c031440c2004036100303800c040c45001113070107040285040c1c01d143c880f510301c6940901c9070703c0c1700440520841c0e000301d0319130b1084d0a00145000024100c1d015000a180506140c1800840c100302000d20440c14036101c40c03604040020f506001590318040c88583d0305511024580940c29101148002c081d65070040400a00c07440320f5110655403501201100490b44072031401107030004440d500460000c42c4001c0000c160400d042d4010050400c0781c000075030301c10f0f440e01d50888030743e909845107420416101c903802103540780540325404c4200d0113100d2280100d082c1000141c2111401c107075040a02641c001c10b01130b5582d555002055504240003d03072184950b9005102584000903a81d00e00a0041e1544076030100340104000c0c0e00689003061140d1401c04001099204c2028402944142c1c400c1c0c081241150442c00e0080c211012110000103101219852124103140c07030141b00100c1d0290080e042da5405034125810b03500b81400a0390140c021a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 962486321 1250 962485071 962485079
    0x20c0303010801050411150427092301090f110a0305070e0901112b020903010c05190807080a0f15030b090c0301060b27190317070201050a20030301 65
    0x40d08185d0185024a54038110010860104003070301c810101d10003d0440100b000b0005100301340138100c0c0340c214092550b14012001c41d401803d40380415012104030f0b05580070340b004c031165419403010040084e0001c0182500c80d42d40c200306004c100e4806800c2810030f05500000e03a540d80191009154000165140b095a07500c28455030f1320140c0c3c0a91181d402c050303400d07241e5000708081d40c00030b00352441c0504030703140c414a805c60313020100004808a56004c00000b001e80d02c09001d0040d2940e1507030f580c0380e5911120712401306400082d406100803c8140d0b002e101d9601c3d03000110b160050f0741c00c4400203401c0c0791452580010001c401109055181c024000800d00501a00b0b0f1803090300e40c0340c19982e03143d5210080608071401400307210707030100d02841007c14a4110740117061070050803a1403c50302e07480007000940c4403540b181185460f4400e4800520402200c075982e1405000d04545d66030030201e0a034006415405a0300150303080003c81007072030340210f143e81003442010010703400b40ea5072135842d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 962487571 1250 962486321 962486323
    0xd1704030b0a1b0806060703140a021b090f0103080c0703120e03010b0a0303021009110409050d1205061309050c130b011b0b0109050921130504090203071701020c03030108 75
    0x2c4507a821528503204105500515512180c0180c18480d1340d03800050750b0703241c10000e007904000801d5003000100e941c3d030400740a4800c0142003a104980007007019448601c0703e1000480b02212140c0228942c01c1440f5003100e03000b144a0540303a00c041c1c600c0d107070f05042c2e11852504119501c058000e000c207840c110304461b0040003400081000b40d0080c424030101b001405060841880000e00691042100b0341c5d1003030b038940c0f191508038881d80301d100d842c000010002d0300795103000c001568180c05c40d401c0d907015aa04000f0751008540d098406104528051000a00a00e50071182261a40d141c510750400c0210501107511204c01c020016560602104030800c01000b52554003404181107e403c0d48003403454205400c802a40704542c41030701c0e070034141031902626010701040c4441c4a01d40740701c48000c40c0c8481d43c280c2d448602101a0f00c8a42c005802071186c01254401401549801c46140160303c0200380c04050b1a50320f01407170240480e881c4c07910b009104445c0301500742d010220001c0354040c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 962488821 1250 962487571 962487593
    0x1c0501050f06071205090d020406180507090e0613060306140114010924090f0909050c06040503030d11090a03060905010c02010c0206070806031009031e1d0d170403 72
    0x10059501426035001c1c0c406002441c0b103003c00180648804140c4100c441d0700c0b440041c40a1000640249407030642980401c3c00c1d0f41c0141c10041c0304d02c0000d0007442c88221a8070409a101b0810315090740030b180b07810a84882c50724041c0c000781c090740d040f00340b8420103002038020328000c40d8007002c00c01c030204420745c1e1a641c1120a00841c00941c0d92500d141100350300c5864400c0aa8070b81030340f01030309040516000200308040301c803c502407129001d8005120518402c00e04010304400b40040b032031410074501241001100d251140c844c8030140418012601c0c000b0542d00d0031420424009001c0c10740c0807540c102070040300291541f020406d4004010841e142d002541003e100f031000b4004402d2417003080c0e00f030703454070302403440141e00400c0050b44144c810003a183e0050005020b984c00032344905d01030030030344000c2201980030880a41460075002c1e4194400e000454942c54000e01c030001201446039526000403104d881000c1612190007440f8086500e020b803024041c0400e55100c2d41ca1816a400030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 962490071 1250 962488821 962488829
    0x1090b040b07051608190c1a130909080d09061b12151d04061407050306030d0c021509041503060605031006030203060a0f1506180611060612031c0501 66
    0x4001c0901c00310240e0240380081c0f09171440310010340b031028820b52038211521114601642d01d60295100095020141001c1407203a040a52107130359211060380c000741c02c06405920610146107090a0140860003c105440802d00d901c0d4001c038a0140d18100321002c0d08190494200c4c410240c0405003d49030014110510074081d48000d100d0305004540840d016000ca11400b13545040d403403800d21000400c1c000d032551107881802c00040c48100c030b01078454442c10840d640d2002c40c00000c1031261501e0104804c01d15000d85107444500094181d0202d54820740421020030301c00b5020039807100c941c0c0c40b50000302031080407a410054803076480c1005c030058800c0c0d1107070364060f01403424144441c082e907000700415a034000e0028003854072150141d40c010040001c0005510769202c00541c0051080c000590040446030350b01c00c1040c0c800e0080b0481c00c1c103181e1141c814050300300c492001c80100413a100b680014115a00c403d125854a06213085114100030300d038841c1450030424410910944c8104e05032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 962491321 1250 962490071 962490073
    0xf182d010e1f060b0c070306090c12110a0b070f110d080f031e070c030c0204061e0e01050102011e091e03030c030506040b0631030b090d0219030e01090b040b0705 71
    0xd0350703c13442c800382072103004169526504110030600c0402e210f42c101d42e40c030601c5540d21b804800d94034140080c03a5842840200d40000a10030400020b03d05510680b0140c811245c2040c6010744580c1d902d4804c02400c04020007910240c60000e10a6490860780b031700b07658121124642d10140d140011110754011038048042c41003006410420f0361114071158402c44154a402808004c0da403010f0f95601c0105801301c0e440703911110045100c040d000040c20401c5054860510000d08000e0303400d0102c0c005800c040c0c110ba1520038213031501800c181000741c1c407030380941c0e0003d0701d04018140417401e0340c1c882409400480e401d5407000c04042d4140d00c820030001d2a40c2e020005516500200f106079490100d00640c005014003402c501c0c1c030040c000580b000c22002c3e110f84504a002001401190803d600c140c420440410400c65070382c0c0d0601ca1503101d1003d81c409807059841d001c100d940300c0001d5440180400800302500c0d031069019906100190442c20000d98550340d07160040000c950040a0440e21 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 962492571 1250 962491321 962491331
    0x51803040e0610080603120708160602071412090f060d0c090305060702062401020724080a05040c0605070305070807060912080709170a02090f182d010e1f 68
    0x307031413041c0c8105000b9000240135003c5101d016100d840c8030f4110400030341d22090708100c60380701a4140b070381035081c541c403c01015840c1c100310300700720002980110b10400765402c00c10004003042207500c03c4480640b03040b40c04c6003040002202040c040d00031110f41d1050103207003080ca00301d196041402c1e2411244500e04440c41036441e11422078481c482502c05503003100e48108541c0078500104002d07030700f0035010b20486a1241d99100c0b1070b004020803203460129400074010003007020341c3c00315112b036001d82d1040c0188441c0c2060b0361581c84413103c5110b4802001400300d5800109441401143e08242d00440034a842d2062424504000e1265000480e050076050000901c604e0007211694403805039515451030f001d1038010040041210340f00d54120900030003840320b006a0b00c0c0d0032200e0081d40c8150915100385403d0641104100000b00095020ba0001c0124546040d0141e0b0a040181a00c51000d4a034442c40c45042c3c0503012044141c00f0074010b036050035403142040b00c01c040011041900c2804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 962493821 1250 962492571 962492599
    0xf080f071202070b0a0305130c0603020c0f06010315050402031e0705270103020108090c090411010809030f1801140a02060a1b1e050c070e0106030c0801050f04051803040e06 76
    0x203903c00540c481c0d0740c1011010b000107002c05003e5408241e004007c5070070300e40b040380b80340c1e11107c3d0560190400c001003a03002c54903006020080004c42141c03604400104455415512000d89096101d2003610689841d040003508544080c803071841c000000e500741c295140b00c03071080d482c0c03a801076001c0d05000d0310041004000c00004200c03c0302400014601d0a5020303400d58004446400740148040c01034840d480c00710f17a498460142d140e00c11030044002030100c92448000412031380b40a44803040702d80c020b03c03450111a24501c1141c2c80485c8140248406c064183c005a8202440d0014500b06072804506401c4a54012903c184a0031103980700704601c0c03010400722071000c0d04094080300000c00390051184440011283c80d0051900ca00340176040180558179103190440303039000790a50441190041101c2505802100701080d55818000c14075814a00421805150020321501c600d4a40300411070400c1078103541c0030074050140649507115220307002000c41c804190313030f440d0040e1181d80c0c0c015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 962495071 1250 962493821 962493823
    0x60e030c010e010c0f03111006090c020d09063e01110c0d0c230d1101020301031101030f0b040e030405090105030d02030702060304150c110f0705010212070f080f071202 74
    0xd98a0304142c54003a80c0a41644841098601c0100300318244a10004c410321201c1c0104408c0b02103000345a80810068103209080007540e012040708001d40d4003d9190301e5a25812074201804d480c402e10b001025000340c028090f00d0ba03441c01d014841c0c2c0c14011440e5494610700c91042c0c82c20180b0340002440041e8514500405610441e22027180680000d001c2440d00d9115460103000c01f4090000113001061400c10f8080700200d5200700382250780240c1100304001e41041c2c0940350301460000860543d0b245480302000c0039441c4000d0790405a460303d09000e800403c0e84106030718034024000304001c0a0391001b10f603807a03001b8040c0a210f1200c0400018003858002010200c89155901840c14005e460342841f01c290400b400458401500e014006442c0c151403140c0d240500c003658903503001c0a05c050480c1d04003030945843c00f0050308035010900c81350f43c001500c00e4202c8007040701c03296155140d0801d00c40580002034020b001ea4400540e10440b1f00b402006440340724001d00b1041161304590700c0607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 962496321 1250 962495071 962495087
    0x3031e08010f051903020621010e041214070605151c02150f07080307030207140d02060f0601030f0f02040303090503070e04060b0406091b1d06220807060e030c01 71
    0x8402d5007466180c05101d1400d00001d045080020003a194807002e0300c03039000400e2031304a48ca442080003902d140080350002d8481b0303002d004040088460525052903250b006120b100107c41c11f0a001c1010982142d0301c18070b5080325503072a000201007005080c4504031806081081160078132070540340382184c2186150328410861268000c14290200580740140d00140d001160504a1400e0070b2083c500442c410300000c1d44070300d00f02d50700107a480b86c941c604618800c0c40180d80c00e0499210031a0b5401c2180c00189540c2c10030b5059428240540e00c610049014000002940d24401d08140c1003142c1400c1c15009007042e41e11948541d10700c291130b03038117040c0d540b50070f4411071a0700c40c03040c4042004107030b440c0d1140200060140004c14860303207070307014441640c03100345084456240d074016200f00c1d50fa00c00486504d1403041181d06021880240001c2c41a0007504160490024062025000245e00124110051806909940503141c0d5030700003900c5c2c5100c4ce0001400b07030203441c0301c0580961090000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 962497571 1250 962496321 962496329
    0x91e0c030e0c01051c1107020d2105040e0402090a0f09030e10020d0906030507020a02042d050606040501031104050d0305030109050901060f0b09121e0f0d0203191803031e0801 77
    0x1280071417028101ca900c0030f04100c80c01030700307840e100f048268003588032000501c071418000d030008090106c017100c240003511211002c1c0d000b086001c3c40140030399401c2c104080e420540489002043d519084c240c00010310b28102420440751802c03080c0030425400071040e000e2043c08990401d001c140e00380d82661910940400800000c001020038030083d406680b2032608076484e032046038105181d0368045002c40c0d401c44103001503952208000c50a01e8008091045c0682501c11f0610050409801013191070049000d071505046d103580802c054811b448050741d004100052030b190110031207003000f0701558020300400c0d040c5424a00040c00c10141401120103d481030700c826070000c1d140c00e0400045404c116180755122171503500c1280019000c112541c0d0907100d4410080102340a400300920704249a404100d0b640c000961400480782c0100c1a1481d0345000a00c059115980882c110760110031003004910003800d1703500c0032044c141d01c02d0884000c080b05000300600c5080030341055801180c2481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 962498821 1250 962497571 962497597
    0xa0201150f091d0d1d09010914060f09010603020f0d09240b030718150b0a09170601060e0d081c140f0a0f1107051005010b04030804091e0c030e0c0105 66
    0x403149103e074400c440003110008205d00300b030032008066002880d00030080c3e1000c4140780e21070301c020004036004003225801c1001202c10709040401c040201d20f0145051207044140b5a001c41c0b00701840c40020308035a100880c02d80100b003651800c0c5040d030790181080e6945400d6461400b03011500000a2040e040214001001007465602c0e00058014a103500405100783e00d840b000224000881d1082e800f0150000802c5140c680120442c000e081e9401e81d40880d140c15103038810100020808640e00381035444621381890b03401c02c4030010880400104c48003e2001d1800201d000e80d0f0b020700c85500300482c0c40e020092007620009044003503050070945c0e90008494005002c80c15020050344a000c0c0700402040204040007642070400098120300400c2c5d40d140c10200003440c00c254079108483c00b4020043c6201d05041c1107813640000d80c0214014004003e03540c071444072108105900828403490301140500441600b40c200401406d0481c50301d0301148100e0001c003c1543c0030750b00f03440d41141e83c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 962500071 1250 962498821 962498833
    0xc060516150b0d050c120a0b240a030b07080105100806090601110f0319030501150507030210020d0222061b0c0b03101e18020a0201150f091d 62
    0xa140c14145041c1503101240c225903a607202030403074441016802860740584c2c083c0c0344101c40b03181030003005580c0380da00403d5600700c8081200050680c1d24015005907002104001c080c4169960075409136500c4000e0fa8404003050000041001c0304038124481c607103070b6480301d4450340c2c1e032814421500c4401112001095500c00094928200006c070325522100515040f0342413000251703034038241a0301001c0d010b0150000100d25400c00c01180c8008540c00c52850100160341c074100744001c2d00b45441124034100880000c070a4107140c42002030100100002e50304644c0c42c03184420300300007507001c0710086501143c030780c11841100300300010030300480303900f03031148100c2c0702401104841400507035508544001c4603400201304000041d025520840d00d05051640e13140c03c00c0e40d04100b100300754000c0007100d0340106040c001c1203220b40700550034001e5101c0142c2c40e08904a4203070b014008810b02000c00d090454400143d031110f0114910444070005800c07c514a8a030300c00c400359107140c1c16410301503813002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 962501321 1250 962500071 962500073
    0x6060903060207150e07051914091b1305041a03071a2107020601090b0a03020108090114070e0a0e041109190c0206100b03040b150109030206160c060516 67
    0x42e400511540d44254a03c42452003d6600342c1c0071102d2094501855600030407092000f801c0604180302181e8144860f0001103140002e0f1015400c9071030174090290340b98601042003002c1d1b0560500d17000c044c006189403207184010079281d0415041c80303503074801d608102811440300c402c120314100010b0007030b01a00d4250708100c000c4c2080c02c9140c000c4c0d00070310001c2100c4040480c0d6408071500b04030141c08464050706110038020b1506406810400281c2e00e4003001c01c0310b83d501c201241044a5081c20030304842e03581c0150301801840700880c0100ca901d9554108041244d202c0d01d00c0e8090f0908403440228183c80e183ca0303010140040b07400410040303203041d00d0b00c810301c1d1142a05901900041c0c072f005000107000320084c00d84100403403240241c0c0c03000b070a016008154010500281c00c1c60312005055140c00d865107842501c0141900240c2902403c030240c0301d03440782560b00c001d1070700070301010f503a8040d403039a003014466992808c2d54121202000070a1240c0300782c1c100c0c0c81e807030302c2c1c80c2c41c900b03070002e20f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 962502571 1250 962501321 962501333
    0x60d0c060e030a020a0b041410050403290411040f020a02062a1216030b0f09060316082a0a21021201020306010305060303030c0403170f1314030106060903 68
    0x10036000360b15105100941d4016521000d07100d0203421401086900d85140181c010f0580002d005043d10400071000040d506503404003c1e107044079040402022009011a420811740c5080b90300d810a1280080421040c018503101070660008180c60401a01c2c3d6514504010ae0154014503401600140301013400c07003801401c504a00c4100722312200c0503851540c0340781c40c00d601c100c014203100c2d105003007040000d06512a07188001c40040c201803040b86030100002d01034030880c007000c42c803503d143c13004240552010810749544c208010300401301720380c98200d466907420f0049104041296515000001d00701c4548211509590241071010980d04007810100f014070741c110700c440011202030030280541d030360207103a481011900d000140d0f07a0402d20001402c0da140144524025402041441040c10b4004215000c481c1c0009004007501c400c4800d641c0d485c4101c0034400344494001c41c40c08100040710364074404031044000e01c14000051a42454282c0f0000d22540c00442c0742840208007142c1e03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 962503821 1250 962502571 962502587
    0x160f030224132a12050c060f030424050a020c0c0411040e15030a1109070c0b0604020a02010e0a1a130b01150315080d120207020306060f0d050102120708060d0c06 71
    0x3c003148440d400c2c0c10807821080300d107040d540f1580148062610403c20b000d8240582c0740c050b001958580c0c586118511070130032314800500300800100840c1b07d0b4040c035040389100301000c140114014080d0341000508800039401508200d01d09024400c88045c00e817819109509812882840482c201031802c150700300e0141004000d812504228542140d0030b94041c000014003905c070740700e92402c0c80f5104052180103240102194244610081c05d040824400102d0552090302120056951584c03040d0890141a541c000392089201e8040002c0400a11000d1100103801c15460000d180c0e030b80d1407008050110181010740401400d20041c01041504154240004514200858a551600c1428081c040c03d54400000c40e042151003100b055804007604010000592080d800d107102c1d90002a00d60b00003520043c400e01d01c48448045c2c4d52166120720307002a411200840d01d8060b9414416101c0c11700300d402c480050041000100c0da482c0403200c511602e070b0440c15400000c0c4c1030007c155100c007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 962505071 1250 962503821 962503853
    0x6050a0e010317160c06090905090a1b05130b100c1718060d090308010611032515150e07230d060803041410050a05160f03022413 57
    0xd0020413a21100585296065019030320070006000e00501d407100c020000c070055082280d41a00342403d000c1204000100e65800c1500f182c071400c803c54070f03082018050a100d81c8010b40140903800c00b00701414441c0c2c013220020000383c3d1100d90541d8829000c80c1d44420007040184100745009141e04c803e0340c100042c0c43d03500e65500c11960b4800740b070310001d102d070313005000c04030001619942c00304101a84002c507a0700524081c186000954201c00c0317400e4590049050107030f07021490070303001b0610311882a030100f925500008454402484046684064040c03281d16031200780c00b0704000203105170070082c014429580c503030300c04494403a040c0d000e9200e050f00b00d0b0076210401090103001c07944541072092400808044c001140da41c0e292110b981c09002c1d9030f00d500c0c1c4c814012407040a030002d2300001107403003001c101d00e0b00a41d5003a45406110144c010004040d00403400c081d4280101a00000c0b840440c0da001200c5409e40b03e4000d1801e002160116180748004d40c07801491000605030060801c041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 962506321 1250 962505071 962505113
    0x40203061506041a130503010b0a051e091905400b100311030c090f19090f02040b0a0b04050f04020d09030c1e031d0609120c0406050a0e0103 62
    0xa5851003800c02186914042c01381e45000021080144102c5004980041100741c0090200c0c4100c0c00018403c030701070f0710444e400780080e4600b0301c10211149011540d200310040c000281420072043c503444845541c2407000a0754501404140b40c03410740c09024a00440c118890505621210300700004004440c0c001000d402c0f0070311040000443c1c103c03000d80328901c441d24015000b483d5060401c04040440c001d180250045500800262100c403a519806550030f4541440d5803128052540c040d55101402c40d4042e21b448000f0081066616900300018000c4805000380c00d084420002c44803814883e243d03c0d40800c1108100c0c0b4103040c4112291410010001420004482080006d64003c0c08044001500400c080420000d42031034507000d5040341d08101b080701107940d401070030000d0700c81c01040343d1143c088030b00d001c6960748104581c11084043c00700c3d5604200d01c1c440a0362158003120040c4101d0a064011070f8509140012004503903429230b1050b80b6901e507403264041d1508100c120055 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 962507571 1250 962506321 962506327
    0x306080105043503061c120509031e190f171206041806050c0f07050c100c050c0d0804090905160909021c031404180534050d0c030207140105040203061506 68
    0x7042c3c4d00c1c5603851144100f1b441d230641d100744800406040448500c80f0002c01c1011900009509070006890300b103c1000c4041103d403214642445004480340c0c4000803d116604400705188042c030402070301a410300302e0031402480e01e80d8020001903d41d1002410f1070f4103100c499150129a00390003050f0040310703001c1d5844c44d110480040020036809030744159001d90242781c6920a0303003000307a6030104290261400c18a20019640c035581c8400b84800082e100d503080080711024029008121802413028540c100011150b41c50300948422003003c801c420240040d900003401b1107140240291103900a041d10055100c0c0c00c0030080407000d0801c103804000c2105841c800704c0041d240208064000700c505d4140009562500740d0a461000704055440180c0000c1021210074803407c90319051400c1390000c84042440808841c0b40c02280c0144d450f190070515000c585d01e0300350740100303049806100f80188a82c20045240d09072401580c0017501540544c0008401410120080010000040031585 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 962508821 1250 962507571 962507573
    0x51027021021150f050d0f02010e060d050a1d0a031407020d050a0b060a150c02190609080c060a020c0907140a0e01110109030504090207030306080105043503061c 71
    0x10301440728000c84110664580d200943c04140e00710b901c1c0101001340020441e103003024041540183d0360040102030601054075002168000d4140e1507151501900c416103d010f6414a1300c060241958450042c0740b0304903c108466844020859070100011f00a040c0f010407594102c805c44456030752915820302c140024001aa00c1c5410400b150307016900a14403d081420020104a00913040c20f2150659160411000c001c2245071040000d0600780b802c0c0d43c14060021a82c82a448a041002180b0030382c030205030b094001d2051415662400c0c219030f04800944284104c0d440340700750800169001042c80d4100e4136151401c242e1041c06440d00e008803841100c2c006c10f840c1c000301210004500854400b20140d49e0080c98140c0040b04c2000070302903268240c4003d0150321640c01090030150b00000c00718113040c0a90040002071082030300802c5107240900300b11112030780b01142000d002e4100c04e40c451084480600d6080c520032000102440c5844074000c00034820700d0441c07000c02030b524141c0014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 962510071 1250 962508821 962508857
    0xc0d0c080706020d0f0e01020705120c09090303180a1109041a0106020c09060102190b06010e06070c031205121f090f0c031506020703060e0c0d0510270210 68
    0x79005000300c1c0c0080c2580030070001c0140404121102980801000094050307150fa400a54581200c1c0180c404e6800820061300550070900840d050380d4018884005102c0c030040008000d600c50040315607242d00000c0c404005c02c1d00c40303000840c007514200640003100810b14000c0c0080e034205108003ca625510b000d144240903030802640b11b071000d43c0200400350b6250400891407a44044240b02824190322a80e0180f1881e402d8144060400301c17079100010820b901402c0c4400030010020611503c030186441d0441041d00e0b280070440d142d410807050700110b140944155008610303001e03183c07135141c1d503090700015031404503610f84200001d2146000600010610070844012250b540100307001c0c805c0d0700060196006909150760411100c2410451503601190340819268080e0300403500d2120611118503010080010a40c0720b0000c0c4210b5040005c00611020107501300b56050100e2108519003810003034088070159185d9260740031140052601595103051100345040c01e520354550740d1020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 962511321 1250 962510071 962510083
    0x1e05031b01120513120503040b07080103051509011128030203061c020f060a0f0801080304060210050a0e0322081f180b07021f0225030e04050c03010320030c0d0c08 72
    0x91782c081840001400300340a15096003e900032002e00345040107501d5503a420ba6240741106120244015640210310084001e4200032106d000c042c51003900c0f6014040b007040d810a00c2611190366021000c080f030007041c024001c0e01d206050061411142c504409181c4ca802da4403000103d90003603132240e002c001039690802038580c441c0303d0381d1010fa074500c0300720b0050b00c50700d0180c00c0054654400e000030000729900060b48048105003080101d81ca86910380c2c071401500e01041f1400440c0004a400c16500e07102d103194611014002c180440260341c0c2e80c107850345a40706880340c4469010003100d04c01d007100d9a50030038158040e110030440445480c0d6114032103101d9042d2945001030b00304221601000104c507202d40c1480046800031464164401c4a146030380c403500e100e8200c5a06003440c401d09160149084800c0208050414000c9140c2030b100c41c81070340c0c02404101c0d41480c140348903e1015130b01c07410f12103050300090001e20035251a5001c001c110450f034582210520151b6001054284041c050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 962512571 1250 962511321 962511353
    0x30f0608010e120a050d050c0a17040b070e010c021201020a02070b13050d11040603081803071d090a120f031112041403040306020705030c071d01060503101e05031b01120513 76
    0x7905464210040009040c01c2c03000c05812b0f03125030340e1030901020a03910540e060f000f1004d030510181840090b40142c03108141580060b522000804000c401d0000c10340040c11504c1243c3d09986a840d29861001e5043c090120201d01060081c08240010f0500100ea907014500072501c0702c424044c0040028140c890720f070011158008041144080c0003009181710525600c114083c1244a044c1681004200100d0414440c40142c48011421240c001d11454944603004041c81e80b00c100807001c060407184e4510440e0b000689808a402081c003649815902b9100540000c4289911a40c5481e140c05000f0410840c10307010400c800000600c80d8402000360030721031806584c0701c150500c2243e0520b001c55100404070814151902c002594046805064400c2400c20f240c807601d0b1451590b01d414010b030082070011a12908070600c1a05003c4030030b00305c500440c202c03100540003420110301401c03000c0001d40800c003040c0742640c2d1803002d5042294410340d0144260b10005840d203e84600c0072a0000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 962513821 1250 962512571 962512591
    0x70c06050a0906180201090504020c030906090f09090109170f030a0c12022d040b030406020d09021e030d0504050303040909050f0d1701080c010509130b0907030f0608010e120a050d05 80
    0x11343c400440d6004043c0100802c01120110704090280170629203911401a0081c410070002410b40c141350f4400202c2117050802a2800b291413400d16003a40c02041c04900c190740c2c8450520350900701c4180d0780101c4076401c112010715802d43d103031a08200d0207080c1c015004c00c1406600c5007040349221862020300161481c04555502e07010482801d1902141402d04000c1c0c425001c00c401e220716a24001102c0e0066031156005a40e81411904a001008600070080d400341004103005107100c043c0c41b04130b00148040f800d443c0c00e0111103c065810744154885c098040c0c0052004100c41010355200340300181c0140151b4040c102d5100303c00f82040020100702c400f14030014507615501601d4031050340034080800040c02144603450019000e406001d0020703100380c1100d120030b0381184098010040601001d0800802d5061252002e00504002005891000c0c58040000b4040c0f1050242030941da007104041c0c03030300c032403c04c0e45c0152503442942244203000c010000c5c0040031400b40300d8107100c1c15441c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 962515071 1250 962513821 962513861
    0x2090112050618070e1f05040e0403030902041406040b0a0807050607050a1725021c1401050403020c0f22090c080f0a02041802010e2403040c0e090303070c06050a0906 73
    0x5003c00c40760103aa00e522101452848000c450306c03a400600303c0b019140300303580d04009540c0704d25045014001c41d00c1c4c025040fa0500d6515058184111042c40c095101181c1c00c2c0150041081404a09105445004034642c80181c04100e1400c104008141c040d0040f02686c1c00480640c0342c000c0070aa180e502d40a5408000907200d00390040744411320003d00001c20380404240709600080d404c0f800242c41c40c4041440c4515140400800321030060082444000911040c54907090103512032400a100c14001c0c0b1008001d0003551515140000910301c1c0c0541c2c4208085644100c40f00420810104403001c114060700403176014000c001d00b01c0200158001052201c0b00342c410701c41510488140d007a40300c20444142750050382c010305012590042500e409401c213014000f050b10000700304038910b00c070700d40c00014001409490450354041e11a444e14098507a100c942000d07035a071004840740b000141003210590001802508513541160741020046032821b040c0d11303036104a038010080c40000656038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 962516321 1250 962515071 962515097
    0x3020c10140405060f010305071511060f0f060d170a110a050705041b1e120f06090c02030408030a0804020315010b07110405100b0c01061208030108060a0209011205061807 75
    0x20481e05901c0b140e014185501c5c1d51450391855558640c5002c2c007181071140281a02d55a03100351483d00c40d05035031004642c071034103029070104001c440640d000711251120100248240c108002076610a80e8002c00c9490801c00604000031140c000ea0440801c00c808806055400702041203844030311401040603240ba01d24140801c4100c40e810150b00303081c100084101214036401c1808120610700421803100301e0b0203014000c403441e41a5102c0c1ca0b50349403422011410564180c2d0280d4162134004404002d421401175081c1ea89002d503124040040e0f204000060015102c0d0350140c0d04a4805422100c902d4100e5514031a01c9400b45c1040c2c150a0021032000d0500129940314039800c1310a8a003000103040110044802c00018003400c2c42d24000020a24841c14095001800411840c40e00c01e1204034541f03403402c010360082c81074460700e10600300840c4070724501d4400c03156004030584854034803006000c0d4031400b03824001e20b82c9510a54215028a6002051306680d109144507940c4010282e08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 962517571 1250 962516321 962516323
    0xd020105090601030f0206091201020c1b0405010806011703121603050a0905030d1e0e0703020a09051e040503120703020a0f0e090a021b1605010e010e0d020103020c10140405 76
    0x20241c0d18541d00250040011802c01c140300b030241c580546000741d1741c0d640400464001c001c042d411450540c40042c01e40c1d80c84002180300f101c170710203040d4002c006088c0d0070100070135240280101050303500b10702c004001141d500c140c80c030300c3e50030100d094a081200b40e207946606800e0817a48049007810402a0441c09681440380b03a03445400075008100d0b51000d521407a03900e024011030b04041e59030f581c080e0821148034074080300c9840b40e442c038180400c01c42c1811041e281e4200d440200d0250003000c40201e14900a405940e116605c042d842c503500d80302e90403004100710009031003902d1a0208109044d511f140025505103d02400c0d20050303501c203480140141540342c440224002c000600c4030901e85a0380b074031603c80c3c00c001a00070260322825003000d512403400000485170024411440455281c0200c10145000c541d4240c80d01c49000b1030107801507500100f0f03a03c88c250f0216045841c8801513000754041c180c141419000c0350500d204100d81501162001c8840062950254080108100e8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 962518821 1250 962517571 962517581
    0x1509090b061603080712180c0e010b03040f031b03180906050108040206070302010b03060a0501150e0d0224070605040507080d0512040f0f060203091209030c01050d0605030a03020d0201 81
    0x10780d0a545403010400780c80d251100410801800c200501e4049540d091140c240c1004035000d041080002055280c1c0c000c0528484080880b40201c0d15040098000105416035040304c602000542c07555a440c0e440170201790800c2012418031000181129581c40d01400c00c11001e4401d0700d448002c0405080c8050342003031564010001103081090a1000d80d038440038554001e94150742040c0c641e88180340503405425282c501d1901441102c0400c6010240754000328101c81d08416081214120301004844540408540e10780012000e94088011f0801403c82e003910310102c5041c1224080d181d20f011020381c0124400ea03042921402880140042400020020150b01006110009000c03501400d94000e14910320020903038100028188030003c1e809281e01c0354030140103c150703111443e060009401c1a1001012846900da400003140307150b10444154a900400070b02441d9200c02c0112565441044100c0030b05885100014168030208070803090340d886500505201410400c0082c2119 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 962520071 1250 962518821 962518841
    0x117130c09050601021b03190b0f0906010b120a1b03020c0c0d23030d0f050a140705180f060703030506100306030b010e09030712020c030d0203070b1f150909 69
    0x242c58001409281c0e0380004400500c0c501412412030020920000030b8141000c00940252007640c4048107420440800400d500c113148401c0e40042c41d07251081c00c0d5994907004d004812041e1402c100c80801133444e18803070396014581400200c0e010381c50780d84e14603580c2107541d640d0010030b030041020040908248403e0101e0780c01610a01c2031180580c03911004080440c3c64a0b070f6818250222182c55601407088850aa00d00300f4203000300c44110001500506088980403a81d0745000c41d00115018414002030280b0107942d186c03814005900c0400c01e00e45038450407554030003a007010144440e242c3e45c01400c012030080c2c40000d514940b58050001070045198407408140c640f08090000410410720181545e00440c2d40b01419594001030902d140716800303015002c42e03001d03070700c000400e1b9000601030391a00069058620001d4140c02c00e90352809606030050a00803102c0000314400d843c410800b842a074600780d99800c0ca580c070310910300a22166400d50000070300d00780c010f000012441c0901c81c0a2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 962521321 1250 962520071 962520089
    0x9280b090306070309050304090606050d0e030307020d0806190801020a0f0207030302030a230d0903020c01051c1a090c03090d26060103110406020304080c01020708070b090117130c 79
    0xc261a00040c1d16100700030801c40500d590342d940d1a0500c441042581c015080401c01000401c0d1070304405040350b0001d506803000f1505050364425400c2c00481a61300a46180c0c004210401c92800306503400d0301d004041e01d800c02036581040b00d40c0b103040ca18030310041c94000c0c0010390356020307003d00408203c02c6440300d006560000b1010800654000102c902c4590769242498641c0c2940e080b40c001c1e0a5601c00d5855005404901c01301a80483d50002111034130907000c0f0717801040300200540311070280c0110860f51550074054002c200c0c405410860340d00354070f03684005102e9105000152805000e40c0c0c161016034000c07003044421601080f45400d40022400d02030341d50b40c1907400c083d100b000c825490516203007419000c2111a40a40c0245100c4445000c026441c0da8a03a04000c2d5250041e103d800d07012b2141b240340b01c10950011498401359000000a8030156042ca1ba22514640c1309990041c10801d5400503580c1c0040d1419400b40591401007036681d400300542009040100c00d0b030445411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 962522571 1250 962521321 962521327
    0x1b0303031e0612081e190306090b130b040f1b02150c07031d0307180f0204050d03081f0e18010e280b0403050a141606020f09280b 57
    0x2031000c1c2120b03d01d0306264040e82641d5a070010b00c01c80025032100305106104400b01040e804507200b8030048061000202e654201309060782e80401d04281c2e0541c401a6421040712076201031064103540110704401c01c058804101c1140141031402102c10000c5441c042d032606c01c10104460350b043c481c0d411024000c0141c0c40e89400c002500010038411a40001e050202001041e0301400500414100d1810010183ca10303459480c0b2407062049594925911128a0b0003100d101c4008140f00361019030700090084c4005107101e9800382c03150740b0042c01d05000e0701c50300f01d009401c0c012058658809880343c240e8009140c03d00d00402d490304050311842408076414501400012038001944440001741004038a4151f41c00c40d4072003100ba4514000508030000a60800080c19000780013802a4105641d410202c01c404120b0268280642610044070325a100c18210201ba0940c01800c490803403104510b291044510018803010201e80d41c0041199800007448400c1554599401c020b060703028444e45 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 962523821 1250 962522571 962522579
    0x71226060114031f030303050108010b01140403020904020607081303030914030a11012304210c030b1b03070c030e06090a1e15050306030106050d0b04030c1b0303031e06 74
    0x400000b11040c1d100b18070010000801d682d401301490280c5000304424903084680324107000b0060310003400b81040c251b003030080c228400d52150080c4107402581c038003101e0601c0d09503400c000c401c0401130002e81c0d0083c800d00403035001c02c014070000c200b414004042032a503d0300c1c40ca03000c0e2000703900c0d0f80220718401e4002d02501c003944002c5100f08100b6844040b11200000d01001a2008006942001e8800040d0850721b0107600a9100510981c4c140304550100c0007002152a043d030300d00a0300c018049460104100002060444ca840d0020350f218882d880d900c001880c0d20b095034000f103401c2000204903c111005150700800e01e91a42d40c01550703007034540341ca00c3d00031814041caa8818202c0b808141c000c6641c00c0b000d4884210003400342031700c490010a41020000b80a0b03002614490f200b94a030404c00945450030a00c81d262090f030140c2040c40550711601c0c00c0c3d51006d1103401c2520b01c5081c544140c000242800924000740d4803c1d00e0000328000e1003003004c503c5400311540e41942924001e400c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 962525071 1250 962523821 962523827
    0x30a09200105031b190504170a081c180506060f0609150c0a020a0e0712090b0c07020a150201091103010c1e02100c05030105030105100f09110712260601 67
    0x95025102c107a0305000c0001007451080e00b8440c0c17504842002054408800007a81e0080c014411110403d84080a501481e0011a21031551034070041c2089400c00046a4160420215217542040b90000241c02c3c4038558040b0303801c20250104076201d800c40d00802c402c51034862030034a5010f10a07140141001d00c2400401c0d4117005480328068030140108030a040c108040001202c010382c050b01c1020682d548205c1e402810340d060362200c0200d400104e00c2c0d0080486403040864072500002030040e2a01c42241441c481e9010080580e08443ca87c08042403105c0381d5079000e0150b202c20703400080c0200081c2000e0303180796119001e01c2c3c80790341070181e92400c071a0300004010200184110035080043d021005038540001601055180e908000c1c00101c040e8004000d94100c5900794020300c000d907218103600380a0741d124081c2c1c00d2aa040701c0e0781403000d102c0c3e0b40c0c0510040c40840301058a812001d07122403101c50b90101003d400a000291080e80207100400d8000c4a00c02c000301d99006070411070b00203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 962526321 1250 962525071 962525077
    0xd02041d090712081e090907080f0f06060d0e030406020115080a02010302090109030f06020306120a1a09030408060108061614040e060a05040c020606010f020a0308010b130b030a09200105 82
    0x1003072040c20840c1c00c038020b0049040803900f5101c900d51020510301e007085d0315100150421080644187c01c1000042c0185014072001c0703100e51820302c8140a00d5854114a51281c100900b24640000c0c0c00c0c4894a1107003254800d0000b4060200010341c0c442d80391503002425a0b6600180c8d09120141140400c5801c43c0000d184402c5135090a0160b00c4d4000314004a9070090103500c0640b4401e0314a820740240301c150307401540180416075081e20b07a4107a59250b00ea9039070340c04d81c0080035030744803030000001d03a88141c44c051b404c50b1101d420f980c80c0070307500d0034041d16189080c0c1108100f070300100e051004030010394a41c09076074502801e0035924042d61002400e01d60285118401a514802000840e1aaa0a03030614090a0f005004000140881c0b00081d03594004a48030303070125400c225003c810f9400000c030900140c0d40341da6003050f180e003442441340040d008500642c0880d45c0c000400320300d8003a000080c0d481030401d00c40000300001e003030911203002c6004941000003110400701e4120b086c1d901c8422 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 962527571 1250 962526321 962526329
    0x60f0717011403030c07030c08100204080a03123c110301060309020102070b0a08040209151e0f03150f100e130201020c04052806260708030d02041d0907 67
    0x140b6009071a44082800c61003580c5a07118203004008000c010010100f8810040d1b425401c11507151680400807401244541d0013210590f510070b04c250300003e1310a1092410030b550b202070100d016000c4910582d881004048002180421412b80381071042d07884144080c1c0300b01c920414041076401c1c45d01c6045901c03040c024201050344a072540000d690080000360020911a16020398903602d450700100381c00c8069600f20711841c0424040740c0c80b1220b503000068000300c010008070403400c80710401c9407600605958140c001c0c16481200e80e046d5070901c8002e20700b40c01d003031800250b49489002825102e0000b0301d200d064003218842403080080c1d10147d00d5010318000042498015207000507443c190815a43d164400d042600700b2407204821031043d03407960ba908450001220b0211722000035500c6500600b4851042002003003c0381c208022450104008081a170b040b81e03860310217450555111014203013006400003402c01030703012003021000f92503204005c101c4680c02c21158150716003126220b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 962528821 1250 962527571 962527589
    0x20f09041a1f020a020a0b0d05090a020a050d0201030b0a14100801030302060f0c07170c0d03050405210f03010b070c05030a26220e07050304110d06020f0c060f071701 73
    0x3000304141e000700f0440184c9074000b40200c2e0503e07034595015400381d0100075035070507803030405021801d00705002131a001c0f5030380d00078995481ca84c148402c3c03114420f0032903000c1e81055100c4840803459120103100f08040d0115544512010350110f041c4000304c54102108020810a80010000700b6408101540c1080014403519043e49a0650100850203001400b0385802c8000000003d40d8204c0c43c000c1c242002c0724000d03141070794202d0100380c0c01c0318000c03100a003e64110190410f2600c0501907084080180000d606003046919604520550070903041a0201d0000246420500c400380d0400350003044202d000b060340b1000d507500d030703800c80c400e141b0581045121441d1800041c090075050300e030541049902030b002544616002d10038026640300e608a5900740c0000b08284a101d0402c903407040b80c105480500e0022814248403481c400c140c01620034580c01d1100c3c410030303800321004001c082003c0004003114142411115010607001e0302c41001c3c020483e09074105008002001411241440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 962530071 1250 962528821 962528869
    0x1120b0a050606070503220b0408031204021914090a0c020d11030d24061404140a0e01060e09090c1e120d0c0c050a030804120213020f09041a 62
    0xc2c000c5507013030003085401017541c08003150315000071000f4022040740800101049651a80d502440d058901c124050700703001da081040040c2001c1a0100c4003600a44050481800d000c030210140c00d913074500344c200c041001ca41c140c201c155460305041494000080070710400070b460030310101a40c0c60084540d4141400320068401c50500014400d80d000380d41700f440b0a202205a403082014070070240250300140d02540c410200d05107104032640070b60410b0b00c007032a6150174103046000c2c0d030300c003040380c401584200381640114050100640c4640201000d880391042000c00c4170410490100040c01d2445c5503000e084240542c2d5104101040031882d80564020300e00f03007480114a428903030044450440c41450107110150340c0c0108042e00043c00b07a020400c0103901c8108220140d01d0510004c0c0000f88140001d10400701d8807514080d609100801402c04100711420081c1a60070002e402c0b80ca0303810225100402d4201409040848007008440400010310040010304440c80602c01c44d03003d500003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 962531321 1250 962530071 962530081
    0x203120f041109090706122304050304030c060c0212060628050a260c152215090605041a0a110105040501020315030303060d11061e040305010501120b0a05 68
    0x316407001c56001000d412603a4030f203080c2130107503a90000c034410000001c400d05c0c181e914072903403846200040b01c828100c4c00c01d05e03422107001401684025100f0380300390000b000f0020001c0c02201031a4010022070b2120400380d50f250041001ca9010041410a540c00c118108103040c2e841140c0300055803035181c503440b130300d1118501034602d1408680085d0b40011034401c010581d80040c1e6030080900f111200e008c103112110011598950780107100064214010756100c2c40c0800795a806040040c080b04180c0e0fa441012000480b100c90303081d0f00941144407180030720121564444140340240c0b4140c100780c1c1c54240303051291103803402e519206610720607001c54002021031096615612448400000f40828186410580d000354000d88101d0440b540f00c40c03000819081c00303c00d4910841d00101314540450300c58580440705010490110343c4850100300c00c45080141301d8031701850400d900c0c0517540321400c42c9455400c50340113801c0b00700c10036101c512610028030341c1c2d00d240d07606c040d01e860080703599110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 962532571 1250 962531321 962531333
    0x15010f0e072313031b05190e0610032705010c0f090506090a0510080907090c0519031b11060a0b151c0509010507080114211e0304090c0203120f04 64
    0x100f0340008022800d241c0c0400f501c52030401140b01038400445003c1607d43d002000036910600354032074041c10b440c2840c005480b5107000007810b4041c0425040c081419415000c42403440c2641804019928a4050090050090920441420b5261030030a9400d08580d8000a001c1c88038601c12a4400c4800143d61402e944030020b0305070003840e02508021111040d02c50203482080d0440b00c08585204400000504542501420309603c00c1515900d140c01051500d403d181e0a24042040c28180c441c450240c620718854000c44000a1903a158201502001c1200e4100f002c041c2035082c202d800c00c801d0302c2a0390f44481000601c40c1508284558803000700480560000d014501c07016880c0c41d00c802c001d5012419000203110b00600c1d901c204080c0e884407500261414042403554000189040c800b40c807280103800b112880703680808495200581042c12400030a200a092840740c00c080340800c40c0301e200780900d9505111900145042514800e10381000b108014810500702c0140b80224040c045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 962533821 1250 962532571 962532607
    0x10c0801080a0f170c0604150903050405010c02041e020715051b0315150a1b1509170c010228081501110124060903150203040515010f0e0723 62
    0xc003a41159110b900c178549079600c036107044400b80e0781c4198a040748401144144550340446078103031125406c082c107090044034640000f00e012a08565154160441164000300000405400314409642c525041c0b138048135041400201c10601810207042c04032040301c0300d11380310b644144483d100761240d0b502010403404404200031146c2090704013009008002807807004001da13040b030b600c03080740002c907000c080000c10740c01100150541040004843c0e040c80e59410140580b40075440703103018010020f1040e04a50310660b21403d05a41c001690454010030510241134054918214000511541c034003602c80e850003044000082528490761013140e000e2640650f440aa0308000c00005809000c0030110b60304000c0461000d20a203000082c4882c0304e141030105681c2d20000c0c1079690030f41e00c1c1c0ba800180d04050000c4416015030303803a52504104680055000342800d440c8c0b441c1c01880d08819a0091034098041410012100d0040b004000601c40c0d4904c02403081c000340343d03645410006814426 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 962535071 1250 962533821 962533853
    0x90902031b0715060605030420010903020f03030705100506030132250c0b0604020c0307082505060709090b030d0e01020f0a030e03010c0516030c03030b06071202010c0801080a0f 78
    0x2403138550041030380e951180c09144120300c02e14150402001407000340c2c00d10340310080c806000030a0070b0700038030060801500c0810305038806000c40e401c0c01441d80d251b505200b44503114030748450365030f4104103040c9400d00894000c0700d0031542d4030440b03140441c6c2c819051944519902040c91101c03001c6040c410405400b01301010500090b0342003c00031141c020803100702d421065030418001c90111710185000c0c400c90301c1e1103a1900007185010703407550f02c40106800c202e8800321441d0301c50390b41d20101c4030b15900c9100c01900c1180a0302891901d030501400a00b559081601c80c186405006201074500003201e07910286641424460210b4400c0103c1c82c103510280f8490b040d0040400803010986c1007900f1082e240e100318002d01500000150440b114000c405030f00c0303481c811300210800032034014050760744950b0107880d0104d440c61100c4081619948591002c9505403031180084d0344182e820f2047c00307900200c1e0b14001d1810b516001c4066900c10448402404081e003003000401040b110400a02c041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 962536321 1250 962535071 962535113
    0x1704030804030303050f0f070917010641010504140a05040c031d0c280b0714190206191106090606010f05030702030a2f0607090902031b07 61
    0xc0c644a03d80103000d40801e40703554420511410104180d072081c504254860301c4150fa5803080e480c43d2a8180150384200f9224840e19581c1d4200170440d03076407642a40b400085d440311003518010716001c04a603181d185610300c5000b0fa01411003005181ea00004442c00c84801c0b01c10024080b408400103034020741c140e80001e62103494010340d0300800b500364214581c20485c1e08141d010b00084510b07025243c4151682c05580245c3d21311201000010480004100c0752900c86500141c5854210f0602c0342e600550701680c1c0c035115403c0750226041e082280300c2074640103282201c1040540e9010a0080c003d00f440454422030b9580d600440910880002e588245414119001c42c108940d80f01c1d04c0740781c1690420700240ea00040e00300700a000390300305ca0092801c0c0d80218940041040d00301d0b01c812041124101c5a510050360b54908035035589104405540d0801503d4076042505000d40202c440d0303403040e10400d005204003e0348501000034025884441180c0c0c0d0355601003894805601d0303407010006051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 962537571 1250 962536321 962536327
    0x20c01141005090f060103020a1b0308040c1e031509080409090b060108040c090c12092f0303030609250327050604171c0504020a1203050717040308 65
    0xca40c2414011801016960aa600100d80755024003035420f0b01182c00010221284001c210700354481d03801000c102d5010301d010440c070b542c0e0210030600c1c10142c4106400103211402400180000744400340300400d40d0600450b1450709100010029984601c006014143c10000c110100d45440d040301181382d51012002c0c0c0c0e42c40d2500302c0303035008000540b41500c0440c0e0704400103140d03501824070356000e650800f009035291032511111002600c5804009000c102140504100c81c40d8540100001640f080c00c0040740b5070343c018000c16203100c0d400181a00380050740400a0261030120499070080d00c182c61a0740f066441d4034a03480295420086000424030f0740f185421b4240d455070100602030301c041c08850381c18256800008620010000c054140d80203140410005643c46901c001d120204c1c40400381495000d072042c0724000d548000440400d81c948081101710318148203028007501c4404203031002c0b501c880e10020010700488000405401000b01c0c42c2d0381412100c000d0340c0045500640a503a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 962538821 1250 962537571 962537591
    0x30306080f010f0506010309150b1302030f1501080c0a111914010b0a050f01050c0f070f03050709050721060b0301090902040f0c080a0c0306030204060b0c0f030a051606020c01 77
    0x2000b04005a1854561413408020900d20341c4070f4014560f8041d080491100c515401304200c500400034601c00d2903000006481111b0700d005a4000b0f50310030f42d0303402c01010103031030191008490042c2c01034201d41001014020000314040010907500018204c1c5130041201840d52182c510300200303454020300c52640c03244084204410307140c007800c13001c003828000c0c031082442400b880038101990160340c0c1d109944e80800c1003d0b5100e1800340440c03504d90011502e20501480c5c40c2070606000340c10445c07099100502c14803d00004129000040085403800c128520b0020301c010a2444011b40c1c0c450b4503000b4a000307600c44041500b100d80607044550407650359595070032036400200f154180490150381004000c0030141410700c00d20740c411a81d511440420354804500b00b0041c54014601e00a16a6400c4c0c0400540c80760701c10070001e06501c159a03560b5040d01d07811245045500f040d001d050313502c10000c000383c1c194010182c1c0c803a00800059240700c2c2e445460301801a01940120b16007944c41d10300080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 962540071 1250 962538821 962538823
    0x3020010621051c090e0c0d050907051018050907020f0105090d0908030a2709060b0d420924050a080601050d0c030f0b040516180504030306080f 63
    0x340359684100102c500c640b100d0f82d554889040002d140e0800306090301340411a01001040c200d51081c0100c1e03140d03141886101115080703c40940303404010354851030041c8610b091141e5500074810380c0b410003143c0070411401810318420345004040c0034004820116990500030041c0c4086010302e8402448507203492840c950b90307040c8201000300010b08040001603001b001200310b540381581c0b682c0d00304100001c6882c80b08186003031201d122420307241c1140059160264850a80900501071705190f684c0b403030800ca6400e4404144403244100d041c2400003002c83d80c001403560f1000552503c00d039144105040c0641d4812844c0e0012505a0402010112040304180c00a1a4101140f0b40070380050f01d401c140205000140940140f5a001c20010b10030380c607001c900050324920800f48403050a40320703520740c40e00d20715001084403164400c00c18031007000700030b10601d4407105612046091040c41d0000003418075601c4041d40c0341c6250350f031000c1005c0c1882900541c0203410303801c08a4140d090070307403c12 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 962541321 1250 962540071 962540129
    0x120106030b0c0a09060906230d021606062709051009240203280b03030a05031b12070f020709050106050d0515030a080d0603020a0330200106 62
    0x2d18000b0b001c1c40008144180506e0402c8142d82e07517503070341e10b13210300061a988100080e2032558006004060100b540c41c1081ca000805d05000108a40f00002a90f864004140d50868001c03803152070b007040701a0b54030100e00b5066000c40088000c0451080b40e1803e1003420480035100b505595030a0940d03100c144407901000342e5501c3d2000385015101000840703180c00b240800d445100b01060455508a2180361b00000c1d030901009007440000c0740042400042d00d1a4003d02041e07000c60404001c100615500503900c880710340d82c4c0c0e00200d2601c00840c80d401d07210140180f9005c2032105080160741494070800002002d41080e000400c86540c45070300190254000c100e90021007820880042d41d203007500840d8025201303005d001000c5000da02c5d41c1d5008680c019820b81240e4039594500040541d03221031201004600030562000781c035180b1010006080d201204202c4408410b1142c65200c580c02204003406c903402c85840500000d19014903805820309034045c0b20702d81c902c1d944101840541241c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 962542571 1250 962541321 962541337
    0x90803010b0406080a0905031806040509100501110d0806150c1e010c0e090402010804080c060c09150705070608060301140412081f09020a030e0d030c08090c0d02120106030b0c 77
    0x20098655900d21117101520b2030041c0007032090b0003e0200540c103014507000081c054000820141c28581c0703600208d90102c034201c0c0d000b40d10b180000320420071942c002c02c08140d00343da003030701405030344008040c0030300403241c0174010794041c03d0300e0400800300204400c10f0b02ca003101604180d89610b051508214000f00c1e596100381b00952134010151341079400341c807015004860191413090b80c2d03933540d0010340b52044001c1050b985a00100451526880c0504c110b13445884402031340768a03011810184000e00c1c450b42841da645001c1085124041000012208110f80e01c03840c1250135a607804010a0140524581c440c41c4141101c0900041040910035122100d030f06650340341b07490342c03118a0101850b518200851308040d00e00c0041c020310303150350028076407400b5a040100e201b0140d082114903007148a1043c1d00003075034441d0086e8003554000e07646038111b19000010840340f50304000181e203144050400a00c260b0b250000300c0002c1c3d40a400c008011500000809181e280c40c4007007007080d0303110042c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 962543821 1250 962542571 962542577
    0x2030a14160309082404120309050607112a040b04020405030a0f110402040509072604080a02060a0501210c080607110607081b070f021005130b0c150703090803010b0406 74
    0x1d0812041311041903000e29030440780000459649481d154051f20180e000c0d0381e0b01c2051780b6041e4500204004000c101d024541550720581c0800d82071041e41e0502d0104101001800148980d03180c0c1170281418035140740d81d00b02d6000500701e142c100003034001e04c2641e200703542602804004000348429594101c0f0214080e180c0c0300101c5840742c08002c1248030360300406601514036004200c1e40c1d440341000c1900b004046410744900c00800c042c50045c00e170103d60031151141d00041e45103486a040c0800ba410214440d0709220550501060f041504c07140e1807080544040300310890184543d28a4000003045000180d9050781009031f001007400f41610700c03000f03003482080d01040020740701c4c0ba5818456000d02401d001c135032480314125071050748001c00980b80e15204001c00c00241c3e039040342d049510305c11900c0765591a428650900b9140b80e150b40289803040040c40440036095011030b64442190307044441554aaa5030881940240500d282c041d0000001000201304a0b032036130002d100f9183c0c107071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 962545071 1250 962543821 962543833
    0x1806111e070807080a020604030f06020913020d0b0102010504031e02070e13021002070312031107060507030e070e0613092a030204060902130e150301050f2502030a1416030908 77
    0x1403003503544d20f00417030025000070703080104101043c40700c0c510080030352180a0242ca04016400091001d0440304207541c1d980c2d074002918a0481c00d130f403150410b445030a0000344281d240c5510090401c0b51454503000d00c0030f10f407141d4485020310920240707026002000400c0080d041c031034404002c5071040c40049000324016078240b030a40d4000100101100d5001c117100107107100041003100a428a482a144c0d0b01c0c00a002c40c90000c3c00034000c07244120016030b4000340283d0300b010194904440c44e841400040000310a201582c1c558003000540c80c400004042241e240d10f1078440198403207000303480350508454441240c64944035030072004884c02140c06000f0251146180d004030311508003004112036012034200620480c41d20020341c40300c02d98856030050458200401d09540c07040f5507402480c10500304000c451000312442000f4240380900c080305040452401941e0307031003400c1e407080503c550078400d83c07061010802120066010210142d20300d601515029000140d01e0061041c0c0e402a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 962546321 1250 962545071 962545079
    0x203150d0506010503071703031311030a030c0c0b0703081b21041a0c220801020d020d0501170d031a0d0614060f0d110604170a030e011806111e070807 66
    0x111000b1040c07a1400c800703546180c50b9501c116418000301801101d0703034901245400c8a90707606100da40c937030310301a44840d07203024041d240040c01d4210783c3d048101d541e02e081c0b04e000007295001103480d07844141c150003851003403c1c41d80c80caa03040c01140c00c0c0341d1409416034941c10700b801c41e11030541d001d50720400a401c080050030f04a095551812646084071400510420fa140d03540d003c40031002c0040c1c0500000c06a40300c005060070790b88180092030701190000b0700082407501034881c003030040c9541c1042d18019200d60400b6911800c580f40c4050030903854407807102c070b1909078500210321410000c004200751503032850008050460840d81c0070091140c0c00c00268030341011502c045840c1401008050621031507503e842220010140203500040700b400301007101071003040e203030b81300340b0700355000300010b05552400030000c85500400c5030403c00c1030301202c200d100041c201101910700c6420404400940045418078102103042c0b503506c1c9005000d00302c80c07410404111f034800e45209400351345d05541c031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 962547571 1250 962546321 962546339
    0x51509120a1406220c090219110f0304060513080102070b0403120c020309040e0f060106180603021201090e010b0d080903011d3f0307030506090f0a0203150d050601050307 75
    0x316030038250400c89549070000c20b408003c0003104544600c00a240d17844c0c40744a130170100d8010080d80040d550719a03905401c0700350004904068414990300501d031203808148502c0e243d0141e88144021b0100102d049003502d0b8081c01000080c003184002103480d00d0160030482038410f029a07081d40450003100710714010385a03034000e028a9144a80046207440c001c00d041c0030080550140440d018000c0e400c01000c28001404524000c055a64501d941d11500b03442c442400c0322550b0000040c144100441000401c41030035550450f00500c400040042d00c41c0d0442e40509841804c040e44100464501410000650043c04000d60294001c00000d210641c15001d44c000c1840e800040d94007026948a04100d0f04160b4010701c00d50400d82601d04000000405148a0070303580402c08160100802010726458429940d010788215240d82c11400d00f00c1740c0c10070068000d8071a44070f40ba000000500018410001c40e811800f02070700010b51400e5500b00f40e521f446c000e005443c4203014000001a080c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 962548821 1250 962547571 962547583
    0x21b03030c060c1b15090706110a1101052101081b031903170703060303030c09060e010c030302090d06060302040f0b060a030b011b11030f070609051509120a14 70
    0x741c08002e005507114401018030941041801228182d01c640000f02c0c204030510060348004040080d08200e828200d10305410204213400404c00c01c8070450404038881743c001340745403415401810300e06201e03d9410048609119880c2070040b11506100703840e569101d082d036883e04803040350050704d206107140b00a0561100a8030030040d4158803c0c3c0e0701201c1c4840710650399011f980710b07003000d0302051800a220150482e04407105070100e56542c10800c10305405000e40c9492229919100740400e0422801800c140c180c2500d140c108a990640d0f0742c100b6000340d045403043c40c0d00034656110040c6618245000e850180000ca0040f0f007407a2200354120450301076150503580041100d4141154814110020005030a00f5030400c040081a4064084000c81d04000385014807400002d24041c0320900d485c2c6440380c000c00006078400841082110350041040c02541c0013201d214200c13003a05284104170b4020441d10b0390b4000c081601001400d0000a0342d6040d0501c1003a07000d09001c030000c680750700c0301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 962550071 1250 962548821 962548837
    0xf0102130b09040906050c130e06010f0809070504110c19080306131e05041b05010906051303080c07060917030301060c0807060923300712021b0303 65
    0xc80c40c26041c4103000004000c0d01c00080c024000165202c0c2135140c60741070f1441910000800031000900241c40d07503420f0a0b03c0013607e0864800c003a142894800281414031b1052410200076140012070b0241900b4045000105801072050002d90b0100c0007001c0103034440c411100807071061450307018240701c00d03655888005070081841819541c900060154242c00310b030341001100d030358042d0030707000e2a105a410984120308aa0006452415107041403040188500b0603a2404d514103040000342c7c0c0c40034006080d201c0703511308251118800c1035503a07098001c40e0001070958801144203d080d1500203465000c0701c0c401d6885203585039465400c0c0c41011807082459205400400c01400014052801d070440c2030f00c5403650302d16003030464407510112a00c008085998000080c03540a00c1580740c0101d99100822002401da902d83d01c500c248602c81750300700c24102c00d00282068034940180c45081d660081d401010101d07003d4240302d80251181d4070054800c1c000b001240414125003030000c140c0700740d070b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 962551321 1250 962550071 962550097
    0x1c171003020105070311012a0806090a1503080705060a1107050c22020c011a011d27100f0b0405060a0c23061b090a03030e04061a0c0f0102 61
    0x1060458004483e00d500002d01a024011703040d0038808142000d2080c02d61540c0341c21100801c8110402d600c50b442903543e0380310000c10000c8401d2080c42d50f034a4000710b4001032a00000a24100141c0308a50210b0030341e4005490034502260500900101081892044086110400249040389202c00007401015805085940807d03c10021810080300c2a4404d040b0864060020040f411801c0c050742d20220805516944a070a020b0f40011000c040501c244824240340d0000000c804400400218020040b403040342001840050400c02a0482780500c1050b00400860b04d04940c0104401103248a0034503400e400c0724000469100142c2138a064800c02032420f40b0f081007910080b50140c0707403250255041e1186510842d180c1c44079100d4440983e4500000c0c002618040040c00503403002448074440c0fa003c10403c900d00c0da41d1310a00c00307040c0c03985414000422591140414010030f00c540161190345180d00d42000c1c00741d200c901401403078120b03c0490354072031040d0301402c1c245d0003480356134000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 962552571 1250 962551321 962551351
    0x5030a151509020c010e0d1b0b04080f0a080f010e0c03010e1005040f0b090c070f12050f070f05190c0b0702010201020c0d03090c080604020d080c010209031c17 70
    0x11036280d0000c09041814802151040ea160940002241d1000103015440d80d17540c5005541d01c0400e02c00d00c9450101c50230040c212a15000c549140001100310007042110488001010415403200340c1d050035440ca940652a2000a0800f501d100000d40b0340c8000765072503c0001900012101d1010710072003071120b027107003164600344294814900141c0352000032a003201008c00d203030300e4a00c00c2c0b800035440380402040e0122594248a00c40401400c00340d032600b020486480800c00110003045611751000f00c16401e40b00b4420101d805000d01c000503070300c0d040c0001700c038024070846000282000d4010015070f0b00603441044080703425100a20000c118040c003400802800440001502c01180180000351424681d080e4071820500d02c280d400e000300743d807101e030f040a00c0120305c400c0c800b90485d080105494289500015100302003c40000c0c6860000540245060402e40540360300820140c1103610007495041c941c8900c0d003513028454009240c000c10003640f510a400e1240c02032403104240c001e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 962553821 1250 962552571 962552603
    0x60b0703080601030e0a08190c021513090515042d050c04030c0b18010c030c0611040b160201030e03040e01180207120903060606031406042d02120105030a 68
    0xe002203006141078103141d5120360314072081e401407214071000d034420301c7e4242d503e020707c40c00405100301e0391902c401008a4030504400584503041c40d040c0c22a41d44404c5034491052841c400b041e107401e6004001d22320700302400d1200c1190a82420312003820129001d001c0854146031070482c211041892603030400712801645400681ea5201c00e8000820b03041c0e032440c0c143c80362100003481200c1d5000385c3c1d41203c005002c1c0c403c5110804686082d04091a0001404803d602d00902c01c2d050aa40549940c0c0d41c1d5829610081d0f0b0784003200c00404410b40b01e144c413103a0000c1000301d0000303404800e80c0400e00b45545902c188001008850544182044402c03099003044c40b081f18000c0550300590f480c543c20801c1002042c41028600c1e0804442d81d9400304040c11458400c054038110b603c2103041c5410042c1900c0080840c01c1c030664000401d95000481104503400f02a03a1040715080701c4000005070315401f4040100d400034003920140c80d01402c0c02da41d9410500d075031f035601e000000d44800307407031070380d000f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 962555071 1250 962553821 962553827
    0x5070204050402130c0804060c091d090a0c0303083c041b121403070305030115020709150509090c01051903150608041a070906051e130810060b0703 65
    0x15030418000341044c80501c02884005085401407084403000ca607030803080208119807070241c108945024940441c0040c900146201c0d1021900b10381100700030060b000418010302040603150b0142c006e06c40700c51840d52810003501151040e904004a41c180080d5603005607414038203076004000d2162945460700c21050030f401c146901900841e8042d074203823032140c1d0544a400070040030703010344407101044038482d2921168450011403241c100341c00602c051004250400140d0341115107001010850f0142903170101e040c411076800489541c1d281240c1c8004060100c0d4403042a9901900c480c810713621750f6054103940e00c200000844c0014400c001000d290080340039000003482e000c0c10b020542154020f01013202800e01e400401c00610400b0420051009141030700c1e5100001d504071188030f05001200600300d146a014000500100144600602d146400d0100070408078802603600c9080340b000c044e100c0c071040c0c4602002071144a54441c8004454450070007119030206a00345400616075081d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 962556321 1250 962555071 962555081
    0x6010509010c0602090402070501150e09210702040501030503040810020f040605130b0a0c030e04090201020c01110708061003031103030c040501081012060e1b331303021f05070204 79
    0x3c031003180c4c092200c2c10107910b075800034001d40c034401e00012a0104411a042c00b1581465002503000500e80040c00806500419901500c403907040f032461021a190481c9407803031141c400020340141c80c100000003402004006802503640c1a0305842070402e01034421401c3e409102c040f030b040d0100400003009094002c800528000d01045900b200d00c0c1c1d641c0c6030780c03980703504261040808103090945a17000c065100407031003d0844112010003807044607400003965102c1c180c0b09103049c48084141d0200300346c01081003e004141c400d00701c030740902d00882c0b05408005140f00c11404600c41c0140c0360003900000c400d8a114900d21207005d0b082c10f00d06001103550100142c0442d40003007810300e012030450720840c0c040780351034010a0085100071050110f1450308a045241e06c44418aa0f2440c0075950b45251400710101d1030041d001440c80440301400007003005040b01c40380702d50000507640340c048110700b0300788084034000c840b0002c1c0e520302107260f844a81911454100020010081c110041c941580300b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 962557571 1250 962556321 962556323
    0x317181605130f1503050f070e0f040b180d0c05070512120304060f020f1b0102040b0d320f01080303060609010c0318090b0a0b09060f2d0316030506010509010c 70
    0x201e01c500d81013400805131110358005075083d40005110084c1c01d02d0421141c4001c04c010040020f6518003003040000585019000808054151010480e03035076002082e80f5507100b8080a480407203000c2c00024081d80682c43c01120315001d4000c0005580c03404052407400e004440c00601102181400414004d50009000300c0d5034070b550310001d1039050b0b281d1010b000748404441110783d135111030314042c41140b0f03010501d00310140e004202c14050743d18001c040c0c42410601c01c00204030a61054481d00820540354506840d840480b084608241f002c42440390160641228a540a03600c6001582e1284000c561b02500311900b00003e003030651082c000c82018602078908641124400071900130581c3c11540700d05c1c0c9542e00c941c450001071a2003030340540281407141c0c025260140c80404940a0b00400030440d034003800200316480740e00d24000f01907040390301000405c0b0840425004600d0f00b81c005880000700c4030514203401448500902c2094001d8005840349030078944003800441e00c62a510f40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 962558821 1250 962557571 962557601
    0x30b0414030f041707030201090504020904090515071404080d110f070b0c010b0604120201030e150f15100909051e01080c1c030801030f031718160513 66
    0x14400000c0406001a2610b00d95030300e40c581c1d8440c41d0081c0c0144161690340d440c48650000002000181e0b00031002d581281c100781d030b015031a00d4194000030b00800707480700040c020340038281a50781c0200c0250b80e424400c041a88509140103000000160380340a58006e040c0703c0c0d8440200c00002034003c0344000080d0501200f21103c0105217021a805d000859000000160010480c8420442c0a000d000d42c25042607554604042c6011100c1d090f40c001d4250182c1855a00c20000b0504101486451180542e5501102260074070f00481c8500741011920300051507960101d218071444d04141065200c80305580c0c1924042c2010f003103800a103c06800c0111840300c0300d00e00a1200e041d000064000e050307200161802c0c1c074210f01404500c03003c2d0040201e0f1510194041710010390030540c140d065981010107804004503d00d07060b102c032850f800c0c0f40c0781081070780c40800213680c00d107102080110828800b0b40e03401c1c08504e0b070b41a60204c00390007a10340c800c00100c09010840b0090f40485c200c400108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 962560071 1250 962558821 962558843
    0x213020714062707210515190902031b0616051c09050a0605070305090628110d03180215040602060708040c09020d060b0c07060905090402030601030b04 67
    0x1944141c41c070100100c0c2035146411150401c940c102d0400074040c4009510540500440b032500d04071521140341d4058070f201030040d11074403101050705021092000d5400002c41c0c0301c01800c03005c9211180c1c411503040d142c03c0411400b0714505000c6001c1c00380030990280040005680b01981e440040703050030340251300070009004640d00980c034918039101c0d850054002d080e00b40e48034400071804800c0c0c81459024025039803010415912889501801c0307501d82d2138101c0e100c041600d4104d0381d510030a0792490340b00c0e801181840078034070002c02d48800701480c00300c103455581d14228140c405004d034101255007900724845d01c3c02d45074020b40000e6000141146030108649559000400c14144d0f518540e5075494081070070b100164041140640041242c103142140d4a0f00d80d440d080283c01358000c80c01d9058020428a191702040c2c1c020741701805223554800d481e05e1641e1411996a00c080c0b042c1c1d400100c44030b50000345070921500c468007a036000b40141c01c190b802d54844e201d0341000a40100c40c00d500038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 962561321 1250 962560071 962560073
    0x204051b03010605040e0a020301030f0b041b180f0e06060f0310020f1218030313080c07140f040504320d020a060e0d0c110409140102070611040f0302130207 69
    0x20344000c0d03010307042a4503840e4646082040346e500c5d071140106001d001601c10401440403039400c03030850103410383c40100d04c81e10740d5880c6001401d10343c0700c0e000c8640d020344188021841c40109009000407902451003001903800144900081d80d4900c40c401d001508000003244036801c00000b50419064042c0c21030342c03c03040e400411012a07006105809054101117881ca014145001425400200d20004c01401c8400340b20703100d444c0d11014003803080d500c0d80c1046c0e1390104100002a1100104c0e0174060300c0da940d5071005160b440002078600300d80300750b00c1c00c20719411500c2e10740316450046411004101d02c0032441c44807580b0b4030240c14080782c0141200360007090000310401a5a1800200f42d0190400f900c46261103401d50f107a194194016402413880c1120740c5070300c0011440810342005e1003144c2c00319640d001c1401800f04200182003080144500403034108150000c0c01824880c00042213071044030802e4880e030780a50300911030070003036245041001d4a4000c41e99900c0c8901150014030700310355 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 962562571 1250 962561321 962561371
    0x60303040e010308090a0b1e070f050d020c030106091401090b0a050607110301050a05040f0209061c0c180204031a0c040902070609060b04020a092c180f0118020405 72
    0x803d038411120300343c0020b00d030801420302d02807860050036000c13110303401d00c5d0042a01486440810050031030312180401c002c0305001d002581100c0f0b65801209503142c01035041d9000303480d1700100400728000e41c2440d6001451208a22420000742200b5441c1e64159003041c5120001c0c0c91407806880d40702009400100309030faa0035005091541c4a17070080500140b00a080c5425108010002c1a069260004000200380700300c92180343d05904803080250740d82d07581c001600e0201e041c4c602c0c44003070305000400820881c40c5070011068a100309090070090281a038010164856800000c2400e86004a418600d004040c80c603a000060645c200e4145034940e03240c00101e810440381980c0309a111070800090002030f200701d15042100765000d500c1d007408803402900169951007004042d03408010900c0414540c115561080c076010481c2e03400340e0818146803910314440f42603121841c0a05801c203590104144640e10511080080020701c1842640800004040003000703070b29401002c00f100400580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 962563821 1250 962562571 962562599
    0xd0503060301060b04231504060c0203122205120c010f02120f041d010b091c0f050c0918060403030f1d0f010f0e10020307050f0a0e0f1e0906030304 65
    0x1000218420451854088040f00c0350003280040740502400d0b2003240000031f400d01220107a40280c00c00084202140c8042441c0c480311100d8501050000b0609101e603100c20800039000fa05640880c4030348940703800c10000d010300f501000041c1c41d40301029548495014005a5807200024010360b51180e42e03911308001b095000d644406121100010188800c01c0d6121011000c0c182d103d281c90025030411a035004144201c10105124034080c6980110b000101c0d40c56488950344400703118034541306031928940d11841806c07640c1c450200800082d40801c811000703a603e00130200020081a101e540341540188243d2004082a03902ca0300090030385815118840681000300b00281201d008890a150840e4009c41c120710000d800d00388044204000040c801c2c10074803d000005076283c860b40c0c0e060702c241c454968195244540810960480c540120500804100640e000200a88014204558400000840a20420203251142140c1003216000e0380c000c401404591070507445030100b4030010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 962565071 1250 962563821 962563829
    0x403051221070807030f020702030102070f0c0501230d06081c1803020607320303060a06030b0108040b040c0f03050318010c0804060815040207050a02030f0c030d0503060301060b04 79
    0x101002450340011551980000311181c1c2041c241c500364240694020a81c58000d096002010f07180d14019030030794000c1d030445820a40c010000c6503912441d01e0000400310f0126019207103c10f500c81c0010302540500710822082c100c0d10881c0050300106000a4456049034280c50410340e0f0700c1c200400c0075030080101c5103880101d640e26001b1010701c0f2500074800c2c64a00031648060303401003003c00050300e8001c2942c4489030301103014901c4248a08400c0d11151200884106940d0100840010144048000c6004450a0700e082a0603030300c407601607068406002506001130729400008000c0b42c04010080d80140c40351030040c14591f561041c1400c41d11080e00256103d8000041d10000003840101401c0c42087c01c0c02d0140d20b030719160f01c940030315000d10b100d04018408203800081d15400c0040da41d001224000300f0440d154205030a050380e440003400c401705c1c02841041403058643d0400289000204c038000d000708010607250380129460780018005580640d21654003052007085d080140c4007074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 962566321 1250 962565071 962565103
    0x6041205010f0b0a17010213030f0302010b0d020108040206031b030705040e1605220f0b0a032019020a050a0303050910140612190605010f0807150e06040305 69
    0x100549003016801c554000a10304480351034000100c007a52030f01100401202c01001d5012800a51030050a0180c070a562204a08919520000c42003192908a101101d80254000c01c9803001d00014015240b44440c000307408140c810002034018a0505d000b1940160580503a950220041501203903075001034070601c1c0442c0e0046400c0c4440380c812625180d00c0308205805140c0c5102c0900094018426503507a80744290410703105619031100781c0b04a42c014000305007484a03d903030310701034944c0907003001c0100c40000742010054081d040a4520840b14061070303180722841c240d0400012159a54015403910541c015a03140502141c0241302608085000752000700311481c042210a003031424440418812070314180c0c40051694100d0455030380440c0035608908246403041ca40b51078044101018541c0902400c000d0007000324503004141201d01c041c0030000021380b81c00056465140901414000030a81030340c4210561003584c001400c007101400c1240b4190b00c0b62600d40c00c00000007903007075003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 962567571 1250 962566321 962566349
    0xb0120211b15040b100b0d0c0f08100b0a0c0623070f0e10050c01051005010f0221092e120501050d0f02010201060f06231213110604 58
    0x104881c040c000c9a0348000c190280810a080440d440c642081c00341000e441c01c11603500048551003200805800b0740a40b0340c01a03241c0c07a009941c2c5015049500f46240040c5900f03510440b12405407070074074020042400c0c140b07007007400c0000c00040c9812645c10a0104080c40716080081034980c8150070f090426003441d0360000c0c8d0000003000e04020090700800c208055000c0300a101d0f640a00360a02110080f41e4000180302d0000c002c036414000c039074480700e0700c0d481c010034041d255081c2054941141c40a8907080305007640104240e803034002c2c4908208241030440100001c00394020b00801d02c0400040c482c54031882c2030864112164400002c142e0381040411504202c15040031200b66176050001c0705211035070604010807141454240001d100381100034845046a000390081d80103000d10440c0310000643c0e4000007004103580c4a1480424a00d00b0500305d903808241040b6000502118115100c54880100d651000c12141c002070394000840d183d070b208075030348850081000300070755100300d80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 962568821 1250 962567571 962567587
    0x519051609060e090a02091f1502010207032a0b060402070c180b090c0f09420703090b1303020d11120601050a051c21120b012021 57
    0x101c6200701902da40001c3d8400c04a900050751420340d11540003003070b0443c01c40f018003030960041d802a0b494100fa807270300044e0810070521650540c082c1c99014003035a240c1200c580c0c00b54440c8043d40c54400c10103070306414081200041000d040100b5003110300504010b10700081501c0d0742c111401643c2040b03036003841301c1d04d4079a5444403900405a501c242103403440b955040c199000c1c2081d01ca5044071071810500460a5074007a602c09a441d2000c0708031150703815099042c2d4514081d0000714401100c4109403201081101d94140010340d145140e2544076408001e06203c3c0507162038101c07602c0a0354074440182c4c08001601ca0718844a40a031145c07503010500002c0008000030014105c020301c481d80c0c0001e0042041d513980303074200b4044070301c2a81e81c3d84030740088010103c1d05080401c806422a49180c1034115800f80480b41e10303804242a94504c001d00890000b4030050783d104101c014005903101211340382d14600d9480102c2c3d042c0011044491501c40184414020390180280319000040450901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 962570071 1250 962568821 962568839
    0x150810060e0f060105040504050a1503060606020f0c0f040b120313061d011e0c02030109080d0510061706041d010b15070f06090503131202030d0804051905160906 71
    0x142d085840503118078554646540020b100e80030b517109843c0b0458481c4045000c0c0310302980301802c2070800344c4084851036180c0c00c0080c0a06032500c180d40044c0310f2501002d10094010030002a001e41c0241840d404054540420015080c0400010381c01103030034022210216007000100007468a44e40c40303412440c60140b010700f84161200c08031020000b690090304460b80c2c03100588200e4404590610700741030445000701c500b6405208029015071a0580038001e0006540c058984d02e02c1c9008184019a241400707040b85244030300c13503d000b10351050a071500344035844100941c04078010300005051003a510031080c80804a00703000ca06659281d0001c485030500a034250344e03d0030500b901c1841d15510755584007180d00c20203409421303e655041060108807050045440f2111450443d00040b51981c4035100595a4198101d103e031256000003414140074a80052281e0782010182c1002c03801020b0320601c110319600100c0b524010752aa640c101210040f011300605405140010501d041c04049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 962571321 1250 962570071 962570099
    0xd090c150f090b0a02060708100b0a020304090501050a0302030a0f020402070b040f1208010f210206040806071e08040f0c09050c0403021207050913050f030f071a010501080a15081006 80
    0x2600c05040100071013018560000342491b04403025140c040d038070380e885203500107051480782c019035503c890001d00002c0041d4000302410684212100070442640d0f100d0130403d05508501c0029010b42050f003030703075011a45824030302c0d4015002400140ca0403045030341d60b8444070001c4504a80c1130a441d01d20405010046400d01c4403072001e070410015950510801d03a0302ca8800c5d103e0f14440100117030701401600b941010500c101903000d06044e444035101c4005540b00c1c03c040762040001101050030600200754909480c2c082c0e1200d440300422501c03180c840f80965078105c0400d5444516802e4009000ba1051080ca8030443d419848941c4450951041150300082101c44c030503190309c50745090040c0e985070303d24550400c4000f0b02903400c01c522031400b079007025040e9803000360501010803a05020103155006166003481408200c019150454092600c40828002d090000e907500c00040d100411940c441c80413030b04411000203225944107080762401e408c608038480c049440e010104046c120b10550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 962572571 1250 962571321 962571329
    0x2060f28030e010e071205032808074514010e0301060e06101707050d0b010c11040203060a05040614010809060f13150c0201200f0d090c150f09 63
    0x70b102d20310b030740740800742d4440041c000c1406d00d282c40d40a410410400b0070840c1d505241c501d0003482030080b1620658100035200000b0000b0546500c0020185840b840407100d940051102c100000c00c404d040c00340ca0b0403001c01b100d0322641120000a9001d80740044450000c00017100c04192604c02ca200040920200c008c01600a03810403505002900c40b02c42c11030f51001c403c1d01d07040d0781014061030031070b480089490b00d42402c03403007003041c08009a400b800418200010b5407040c44035001070801180e039040100b1000d042d2595890111000c0c0ca4250021070b0003000013004007515640380c0700000c2c00c8400340e0f409880c0380290343c2601006540c10000b01507010408602070302d403519000c01020010b0704020503010b0b1413a10b0b9031108042040319502071400305841e50080001100907000a4001c0001100306513069450400d0b444501c2101002c43c0c9041202d0b1b4180c40c10418050000340c0079100c14881201e4500d40200c000c01e48030503a0451900310350306540ca441c21824401d00c0941042c10b213400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 962573821 1250 962572571 962572573
    0xd020d0b041a0d15020f030109140105060c2e0c20030406090303051c09030f200a20061c06050406060804020d030e0a0b0d06080102030106020a02060f28030e 69
    0xa005490341d0f90b669070982c02540c200181140c042c0c18002444000d02c5000951000c1c12004400407c628026520980509580e41107141c826602c540411099004030f19400e221980201d055818110442104407a0380383c8100c401d441c54440b4a0440c8295862040d0403800156040e0f085582201034003001002c1d41402070107907251a00b0f100e070050010200740006030034484002084c00c1c03032403850203404115001c03241c001c204800d59483d0040510510141c00c0c0700281d11004503164188c82d958064041c50314040040c03c255549594503180382040e44403200c1d41500c0188500c41c40d80f00e54000304400b21900915448260088800340100c8100d0f4001742d000b1440d01c0c03005d0001640000725960401d4040b141101440010720f401c80700e03070440a000b1034008002c40c0d4001000d070a0140900141100c40700c007480302075200c40b070031400c0f80400d21401005a1103141c107200507040600c000d00815508551140c036007160001500030a4400720f21804094420b41181c260403541845001060400d01c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 962575071 1250 962573821 962573861
    0x14011202030601120f05012a0e0a05210f0f0706020a020d080d090c03080a11060f070f1e090e06030a0c05121e01050115080f0c0a050d020d0b04 63
    0x1401007607861505005184448841e28205024411000c1c00c02074440d038410000d002030181309000c0c44c0401c0d103444023003800c45107040b400171501e03005004841c01000b010b40f2400c036551600c81041400300031285158070000321391074440d100250038000e2054200400b00200a0012290201c52170095258044c10844d0003440f001c0005aa54108020000381c00201080c2c5901e64100140b0040c08441e41c01005c032581040c001042125100207000c0703100c2c8584490810070101820985c072120700b00c68007141d070b005c1c03400010780301130050454000315011071810940c1d1000000d10380d403ca005610040001c2203c0c0b0b0810050040100441540b204041c1e01800240e006903561901e460882d0044501c201e040e0044109040000c01480c007211030340c048201c1342d15205403122802000203005419a032040c0070f502041e51801183c40c0350041c200e20680d0000c1d50348000706002c40b0307006901d40800300141000a02c05113041e82c000740203195049440002c40f141c101d0100001c464602a650b10003c1d846 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 962576321 1250 962575071 962575073
    0xf24032013290a0302090a090911041b0c0807061815110a020c040b01021216020909010509060a02090418030815010e060a0503041505010e1b2505070503060a140112 72
    0x242c401c0d51041c804070f09026849402040004030065595002a4a054a4012414140101031284d0032102405072000c00542ca0100340c0e21980c4540c2d241124040341c02d00411200140321790001b000304501403400040e0344503600c090024204080041541c021082030b1000c101d001851141101120b50990001c0c034140544c10b0181d1500e42c8650020b204a546507403d1080e64024000700390f0060003d41e66079942c80c3c00d02c00d0703440000000702e41640a17180904c00508900300500c81c0c28001c04c0c901004082d1a9101700400000c0e50000c011150040d48914401d1041c200e40c4a646034403074031944481c2c4040c507207a5503001019520310350b154100304007840143ea03191502000c841e040d105030318002d03680b5612820003030500c0c01e40507491040d07607281034000240340711480c40c000c2c00b880c0d90a9071130035803820429000c0302e240640300b403083e194600c01e080110014040201c202940c0d11a409440800d551500024101030044074266403241d00c8842c0c10070b0014804403014050450269208007442031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 962577571 1250 962576321 962576399
    0x120a0f030b1e030a3509150c0a050d0e090a09120c17160510050103081801020f010507020717060912030903070f03090f24032013 57
    0x20507111045001001c5065811945042c44030200e180e82005c040c41c888001c0c1040c0b121140040c0401210341c04a104054070621918000c42d244201d004149407203415890031a0552507100c60014100c1e4418400d00e80d00040040c02950b04035202038403103a07152400b0200303001c2c5141001b80040180f621307204501000a4a40181880c04111850324200c0d8600398a0190004e030040348a00c0000c000c00b040140344012a09a0000003070b1041084c0c82e4400001039525064810a0100400c102818051880e412442482c1c2e509283c005204680d00e02c91440500c50031500c0179668000143c010600c140702101c3d10b504240124483d0b01c005007100d01d031420340c1d55200d155501110411050000200300100c0d4104140d91f2543e4001150790301c44030040c980a08080c0c0c0521406550054103000055613410552003040079602948094503071520246084008049410240e20307101c052a002c1c0d0f83d00c000071409800c40821580050301303494202000051030040851001d20f1003007403000ca011010b0a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 962578821 1250 962577571 962577589
    0xe030903120306010306090e0607030e06101406090415080c0a1802071a100905061c14011d2805070909080403060c02010203190c020c21120a0f030b 65
    0x1441486142c03243c0703a60340100e0280210340d03c144001410425403203145280443d10702c0c050b07102602c0800407071241072002611000103c50f00c15078815440d80400184000320b0562560480080c42c00b494020808001811543c00c01084150705544480511803000204545070010700111820080d142c60410030601c02001c2c7c4119903609130300850b5803c00c01000900760700c211500041212410b28190140c04903804e02d034400d030172800d402c01000c10500d0400c2c14203c103640c8c2220791034082c00c1042e0b4480d21520891941c59081c5996102c021090750602e00c4603026405800002600c1d184400440c0649070400a020140101171014180c4000071800038040e8100c42c03000303d011900303408504102e031032401a640041c080a0410445c070b916254190300440c4180b030382c7c000b20304030644a00507007002c4031141c0190901503800705d101254070307180800035100201007043e45203000c444506980c07401c0448411b806101e409c808114004002e4010903080c03078100d541d14003002002211000641000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 962580071 1250 962578821 962578843
    0x14090a170315120c06210615093106080f0c06030105091312030507180f09111b031917010302120a050d23040305150709031b090e030903 60
    0x4603080c1c0c1c2c5202c3ca4038240103280d44034000801d5107441d80741c071501603200b1044840702400510051400145107140040c0000340da031400c0c0e840d40d0300b480394503418000060362099425072210b1402070380d000036230090502e6501d801a080c8002c150503140c001003030704c5e16102141040d034980100c02546081d443e81800e490464508440500261f19490500b20381142070020103448218061032801070b19405403c05801641c2a0740c4003140d4143d8010000949095401241c0d21400b0700c80e010080507426800c840c0c41446150913881c83d01446112039070b020754010b503078030041c0d03000440c02003441840d8040c0b0a00340001070828034120210b140c00f6018100050100070310400c4078900005609000b00b0004440301d80c041d049941849444c1d001412030308007464000304014019200c8180f0310303003a1003035400301c030b034001c00070804080c00309130301c0c01c141100070305680400612000c00004a07030800c0000c0c008010305603040d00900d04002c4900c3c180c070065046d00c28268000c00c0054819140028160000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 962581321 1250 962580071 962580079
    0x190201110901141c0204210b0708060f030616021c020a0b1e041505070c0c0e04140a06021e0f0a18080d02070e0f1b0d14090a170315 58
    0xb07030000c3c0d103c03030043c000c042420403007040390798001d030a091140c3e00500a5407901000f0b025040c1044030880480b03504c4c1d150040c443d040c1d120106550a02a0b4000c41c0c02040c0103040b524046100e20200e8075140c1d040f80c150b001d14941d02000030390a501030000c5c0485050510651480c0ca20305070012350340d19400100249100c1100340011083d04642042c02c4855592041c0096542000d007070294140304420304492072030b8600004076850324007480d202c03108107a2002c6a10041c0d89000000401030800400590341c1a1101c802da14a20200b4040140900d108910040e01c4050700084050301032083c1c071b001c01c15914100000340e014400001900d40700c1c0c400d440e12800858049408007550081c6034000516842043c481e4160b040c0c010030350005444441919400960b01d0070041004048181d9040100c44198403000e40c031a12200c0c000c007000d441140c000700d00c54030710641803c0719030011a02c0b207501c2e030049100581088440d850140100c086900b00c02e040d4140404040603004d0011110361003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 962582571 1250 962581321 962581337
    0x1090c0804120509090c0c0d020105130b042d0507120b0a1d010c0207140906100f050f0403030924020c1905030304030609260d0f090b0c190201110901 66
    0x700b0b4411400c541520a0260200219007031504c021011b94116000c60805802180024800d461051056601c0350210207030181c03a1140c00c2c0c40d03008500d40c02030400c1cac8041c9400b50010921030702c034000d505044e60318010b45d50f03060f06035030500c9414040030307411842020560411070004103407164101c0740c000103421000100301003503544010811074119200122542000f41c5c0341e805640100342c4a040310054903041035400e101c1802c0080c500b074200c2e141903000c48641054480c0034460301851110303d0071400c00600e091400c211144894005502c01c5001030101d14041c403009400090b550421222840000c03155120140d02079298100d03078400ba801001e4031017400d42040610098180201005001e0700d903a03a840e818000050b2a09040a80d41d5644051407088000041c1302e01c92000c290040c0102d0900c1441040c2ca8090042030040003516620783e80c08101003000c6c200c1c07407401b88190003005030350f4640c030b021003c402925400307400095924188039800c010701d00790102e44602c030003444e254403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 962583821 1250 962582571 962582603
    0x402010e040216050601271503030f020a0609200d03081f0e0405060702011118092701090302060a06050901030b0c0f0f04060905090105010509040e010b03030a031401090c0804 77
    0x6064883c10101400921801c1c00008405000d1000d540c110040341090b501d24150320360409055900789140d0300c40c12203030b4440400120340301c3c402844000c03070944103440140d28252104000c0c0c2d0b00014050382c004c01d41807c0c212107024611b0702c0184d65442594924140801610090980c800040182c0340000620a45200060a12075450040c0085080e00400c60509091141e9249821030382d00d400740d8a0005046558502c5001b40c0341903541e00301a0340000e800c01c000340080312402800f041d090030542031a90080000c00561042a6045030b000000d40007100e040003480d0401c040d243d0441940361003418483c98461020240c1580d0304140d162140d500d4900c1d0100d1680315000c100c403e09000414000200380886006108481c51550340c0780c949500c400c00c21195140a1107940d02144041000d60701c1401c3c660800c9140a060800011b003070302c4043e003c6425548000c980d80006a03440c1d16414040c60602e9603603005d06603c090801c0540400d00c006420300300080d002030005103080d00410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 962585071 1250 962583821 962583847
    0xa05060313050718021201060801050a15020a060f02071106040803040302060304050c030601030c060e1504180905060106030f20030f0a150b0d3b0c0d0c08070e0402010e0402 76
    0xf030010190b00109001502000368000c00940080300e03c0e080e0040700400000301140b00b03040d1039040c3c620003013094400394503004002401d02e0240081200f50302a0000b9940403411500c84e401202101400c00341e41e90050b4901400721f400081681442081c041c407040c09802c40c00819642942c0e4141c40041c3d80340c8640c00c090303103415186a007595240c0308250002c020442610000c000b20398890b1650040c44521004010200c00b0038160000c14402c148410068849800358248140115640c00a4803902c1901c03120f0400c2401d130411004031751a840d030340b510020740d417240304d10100710b80c00a600b4080346101c100c46507100103031500303007491512000300e600c000003944020804418064844a10340e59001c2e0080b003900f0000c0018001807134000701e04e105401c8051007600c804c040d84041d035640c60542ca10110038201d00800b0703101c540702e002c00c2200c1d9911074851994955014542007440a440c00300038918060042d0401c2c8603000c1c03010700f8030005036080b060303013802620100c4000d621014885111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 962586321 1250 962585071 962585083
    0x140601110706111f020418020306010c030e06120702010501181103040b10171f140105090a02120112060c020f071208070209070c020f03010902010e060a020f0f07140a0506031305 78
    0x600268a450002007138030383c3d690081041303030650b000408000304944840b000301c1c00111000750206190110f80d038000391003041c441c818210b000f020582050085211400b28040440d02100903030354800c01404415102011b0340454100c11806011850030304094200360300001e07000400c414002400324030329814483d10324024004000302e04841e522800d4510340e0b5141422030110115501a40180310440d66001c6c40600541a491342c1c0072592030102800b006000042600a11344d5090100003020050505a1402014100d142c200b03140400d003884001c8030049105c0400395844040000e06d4004003103942d030100c481e0010505c0c024032403418411020710a0801c000e6104603110308218129402614401d00ba40c000d5032100f002c6107240b4145803c88000e440007901190b80c0002e80c840c07030310b0802d00070310400000b4230680ea0342d00c42c284440c6242088808072000c454009081c140042090a84a008102003c40c1d403850300d0362802000c00c0c00c92001510020300b03040d0000e10f0100307015040002d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 962587571 1250 962586321 962586343
    0x90b0a1b022d0a150b09090a0b04080c0106060306030c0510171b0a0512060406080304091805070b0d0522080d06231905100503130b01030614060111070611 68
    0x6a8041c18010715064807032041310740284c0303007462030815000f2180c105a0f200c3d9201d11401001406440031949a074800e4607001003084903c401c1c104040717882c031042805544020021901c0116038079085151414079000707260480c0e401048103e44141c446540310300c4030040d00b40881d00705c032070341d4031040098500040e03c8000d50705d9510001902450481d400001001d00c150b44c0c002c0710b42552500c82c02c0000360742e040e218140040d0700500060000700c21561040c0360540740014510707010001c680d03034281099856031008000d0880400c144811507140d00555a00c28524902200340f822a0718a0144400c0f01d510080c211120114a001c1841e500f540224094800f20411780d6039003120884549400c20503140050184031420303840012a140d0294a03000d84e074005003070b03800d8686c0c5a4000c45440d00000c1081c1e0001c840341d4800e8000c1003511190398040c41c02040f011030814100c4000c000c4010000d018a410840c1618030b84031144000f003402001c1e00c406141014101c01c14508080c60403448003e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 962588821 1250 962587571 962587573
    0x90b0c0d0c03110604080d0b040632180906390c1b12070311060c1f1b111e011517010b01050703051912090b0a1b022d 52
    0x424441802a010047c1601124680307040c0301e4070305014144403d41e0418810b800004c04c0c0c050740d01800703982b200b40314000700c500001d400b400c0b40f003c02d0000f4070300c4004d4401490609500c40901c40b0582d000d0103c207030710420264034200c402c480384400804003403041489510320314090825042a0080004641d400b1000d2001c131510782558282044411012568491080510142ca094500b40108030201220742000c018000000315a052045a0b4459441011180a0b4030786549046038044240007018218072000610f94071000c02e521301d4000c01030b0501d000d01c01c200c0300b40041c4000001703803113803035040c030b06041000029204140d03405820403590141149901705c20100394100c002d1031142d28140b01500900038500440c3c010764140c0310f14031000e0300003442003000401c10025100c03181500c00c40c40c54881d10081c040003400d82111050002102d498600c00e05001c07a9124602801c144c0c030810301c440c00034903026070102941d580007050b0000d902401c030040802a103292400c1e01c903c0380350f201c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 962589928 1107 962588821 962588833
    0xf080111030a0b01030b1009030c0e150d030504050d050303060a0f0503070b0901090f0608040209070813060917040b040602100204050a05041e0219090b0c0d0c0311 72
    0x820341c03c1c0c10b00d0303110500740c0900e031240400b00b01c15520075500c541c28141180703440c1031180350591040340340203003900a200b50f9144250b1010000c00040300c0c1800c0c01c901c9450180e90038000c0e0390119510480720b00302c0c0400c2c00800300080d0321400c4110340c144881d5840e4001280b84004a000342074165200150501032003813001d004000340c0d00e05041000303141e039580b41d1300414540c0c960080d0001820300c00500c402c5040c1168040e40004842c14036100c1031034101d00d80e1460408560740075000c0740d1105021424043c501558400c412814500c0995171502c0d9001c2c0303480c5034440d00c42d103401485020328508212280e8400c1d00c0540d07000811003501c2d50b141008000291034410f14054010034080415101d9440350b10040801340e41c9510051080c0b00002405851a107041d80b001c115040108440e04011a011404041d000391500700395222108038241150101820344450b8420f100b0a = true := by decide +kernel

theorem cover : BRFrame.Cov 962410071 962589928 := by
  have h0 := BRFrame.cov_init 962410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 962410071 ≤ n) (h2 : n < 962589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
