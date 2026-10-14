-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3548
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:58:41.691975+00:00
-- url     : https://prove2.me/submissions/a9ba59d6-cf61-420d-94df-09a4df338fea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 637949640 ≤ n < 638129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 637950890 1250 637949640 637949657
    0x1e0c020c030f0312101a0f070203070f1d1611011b0c1a150402071e150c03050903030c0c070e1609120201080412020a2109240f 56
    0x256014003081c0302c100422000b8503542c01003e88140c980e050b00522202903105108000d000a49104402c501c4514290458541d41d946a02c5884d81501030000c000750705210b002008202c0c42c0c2d01c3c403c02401c440940c0750106c0c1d916406208039500358401c891101414a071000c40c0200940720340b2a840303940100c0c000024142942540442d44520ba00d900300000c501078500310780421060307014110f40b428a00b4510070b41030800845080100004e400102d100e990041224810702c000340040030a40603207020818250721061030148101d0540340c112031512443c24080f51700e031600038060207200f0481c2e140650300d9541c5881000c42c02e5000001c401465100c0c2e60300c00300d151888140c7c154000d542c810a4030080d0700089800074040d0107076400174800c1c800101e0040700145d030030525007500194080c15840941c0d020303420484c40e00d400000043c00030301031620b0741341d505d01001100350b501031401c1d0b4411107001d445541550f40101c0c80c1100303403214840300c0a007006941c803030040c0810005840c5000c0d0350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 637952140 1250 637950890 637950913
    0x114100318052a0909030a0302070c090203071d0a0e010b0705010209030a05030c01062102010e013c02060f0a0902011403010e0907231201060905090a0302101e0c02 72
    0x14041c500035418115035000c0e0034400343d000d4140f40c440c9022004075404e145500d08291615124020400400180354000c41c7c1c0310b040081818070503014040c4c805086440f4900060b000300305442c40314060b486420b038400182258180880c12805403030500c100594070303034640703480038504d07500054082e14555401c1c02043d107266014400205418060001162640c10110900c0c0c21a0f81c141c0c022031180054075030004505115440000406409003400200c06035950010380e404140c1c00c0b03030f40b410001400704042000382d40c000319107801c40c50710800140070008118181e903260825140c4807064465400020360358600d83d00943c111510601d440d540300c46000c69400742541080c2c010403400039054040150034507081012000038403120303030081c034a003480380c11445250030aa581c240c0246800160818401801d400820060111034010001440c0111000791640c0c0548411001406101c00d2440e0407000f0b40200303901032540f040369402ca8036045044100504002400d6010f5010342040d00740d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 637953390 1250 637952140 637952143
    0x110f03011d010b0a0311010c02012f120301030201020a140a050304090506030f060105010f2d03020702031002040e06101115071826032709011410031805 67
    0x41480003403240c04a9507000c8078010600303450045003080e0048038032800c104003094640c50304000940003820040001032040c00102c6561031032486518080281c070b0f082620401010510340c02540800d810703904450154202008507103c28400640161702011521021808004115050351000400c035030741080c19548490440c0c00c1540f103943c8480e56002042207600702809403190300441c12022381943d46c10f200018003800d40040b089420424179560b06154030481c0720b114500360064420004482e0082d00008001e98032081040317000c0d028940c40605410306a0094600342c0c1c13600550380541c0ea032450140907a8140610050301008070141c200320311404148604140180281c02880d00703403400d104003405090703286100c461070410101003000846210071601048110242800340b48200c5096841d1440c01054080043c0840a156070244503900c4001042c01a0060f600d25582e030b0380e1561251201164000465013100c5201a01800540300707a000c18804541402c000f81260300645449 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 637954640 1250 637953390 637953401
    0x4080703050706110a051005060f0406080319050f0a0507030e0603100305010c020703081603030b03030a051305090903120406201b0111070b0402061b1605030c030307110f0301 77
    0x5a41c1c03074114090500c2660790140d42203508624200040040030010307a40c290340c68060348102d8880e00c0e038920100d01c05a82d07400d040203003c100213100303108641d25144119165445a00528620300c4aa2030000d4458002e80945a800c14540411418800d100d58151041c3d40005000c400700140401e0140c099544c01000c1d41c02a01d15543c20f07254103080d45010741c21174040028000c1590300c50001040060381000440d84005c07850074408180c1070309031405401814100180c60307494000421501080d561204c0940103c55000c0902d000c2d00703aa8405106880e10155180085500100502d641155160070b14980052080800080195259142aa0800743d05070001002c3e0741c0042d01c80d60905040109104001aa43c0200440b200b01c40c49100140f0400f5001000d5040000000c3d065603070307610584030390600b00303611841020711701d4407129110709000d500b072400c0100360034011070039007000100d10342a40000340041d4a406001d1300e030180300000c0c04410070703440082036100050684082c001c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 637955890 1250 637954640 637954643
    0x130608060a0b04060b09040b0301020c190308070e10081803160c090506010c020904030311030f2203200f011103061302130504021602090405061f030c06050f04080703 73
    0x1402940c1010302080c0c003560060b4004900c228140700c01400a03c40c00c408440e01628111400217002d800f0340c1c0401e01a0168190b2903005000d06c00005040d04590030a603500d0900ca40e0b260307200380e81c07021400c0d50712588809040c1c4d0003001022881243c1401007178083d402150480404000b00080009140380d540300d01e80243c00f5280c102c0411081000e01d5146070042c0c060440c0901403881c0c981c0000788240819200a88103000850100c0c0c10b0502036402000205002c500c065942c1c82e00c3d102c100b90b182010390b0f0300c802000004821b103c410102c2c14480c0d0055600d43e50351400704084010f050306903140303101c40c1c0d41540102c00807201011070034440c01c900c142d54590126240e107800d0040002010008014a41c890300402141400a50510302035040d1002203600680f100e403d020800304003c03910b2802500301c00c58100388800e12400040c5207101d440d00341c08418481100351b2001d4824201840001d03c408540d10007488182d00480c0601148140c1180c0c0c2c9041c10741c1ea040f0185408050f600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 637957140 1250 637955890 637955893
    0x60617010203010b19030b19060212190c020a0e01030305031006110d03270b0f010b0301120204020d1d06040b0c07230c0d0303050a230a0902060c1006051912030806130608 75
    0x8d040007400d8040c4107115144a5002803182130180440040c810740b03e40034038030410002c0c104a26030443d500c041c089005812046124180c9684a1074040c00540c826200001e00c014074881c0000c0d80780c81030701000700d102640c1001c3c1c1041b12114805601030503910302e03030940d1001c44404440b2104014141d8995060007410151a00e082c0300c540c0703146d9103c0c1a000344e03003410340800050140b485005028880c070307035050fa0010790381c1151040b001f0080c2070410f8041140ea078852008040c052000800c140902e01070310007a400c0b0b45a90360004281e00c9012001894900b0081d030060802c0d4501215014610101d025039850070701500000318480080e84046003c41c0d0f0b61000d0cc0405000c07403040480d00c071003e00c0e409084040182000400c420002c040c0040f0a8450050b10b0454a401c0c0a07654000241011114141c1c4001c203684080d01c501d0203800e0040880071402d03000d0510500c5ca038022104101c582c400261010f8500f205e2034071009204c25085440070400c850051018441c1400a010240 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 637958390 1250 637957140 637957189
    0x2004021c1b0c08040b03040302010212190c0503011d270d0810030308041401060b0c030a02010b0a14121f06050306070c05031b010612060617010203010b19030b 70
    0x1904042802003000080c01084144900003000076002c0e821135041e10413a416617510303942e0340c1c80d089029103d20701300c00721003c1c040d10500000d40002c5030226419407203a0000d00107101c40307000c01c6031240000d11420340249142c00e1001c4010128002840d005156500b858000b031030014214051090048105103c507800918440741c10340d440340366aa005041594440340301461618007c0030100c1c050300c05020003105845a0b0384501c002d502000c014501c4460050701c40000341c0c1110303183e8008500c0400554200b20300c01d54949041c840280984990803038103640700944e107051111440740d1030200142d5104140c070f00d00301e0b01d0b500081000b04498885010461504010606041000282c90304081c003070540c52034400520040292264500703071012007440303054040780881c00341c065640070300d0b0400d20461411082c002070760002c4060310f8003400ca0081c48440c0e2545107080380f00c04d2240e03000c41c2c0014018490500700c0440b1034001e0140314a00810300341906400140340b02141100040764001c0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 637959640 1250 637958390 637958411
    0xa05090f0c01031e09031e02030903030a081519150c020303180105271c051005060303070213020d051006080609181c14041d061207060e0103182004021c 67
    0x30206149107c0291014500b005192404641d8a0040c107101030148030b0740b50f0008058094034400302210020042c1040c0c0407280d0b000c840c050741c4005014042c12000311070306880200d4060900d604070643e024004611340301032001020300310f1900416590411004114000b10341c03035004c94294050900c8400c0840041c00b403010098031000c1485009065200d40150b14045200850f1820404d81a2032022505a4800000a0440c440c89400951040c1c0c9a02000f903c40b86a43c041c11800240700c41c03c011940360b145000805c62030910a40000035070440008100d800c3c01d0000b1500441c04144013170641103242d02c41c608028612240c00a8420300b0404519655401440d50500b502050640303440c0504001110032007041c014440c180a8101e5400300385540c8072030900c1f95420303240106a40505032281e4000302680a0032401c00c0c006410061803002c10780d4050800511a81e0180103814880040030124a00750300240300d00e0f51040d401c2c020301210085000072400b058074040320004100700721 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 637960890 1250 637959640 637959677
    0x3040809031f0c09053d0206010305010522031215060f0e0105030907030f05160f0e01060f09050906010c0605010b0702120304060c17041d0a05090f0c01031e0903 71
    0x43d2414403c01c0480041041940c54061182c213107014000640d402010aa5070410444ca201602280c01c1c13410181c481c3c80800c2d404a0000e0690784500001e1000d074036607451051070b840381d000440000325290801800001e01800001134910020030b00800c8005000749007402c0070f0195844a030110300ca68072040641540f000442c012441c0900317009082d07080808089954a0b05800001c1c0b516403040290420b110040090a48207036940034050040e54a484503041c49c291144544d03c1075800810002c1003940c0540940982e0400c030796181c81119181c8810070010501c007505683c1442090014400030840e10301900b8068100a4003940c1c1d42c240501c14000075a0b00345444042070b810502050241c254000c00340446079401c2032010206003001190001c00303103c1c0e40e12110902c00c410604403510081d050b5000e00c01c0a9007081002180d0303540382c441c0c0c0c1f00c0904d0113005031030b41c02c443c1807090f00350b0084c0e02414002410030050841946040c0c4101c04a90300304e40180c000c2211100c1c0c00c00120070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 637962140 1250 637960890 637960901
    0x9040e0145031d04360b0c04050a0e060f0409030e0a060207080c0604080a0b07110102181005181005040305030d24030803060d1a0f0708011a0f03040809031f 69
    0x206584c10468401d00030700d007000d9038504200c42c1c41c00c01c3d0648500003680890109002c0003d800203000d0310313581446a02c0741c41c1c5900c14400c06019400031100040d11105440c0c6152080c24080c010003070040d0f1361004c000051609402c118117215482c0403c0d040d680320400c81c1c1010380010780080900e075041040461401040205042c41244100418000c40c0300104502e8440c0754089507a0300e20f901c9181042d90b803038150603003011066102080d0032616141c0c03c0c4003203040482c143c4800030140851941100c151180c1654068800000428180709040402e80002030444074903010382003e4aa9907081d00750b9000a107003001407922144201c079180d070f41c950742503001116401c0046d0700c1841c40d40c406a0074007001781082d100f492501c0142c1c00b4000c08181e0101071304980c40c8640e0b043d1a00800880030550241c1c0c03c0d43c002190b00300085200140c1840c3d076013041c810600140c0c00d000c1c0140b10a0855400103004132150702051054829a8408000a0300b503182c11107062a850001e920b441003c858 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 637963390 1250 637962140 637962197
    0x105030609030c070b2b05150f0f0d02040f0e01050907060903170d02040b160c0e070504030204152106050a050106050306011d0907030209040e014503 66
    0x10820000f120a0780e00014003541140c40c09189a515640b818520341c0d0401d40000110860039040202c540c12401964031a5204142c41104201c00141d06030030b12261600365800700c2c0d001096050086000d00c1c1c00d0054601c003500c010408a008000e40341031009071f07100840104500d80d110703000c1c084007010501105014040c24600610b641e442c0d07840340d402030b8020103142404c84070000303003209080ba4140c0444010303040c030081d81640e0390529881c105a8840c00342060b104e002e80d42801249101d00342003102c1c01040a941d0b110f09250440e003c110081c004540b10308549440d2050020340c03000501c50302040c0d42c5100e0300e01e41410485040000c16120000d01c18414189800010300403d41c11800352a00300c0d03400c1c41c1c0360f400450030380712036185d109111800c581c0c00300000007080800c542c10740080903801810b072001e11051070441d0400d400d2340c0c00c805034498404400103940c0b8404400442e41400301488103607030403105c1380c0301c030780344105408000058001500806651242c4040c4001594404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 637964640 1250 637963390 637963393
    0x17100e102009150f03150909150121020a1d0711060c030403020a061407110f0d0507051609050a050609090607050c0c0604090921140d1d060105030609 66
    0x9141d035010402144504180180324600c41d545080c94800008140e403022008207580c20364030700b030086c143c44480001e80d203041e1060107014009061007502003003078450300f10b84400909140e4201140018a682000d0102034200707a0400c3c00e82c00f5a660359000c000525401d040110001842041550300c600002e10f018207102c40b507400d203983d9200008910754400c2400c002a500da40f22403401300e003088050704004c1c10f007a00300108100c9200901ca8428040c1031191100c60604041c1c1d58241d480780000003090300603401043c02629141d001d000200200c610034022356403800c0201103e8030b43c51034242c02c14550305039500308001103048244982c54104400304e0380d142407440c002404503039541e4000c003900f040010103d1040c1092904215890000134002c0030240c075203807120f54103c0202540d07602521007101c06800d0121b060039214140c1c2112041d50342c1d10301010080803100b26240e101c0001c64480f40c2e66a68401d0040d4400c418200311a0305140240c10254504010585003440103403410b6003a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 637965890 1250 637964640 637964681
    0x20a051506030d170601081b0a02160807030b0606030c0702030d05070204060e0c0a12021912050a050106020604030309030207030609061a011d01180519080f010605060417100e10 78
    0x480704411100341d0f05c480709103843d600d142e4511143d001c5445001c921035070609000700f143c0344081e030081420410303a441042c08110087c0c0d5500c100380e4859680c400640040e0036200824401d0808500640d40498800342d9103140010a03404a8501140fa42c076650000710041900b504524181c00b4000080100e40e02402040c00c10321910003080c450310f03005d00d041c00400504450f12140325010354001c24160400100d07405c1c40040040d100e80341022201d00304918240000d1107a02c035520803281600c0c0c1a0b40100002e075104d58041c1c0c001d0011800070750035172142100000018180d1701a12040502c00c40d40070911400a210f0301900b0060b41103180c0c107200303c419050000301600d41d030081c01000e003444c1000b2124080344007005140e400340c2026800040c1202c0340c0307280304540d202c0c48048a00d00c0048484050901080c02e00301c49483c01000d5001c502040100145100c840e00d41e01c6c507100b02c03026519502c2e08003a042d001c44102036402801508001d410105000242c45603a400c41041c03605000f5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 637967140 1250 637965890 637965917
    0x2060306010e0a0f08030d2f0f130b040311030105011a0d020403122708070504050703150f05010f0207030c0504050408040305100203041106130306020901020a051506030d 75
    0x50200414050400c112100184030070742d40c05400b400144119071380c8800740c0f9220a070300c03030316a031060341c414201d00e041104c00da201d41d6188003c0d801780701107121002c442c00302510250440d54003602242001d0b040a00c504408040680500d200400c00e004030241d03250305c1c52070207070280d040c40c83d0340300c0c03082e4508001000109410081c0c507100f2401c8842d455903800780c900c0308500a010b540c002501001200c0c2e40c2100880c0c11043e000240e6000840074084000c0c0320000c0e015201e018010070000c0d4220302c0b0200404d040503000250840400d080100f0144e00e104050099880941c0c032042c1d210012003c100810f50308580d010040f142c1c0c3d803001c2d000082c1941c0b25091441018450b5600499498002400340b208d0102500c01642d4008140c401284c030440782980a5042958140d40208400908101d20325000003200c1c1d20f140c50000ea00c241d0351650721a40000d411601e041d5046d07008000c0b521000030414081c941b21003010180b01d040030f0034280185803030902c4013004503080c01507002c0100d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 637968390 1250 637967140 637967149
    0x40506061201020f270a031a0601030f15030b0a0606081501050c06131109071e030b060a0804060f020a02120f0d05090309040c1d09040f02090c0c100902 67
    0x5030310100c1550700a55030601100040c0c020700c40d030072a802c0318107030114490184564402405d900743c601c200700301648081d004104801c0d018244002811401220894003004058200c9958410340c141000200b02840449010940d0145580800300341009541401000b0a07011116005030003440f00700221400c000d030107403c01300003038602c1d03010a40f040d540b40000d0384140c046540e04003035030b4103031089402c0019019804440852007103442c401c44101100302418982007892040e4125618402da014040700302e00c118890240703200e0300b01a00d4080072600c07500e4401c01060306860940c0e80e56818580b5041c10000c44403100c00100c400d900402c050f0b00902d41c00120809a05080703c1420b40d15000d485500025224201c0e18010180c20541005990300004c03014060040059a06001c0352540f110216003500b0303409a40d4040d040c4540c03441c200d0741004220154001d2045800a41041c030a030005481e003d02110407000781c160000750440bd0b04001d00135040c076080242410301c1820820750005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 637969640 1250 637968390 637968403
    0x4031803030c05012f0306030106031a10090b0a17070302030106061d040606050909071826060f0a090305070b0405030307140f0304150915020324030705061c060602070e01080102030405 81
    0x71703045001c021020070202ea40a510031801158007000704440395113510410700e21814101c8001c103030b080c0d01c4030000400d00d8040c041d41428020080101303050b1400c150030040203403000303510340103503200c1d00d0404401600c007442204003030001901c60202d13a690000e0b150030f080701112000c1d400355083c81401c00c120341c0c109099aa40c0b420843d5211480e581d007102c200c0300540300c44101541318039a441c00284c005422514000e1850060300c4c808440481494110340c0d905094403042d0b03101040030006422655160302120013070744030b4500a45046500e0301c44500b4907000760340988460304000207000c1e0307458210401d244248100454941410302d20a20340f500d41c00010400350030b420004240c1c0603a403465a12a8a03802c1c1c0c01303c8036015090450820000a41089501002410290110941310461500c242d0703950500280140030050030002404080e402640c04a4206e603080c001da0344003240a40951405080154002c00c1c2c03403031811041c2c10355150103a21843e03c591040040c04081000071940 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 637970890 1250 637969640 637969721
    0xb0a031707051005010303180b18060c030f0706230c09040515090702061501090323150103140d0c0b0a0c02100f0b0307060e01120504031803030c0501 66
    0x44035140c0000c2e0800e1401c0c9985038414610182c0703810004020160000c0481004640d21001a5010364545900e006e00744641c40b100031079943d072107003412610300c1c11200501ca10104030007a20308006140b80c442c00c603074229044c2198580e0f04c50301021641038020015074001e40041e0000240741c108022a0640c1e4840c0c00c07202ea0140d61180000b07070040303015410710042c1001c0500901c2c8a4a0f00410003034688105580e80100b44a03102016040c03980f240d25030f84c06880d0080c18400c0b0100b82c108000303045c40d0501056180501580d00b0300b81411031003140d214000c41c0904c1c104e680c10104482554182043d042c500c00911058010701d501103001324442c1a4041960300b0f0019000c101100140d1600b0070215003042c003141800400e07844140c503900200c0000c0c1050b0100c0b0141c544030f40e030a5034030b402204007250001d40c0c940c192000102d15508020780050080c188900c07184102100d0007074400301c9800c25004125000002c00410809120f1030242803003809006142d50752032003400000c0c0f4900c2a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 637972140 1250 637970890 637970933
    0x140610020a03120f14282c0c030d090603060515091e1c1106030603120f0403050d35070f05090a24030614010309051f0b040b0a03 57
    0x1300303ca10742100394007a038405403051000c5481032800035a01705500c0940f00d203049a9560345149400e0074040d50041400c105c4036008400c07003500c542041140102c20102c050552845000c103c3c08441c0c400f8040e0a203c14802d58070381200d14100310700901580d83c01d40c001c5002e002c051003640052040d4a00b03072112180c04450303800d4030840071020806036030355181000b54040300b407600142c0744040351004000c007e8410003440e0002040c0750b042100328001140d0341d0344c06400036030311500103008203401411140880e4001c47d003440d480340c640c070740b41880f150303031200c0400d1401c90940c0728000a09110000c83c9660440741c0c03014480030004404283c006840074040c4070b02442e000d4800e60040094811001000e8807e000991b51031000c9a2089140c0010000e10301600c1100d80b07146110b401180140c40403042c0040c00102c2c1d210045009050b084025a01070059400010740c10183d1190b44407109007a140110b81405d0580c04c002c00c580040c03010512a0b81000401c1002841905031800d1340544000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 637973390 1250 637972140 637972151
    0x5091f060f0e190503100b061204020111060405060a1a030703021e061204120f050909070905040c020f1009050c090703230108010507080402030a0b100801140610020a0312 75
    0x81080e510b002a4950b50380c0c1c442607804070329440c6105090b00600f142d07001c904031400849016401d004890b040c03401e40740c000b00100003810520014203400b6800510624000015181210810f81042802d4170111040e030803050511214040ca40211030710b10000c4241d10000511f0000081e90364445880000c2c080c010300c4c0c5040c0c001d01c1c0e028004418024016040641d1640d500240582c60380302201c0845d0840a12180240701e28400e0303484048040341030712001d16182e91070b0100107000e0300007421002040f1082030b02050b281c07550300900c900c1641a800a10b506006100900e00b0070441c0c503c0c3c0d684161401c8005008030f00001910700d0822170aa41200494899075812400b0b0143c0c200c075050920380c1c8956444056150050b100d04aa030701c02c0c000c01403501c603108200c45107401038030040c0d8160b002141c04004128040c405603001540f203a001100c0c1c0d6516000b050030f550070742c1c0822190754851001c100003800d0403c0201d40c11101c40c0b003e0200069a96009049418000303000d0104a030707640d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 637974640 1250 637973390 637973417
    0x10f0c05070f03030302071e260f0c010507080609060a0e090106051009030302010c0914040203060d020a060f02100c05030c0c01020405040609020301170a1709010207170705091f06 79
    0xe2101c00040d0540e03a00c010089600c0f414085d0196001c10700c119903481021231502d989074040e032552180300d1b5028204045070015030300c00c01101200c4007802c91122008000000b01c600d4410020414144d441e00046114500018042c00a620040c00f41d0b000b071084c14200001c9680ba01c0b810010b84414540241680d02c075229428014025034010310381200701d10303103040511900b262492007160f100f58000d00c01031110000c2103039028101d104844c10840401c0d00f182480c609900955404080540040c0f41c03000780f030300040c03400d00c1c655204a010078030301c01d0800e103401c0e41030064130000301e0828005e00c81c9064400c8010113510008251040e0b0102c04120300c2d003403e00030b4040310018403005000740303d00758840504400a50007882500c1d031115010a04000d82040424850170054010000c40b091105045080d90f869100c2c180c118114081c95101080c0d203c40500303a800c40c0c000b0600281000ca081c103084c0151120060714251440300c003c2c00805a0621305907a580980d001441c0014142070030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 637975890 1250 637974640 637974643
    0x70c050a030b010f0801020a051e1c0606031a06030601082d371802090405033c0702060c06190b04090b150f090106050c0c040b010f0c05 60
    0x19400856010341004400814401840d0009041c2c5000075101841c107995491390070f00301e128101d800e6020603003c0c450380f032070140008403028030401c0906106280101800382900c039560f2004482404984e0354900f0301101d0390500c02d08181c4028101c051400c011440009601c9000040401c1c1c10400e000700014101d50107041b460307a4000700000c4aa000407000068600401d84c2224411440d101b4469614840400203080c190007408001c3d0b40e4041c0b09210a1540191042c01000414440701c192202d0060300c0c0d440c0c07154401d501a0020f16140c0704c00003c00b41448032070300300b028607296911001a0012880010300d42c44006803c3c0000e03521740040c404a8002d00030306d0965003072801003078100111200c1c1000380b021034a80000c000c11160f8210001c000c12503203a8503014000002060004034544042d448038074074204028141d4010200000024644d01c1b003d800460000d01e001c1910314090358204100c0020303a07012074007800103152420000f01800c0a2075400c1c801c00205030903030405e2000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 637977140 1250 637975890 637975913
    0x3060b010203210403020c010f0824030d02100b01050c0303070e2d10081b28020a03120b0619030605030706200102040807060c08121009050711060c07 66
    0x76030720000b0307012040007541143d0a140031101500940222012021a50b1007001c0c4c84003100d410343c6079441541c0340d00006040c0010748440e21050440711a000c00301c183e070300300421508000107500605410b210080d01c401550480075200741880002d00030954090004000d0f654004d43c90300c0c200d282001c0c2440007410b820780c50904041a8a01c040c458445c4012003180007110300819280c00d001045460012541c0702803c8545d0030300e01c01c02201510501d00500002d0201c503c80421440e80d05099080c2c80440300388400019015a008a02d01da00f0980c004103012001c0141d400100450800c460100c0e116215845480c1d1700c010358184880c00445c043d5000c0c5000d010080d0803101c203c5e0321590083d0518440303101803580c4202400040e090000140225020b80b8041006040f45500e451810f0b6400740c0e0300e21080b01c0142007440b010440c1e68501700c40a00c180f40e80007080c21120703e04014001200c030050150010050380541300490031a000400940225461400795955a036906104c1100c02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 637978390 1250 637977140 637977157
    0x120c0812190c0c030b040210110304050d05030c03130501080907030506010302060a110d201b06070507090f06050a0b03040c05060313020307080c0405061906031505040507020d0f0c02010903060b010203 88
    0x1e660f4800f0050128406659104d54403ea1f045500c154201806039165861780340b0428460340200000c4c40141018010203020500c100d003100c1c103040616018038115005100b8030b14250725100070410166900c040302d150041e1000c03001d4003403641181c481c03d40340d0b00140406406a500001c1003a07190344181d45500c0120248403d50360020084400106850b110031250385914907048021911403a0101d4100101805a4140070041d56520b05101d0b880e0010007042d122070090a0f000203030113041e40a1b00101d4003103201c00080550800f410044110580e4208081c80e400910810000448040402c400e440b02241e000c0e0b10790f0717a0110000b40c15078409000075050f0042e080001074800c0f002480e555809401c54041c0125501c180c1030100396240407503080000e030400d0700704001c0103001354040003039084640c2c2069800c0740c8442c04602030703940646100c00141c1c850707000b058400f0351054003001512040d20301400400c0381600001d04003106408007401995950310f070500c80c0d84c020821203030001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 637979640 1250 637978390 637978403
    0xc11010911041d0303040f0201030e0703050610060833040e0109151b0f030b040e060603121603050c010204380a120902030a0c120c0812190c 62
    0x1041841c020a4007100708030700a010b0380c10310210740350890451410b0b10000380840c0c011810740e0b07501e84942c00581d2681c0b4069040c96541c00054100c020140200340145000300000d20a5080241c0403010b4240194003450030402174009000080c5000380384246100c1c05070142180c40c440300c0d400c9101614004414541c004e1800343c000b08000c4d0103400c190030f00cbd4021407543e481c580c210303240c14052343d50015429018503104c40d4580b007090b0154022100b02d030340310701e030020321501200c000c981210f0708403255450395030041c030802005160030040401c00e0003a0710005030800030200e17001c9443c00c4500200a05002d004140301d0f106644c2541507400a01c805103010703120501040c2510303225006015080d101220341d04185000c59505012540c00c0380d070035910282c4200813120300340000c051300e150403a41030040286403004146d0b41d29149014002840310554290620711b0601c10884141c0d1054181e90404610840e580001c1d409035070440d2030307206a1280340708106004440c54210300307070005c288 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 637980890 1250 637979640 637979651
    0x60f0f0402060a031a100f091706011e08160509060d0b190905030301061806030603050a150f1a100809070501180801020a030c08060906090c090a0302040f0b1c12030c1101 75
    0x1200e50200e0070301f10110b180e48905081f540c0360032000b02118100c242d6100c45502c2407004206466210481d905a51703541926030b0440d540301c0c4802414400b01a01401502c0303902a8140080c1c87c003e61941d4000300c0448242c25048540d80d10040020340042080c0d80b43d0604800311103800b2566082007000307960000c1901d90380d40c2c42d2080035100300780400b61003201080811002c60aa8080d02c144000d41c0c7c0c00000030540b00740c06645002c140707600404100b003a41d03100c51034004640707518010415011001040140345015400511a409480b10542c00411002d50203104800341d001c0f0b42c05082d59000e203000740e2981c8980801d0b412013002d90303104040940c400241d103003084e82c0c554002908074070300c0c0c1d07a040f1194407024100b0001010a40b40c0ea0351021145000c2080d4040d1000105a96440a0f00c503001141c0d90b07800140846950f06960a111919032010311018581140010510703c284045000250501d484e028152812400382006041c1c0d21201040d1503030081501c5400b265510009010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 637982140 1250 637980890 637980919
    0x70e06040815130c090b0609060a0c14010b0f280b04030201080c04082e110c010509010501060c060c1b060c0210060602030d051017060f0f0402060a031a 67
    0x240c0e071100c401c521140440780c802040040d242031861071405500240045943d90400c50304500078190b07046e01d503074480700400181440361218000f8040260284c1c4a80105180c0390504610003040c980e1a182142d00d414020700e840d030386001c81071400c80002c0e194511600358a101d040c1411182182e011001c1800c1400094680030800003001504e100307aa80550f292541142940030380114040e440fa2a040712448903254a40782c82e0415800c1d015003540003e41d10840ba1580440d102100d039802c002c00c00003462280310300f09000e2030350056503400c000c20066245c00380090030111200d00040c00c00307440b0b55940d08003d02c41c420003516494140707600103840d040c1c1c6c50054001d05420480c9000750040449010b010030303091040c04100c03480340c4c014514051240462a00810f80100106007510340c1282c0410704010f2607206003409200d0b40d0081c0244d040102d9048007420008103810030228920003080016128101602c5d06410b030b034200410f0f4660703e809454090b001d40003d00e600308140411450 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 637983390 1250 637982140 637982143
    0x203101208030702010c18060f03090b191a090711010207020301290a0e01050126010801020c06010f0f17010b10030b1509030d080601020a06020d0b01080a0b1503070e060408 76
    0x6000300e203603400130859019030702403d4600f04144c1e01700f1f40c11001190400c01c10301c4d00030045600100c103c0e280020b07804055070350f000e131141ca090b520020b161844492892040d0540d114003a8514000e000401040951200160000c0c8009181400304840840c40f0030398480250141c035100c990003402400010f443d0f001d03481840e501102000c1000c0c03005220864281082580d080c140d036584120075080c0d07800c00005540e020750803c03031070103040c0c0001c01090903040018901e6000e40800c5001690b90b48081c12050701c1d010301a0000501e10001483c00c0092a02542030f2030112a80c2c2d0300805202841407504a0040c803845032055007000819180c0c0700d007254554400041c0c001c085070165500b40800207100c002d4042d003480c00740c0590003100100381d07050081010580c001b805104803010100c0075501d02d016a00031680c80d566417515140300803c0d643c0c10400e09544100c3c4c1c400100700100602c000036400031900c03d8400c4400303c1c00400f003000b603440380d000c415103c180548180e541d166203502c1107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 637984640 1250 637983390 637983397
    0x903170304020405060603040b0c03131703100f080601090f02070510140106171819080c07050108071e0516050709060803072a0906171b01120203101208 67
    0x40f03100f1480c00002078810310b8aa4140c0e4003403600b226000f40b0654804403585100d41c0f0140104103200000041035002400c41c11b20451a49014481c0030f40340c0c10700801c1c011140352560840b84c0d602070120f10a0100d5100010781d10304440c003000c004900f0702803910710741009200340300e0041c3c000c2c003034101810044085034000751421900c074400001c0d030760b980b548101c901072200102d0781e01c0303060340c10b0205200c0007140300d9840054100c07a0980b80c6504400300d00c0031941d0000b080c00c030303103c2c3c3d8041103098402c001800031100400080c24035240c0d6190041d001449032640c03540a55030b0700c440440007548288180152400e5442d4161845407a844a05041750359907410300c907502001d402c1c808040344d04100401039510b0b066010090013004034030001340f0360195440c05402c1801136807a15001804d02c455015146c02400603546203940c203418403500900704403101c1e032202162403155650040c0340e64400320b4982c2804010200503204e440d80c0f2031240081200d64010070941072060303c0302c414081140000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 637985890 1250 637984640 637984643
    0xf0e03071101110a030e0307150804120c0c05210105070903020a0902041d1905040606080f0a0321110a050a1710171603060b0114040b04150903170304 66
    0x20112607404440c01191040c50844201825400502c0c00300c00081c010030140c1c90401b0300605a8001c01d4840141d60100c6001d8a40d00b00000c4502061005104403201c0c07816501d49103142000c60094240c58400a80032241b00c1e880c011070304505054001c003107003d180030141003040000d00040c101401c00904481040c0402d0b44215040e9900044108040c802c1310106c8d140c2031062034416150b44c2c058010998014245401da83e02c0c130b0790486100c4154450f07180f04520071400004c2d094106420315161103809030600e04503034400304101e004079070003100c007203241020b01d01202800500640d00002402240a810041000201307015500c5900040a489010115a640500740e0a5403860780300320398003a550891424040e1509000340d0f640f5100c0100504c0240084900f148810404000041c030180d00507104207580d654503420035a03000d10001401c10b1010308950506040034a01d509601c128420000203100300003441c00140d010b440c000006582200c192401000101c4500100341e100320380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 637987140 1250 637985890 637985903
    0xe01110a230102040807050621012702090916030e070b04080d0219020d0204020f0c011a0103020702210c0a0b0d0b060408060a050c0c030c07080d092301030f0e0307 72
    0x1085850414140b013558200e507031110081a4451a0405008440e800b4032100c41944401c160703100007003d041c0d0032244c001c0584030502507010b41c5420350040040400c22202e0032103401040079182980da01a40150000200d080603200303081175607000c6c2c004002c0500711880e240103c20000829020501c0503100b10740ca03902c03d03203140341c3c1185004ca03240c40d581021459040e8007500c2c2c000150070420401c400d254030150006161150000b03907511950460fa1410002c0d0703460348894a5600503502d1703420304c1030a0a08055061640e80c0c0c0c0001d4481c80310340070050501064400100d0b890504110103100c030703034003d49100030407a01c8062140030b940c812001c0c0010301c0d0600241c004a0309045e81114221440300001e403801e03480300207000c40909005030044041b010280844d400c000000e00082c02a01308120040213003a142002c3c031803e08500c0c25140c0c0c02c0c01000c0001700101d0000d10000740504148201d050504800400164014201003808101e0340d40b40c8544420401c0c4004014031105003e01c0703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 637988390 1250 637987140 637987193
    0x60402040b0d08030412120e010f0e06010f09090c0b0f0c0105060a0b040b0901090306150302030606040516050a021015050906090405070603090606120b0708130803070e01110a 77
    0x706000c110b07600e6641c0103104410820000b008075148580074003005134035190050031081c1c0d80c83c1440035035000316002541a5518080301b02c1e03201452095154112044003c3c016035072510030050100f040342d22a038186581c980c2a46801c03c6020706094015004030061b4549401821070101000d4206550b002e21540c030b440c002c0384251801d1003001e000c0b60425119289081e00700b6080929641141c0b0040b8107210707107600302000146a078094199510080e110401c011442c600406207032003000f4101a020b140303800140940142da4184842800031241404d5030f076102190b404a2401403203a80b012044e91500c06541003601101c910002180c0c0c0c1100c43c820765032070703141c01c1240d403035001d031401001c80e0b2210108000c41d5000c0e030400c540b0740d8020200080c89070341d00c446144848005481c100c7d001c10400c420065a9a000890702d81c01031005000c0206c42541c40ea906111440094050300a1260451807607640341c2c400c440700a84a059101035442480c26860603090722203542d100c085401e444038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 637989640 1250 637988390 637988411
    0x4030818151204080c0c0306040501020c07090e0a060b010504170a02040f1a040c0e06040e01060906230d0b10080702010b06131221081009110315040e070806040204 72
    0x1c10303a20040c40c0c001e2903212503140c90791400302580c05078800c58498003d81c1340340045940d05001c413900c07850081002607074030010101c1803414141c83d900301188251501d40081039010000030040e0f9001d9001c02d00180c90400f840040e91207000e20750080002c40b604180c204002d007004940c1005840c4281c60621010950f503074040284d42655030440c8202c001080840071a2409800041400e656400c0a03550b8800c80360214840d80c3c0b182d040b242802d00038400402040b0350200c800d0340101203e00d0020200c8011407050648000c14000307800e44100081000d4152280aa000d0a05104000c1c80d0780d4206800c0c2101600440701141c00d00d02551914811182c2400d0074003c941e5500d0541142d40102401c020300321a44104000b07055030341c1201003828030590010502c2d00c0074500c126458504180c60148106400340714a030704051500741c2071140c00307080c040041042d03c0c1c109003180041503102101d0804140100002401c1b1501403050800001e103851010400758090741c000d5a0600401448 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 637990890 1250 637989640 637989679
    0xd11060a0203040206031311040f0b100c0b1f0f08160504050915150306010f14030d120914060a0204030b0c030606041e08010c0f0f140313020604030818 67
    0x203c1d8060340081d42000001d4078585210481c0a2441c070450034904034400c0003000c20b040b10420308805011075034519170040e4600d0111703040d1806881d58500900076001c1781d0b850515011020f80410701c241031300100071b00c4050f0b42c00c0c404000780108a44400c5419600c24880b9960a07003400c040400e1070360f0b00c401194a003010701a41c0d01c5507503884001c0180500c0200e40c003041d400000c0c47c07028a02c0c11200c060440d40e4061044a0003052140018590340e030804800d4170380c802028015900c241c0c002125000555041441c0c4000200b80642c00504c14440381064207241d0507100e221000390103101c00b0462203181c0f683c040c00690b4002c0e10b209400d07940b1101240700620003510034507400001030104004942c184e104001000f071041d000d14016035950454642952240314010b00414102c80d01514169441442c4a4802c240391a14203055000708440441c940f1020b0040d000d203440e015141829511207000300c82c011540300044c20340d1000821301070481a803e000f40f82d441150400c026107041e004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 637992140 1250 637990890 637990897
    0x20d03080f160915180b0a02120309060a05060d0501052a09030c040b06130909020108070302120601080a06031401050402010915050d022505010b190303020715110d11060a02 76
    0x4103859902a142c2000c03480441e80c4c02c1a01d80504100b151840820090910302100d0020302044510f9030f100e11900d800030b820229441c0d504041418240200201041c000428640182e03030802c0008450f11014082852200c6285015150350b00782410f100c07404081d49812111340c2400c28010303440d55080000c0401c10320640d0a000c0e4550b000920034000ea19080c1c2c00740300040070003403c462400c1c00c4000306402809042d403010340d80940d0303807850074199604425600d5000c0200c1c03404600d02a10201d0550034100301510040c10000360400184180c403d40c2d212802458110140707490b00140340014601901088404031b001650215000869206e44400350204070001d803500360908050140300c10027504888114648a0340d2422560880200080c0c1504050f0060002080b081c4912051000d6000440c504541c0c0046c131000410200360b000c01c6480503541c0c000d95080c00c82c04128011142810500c5c41003007140291543c03d55800c0e081403003006402030040917903000e565400d03c184101e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 637993390 1250 637992140 637992181
    0x1080d090501020312060f031615080112030e030c04090c0323031206150301061d10050a2105070908160f060c0201120c1d060322050109020d03080f 65
    0xa1080c469407405c0d807140f4050907441351016101a2145900e030002a2818008402000321085180300c20300010014030303907406815050741891915545800400f1542c00b440c0d12001d020416146d143c2601d940d400d00c03030794600e035500030400e0141025504281e96100030611007201c1d588000ca041c2c5541c804094907a04002500001031403d210580c6454410008020202a40708d02c0200c624020210b8090207107010b00382650350f801821b01750158420892034a42d0283d88282c680c0d61440040aa011049944286051401800d400c1c0c5104680403891402e07540031180c86d00b020100300b00540d00100f8001103d40402c01c0701c2c000034080e1110b400b200c0c240e00031685880504d14050040d0341c041e0359035600c0c440c810314143d402c5002107418601224000e48803100014040381105210300908a900c81540600320352491440c140b90109c1400c4802292400d13a508801c03965446c140070342175201e041503a0b00603003501c052085a1800070000501241c2e6100103848510100d170403010344882810076603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 637994640 1250 637993390 637993393
    0x20a1415011706040201080405030712051c060b04150c1202010b01080f0106020604020d1a0a05010503070608060609150403170a080a05070e120106120606060f1404140d060e0601080d09050102 84
    0x240c40313030340044508020040041e180352004204800004000800f00c400c0d5400c9507440d561070354211083e004d2411080403203001e4407424503c0510403400c14900300c0d422282026440d070782e54421804242e0b800450014042d2080544070b201c01982501900644aa490266200b10941c0c1c0d410682403c481030a0280380016480a0002801410080280081c4c2e0380140505480b0300740d180c0141158400880c2d00c0b03c50940c035800100140e0508010346e8003d0051802c00004924044020400502030004440d00c9800004c48032040d610f040d608643c00f65420100a0416010b000782680141e400030100400086890f40000c0a001c1503104850040d1001c1c4e55060400750a0320070400300410250105005540c1c5200c00607000740e50f84007119909104060215209103414000b610000b900d0f280d06080c003081140000441444904490980d02e4407c611220401c442e800314000309032005000380f54603c0c0c240c800c5802c00b80010002c0c12542040700700d0f13541070b101850803a54029103201d0240503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 637995890 1250 637994640 637994653
    0x6050a030b01090513021e0901090207170702010e1216210605061f120e0705310603060b0306011a1206030a0f1407080705060d0c020a14150117 63
    0x20f82da9a40c1109400c40a5400c5101c0c83c0300860300042c0b0107111105080030285c084801410712820000030720b80c01001406811420004145c956903000324040d002c10094000015042c421680190714204140c0701c080c0c641009401c500c2e14491b5a2038111050315043da55903c4c0005901c00c914003e106440ea610f60440040702095903604060000a0021688034080702d80005160108002d13807a0b414001c0e68514200c1d1080301ea503001220741502d0004c50607004103c00344a80e03124080074040ca004441c040b50040011050054440c03440e101c0094200c9041c103c002040c844030f0781007c0c180c00800c800f510000d0766100d452a216000701940d6501e012001c2c007242203203a800380c210343e902000180640e120800d580d40d54a00348284800100d036803541d0383c1c1d401c0300011420031240e4017a101e07440042607039608090008090f401006584503038952517980c01c01c4400d200f40244024107a000389551542050000030984070860940c8044007400803600020320310600100c001a080c80b0744016116 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 637997140 1250 637995890 637995899
    0xa0603120e0a0503100204170a050a0b100b1201030516050a120c030503030406021c05090312070201020c1e010b030c0906330a110651030106050a030b01 67
    0x30314000c001c00700d07540900700c1d00340081c464900740180c8100344922040140e45a04120b80c101044101e6000d0890542c02001c08000045001416201480d0091080d43d0640c0e41c01d01c081e02c0c0c1c000310f500702c0818407901150701c402c44400d1a4005050300c0c406c2054401c0074100034615050b0b20014450f19602408109041108031400c101e101e0901d8050401d0801440e1a9200d103881c40d031095a003220a50750010304800c440302d269014800b9203800d00002d00190401c0014030341d60f8010300c84418100344030784000c100500d0003507048650758800d4906640c04000f44035124071100c128462488019402d22070076200918020a00d40d903051002044140aa100c0c0014091501440c20b2003154401c99041002c80142c22a0042e00c0540b10350700348181da9203c81e000c020402101900c0810081d4800d205014400c444d880b4030400380c08102207031860f43d083e810300150808500302e11092141e07900d20101506020710003041210032000303070004e00a080d50707030b02807040700000d620019003035511071401400f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 637998390 1250 637997140 637997147
    0x9031e0c0c091a0603040b0a141510050c150604050109060e22021323090a0f061d0105090d08160507052410080c010c0209190905150a060312 62
    0x20ba0904212141c0d0745900320300c8041143c1764030aa034265400c411040c204174055401d8000c2843c082402014010b00e410301d000004820501e9034070403403091030030100349194548100241c0340904078481c1100e054580c00c91030081800011345039103003c4c9042c100040b869040078041c00d000c403100c0a03000d000540c1e44074109200403081405c1c00c06024403203e80840540d48010f0a5050103c03880300024030104009680c0840004d00d46005020f80611401c04c405082d0101d101c000b49070704405a11090b0080740740610081c04001103000e40e2096007062142c800005500252051401c1c6049444a80c542d0000f598505021165130105030817403000000558880c8000d410417501c500229050030700c0c000d0381d030110150142c401b49a03143e601000c101e030071284600b2203c01002c048014001144e002c3c3c00003840642c01940180c0100e10302800300c1d2580000200d00700d801c0c0713154003003003104c0b00c450305c1c0c484d89a805a045a04042101c1c03c046028030700184110b000f00e0307034010300a80d18054074580c2039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 637999640 1250 637998390 637998401
    0x1031406010207141324060804020d030302090d0b070c0b220215040f14040b011716170403020307050607081311060d09140d030b0d2409031e0c0c09 65
    0x181d400c240072010480c80c098060003011b0584030760340300110001801040340c89240d03a160b03100c0400c1091f020180030241e12011800480150035150243e658046800458500708880740c4c0201510400400c008402da07010301c102c104a88218111840b580321015003400740841d000c4080d02e421f180305610300041c0380c0300c20000594a000d401150501360350340100c0711124081d81c003c9103460001c40c4581940d14041c810741091030401d00b07009203880034508864811141c01803808121060f82541e1920715401030b40a51000305591a00344690b160a10f8003c3d2039030020642103506100700f40108c0c0700c09018080d02413296400008400101d22280c9414050810703208015400030030400014207000f00c070b4002c404c441c900071040210203200c8040302c07078a000c4039600749004062500000410550b1082c2c03c0d450035941041d801104034110400c12003e21585440c0c010405141947c228101030304400202c5094000240002818240340025500d40c52041002047d02142030000d0149645540c8030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 638000890 1250 637999640 637999679
    0x603041509031b0807021201020a09030303021602150c07120b16090e0906010305060a0b03071502030f040f0501080a0c02211303030e04050c0f0415050f0406050901031406010207 78
    0x74400c00f0b2581c24880c00700c1507034401c00703552058001a40b1001d41c14a03a4040722041800d03c021407400750041c00040c00e0000d10b000080070990001030a0081e01200102c90030043e80080580d2030141c8001d40c03009556018000900c01c41c014102e0009041c0742062064000c1c0d90069412401650344c6000b2840c0300b412501d089051082e4188046900c1818042d510321402000c0011707c130343d50460604910b05640109250344140c104004071546031004141c9000b100c13200ca1182e030000ba9405010703030960049090b4040075003030218001404c0241d002c4c20300c003100d4083c1c8400115889030007071001900d864041c0680542d000c0710824041100094100b80030741118000c0a00b000003c0090740d00d1100e20350301c25000a041700d1582c5c203891405105554000940701034241c80e118108410407c180208d2054850390355000210361005801502207464a0314900c141030b54071074850314060080c0d00120340c49800240780c4210603486100c1e0031a0240039050580040c41840d14040da16894484844507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 638002140 1250 638000890 638000897
    0x91509060806071b0c06020303070e0a050d0305210c13090603030503160c06110408061003032007081f0b040e0309041d0604050109050f0d08060d050307020d080301090b060304150903 80
    0x8240443c421035601740142084c5d9000e5075483c01c0000d001821810a03044091103401041e00801196450080900107680c0c5030400b142c4552a0200c0203003e18003528552034140c00040401418100210003010600091501d803407040741c8582c201011100749000c014045003041001c644510010044100074800d9803900c90f803446640c5c0d551600303035072a104141d04401c0001c2000e00142c0c000f803101e2035010100240201c0c005103551401010011b0407000301110307500c2050307603d4034035800b4450b0101501c204006c66501201c011216500300d0a00d010489403503241c0001d0703a4051600740190115103c4410040d0705140a140401c0000c12110548810f10580c0000e00100100305001d801e2040e03025038000140040b0070f0900d103043c8504025800d0840d00700350415072801d508414150340100d400d841010326103040349009480d6100720203010394008258102002041420f90081d03042c0c0710401014065245284184031107408240c1c1c1c010705006904402d078007210b842d03600c0801528040e24 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 638003390 1250 638002140 638002187
    0x905060d151e090e0307080a0219151b090b091903050f070503060c040909150207210c03080a090c0f090b1801051e1909150906080607 59
    0x1c00d84410480301e82d000e0303125a070602010602148408a24100410b40260144501034010700702c0b944910410030014131808000c070720320303128a1080040c44e180e070b02041c501c4040c1602c1411b145a940350000e440c80c0c0d0403420510b0030311b0111403021001050441903140c2e50310080c100041d012480e088100440d402504401040d1421100014000001c5000e003000d8550030940c0e600003170070120306400080c00703030344410b0900601901c1c142c21642298842d420018590001c0d10f04010308003144006035034100d001003180001d0104250083c8201841034240030006420420240c0c2e820740320110140c00f00341c00e100007032900c2d02580c1041241600c42c99401c040c6540340c003a520303c00081d60b0030070b0400030f030f0700c00e090003460428202403406011500501a00c541c5031100080c0080c9488070001600c203000843c0d200c00340c403040c01000300801203280301d000041d00c0c0d4081400401c082071946407040c155040003c0c52584606c00d140030f5644e514080e0015aa6030242640c0322f440c554044084402e280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 638004640 1250 638003390 638003411
    0x1303030f091104061a0f09010c08070b0718050d060b03010e15070f0905130b04142a0705062406270301050105131d06091608030306010905060d 63
    0x51065140c0948150300b05032021903075106000880d05260004061482c01c21844c41c803901d021415100c040f807040161607500c0b180c8100480f8001d2410200504950011509c54200a4040b0100f44030311031b10b0382d844008222029000e09404110300c15103421403080e4900c1c001081640c0c00c4071140b01400381c00801c0c0202a20000c620b004004e620080b8070700540300520050581c4000b0381c030b05660713492401c11195400d000005044007180848140900d540710120011500d461b0000c1640c4401042e1005151924103401d0013424850b0002c8150b5541074014080d40803003000594002d65000703402042c00303035181d06034030f004110a02480034412000100a44150740c540c402003921030520035141ca45158034040000041c945403000c00d00c00d9041100610580c1c88141c0c02c03040da04202d1138040340018030303440003205182980c00022194040c510402915050003d075122200004004a95160740c5d03954040303449002c20b4804a0024031286402c00c40c0d89008009000307500c040c10000980e00504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 638005890 1250 638004640 638004671
    0x2030a080a0207060206090714010302090103140a0b1201050f131a04030509090a231b0301080d0f050403050d081e091608030c1f0e0a03030516030c0206130303 70
    0x454001401030b401010140140c44d17050203816003044800c00102020760510160021024075980032604159004c0780c00d5505a00c00e40040b410895034030040c8001d414402d10349130240001d001036a0003030700c080740d58400c00d01c014858240f04032020b0001e0051519405610040303003003114026112840400c0c44040130a25043d4824040c600c00d841c1e141d681c00344d600a2109082c4010141309446151100a05c41709000208803101b0703084d1090410302c10398405001c600031841d4051605010030340440041500500014182c089024541702c5ca6020841100d00711a28443d600008045070031280e80e9444950003101080d4005d1840516214000c054100c521222501111810234540c03204506101403456207200401911454010b1468543c0d184041c95a0742c901c100508104400342c080c4e40002000f07940106c49800d40d210580b4030341a11820001e005d000c05a4071003400b000c500b036040c2031250280c0714580c4040203d401800c02503071045158654000700050036000d040d12004104079070f008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 638007140 1250 638005890 638005897
    0x2030f181809010e070b09030d0f0203041a0309070b0301030206180f060c0a020109151403061f170f070e010e0d241443050403121403070c02030a08 65
    0xd00c1c1000081340b46400002519010700d55002c080c80002c20840150192808560401980650300700041d001042c060200e00d1445103a104611141c21852178a002038030040003540140124000c68080c00c1c2c851044076900d01c003c0c03100a41c000d030b00304400c1030760040e0b02c2c01c80c00c07503010300034000d044041340840819041d500c0591042c01c030350010140c1c44115a0098442009803c8075641a8005e86100b10060640c8000300100800c038a00480003c1541c0c0d60007104042c2c10701c884000d1b1480f04441c0782d0140100c003d030803131858070f050030800140207a05192852441041a9550b0048034542c01005451542030009141d41062000d4130290108909550300004c080d000c0c10031010060314112180102c0305103090440081070320005010700480d25484e00e000056041071074500d030904640701d414040380c00c0101e42c0305869039070500400036038003e0080c104603801403c0c101b04c042880c8608441403513815400e0f0b0440002480401d04031031090b800a00e980344058103c1e45803903400c0d01e42484981 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 638008390 1250 638007140 638007151
    0xd120c0f0f0203190305031f0f0b0c06150108070e01030b0a0e01051507020d032601080d0e0f01020a1b050315070219080409020d110304050106051002030f1818 70
    0x70304141c1a80c21410b081006100042040d000000103a125035030082c0700b80b001070b010b58000c80b0f085480c00800603144140d000200900410886580d030b80700d10040d05c03034001c00703030001040c000c510006000040c1c85003510805d00e016540e0654580d5807103001e942c3c005084045604140e40d4011243d89034842481d9000601142c00c403442c4190b24040c100042c00c0802610802000c41c05d0201c0c00c0140c50309070030150a20b40c103040003100402e808030710504416040038800704100c4182c00000b0b01e00b40100703403003541344d2440d80ca0360041d40d042c4041c801c1508940c0310081c01603006510000216006a02040c802e00d90b48020070119956840083e141000844500f000c1110300c030207109499404000c10030061011040c0405c1800458481042e1030055100d54162241c001400381880c2c00640e00160403048004c0500340c03039080c1410164002c22150140900540c14a000c82000c0e5000006681c403202d800a80149003c1254040400507050740d0034440d00090016803440408190307900862250 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 638009640 1250 638008390 638008403
    0x120402120706270533070512070218040c030b010f080d0810080d03060e28050709030204061205010c14090402180d0b0901151a030618070c050114060d120c0f 69
    0x440c4082d84070071100d4682e8030301845c011020000c080000340d000c10b0111b008005030701c20030740710b2156001040c044883c0070740c42107050f00c03c20100000c02142400e0041543c5c01901214096a00c400046004a031180078403a2075a00440300b0703d004c5407240c0c0250f9445024000e641c075019a440b60020f14100d100802c40c0c01080d19903034148003100c102002c41c2c1d8090070240c08824100110501000011150102c0d0b04045488100281d4076900030aa08030056501034070400410b80e0711400281000d01c1882c0494181d400c01c0c1880311428451346a55070541c03a0000303254501901141040003d41c040107507009840e0000180644d1583c1e19030048900c81d010f900c0b0714940b4070701461464211040111000624a070380b56061101d264000605400e4225001c1090364903120003000602c03d241400000b00e030b000d410f904000380c2c950b114101c13151a40c4681d00a0060307800400040d84242c0046640e41e80103a6040e49640200f0311b52101502030f40c085040c289084101610341c0c0d8000400000d00740c0300d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 638010890 1250 638009640 638009689
    0x4380901080c0324010303121b080108190c050609040e01050a20070510051905090d030605032122120c0e040b0a0c090504021204021207062705 63
    0x1642010301c01c01408007541c1d01400d240d0101801301841c007410600025081040c07044000c02444803e41c0a0b1080c51950340c0d40100070303102404024404d070024000c09485000e40010740455407070205080856aa0000c4100c405038140014440d00f500500f0620758031031f0311940805640f68081c820a40a402746400c0842d40c4070200101c1c1411240000c4c0040030765004102c0c01c400b08d80701260303000080100480100c0c4a4640256819107084010310300c000d0030346484103204101c10000b48421128101d03840c14810035540d4010503454601408000e0b0491001c020980c00c8001e034030000303100c440900411401c030f810703c040381905110340300c6c1c101c031040d05208580c61042c00800c42c8404010005c8156600b214030302583c800800e068050050a643d98a072442c1d0300002c0d000c3c40980000d8640600115111103854007046119034041d10180c0c01a800311403c980c031044003103440d1098501c1c0761a00d003c426000014580216841da040a17200c111210000c1000d568118960500601380c50701c040c007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 638012140 1250 638010890 638010913
    0x19030e0a14420f010e0415020a0e01030e010b0604090e19050309010215010b0a031d15060a0b12151801060809010c030605010e13060306180309050438090108 69
    0x103881000460b200800102041100112401e5509410749607a04150280c036103c030b2603c0c6c2c04426143c0350030f454103400491040c0d0100d601209107110203e09a82c180a8403003440041800c80d40321118007900000c04110502c402e819035003100740050000011500a119000000e40d480c0b401c840c01103400e5080000d50404035a410000da005181c030801c1e0b4022075501d001d00f122010711a00407503005140d20303501c0e40b08000f61264103641d13102200b0b4090302c5c055040800941e182010840e480d52203941c0080300401e00d1500101641c0c0a85810000c9081940741d42c81c003100711804c1102c943d80e2040000d103052440c1070a0724880d0f802040ca58896134a181031400800d130a640b01c00d4419020103280490400c03980c0e82c40400030950b00415203917080048000071401016007440d42010380540c1c108601d03401c1906603818036a0415000749da64003001c6440d0b00c00c00080e200d68952501d21500030ac035980030708030b1074035106613090810300b0200034081d290803012070b410447c01d07400990b02e50030584608a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 638013390 1250 638012140 638012233
    0x9220c091701020a0c0b06130606030e0124060518040c0305070305060d02090601140d06031209091103062116080118050d0f020709060b19030e0a14 65
    0x80710814003200070b500309034a00c14010070388442d060000c0c0c07440c003400303020801644400c0d048061804040800744015070719564054064942407000c540c5a6190030313004540b030444024001450444201105030741860054100e1f02908600c10400c95410440c02803a82580c0d40d200e9440ca41d003042e00c0c041154a00054041e0407510000c0580d8001c98122850707000503039407004415480312090030017090b2030101c00380240d110300650041c445543d140c1900801440400d045250860500350b548448464442c410f2200355100c3d19130700b01c6ca007130007440030424620307000728056242000003c0d074041500794856243d1902d1034101c80c8501030001d1000c1400f24580a015401c034020384800c03400030380a02552200c1c0e8404150100004000400354601186403003400100c0042100310700038815103464030b084030401d520001010301e07442003a9903800ca40c01d00078041c801c03a0001800c0034043e414402e40b1100c81c0700008000c160344074003411510b04d0080c03410f1248545240d2081c07041c100b1100b520900c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 638014640 1250 638013390 638013419
    0x506030f010c0914030f070e0901022b0c1e030c2105060405090d0c12110604081201050a0b071b0b34051b130f05060a050a0b09220c09 59
    0x640241c00c0a09048a06c880008080046890818241e0810341d01ca07620b0380e0090082d8036403000c034000540003400102c1071002140b035911080f0a010000c1000c400f400f07460405c4003400c146002c004402910b05581e011303901c03485485407039040c498210007925941c0e607240b00095211a0400390b40303034103001050500344a1160300041510041000b0602d032030700a080100400001401d44092901840c083da00c5080c041c003060031080e08450752818989800095900150311584900220000026080c60b06a0010044072444c030405071401c0400d48403643c0c04200012288681a040303800091501e40800080c1044c10000c4072440309901c0054444040300d1318041459041d60b050040b100120384041000c0400200414690342441c000d04041629100c03011148003e1603d03102c2204003442c8940c00c80c0e845440216000c80c50907031100d007080051180c0f401040e0805105000c001d0b150b0408080300300c01e0030342002c01c0980310701200e803500e010b5442c1c4044203400030b0303103c82c1c08102c90000d0643c113 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 638015890 1250 638014640 638014679
    0x3020c100510170c03070e0f0906010302130207030e0312090307231009080a030c0210020a0b0a020d11040f0f06110d0c08132403060b0d0506030f010c09 67
    0x1448241040000b02c8800802070007450741c4001510f40d8452181c608010500000c50050709450003e6600d000c0031140a0080b1914800d651810b00001c02c45e001c0480c03100e0503613500404000440459a0707008000790000c1404605019000c2c0e030340364242d5000c20028458099440d04a9901c0da0b120043c51b04081c0c0e142c1c411070f030740c81203184000c07100d480300c9035030449a0005075142c00f00d0806055003200c42d000594400c605600402c2218000c3c1a070040f0a603046500a07100c0250302504040100d80d600d00742c0e440904540d11640104581564680003010380d81c81074440130074080040e49503181c240d84658844c100c00806100b041001e40802c0740da8070003c01c03c90a180b89560500c11055172255118013400040201d0f551008080001c041c0940f0080788060782d008030003a1312110501c0310641070204408a500c1d6003100503583c0c501c03d02640c01a690a401981c1c00e0001104440010b40f0300503040c0d0390b26000300601000582003d201c0c0a0400c1c00035500c10308018030745001741812900c002135 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 638017140 1250 638015890 638015923
    0x6130f1d2514040306140f04050606190302190306113c12040611070c030204050c0f0309070e15011b1704090b0f0402130e0c130603020c 60
    0x100840986100d081d041c4480c01e1140c840c00406903a9422180200261205141e003003001c2404800e000e0310707501c18510885a050310b07200c00d8407800348003a450041114000d001c1d81c000c4002400c581400d2040202c9039141030190b4000c69100d81c00a0340002c1a0a00b00140a52200040041c0f00c2e05009407900340c862a400306251144e0b03180c5210320301a107a540d010f000110085c004100280a01490015580c3c00e0001038545503645010006444256002d841c0302c0d0410084c4d803140c0640d81304480c00c142d800f101ea84c40a600e154284000b40030b0041c4004009a014030103181ca00e0078500085128024540141c642c50741400c01c611a4000080c081c6003141c2041c21902c00946d0700105000040050320380c11000c4160b80d4a403c00c4200001c07205000144d80100b00020741202d682c104802400c1d0464a0005081601c0207000482c01550030301300310113441d20070400400540b0400b558002f109168441d01e000110f001c40b0041009940c001c01c00282e0028141c1c03540a024030401408840d07900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 638018390 1250 638017140 638017199
    0x260105010509220816030203190503011d15030f0d080c0415081005100c020102061803090603150a030f031701080c150c0f010501170a030207090b06130f 67
    0x910084904180701849100380103208400c01c00e100c113001c161907a40c68020040361038a20103140082d100d81061655178050ba03060902d00000714000d00c01d4906840449605400c1422003500e0141124406407104054030700503d06071384a610284103001c05071245d10020803011045040c0181500d000034122420020b01340028420706401d04400e81a01a884c07030301000f942c40381c2112186901181c1e010f00e52042d2401a440d400f01d800141c4420307194000d8080e0ba400baa0740c406904801b40715140c070484550403c100700402071038040301458110017400ba0a9031900072200c04215401c0480d0001d0700c2071120741e40150101a407000c4c80b0920740d503482d00300c052607514081c540365403140ca10441520034845010514480490b003401e89903906110800c403488050112074040c0281002c1c000c480d03020014501c1160406030000c0c10712001e0390b0560060040c2ca10303142c401d20081c03054005155001504000b202000707203900420802400d070030341428040074900088021074050350000600c2d44003807031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 638019640 1250 638018390 638018401
    0xc07170711151606020d0e063102030a0803041a0c09040518070509071404090c090b0711010305040f0605070206061c0308040215040b030a1a04020f071b260105010509 73
    0x403083c02080039404000075850b620900383d000301407c550903110115201d21800c000b0000c2720f440001980b5a801410881c40614901d0040d120380603040f0080e4142e4042e000d00d07800500d152008560090081c0001c05100202c0413030440700100503038955040c08000b25032014585846d1080640081010006a0064802c00461038842040b8401c0034802c1801800280c552800303421112404c2c0003100d09180e0303d035164000000101500c914040005d120101d0108001e41224100c907406500150004808802c0e50011405044000e000b00d13801c0360300d422510002465406054024201a0054159480c011080c45917180d071303c003240060546d00b00304a0012982000c0c00329005601501d1001c000040c2e00d50714000c5202e81c1c0d10070f00b0000c030000100310203418107a00c0800340d1032884a60f22071083d4000c007000140c1c00703000320000303003e0001c0081000158520840355000c18010145040e125512002c45980d0300c400140c060f41140031802800e20940c0a1190310701601080700c6403480d80c11315 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 638020890 1250 638019640 638019667
    0x30519030c0b0702010e0312040c0506120f13080a27210206070b0f04030e03011509050411060c16080106080718020c0a030e03100b090c0717071115 65
    0x300000e4520b0081c0c0c4081200d480c800e4210614010b1a001207a5540c10b01c1c203028042c0b0001240d040d80e0f440d0010b50301140c103280c00700171120400c402001d000c03c81d8880a908600d9041c0c080c00756101c0f8640d4002550000381804094400440691a1300c1000060140c0700e0340b100710707440c2d29074402d034a02e8042070200c030141c10b091071030644220326401c01610031440811024810180c014201808801c00c00100001c000d050ba480340e4401e90310140c000e1744440504d401c0c1c40300b40c140c1c4207000c4585001480400c4040d800740354004d000303c2d84e0081282d00c420108200d68005e0301e488009030400c9465a2016803501c0c828001824002d008212407443c1c01d4440b0344903a1a40902c00071003032852041d100c4881c59406031883c1c07240380f205448952180d841c0c0605960a178000c070502034042c4140702c060704040d52044812014001c0d007041c2d21a510200c096500e58030071201190081007421100310040d6a50003e0103130144140103612800001104001c2c00b14140160054011401c102607090b4410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 638022140 1250 638020890 638020907
    0x1b031103070506040909051f0516050702100c052109042007170d0507260f0c1e0c0109050c09040c050103051503150402040c0e01020a08030901020405030303010303020703051903 78
    0x1ea1708800160000715160150030801c406902200303000800004c400a0f0b03d040d8072860040038841e2180440c0401000c05660601030f410019510400040c010b0f40d18601800e0701026440c42041950644c0c41e001c14610f0f400e0304006501000e503c1c002c13448003958149481896455000000300c0088440070045034211403246200040041680c0c0d0310411070862901c0c140c8002078401941401301d4070b030010000f01002d007100c004250311200b020902c0d40c4c204121070403a00440100c0070100c1159903400150b015640903e007007086a9410410307024800c0e03081409000c41c00c403154004113200c0b00c1d9040007898001d510a035144540070031010700001450841e51303401251820f00380030420b9600d001d05209004076082003203030107014032040300040c251400c011910641c4225004c121110b462801114645140c450301070142e8400d80d602e82c0821210005158410780d0301001510b007030745407000710b82590000c2e48120302581c09100148200700b01400360425250350381c82a1a0800940c2d00d00420048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 638023390 1250 638022140 638022149
    0x6140d0b160302040b04030b0a06061e0f050f0d05060901080f070e04030905090103050303061e0a030209061c0c0315050f0601050c0a060507090e0f0c0913091b03110307050604 77
    0x5030022070380305440d00a070140c80060111000031a00c5d41d5607414a0070420008840c10803000d40b400c00c1c00306515002d020300b1078804000c0700c20380510b15211502035805502c251803280a104048c403042d100c84400c1300003409032016480d03000c17030581000b00c180300b005601a002008950403407000d84548402c000740c4101160348040c0003100f2038991381405d441024060700083d8028100000100034450700000031409000d064a001000e00320280707800751008404400c141c3d00101d80d0307004201510741440f52039000140141000d1100c00322415030207892041e40c00c01c64600400000402c140040c040407061400a0804c013440700c1e1030480c0b102d0b003800000030f14090500801040d41d041140f8204102c90350242c0c001020001e070304200c00f015003200618468250316031240d10005c0c800034001340e860340c09010307191992400d01140c901007100b01001c4100c10f80d82195150b406101180100c441601080c4c40d034007000e070102d411070500e035a040f558500d070a4000e41c44410100400e450704401c6800f180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 638024640 1250 638023390 638023411
    0x114070c02091909061a010905010207141206010e0714040614030916060201061406041202010c050a0b0a0b01030b04090302120f1c02180d08043606140d0b 68
    0x580da1840b050740f85562483e92280c0342c92600d8003003410840c0c40d5118031180c91595441c003510b0707403c400046a004850b402950300603040700c24104907014114034003005000c0014810796103400c0303103070406d03281c2002680003415030000d88082c048000d8001400b6011482c015200c1450f00d402c120700034002d030401302070341d03a5651780000000306800814030204010740001982014a1552101c1c02030280c2220b0040f03410042d15000e00f45001d1a003030003114115460012003038000c007099001900c9200c0414001d0700e440c043e50030001c001850180c1d0703092280b01440d40c00101d0700c6d039140c001011214107050280c025807625403200046034001503400c4145084100c801e94400e000c0000042c2402281e0f5041c0000943c8200085908050f401414414200b14416480c45404d0700411a00c00d000d03540203040f0540c20401888080b40180c2d005a0b940c981c0c03510201c40c142008180303c14a038a109401c02030300d0780c540050110203640d0045032010a000c80c2e40002010080d20341c04401000a80518100d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 638025890 1250 638024640 638024659
    0xb0601050d0e1914010606020c0d020a03020a06020a1e030804150b1012141306020c1204030f060b12031204020d0c033518010c02060d0903020114070c02 67
    0x300a540121a038607007440700b5540820101e8245000c90000b66404552108420280c1d0405640511600085031f0071a4000c041b02d510a400b44022040c101c1816078110702d820b5000310140c0c60344001d680040c000c0d903008044094450602c800c000c040701c02d0302c4041c076010080503408260f00c24030389034015403c18088c024503c01d50302101c000b001c01c0d0401d660070011085001d043e9582089026011210001d014441d841c000c070700075048032104031181400084908081130200da1203034007030700340038003100b0441e8001104032010342c0382c1e9000f59104440810304109400d08006141c040d1518012041d5038440d144800c60304029103900440f4410711103403105400250642d521411418491504410030101283d102e04110100a002c40c108100b800516200007041003800075100c20404100c941c114240504621038018915810803420704108040a00c100540d45d03902c001c0450150701c800c002644602c81c54003900b551600c1456103000310000c1d0800118981002e0412103040e4122030340c0c040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 638027140 1250 638025890 638025907
    0x8100c090f060810030c170c031c0507050a06050c1c0c050319090803010b0901110606010207051e040f02190c0f0b04020111010903050702040e06071205101a03010e0609040b060105 79
    0x822144c1070f4009022602c1002000541c240780c004250441d0743c1c10429516008075260516540c1c0300307005420640c200540855040301c512400c0501803241c841d038261780c800b8000e515040141d520507640d4508000e80016482c0b03488850f02c2c00c000c1c10800f010814404042401006401804024584100c00f03203024107100d009915130344413032041ca80c0203d5098407540c540210102580000c400640071514032003d19112403000101d00e0f01c034010584c001e004803800c00b0f00740081900010b50b404c0e00c6242c204110344090f511400b858491020407100182c41e4220f0082c84a43c05084034201014000f0040440001c0f641c03020241100744e4011a003800142c4642c0300403580201c2c000c0e1084655480e01042c2420554441d0092103002e0085906104808484c01c4ca91f480340c0c0165200340c0403800c494100410764201d504503130760100001203401210395441901291818080c4808092a5000801800800103080102d50040381c00e0798108138a14241c1c0e10310a403050050b00745414004003156441c1d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 638028390 1250 638027140 638027161
    0xf08060a080105150a0509100312030204050301241512091a040c050301050c0a17040309051203030f18030a030b0307090f09060e060c07110a03020a08100c090f0608 72
    0x90007410801c000f040185080c1d03204c9203040840120045c4611450040080c0c28680700c590300c1d0003080b042c40e40350301c0145160307130750345c01d0403c500c1040081c59020710000406a0702031003949620300002c031103100d4209200315030300e00003d2180c00442d14a00305010094030580d01c0b040b0594001c200c2500051540320b10300384455016940600489020740800412082241c1c106041044034002d80080c0304030384594010850a0280030302c50700c0007032060700381c91010348001d01125812501905043c000d00ba1601c0201d10030012240e00703000c00e540300205012550141c030700081e030f0003003004880c00f088035024058140c4a01c00d404110003059114481c0a080da40d0500c904c10040c45485810007644110801d80700103400c2042003500c1036840c0c16980b000c4020049100d0340300d11a2500540d141c2031300e654038440c0a6a02d5580e058012284607000300040c2ca9100090015082880080080d03031210314281d016200c0f4428000300f0010304c4141000040c0301b10422200761307000d5050031045a540c0e0744100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 638029640 1250 638028390 638028409
    0x30f040201200c240417101a01080406331401051c0e0d030c1704030905040f020f0a0915090f0b0d09020a090f140c030c0a0219110109050d030f0806 65
    0x7041c1078000900083c140c900d20b100b46c016090100d0039030700c049801a080d00c088400041d04144c204c010401e18104941c45401c441d81d002e4450540003441c20519200003111000031040c06600c0c1990010b42400d00c1400c2e01044014101c0c40814904565201c000904602500c100c0f100300f01011803071a0000d03400b941100007900040d4007211640d40c5507440c0280605502e03e0b40c00042500300451000c144000d4201a208035050384803d05014900002d01000f002c060409803080d0b5801d200440c524981d0300000c15212140303640340c00b8161f06010310000c4210307600403501e003400700e00717202001518002c0540c0707003c84150790303100c941b124492440403000e80300282c402540240c0c101030124905070680e00c14003041e001c022003000b600001c0050000c060360156a0a180c00c802480014001001c1200400240301d035131040c0c4094001110b448452a880b0080c12507a0a804102c40000f030750340715660300c3c02050100c4044149207100d0303c01501206441402108000d05c0100043e859151031004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 638030890 1250 638029640 638029699
    0x30506061b030306040509030a08010312050c03070f1a01081002031e040f0c090605010c0f0201030207020d0b0105040c08040809012a03020318010207030209012108030f040201200c 79
    0x180e08460390084150b100c0d401110308510561901d0041444480300002380c500b400c0054881e5650b82c1d0843c0c5a151040f0010319880003000810085002612070600c06420f0480c41401c020300401864540701582903044078155401c2098000100075404002039001c00a900c0d2000043c0d4a44610141201d800c130706521440b12021914240320404c101e616407000e2082c000c2d07403008400740d140c40054041c2c2d00d02e03100d0f590019285512600105141c035038501c3d113191050400600c4d260945d40840d80c07400d0748040aa480700f10441c010895420a40203c014031080c9180001c0d9628017580c03221001e000e075601d05070400205100c1e8045074001c0c3e140f01c200d01d0500e10301242c000780c06850b000750f50b0b1788801e4450100c1c9800e0603e44403e0750002896005890b4020030b018140da0030603061440b0207110300240f4a03070030341e03903102c1e0000314514200640c0106415541c0000b58a0180005090141855008c2402100050340d03024052400310705c6400d1284200c1d240c19040c04d990100400485d0140c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 638032140 1250 638030890 638030917
    0x705030403020d031e021c080a0b040507050c0708070f0e090f0f0709060803070506071419080103034a060a0206060a080105070f0309080705070305030319061503050606 74
    0x1060818550404c5d1080c011881d05c94094130254490242240c50b8640c00319420100c025071b1600c42c1c4058096008181d00c24080c00c030016051026100207802d4403001c1c4c4171038020403c0010b149207088400c0c4001e001416130704004002c05407400004817840591441075031407214a0348003050500300700b8061031503002185011103d50b1880f881155440d0f80103407080740300c0149001000101c0f00004410344866503080406010790b9546e281c420b6480e4146030b0308003280150200301060f0001c031516040c1c0289015503880000383e40c1140b40c040c1c018500e000d1910034541141c1071306c00c681040f0248642402110302d00c8a01c0514402c01e03490044000318927901d510071400302e50110b150b0390002e0f07502e00c152011110344a1066640d2129400c8070307400c0d5405800502071b01c0e40603c1c6a8066089641e016210b501800c0c0703010002d0315201e0401c0300c035420482c0c00b6013000043c003240ca10280681081c1d4240182d04110803490a503940c450011034221a10915490310b000507940e40e25a82980d0111201d01c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 638033390 1250 638032140 638032159
    0x90f010c0b0c0310080a0503120702120a210216030e0307051203030714030405030403061122090c050c0a1509020d0f1e021e060c070f05040b04050714070503040302 72
    0x281e22180d4000720742c150070989000400068810000803000d0401d500800a9885e100c042d4002008100004080030203500c0354034010503210700706000070810014503a4070200c0e22500c80c0c2086645198104ec10b20b00c0e03a0040c0f10302e10008602c001000b13440c6525081030a01c1d10b0080011a0500000d60700940d1b120058075000d0b521150040001c3d07104400c5655080c0c0741d4041c210400010740020744002d4010790090105000041040d44400018059468080e05281c50036070031440b07101429030354079001584200c0800100b01a800b42c0ca0255040d07003002402c0a2203a07480c140d4a01210001412401ca000c6000c3c00da4221640009129034020f030942c1c407015142d040000d41d90380c2064007101d0003200703202203480d0801a00c041d443c54030303402800f100102158061200e100407102800c142c1c040820401e0550101c8104000d00080c05400c01c0700c0201442c0c4403c00048400003c00d40340524242020446401e501168910f400c0010305111502c40d076681c14491301e903001d942c00080d00050201c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 638034640 1250 638033390 638033401
    0x120102040e0f0106140c030d050a0b0108060a060f030b0607080f041e0b07030305090c0634120507050309030d030b040e01110306100c0606140a0911090f010c0b 70
    0x190014426606901000342894542410201050400748114000120408031414024099200603c16090140708403420640100712210456805542a6034026134544507081123503000b1050f00c0c3c2c800b0044548482140c9031071406000c440e5100700007010540d4425640e8400c0e0303501c00a07100090f400048280e00e905d00e609418500c0d43c070034050b2900e41c1520410315809268095980001d81d008205128200042d030740c0d041e40a06405008009680a84000581ba984820b0090000702540700c030180340d0109103842000c41d0f0030103103d039102030550408011000c5004200d058220030a940340c1103684444034140316041d4011045502d600d4081c5000f401c04951b0301d90486144000308035010000564610300e081d00f241c0f080070032400104024000105185855a800640d03a040350074640548003080e035403842280c2080d009481e16172081c000035512800c010300031001825014104011510541d01181868020121400c0c07140c0702c03008503801181d00c82d840440c82258805004a0340b401c02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 638035890 1250 638034640 638034643
    0x10915021210060207060e0609090412090e04020a150936151406120a0203010801050702030a1e0314190b06090609040f0e0d0c060501060f0509100e12 66
    0x3030740a4810140c15240403440b071040c600e609030201c0344290018070b040c601e0140107072052041d0000e05039000100b03100020007610781c444950300c01c6108080c1e1907545003031003e0140c42c0384602d8011725448c1d80700c0030400c001a1910f8094005844040828040701e10552504450303521141e048002c16403207030806910030300c1c205144140038110003031642414001944a140442c0c0c0e1080c44042c0d2821080007c00000900e0b0348030800021740900709914202d030107405010042c2081e02c1d200b4482c0c0e400001000b22a0003031065641103002c510181d0701c5c107004104c0043c5481100f880c1e40004860204081c80311a020340c0c4039003407540f0080f01214081c602203450b2069040302088040603142005420030942c6003040444088000082c445810007907020f0601000741195110f140c40c40b42d440100e2094044204102c10380c02449a0f192104142c251130b00000f0703110107a0005040c00703c82069264410340080551348103600a0311040000707000c1e042c0481d4400406440c0f103030404040090100303410340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 638037140 1250 638035890 638035897
    0x71a06030c121c05070302150a020d0618060f030803010905070c0f03080405120309030f07020409050a150f021303060f061e06021b010e0d21030e240601030c0201091502 74
    0x150741460150700a841072040e04e581c495520002c0c0144c1205880c0542030440101a86e0040710300500142480440c07000d00c81101e6854010100e4081c4031a04010890302e80d0044001814058500b440003610790350722008540418002c4e4400107443e2000500d09611542d4801d52068000040f050001800d0034007501c0044143d40170713540340c010b002c1d914020007082000c8070301a40041000b1407a0082d22804520140c0260030101c1e03100e5200d22040c0089a810443d03601c003180500c000044a10729030a219080b01d0a4512421f0341d18014450000460032130103007035044981110010540d0000d541d5800f00409080d01304100d84c401d220744079200410140140700646800303808440d81c3c20a4180000064846000d0702400034032401e42240131810301865211040c0d108071030300209101151034480c100000c000307040d00082c1d50b4002d04c006808040001c0c50003042000c0702016400e9034544001410340c80101004d0515441d11070401c80d0314800d5012a80d003d070006c0030b000e8451050700000c0c01039803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 638038390 1250 638037140 638037163
    0x8041b090b040b040c08150121051f060f03050a1b0203030a0b0105072604030c09050709171b1302040b0304020406061b03180509071101050c071a06030c12 68
    0x42c40e02c04021010304080c85052042451a1104245e982d00d801914956841c4264018108041c5e0005011101d0343c0d1030070f03270085070440100454a0714001c4100b44050203c0c040c10722403000d0320401000090f81003140114441d50514010945549551102c07002d06101d10100c41400d40f2215903021055021000c0c6014204170b900c144421075a900044506020719040a00324644540401c0800b00d1001149440314404000701400c03e5940c1c0c60b4026a00d1096028101070b0f600c0d981002006580500558050b080c8a01e02c544405100c0c28003658601da561f4491030041030340b6010a00342d50b00d010365080101d056400a6640310785841900c200c2c0e4109441c128001d03800c1441c007103140b6010700405441202c01e000d4464400c0d840392022161181b2031640c2020fa44000c0802103003548900098504ca507445807180203c0d025180307416030858000070a01103c0e11803c3c410741000034910f40041d200d80c01004250040d50700d0b0f01c030010b410140c80803045075200b0384049601c2014180400d000c039100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 638039640 1250 638038390 638038399
    0xb06030a1518080c0c030709150b07031b050a0b0c03091504140307050a0c120b0a110706110304031805060906071a07170106021c0302070f0210110613080a08041b090b 73
    0x41e03588c01009054400c001c8080381540314100c428400309841d80058020b1500a240001d040301c881640101c40c00780c1b9090a42e595000007851f0020701c025100705607044079905951b60700c1d45c80c040c0a200d840740c1d10070038440d4591100b0700104007840030031a0600030182070346007666581c41c400d1030803a64868500718119031900b4004c0c0005101d81e20304202c44c003555040a03e03800295103542483c0d004108000d040c4011000512003000401c0041c4180100c2c1001c0020702c4e030740d03402c02d800c01412025012801d00301e16a01c070b120500c03c41d203881d0141c4000340b205403070041e10741c42107141c000c05035039100701c40c08a4564010204903c0e0350303000900802407480041010801d9072942c0e002c98850b0f2a11030300220001464600c0a0124401d5004003c00c17805036948001c0003643d54001382c0c80d0445044038100107100c1000b0030150820071b2028940088560a880e81d4105090b580d00d0440e015010114050145000000e0140940c1c50300070707005501c800c80b00c003055a440d96040c01c01405a080114001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 638040890 1250 638039640 638039653
    0x7080d090f05060702190f06080601020f1b0f2806090902030c031909140d020c0f151e0403080a03050108010b01080a0b01050d050c04030b06030a1518080c0c03 70
    0x10440340c0c9244007601c0020b090030b40340108503000d0180c480c02c22020301b6892040f00c500092421000c0003444050700865807151507500303048000a207403072a80009446150411008500442c0914640e105240400c0d80c800c814000130800140c00394100360050782c03148041426802c80d980703411480d40107440307103a01d4580f606600d80f0301240480c002241c072440608001c1011400d840e440c4503035000500160034001c140440c2d0795450002046401868254950007140c03142d84161701800184900e00043d00e01c2c1c88440c0c40740c1c0000d01440c002610948001c0780006a120811801c130306e0040101c1ca03003000250361107980e881c043c00243c0c080100580000d00d402e0000c03800704018056129401e10507913403803406132039a03034010000748010780b281c1c0c3c1407080c100005041c40d803450144500c141b036040e1103681c960b465401d050401520041c1550703c40e4210a520700001031121800c0c41c3c6c188103c90b0300045044440702d101c2454422280058901100420001140400080e2442070b0320810f600342c605 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 638042140 1250 638040890 638040899
    0x190311130e013206010309060204030f051005060d05030f0702120d08010518060303091207050d0c0f05030118030f14030f041a070c080306030102040b120f0609040f0b10050307080d09 80
    0xa0000300c1803d803150000a03501203402036110340c00401d01d00c0c1c05148014075096480d50f50001044604904071040d420030404800c4038803140c0302d85a4400002e864021000d51242d40e138a44a20440090060840011407008159201d812004910001040403540d01c02c204450180c40008244034551140a441c203903e056149904034040c02943c001d8011402c2481d50030801c005040303481c40c00035041c480c050307000861f56074103001e00061a00402a40750b980e41042400c0132000c40b01c2c0c2005000341e041001c4000342140006600c54101d07050300e0f2000c4104c4428008940240071400d0751601400040140304108205905031170090384500c40f000760002c44484489005002103906c100480c95820b150070105480500031540550018001031429481d040c000080760020f03540002d80010070010071804109424190760460000c0b10314202c43c0c40d003582c07407054200e00804003e0011b41c0d5080400d000303030760b0300e09080098600202500c54064584610555035020500b440000a000e81800074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 638043390 1250 638042140 638042201
    0x1e0b03090a110402070c120609150e0f01060b0703081909110324070c03020718140c12041514040b0601020c0a0f060e130e07050f190311130e01 63
    0x441c0799030700642c81406c181c0f90801c145000884000c1c2903411a072104103840024070140514000c90100690028042d204182d5442c601082071803860313500d80c07400100380900b014180948140c03d9042c541082c0940d030701000740c0380121001c011040c49500f441c103400200007103c085054108400c2c1c0c111070310790500c100d03210f00303001e0702c2d0480c1c1d081207448501042d0702170f00c10345a9135400340c000c0c01188d2009503200d0b00c412890424561009010390348030800758608004807581d54224515086441c1400140000711b2250b03000070344003d212411440c0740001c418155044240780c0000820344800e10300d002c1c00d28541841c02200c509006000b1020824124946112050f05440c0e1840808207203900b0181d0903100c031406503d03000d45c00841e04078581f52400703050103410030110050002d000150b18000c03d1254064101e001603104201c0100d40c483c040c02800c2c16101129001a0101790840c2e200020540020005940c2c04029050902c12640004150802c60b119103003075807040402844480f801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 638044640 1250 638043390 638043397
    0x305100f0b180601110a05101103011512110703080a05221e080c1c03091101081b070f022b0b040804050904050d0e191e0b03090a110402 60
    0x164001041c2e103042d4440c1891400440c0e1004043c105074031520300b258003203440d00a0886048889a21141400c40700e241c135401a44200c80489190b80d0565041000f2640c5014025850404200840c909680c00900315085450688003c40c170081c0d03200d4060800170309a03142121000002810f03d004142e41c1c42c18412050030022100003998260b134401d5079542110180000d000300400102a00f1b4408070f85090000d00148031414010940b000300d1209210f0801a51640641414501546000880c09440c08880510310034a003614203580c4244031281721203500d13998840028008242402044121780202a02600071605400810180b020904403245c1001d5490165a01040242d0010301c001d00ca09070400d100350203031410a611000410590b881c21901914203074805c7c3c02840140d90000c203001ca0300c46090f41d12042c0c0e00c07094800f1010110721403213000501c4090001d002051044007000c0c0c07024040c0f4142555480c10301c0c6070aa580c81c581e41000740e80740c007a0b2400c840203c1c0f50602c00c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 638045890 1250 638044640 638044661
    0x140d0c200a020d02120106080a050106080607080613061e06030b0d080910020a02090717130c0b0c03041e0302010212090d030807031509061d1b0c030705070305100f 72
    0x10501da1520350300344020b5400c507200072030b0016281c03540e02e6250b010a014003805445040010080c0c10440e0030070703a00b599001c3e1320420307840c0c01400030f0180d2281e100c40354079441103064603080b00c0c6920311800100200355507801245000c0c84110254150103114030300340d0444005507810300960844008010015a500d600200140b008000d0720900e401e00c020305245121041c0140c803140e45103a0042080c490048455100080349540d01d807100c01042e00800781c008410a1015030450a9030765804014640740c01010b10000d0007081c1101580010804c4401402c1e81840c0105000358042c03500c440f0303440e07500007203002d401f600503004008140e10044d2821a00004c000c0000320354143c40c04d0b651054050311441c10151914503c03290b0241d5042c5000003800103400c00036003913141100070f06203216061a42070301030f145201482004255502c02c8840761900101da40d42c0c0340705c0109545d10b5803283c44c0c802046401610400424840042209a282000d020003400103403001004182115008802c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 638047140 1250 638045890 638045893
    0x705060c19110d0c05070306050f0a0e0d0f0e03010e0f0109050d1e08070c02061b0601080c06220f0303021c0e060a080417040f1502010b0a0b0a140d0c20 67
    0x3c0e540c250070311841840800c00e025a0960381e0300c5480751144419100c0460f148420704003900180202c0003414820150413881550150005c21000f840003015074841420540c03c0122580640744030359021b6201e0310440c01d4200803100204010104180600003c10050b5158000d9050064030715018181240c2001c031000603d088215000c5400d4403d00009000001005561204c103401a120359005150310091110420b46e004180c0d68207518102e0140c1040102790801c2c0540c000a490304001e542203c800b0f0130200c2e1407000b0038401081980660f42c0134104541c0450800818181c010801c1d00121701c1d01030000d0980011240d09454503601902c10940008040044810b41032040701000d421911546140d0603201035030303001d012682c2080d04104114118410200803184480241c2128200540002d019010000c000240c03c4081072083d241d98031f100180010189100b10310ba19002d0800848a5071030300c4040096000900341c003252400411854828084880101d50081856501500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638048390 1250 638047140 638047153
    0x150603020a150201060902281b020609060705150f010e06090c13270f05060604150c06151404050c030106050f0904050403081b0901170601050705060c1911 68
    0x2221200c0030b800c0c0c1e4041c10215503840c900824184401d000500c403100ea0000c0100c420329292900e6502a0b030041008030500403c0014900303803400c00400f9140a46c0c04462650300c0e50040300c041003042c032070320400504a00036000f94418410072000183d00403000003441c50026a02c031410701500e8002035480a40c00b20111001500301b00d40c6d030b001040119080c00815a0f0203681e41c80d160007213005c101c100e4030b502007172288012500e0840e00c2495a4156200402e000f1420620081039817440340c1e004070844610420488034001d8010b00b51040003079404581008410044d03c064105448240030312102107041456007006403400e801100d005101947c1c80500d503904c0c00d102078816601c180981450381c00c00f030003c48099991032007a0f40c405ca020ba194483c00d441d1003000a1b0400c5c1070000c06054848003401403181c180d0f84007525608002c201c800c80e8806403684c4005a03608e000300301004000e0300c070360420040c0070036542000e01800c1414082d0380c000c04141800c26a20003100e0805584d8039807291 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 638049640 1250 638048390 638048399
    0x120a0305041e050a08032701020406170423190501050f06030a11040506010c0503040e011401050a0206040b0705160c03030201050c210604091a100b0a021b03010f0c0c150603020a 78
    0x3040255000000000c020380c3e062204030071f00165800c002e42d070f05000d03540401e00f000060b0300a2000810b801d8034242c101050300d8140e80344181c445d4091503290941041d8030380001d41c224100b240e80242c07501301e90140f03500056490103a0103442c2c1125406038105e40180414924107000034480c1106a108000704000c1008400740310082500400890421540081c440f01007003080c002080276161540800f19a50304060405900b01e00c034060f8517041000400c407181030543e01049050b00103920840e040c981c0d44070124200c41c903008008804c0c0b10101030002c044104909003805e981180d00c2900240100e5075001040343c528004d0703200c205503030307240340c90001658010200e003154400d4000308005140d9610361145201e040810602c040710200b0b0000340301c44840008143d10080c418680e800e490111410760081d1200040042030403c01004400f04045540c04e4100b002503081440081049001604004191240001c400d803148030b0800403000040f20725000d103c06882e00580700c2110280341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 638050890 1250 638049640 638049653
    0x5030c04110910021f0f0606050f07031202070c090e10021c0509010f020703020f1002210403170c0a14040f120302010b09040c080607111e120a0305041e050a 69
    0x40c1d060110131400b0314401456041e0700d400701100c2e054100c04000512145940002c4201c0b0b000782c100b1024014188070842e59900c4400c215944254580b4140f03100c02506202c00d0064091468000c0c844840503001085500b801d07400034000c4076800341280c24080b41c42e032640089108000008031140b01b203901c00c00704180150011600700d9020400015032007054024042242c10010003200160807142d54031681c0c03031342080700103007481d005a0114074000c005050018840140b011040022040100050625028030020312004203035028000300b61800060041e1568412461180401c4d841c4190010b1109410207580580e81140301c46e41055040c100d200c1080101c10303004a00b15902c030803484502d6203032007508501440c0300d02841005141008034941c00c10000504550410130501074101c4003810008040f9501c04501c200503078103004144040c0e003010700201041e019114001480300c22240d0581c006440390340900080562039001e040d141000c0008181c000d0718540c441180040031804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 638052140 1250 638050890 638050909
    0x61c140f04120c030e0f210303010e01090c081b0705011104090f02090607030e0a031b05041b020a0305090a0b040b09040c0503070819061502010b03010c020c060319021308030405030c041109 83
    0x1402080d00447c49011241c02d1100c100e44402140c0e00d400c04001080401206580b00c0d014150040040c84001501d24000700f01000042140b5000c044500b844907400c81c007041142c3ea5550410020b0018603455400010150f0003846980b003590b140c04c903403202d105000c3c400c0e18100d040013802940b9090300c1e500e045400d0205100400e5010341002c0c00040040c0c1d120802c5102109511010102030b071520b004c2000300c8d01c019110030800d84501600110a030f40c0410b040228a034181420382e11215028045007030105150801c004070040001d0100300080060003030050300341c0458050104410008003262640411341d100c001180900c0c021170a03144003030003054085820003000044560f6101314440d8021030404070f40001d80d54540030001d00d401c1c2800b4200b42d43c4014001010303200305550104585100c001c000e074011200c81c0180d01000e04403601110b2160301d080105034000723612003506e9a01c03540140f2a0600c00e12070004856920f0405001c1c060303000b1070a035a090306109916003440440030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 638053390 1250 638052140 638052169
    0x70f0b0612070608010806011403100c0203090a030c080f0d080703021c020a03090c0b0322050f0106060906030e12040303031508060c090f040902061c140f04120c030e 73
    0x5403002040740c1e1128100308460081c816541c13640860b5240641d480e052400c184c0100076402040e1714095415200060305462800118100180c4041c03d198103c0c15030081409181e409890090b00106003c145607803142511310301d20640300f00b1490419020346d0350300025035040200b0744242c0010500b0340203501070906406c02d410108034400c0d295622400320307846454014046642d4a614038240450101d418010b045240d0401c1d2560a0140300100c403007003050700000740884030b40c03159410070409001c4d682d03440b0070540086c080d140d00d0303c40c0a0245d510700e001e2039000a00d061140007007131000090384403035484650001460a820761310100c010b003410240044d41d240083d00001800c06007004094417540e0301082c032039120f100d84030030001c203060080c03d6244980d0900694102503590351040710111120180e001003020313035004500c401740005080c0a1015041207080155404186540510407417044110503071005407840700b610700d103155502c09000201082420507050503c03101c24580031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 638054640 1250 638053390 638053399
    0x2040b0618150c060f070e040605010e13060503010203040807150501030c140d0b1f0f260a050607021501080114010b0f120901020405040b10120908040510080417070f0b06 75
    0x43c10142e07500d10340340c1c1c25100510601070000801c540d85900404509160030115424000d1516160000302024000c84000f0700c555552000702c0000303c0507500c480000d10000d0300079502c81c90315045c68002c540040b0002c0d1a110040c01000b5120798180c81340e18141d95110700130b44a20303405c0440d442d00d4a6041800d583e00078804807402d0001c40c10000d940e911030098031800350038000511310600020540d0307900c038040c5076040000074800345509601d40740c40701ca2071040c100001c4449070030f1540b9044928402514900404042c062215408200d200310801041150b0f0120790381ca1000c103080714081c2c42c00b2096a4401c000500000900c80010803903d4050040d003802c000905150a82c0071409654482240e940020104020300780303802140c501580842d140d4074520310001700944030010307180f015848203a68030140020401c4a0096070060034014046001007482e2a401501c440400e8034280d41105020207019007029040013194030700ca51088072480d406000340c0e01c10006180140026902 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 638055890 1250 638054640 638054647
    0xc061202070b0f04030f02070308121b03070203071e050a060c110f0a260a050f070803330f09090a02030303040f12020a020a0e040309031e02040b061815 67
    0x86503181d69054094064004151901d0401e841c3c00361006c03000031017103401e5401c40700f02000401c0c0301030251101d10000b0ba07540845982c8a2188074105400100c60710998200801407210844d80000a801640d1190f0b58190a00c0c1402007101c5134003841d00c6005240c1c0c2c1c02024000f0020f80943c02c0f000b0045074074101044200c0c0524060390420100b00c440e9100d07640080d151000f400444219680d000f00d00f00d030074800c0407003005003001c1c551250411110911400040424444402d0012560029040f000c2142c890510004c50403c80300f20501005103c08040090700185a40000013010150b0050a40c800c61180d00c06019540c000100550128000c8103100700142c1c40510040d03210741d105080303201660a040c90051112401e4000400855102d40070140050319429194000d40c1d02c10440f65045070b130b551600300c50140c8141c200400800300c3c0030450704c803042d00c0b00d0344140d4035208487c01d04c510b0900000f48111405201c0d0302800f01504180d01200c10705201071003c10317482c0e018001924 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 638057140 1250 638055890 638055893
    0x3030f0b090702010f050a0506010c02010f11060a1b1d041e050c091e0307090905010e0d0e0109051c080a0219050a0210050a0c0b06010203090a030b0105011b0c06120207 74
    0x160318008561410140c4d440d20b81c90005c4203c44e01c11107500200040c0100124104500024819030b04014028144403c820503010790364050001900f0320b000300d408450700383c5008401d070f1002d0110703084014006010300c0209402c0c2c070300a0b140c0700b8500f00f04560351440d1404400400001e480c0900d03562003201186401516030040c50b006883c82a180c520310383da40c80c198141804401d0b40704d80b01d00c4800845540800303a90365404641c0b602100c10104012a49401c103041280c010841140c01d45000d12409039202c2e250354000880390100c58090322940000750f5100c040c007991003440c059066840510f0060700340045c0804026050040143c41204c030b5624040601c0f0080511102080c6c9440d484480f50300c0031490411000c1c0704031866460103e0400e5980d03c006403002071900d0009140a009000046141e4401c005854104100408030506243d80c0d080483d00d006007806030a00003443e044014801038285c45440c2d0505038000f6003140b00ca480c0400c02c0380e0a21465500400c2240c0030480c420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 638058390 1250 638057140 638057149
    0x15020a2a02150a09080303010e0601120b090411010306080c01020309131104030b06041808070201111c0804050d080c07150603020d0821090c0d0c0803040b0d0f02040b0703030f0b 78
    0x5a860202d60060b40d031500241030181c0801e006070300c406140d500800c0140940c6100d03c518640011081c01c0085c0b9542c0c2140c1888041c0030986042a00504041d04100c140504980c01420802d402e072002c200003511400400c0d00c03448544242400340e8000c12102c2403d041400d00c03008400c1c8103080005900041c420308950070b40c0243d10a40d11104407109001084c5028440c44c040300c043d1110340e144503401139a81c01700500441030040d050112030440480180d41c14442c05414451000a99011414ad8a4007600c54101550140d52034800c038503000d030b070940c003c0050b140600c901051850400d45941c0d00d40e1003c1641150740c126190b120280040181c0b6508040141030b84901d00213602d1b0302212544640300044031010300e0039240d208d81031103071582010404422085080d580300c0701d000064200f51003803050305da10081c8684000030b000503200e40400f02400c1c90b0400d001c5d06200c41c0c0e01c07104031802603004a0140e805071070001c1180c030002038040e511081c200c03e155007000c9010300300c000014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 638059640 1250 638058390 638058409
    0x1b0f070b0c0301030314120103021e06040b12062e090b0412050f060601080c18060d0b0a120510020a020c0d0b07090b120112050a080703030915020a2a02 67
    0x103296008088014001c01d5001b00c9206184001c04042c00d051002c03403a4000c1c000101880040d00603103440c0000081c41464170414483d1410142c24940e450350b0301e544a010540c4800b01c2855410071500100d00d113440e00000420a4800c45002022250340f00044181c52074680c20205007400764901d800503002011002800007040c2ea2000c400049060381003142c206030040c0c204030310f917070040c03402c109283e80c010401c940c20585681d6050345441103400c0d0400e8180e1140c14159002e0004558010000d03c40e1b00500110501581d2003a0440c0d078032080303a4001203041d00c005290750001c50b02c1110202d06e0b5070203098441d00503c1254a21514070020a6400003508c805480201c003920402c908184c10917401801407411a552914201042c079850410500600552050780849580703882070040c2001865406904076504642e688214a0060700504c400302c0c0031114030010b000d0800d403152591082e56001c1d00261035040c00e4040440c02c00c4100d4100405c14164020308410060140c1c80703c0707068 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 638060890 1250 638059640 638059651
    0x4030b130b0717090c030607030b010c02060313060c020f0d08060a2d1401050f070c0e0c0304020406051e0f03160b0405120304051e0d02060a0314060103051b0f070b 72
    0x2903104109001083c8410507800518040c00e680c807000c54070b415503c000408039804942450002800e4002c500100d458515094000c0d51211010060140ca42c0c02001c10030790701440340c0c3c41003000301c9101d003080c7d840c3c190b82158604140c0241030340c240c409001d02c0c1c040e544417000410105900d44c4421a0b0080030002c000007442ca6103405001e13101d40d42248148901a1000c1c600c076003401401c00000034014030400c50390781130581d00840c843c410007a2100b000b801034407d0a41c4840a4606900f01d8129500115030591090b4203211000620707080c18002d001c01c00e960001c640c6895241041070000041c41060150f4152044135501c160305080d560890380580001c014269896181908204245c00c0c510625846904100000c0100e81e6641200040590000075806ca1140110b000204180f40318031020b50040c41c0041c0e07103695541d05920400c1011810385040c2c0c1d042d2500e80044044a00466580201c00100449503041c001c200e80035000441c070380c40c1c169240483c140e4a07144000010740c1e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 638062140 1250 638060890 638060897
    0xb09010602060f010512120d0b09040503220e010b030702070305010203090307022103031801150e070305100b0f09040225050609060705040512030d0516030e07030804030b130b07 78
    0x140096010145443d40c0104801c1314000070100010343c19540300d0380c44140d0078140c61000034035000d0b0340095800540500400510300c1c1103914280c1400ca4480d07000c6c011082e4030800410701600c11a221032140c80903944841c1d041034590b030a0205100561340040c0141c0c0540c4a001030010000d40c003400254030601d0898081d644408952041c0802e5807003036481c0c0203050403260f55084aa08001081e254050301444001c214203004141c054018010498003000c0c90040b15000724030085010982c5000b1895a6810001a076512021882085150042440300041000100d04400002e00a404614030040c4011700d00840c11410070843c284900c510700c44201c078652070300c1c1401801e009180c1d1125071200078100b540782043d001042440343c2d0080911a004c141803000006104000341d42074512400e400308100d0034406034504040c51510351900c000780c10070003503d84011012441d507044030783c0190034500302410760b9154000b810006154100b20005100380f4404a001e106a06d4051707040d81d20b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 638063390 1250 638062140 638062153
    0xe040f0f0e0d080c070602030423070317071205031906030605040c06020a031713152913090f020307061e03060501020a03080a061802130f05030d0e040b09010602 71
    0x1407640d0801c80c04141e06400d0103e681c0420107042c00c000e00703c4503266408800180d80360765501c0c1244c00085190f00742601c1c0c10420f542007a10034000200802903030702131503084034100060344000d1100e10501300000e0204413180071614415005501035600007800c6200540a01038030f44490040b25105e502c152042d90300d8030f05000c03d00900346110f0f0003a049070302c09451141c0180d200948030b01d8407080905404020f440c002450000d10b42c44030000240c0c0728040c2411110401402d202030040e030a4586c00703440d07070b82d091b492004030851392003003510790050001e034804002800800000e01c0c1700802940c036210728104c0100140d8052228a01030130721510740034020000314518050491062584070180743c50710702c0510050381c000601744030301e50b4035241c14210365480c5400880a02000d82c0542403105104100b10b207405c0c919005068052081c4050392201c81c0e44201d108912207592050035090340056181d03002c4a48180e100004903100a00041340c1943d00802007041c01c2c1d001d9006500680026 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 638064640 1250 638063390 638063411
    0x130204080a110a050303130e1e0a0906060e010501020a110604171011091c1106040f1a0a0e0d2907031401030c09090318030b040515010b0306010e040f0f 67
    0x50f01d080160030168025814000d030154074112119490150b10364101c0304000145c1240c581146580d109c1a0080700801c1c1800c20040300400b80a48a4003140c015040290101c0d0881034149094102d4805900500000c0c2203500c078034140c0e8050081d1030390840b000b0040452101e40c52425126250ba082e4003d1092035a006505411600d4001d42c40a402c1d50801011f25159a0b24000443c5100050303078044500d4a9444d01c00e2090017a070032a207030446400b040004042d803214130404100c49603200ca8410540c94859030004501c50742c1e0b444004a13481c03003060f294605024482c0004241719080c07040c1030703c20110300c2c00c0b040042040f031001e00d441c0040800a61683c18020a1030740c1d15a0015056154110350710014441005d0286410030381e92100d9010a140c810002a00700015400c0300c405200e403207040011a01b14100c80544482c40b907081401090b2440d03084080c100c51803020381034216201c90004640340e52451008950050f00d810020000b100c0a1003a00016480b1074000220a40b14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 638065890 1250 638064640 638064649
    0x60f12010602010b0d031b38060306130804031a060a0920180a08060a0b120a020f040905150105040f0c0e120f060f0403020106120809130204080a11 65
    0x50708448116414030440e5403540d00d4404203540d4079070b0b1604241c0030220b04042c810341203c4001c070002c1c08041071500a850710306500901080d070a05c0c0c10a550f03c500620b15680307402c503031303082e2103880d0035500403030006900d40310001c803420310588152032051605a50b034032030248682250603041c0d0400b507010244001c078503049030510000c1022020074040c2c0e0b2808e991651a88001f01c02820426200040d0b1003000d440c4134003100c0303807640002c00100110780c803042d00d6555428103c0f040c900b118900400c032526480e0083c44480c0c140e5420000f09000102c540c240030030f8500c0c01c10010380003030b101c200c2e5000041003401001400d0750316000504a175803600e020042640c4580b0315070321080d8a45510410321644c059031950340000281c410505901c041c0016914003803003220152101d00812050285442ca44040c85000d14000e41c000d12045445402d43d4a001d40000c0004104810400521042d8200040d5071000006280300060901d43e440c002c2d5420414078101c2100d400100c00c2c01e56a09240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 638067140 1250 638065890 638065927
    0x30d020a0206010f12120306080109050f100212010b07020612091c030c0e15120c18031507030509070e0907061d0616051002070b060f15030a09030c02060f 68
    0x1841103100c0780e592174a40c5000c2d6406500401030550780094400d0010a40260041c400403d4590001c12084195007819602e509880c41c0b0b81c2000c0c00350707601c200d501c0c003590b0081e18001e40e10446104900e034030b4010405040d5000781c0303089811080038844803044540c3d226200307101c0e21402c4041c29240048618500300e4401d40b01420040c540340009a200c860340c4082e440c24090f03400d4845001e404000f004c2c4400c1c1e4040c1000207030116503041e0030013542080c1080503051002d2140802443c001c85a420562100c03914025500050005070015400a00c00d411164000751503000352202240c03240c0390b4100141040f41c0110300c5600000c0d00b086040c2d440f54140f1714580e4041c41200c0700b6030460b00080c4503885007141c008400884100a203082c01414082007881110420085540b80300e1b0303160558640108451044c815061000e00c0b50b0316086c5444481c0314010021142445c41da125101d207c01403404e4041030b020003c442150318016200c000003004101c080210054548801000d40e141071b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 638068390 1250 638067140 638067149
    0x19030e060325180909030c050f0d0f0c0506061020010204080f010608120c120a030f0c0206040201140313170909060d03140724091707030c060518030d020a020601 71
    0x40c500001d405141c50b443e05150540c0c110f5800480c448102c0d080441b408508038070043d00354002c051040c000740000103945007103805161200d0844122030001503e440c1030701c41e0090b1282d04401d00052051070080c0c0e04042d0840241010f1001d1b550184d0009800e08400040c2c2d038581c0e50000c1c00703102541003044410ba54042c0304000380002420041c005481c1c0c00c0c80d1210340701c03292000c01c1c80315040a00f07000e810303104488136895548030450680000c1c081d282d40c0d003c82001e20f103040700a041c0c4510210380d1038820754060315245503411802092030450f0384000c00c0c515490440e200b1400c0000d0035030781098034440040c0d01d11a01c54148004000280300058000e070300c900814000040081e0704061101240703448100002d03200d030b07100e00704090302807c6140d481500c00540c81505c178800603075602598445010f041c3d450340c074003044a0501014868050041e000c07402d0716640800040340e80e085594484111104100c8250703244494a1554000b00241d0040381d1300800c0c0100785030781c100280e50040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 638069640 1250 638068390 638068397
    0x1e0d05220503090409050a0803070e090a02070506130303110f070b0619140607060c02060a1a0102070506070c03020604170105060d02060708030a140a0606030e03090319030e060325 79
    0x580d46039115966441190034090245850b4403081c414070401f84a21003d0541241d011640d1313140646006000701500c6100c64071030340880b00802c581c400e00703200350740103503610000501d215218000e00546540760448128105601d401d2408100821003011300407009800306c40c940c5a18070b602d41649400001044103000d01c900c102c0d141c14a0706844840412a48002d100003c01d403c4a00411050310802c800030f800241880c104440305640000c4c020300c600d208600800c04062021002e51298001e05800350042e84114414016890043c0041c110240700e082c5d01d0b01a51350383e60108040d50020b41c444040403502d80a0400481c41c2805910b500c25001c947c0d07002c486080c1e03030000d159405004d4015110300c501000203420691250b100606542e03031071059003d00d19100301002d0161086000c1c1134006401e0403010f1218450000c261120440005c1c0070f0100000310722910800300d00544800d808120184510704901e40382c590045000350303440c0500c24068100c001c050038525404103001c5081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 638070890 1250 638069640 638069701
    0xf0718060b120f0703090606031a10060e0f01030f181202030703021e0f0105010b1b0f0309040923010b0411120105190b030c090108010f030f081e0d05 66
    0x1070010b6555260300c050003580501164440350b108900410300228002d1035140780c000301006114481c00e95584031441000301c03860380c2d560b03103610401050640c80340300c0c00b00c0d581d1402d245c0310303140242d80302d1000c0406140c00a40c12340a0010304050315602181c0c4182c0c00800e0700c40c0400d0203e0703c60b81e09100c4040307000551410140c9d5a0095645c2440c1040340e140036901940d80140e00400e12484030b5946a02009202c1c5584604001c0340075441011600d40d005240030030ba1180542c041540e200402690000d182408441e10a2101401924108660003110101800e0070307001c0034400640188400c5000041144100b0705120849680b0003c01d00b44a00c203020710004402420071803419113009a40980e0b26641e4025407080760490303038221b0b56540d00007204202400300f8001c09882a480c090b0390b9a0b01c04d0340c0c1d8510540d84003909000c00b1300751001030b1940e0f8001c100394a004045891110700703e00131045034500da6020b10340010452060030b9445a05021503402509516450200110300c05202e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 638072140 1250 638070890 638070907
    0x15100509010803040807180902040e06071b03020c15250606090501180b0303040506070f0213050603191704180b03060c040302091b0f0a020706030207021c02030f0718060b 75
    0xb51a56103104081f10302c03500710240908600d840e00114a00d6501a00600c81c011010403a9a10340508a4000740000c521402c0c441050031404034141c4100d80580203000b4000c800350920010036005c0c4090039441d9801c201455005040c4403203d1150080c165050210389003d00d82403094a000394415111a400c20006001e509030001c042c449a0014200008031110500b01090860056138002580980d0105044e8180060503000780301607842111082080035180e445034040380c0d0103480c8150150700c103180c41074881100704080c01c441e5000700c4030015440c0d001c10403403149a1154000400040c000001040d02c8800d41c000c000b17000301c01310042c08013841c1a84083d01d85d4019403101034411034000c0c1c0410f02140c90072106003118940c08185943d00c1886d0240c01046500255110006200d24400081e9440c400d00c281e54403243d00610000ea945840c1d900000c96603c0e14200303a90601a01118441d03080040260320018001f440c0c98800c0c440f40003500c0822120554054562090304000688 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 638073390 1250 638072140 638072143
    0xf03020d0e010906082e09090c050406080c06031321020d020f030a05070303061505070308091f0506061b0c0316052107150e0f0f0d03050c151005090108030408 70
    0x11b51001600716021615155600701c5420140303502254900d1414111000c9140e60b003e400c1202000c3c0100300c00742c011607030342c81480200c460030310418070550400307108844030345486002550014040f401008809105496800910300440ba05c03107807040c581d40702400950f80500601c61134020310f0018142c40c03c00ca10a490301c0e48984000e690402400091010405000b44c0c80345025204410440106c0414040b01a025900c213000c1600496800400540151400030b242280c0201c910a0b800c8500013100c10b10b4003800c00a4221944880103000104400503803640310103801180358018401c1d903510310241400c0119250341c00803103440050301808243c583d80b901000b09045907407003210945060001c203040440c103810074407401c1c40070381018254a0380b1600f501d00000c422140c00303010101d280300300804440c101c84290741080c2284282c1000c80d02406c090080c01d10680b05940c80d4411800b411581c854088400198200011505005904041c142c450251a0010041d85880c0c201007043e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 638074640 1250 638073390 638073407
    0x207030e010503060a0905161103190507023c2b02030a020d0305041404090f0212160305100f1107061515020f0f0d050a1b0f03020d0e010906 62
    0x1d060000c00408100d0589901000358000d101100c420440c90502c0904601115507613443c100000707020b50204084404081700f00c81d000741116a42d010110314001c41038845401003941603074003110381c41c070119403e00340102040b84604110300c00500c5541442486100305190a6024020f10f103441080040303d520010384004500c2515804c03680b0b0141d8030010b0310300558110000c2d080b20880403c401090b03040009041540c000260f00301600107944180003c07100604009090881404566005400c2080c0c4030300b00d0b14800001d94004115072071800c0c100035071076802143d882d4421240c0040a0080307106540441100700c00502140050160b01c2c25039018148020300f40994a15000c085000c0524100009280b812003200031146d202d28003035250b805190a401c2c0501880058101800d0081102d68501d0415115642401007641084907004080303880320380701d0b03201c44a803000070405941da04244103200e503009080c290340030780c3c4c002d000c1e489055400c2c1c140103000c2428094240c00c070403607 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 638075890 1250 638074640 638074667
    0x1104060e0103090c03082b050c2d0a05180604062f060c0403020f0f0306070e0a17160902040e0705030c09120d02250e07020f010f0b090604020703 64
    0x20a1803802403c201600c011a50710050032020001407250400d6915410058802c655a000100c03070550802040c058902c00c81e403030703801c01c0010041941d031405565000e02b079900941908140c10450103403c2612a44119001d401243c4041040c8044441c0c02d9a0340c0c2d801072040e20101c1c00c0c185400006028a125a031411011070000103010709480822510611004080801c581e01414a1111007000751b03c00c0c0800d0b400398200b410452443e083c6501407141005000e001090030381e80c3c001003240c0081c0503807901c651154943c00d00040d9001a44480e98a5404c0758002e08690240e001a07445031103466801030b50f0aa00500003040410046500242e012685040044e501d55440050004910030030f08032641c481d580d20503994200c980019010881c100607000c80315800c100000441a160110408440988c51404184800b000506a142d04101940103c901098501a0301400c4d00d401a1400c1096030f80d4106000d0749160040e64103422820942d821450302c180d03030301c0060030403801c50300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 638077140 1250 638075890 638075897
    0x2090d030311070804060e10020d17060a170f150c04031101030b04020c0106050103060602120403021e10051201150c02090414010c0509040e030301050306011e03080a020609011104060e01 82
    0x3002e8520301c1c0180c04440f491079002c3d01e0b5076a21900c416000e400c501c00304103100d0081d030300c5d40650081d4500026a0981005850b1100908000c0681900b0024500146031a0f04140719050018448441140c02c40401e102540940a4040c070b0406d03d03498500d0f08841d007500c0744864024041102044001c5070309481e00591b46221070801031005801a2200c003903501c0d04288009005100b981066100d06d050302e50980e070074040c07507a496000304e9840d1402c404c004518a800c0004000503d0180b0b0080a58092000006a030f0310b13644000480c045c41019427003000c0f8030300143c88455102c2c5d40c1081405440e001014440c14455000b0003002d1000e5220001d00601c103e102080911070214102210158040003d021000000300f0081098200d80c1015016034205410b0505403e0b0100c2500c5c1600e0019008060582ca040b410f20f030550519010783d600d64401240220100368844010184903030b59400401c00d604007080f07001c2c00c55512510040f140c504c107200500200740e110000e41c01c3c0b10024a1b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 638078390 1250 638077140 638077151
    0x303030504060605090a0912020d051206030114040b0f011d041203090c06050703030605040911060715021308060a0504260912060414030309070e090102120f061302090d0303 76
    0x1d0080002c2815401131a0710100b40700400001c4e50503a0415281c40380300c1e50611500b02d180900603130340c074020368500e1008100140203c0d210b00400640059000c1c40003000428480d1924440040c3c0708010741d02070383d0303007543c0c4001c00c040f241aa01c0400d0040c070000110407900061120b04002c8040060310043c0b031359041c020b651041a2003900540782c202e40219007003041603034600c806042948440812004a414540002810300d840d20502165641220581034040f0f1400104810399209070400c0710200d0003601c805a000c81c051028000d0f14000d0b02078001e800b400d1810441ca0020020400002d081c1003a040000142d000400294860020080712280d6810b001404002c2d000d04540756030005000c1d020300b440c0d0ba0700013908601441c001c1005203400c4803081c00d035640f20703c0100e601101550000904105c48520180d000c2d900c03403005c100050503e04003000d820880d6600342d600c00700b2041c41d041130009501c1c080d243c01c5c00700046454110718244000003c10b0942a10303000103400c3c9a03507030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 638079640 1250 638078390 638078393
    0x1d070303080a1a0306010b0d0b060301080309060f040b0403291302331b0706020c010e0d080c01060612020403021503060102070806070c1109071b142e050705040303030504 75
    0x100301c0024030b10700c028185c606079a1514520065900a040318048985c02c003028103441c0e040c880c040700d0681e4900c9019602c0c0c45954014000503900506c480030100c8810807001400401140c0a40042c5101c1e690100d042c889421109149810548909144445030000e004039890118248541c6944c180e51710380c0c05912801450700f0740b011a14038858040010700422a035400e00e40010140780d401890303216403400440310a181e0701d00c560701407200560b0011000380a03c0d80240008038125800403d203000c1040103695400c035a0700469415101c3d40c1d11070754280103164021020b4003d0681390308003107040c0f03880e580014003030011900f512043e01e0400408121180d1081c031108014005100c00c9486a0500d003034020310407098400300741c3c0e4009041c9540d803514a00210118007500403907559000804580420a03412080d01c1e9044411114541c01c40940031030070b0114401c1c1180c0200191032206548040086200c0c2d20b40815200d030380741c4010071114039002410340e1b060f80e4142c5030010b1360350b40c0d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 638080890 1250 638079640 638079671
    0xa020405040c0503160f050706020306040207060c020c0109171906231501030212070503060102011508070501090e06030304170a02030714032a0d150c031d070303080a 73
    0x19908031640140c10201e0032940540c11030020360042d0781520405121034a41801182c10400000001001030b500300500d2010904076000b543e001000100014501a0700d41d69000c1100c041d81d40c08000740e00285001e189960b0046079041c024000b43e4840c8110b080038400f82502c480c0800c07440654102c011610078180441a031240039120100c81001d64035107048040022040e20490b00c0e1810746450f540720300c102d03501c6030007640c2a001c00d0507488031071521502d0043c0d031385410051281c0e046650320010200c1c58403070003000c81c0c01445490f010703081082c101400140516181d401c5444403421110500100d5100041298201c4240004c33440321a600e100f0f080d170030300d100b014001e98184903004021858002e08500703012500c3d8103d0480b000808043d04456601a4000c0040f58405007052800000d080144050751254803408400c449003046200a1040320010340c812000696502003041c201000c00461788581ca005000610a40d40746590003031000c1001800d0710350098407200c003c0c840d40309 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 638082140 1250 638080890 638080897
    0x1050a060c06150f0510051602010f020309030a0b01050a0b04030c0911130b0909160804022202031329010506090d02031509060a0c120515030a03030905061509040b0a02 74
    0xe21040f0400c1c0d09035600c80c0f20014241d10702515100300f600018400159018800b1105441c000ca607000c2031540761900192180050107030326105500003042220b9071540c09020440742c89114280c0a003c0d0b5040909011030b801450300441c80e41a03042009001143c6220005000c6404001e0085403a80d10b0400e441c41c540a91000807200600b2000b01003170b2601e003100503004c0c20704265130400540d5a0b00b20001080805000d0b45000b044030880400d000d8108006440d500b440540006e14644141e621a90120307030003201c4c00c0250002c9450a401041940208040b4071580b01c84400c00803003040f10825410035040c401d2038490a40021480040d898080c0c00ca02c1580e002010358907a030301c00511612030208115003995541c0910000200403801c04d105181c4009030307550f5441d801c40d2404400a00a200203030108600006070481c42405503810080444001d20907680402c1ea0202440c01074a0135101170143d105281400c08560103c1d15102d020030360080d000300860000e5222088520028032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 638083390 1250 638082140 638082161
    0x105180f03100c120219080a020c0a03080f01090219110703170733180204060b0d050906221a18190f0803090106050d060e0c03010501050a060c06 64
    0x500310300720000b0005034010440b00e541510391004456a1000034400c82c032824403500019030310380360000080b03445801c032950f0201d0b10751001854204144400740c5802d9081e58220005150b01c010842d42201c0c80600c180104843e0906508140505e500744902205c40c481071020001c07500010a28801c3c2002004011508004d034109403411141299045034426041910600040340d804201c000c080c42c10f00d49280c15540a540c10010007568003000703020000100e4a4480800c0d40400142c0e440780f003524018140c0c031015030f50f14400003400d402501e20040010441d50404d6040020044590080a001d1a00c280000301c03441203600e85800341049144402c45c070401000c1c1001440d0000c1c1289000390000e0030b00b00c540041c6144c00c00240402003160042400c0c5000d2003800006041d0b05c017541d041400341c0c00200d13880e91a04c01090b0641c0c0701c04403c0d54030a8407418076692072101840010b40c440c10036002030006606140210742500a07c3c0300f000f0402c043c030586681030000c240d100c3e01038807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 638084640 1250 638083390 638083393
    0x20601210c0303031b0e0307050105090d0b07030e0d050a0f05030603010920010e030a050712020604030807150f0b030a030f0909150e070516080a0c06020c0d020c030c0105180f03 78
    0x150b1282002401440a0b01d40c0c020f00100c1e1031804030119019800400c07a11200030001c00351541080011a2141c1101481701d80113030b02c12049034005101802c49074132401c0503030350001c1c0355000484402c1c640a207203061002408010080c0c1041d040e481031440b4210b0700d46051150b85d030703183d800110380180011200600b4196030711007540101c2003803007440d6088803000d80e00d100340170003504201030701c0d1041602c4c01003d65001500401c500c00300107400c0291140014006d50070503940e5100c40c0125404180215154401070050514480d0940b0810000792280b0000300480b0f281007000c0f07503545c1070707001f005028080d16209041c910f0b4494058034014100e100400d104219600111414060541c0600b501780e000030800a82d800d0300c1070050300c5030742e102d0f140e482d04642019100d40d08136038800f41c0da080801c94107a41320307008141180001c005a042e034500501c041c4070400c1e0000c0c01d101c0d5040c13a00344260802400c0008a0fa0301005540c0308038401401041c10500c50310000b82e0308017440040c0c2c2d405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 638085890 1250 638084640 638084663
    0x90e041509140f0a020907091d04032106030b0a05041a060616030804021002030f161509030503060411090f2704031d04090221012705190302060121 65
    0x983c0404103094901600c280c407588090b840314003050b1603402180c003800490308108507003e10642d082203031503038020780a41450410700c921044654448100c624641c541c0700d0300d80c101001007003c01c401c056800f5121140401650070103030740741850100f8224140005158103808a8415565641102c142e02c5e4101901c00314040c007843c01034607000b002c80f0700380d1081400440c800700e194000310031540700400440c6014130380846090000300740c80500300180e0303901300c0c0020300e410100201e203e640c01160090311381903128907140040005440c2451241000c0c89030a11446880c1d4403400d20145d0030300000c5449c1034034501030452118003400740284032114283c040302400280b6400c00c1d6003080003d0207903c0d030445005840140010313907103402e20017900004000d0802c40600010032200200103104400400c100c0401c0301401904c2d8490b004582040c00b00322148800c003c010000441118048141c9c0069490031b82c801a40310074052144030038035120304490106194108062a009580c0403440411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 638087140 1250 638085890 638085913
    0x6040e0a0f05070c170a09030f0f05010614210d03020d020c1c1b020d081b010f0b0a0e040c1202030a1202070f050904050706030e1207080a090e04150914 67
    0x1da4040300d5007580e201007101d11750910356a064003228614949512241051480e55640064000180368180c4441c203003c800300d4006503003070041030000e11590560441074540242007015501c0f0080300041d070581c03003e20207007402c1004a00a10340250034240161a40350f0b407101c2402174440e40e541c01006004540400408070355030740c50200801c4443d92004084602240c03544119040d401c0080c0d440f00b402c0b0310350000946004010400010000c16041c0300c0302c0a84411421f4840036400100d0702d681341c880300400da01b400c1e944580100800300b5003510a042a481c1c03500d601e4110f01660b86055042ca049005640b13040202c40303c1c1a50000b00b580d0700486811000b5141d0085000d03c940040204000007900d107001c0b034000d070040307401c8030203820410f00e051416401024461940042c0f4000c100d40000181051409440750070b01421120780e07200307000400201444402d4004440000303490080c84041008015410320100b0007001c0022251140c1c01c00c0c40c800c0d014010580c0c1b0900c1180094003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 638088390 1250 638087140 638087147
    0x105101e0812030403181d100e040b070206090d090308130b07110405010b0c0c210d030912020f07140d0b04062f070303230f01060207080c06040e0a0f0507 68
    0x144501d0082c0c2d01c1c0c0341110201381c0c4c50940040a4400d45d102c0c0300c6000c81003200020300d11f0615401031005e2065042c6030399125811820744004940964a408501040010454040c02910751000c904005810300c0d01000001802d5028680809805010b0100e881c610704c64002101c1d4014200e150380f001d0310740c40c01d032500b500d8105400c21024021424100001042907000003503500440595000d0203809100c001801140c3c000600101800c14200200c42400c2806101a151462031568007245480c0e160410a004c641c550034004215400030b80e07160250a000300e81503060b0f4104582c0d1880742d101d500005031450160341d401406504100083c001003120940c0b0040502c0c082c0ca0f5040c0d800c035811110102203e03041e0f1911440c0704020000c2c000024483d84c000e9000e41c1c1205052080400307503540a008000044a58842d0000c400c0018008207804001c600c00400f0464010f006010540011600b035010340d2103424400d0b00070002241b82160203070402c2148200c4440e04010a280540c0c005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 638089640 1250 638088390 638088397
    0x120903030115080105091906090e0a0b162304052e031104052103030711160501090e09030912012301031a04021c061a030105101e0812 59
    0x42440190401e80e02c40b500910225048800003081080282e8840c03241c4006c0c10b03a1508070040c1f890f070b500c401044c102032a22580c440c00c03680300b005062080c410316004401e07060162003001201104400f0290203070380410f04240064461a291140c3c88410305521250b000d2a0040c40e8044000109400b00034450800e00c2c41d55444408070407400c90382908140c040f11043c44585031380b401c00f040180105d0800c01c0300700c50010b403458494001030131015106800d40d003090350034800148200b003208180d1041004885100382c0d124845400c060700e0000040c0c41c12506120362000302100d40b001595944040c001d827241070f440a400c6040c8082900c800c01e0013400400207180141000070000c0c400c051480c004541602c0c0d00903c90114109440301280c0c90f4030340208100da010140081c41d62100356018042d18100c2c0c800c84c40450442c6a46020400c41d00d104140180680e1600040103460b540c01d03208102142c1803a02c200b90b114042e05100e02c445d0310980c001c49203034828590002c40c501d1449004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 638090890 1250 638089640 638089649
    0x5120901031a0f21060a020702040501080d080621030a0903050d140d0e01090f050a05070506031501030c0e0618090703060501120f02090a060519180e0402061209030301 74
    0x1003220126240201d10490500e09445400c41066400f11030542006500c200303100e034000800e4119000200072581c50100101c0b40c05001300e0300450440c00314201030040c5400341050501920000070500070081c2021030040140d48903c00958440c500c1c030822500a00c003003103640c1c0599a8480365480003900614442c401214544a18244144054495915459002415040c00b458015021850009000700e2280f080c0b02d55a204003000c0010401c01c02130700744510132000781c0f040c1c485900f082c6082c050700390b01160092004200b0801300c55200c50800d94181001d00b0000f4841c541c2800480f01d07540015000c41e001040000d2005032401d4605080c1665101119121081ea039400802c5090f5a0305103c1d040c040b4ac0083c840301c50340342c2c2e1600441d000c106504d80060505c5400b03000210b441440340d100c28049100003801803544402e1051600091405040455414031400c1030b507411104a84500c1d0030742403054021400315500c0e10308495403241859425261401d00030015900ca03403080c801c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 638092140 1250 638090890 638090897
    0x503190c0f1707050f0c01060504091211010c0e0607141014130506042409030507032c0f0112050103051606030c020304060c020402070203010504060f0f061202010e030a05120901 78
    0x15801168a01c02d82564803600b101c1d0f440c9410022104c08100c81078224440c050029501c550300401e0a4039107104039100300c4c0c05010752103420f03440310308051b01100003d03000b100503034107054a0103410b6400420140000f0001d448842d40c84240b802d280f4035809000d906481580140d02c0070300090500c0d508000d051001c150803202c1d29071035000c0c154100c0203078110001c11036009a8005400f06902d030b1100d8a9040040c41d012200b860340000680441c1c0381030200310701085001c03924605164cc0030324401181d0b5548500c1482c002000203001c00109440f5960b148503c82d4008060010791041000d00c0e0301042040003404656181c6c0392651716070200103d00715004010581c00641244207020381c1c01d0b901c03020340145160604012080b21307000e05903201a038110f5000c01c800f100588003441050300c03540c018403001500c0c140c080c180c02e050318038044c4100d0585040c480103101d40c0e9001380081042d10340c2402c003262841e00c014080707420071030003d13005011400384c20007205940a030080286100300c0e00f43e8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 638093390 1250 638092140 638092157
    0x609061d070608040515060d0512130504050402400e0c06120109050403090308070302060907171c0c080403030903052b0e2803020a05010801080604030503190c0f 71
    0x4011615544100d501030296803001c1d03c0c1c14111508951555005403026007460507201c10354417001e10b02008002b01c4003c500b000070b080e4007480010003290002c3c140c200d400303020605098001900401d00414441c1500d000c00040c04041400c401c2c5450752002003070420f10302216180d4841000b40581d00d102c01c85402803d964190902d00102183c1489901c40d140c296164207040105004003002401241480308204c1d004c00803030012400381c48250300c60b600030300140c94440c3d03007282814070716481300c40c4824401c151428140700106440e460148901584c0e007210351668170880b69a04038940180101d80e0010740031050503030010609007900c3c010411030300031a03590301c1d18124020222228803d44003c0040005e295882507101e9003520800400b0f05204009200294640b400d1450f4451080125580e081045007031291500005180909105a082d89401d000179214900108000e081060000c002221441c0300380010701429070386c0008000c90205004040c00b80c065001007140803501c1c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 638094640 1250 638093390 638093399
    0xf060506010e0901031203020405061224182502030a0314010509130f021c15090515070302070b010605030a0506150d0903020f06090a15050903160609061d07 69
    0x112035102d180b0401070304241050b031854a99038101841c4000d100d080640030040000e580c0d5464003c1e000001a0031800364003814801380307601c504944502c000c48210391081510040742d460003201c00071300752000b100600940d90318010688040300051108003d40c0320b44c07080015503078000040e200440103a03c0030840110f591005039807100d003d1141300d610140c0400080c184d1201541c400780100c0c414a083c1020708015400140c032026107000b07183c0061121011041880b01d00500302c41c980c10650740801c02c81c1415121a601d0f0342d8240300d83d4025800072000710751210300c60384c101c41843e90061054103080d40c6604005201e0b900c240c0300c3e480c046040a000c0b900900c1e15480101e9010350409011349001c844141e002c01420100c4000c0d0194040d01440c49131012040c442c25100d103c03100082c0500e0780c1207140130296645803c02e6810607600d00001c0042850000040781c9a02c4102c4480c108460014175041001e0152001d004020138100780503500c000103241d00c0404003105080607100010b445 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 638095890 1250 638094640 638094647
    0x1e090f030204020a0c0204240b0316032409060608160c060b01180803072306060112090614070207080102070804090e1e0f070f08030307030f06050d0f06050601 70
    0x45004055005100400410051a190303000b8016000b050415850300043c5400060032240d841049039080c1d5034142c038004100318030b00e20074000703418002c90246c15170078100100501800c1c56140f600501d5650503a4004903001480500c8017968004405211035440311301e02809056107100fa140420103040200d120101e9142103444001c4850f60b40040807202030301c0764070282c00c440031a2814451a030a06050b180c00b101c1c1510080d08850000b903079600120b240c500402c2ca0300720740c0f01c540303214074043c0309480b50404151307560400070034030340743c2c1c4444031a24030744e03000b0032442000802061030712201e0b079080b882c400340c00d5104909079026079003c03540c0c0b185007500741d110300c00c8010702c030b0041004144002c5060b0350002d24120300010840b03075080001000e158401403051800c8010707500c070010b02c2c1c101080030018a0f014000b01c1501c480c58516220140341d42c1e001c01381c580310034582c41e1030f10404140d0817640300340c0c01030a00070140d541d42112401d21000b51221102e0680740c4500307210000b40203501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 638097140 1250 638095890 638095907
    0x70b0d09020f09060d12050408070806010311090402060703121b0315080f030a03050408090d0c0f150f030902041415090c0f0703050a020a121d0d020f0f01020c0604061e 74
    0x101805240c40401305d55900e8411400588008040c841c0c10b02004c141040f0410005010305403c0d00100b80d1541107041242c031039084440c900388100e070160108401030711840203540d0100d9060620081c0701e1020702003071000d0480b040c004105000802d604102403545038000d004280c0e042e100403440383c0d89995038561a00c0e00320703030050f02c954010407140020034440d50100d54040c7c050003906040584840c00500381c483c0000741650300d08126403040c49900c08541e10000107100041c4414544642103201030080120210700f2401c2c1603903104204155103903a008030034462003259020141d0314120f1285441c501c680d023040b41c041c0e4440d4001445030003180c0101c511151051001c107007070035140e0f40c0440b03250780403811a80450080300c00c138400044007560a1000711a447c0c403075141d148504601c010b070814420345801d1055518442c5900945c81d003072009039a1010603200c810058138482c0050385899190291a0703000280040e000a1299100859280b020741d41c42ca04c0c00301401d03254048440c4103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 638098390 1250 638097140 638097151
    0x103120c0206160c0302060304032312130303020d0906051902070c122301050403030b0105031b0318030d090201030c09030314070c1e06120612020d05070b0d09020f09 73
    0x101002080840f02021004058880c4110149813100d0307142c0c1d0220705160000d90b4100e0100d03001d000841800c003640350b461950080004082800d00c0c100c0055000840c00c064400342c0b441c02070b940341800341407281d0120f070340d105030744c0d10184039109051404000030101101e807003182d2100c07034004012101d83c50084804154000300080356107410041d001b403051a203800101e030462000031060400d0002d2036156421400000c000052a20b00390402409503450481001d0421108008011011807211f076160190441d201c0590b480c3d981e25501400106503070f00408416110108100071550710075041600b41610030b82c0c00380100d61104109503030b01405d9020050204022402107042843c0e0b90010308003890040b82c540b481250b44a10080d442944442c244584641442090112039042581c4106c1c01000e84010805546800b00c10180c861140400902c01d14400c1d002805110080000d400907040061401e50b503150003042c05402001c040804070300409000158429520309804110700c42c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 638099640 1250 638098390 638098399
    0x1b020301181727030f06090106030218010e070f140705010501170a021003050606090d1b0b03090c01030b03150f15010311090d060627050604020406050f030703090b0a02030103120c02 80
    0x100000b240040914040f0304042d500751081a0a2000e030340d00c1040064054140c1c0c00c0000f401e54190b0040c0400d8100c2e11000551504070b141c01000303c992081100342d40040d440c1740400d0b00f202d0ba48000c9500c5540300840da500310001082040511106621030b504807031f00d425000071445811030b541038031251206000303503000751144180c01a1600942155612010081c51103241482c0e0700000f03000b51800030b10940310515458035000b1901d20000c41c0c20040c2080c00081800e5117000030b5240d9882a01034803680c105920f0b0340c08110b0545081080c003054640d249820340311850094245d00b88100300b100e000f0380d2180c00d00c0c0b01c031903254040c0c850410000c00c071030503c5280200d214203001c60051000700440d1080d90b00e50b0b001405200c4942402d547c0744030310840c500c02c8624080054259400034100c2445244100b0040020a40002c220303500309403440d040c80d0326940c0d032080030b07801003542c982e0140c80120329604001140303c0d01da000354140c87c0720341c140690341059003100b110150700d4600001c0d0003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 638100890 1250 638099640 638099677
    0x140405180309011202251202060405120a110f061f1401030b030a052a30070e0c0d060602011e051003020303120f06010c121b0203011817 60
    0xb651160754a00784600c5030b00805031410300c641010b800728102da8005002011201c0d80300c40c0400003005480050700030544001e290f81c0c24070380c03034150b2100076666003043c4400c03001a46405490152160402d0343c10740380192031007010070100c0350752140000c80300343c62080100b607014012500d03010842c000b55101c81d442951031002010041d001009910030307880c0d051060024290001e0300c108400c1c3e0603001201007400e4294500c100c10500007501c407412500c1034546261181c600400d00f907050010040840700c3c0744824590021040c10807503a50450802c9804003000c0210840e00c0c0c10051040e071540c54400c0264507a1450200c1c00c9a0001c0010000c40c1c3e0000100c501107041a006907401407141085082419501d900082c034551140036030311401c1c5c0000023000304c8000d440b0542c071351002081c201052070306e0459461039960011428440140400c01d214104054044107140c0c480581c054000c01c1002c0c90145030035160300710b2150841b403120312261440c4186c6d69842c05e130f5018400740400d21f9103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 638102140 1250 638100890 638100907
    0x9050a03050c0f06070506160e0d020105070f140a0506010810110702010e03071e080d08070813050a0803010306050a060902180d171303050c01050306010f11070e011404051803 77
    0x43c06414041c00ba0310a0051284102049060000c1c0f4040d00d2614148100048100310182c001c2001c243c0940c851a245582700300580d030403500b12010320b5400b0400c200225482d00c1d000e01c0241c0a5000c0e02032602c547d1080034108180080c1d07a5050326690030440341009061800070040d1500300180c1c0954030024440d480055018600002c2c8103500241a10380e01500d410303d1240800459214000c141c05800c010802c1d02001d0020901d0170320f003450204403900c0c0c040806054208050180c462854a94080c803040c440180404070f00b240d800f540c0640e81e9652410800042c200035211034018501d41b20002504590620031241d089000040110040c801d400802121001030302c0d00303490164210000410011118008054411920707030032060040c2181030161524031101d4000d81440707010030910903143c0e0014043c2218030f0051600c480d6400d00401d580341010700c00e501019000e81c1ca40008505c5980355014210300c6101501c0812151741c607513004500501c21211070345020b420820285c03a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 638103390 1250 638102140 638102149
    0x608060306130f0224040914060303040614040503060f0a0c08060310230a09260f07060902040c02100c0206010308030a0b010918050f1e15031f060609050a03050c 71
    0x39243d6000401c080ca02c911040385040c41a0844000c1c50040c00c0001000e10030703800203102d0f8045034015421195050300d05000404d95a200314003414040c0300c4800c01501c00980008101c0b0040c19015003641c00c90b040405448807000303030540c0c9055805042549a90076144a034040500c80c840080040c011850382e03400200042c00d910503820039103610611003009808050b40110b018048215000405032024140b0303d0300e450070300d050043e00106d0311003084188000402a11200103040c0103403540c0d200b41d0300e4064010440246c0080d046820513451046041c0c021039001c3c502000e20009000c840b0b8400812601e41c0000d010040c00d03004113002180b401e054a9005800e0307540181004180c05854003100c50b544080300b0030010b480c584440800c130246160314003094100b112190b450724104180702d40102c1e040002030801e41c0780b031400d540302d944030354080001101a03075407030020340d14808501d41204041c0c48540100c901058401e503000880b4108103600c00201c0741c02c1317009420b02604000422 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 638104640 1250 638103390 638103413
    0x20607050c0a0614071416081b15040209071407060906200309280b220b0114030f0a12021614040b03010c09090908070f0507060806030613 61
    0x30329080c410050001c0010b8210304c50300d18031000030844203429242800009002d40600070450491400a0043d40104107050404124455001b41c0181e201e40c101c4aa8014050350182c50041c40d1062203100d5110380c142c001c620380518003d9828258980c1c41c41c000359606206c1600490805004001302800b203000b50380002c0c21548a44804101210707102500203403500c11503140411000d000040c0000e402040241d03148101c00c010102c80e00403003544080b589003d450030b010f010400317a08006441d18205400c80320640c0000c1c071203440001c00908090b0201c440c2401503c01180b4101d00c26191450002150b00f40304040c2c2000704080c1000d0f81c1d404800c04540319080d070a61042d015114180240c0d000240050318020020003106190b0340c003000103699010f090725000b41d14003094a040e00e94048915400d88440000201c2c081780b0610303060201e8850200080c10b05010050210f04206000ca002412124503a80c2e00800b511010101038990b101a103002a8041c00c07004101d00003002c1c607800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 638105890 1250 638104640 638104657
    0x30b0f04240c030c020304060f261905090c181008060a0b030c0901050d1209030206030f040605100b1905041502071d01080c0f01020109062d050f010e1909060c0e1002060705 76
    0xe01c400d12b41c01d19040084c41209403001d00400b001c207080004000d0092103a95030000b106402800108581c1000c144100480030003120400c04c0403002032005002d0115440c002c206400840340c5603d8641c2c8500d005001781100f4601c24000c08020003040e191010501c7c0c1600c02c001c4c00302032000407039524140741c000800e68007414028100e00000140c0e44490142d407050f02400010042ca150600c0c107541101d800802558100e1003044050212040c82400d44001030b2001c91020f02e21486954140e51a000300e900004642c11003480f4199079035800306017442120390b4108064043c0c00d188080542030702c02401103c0c1650b0101d80b80002500c0c1c41801c001c103609040c0000600d151060316200103480c1c0c02040c002c010080b2004040754030313514000300211920000c004201a080103141c0000346003040c4030300c3d02c50900150202c3d81d01c0088540c51402e180340d02004204043c4103141c4070707014044240ca81d4000c12038007090f8824034101440c0c501416290380d805400e0b01e81da0201c068130f154219100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 638107140 1250 638105890 638105927
    0xd02070914010603021b0a0606090612050c010503071b08040e010f151d041415030c0a050d02180117161508270a020f030304030b0f04240c030c020304060f 68
    0x6000882c0f107000c0c48241f00032030081d003000c2092402c0075000401d0b01c040754050a00c0105103001e80004c602c0105031400400001d203446540c030384410740c048500c071030401210070b884660449400100410400188100d400f440c420031042d1381c0c1c503002103184400b14441c54032003c403c9680c2d400030600c101c500d40e10020201c40300c10f41c039816203000304046420215000460307000b01800e0140c54440301e4040003119038210004d0040000500c003241c800c2480744650b6000e10945140001159504610309010984040300403020b90707900c0140740c0b5940d05007a580e0100d07000d690140d0700d41c0d4102000c0103003503a0008103a2112110043d5003120030300c000800c4a040e261036107158208102100382001e140c003210800070045858140100b00072800b90807060351103035204000c200002071005091990052206012a08076078841c206030f803800420415250304560080b48450701074190b548a030304958610b40c0d0410080020745800e0746d0313921903401103101150754459429103152107010138040610f41050b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 638108390 1250 638107140 638107177
    0xb03010f05071e210e0114060f04020f16030512070f2708100c080604150312140415020d020f19030507080a0905090a1512030203090a080d0207091401060302 69
    0x600c07000c4041c0c4c0751310807501080d159048911206024050b2040034402856001110700300500080c91002800701d03854051900070404c0b9910307034250019a610507440700c45000500c051450000c20b01c2d032124820005030030001011a00c130511900400d8000c8565440703861a032005405e8000b482207858803801d004034040800810300d060180300700c0c05140072003100410003c6d0f40d0440a0003000c8000d00b2540194580154400c40390364140030901242d030006503041e02c0a00460041b991445036101642e214000042c0014800130084071581c2031980039820f44040c1800c4036001c0303842e42180d20282220340e00408194009148050304c005215229084c00c038070345451035682d00b40c02c0d0026040c000200704039500070021403c1513014140d000c08680404c104400c0b0349034050440400e2801114012076034181b540b0b003014002c00480300710400041c110001c65070360f060043c0d42c0d4002c41c40180014020f0301c3d4009020401030041001030b00002c810410560f0803c00200c00a4210100c014815044003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 638109640 1250 638108390 638108417
    0x30510080703110609301b0f0103050405030d02040b0301030b090a051b01050c0601090605100903050d030507051c09150e0606090a231e0402091906090c030b03010f05071e 75
    0x7240846e920301b014015020301c40030030b20282d03428005c154080f40841045184441c4840d42d604000c1f0f0790b4a282401c000a80e501d4900340a49075000e0019000c0b01c441c0f00143c041152003c44c0045e604a0f88140700d06441e41e628081c03c60f403142110440203059610010000d006004041800303100c404040c548942041034104c100c0e0300e02082a805148032030b82d6000c05001e141046152400700340954100703a04024615600c0e6a0745550244045003059602e80229034a0740c4240102d441e1a100700c1809114080d81401420040040c41c1045500e6a03290544808115880c00307213816011002010340310036503c40f0180103501c5c00007824500c403256500540d0b03c1d4004c0d0307820415941c40314101d03180481c0c6010001226020343d481a1400e911540400b0400140d850010b40350307110a034014299041d0000c1390065000d4609900a40304442c01c0403010109560305030721581090030105c0c02880300782c0e589080c40c1d046480c00c0d28180000740303204444030083d0039044003844003408207150040f00d08610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 638110890 1250 638109640 638109679
    0x40317091e123004062a0218070e0f06040e15030703030c05070609030c050d020a0801060902130518040201110a0204050403050a030f0b090a0c020f0a03030510080703110609 76
    0x400c107002d080000349900d004400000e4260454509403040340620b800d091417030191080c0c11b42c00b405d492220ba4144a41c40e462250351043c089141d020746001003803a0341c0302e0365207078141085030031000060305a01400114504007400c0014124041c10307007841d00d810101880046000141504103031880d0002e84940342d10204203000c015030103a581c6410b01141440c250742808040c2d4004c0c810000641c0c014008159000e10200480d03030110b42844003040c42d40302282c0120005c0c2d0050200f07501c3e01d2400900003500d40c008085040016203041c22440e142c0c82080100c91002d40402d20905842c4c1c000344c0107500406201b040000d10708115100449180d000400365503040320100c000a10116600160719010b0185003107140b007036201440241018008604444030060040f00d0064903401c0243c0d1590080c8043c801a030060401c0d560340c4a43c6080280c082c000546819900c005080da000170102c0b00416048150f03640200c4060000e1070440402102e82c00c1070f01aa544510501c2000d014a880f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 638112140 1250 638110890 638110903
    0x50a050408090d0501110c0a02010f111b19080318010203120c070804081b040e010203060d0b0709031b030231091703070f030b0103151514030a02040317091e12 70
    0x90400041c2300d540221310005284240c1034620302c0c10700802d0304881941c0c03031020078801e4100c090100040026428040081d80798040051840a0341c0701101c0045641d2030301000502c1e00400508040d2981407101004990f00c1c441c0380500c0740144160004038481d400d01400402c9400c1c0649015420151240c40321410b0680007200705050750441c501001607804d0034010f04600084030030086065240072000b16401440c2500002d0141c11444001140c581c010003445001c0c5412609a202e9168400c040d522040c106010907403240305000040d003c45801071005171109246035100741841c0d0201c0130420090030041004440d0741c043d21003140100442d0001951041c1a2030350754608921555101400305c520744521030b8101030405600031070054000c0d01440846507000c450482d030680c428002c0710618505088c2244003d000030920a0f44070007900600207603400350440d000c160401d901c1066451207129941c07a04000104954210304048003044064500040c004404151641a500d4240355 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 638113390 1250 638112140 638112157
    0x604060509090105010503010b071218171504030504060e06190c0201122904020c010e0604031e0804061e020d0e0705090c0f072103020c01050a050408090d050111 71
    0x503004075401c40d141c584440e00500501c02802c016195504081d00d6956510640501524a110016540314124850316052031035004402c110182e040d168201e00808103030241c0c1d804000c3c4100f0740e000d0103144004100d203020741c0d4192a41480d00d450310000f81c0d00c0410712004d65a102e00103014000c2c0341813a4860005c080202c03550394910941e410b200141c80c2241d9810003207076507450405c2c3e5a4865070301114041010024004018500c1d0310100020302070700c14540713090502d5003420b01c124004400007541501446c840d80703512100b4000d001450440239001d01c000000107120350081008540c8a60280210058204e02c0c030400c24009000d98043c0e80c41888080c40300d603581d406820f000304080c09031078050b010484d880e00341401e11180514240c020113459000b1180009048010401c403030085951202c0d024002280c005400030000d03000390829a0841840c0d405e00d4005400070311103102e1203100b07a034441c1d8040e003003102000c2888003003004c01804503103541d65002d0b442c03846131b007a42c080c1c600c03003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 638114640 1250 638113390 638113397
    0x1082409040b09010e0109021c0615080a0b07030b0a030308040204090b01060f020c01030e0604110607150207150b03070902250609110102030418020306010c0210020106140a051e01030209060406 85
    0x1d04090240d1405c448460310003500e81c0e4900801240180e51702060b08402d641042caa009400d503041c244030004040c4c90080c016414a803e038002441400402c5000c40d950003104500390b03507920000c00b9010391301e2070345200b54031001082d400c1c00041e010f50b01c1240c000740040c00001c0c80404a82d070360440048203070841c0c03012a201418121007a03904000c202c030300d207400f840e00380304840055414a9844030090b000906904007101ca606450315448103549405811482002486c991078407451700a5100110580d203d1880030080402001c96000300901a500500244241d503e08250100250000300c0d050320030541006a134441217081186c100c18281c05180002401405031034540150754402c2c00042c15904203000400200b1248000b404000b11080c001580e42d649542c0100d42540726040000d42c01200e85002d4104194150312070030503030305001c0103c0d4003140d40004012410350180b28031030380817440c40404143c0451407104034942c110b06041c00350400840710f00207030b000d81040c0c0001002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 638115890 1250 638114640 638114663
    0x40305071a06120a0c15020f060112110402090d11060c070b030a1a031c02151504061406250804080d090e041502181210050a0b0108240904 61
    0x12450102d115504550f6010028042c080080ea100701070b0443d144541e21450100709900b40c0030341d0084c040c40a801d400350065800303968403003c08020710b00450380f060b240b201d07044080c4591401c0c40d108440400400402c070b03001c407008564541c01502c102c6040c01e90019001c0c002d203111224104407042c060101429100d860349130246005040301c1012130120401c030780c031200142d099100482c0c02107a0140c00f9002c10409030011601b64540f1040c98141c140018400c0100a080406030f020000c60038001c0740c0502c0f0203503917460001c6415561180b41f5610850800111604961002e907110151604a040340c3d140340382515807208942080d03210150710740105010741c03409684449a80d01a0105058070039440c20079840760000d1402c881c52803c8210350000c0c101c00107100c2948801102c0400400e5043c450810202960300c1d0800d583c200c280490400001c1a0764071400d001d42114000103948260322940d4100003100c02509030310a100f180603c07030110300030b00d433603c580b601d105502a203400c151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 638117140 1250 638115890 638115901
    0x60b130e010f02090a18091a0603010e0d09050d05070312021509060405030306040222030c09060b092803061a09010518041101050c03040f030c0518010509040305071a 73
    0x251142c880c0e400a9040c81040a000c8990b1048010300130385415481d881d044030368540c1d03418002c1181500290044014005034030b0803404075004503100b030344140c000780600c1a042494a03910880300340d504004c20660354080c0000d0608500e4031980f540030380119078106a583d141c607100c8118541c14600140c1114600081d1040320541c4103030400f0002c00140900d180c9911025100c0c0009442a40b02d40e800040b00180d00d840360401220848000d10080219035882c5480c44155075184030f62406981001d02c00541e214412064a402a101410384881064000402c0d0040c00e541141580408698070000c80491110310999030503402c025550403202c0040d20410420b0b0380142d0003240301e880f4200d8400740d5690800c1905421607803004043c3c0186800d5001604c943c080d01c0d811000a01c0046000600f44c0103442110741264051001e00801d107840e02c007400702d001c48412441240e10361800040082d82422040181d12500920340340381040266a00e070703860284210410070340350f00c01c0c50130300c035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 638118390 1250 638117140 638117143
    0x90c1b031e03020915040311152703061e0c2a030f03010b04030c05040b010c0b071b060501090506041b0c020a0306020d0b010e041e05150612090705012a060b130e 71
    0x10b003185000c5884160f241c451443c43c4041e4442c0002e0070041c3e4202b100e9400440c0c042d100369600c1041d0040684605140c20481d0b505041d12922412201040078000b1a291075500c00c1201e00b09000c0f000b0940340d078100100340c0440c0da4400305d1480405d2004005940038100350300061806800c07406805617845156003444440000300340c0206d4031562800c141b00d10141c2c2c00110b502c00c110ba100240034415990a4401c0e540f4101c0182c92100a86914005400300541c2d940004d0682d4a1000104096228070052000301d500c2d28400580358192241c144200074000c04400319218801000140c00c0f98a0b41d441c0c509980082c244201540d448006000c034541e0007038114140c1c0103084d00d04118201c0c2036043c5451411a040d60400f03803e03a59404201c1001c114030400700f40d00c8000d003100d581c908001d0101c0300345000803078540c20903001d55032010545620030b04211800c4010102c9981c0382e0003405034111a07071143c074981101c2c420369800070107141d62251022194510104507001584c0c020400545 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 638119640 1250 638118390 638118413
    0xf0905010e0904020a32040b010903060504050c040c0201020903070e060f061305030717010f050403050d020a050d020a0207150503190509100e0c030c04061a16050601090c1b031e030209150403 84
    0x200d1052381414021600d86c0d90040d9520300b00e039004103020606403a24144181080b44540115070018105015000e00c10b0301500102060001502120405503882407964802c5409035440390740101aa0810703032117850280054518055038891030140e203540c60002910b410700740d41c000d00084658240c9000d44d03440c00e115010841d24215428041c40c5050b0740c006040744190076030b0300c84895000c00c54200e2103100c1c20581d50203c40c8600115a615600100a0b54800c0340d03200c0d9815103844007265800c60b500c500180c900039181941e0103503480030140c0e0020040c207001411220140302c0e00c0b0001e046480b0500440c0e503100082000303440384190120916040a035004565401141800400c22180705ca0318080000c0501c40e400300c03600c80e16000c20b082c41c203d0490700040c00c0303440f8840011a5a1115a00c642c10b44501601c0c3d00300c1c00c110300c0720070541c642568140070b4082421034844007501c0d130b42000c0e1404204003500c2c00618284c13446002804400105040741e8003440c0118040c0104607a65030308 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 638120890 1250 638119640 638119739
    0x9160e0a0e030306090601050c0c060f070c1d040f020411190909020c0a020910050d080301061e08181212010e0c0f37030c0f0905010e0904020a 63
    0x2c0c41c51840e001010425030700c80030349070764100400040d5a617400c0300309016000368100000c1019035101c0b03c0d24051015600f040f40c064510246d81000000c0030813410720046030030f0542c0f6941103000d80d038a8854298815030808281d0f0400d40b18411501080c03040ca00400702d4000c0b402240300d01070740d20a0001d03c145804d03040510528410890170410350030009018690326412100784a0554840d041c9585001c400d50208d45c111901c00306c010200440d41000e103040c1c460b140ea450980a03c8002c0b165004a03040e5845404103107218007103608640240028180c07500340710200c0d84003480e5011803040d035601080b41c4045654100c001842034445040e0316981120010a2190400707140264008003031103001000c0c034010703041e181da9000c4070709140d0448000c01ca0110b045480300076007040260152848040c121300041c074101d0340780080c0d4020350002d41900c10603968044968400750074011080d2014209036480f224003440011200800041c0e0b10001d141e119403030380c600c01c0d01c4011000f4071290200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 638122140 1250 638120890 638120893
    0x5010602070f272d050601050904150305030307200304081203150301020406090e18191e290403170604150e1008010902030706050309160e0a0e 63
    0x4120110321954100103032801c00d01d411242c10020340200f02c000080e64940d40181d4140b501c490308000794620b01d05a551240d00030b03038143d490304c901100d00301c074022242280410414031244005041c41d6008a07074099141d0380c00c50341d079070726601e5451031908115000000070380c100c01e214140d0040020400c030801150001182060f0030300d10345c81e4880c1d15260000039140b4002c000210111052040b0307810300c1002800840d61685c649100070a03904150255000c40c00060011681341d034155801805203207803000103859020006014003a00e00c88041042d84e50544917080f02984440c1c0c81c03000c41001c0d2007444000100380d08003110240f54089038001c103020b044501c0c01c0001203a0041502050006105100c1c45190307030b904001801854403001c000700b640641d8102240451003075941c1c49c00f0321700781c0000541c002d503500065800d850a548000350940c0200c1820000540141d003d541c0020b10a020340b000400641c45040d004101c5070f1055500c01c0c0c1520078020a0206440350b8950b00c0c0c035000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 638123390 1250 638122140 638122153
    0x51c1b0f180e09100902031002070c0e0901060321120209060706020d150b07050a121403041b0506090a09020d0e0d1211071a04060e070e090706030b1c1e080d05010602 73
    0x800123920340c018081ca5410103900003452a04002c01c81d00400301600041e0989110f504101180b0b81c000c2615000403113164010003040c030708009200820005126069940c041003180c09000c1d2006508205a07441d04a0b00521542002070312500103030045402c01c1c2000a001c0c2001301d070700c1026240e60f901c2040d24801c200402408543c0c00701c1e008100681000280d280600d03091400c8485151242c00e8002507200030052104114050300032114071044986c050900d2030715001002801d20502c000c169208451a50411109200381c01424544205d21400100d00c010084410b00b0000c0c079400807400582000034100c0e0002407485201e1151000c402c91600740b01c40c5590312035014000500b1014130b81c031500b000604008264101c4031302d49081c042a52000c50361840003241c1d0080981d9400fa681c001c0c480c1c003251881c032074892000810303001444003074078580009030300046404240042d100c0e81034807000e16103003104001614108a1094240960b07030700c52202510116001a0040c408541140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 638124640 1250 638123390 638123393
    0xc04110c060114240d050906101e03061a060c150a02041523180a0e071b03020c03010920240f120403051c1b0f180e091009 54
    0x1500c107001500010384c107001803407184000d6a003d4020301c100403005500700030800425003008100e080c02514203480d4820f02c5619840450a10b01000e00e400811100d0041c040011441075040701c4050011082e400c04a0700c222800304086e68005c0b0031a114a40c051200e0000ca42c401040440c0d101d928580c046080c9802e0940050300880134040120070070009500344007041010765080b807483c460810781159200301d407020090b0418104101c841c81070702a07040010b030404510399641e20859440d9200d0b00700200011542d02480380c2080248e0851041100b11502c944003441809560741c00f692225440d261602c41c40035200607030070341e854010050801540c0008000c00ba03000c06c000c0e00b0410701900d07842c25071425805401190342d2065030454210a10003455000402003222444100340202a20000d00c0c07a4001c0d2342d0520b03003250400b2940c040a0100902c11000d07800c0006191400da030b19004151000c42030303012140c0040710b44510b80c00501078810310030003041d000a00d0f00c0c1828040c00b40d89 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 638125890 1250 638124640 638124649
    0x90903020c010c0317090d030e0a05070626010e0f010518071d060316020609060f010302220e0c030c0f060f03060301060312030902040b01030509030d0e0c04110c060114 74
    0x107008216050003c2035001d00201400340ea0190360358280c5034951641490403102c0359685140030310440d80824500701402511031008503080101e0b03030b0444024441c0d00e281c42412680181c038122080c80003980c0c600525014005421614020302b034000201d5080c0c2000c80a1070244281030303100b20700c600c3c02e88114108444030311403031a034040128100503003c2c92080805580240482c2615a4010800810010a80741c2c1d8455034908d1070495084036125920402c1c1903503504070a540500740750808400420041c035001c00f803600e4002541140d40a844035121a1109450b5030940310b1455403c0140900d41c1420308100c031f04581c01e0216003007440e072200b80e230100b1a588228540d62012010000000e403c0d03480940041c001141d1040100c1c1d404200804014010100e0b00c004a100f6814503019003420343c03083c020b050090081c08003447c5803500140c2240004c1c110b542011915004040000203a541c480c8100c1407040082e8461541d9035100340c900500308401608102001031407401404200d445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 638127140 1250 638125890 638125903
    0x3121802030a170c010c090e1036020c060402151903150f0303050a1202120f04020a08011b090b0f1c0605041815050903091014030c1309090302 63
    0x104820001228003c0c403c07078030315620420030740c403156600b0600f0808402d0b134854904400c54a0804410655403a0b004006003504100d1007181c0e00f060040f403440c11036010724400c4400800c1c54280103619010100d80c01000c3c0e0f00061414006500010300300810350500101890070900a94100c51401703d1592038000007092100c0d0302c800f003659441d42e0801005030814800050110003011100c4640d41e450010080e5100040c401c0c0060346003a00f03035101c0042030007130b40c0c020140800403074100d13640d00c20842042c20000b881642e1066402c000010074080c00e12a900f10440ca001415640c1c0100c008040e00c403000755440520742c61002c102111200c0c00f5801078495000007569000348446600c80950050300d07035500030950040c9081400f101d0070040c2803000001d2441840c2c002540c00d2480d25800844200b15801d0a0542003001251400d14140100305001441c5062042003010700800441440e04125071046011070001200c0f60300448040f02030005001030107082c0a0b42d00240e600031349949 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 638128390 1250 638127140 638127143
    0x18060f1a0618010c02150a120209010c0f082106040b0108150909100c051b03090f060922020c1c050a03020f0405040e010f1506230f0703121802030a 65
    0x301d11020b40207581c4c440c040301d001013600100b0419504010703c1c80510240e02c50091100070580000d1110b450a140d80255640508141c40386200c050302600c0d45590390841c0a030840390328a00300328141d0900c40c2c5c11168500d40c1c060180b0a4680c0c68140140822140070806580c10300c000c2c8401c1103100c240305428111405002d503032406840d29180425803400030f0210009015500708030410403890782c4100507100c0045406440f285408006041070b4613485450700881c1c001040d040a4512410407000030b02c5061005060060640000d081c501c4201c42c0c8d000440741c016400043c124052001001495860084009013004901c64190050410320a589030801495004100240820860802d0710b00400e00684103208102520781c000c2c0c020f0480a0305038009a241c860301c20114003c4c1181c8400362500360b10303680542d0785001c42c0c2620301180d040e807a1803c000304100e035110f400e08150240103074510940b11100036139200351700748090310410180841900e00d040340c618003503a40003030b03c04201ea = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 638129496 1106 638128390 638128417
    0x30a09031e0f230a2f03090f0411070f08120906270c011d0d0308190522050a121106091908030a18060f1a06 48
    0x11282c01084100c865424048a01018021100d180d500c4505d1001ca003000c0244042040e02c100c0714813076107269504045400c00443c01c0080441c1da4428045500780f04240103c4240c00c901d01038408042e02400491054800b03100c0414221203006000010f0107102e4079000c000959250310690b185181211030b210f05100071000c2c52000a003030203660b8040c00d100e1a00000442710643c0c00304500c95103100a400d640c03d0750341d4403180740212603c60340340c0210318901444101c0c8160400c1c42c86c2541103040c4001c110380300c0310680401d0308030898000445807080c00c42c2845484d003403610300d000b04444c0d02c08812011040e00100c4410b1400c45190845050b030b130364811120344a5a01c07039000c2c862482e540c40254002440280a158001040340c40012080c88000c0c03805011321441609440981e03035091451002c185070b01508030300e0100451841440300e010f8012680e00d126010b00e84411 = true := by decide +kernel

theorem cover : BRFrame.Cov 637949640 638129496 := by
  have h0 := BRFrame.cov_init 637949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 637949640 ≤ n) (h2 : n < 638129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
