-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:32.180507+00:00
-- url     : https://prove2.me/submissions/e9c8d1da-d632-4863-b2f3-5e9212cb181a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 380575539 ≤ n < 380755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 380576789 1250 380575539 380575577
    0x91802240d0906050403080a1a090703020f0f04050a0e1b07020406030b043008150a030510020d18021c1b0e0f01090e0312192c060105060406 62
    0x1040d2210307a0014081d0b0315075414844000c0000320360a50100d071080c40002c0403040148640c06061481e0b81c05031098802400034040600380040ca55814582e00300322030114089108003a0031000000402c290b50b40c2d00b064203000309800c180d8001045880044240103112032130031824003043e0340c801d4a10351690028000113000d0322032350380003810141b1813009200611031812185080350035841441400d01c0c2000003660411900344141100180408000ca25841d403018074120840f1002815004820340300d8659500b0320711106103181d20654000394020045050340150b81450039038207504070a149164010450185042c2e45e403c03010411518000b0400c24051040c0101010014220341d00e652a070000944c1c111096540006007010440002000301d075074018400d00309904000b9500b020311202d42c144616401800c880c00032040c1c02034a01d0f000c0c8003441043c0604021201d20810016001c201000000c80e0038000720641e00004c00622003038030b41d44115402c907200d82c6000c040b10515919004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 380578039 1250 380576789 380576797
    0xb0409020a030f061a1003020304020f03121e030402100503040c0906080d08130201090e040302030c10020901180522110f030403110708120307050d0c0909180224 71
    0x20750044141a021092003c00840f0140061142c2000c020000d8418126244901e1110340c0301d600441c882450784d8141d100b90007450704284040c0030b01c0558410307000005c3c142081850140c0c41d090000c40e003000c8803c9245009820600384041c1c01e0301e03500f49a00442c134541e800303012403001d02400101090400440520400c01402a01d90070001d2540340e14000791034500008510000030601d070701281d50303164480c1442c00740c030798140c4032644001c2c80d1200c8202e58850080050702580424000089044010300c2040d541c100d4039000141c3c2c5194100000d8035400d585000c201c00241d10030002c5c403103611240c007840c50300f842e540f07814505034580241e02400380c01103001c0c68a8031074010590141440b00302c8082c60169210340c641140d41d119041c0c2c0300380c0e20219403181d600594484e41c44810100c00301802540c200c140e07482e2041c6801540070038501514130650400000928180381081300d42075521504400c2c48024040d031162100340d40000da00200303202d50321584180402c0d042100900210700321 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 380579289 1250 380578039 380578043
    0x8060108161815030c0201050f13051509030a031b080c0c010f1104050a12120c020f030303130c1205071703040503100b040b0402070b07030b0406081e070e0115030b0409 74
    0x741e42c00c251551500000a081c0d8003203980441c0c180a69042c08a006004440c89949251070386203050b51030240203003550326560b80a9800b400b94400c54103d607290003003014420710008008590703904803204002e00300da10b0891410420b60f00c0149650465034002e03601500401ca9205540e150070b4030b58034942c014010030350044107840c58680300454260704d0703401800403a24200e07010034580f55a0b41c03501030f440c08407960040405540c13201c00704c0254000d0741800d481a0025111108101d47c0c4804a440c581c003d4403100c8800710703241c0f905001c1000040e0300d0300103000c0002ca0100480410b40e641d03070341d030785242c06100400d4150703160b00020040200b0139140201310082c1202c01000721410310000614940086a00940c00c00d00b401c861030806000300d030010380c0d011031281c05d503603601030040303004110b180031882d4020341791400082c04004c2040348170310542c900e604180130242e41025892420032994040503000809000400c00d00c80040c8008803d000d4a09012a00d901c3c40400200142050180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 380580539 1250 380579289 380579327
    0x11d0a030302061902070f15060e010308070c05041e110c0706050a0207060903030e01051b061509130f02060d090804090b011215050d0609020a0603090209070806010816 74
    0x4004140760340003607420300805921414000704c0c40350303803844000d0f0310a461014101c070121080e1040014444409451281c0c45035200003021501c0c0c19500382082401c1e8019644c01c0d9010039010140440110f980005003400c44080100f0b14490b5540902288081da02c03004042d0345415074180502410100c6907950440419140907949030700340503015800010380e00c001440388002c0031490b680940c81d214141c81d01900c564049201c600d00440b0f01e07510070340c4021500040141a882c0c0030000f048458003035a55110446914580c69041c480b001100800c001ca012412031161008590120f0140000fa41c05840349035940c02144001d00203060200d02c01440050f0000e4000b0f10b003501c5a204032100303d000d03a2144c00307044102c1005015105c009481c0d89e01c0b40416a420070071864a400d01d00002e5114072408a80c6140c1600003401e1203a09901c800e01007a1101001c0c000c40c039100b150283d10030018240b010440c00c06500003420844010030007403030860408203d01b1114001c1c6500c01c1e5114507401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 380581789 1250 380580539 380580559
    0x6040b0102010e0f07031b0b03040618140c010f0c0f0209090a1a070905030105090705060c070f090902090f090d2006150a0812090609041e02030f01060c080702011d 72
    0x1303d480ea407881d40d0b01c003d481d2401905070100d035000c0c0c0c100d09282129030480880c0c0c21601c80313855036002812482428200302d8007a050384c10001d0300c0040051080b101c82e42c050b10b81e00b06a03074005000c60440c0081502000390080c5003100094a002c50301c500d00c0d4040e21400312550ba016841c5140c0320304d4030000340c4240e4103001c50064100510b823507544990000c0d07454030b24035550f40041c1801d0b24001c1e00d0a6001e0b8104507000c1c4003a041c030030080e002d014000d01c2103800d43d0f903076201c1001580e100758001046080e16110228150b00786007050759005a80a00343c1c00e070780c0c41d09024054170340303140750740103404c00403e4103511f009034080301c02000600c04c03030034282c2d1403034107118070b504505440c6058485e0045948140000e8000c10218045226841921480d1320303090403c0104015940312614003544142d84d400c0744c03031071100b10b450000726202010900582ea800e0070b58840c07411110581c006410030a890740c2d04400a0003a0065903212582130070902111079827a00d0680e4514081c3c945143c211700c0780300b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 380583039 1250 380581789 380581813
    0x3080306012604020f0d05030909070909020c0303101e0b07030e04140405120408150a020d050f190614040f06030215070b010519050111030c06071e0201050f06040b0102010e 76
    0x18042c18092442201c00500041410050002d1640e011002800d01d07001801400620300341a440c50790b12640518062817802d44a0000768221317000544000a580d0000c17003000b0340c03041039000760f0018040402089002103c1c4480340407244036a400760b4810101d011600f4404c040c0901a8289030000083c024800482003559150b1100320484040c1c9191041d1004e101e40040302001b00c40565401c680500a16440d40507003500c620f90150903e1a183e600b0403502c018a4084c1c80346a001d5010b98a440c4510700301107610742c501c41d0b240c40b0044075843ca410810051034040c181600d4052200340c402141c00851544900020802648007a4118129a00742550580010001d02c0702c0780c0328088004503030741c0721001d20170310100d59100e1110048241c90207000c65800f0301290103211300300303000310785c03a10780c0749410b0b10f003408800c0d66a20003180078441e44030900d56054816007145402d0f0b20013080103240c5000c049050403005442c03d0300480d520414003156920030342041d01c0903840c85080301e103000081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 380584289 1250 380583039 380583107
    0x90f12032303061e03060702011b050f030105040b030a170912030403020303030106050313120203120f1003031b0c18140106050a051810080711010b03070308030601 72
    0x44a0480004294207145001212401c20000e03126800c2210141103a036804240003940c40c4482010303500ba1114400a40700d59010842e0500c106500d50010503000108502c42a030807205120030000d010082c08081c418100d0a01070341d044031001c903000308070315000c08007007420011058800340c80350b50000340b00350701020320b5402007142c0f02c02600d01c0d1129500c0d40310f106403a40242e0000a606401c00c0004200c0c05208074007031600001107544210314403406a81c0c4005c4201c0000c01100503030400305944a081001c03101b2030b548510051004000c0d031034044000703d41210180401814000c01d0103500e8030412820b81520b6995900415844c015503c42c515030802c01c0c10b900e1243d50080c1801000800300030308410b034604889032070f1190742c14070141103401e8690b600806481c50146080d104041c90781c0d95210141701240c40706440301c00d0035003131132040100049901d207400c07205681052a028116240024403400716500300c0c041c15203039210000107c901d80c0c995540d0b89050b400900b42d00d43c3c04990 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 380585539 1250 380584289 380584319
    0x305181f0207080f0a020d0803100b04090f0c09060f0c0302010e0706031b0509010c030804110d030f02010b04060609170f03040b0c060609040c0b0904140702030d0608060c040312090f 80
    0x1040f0440d0343c680c20000034999120100540250071085503415071000850040181da000000c030085001d070940c8600c0c5007140d030340069000c07200c01d035101e840c00c40314070780203200c0c010058000b8034111214a04240380030b030000040085040401940400741003d1510030f511520210503c28252902c49075207100050141980a84d081e0002d142c1e810807608280c0030300d045407000c41c03042c1c45800424a0f03c0c1c905440d10342c0000c0041e20000b040b80800711140c1da610031144481ca00c02c3d03d0b45c0c400a40007100003030840d42e80013051400b45141442c284081500490342c0d50444a01038503140c515202200d24a041c02d401e4401c2040e644000b1401080303550170440034040c0110010101c41d02c070fa0b503900402000410699010300040340400c030030b102e01030480006000040001e0300c045002c4103152040135020104a0f24000140c101007608003064400f8050300008002180c0107101c1410201042e005034419848014202e6107800701c1c0003003850140e10440c004010854410341040c0c2d890300320a0140e00c0e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 380586789 1250 380585539 380585549
    0x60207060809012c0a0c2c010303120b13060e0403140a140d020c070b041406030603101d0312180613031d04020f040e070c0305181f0207 60
    0x46488006071503220148502050708141d440325001140c0c080500422a9040361200403803030060094a00c04154101c03d401d00402d0081c407d0546a08513101d545c003502120714410306451190300041002c03c0e0b028940c0307a8420030424000840d8107100c00000d2411448a03100d0804600b0306500150300100522158481e6004ea29400403040c0030658800251082d100f0540102e41859084030305181c0c100d000c0e003004070401000600d001c850035211441c2907100d9100101918002600340b0140d0351004250f4075826068410301d003903003031010000b6101e540640754100c200d69070350305010300e04d40c2e1948003c10060b04001030b070759035074507682c9402443c942c00c807003d40f04079140d81c01c854034403400090411310851494a0712200c6200c1564102d8030b410500003400048400a170501c030256989100402c03040348080c0d1001e039a1f40c649000c00c54900d800500c5c2c04180151030104102180d04107044402c2c55001440c01c08242c80381ca80001c542e27510b503858441c152162000105070843e0005400010381e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 380588039 1250 380586789 380586797
    0x7060f0c0831060204090e06090715080609040c030f030e010e010e031504060f0f020909010603090b010e0709030803040b060f0a0528030501020f0319050618090109020a06020706 78
    0x95900700c09030b601e0002c0702e1a0b12400005902d03441c000401000312503140700d4490030001d0b14240c1e035040848256082008480c1c1660030281c18451190b03020008000104609000610341c180d9100025003120070090609004591840009003008402d5080001131a0b00141e1041d210200d030800604228550400c40d0214500c868003108a60155000e040b4401c801001440045544650140481000751044640546900d6000300c1c0701094010012400c3c2103010061311100ca1100f0010071440c1a841101418607040030800400c100c0180c0234103562003500310072001d45401070111405101e40c0d1002d4101e01c1c0201c2400100b20181c260749019200882d403000d0040c4078503040000c01c03411481038540c410380e010405084400216006600204000448040d241d540c0c0c480500f66401001d03444c5a0510000c02c2000c10020350320000041d210441b401c128074506000440c180822404a114040340da820004110703c00035040340500701d9020f043c02c0303055507840801035610b003107a0103424089 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 380589289 1250 380588039 380588041
    0x4110307090902130302010c0311010c0f081806180709050406022205060a031a09010303020d021b06090f04020d1b1b021e1503010305030909070c05060a05060607060f0c08 75
    0x1c41030b6802502c640850f03114800c48050314690041d02d050801e0300c000ca0600076081c88499892000b8802c418603110180c1f12000e164a0480c8020f000c03000c02030207800b61307001181c0664404540040c0f80b55011195078044c0b0440c0580f8141146040210390150400904002c10041007100f10340250082c01039034026001d045041d010f11001543c00e5004040e0481d40501044048038402d82082481c42007450542c000c69038183c2c0412088007090300140d015900607001c00e0601541044034100d0003404041c100c031811400c00c0001c200b071140740f00301485540c0e940d8140005680b580e0403648074101080d000c000000e098186442480c500c0e040140114003012281c154200d805034020000c2c0d0740c003c00808420014080701c1528110340180d040e0812030302d801c2484c00c00b8a00006502a500a01c01940c07140e081a0070001265801060041006101c403408000148006000d0360080b0304080082982d69400d4081071341c034001c0000c040c00c0c00e410441c0c0108070000c81d40c000f181c8140386a48121203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 380590539 1250 380589289 380589299
    0x606071709130e0c01050f04090203090c1903030903020918010c0f080603030a080f07030209090406200a08240402120402040b04090213090302100204031110080114130603020411030709 81
    0x21207881c0f40c0041c03400c0e040603400c0883ea40c8914000c00c04204004d001070309082d12124910126007003260340c20896030105540b550649007568041e18110000341c1c4c4160580c1c00e558000f0418071541c807009002d002c6100204519010565003c4046403c2c000200b040c45102c441c010400000c0c801aa0080342d00000407600c0e0381004411a80d075604039844104440d280c50142c60b101c488003c00560400d0340c01d0107012003690305c0c81030483c0200e0060502080001040c0c40305402078485070903001c412a002c003c00905981c000000b07940c008108404190400d90440c0d214070341d20305c9a08175960040c4002549003420b505101c0140c06540203071010800c2d2040101444121802290080d48c0712040d9005d40c60b141200f6040b0380c00d0540319105485002c00104400c405a0300a03802c101c81e0511000b07401d4200303080c1600000341c0f00e0518984009154504583c1e89050340f1540650782c01410307941c601c10415100c0341c1110009642c09003007000342d40408a29202c86030015a03404001138604100011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 380591789 1250 380590539 380590541
    0x16050a0b092e271e031704050a0503041509090204030804030813120606061706061836090106030b06010806010c061b020c0a030507030b060607170913 66
    0x4241030308201c64030524824500b010800d44100b0000c010151104000c01c810155890101d9500e289546129400c0c01e4a00d80021041c0392007070286003034014424440c0c042a401700250808101d1602e070346125499a040560400c1e01241e0003070017512001030009120f998010800d450003440355540542c040e21440014240d102e24800917140c140140001d01c04145010000d02440c99200e01c8070200b20b0342d032100281c6900170900f080c1c444a03550340c0d042008582055452403510310000c846412860304d54000341882c0580b4440840700c0000c002c0280700d54540d1f250300c528071101c0b51482d00c0c80c40c1d03e503c4407203610803c015170451a000701d00c012511842d014000c1030b00740c0e58091088001c40d0340780401140c403000010503590400013907510301c40118030207200f1407182d00c4a03001444403654030b035100a8500b03a4066a168021400e40c2002c0000c59070101c0c2d601c0940354045c20a0710341c3d403180d40020b281c9029441c1c0140c28401c911003e00c0200c54000001e15a804081c1d950207616131003000c1041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 380593039 1250 380591789 380591803
    0xb0310090506300d031e140123190f060c0f08030c22050108150307030f02010509060c01050403021c0203030601030c1107141807050a1416050a0b09 65
    0x280c0080c06006849075010b598141410a41189641c1e110f203150010319651400401070a0b03100402d50b61401c080d08007a01341c01a040d080b08048080c48468110250001c1e440d07014482c44104915001c02500c0c248040601210813000007041c0c113456808101280391004028807402200301c03120b0000043c65406481010341c040d4103c41d61a50480d0b85407101c0150f54801440c1ea05800803c01080d503a941c0f1036000e20091a03190b82a03075a00c9400d000024015401c00b07080071464803c0001c7c0494640c2d00010088c0c1502e510607000b5416031054401130b030b000d00842c0385050340a0408200100d510708150300c4984184c4c001c0d0700f150000c0d80e20424004c0098031810000e40142c10400005100394060341210070b0032412888e041015036900b918080c106035540e00b00100c643d103030013441d02c4245040c221501c4d030002c030024400828100b110000d442441034507940c07000c1c80540c02280f4541c0c0d50751015202c0010f41030035070101200030391401d1500c50740712400899205408101152508000060701 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 380594289 1250 380593039 380593051
    0x115051c0f06020702030a080a1e1404050f03031612090b0306090105010e0307030b0a0212060a080a0b0709080d0e01020d0c0507260f070620190f0c0b03100905 70
    0x1000031406942c540c01d01035849034209907010320681c6008000100604010082c120f900c4e514007903002c0404c40d4113a0140c0c940d00000b400c02c075400382861702c00300c0000103e40c101c90f001c03201a20000c82040c0481e06501070104844211071409503180c2c281f00844801f519402401c2e43c45100241d240d641c0c0b03c440703005c151041a0011525001803003654000c03039581e44e000200a00b00d0319225a241e80380d02c12000200c844040d0180c000c07840382d128000b1f610300990884411034119036040d048c055840c1d07640c9038500000d002042e0341c1000c01e01a500610318940a0120b4605441c40d6981c1c8410241c80d2a800031881030051060500c42410a031003100b1075004241e1110141a0442c03900e4a1058540101d002008120030b400a9580107003a0410081425182c030341c1c0605040b920700301c0003907d01c41302d00f150000380c017200c0d4054913a20940410141c100416036098800301c1d00b0b480c2081491040020b000802118080401049181514015500ca0047d1004201e04e244c1c544c03000d0800e842066440d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 380595539 1250 380594289 380594303
    0xf060f0f120605042307060e09040f03081b0705010917030f0103120201110c0106050a0501091505031905090105011a0a020615040b0901060e0405160f200115051c 71
    0x11480090301c1500b1454206009140030030641041c000205903140848084850b290705c044000c011123a0440d5200d0310444080398804da031843d19031541e4000704400c080c0102000316010010701c8002c030213010200805055003010352a0449464102c4c0203182c43c0744103031101e890042a4084803011041124840c1440c0204908540d1850b80c80c0b140401c105d070030b500203554a0300c00314000441031202030101100c0010003c102145404240f0402c42c0440d00480d04002c15034405101172a200c14030302c000c14400c2d18040356242c1d6048e000d0b1207050103400e41120001d0411052182036030054220f241680d8290711000c45952250981c42c5840c03217840308a0740503800c1540001c846041007900f900040310003400204d00d410446000850b800303c03d0300b0090200c0c0221000e83c03003500b0300d40305440d8000e0501d15903490b000407900c4060510380d80b04002c00200010380d44240b8142c158030855545c0801814001d004d8a903c2d80d0100000b400b043c020b16020795586068165222503160b5840f061a4200780 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380596789 1250 380595539 380595569
    0x31a0105180a170109060c02010207030206070f0e101101240302090c0708070c03060b011817151303032f03100b071a0f06030607030f0f0f060f0f 64
    0x40c07200e01d00181101564055404100011005000c0780280c1c1c41410a01c0001100b040c00c0c039003007003191b0716240880110380c410f210600000360002107458001c925814581e0f01065480b80480358540030050090b00302e800703040b0484000e0b40003210303420800d41c1080244004017070110503020000704048200001d00300104100003604080d0742154100781c074584118070b81019616241ea45074080c1c041182d405900c0101002804454031650075812000d180ca02aa07054071840e091990006000b0000c10f402d843d00d040711429810050361201d43c03031208414040303140500880316100303031041b01540428282601d601000c003110000c402a0041c01c0114203106040d6068090713641c200a000305100d240724800403400c1840075000d03040300c1e807152400c08051144070030f20095002d070142080074040030660501c0416075004c10307210b510120302d02d000640701581c1d0a8440150401d404200003175880c0442070900c1000d203410840907a80403180304c003811a540e112882202d6080d105040c20958060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 380598039 1250 380596789 380596807
    0x110c03100b0112020c06270309040e0a0b04050106050a050d0b070309030c0b0910060b0306030c0603070318080307030c1b020409080408150108070f0e0f0915010602030a031a0105 78
    0x1d400001503540624098000c42111102c440480e0302403000c0e10025800601003000c01d10581e11810182e004120070080c220316040c4145540303009404195100700d07119064041c0c0300a04208461140d908420b00c6160340c14030b8103100e4003d10190280360301401d10501d000c40c1c1410300319484c40a6903400821186682d40d003540482c0103101e441d600300c042000426610001c15005040c50380241b03134000240c90810180041e42c1c088850345c0c0c1c050f1405030000d0040016580c1c010480d0319030010161140b554940c0c90b40310450003050601c0c80410182480024402404443e0f07016520886641e00c0c02c1080c4c241641e400d0320114401d00d00c9010340700c644001c003001414190090070209100ba582182026214900503060464407486401a0b020100041002ea6000c01c4400d0003003255031296280241071004002148030010540014040b0100201d040f40d4001c10031400300024400e00c80c0f07515611038800179140d070305c0040c0303880003c1c1c1440290b2a8150128108a041880503158549046041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 380599289 1250 380598039 380598041
    0x90a02010e0d33050601091410120e060a050609090607050a030f020a03020c1213060804020f040c1d040c1e11071701050c1815040b130303110c0310 65
    0x100c00203c40d2941040c2e4180c240180016006007482c0310001014890900c100c2e01c0821601c0c020201070410030415010045841c034401003481c80c42c42513038000300100304c0c0c9030181d6106202090525540d40327070800d0030121100100348035009d552142d4081c4801c0d19140200320b2080020703a840c1b269a009600451b542c0c0e03008800403c25010b41303080204920070040880b000f00d070085c03000c81c1d01007600013072a00480078052003d0501040341d0b0030f5150034858510034103174100449005510a110380700c0c02103402e56413105c0190b0710b482e40003042480507051820004080c0503414040c0c110b8200d055810721200e1800340a905880c140030796135010b0380c90a02040303e155503941040b00c0140308007481c8110140304140021405001c901106104109400d05040d086074001132100001d018180090600701107549140482908201c4000b11412004650200c0a20035030744040010709000928241580b10008010b04407400fa0b101c00c2010911400f00c2e986644442e40074640c95041004240300e0480c071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 380600539 1250 380599289 380599309
    0x70512030a0b060a0801030201020f0a03050306040b060403050105100e09010b0f06091201050c0c0d02010501050a120206120a1b02190605090c06030901020d0e07080304140114031e090a02010e 84
    0x2070030030701288410300390b40443c07026800001e1080020b000d4034014002c0d035804022241d50852040028000118152801400c2d0b0201a002c00d1080345c44030010303009556605d050f01c01958120f0002c01480c2071250b040800503880e03100740c1d003d00c40100c0015a1501040c459090200009001c405000e8204800c10400340e018040040e4400b00a980316041780d20248199885042d0b0f0403002035503560340c4040c2502d81308101c00c00390b04681c10a4014404c58503441214003c40e9001c2c020500005071610010346240a02d844c1038214900040070880010341e03075000140c1000604030540c100c81c44c41e400407a15085c00f5180282207000503541350000030318540c8115841171841c0c1c26500f0318000700d40010302c541d00c10f450280c00c40c0c0d008152051144250b11488040c880804000c01c0b503540b07050311607a240d00a40c03040d8800d00c402010821502d034044c03000f0510a5414000143d66481c003460305260007590034220348a0140c100002414a05000502e074205903016182c041c02d0f010441c007001030800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 380601789 1250 380600539 380600551
    0x406031806020a020705011202091f030e0d0804030f080106081302030c0a08010f0b1009120602130617010f12142107062409020a03112d07051203 64
    0x50002400800704a0620292039454200da020701070461030100010100c540c000c640010651041040036140d943d0100c030010007500701d03000050302007103a0a00342e004025408010203d07000d5407040a058951284d0300f6480b41d882038940c111814400b1000301c0310f81009009400104600310b011540041035195503144141c4010110392040d410000403074140792441d480702070f10769181c042c00c1c8021030345030061040d02c200980d90b01258081605c00140350207079030710550100b0051201441c0510000303030100c8120070b09440240482c1d603a981d8004010381e511000e140403d143d40b07000414105402e0600360121500301e40da28410701e44c079440314000348a0402c032115440c85103503111b01c826600001c0310200e41e00c1c45001107840f0445418844142c03000c6202a8aa40d034055074041800d8620303070082002c2d5090320300010386515003400c0680040c000480080600803000c07501402c000d00d8611402004400c0304200e6240d01502140c80c15030b4010000020810703000b0001120080c481d800246074005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 380603039 1250 380601789 380601821
    0x301060c020d0213140f06010c0b09030d09030503040203010507022d030d050a05090d020304120809030a020a0906061215031b211a0709050910090f0209120f03040603 73
    0x141c1950000d1002c0c0d80c050b042c18011501c0c5c011907480410850200c9520691070a05d00180e032811000080c007010191100400c031070355107800718080c070b01e04005851240d00c2c80c0718100b2401400e0b060243c01504101c604a201c0d41c24040051059480810500710030200b1452042c65030040056600038010720b409220024070091203084010b004034003c0d14007075034401c01d0004440c18401c2d4028104035a003000a401c3d540308200822405001d84400d0608a1700075500c02e0f110501800080d0800d00c00780c0d000380d400301c5038482c007080d55030ad20f0b40100304a40c440c0e11044028200712800c0c1003035459045100e802000303800001c10114200706c841e030700d0000c504c3e21080c4405403500d85d0550b100c1d140c10f101d5500c041c860b251500030403503407080300d050300d400c004d60005036807a0902c0010030340d0300b4a007d664010010440851003880c0503d1a941c05403150314000e010402071a8107100c029001098030a128004600d656080140302042c10b0700c964441d100590301e05030070003400b500580100000e2803000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 380604289 1250 380603039 380603059
    0x6160501020d06050a050a0308030c070f02090906090106060c0213091e0f0c270e010605040e1005010e10060e061b03070b061504030201080a1508070303140f0301060c02 74
    0x50020700c001c200c046494480018050f0424040c05801c05540d08524000c0c3c034000018004035100c001079a500101c000314480c0c6c2e0b0300c050301c0c00344165441207074025048400304003030140d44400404c1e001e00c00c1b80910020008180d4400c1d00320384481c103481020750040e9000d00d50b0f00c40c003241c0e074001c0b000d00d500403c01ca119861418400b00e0840409000c161020246804060200503000c540c180c010f0130485502141c509a07030320501c0c0c01c181c0d001c1211000999807684000c800c0700a421450007403c0c0200300b04641c0300000c992507228041d040b4558041d51030080042604550507407628005e007540d419005a050800342c09481c250010300c0c8103648150300f0f121300c2021500101d003014031841d241e4055900c8011034500014100805000c0703c2c481c555048a20302810554401d6500300c9409207030403046610b41d88012002090a02241c2c0402d11298001181455000a1107400c882c0700727555058550b000303e46044040d01070760700d0b900b0710510208010400729100d8048032080a00090a803028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 380605539 1250 380604289 380604293
    0x2060609060405190b03074b090f09020a0902090405060a270603080301170d0807120c0507080403060204030c270908090d140d0309020307031209030501090f14030c06060616 76
    0x1a03600c1401c4e2140880070329a07014000040d00c0001e1084203408400b002000c00340350b0207a50a1088c1d0350040c0441c440c1d54040618040d09541c1000f0001034019006051040d1141c94403806523000d128918016820000441e425042240364035040358005138582d105510048070581800b44c2c2550500130f0304e0340380c07000400803c0184008600910070000b01d4120441101e00850a01320350b82c016074148141c2c1070400c042950402c540c15464601c0001c00500d603142c054080e40e982c0103400c00644440800318011042204c40c1d4010416a8054065030782d0302aa1a03e07140d07210018a100f0f00c4403566050240c4002c0b164a820540419200f0b8030300f541081e20070f5001c1071000c40e441d041500c2c2c0b00102c0110dc00d0241041c803070040d01b082c0c0d601e000d03c850a11600483d54a4000e448010405240d03019000061031091001c1e001860f40705000b4040351206091810043b07501c00b106448078a000a10101000c00001c00c480410b050b800c0a800306641c0c0100f0480507401241e180e86c4488544004900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 380606789 1250 380605539 380605559
    0x402130507020102090a0519030318121112030315041e05070804030e1c110102190302060103030215090d030c0e1804051005190f1b02060609060405190b0307 69
    0x11003201e0707990005894501030380030443c14500942c41a80690071031042c10040c0c00540601c0801e403602350800d80340420030115014400e00d81c1ea8811410103001c00c440000300710500b41c644000c8482200d00c101a020b1145020780c0b00d1005070341030b242c19420b400198181d8100340c1c21207010401c6064045100d0101030707204006172141220040001603400d8204000c150300280c030380500500c04d88107011000c00586c018542e612200002070002105103c10102e030780c2c420011307d0480080e000600440381c2843c50003075981e01c000e00088000d07000705450801240e403d4403065215501300001840040201c80041d8002c100c0742d20800200728140c0140305030350300c0c0c1100c4c624110014600c0d0016900d0541416800e040ca1486100340b954144401c3c05044001042d01c3d07400e40d486064006444414040c03400010450a10b0302da050b07010032506c3d01d040d541c000c18941e208403800c0d50740d407405903582802c0204644080320b000100003510009242d11742c009034422f42c0d564002270704036011286c41e03003800e01d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 380608039 1250 380606789 380606791
    0xe0d060f0b040e01020412080927160f09061206030209090c0102011103071707120f0c180305030406050d0b0a08010204060f0e03070302010f02101b0e030703020607080304021305 78
    0x2000680c1c031811400741c641454030031042200c1c0000000c508190500c075032101c142d0001080a4901c02002c81c50404a075039a51000811000b4582a00041c0a4192440d00300d00c100321100d00320031f14014440d40045001e12041c41c0c0c0d26005540faa200760307080003020741c0d000320003803100c00510782d50b0780d0003200603140d014010303010300c0c5040f00502414955400090950326060141d0076100814800d2102071600074654450303150048031404015960780310100c0341d0342101c540c0b4075100341c02c0c441599040304103a48041c503450000d50f100c124082c0241e101c507003450710703500c0000c0070303a0320422003003289502ca14041d00740b01013113080c040b840862510000f050051181c00c00e40040c1d600040030071006401c0010410000043d041c01c941c484800c80001e912040c00d88406410301002e000341e071100d903209001040102400c3c080c104004a0b40424016581c5244003405011401d500510012450006400d070101ea6006101d203141c0100d6030341d1005117420250049810065140604101b03100da40102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 380609289 1250 380608039 380608061
    0xf0a05100b01020712061d060a0207030e0303030417180a030501050105400f0c0c02091e0c0a0302190c1b080a0b1f0305070f090204060f0e0d06 63
    0x2414054500316410301290345503155681550700181e000c00205000054100010750032080c0010540034440546200201980b00414103010f60020024500c280c3c0c6d010304041802659103518100198052551300d22090320050501e08070b0401c0e034161840e03658001c02405002440607a00b42002002203002404a81c00841c1c0e541d450748014000c9041c14080400c90300003003002d4920360000301d90513060319100030030904e8141c0304070398951011502540000c401120164010001080a208020105900c16004030700c90030b00d00020a090002c140d90b610348040e002000e880c056102d04004000a43c08030300040c041c940c0074496420b83c0e13602811440ca0300c0159413515a41d010303007450400325200500080d480c20401e040c0090200700300000311b10b050300da404180906140c8480581c0401c0014000220919942c0030b07001004124000c50300f542203480c00701400ca140d40d1900b0440061780603e001e500c0c006440000030621480c8a925034004018000c1c08102d0310440b140c40f4070090394402004c3e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 380610539 1250 380609289 380609293
    0x30a0614060604180b0102070b211503100504020a03020d05151b090108100503011b0e060306012f03030c0405270c090315070f09090b0a090e0f0a05 65
    0x980d500032006525066101074200e406a10301818030a200c0403111101c80d000341d540b42e036030007040d0b00c0b0790080066001a003101200d40c0d0702c40000082000482550990004120b41c8204c045000a600c105020141600040c0900002000c40746507500820000344241e85c8100120000000b5880b900721f081c02d003500920182040100360390004000c100068031802d240d42e1145400b441340342110059540042d424a0002103d0300c070b07000c01c085c2001454010561651802c070824481d51281d81200456500c1c07501d03100710301060001040014007045078128085103c2510701d07509c5511308026070a0690030612503030004a5528000d91940d04212105055140000341c14045403070008440e0042c40009480e00b003c02803031503011860580f01400e07103001c07180c020540341290f80d424060b040c0840c4038100e9400c0f030b601d441a4020038000c480c003440c00100d00c2c2c02d030010446400c01d01075082c41d80c002070680324606191210000040c402c1c6042000f2900650441c0080701d881409011005c0d405100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 380611789 1250 380610539 380610551
    0x120c0409050304061107061d220f0c211d010207050c0a090203040521070b100603140919080903011505040c210f0924050c040303170601020705030a06 66
    0x2401030485c100d4800000c0b56548500420001c103903000da07140c1c0e90304017010f030002045019040880d4142c1c1c0300300220044130f44840c6032107420418030744c4080c800c0250543c0a0080c0ba08802082d10b0640701451240307084804070b1001030071490315403c1121504080b510780303204696020051800c98104d00345c00c903a5a08449400319962034086940d4028241000c421883d40c10250f44882c0e640800000310f090548a20304184c4800e10104143c900d01394101c1e00001d15494000110702c07009486011340e0001c0703840c0600705030b00300240c070344542d11440140e40182202400200c803423060104c071140271500301004200c03103000d9890030300a9207038401464039400309047c10031081100f558810301c021401c200554112421140400110121003001e00031700107461440c83d46a034004c2c148620f00640940380b06403500f804120078041d442c1c500e100c000c2c400c100740d0315082519801840303144800740c00103c05c0c2a140711400c3d01c803149c42e030f0005d0050044403c190f81c1c48012a041c090a1003040d6400c1d80e0b500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 380613039 1250 380611789 380611799
    0x403090504050f070807050f04061101110739080604050114060a0308030c070c1e09060506030408090a030c080102070b06030d08010b030405101e0f05040809120c0409050304 76
    0x2411020203000e049506000718504200204408200141100b040158942c00b10700d04034040e0080350094840b455403103940355201d00010303082c00502481e5020380c0d07183c01710840f00e640c40441038170070465000c6418030400701e02c846200c0a10703424601c03940e01800030b00d4248040465a00d4240c5c001c0c4031810145c0907514190502c0350031a130000d0002603190391080200200c90b80c61659880640754444507254403503c079268a0011801944801440c02600c44404a4480c400190391050b040e9a4084a801e4640340c2c040601075030949e00c5070540140040c4041400103480c240034015042002c2c04607100340f507a941354903081e0204c1d071b8844086039500054613018041c00c440865840301c0150018112111920802417030711605200b20b00b04180e010000c6020098180250f00004c0203505003405040a22040b02100f85010070070181c00c603181c003142c9680103403171f801440d1060b0b03000f6118034101b011010502c0410080940020002e0240401d003003025038451045000d21030088004545540c205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 380614289 1250 380613039 380613047
    0x220f09051603050f071209060c020a231203040201021c050d060e0c0a03020c0a050f0c010f030e06010302061b070e01090c0825091503050f060d0f0209041b0e0403 71
    0x100203040402d0f0420041000d10606040344030342060440c81c04410740300110340c03400014400b082c0028122400e01e41ca46002035400101c0000040c085e101c0003103a40703101c960f18240f071624001300220039003200065200b0b41c4c10000c0511341c8540103005a0782c0a440c0601c800e44942c1c448c48104020960115402c0c040503040d10030000503000c14a84800301d824480c0d6054841e0041080b04020141c0000300040c40400a008000000750b0080488401840d600000c80c0c8a4001305000790000345603007614614244240980000c03503620714081d00c020f901350b409000c83e50303204884505c80c0120000c04500e404004011040040c002c089240c1825414806648141d881106c044410005003405000c500d07254003080d0034540e44410320303000c2c070f0744603c1106a030640c10756440b1289040410601104e40c0c3d4040e040b140c030500420440c51566540c4c4000c000c15a4140e480241181140842c81001400e0080c0300540050203843c01c102020840d01034006440e86542000c1440c40102c4180801c00da04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 380615539 1250 380614289 380614321
    0x1905180d0c0f0204050402060f0705030910030c0f08072109020f030c0312070f1401020c10052205071703130501020109083c04050a08070b220f0905 65
    0xc0d4a0403201d482440e8880e40d180d05101c1c240a8403942c0d981011508556680c400c03980001420b28242d502c60300c090411980300e80098041e00d009130725030150080e80718407038464200d50790210703190300f0070860905c44111003803800100407030180008190440790b000d446452100d0002114040401c0402041c0b050101d0390030300c80601c5010741c2c00b00d81105046d650210700d260058504a14150305c0d042c00d400c04d246030706400c0b10041c0c010740311040103400720322041d0000c03c0c1070750036081110348a055650700081143da0840341d07400038280c00d0002007404250421a000c1b8580180700315102c0c240c0b54600e4030341030703d100c02c40701a01d54400204c904030108039601d24002884240000c10040d106a00c0c1e941551107882880c60800103100c0641c140b480c1034150381c20307503000114641c910b8190488134141c40e9912a010310b5120742d0f06620006620900001c664056a05520381c05080c80b012134010f43c038030016410b1203443e0407554800400d90b0340f00309081c140241562308010801e418290314219007042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 380616789 1250 380615539 380615563
    0x60506151b0715080705180a0603140618010612020705010c050702030d1e050912010f050a1107080a0318170304030909020703090614040b030405010501210b010e190518 74
    0xf29040d00000c50340000d5801d51241c20742c10314030b640d144108100e51284001c001c2260780300305e903508041140da6260740901030000101000503281e8603010100100303188021706c502064010800140310791845080b00f0340c040044600d0250070110303a40d80721425a40c10880040000740b01240302401e6260030011030403c514181400107203a1400c0340981c0d010f968001010060000000700c1d0829600d079812001c040c00300044c001c20500ca028040034001e00300c02d50301ca00c0001d00340f0714801907808811080700d42c0d85034080340083c6482d07444102680509102c0740000d0391f25207441e10001c04150a040201c540301608822140e5928041c034028103641c00303030b802c6451514418000c080029801580800640c0d840c1d040502d1b4002c0e540424440a1140360402c11150902009010070070805403c5207042e280501c008101e07442d0030240000803500c48402c040c10303840510004010808002e01259040f0b03000d4070613581150381504601044da0030942e80340040101090000203412001e0194401c140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 380618039 1250 380616789 380616809
    0xd110a0f0801120f141e0706021b0d020334210213240905060f060412061803020f0c030c10050913060609091503020d060506151b07 58
    0x350400203c0400000400b0000f0079108540c0c000c4010b0050402c0d6954418085108541140f0031094105000400c4142d0012242c0306181303011915074000b0860303130450b40505114440c5e1907a44401c102c070001e00c2050503a0180284440c140060036012a00d03520000024140c0600e003010075503010300f88549600041c1c000380da0402c0600d540c031000044000068040310450b109161b035004050080101900001705800828420307015a08007900c0d0008490f00d03020108069640e241c02d02031011140500e40d98031070710800043c45008004d0305a0000f1500036a4000781e8000901006400008a140c050b405070703000610811680d40100030f0107074080c034103402401000c104000401c258007080d4590b0007e102021030010f000b92150b10351a010002c680030203019465441c0c1c0003910241d03030780c0188100d840c20488101c05074816074080c03000b1a0b90140140d42124041c1d100c000003400003402042e440780100311607401011040000d055055449044440d07401d215040091030b1410301e52014842c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 380619289 1250 380618039 380618041
    0x70e0d0f03080718060207050306011406030420040606050c0d2a0609120c0c12050a17071505060a060201051519090e06011a0c0c010e0103020d110a0f08 67
    0x90642029a085554141002c480e1600ea502050b03401c82070b40e0f0720840d0902414000040d0705c40d40001d0340e9086640582c10342d000b03662101c101c00600c448500700c8075040f0b2010004100021400240c0c1101145140c4603a0032517100040041c040d1401540b101c00001c4d00803d050a25a2052120800d0022941854030061640c000c0da581105a801510300c09410b60003043d406110690304031490b50740e40b0840340d8000019202c0040e1540c1c4801d242a128500041008950100e010700502c10082e003000040507080400e9640b20301100d5051081c032110501409510300040410003001400714201034041600d180010a000320409941e20003801c5a04140c2400755079685a10302c2e1103845416034003941e4641e8500305030428076000c0c2c1e101c88806441d1148040010001041840c140e60182e0020000e80c2c5161108035030502803900501110740080c0e081d01807940c02a00d481d0003800042c10003500b48803c40301d8440403600c1610302410911000101c0041c81c0d03512001e018100580c034240840c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 380620539 1250 380619289 380619293
    0x50403021b0406050a0308070b090f1009060b0303030a060303030e0c0619020c1008090120192024190f0b0d030e0916020c090a090812070e0d 62
    0x254011001c80c10751964140302420281d510703281c01030406014040d00300700b900c079541d00c0d010b041c9a1001000782c84402260000c10b00101300403658240014010004044040224003404010200031200b1a4030035540c0c100c002c3e060700c4c240003842c070420003a91b00042d250301e10309001c1d003a14010103008100381c100391041113590740c54006817655043e0820718017516904080003a481c00b803c03031030036662002c0c6900c0c4044c80aa0701042e002e1103038081d00c00070b01400c810214443d200c4803c50388032000c0180144034451035080030b803204010b00c02541c58004e05c150030131541c001651854090705005504403d802c0f804030030b010742c6414080403c0740c02c02611850001e142100d01c1100b20081c0c6d4043d51103103242e03440c0c580c5c5a00300440c100802054103070b0300542440c0203452100c80c5071101d03004813004000915400c01c0c800c1800c8414440d50064502c2c0e080560030007108810091100000e25501c41d1004003040c840c0f0080c0190fa1108105400c4500340380c400984030320f60011182d13214500742c4041c500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 380621789 1250 380620539 380620543
    0x30712050610110705030111250201120f09080a0203120c0a05160c03060f0c08280c0512040311070b040b1614060f071103180d0827100305040302 64
    0x2d00071070740e241900c050108058000d0412169501845c0d040d82000342c8880d080340302c0002000c0c02002c0c2c0d4200d41b03501c0c440e42021050b41c84002c1001c2e0205510000056500f030b4550800c15494916800c0014042c00707654941d1440c0e04180c1d074013001a032010880b49001e03400d5000360740e000141e14032004d052004c0c0c20401045803213000038040384074461013030303040802000c1c12041014540c03106050040351220030a02000302140364581d4000b400403400f107683e2511710040020b103400010402c0342400302ca10700007000740415003000004c116003082045400e9201416180c06140700703549107040f4590703001c0c1d07640c500405904800c0b16007400704010000410300ca42202e1400c40701c0308171003002d01c201c0e0030407810300d41400540135902e000f00410070000003d80c202da6841034406485800d9410b80c7d01111642e2800395440c03a49400000040700d14191610741240d001c0c45219865051a00480900d40b11034035220a40b8241d409000750401f03681d9140400a80700c41d2085403a04202a14054074025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 380623039 1250 380621789 380621809
    0x2030a0311030c0f0c01090501080403080c1602060d0e0105060105030f040b07030914100c050708070b060312070b190519050a0e01090506100f0608070f0509090c0307120506 76
    0x1801c0c44510100c000c07820704180141e5480070703150820b0b12649a00c9002254840441468450004039064404255076001e4a0000d02860f090b50719900c0306d40d6400b5200c480d550113031f0100000d000c500c10803000103945840080c040c034444c00c0c0010a000c031001c4503403400c0d00c00c042d010b0380c10301c40140704002c00d040311000015881604060550410348942c87c050b00148002c0f48041c2c450141d0f101111080f0f240002d0510000204043c10000600344e80c2044034240520000200720007000c1045201050200500c4c9401c002d006054031000d40c0744998221142e030050700110b4881e02514200035000b0340e000a48000e84600c4070042c411880c00228040300880501c0d00e2a02442d074400110ba807d00d580d074400410b00b101803000708050306160400c195505802c451400396041d80e490045000c00100d031940c0210382890b03c8164203038884104c11307a86a040e0746000d1080203814000c0340c80c0d40d41da252500d4020790303040c42d540f82c0d41d0400c15001054400070f601c100c100355051a0900009841e400481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 380624289 1250 380623039 380623043
    0xe010b060a0c031b0b040b0c040f0b070203010f0e1018020d0209090a0c0803040e100608060105070f020303040605040305160326120a02030105100e012a1703150a0302030a 75
    0xb01002800f843d00740c500c40030300f140d1103503880340c1305111108112624404a0160b8003c2d450f040840d03407162240200d512880c0244204401d40a00410140d80004c010b081310610080000c9520710b00460203104542d40b012001c0c3d0180d210714409050880079109480c7c035010300305d580040c40380b440e0300070070007002069800a0080031a0700000e021035005001c0c0d6a20036a00040c60310405640b21905a5250860f0003124580c3c2088408502c804403102c1031030b811030302c250312030410780e50341d20006640c150010202030719010050600107005039030500081028044545030b0301c3d21a821820444d1500c48403001032040d040e4401c4051002c9800c1d07603040d015100040c1ca001c050074441500b1010036001d110030340c0b911146c11005001c030302c20040e000323941070340c40c15a0846401003841200303e410381200107800d0f001c43c4e110b030501c007154001301c1e103940804081d0845164107503007a5a101e40c44840001f0141250a202005002c0140380a034401c500c5241c013110074040b2681540c00082c1c90380c03540702c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 380625539 1250 380624289 380624297
    0x9060509010e060a0302071a0612150c030c0c2a0f03120d0e06180f0307150504080f07060609050606120a020703090f030809030111030702030d110f07150e010b060a 72
    0x3041e084d0b248a501100d5a096000c0094006180c01103c8086c0084040e2038039403007070248540d0556820b00020b503600c2c6440c025180c2400a07241d40c2c641441562010308840003108040103103031605c58040004403516811960300c108074403921320b0300d07901424004115901c00c010488002e12160340020300584175400b07080e00180c0e2000f41d981c002d03009104060344140c0501610702084a080c81c0200d400c1d014607442000e40726005903080d412a120f100d0404000d081c5101d01c20303401e41f0903001c2d5000c01d910a1060032024034004c9048512800d41c6c0082c0c1c004c80f080b03902d4940501c044420341c00f40d150480001d6507400c0c140403d4103920008140005e0844d4910380e4041840380a0510a0801038001c007111518031442d10707280e00b082c1000f580059440350080d828000030036031648022049920803042d42d8007950811082c5440c80c400343c100c0c1d103020725008070240031013032407160b008008190741071140e59500102070402c0c0d84007040d255580011245a4980741100c0000d07200d01c03046903503004840c54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 380626789 1250 380625539 380625547
    0x2d040e0a11040222080d02120a0f0207091a0f01090b040b0d06090504151503020901030b060a0b0c030d061401020604020d051005070507050f0f12071a040c03020109060509010e06 78
    0x70101d402401810707500200589404181d180c011a103442070702c00da401030400e40d02e8003044100140c1e61940c414241c03401134402086250030300da2088910416410903881a15406503840d243c140a0f22080328100c420f10341401d224038600d1901032100d103a0b006d0203081605040e8030304290004203005a00c80c107405000d002449500210503940084060256000304001e9801c2500381a01e441000b0034840000a10f04280c4040180c444202001200d5004000c0005a130840c1d480d041e5080e0084d03d4942c01603200f0b01c02003504042c4801601c0b00148540c01107444081c20040d080a9076896444501d00b041d00500c0309045903030105000346d0203038043c0c4200c030189109140551070aa0749000e00c0b40d80600d04000d10500b60b5004000b85011401079088442c43c101082d520303902c038036584422007225030259003922906010440940081c500840220418028520364103140c0d0500310b03000c640030644410180110b40c0c20819104c0501031514020742403001940000c2d26000895445074400e0602003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 380628039 1250 380626789 380626823
    0xc09040207020d0b0405060a050f0601050904151401020706030603080414030f030c031e12060906040b04060e010f0e070c02061b0a030e1309200109052d040e0a 70
    0x90101c03100e103079019101000c40111800e05407100c65094500326100c4c05050301240071310a00e8010310b0b0040000f850400120b0b2103440040d80c0340c2e4044003407250083c0c0c442c41100c081c90354070f125050041820f81a088412068140020300b002c00c103812042c20b00d480e00c1020b2003c1381c074040c2902c003565081e00c149071030344545400007450900400d0000245201c0041e4420800c40080050100c0b811021205e41c440c030180744003400b0070300a0098080e9403295440000301b0502c0c103407810641000020f0030000318600c2d010086000d8802c0703504081118003c03003004010303200030307000340000400c004803002c01e030b1303040ca4100208034122103240607103e01004191082580d11020003034640c1b000101c00c40d2079900f1203160241610708201416486101e4141011a8049441c0201ca8042c0d074440c100003881c3c2c048100d0036074043e403201012810000b01c1d200c0442c940d250321141071159440038075250704c0c10b0860b401100c07220060750880ca0240307060403046440100002500d0300a00e034003003182c0c04000320003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 380629289 1250 380628039 380628041
    0x91e0c1a09040b060c030a09061202040608160e0a0e1b090108042901120312050c09060f040504020c1b100503040b04030e0303030a090303060b0405061e0409090c06021606080c0904 79
    0x345034083c1060000140321454260008004001c4403912b031a4440c628142e681030100300d0090f84280700210b03224000080c40c4c0c1c0400c42109003118483c0c2031219008140d000440c1c2901103d800c103c0d02000301809028000155209801b825136407130007014540003101700024030400018200078035040380745800075400d000c0700c401da004450603000f01318140d43c0d450300030749642e801c00403054010581e101c03a0b9801c0b50a19000c1c45105403402000d20349004200f400340b1001c0c0d4024000303641e1a00041c00042042d0b500c900040502d280d02c1d1000b41b20f20301102054038850099085828401e0301031002030f68900b0f4014080e01e87c020b40000055840b80d41d00d040c1a40d012540207407056040c0000020060103200350361019034845d0007650100b00e070f01c0e02c2d40b002d20198401e501030320b540050240078a14003a03244840508800c00607a2401d170a055a5403001415079070641000c0715036400b81d01c2c090280903810801203400c182144003004a4616080c03020300000c40182c40d21510060001d500141030b161 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 380630539 1250 380629289 380629297
    0x207050a1410090b062107170a0b010609051509030d110109050f0f0d09080604060e070e070801140f0f1e130e01051b09060d091e0c1a09040b06 63
    0x1850030322030200c032490038004c454001c0742d00920803038404030407000741000100710b004091010f6000300303080c17810030750f4403035001d941d51602900d18451025018001401c5074101ca00821043d120b04000c58244010003250040721644d051082c401800521103543d0002140d030305440e80340c00d160a26401c90340d0000e0160100100182c00d622407150360122024001503140c803c40c0c9040d09403883c0401c880800c80b030345c040c2c0388610394030b5501210218010800c15032001e011a40d140303003103a843c0390380c46a03003a804013800c83e460400705541500412048031111040350306d81c84101c9645800e007e80070001403210001481d2103004000700014500c055002c000504680c0a0083c5103808000300d08429030040c180038819045d45508003000f0401506022092086101c81d03c0f003c2c5042500e00350a12450790841d491810b1906d46961544010a61002c40700707407200c41c3c035480000000f904e810484030b002010b43c441000a001d108010100030864420785807101c9003181c02061078480e500c00903071207000e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 380631789 1250 380630539 380630563
    0xa020408010903091701024807140d05030a030e030d020f07060b04060302031207060b0607030e0405070e0f040f02090603130c24030c0c080a12050a0207050a14 70
    0x202c1d2081e00001d06400200d00e108a45c424844d009aa100c011800b03030a0740940b03001d10450700d0050421031041141c0014900700d0011003011700091150040003034100d80300d0031050043d0b0703805c1400d051104440d00c0645d012003502c06d42d100400109603a0310b4580d01c0c031483d550042010380c2c804007010300000c1401156030720341080b001507441e100044280d281540c041d80301100d146141403841c41c213508281c00380c40104d9030000d01820141540c580602800c0e804000b0131038140303135194154840ba035200406824034a0181d0340d662034074520351040c8821100043c04820911143c580480040c2e520154000800c14050341c010407451a40c101e103101138090f18810030b910040103c1003114a00500101c07442c642d0041516840781a55011a220702440c10b20140b0744184c0c3c0015140a4103020350040c8000030400c1c82e020045440075200c2031000c1d040301110f400022000404400385241a00a481c4c01c039403408002c43c0762130000e0b0381e6542d0354102040014002e0b1134104c4481c81480341400220f41c510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 380633039 1250 380631789 380631791
    0x609050703020a12051b03042d05011d1011090904030c05190f0209060d0b0103060203180102040503031b150901021207020a020a140a031a07020d0c0b0c030a02040801 73
    0x81040c10024000e50000c0c0140e00006680c60120000c400e43d501919000345850044403041e19602c0e01c4580ca41c3e0b000520130365014040d8560300c1e509020080c1501050b00c2d01d0100741450840310310b005400d640070140280d85d04038044046484010300400c080c42c8407011018002041848140900342c24090124015403100000c0100800d040e000300e41c0c2c0079140e202c0e200ba1203a1502220003580b40c8540306101422049001c052200141401008a030b081000184814a00300c00d559521600c580260400c41e44185c001c01480301c0b11211707041c0346040349050340082d070419050001103950380c010400e4202c40c444058110380054002130200701b00a0710034145615017454202042d6020b98010003d814405010030006801e040c0f010802e03e5000303500500001c3e4040ca4110966402e008615080341d100301700e0100000043c5108a042c0380070b0054250303901c0d00f850582c0d4041d0422110403c89028001002400000a031024440a6000802c0704032a07803617440f194003070310081c041c540000e00c940d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 380634289 1250 380633039 380633041
    0x2072a1401090f0e0105030c0102030307050403030302070218090d1e0c08030a060e0a1e021c0f110a0206010f050109080307080307020709060b07020a06090f050607081909080d020607091503060905 86
    0x90703c0044e558a040e513400b58121400704007100012603480c4011034180c800250103100c144001ba110b0340081032401d0000f88000360f007403050700340000c05d000300b5a2014a59070004040380f0000d07401c030001b5001c2803c140d164411090450202604204580d4001011294000006600c04480341d110b0b0010700075181c41c242032071800c469a08000e0140141814501080700b07401d0280211500032608414101082c071502c04504203420342c090702d20384d03402401c1583c80f0045030410354561400b92071813440300e03401801107524268140c68003003000e42106040210301c1f981400f907a85c00004507404aa4018585a82c07959050012400c0000c19000f0b00e0300341e0300741900007480340206805495518000c9807040006951346a050310045d515118a0f00c1c02d60000004004915180300035201c0f080c040c10b2110318100781c0314544480000340301846000304162440c00e10000c94100030490740a10a0300081490707003001c020281458846100d62400d58800d0016840030600c250040e900821b0300c40c20030700203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 380635539 1250 380634289 380634299
    0x605090a0303050916140102120a21061a03130503040626091207020609150c0f0d020a060b0105090d05060603010e0325031e0302072a1401090f 63
    0x2260a2000305900003802c000201d841c1041c0030a2141210003134100080d0302c240717003c0c2e105000ea510102028194003924117400d00100602c8003c0c00e001c0c41aa40302c41d1904185125410026031030741010150501c1d001c402d2006030103410030004502004000b01e9129039440c0c072410900c44050200401c3c80c000410005030164108666500512a40d0294000c1c08000c90001d2408007041340e4669066003c841c800c00c003c070b00e1000a15120340090b0000d4503000110000c141c000000d8048002000c1c000100d15840070000d0040c030740141c060101400a8032001e10000f95145175008001d4100d5a42c0e6000a90743c0e80038008076007104102815000c2074036a07a00b01661145002c4441c01d010b5400c0c80080742d03a502001c012200700c10381030b42142410002110f40071401e2001c004c0101c1c1480f003100308440080c0c100c4040913403103818654003da82c80708207242076802840e02c80a001d100c2082c50381803100401c2143d41340d0050395607800c0072506050b0100c0040b51031000706c1d4000064003510b0480429 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 380636789 1250 380635539 380635543
    0xb0309031606050f151f12021902010605011706040f022512020d050d0f0209030f070303200309311b02160b0c100e03070b0a2c0109060509 61
    0xc0704a0b881100080d0a541707914598000c0c482401015a1018201200d4426074003281480e000402e403511704001440e9185000c501243e000030240310b00c080c40c524421031741d01c0e42406008007422080c41c3c03903041445c4a2600080f00ac1d800340a551046480792618540030a665066400800704410000040307280e0301c1d080b0200c0c8201180540340095442100407046000084500c030417401a520030b85041100c00b0f0003001000ca89104401180d0200610070603a6000c005644070145130030007038600f040c86c502d4090404c1c04200c070240c4190300c13580502e00051101005079102c8190540e0714082c02c815807a906d0b000d110113003a0441c201c80c081020180c280700181c3c000805c00c3e07642c03003090034101440700c0c0981c4d13210a002e00c4d4142c8568013290501040314240c002e00681c01190003156a607018040e010400d0710040d202c2054294008105002808400740e4516080149000c00f0082c41d15813039481003500d5403403c0120f105041d0620300e5003150009511005186070444000c00940c201140056 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 380638039 1250 380636789 380636791
    0x409060e0f1207030516050715032a0c0201020717010209030615030c12030f03190518060109020a09031208090609190f050a0605010608010f060504050603010b030903160605 76
    0xa58034892101180d001c84030015824008038411030040781090010b0b90111002e500103915000c2d442c52003030705800010020804800900392020014540f00e451110040031152076140c44003c16804600c035040f88541100f1304640701c4110300d4480c00418481c0010703464450743d42d01007107501c0f040b42c042d07400a11040d030142c00b0f40b403021000d40b220f03a01c8444410b444410402c8040e0b9040c2c01503198071006151612440c440d4042c1203042e20305102c542091034013603400840f51080c05000054950390300c821188203580d4840512004440d2584c43c010b950b5640d80c405010702039209500103400c41c00c0a025013461070055500000030b0044041c06a8014402c14058503030b280700344214404101e0350000490064446411003505007096082600c1c3c510f510f0b6440300080d900b078020f0402d0240802c441d802003601a05240d1699445940341c010b00302c0c036540c0ca80d44010700b008024401401941d03503040899044600d90344510340c980d00c0703a51071641548500043c185101254101c00020007089401407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 380639289 1250 380638039 380638061
    0x15120c0409060e1905100b0a020705010912120806130e0304080105070801180203070e1305040b0109020703090b03060f0306072c06071205210115050c070b0c010209040906 75
    0xe2215943c1d4901200da65003098540f100b15441d000c0079089011990b0380201c0e880740600d145140d00d603955009601e51030740b10405a0700140c101d03610900040d40c010700d8942c010498040088103c00080d100c048010481d0b2080408002005000c2002170341c64a11040100000d18001c015565424124a54a0b0b129202d10600d55080c40005403100f0b0080807481c0c101ca589110540200c422030300c04038001c0d400184948140701c01c0c00b0750f20805444114104017040c0c0c140398001003906281c1407013820000140e1000492900410480c0e000991250324a070032607140400c020b4607a114000041c079860050032589070944604400c100c901c59000e07081c0814403809a40c142c0b000c1440800003000c0362542094560080341c1040140700140d0502c5031155440d12030303d405030803c400c041c03401011580d428400f04241101300d00502454050124a6400000342c0c10075a148c08003030745940c1d441c0d07031640c440c40d61808800b0400801300c050a404441c0ea141d0020310401105840389080c8000381390394454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 380640539 1250 380639289 380639291
    0xa09030606120203030711010306120b0f090d05090d0f0605040813060302040302010e1e0907030f0f0605010905090702100612050c090903090f0a0b03090a120212040515120c0409 78
    0x640c0341d52003410b150b00c0394014014614012683c2c841042582000c001c0350b04141d99040005803e070f5104200307040081c411000080203013480e80d00107520140180150109401c684048181c0700d81000455000c0b010994090a2061007410104100000320702c000e0402030920013000100400d41c402406c16640c0400c81c0f04240f612036101320101c3c0142d000013800306020040e124080d00d041c0e2812102c0383c420408081c2d80c4443d00d008200096030a84090021075256036040105400d82d00910051000b4081e081196030700d0400001d12801d40c5104184c0286902c00c00300341054801d110b400419908c03980d003030003030b540d03038003411964500d401300117440c40d0150860908540ca031400c0214060450b100045040411000c108020005e5203c01036034041030303a100004035803a02d0700103548199000c4010b04120702c0141810803007640510856411904070040d03500c00c400010050300e06441c070a0b00c01a020401038041c4092a1040f0344901d100d040c4140100291503031100c0092090302c0003000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 380641789 1250 380640539 380640551
    0xd0c02010f081b310503070902031306020a0c05070e060906060c0615010908070305060a110309150406020421050d0f0903080a020a08030406020306090114330a090306 73
    0x1000702c2c1e5201060b140310f08030034112a64001d045060341c1c09055030405002211064103e4a02005512424090b000380800340c642e074200704904d000c1c00548000d0442c00d10a40c035506e011003204d04002c4842e08000c0581d0781c04600200114070800c00c11944981c080122015075442c1d0381c2490200c481103070a24401c0c81041c0000ea040e003009400d803407801c02200300801541c0c0718104060040003400100a040000c0c441001070100000c10240c0300650051000e80301e42e0500716800d0703058503a01400455180000c00c00e12940d01c41c0080e4042d04071404000221a645561a1070000f0340304039401070f1103003200b0040d07200001c01e404c0ba206070518403400844100d4051000117842c14054142c00c500800c2091104201152040e002080d040c5103e1040e00c00d0b1240d640ea4a0748247c000340c60a1b00d000d6408070820005091080c2e8181c0905007600c0305a00034815003000036610102840860106994101d43c44501100e14440e000c400412460f20354450001e1440140010390a1200785d6825003070403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 380643039 1250 380641789 380641817
    0x81c2601150302090d03030b0303090604090e07080a080d09030302071202061603200705162301031b030b120316150e03030c07050c030601060f08100f120809030d0c0201 74
    0x2c42284c40c03801c00a04a2000e4000b581c505030002c1400283c001e8040c001000180700c01d65410004101400b42070303070001400304a0740e40f06854031403c4e40059403140e100101e24000300301e081090341c1842490210100701ca00303040c03804402a016107a0010032120250790301500ca150045070941c4514800000716407661000f500860a4540411b00c01800007130340c1000149650b100320080a0300e038054821203094442d20701d03a2660b070b8035035544072580460303401c0c801140c4100c50509a5014010910f000c1c0168000a02d41800700982c3d04410070a041c1d4074161410642c407084e40b41c149849403501901d48500303542c000345000f03103107042c022908400482034090348072502c1d00c0f0704d4072482c03445002141151741d01006070820742d100450686072441040d50b0b540c603c2d13504000041c0038040380d685130b02e10900081c0c4042c15900c4044c2000c940701880798001e200c5010702c42100c03801c0392103000d11120080b1640c10022818880c0604c483d07014002c0c080054915900200711105007403003a41e4925128042d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 380644289 1250 380643039 380643041
    0x10030804090501150305161b050f010b0a06170a0203040303180b07091a16020a0f080d080108030c0a1509020603010306090212070b03190e0a03020a110604081c26011503 74
    0x72540388610070300300070810790610310501000c016550b6400e03d2014223803190b1221841c100150386040516034445c0b5003403415042c00c8036294001c140c00c0c200f410844880042ca400c4076000105562440342e4003000003001c0c0742c0310750017180603400803028151081a55041101440c0b4044440b2800319101072800030700f4881d0b002908010106410751941444140c1050500a40740c7d51002d0340e002d1400480883c800285180310401402c586e8020440c9024501002d44104e00591050000c5d400500018030441404038012003a2a0700002d0408204456204240104030440000c2d410220201c000700070031505601841e8028000c454101030f0102640010750f907007040380911140c50304180046800000301c0c81001e01e04a00c4604003081d2140e0121076517140400480064005a03c50f0003180240140c013800041d400d0410754241d0310341420140c0c0a43d50320202d2013485400e00c03007501088400307403140940e10100c0c40451001c520f021103011001052410a0284002910303c0703000301e024450007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 380645539 1250 380644289 380644291
    0x120106021b0a030f0c0e1005090705030403020a26040801051503030304021e0d061a19120807080d110406031103060a090209041e060303020105010b0c1510030804090501150305 77
    0x1c020041d5003000d0031a5074096a02504240c01c0791168040c58003c581d018204001910030101a5120060180350004014282001802d0b040074031504005120100c2c1d4089000c4929a821080288041c1c5821020021000302c0b41a1060480e1000ca00400c80e200190031513802020030145000420701d400d0200350300c1c1d21040d20000e60002c0186060480d060080c00300e084280401404404410055109d0b00151481c070018440c400c03500c45114041171911000500340c0122122660300d1f005d040a40e44a55000040d00c0981132110202c0c00004010014080341d030320018040d000d01c05219400180c00d45504240203460100f801d0102185d40a40300e04244e81c440c031b0f0020b00948100746819410002940038060841c0c02ca62104c0a4018000e00c800d041c04101240c42d900107016899410700030300719101030700300c160441010071484448840004102da10440711260444881d2145806100c21a070103500003041403038080b40004098206522281c122600c41c500d0130840700407014110202e81e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 380646789 1250 380645539 380645593
    0x1080105161218060203010612060b0313080c1e1203070c02130f05190c080609070e031509101406180a1104090608071502070303030506011412010602 66
    0x9807403410403858030402c2010224000d81e000000d05000500c40114030700c074400c0055071140c1d000001009810fa0200380c0c0c0144a00942c4200b1130181040402c0d0700c00d11024002e080c1c00701030740c2d00c06014000b8000446110300c100320110f42103405131800a03821041c1d80500083c250080c9209070b035640c407140e01140e00c50181030752030025002240d030802084c07940b108400d501031540c60541c06001c4d00705200c0e55009054880c50340f5190044a8603e109880506103220108800d10080c0300494680e0484140c0141032410302ca0303500400040824600f51040005a41d10400101400490346006c5075180c94030f00440018480356100c0d1484c1c48016100751034007600000d000e06118842d980c0c51a056070084802c010100d5503a66001003d540c80c2c11581110203656581c00c802c0180c05010402d900040a038407030844c1d22424030383e0003c0c0d1074811910019090544403400a20b4a0388100c040c2c10a5201d40c8803150345410150300150f4002409004010251060a04d20000d41c00d0f07404103014800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 380648039 1250 380646789 380646811
    0x170406080606030c073201060509060603040809092d0c220915051008010302011b05010902060f07030305060118031b03050a0308090115030c0e071e0c050601080105 72
    0x1071101c000340085580010000d1315248024801100010f11050781000c0d00e0051003503241c07003641480440c0c048000c000e60b0501240c2c0c034190007002180c071122025548444125081d50f100ea540303007044142c51007410f403402d500440d5101008480b000d10600d45c0c071561003071405204c0f0f1880d440c042c003640300d4051703031080d80401c024003500e2200d100c10000340c4200c02200308100d03103440c0d0311151300702515540b0b07044080044c074203401403286080c80e107090300341c100036498600703c0c0f9451078001805041c0e0710402c0005403440c3c2a0b03100c2c1809425004240c0e01a4003030001d60b078408420226407002d4101d5042100004d0511020980039807045d040144000741d0400080300d103a207540e540d41c00040c41c0c480d02100c0040d4030301000000c10400e00078900d60078000e41710545245000c004507400c48254080d0900c141510107014408240280c5034401580d0065030700310100d4640303640071780301d080030305102480c002d4204115401807544201602a01d41c4964108c2d5060798aa68a0074240c4d0000c0300c890303c8007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 380649289 1250 380648039 380648041
    0x270f130b0f0907090c0f03050a06211407090203150d030210090201020a0c1e080d090306020a03021e09040b031b010c0206040320210d1404120506010317040608 70
    0x40d01e000d60045800440c101d044516036641c480002003640c0d1800c1009000c2002c990144094541500070540d20044601c010000d2504000e01400c6107011003e21902e002d40c545100420849481c0d0311503030000440301150202c03a5198000c101a40c0100c40317140030000c9040007100d450500044000080d94181c0142105420641c0f902c0300520702d488042c0e04610072108180041407aa000e010050202041c8596006203c0c064111680c4401d40c8009510391101d01e0384802c5581c4000400c041da9400300b80503a5680103040b040300640607a0034130621485800200740400c0004100821842400b9102840150704804c105512040d600c8111f0101100290b09214158403620502014a100400481c2043d440b82c076210540b8030000f03860110000129210b900d24580b02d11801c140130300d100d0b85440840800450141c80b2904c82d0105403d0207202d21b10f09605c1301e461400d881c0545411034000b00a035400d42041a03a5090a220030345420020300d0210303441040d030000321000d40d94152950311003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 380650539 1250 380649289 380649301
    0x606180b0927010b090c09030601121212060509100303030e010603020913050102040b0c010c030612081b01021918060801050307150e0402070f050c060408120306270f130b 75
    0x40c400b4055980e2145540e40d031881c0d452075440d134018500404242d9a0241c54010301c00902d40780120682008011601168080d0006a480203030804204070602e40706c034030792030b0303482207103000e00030941049900010100030041a202c0c07207180c4808603030090b40c050210104030403809080300c9442c003010b90031a949a0028400300d80c2d0a62101c07046108400040c949580d51040030780a8000259800199440302c0d0851100c640c54020f40000d4180903144000d41c0036203a540710402c0c403510310301c9035003e40c07214001c0a03000c20070741c155070030342d561141802070751170200c28010504609450103120048a4100100ea01c511691792141681e502130010600142011000c02c03880c804400d0b000e0402c098007810301340320340700ca0010f00070003403054101c1c42c0301c4810341c90040e0810307200b400601e00807801440108200100001d400801d0711400350b040ea87c0f43c50700408540500300001d1403000600b81882d0190aa01a50b07081d917105090000000c80c42e45c071000c0026036081d42444d4090078000c3d0840100798 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 380651789 1250 380650539 380650591
    0x1406010c08090d0614010305070b09010804060506041e02071509030c021507150204050906090f161103191202070f120e04060b0306040e010b0d11010c0606180b09 71
    0x150110000d014000d125155a10b00098078205d1182c0c1680b000300c0b500410401a040040030060140b00d00310320b050a040c40c00080000c00c00034000360070340f912280850700c65150399000050400122120f80c8041084c6c0384c0600103944160400c440981881c80700e01000d520911500140c683d2540d0f6401c0051201c0e000c1001c6072000e2182031000312400c005403c0054413840c0d541d031900218103409601e0380d1074041002100340008021070b0041090030708000035281d0b468a4241c3c445840048075101c103090403400c40d074010710142d50381e07600d04c00000c487da481d0040c802220010241a43c5280fa100e13013000c9540d0590107980b40041c44c1d80a16441900001c40c028101080b10000d8540408180107000c00102903071314076400350200c0b003800004d02429090a01801c0604501c1d10b00030b1020091507808507002060800c03010306850100c000000c101e83c0704002c842d00e0550040b2090180a466003c0000d03165079150404200503d40703240c2ca0858100080c0301403184584d0480010a1890a0b815407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 380653039 1250 380651789 380651797
    0x150503070203040f0303170903030403140a0c05121206030a05030a0f0e0316030203070617040204050606160501060509010f15030c050f0f090906062505030403120806041406010c08 79
    0x2030150b000c1030001044da10f00c1d03044031500950180d503034507140040b04404890b09490150420f9091b40013081040046500040c0d410151007004041035aa15082d02c000c40c0d1081608400030114041c018140c1d07203065050018008d25242d500307580005440341403c15503100030f0040004d000f0f800503c140300c4175a000302c41000d2114a281070004c1040e0a00b000281045145150030161004044042c8250304080040b0030150100d4100340d02c0d180300f41c29078102e00420040c00203200d0313a20303240090f07960f0300c1e41810b07541c61004007a000600ca180903c3d0150180c20f040c022180111044000091005054200d000442d0351100c01409081d403411012030280400131107400c280701c8100507249407a514103006168200c0c01c41d8142e9180c490799801c00c400d202024150f18841c0500b032010040d081e00c49101000f800150859851500e0090307d0007505500480e07102808805082d02440002c03a000400c1e5489048115001c200c9854001e0341204420f00c00d46400d070000b0542a622000074000790024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 380654289 1250 380653039 380653051
    0x309010c0207230d0f050d030f060810020c0304120c080d0e06160309050a08010b0a0b090901061d030d030e0c0a0f05010e040f11041509081f0e010c0201021305010306150503 76
    0x110500130142c5520411800003001100c1c0d65214004000e022030b81841094482c4a01c00010b0000d10702c0d090f000713075a51410411205146600080c65012050100b04840003868180400660a80c160030141400d228502c0303241300c1340c0124040720901500c100c0d10480320740ca000b0040d5003003508002800342d109004900c120240724103d007010840d590780704444002407500c1400030814a4607902407145c2c11100354802600000f080c0718803446031341c1d0b52454505580f110f1904140c1004403030b00781c04a161101e24110f8140c010320803000c000e5549a00010143c0c0300400441c0c0103500344009001e0a03d01d6031180c0d4840301d100c03840501c5298461a50040025001800841d050b1a6080030b00304075070038000350b140c0b81500010204030402a1020324081c08040c1d00b0f01d044641e01d0542c0103525128003000c1c07030048680340035151a816040d0b038450341e00040500001c105481400e00083d000758032520000007841c954000003d400c5d0300c40d0080784161220244500b041d4106207105585541000e404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 380655539 1250 380654289 380654299
    0x203030c060412021204030f0311030712090e060d0233160b1b090d020a0305030a020c0a05040e0307020d0201050403140303190203150f13020d020309010c020723 71
    0x1022401010030000745000700d02440c1c80040030008084040d10780014444910249a420300c41040440c01c42c040c031600c0d9680604080140e00040c1c1442c070300350301c2400001420011001111028180d20069070016280c401d100c002c0c4da615a1800c01218400105c0025030005480030040c070b140c0254401112f2081d0074030004064012500c1070b8206035044225010f03240503442c6070220921410200550300582ca002d807045950058410300000303880380443e880c0c010080c1020a004540310060814002d41e00401503070342714100d05c40000d440303103449030f0105d01c600c0c4a803001047c00d180c280708941070181d01c48001d40c40c00d00315074244104040f4420041e03041c40070911000003c52080001d0100c481c440c90043d664a14021114182d80c00503101c00041c06441442003006240003100c90603007800f41214040c03404800d000001c2c8a6214421105256a00124030030800c1800d580295000702c00300c00003072203a03c00b00b18080740e0702c001038800c542c0301d0794030782107030103480d84480030820255074010308 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 380656789 1250 380655539 380655547
    0x9030206160c2105010506121c02070e01170f030a0f0c0215030c0a02100209100806040609022205061206060c0a02041b02010b090412031e0f02040305060f01030305030112020303 78
    0xca401d002030b0683c4010b00954210100e20420484207204040c0d10840c201c0380d840c401c03001100405d81c4c8596400302c003c00b0440c0d400121003418020070020006106401c0c40c01c8456841d072086e105d02d202c60034071802c1144030307040255a44010101c1660b00c003140b1a0360320005540d10007011141c0300003071341051307030006c0c80c03004000300002d04080114441c18085d034449549004141f0000c0c0740c42007203a040e0078200d106112152032945c40000c1c0e5500c9500e40d20b010140ba0b116070b00068007e00071a404174000d41d200050895401c999102907803c00404101e480c805a81d503078041c00f0691250300c00881511b00f44400003040b40c6000c4001d4950364810404450341031241e0b501140c103c03040c03000c000d980c8040044808500ca94240030b90301551901f5150902da03401c103a903c1010504c00d0f01d89040504d910f481865004400da41034541900007841010710000540c440d1103002580140025030b03250280f040014100c6182d007460b14100c0754540d03202c62441c1c0c030748480b0204001c4200004c0740e042c00200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 380658039 1250 380656789 380656799
    0xe1501111504030206010e04150506010e03010c1d090c030705070f05010504030207210506160c0501181b060c020f010c06150806130b040204050405280507050109030206160c 76
    0x411a528078403005010710460401d070a01910b0102d0582c0b104400f0100003040000248071440d02c07082550303036500d0102c1d060300c2d6003005950b9644140381070350f055880d0808410440b58041d610180d94070524891910070380d68841889500e0208480300c00d008a010400304184520400081c80b0b881d00407150889600456500c0750309481c4191401c3d40180d104090034440d01610340320090852080004668070142c00f681d079103480d41401400001c008050300e2040c400c0a0050082b41d03040c5600500800003150b0a03020648d280e02030301f005450710748002c0d0b6020900001515510240d5205440b03600480000d6402c008001d2070140099040081100032800003035124000c099196407182082c000c500e09000e2207a1804000a0030f503009540340301990f601088440700311070b03000f6805440102d229038540c00c0c858030380440319880304858403005001e0440d60006500310700c545803088080d600c1032369507600110303035110a500010750702c09001c00504035000c0b4820b10010b44148940103540a07a0f07622 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 380659289 1250 380658039 380658043
    0xf0206040b0a080c07113f0114041a0903041d0910060b0d0b0607140f2526060a09060609090c0302060a140d06090509070e150111 57
    0x6580481c206000c00320300301c4000c5030802100ca07402032210081300e0401c1140e44400361641003440c2c115004561000c46086210030648a040385c040d41261a810f2401182c1c03460b1b000c6200301707101c0d00015403034603480314040e14445130315900554014545001810000132018804132019050344402d2001304000248110b2003d2a00c4400011515059a602d005503204d07041c280c22050703001c2e010b071800509102440c445815140c2e0301500040016101c8000e90110b07100388036044014001f09403911804003804000030380b04030728120300000d03200360004c84510320580d000100300120401001540a0094915645210554298582224407a200c0714005a410b000c0c00f5035a10818a84400440c07090054074001c103401040c08980030400c0301c0568681d120045014000284940030020303581040d01d1250990840480421a115581d030010210302001803082d480703403542c19401d020020340503213400714400048070140140030b0119a51602e604c09034199042449046c0100c099000030b40c00c80c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 380660539 1250 380659289 380659297
    0x5042111121f06080606090405030d02070c0803071211070605040614210105030f031306030b180a1506081605131e0e180a080304080d02070f15150509040f0206 70
    0x2280000304203044c580c3c4141032000c0101114005e407041c1c8240000243d0010403640065801d000050b220601842d02e0019010b03241c1c0441100c1c4008660785060055100e20521040615180d8054510701101a1602e4480f01e01c224404564140410065a405a2000c81e44120b403c0b0f081e510701b5610011004242d980b601c0342c07a05108041c0b00600081c10100003488040f031160006509201d005021b80c403091882d80510810151107402c0e00580e03403030704801008468203c590001d16803800d04c002d44c0043c9040100d010066440c440000f0303d6a004070404c0313020721f90780e0b800c24141c0c14040405a034594058100d6440c00d00000100060a54058418201e84110700d1080741910385444c0d50f003111168040c055803403c280b02100211490300c00258940100c0e408903080c2c2e180e41c0c0301d0170b0024090103000c5100425500019525080040c0160b5103031525119103008407030948010350b0300c4211201c0440c0b000e808501c0032010701c41450302c96041e9520910802180c10b2154007a4080394450300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 380661789 1250 380660539 380660593
    0x121005041718030f010605152d030402010207060504060c0f1502040602100f0509100c120914070f050d0b09010f2f030601050a030c02100204060504211112 68
    0xc0e040444030083c0f8062191040d102a040024894207081100080303e00c49400c0c2c2ca02042400092620100c0514088120000011026140d8040d160074480011a842103404034014000c0042c04104540201c080d03400b99603040d555007181e00903580e41e568101803034100903500314043c2a0503c0e4240f040d80003c1c03002d0700c1d956000d010700c0b46009041c0019a1500a000b251403070030a0200f0005410006244480c1480d404010401c42a0f02c0d00569039400034003c900c881a00b003200910078032240010011a0303024560885505955503880c1d00448400c40c050340354071026148141000c03070b0308a080346820004807000010703011245002c410449805030955500712003642c10136a40c0b41c0f0342c2c071055200200c1a1042d02d01d10718294000903c81e101c2e031188030b000d25550310762a84415100300b0140072407411041c3e0441d038487d185c000103030103500144190007000b00ea1031040d401c0c00c054034042c0c04c0d200c3d0340280c600d403111103000100440d8000a024941d100c0c840d0f070400c0c418a20f500314a04046030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 380663039 1250 380661789 380661817
    0x251103160302010e041103040201050f040f0605031f0b0d11210108120c0c06160f08030a0627240e04020907080708011707050a0305031201051210050417 67
    0x1d103903200262290312444c0741c043c800c40c40c128000c225600c0d2017080f00e6000344d0901e017081c0d90742c10054080c070082c05a0b030070000da04002441c0128031250070a0040d401605200540a018519801e043e500c0743d040e80118089140184582c180e081c003290064041c0b40240e003101400c2c980d16a40c1c03c0a07002000e000b22416a00c204010490500f050008c6105140700c09192454480102500c559811070403002c640182e00c0040c3c461141e901110050340c0e500d9000c035000401e142281440c00d60703071b002a2054070305c00d8034150000030003d0914807405008032403214441ea01c11000d0101200410000c800d140b0602d0b047c280d96040100026010005059011450522820580140305420400501d4281030041d00ad06020f8101d402082e40e034115441c4d10060b078000b01030300441a062001035031019070031040380c8002004000d004005000c03640700c0303070202240683e6200c080002c030b101c05152804003034021600100c0c0d0b6401503044150300030b0095030407460300341980b000c0c40c015a0144540038510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 380664289 1250 380663039 380663083
    0x10914061209030a03060f080601050d141c0909090203070506030709080f0d02120906120411030d110d0804080a1202040302150c070f050f040917040f060e0303251103 73
    0x4c9605481808094a0b08070030100c18503061444280c2c0d05c05042c0035951044003072000050821a070f8420301c2c2c410028900130383c1d41d0440445124901a80f1281d10324020a0511401041c5000240704132101550024010100249010280301d040e52001d0145010003014240105403c481000070070481da0701c8600802c0c400d44003440003418081e014000300d810200400c01d501d000ea0310340040e01c0c0f1190302140304410315110b07894245284500c00c81c400d07806019050300014901c1d00045401565072121040d644407400c8020215041d031400c84004000c1d241c14856441e144c0d12840b00d80a01080e40540103282c552240c000400201c455001240f80b410001071150703030302c1000e102c1c030b00041070b1710480c038080700781884006140c04910345140c5002d299107502e028180301c0d4015099084410903034507559580e8603000c001d0490344040c00b0720008200c2c0074200031228103000044a540014060500c03d2403d25645075540d4002402c5040d1401c10304050f9020f003940d01844035152510421000d0521 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 380665539 1250 380664289 380664307
    0x110f150a0f14091b0105090f0406030c1806092d0605060712030f05040201020c0d060f061202030d020303040c17150106050a0905030309090a020f0d0e01090212030901091406120903 79
    0x90180d01c1c00c14000220409540e244645c1d0300902034800211048590b240e800c60070740045801006203504c05400417011001c0040c15464103180651085501d00007800301644031102c11083d54030b030107003403040301c1c080303005201d0302200f8544044441011480003052455542000403a15041000103884600d0400d07807210580f6050700c940e034010910a80188164501354002039100c0f00611020f5004de140a03d07007000f00001d9910603803d460300d5450811846403541014002c0c010707100b03001c900a09c0b685102c0c01401f80000180d80c0700c0c2d680f01882d44201c0c0e0a1802100e942100403c05200601c00c41d15841181c48604480c180a0582a62201e031690328840f8003c00c41c80642d80400e0080d0010415052141c40b400a8240d00060a80d400740c0e440007001901046841686e00c000361441c0381c0500c2d1a0040c2042d048100c14030300845103c4002d00c0300701459600c070f01c5844565408200007400400c940d501030302c108844103400518590416a1402c0304400101040710082a680c00004480003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 380666789 1250 380665539 380665543
    0xf01060b091f0e010f200f06010e01030b0103080708040b07110f06070305340606050f0103111611040c0201090b16020601170319020a0201110f150a0f1409 68
    0x4000ca0b0750310a40642902c100c40007800744220a0009410402c2c2d103140400a10700030030f00b0000300d601c0028031050411012001e180c0b15001800c110032a40501400080c10304070410110b0706a075004401074a0991a540d98a851a03200c0700c002c43e1008000d020001d80d4090f07020281041ca809030f01c025101980303890400501848040880b442100d05000c1c1c000426486825528071641800207002100440d1120200000150901c54118220320402d942048143d81002c82201e10985855249120080044d410b8408203641615412800e03c4000000300018071096081da005507c0c0d1020a442d03040031805840040710700c00c0150391030316220f808120526612560010350102456a0b598116034000d4603800180b03e40806803009490068460130f042c03041f2880034205001c008540b501c441e5029403034038109101a0702044034005d103004803150100e8610780c94006034001e0805403010001c46001698040c012005403962400c044e040a0326510801c0074621051403411500c2c600150f13000c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 380668039 1250 380666789 380666809
    0x60b04031109010503120a0c0507030b07020d03050708060d02090403090911180402070210300c030b01021524090106030605120a03090b03040602120f060111031306030504050f01060b09 81
    0x260180c0e00102d81540810155000c1d07d0250040340780000005004c0e0624a15181c0c0940014041d1842032062004564000801e26800c540750303103050015a80d68101a211b03428200c489a0b084104554144014904102084d60161090411921281d20f43c0f86840c00c480241002d00c10f4000001500f00751030004010844169808440a40c42c06149501045100900760340c41c0c0d0504c0381400182c0c88407182c084201c0000c1e090180305d0f000b6802009481c4018064070244500031919080810b0040d52000c20000f00e800340195103401b10b902d030740403201d4010b0801030040030081c0d418484101260754682e901e41c02010195804104513003440104140f180c160904620305500c40c071b80340030019403c4001c4504072200b90851130349035555402c01c1c84c064454004250304d841c0c80c3e80d0412014109100c40d060083c202070b69000c0d1a01c447d0781089940f8410402943c0038414580d2040107480d20a422980d8020700c180c09845d0201c000f44040c41c01c1d12800d07080a40c0700302d00481d2a1145081c0302c0c21807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 380669289 1250 380668039 380668049
    0xb090102160b2a121908090a080307031107110a1e0e25031d1f09020f0607200405061f030608150105041d0619060b0403110901 56
    0x90041c0601d000c035002128469420290a0849280d01018088050a20001c22009100d0030b8507550015a0b200740040da00007801000750781134502810743c009115106451080c0d45020040c260240b068903410005e4100030309a80030540c41d25003880784002c00d4006440000d102e000301158040c42c1001304808030300150031041a010280e10f0006c148182d00c0c801800315200080600c0c01c645490483c42000b420a52129a180c020040c2564900354581d00c8244103003c001036800e400301616903511340f2610500304001101004000b858180300d91944400040c0f4801008549e05200901c0812000d4200020650310380040c64084c2040c0760805030b2104036400c0c00c540800180c6070001c005000020303040742d10b0081004099110758801c2c040c0d40803202610400d001c0341c4900105010a0042110074099030f802982003444c0055900d8116070741001140804001d800955620f6210031a81c084844c070b0050f000781c8480c0d0006100310104000e102a42c05080352441d80d4007048103010010344181c2c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 380670539 1250 380669289 380669323
    0xc0e01080f0d080402130e0f0105072c060c0a030207060e03010204050901060309030e1c0311420f010302040c110d0302070204060308030a0213060309030207030303020a02030c070b090102 82
    0x3650708600c081144003540d091410110f80c25103450000c180c14503003a00303496405a11b04203d071054004000f41e05494000c40705d009014a070380d503140440e950301c41c200081c0c0c2c0d202041120001008184403106500702405400c10b41000e00700c00c020b62070505081010740c05a005043c007800910f500c80c2d00110050005e40080d85840c2c584008039208820520901e0101561901d858081510400c4544042c0c078000f440044481512405180c1d403100401e0102c0120300b48045403100c40d5000f1607004003848588000b40704640f05c0d141c2078040d500322546101c4109840062012280c883c1c540c0032030048101401d2603440e98118418403085444180d00b04050002e2410b2144142e440040c045015240c00d14001d82c60b030186e44007141c0544560340004010700000302c00c100b02c2e030a181d80a02503400880c11450581ca580341e070250221614448003a0068001c04030030700c0441d00a400a14a4001c0d503c126480d10507800752480c1070031030035004036107000000a20208590381c10410005401c01b0851 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 380671789 1250 380670539 380670553
    0x50708090d0c0b04111207030c0f0e0103020a12140d0f0801080a1101030c050d090803040b100e2212020f061e0103170909010e0f011401050306010e0a050d0c0e0108 72
    0x358048800c0b80244020101030640c01c00c10026206c00002e0700304810340500b141c0c2d10544916003051050041c5c02007184411794007100040540f100c1030300c10b040b6a0040c150740e021508103ea08444542640d1040d00d41b800903400c11105100c04001d04e0103401c0b410750390b030280044031540003441d40e001a84506000c0e44126110008210014500c603200000ad0030009080e607a5290142c40c030307000e2070380464034103858240200240107041c402036216502c14800c00e0015521b005e4000c0340c10605005d1246a001c8800001d00386001c618008003032800d4960b4030300031114465403511010028020101c1c01078000c1c166041d01d4010400c01140c0005800ea9480030b5114580100301c0e141c2c90500c00608030a03400c00c5d0b601c0382c840188046a425a20161442566603145c551a204000b0240e0743d492043c2c0d140b5000080800405240e1480d5031030580d2118a55100e120044500080c0d40450030350000c844140080c5a40d0344110301e481103803041400903031042c6014106216900c05030720110260300091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 380673039 1250 380671789 380671793
    0x10501030b1e0a0b0d020c0c0103060b0d090c050909010b030114090a0305090612010b0a090902030c0306061c06090c0201140618150d150b18012106050708090d0c 71
    0x214018114000b07841d003030702051052001424102e03c551004a101000140c0e488406801e0b400500d80a003141c000c840e0b2105840004404a540034428500a014180705000c3e140e0320580100b044070380904400ea1140340c031000000c115500c143c84848203a9568141303c80d05050a000c0d540c0d4840b10b22200725160710380b4020042c1c03104000b0343c0c001d007007240005079420309030340760400c0e9001c40385c0c030400c0d018017980c403000760344c209a000070624401b0a450b20b00020b0042802c0c000c0340c0c8074a01c42d81600e03040d038554400303029150300710310283c0129104014094241c00b07098418000100b801d0340e0301013074100c40d540e40642180c01010520841641080810003607403a4101b000c07c5400c2c03d40d54030850341c0d40360b4400d2110010040984d0354845450310b0b030300c0180308888114580d000000002008848001001c0081d0300542c00b0072003111448420040040001210000c1011164954502820341003541d8540031031f14100c5200303001c10301d84014465040c01c10414140081101c4c14410664503080d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 380674289 1250 380673039 380673049
    0x5060909030901050a0203072012010203150603090f0a0b07030b03190305160b070c02041b0903030e01140d020c070e0408070b04020a24030b010e060d020928060305010501030b 77
    0x542c489030305101c4002120002d00d80700b0811103201581000030b00900384040024030380d0004d03122800c84d101e004004a10801c0c2541842140e0042446a03010019030005038240a0550002448000355000e4141114400801800300c1c0c0109071061101d8565481d003600c019040301c000a10a0b80607500c15070390705250702c55941e501c0c0b181c1900b5042254035014600551504c0381ea10b00c500030402c14441043c05403450b0009032920500340700f04c90501c0700700d08a8024411040d10040003000051a0741c404001090242d10030144280061520400e0342841440014840e030000480c400126070024290724144020712100d0701500701341d460005a81000d880b00f81d184e002d8540041d000944c140c0c04078003190703200712400000b0b100110741030740c4040503401c1804164101d20b0503c4046401e25203580c156600c1348046a010400040a060031321110b4841c08000b50002e0510940044000034816484804400160300010f10003003500c06060070450005c0a0b51010780c132203070500d420091000815621 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 380675539 1250 380674289 380674297
    0x4081b1e01020f030615090607080408010c0503130b04031112070c05010903020d062307021b04050622060801020c280b04060f0917090a0e010e040b25090305010506090903 75
    0x4111025511b903a01041c0c5103401c2e118800300e6a50082e800101c450403c21800702400490740940020030112091403829501d0384000c039134420480405000d00000124004082c503001380c001d103000da1055240403200d034902060200c400d001714202050400070440001030041c0034000a01e042e5a40c03500c0c642c00b080040c0d0780e80d08000e10b010b448103044030800c1c04a221507810058184800321071414410000307520b6040c2400010310f003005031032403101241014044c4c1d900585014040d85e580051200c1c910040740c28400d00041035a81711200000d0f2141c0034000350007040d0005014045042040c0c205142c43da0920061001001460214030007040d610600d06078865000000451000d00454245000f4041c1500090000f010480815010900030001d440394401c00d881c904151703622000158240c080034410510040071010008000581000c8802d8005000058104c1c0900700e55034560554080c1d004070600090b402c6404000b03100090080c2d80d0042d0040e9502c400c2418600d200304e403a445 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 380676789 1250 380675539 380675551
    0x2010f0e0a091d16360b19050102120c0f0f0c011106190c0c15060812190c032001021323120a061d010b1e040504081b1e01020f03 57
    0x800c000300d8060003400601c1045840442e4030455032045032034003a034001b0908050407a014a0794040c00b00c001c030040f139100c0300980320146c008140300740000910501580c0310704014202ca00400c01203541401c010451104044420300150044000386400104400030107000e0f128554404800d02c211240420469104190354800101c2d107100d03800015200541c407044010882070340321780701421a001a92002d025900da20090380e80e02030000c021038030240511060004134481c0d1011403056540200b0ba4107407864031034108481c4403036010b0000701030010354104595150350002003c0341c0d12107805688901803c10600710040222010315802901d00c980084140504c030120140c840c81d050030010241d11942c4090140489000000801d402c4520341c42030521a600301b100811b060b00e4040298806501200c042c45040c050040c1080003600307010303009990f8803200300100440408290818032440c0c080100070940d034403203001d2144607402d1525281090ba4414060320448410398403c40740c05c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 380678039 1250 380676789 380676809
    0xc05160f03050c0607030510170c0d02120a0b07091a07060509012c0111030f04080901050d0c0e01112109060c03040810050a02070f02010f0e0a091d16 66
    0x2031014a400d0316107100e0003070751000510924041002a980c0740d0440c2e8070904600480034006556164410189961009407030740301d40150006a00300d0800100428841d40018111400d14000e11400740c00c00354440c0061714106048000c20240c1d40c0c0003c40400140b03d40ba49014101201840301c241d82d018540c0e0040c00346459001103040000c09400c01380c200c051040c050410426106018064648071b82e811003100e500344230407059422000070030399200305495504c6500b141d0f520303038071500643d2004039802c2c18448103012034005030a091041e50301256017034803007061142c880800580b6801c074a6078006060341c00766803904c030104c42038440e40903541008980e55440d4200c92001405a002c0c814040e00d992102040000702c4520016100000c0140d90314200100d0f25100d0a40c400d13842a000d0190060441070b46910044d485104002d000c000e241c0f40000940200d07a00203141c04405e58400356000703032500c04000c000c11440002003104c0390108003d008428007541d00c24107070280352040203040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 380679289 1250 380678039 380678063
    0x60507110a0f0315090b0c0a1d030309061608030705030a050f01080316020301090b10170a0503070201050c010b0a081f1a0f120d1205061210051003080c0d030c0516 72
    0x103130706500814402035001074131603c5460b0a044011075500f0601c201000100c410050400c42d020130600c40655241c054065441d189000044c403c031903100400515604607242038003004140084055401a415555620340d02c0c14801001070580c1c1000c0c04452018031004010010700900200b25030b1806480d800300280500d00b4000a03004141202010b00380030504403c10071100102c400100503200c4241d01000410840480d0603a21405032030018101d40c41040f05102560080b8040c0c90403c8404002082000e54400407035001c40d12644404019406400d181401401928910121130780021041100c0c440841ca11481e1701c9034080e010780210150344e06d01501c2e840306e88805060441c9801241c91040724100000c2c562144c00e15407075250b40c038180100d201d070b1400d0190140031404d01c00c020580f03145210f280000600c4042c9c8450306040b19000c000002900c41c3d0090900c0070b40c000e020b000c9800f680d000c0582a203a122250000304a4108030802140350105404050160802103081c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 380680539 1250 380679289 380679323
    0x2031317040f12060509060c04030b0415020a030e0105010b09090604020c0712080403050724110f01060b0d050105010903080313030212030a050610050c070e150a060507110a0f03 78
    0x140c4600d030408007007203081e00030100c0d41d00c0070300c0301c3c94002c188110400c0007950703200140e0980b03079007040d9141070079031300200400c00c089100302d0039454015000752190070034014100118400c0340d220a418101190326203280a48920003842080c0c014541d601c0100e190840420009151b8500100300340e01c1103034003080400c49d5100820210010784400f0300a0591b40b552810082515003051004031424030501d4008644030420b170720a00702d8162405090745ca18003120105036054520f5200e0340c0528031407144007480d0a078090280340001c00440c1021a038519013244810140c800503080181400310f454000c00014104004480d40459280e170f800400d2201032404070306080315102c2c010740c400000700c2132001c21703d220b520150050070101c40c0d549101000f0f8505603840e02880c0f0040e03089811050040109002e40840203030b00c54400303a001007207a440352002034940e55903078203c00c000401c0400c85808001d032b800107039400750304c0c221844000c4034540300d0703070362000c0c042c40c04010640702180c40c030074907 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 380681789 1250 380680539 380680583
    0x4090f090204060f03051c0507080c010908031306110906040b030703091a01090507020c031903050d0f0b150909040303021b0714011d0a060f0507050f1b04020313 71
    0x2034254010000e01800d550741101c060800c805000c01d951a0143c0b81e4000d02941943e46020410100e545403241040510340358144546c001d4078520000e5500c0d4420a00091034610043d44601c2c0441030145d40e02c3c02509003a07080b60148000c40c03410f1403003000b140f000381d0b540000380c8040f01e01d001c4c0d51654035601c02004a01510074100c00030000074401d20004448030010030414142d840740d070b50400035640c3d07242c000c9940d106456003881c2c168108188141c44405070101045540d400f0f400c0a80c03400055100e018115101c0788000c40d00f0590701c1c20385445914185caa6005842c242d0003a082c1840340300c00004d2440d05004d0700c000c007450350001d0b10100a0011285005070008158140c03010603036290070710302e1100039140b20180051001c0c01d00740c145035040c0b403640740d541401428003416141800c0303080d1011650303400e0410500005000000019100700017519104102d800900084500d601c1000201c0552407e00c500c501e005104010614500040c8019003a4121030741c2150504141403242e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 380683039 1250 380681789 380681801
    0x50d0302030a0c1403420108060105070f12051e13080718020a0905100e0a0609030503030c03040201050c250f031110180801090b0f040c06030b0f040c122004090f 71
    0x18001b4907041041145082d01410211142042038882c1c020603031300c1c2d0004640c0da12480c03200174414040802020003080c654070000d801d2401a0070701501d088080f0084c070900b910812406000b01d100002c4480301150414100001818880000c054142c00c01c8902009039400540d06503980350b01241c404126403041600d20b004140180840c80e820b034202c0d900920800003e4400350080300d10355000107040d40308134510030499070000095403d540b2002d00e051507a6102070f0081c6d040040501900c50070100a0008620041c101a52284130700034610048214509560000606900e940f0041021501500f007414032000304680c00b00303a1850f5018203491307c0760646074000c050080c103040413841c014154005204030f800b0764501c0e10320399218040180c115030100c400a004080c0c90204200d0b407402a001507c0d2000c008080100403040700b804038089410442901c800244141c82d401c4528001d845010203600031032900010035414121001c00900c21031040f40303d0540e0f2040702e5070760540305034441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 380684289 1250 380683039 380683111
    0x6060d0507140c0307050d0503070509040e0c090108030301030b090d08060409022116290313050102030a05010e06090f0c090613270203090c0904020409050d0302030a0c1403 76
    0x240c2d0300d454010050faaa60340101004407a0391044112800780c00c0e0240080c1c0b4420b50300c90343c90f5464601403c05200c0035006a1000001900c220040f45603195950b44650780600744260003140c99625500307040403900c1020b411200c550f000280c24074849544860210b038040d40c140ca0101d11454280b01169a0740303565030049031210b035901540340d5a4240400d51400c028114170550203e01d4542c1103191071456000c1e11400c00840d0000300380c007039241c03100c06554484040404180d1000e2507031034a034266482219810f030b5055440d0b006001080407100c41680010094405a44d00d24000903140b00e03e040182c5501d50f106404100045941c1d039450442d002c1d0900e002407034100545d00c1d000008183c2d4010820300c00c0b81120021541e646000340309076407107030441d10020561000f11038207002800d000604181c0c1c04c176440b0405040401d40c10803008041d294942e80040e50b038038012140c14100e45002c424142003021606500302d40984413401d50303130004400d0b0582d060a01d0340c000d446500c07038408045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 380685539 1250 380684289 380684327
    0x30b190507050301140a050310051f06020a06060603140406050903280e01051804110f03040b010e0a0902031222030b071701050306071110021c060b0306060d0507 71
    0x411211a910a02440c1251111820103010403a005c0c01c0140d64001402519010f50040120900b01001c503000301d03402a01c1c030f040a0700810120300c6d2504441230740750040c0026a0081c03a1807070400c0300c148120401848546130800c010100e201c0050f0f40e054025101900f400d8070740c0c012500605080c4212000f9007a1703080e88030040c03541008100c040d04d03184050303400403c003640d41440c0b80394001c000310380300c03020001d07110741c601d072007000c03c110042601c00d41000b1100e100348101c0600154260095000703600480d0b07580c0c030b158500080c061038848014800c05c000350a2210200060320000f9980404610004903035403582030f500d41d49005441e019202c020b952600c1382000062040e05000980561040d55903510700a03052030748501c001f0400e209154042d40643c00040c103841c070440062100340c1c0c4240c1942c40c43c592101c01d0710182c0e0008800c0343c0390b28960b05231100d0001c006100740e400808107009601d0852a0040c0000c1107030061501040d82c040d120000600785520454140a00f6518510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 380686789 1250 380685539 380685541
    0x12060f021c0506120f19030c0803040302011a0a060c0b041509030c1e02101101240501020f01090320010b040501090507270501030e030c0f03190302090a030b1905 71
    0x50355000d400305a403500d010b0081d01c1c02c90106a080803c01e0305d1860004001401400030604615000408412080d001c009000ca881c0d00080c00c0c0d03038011800745010380d0001c11814400c6c5030300c035040000650800c0c402c4d40c90103020404140c204544d88101e640007250083c03a6034550408850307110fa80d4281e030740c3c0503160200d00710825800134420351003e40030309003400c64545071031303101d0342c0c800406800039501004248000035014030a1254624480150340086802c05807407000440225504000b90410208040248040d50b03040114105803034802009000306013140c2c034050314800300554140e0040b1040250980103103000d401c000036151b00640108130941e52848104010441610000005410954117a5241d00c0c0044440300b0708074140411301c036680ca0000150024100e2000280b0540400d200001c40c40109202c0d000710000103402070359981c58080304104501d241900050305151040c40038112076101e614540090b82d80c850021543c0c1d4850541241218221040d00403000d42044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 380688039 1250 380686789 380686837
    0xa0302071a220c2102100206061504030803130f0f0c140d1718090c090a080f0601060e040f020307031d071a031e040614010f12060f02 59
    0x3881281c0b1401c0703444001c0c0090440a100c0309810001c109001e00401c202007010300200001c00030702c5001c10a000194001c4071103c3d408a902440001000300c09a00304004014160034245080441c520750340d0082841c150a50761181642e00000e40803d42085190410a0410420000600c081c580040307036005050035520b440358403454607000d2120f03c02c448803503404c15030400102e200c80f0035901a81480f0007003600c002e0100150004402035031380c54080c8035204180d49a01c0c05160196888034140c5543d03600003400e0103054074103588420350366130103004400c410401c0400c07058113450062904800005030b40001501a10711104440e0a144c400424440c545415520412009036803601d01d440b20340401c45041e8680d40740744100e03418440c40340302c40001100e0302c00007580c0c080341100302c070040300002c0c401c8081041c80032582110800e81c1d8881c4100b01c0c04182c203010b801000244440d402e05402e04100d04910700c20042c0003007140d0f488041c50300c065000e517016180d504003003c00002c03002c2d101d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 380689289 1250 380688039 380688083
    0x20a060908070804171e0a0b040201031107030201060e1f0e040804030b0115020708010209011407170703110105010e0c0d090c151715060702130e0604080903010c020a0201080c0a030207 81
    0x8203400385c082c810f8000340300415022142101020844c04041c03c0c4104c029122040c0d215002001241016640ca411414040c0d9510180800f58000e9000284960400d001c00a032024041c00d03070380d030024404d03003207403030540d80224603401703a643c40f0700e0056176500d403131030324454a0003160002081c0c8150f000011031070f08003d4103107061008882c1e080710a0196600c180508038481c2201c642c2c0011002001203020090300001000a0351003048604c0c000c1184a9044120350000300d021400540110701072410300b402402440d0140c60b13040340074140f50502c0c400034495881108036008416856039200b90034491101c0440000b41440300500d003001e0700c0712500600d041c0400c10342082d4010701c98045610320345070800d12200e600b4060000c40c81c1c210140c0030001b000c4c0e0304d01c1e0032010040d00c916054070f0052052110314002c40c0318502c0039480d08400d0f03042500f90b50445480f0320441d440841d141d000351383d00c030340d2042d088400c03d820282d80703098661003200684288800900b80b0700360110508240846 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 380690539 1250 380689289 380689319
    0x203010909120908120a0203040302120327032a0a0312031401080703020f06070c0b030a0c05090f0402130b0304051608030a120c03090605040b04060c030c020a060908070804 76
    0x894007102c4a032101072102600c00b211680036140325a801040d1007642c0040b08001444102071500481703060654981c00502c0504907110685040c3d04081200d18543c40c0301100c217414403050340006038200038144041b82c4c0c0c40107030b032081c402d20759107103111004000340310003030b6181d5a100a4075489203142c50703042400c11510224500d0000078a0303c000d01d00000c0410703003000d050f07494a5010f405501d2850f000c000d0246c080b0032200d40c1c0036104115000000b850002900700510a20560607100c2c80c0154a0a0458031016510802d105040106022643d1782d0505481c500c82c0c07c650050702c65000140348480030516130840c0c24101400420301013030220029680c1c000d81c0519645100594444c1c802e0394690040031200d10100d003250b0140d014280380354000400301c0a4500d4000344e2150261507410070f4440513981238560b43c0420b000c0c04103214084c001c0c0c0d502407265040c180030101090704000d580700000d60300607112079900c0105404000041d4100c07501c1c9500710b80d901c1e8950740c0300c005200c031a0700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 380691789 1250 380690539 380690543
    0x30c0203061e010e0916060c0219030f06050c1b030910021606030c05250303050906100e09010b0d050706080106020703020a06030f0e03040b070201090e0f0711010f0203010909 77
    0x440c401c00200103110282800c04244002401d840142e480d1225124262001409546007070040e0074009900400101404000300455550390602c1e91881c010301a400c0000e4041001e49034101c4024004521003200010580390f2107100042c0b940e846c4100206070380200641400c09055400f020012142c1c0000600110342d001c9440240350b1812a40c240c0e950072100302d4680001d400d40404100440c080e5000c4c070408591030518620303041c81c034800031202d50b00a01e28410183d550780050010316a15100d8142c0c0181144000d02550070859030790180d800302e52141405006c41d60f80022008034083d04100da20b1240030700078809070300d440d1030916100d000780d00850340080c00e81000042e1803880050503004070780d00506410350305810320704100d010301008030441000342c0e20344c4a8011800000c00c014001020ba4070400c03a21a20f052000500a160035440b00d0031a254002c144002044540c00c0540c209815080144140d192030120746e0143c844421099119407010000041e010040d03000700341224 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 380693039 1250 380691789 380691793
    0x405011e06061103070b01050118050913050d0201050613090c03060f0605031902060304140c090c0c0d03050903041e0f03050106050114031003200301060320060a051801030b0409030c0203 82
    0xf0001c03070f060f41d42c0c0d0103030200c080c02841c00000100840e5000b000901488600b525010703a0258a03038011801c0c0d16801e0300c030006000c4032070302190140700b030600465030115003c1c8024407560401c0c90000b00d064002e42400020715a840402c0d00401103003100080003103a02420030f024407641203100c075004248501c40c80b80a4021000b070345171303c0d01c8541d50068500c0d6001f00361609640b52070711550881201480d15508a01c174a810700681541c640d00e5041c49607080d00449030f42c5912800c132081c01d01800111f03c00902d410141800f0000d000402a1382c06c2e603a10400708605d00b80745640e191160705160b401403070020042c0380c000c021b002064200600f41c52003a201c0e1819030643c20700900e003a101c1113a1030003030106090320a00024043c40d65601ea44100f0b0344201079145080b000290848510341d2003100e603800d8509480c40c400010325044000031008641c414208120420040c080348079942a204405c0540c1140108980c081c0c0d204603030114015000300a550040c2c81c01600681c0c0c42034003a4864 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 380694289 1250 380693039 380693057
    0x60501121b0308040e2805061c081603021e2a010509090a1b03020d1b023703020d021b0f010305042d110603011d0405011e0606 56
    0x1c4001103810040301e500c040050314051034280203150400018100d100011100c054807100303503840b44d80c0000d01c080c42400005050400c00300300074020205541b60304961010400d150042544201078401c0034166045102c0c00c1822890101e041c00301c1c45081020440200c4c02205091000007043e030301c80901c0c80c0c440c156510114004601d680e00b4809854000b0308100f01034120b500f89048100d402111a01c008a010318042502a100c2240d0200000000f0341c04200c802c0d443d9828003a00045182c2410740901000408000940740c0c0025984110b01e410001c190040c1180000c08110120000181d880c205c000e01d494003c0d19001c0000c189401032140701440b0340079196980c24a003441c00f0040403d04403130551801074005d45002403080d1003040701d0201d03c010442024040600d040c440108042d1400003918110b00e100d01d0203407038507010b4030003440107112100c54a84900e0317580d64880740400460344c40d458454003401800460030000e40400c0000782d040130450300201c0a8580c1619043c4003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 380695539 1250 380694289 380694323
    0x3121207090b0d0f0b3d0f080702120d020301030308090c060912070b0403080c07080307050703020918070b030a0b0d0209040201051606020a05030403030506010f171306050112 77
    0xc200700302d0190b403003024400c00062000140551003501c82a00702d0501050103005040080ca800c0c070290440c001c0000103400e8928417900110610711403101050300e040000031740510040c141c82039020582d091041440206540d503000700705242105070000001079035007a40003112000b0303401c21310045011a6901001c20340400c07011513074902d032002c0a400c0a042c03400f00010008a0b0400820040903402408000f16252103c44000c2000d14000c1d18030a5480842404040c5441c040d44d0003c0e1503504140301c9a0300040340401e01c003003142e404861541060f11820304043c506000c60341d507860b00b48201c9000145050b00b107070145125152500e810003c004000b024403441e0304071a10b0007944401014002070040d030051380607005244100079000507224a0fa528401281d10021208002c0740010041108140d81805801c1c0e001000b8a44010140030200780a400080d408003182da03803410355800200c1d14501b02c1108100c2c02d820480032701c0156540e1000e11100703100042d082d42c500c0900090f0780a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 380696789 1250 380695539 380695547
    0x50a0908010c2f030d09030905030d05030c07030908030a0903030e0d0f150915020d0c090509040b0910021605060615030a0207020a18050f010503061303050c07030203121207 76
    0x6000455140c001541039407101c001c00381590405040340d14500783d150f19583c0b04040000d0b03c80303d101c1010004102205090160603000c003039101c9440ba50000108110040e44041625040740c443c07804c054885002c2c1c941912000329a80040d07009201c041099001c4541c003000050441e4000c3d180d02c2c1c04610844280003003107580703000c007500354545c8030384080001e041c040b0507104044a50740000703201d00b0380760750300c131200c0001034841c80c0c0150f0045500e14014213203101d200c14003012400c0c800ca4040c50080841e509010080c00584955006800918911024003454507007050003002155a8a103121200105800038041502e01e84100b00c00134030701d0304216850504161a4440e91801c1d507a0704015040a94050b40b0100c0e048170000d400050b42030403180705408110000c2101141300d00d8011200075070740c035050340020b11a92024083c08000c0c2030011044135016050700c0c103169200d8445a0079403400d842c5600c02034242c82101840c00484104401030401c00c0381c92a004520f40e107420340212 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 380698039 1250 380696789 380696801
    0x18010b01020307031101060e04030804141b01180905010f03050c0402031003120207180605090703150b07033f020405030c090a1b02010b03100905150c0c0d050a090801 73
    0x40d0140e4030400403180130a0082e00e0101c0300b1aa040d0010428a4441c0811155000c0035203048000c54511400d00c0100302220740e03134903d04103061000306041452812480720021b42c844803d414408401580814203000e06583c0e0080d180c154070512880d690341180c401c003241a840140d5160140c040c9441c41440d0500031680981a0442c03221005400d61300c0312801c0c80607070705442080d0321480c103000419001c800f444054a59281f0000281580742405100038044014a0b103400c142c0b030148680b03480d0610844507801e880015955940321000341c034050b01c4002550132201103007048183c081e48402e94032000d8103408800d51007028403490f00c490b80c3c130080c0c0c0207601503183d040d0041c005100703590812130480740e40400c11203c0440c084c000c48907180315400c6000e44010041c4d445000d034442d9030504000801c94814606800c210920300f545989440e400c600300c41d07910030040800822084440c10064030500000101034134088201c245001d8090f9004640446c00301c0c00a400c00070b10700790103100d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 380699289 1250 380698039 380698061
    0x1d0d020d140f03041136090d090b0f0c0a05010b150c06041e0816021906140703020c10050406030513080304021005130602030714010b01140d02040506030f1801 70
    0x440c1142c481da500e0b2206404440c04171500810260928402c400b82029100700a520040f14000d60010b150448074000000804108040d40001c4801d110168450260001c44004002c91a2100622400f042c6d9030710400d00b40040d80e115025401081c00010b6000c0301e08024122888400e9040717804a00304140140204107140da0080400200400e030044c9071100c80c0090041da1590b940340650344c134a010780098050114150407509020b00b1801d0a600d0b03224408445a00600201e15241e0f006085c40c10703a80c5418480310700480d4602c201802048840f940d9407000300104600d10701e1000082c4150001e11404000a041801203003050b040b0713100b1107081707d4100b8189440c42c0e84540a012101c0441e48044040100400034601d4481c40410000064a61940034603550300d89803c003010042c0f122504882a41d25006060315240c3e001185084820010202c0035124825011001d009000d260f001c0303174100070000104280c0900d00841ba41c032075610800c003220070040e02034415081703c01050720 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 380700539 1250 380699289 380699317
    0x3150306040201050a0f020c0406170c0f030a020118090905030d060b0a0e0f0a0305010e070e0604020a020d0c06020c190218010b0301090908070606090c020f0c01121d0d020d14 77
    0x100f0401500c60444203806c00103c0c01120354281080011a04075000c540c4202e02045003140304068000b024004c040d4215030441b0307142d1608080800180d216692010024140301000c41d0080c142c1d450002424024980860108600b0300c040c1050758403540b001c0314003a51249445c41c0400d40c001031a0940e0b800f0b150b0b81e514961248103100a0001c0300d115219842e0b400309103080000300088007400750352652000341024240d29417500183c540c00340c4010300780510a90051146100c0342e075002904114440c1c107840c00034240c07200b600b4110001d101e00089080c00d8010242c004a880d0311b00080da0003d80d1094030040112200e61003103620002087c09a0150018100010410074907550406507041e40214025850b001c410754461003182c04035444581c1031515405211086034041c0b02d0340103d0340f000303c0a403031204502c0340000c0803141602201550b60355503881103d814441e801d4008450a00d107001c9803804440d49134040e644100c3c1d1082100022605031010311109003940c25100000034120f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 380701789 1250 380700539 380700547
    0x20d03091e0e0c030603011d010e070b040509060603180105070305100e070801050f011b0c03020a0e0f0a050711011d0609010c140702040b060a1107090501050d0f020f10050315030604020105 83
    0x69540543d41c0090105d56243d9240d032144170b04201c10850101c144240742000240002d040344100341018031035440341452100034081007103513444921803180d2080d001c86c0e000f5a20744c1c8850285a550011140b41e4100d9031034042040351041e0564081400340a09494803618243c0c1d40c80c1c0c000000d4002c6070b40e800003e008200400090038422007203a281b40c0d0505103c4a070ba5a603088041c0071000c40c81c03040c0e500504070700c400c1041d41403441503180900581012260545406104155042005003058121656030400180b40740d10900310445422000b030000e10041c80700405481c81107400e04040d82d4240039200110310704040511681d19911741988030b0040b000040140d01c0d109405c8903009a0f0031980f50b24210010f42e40c0c401c01092060783c02d03107902040c5000598402d04d0302540d07404c070b582e0351482d1900510055860140c0a0481da9102c0000030110100c0d202091b07443c0c0d0400780c100e070055070854890f268190044040c601c9041000c42e44450105074004143d0341c1d24007a20040d0114600f04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 380703039 1250 380701789 380701801
    0xf1404121d0102100504031412181908090604030602040b0c010b0103061a13090e0f0d02061302061602090a0b030c0a1a0c01020f1603020c1509120703020d03091e0e 72
    0x142110740c1c418040d0620804101c00c05a80d05c123640e20503082100c0b4104000104400c903100603442010603449580100501046420030007481500f451001e4280c2ca000300e402c0383c0302da4407002100d0146038840b038103544465031480c800006401c202c11030003c3d9400c10000320701c607501c80e01ca528100e038010f02d048020003107000d0010307030194010b580d80b26041101280c0450012030900411004590010040c801010030506290910000c0349a100031504003805020340704140c04068014980c04489056941580050030403448241b8040290851424001c00060360483e501880728424290250b80f4000008410802a8842405120450205030f90003203400e92200300501403d8403004e00042c5401040742609000d03405c08050342081c1c80314003a0080030940e061044603400d800984400c4001c500e4003001010500400c810180030b500a580d248138850001c2001a0007185c02a249400020325801d000380035034824015600f840d00e041041a4001e450b82e040300c802c6894210b41014503460f00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 380704289 1250 380703039 380703041
    0x305090c0402071707050a0c2301120207050a1b0b09180403021915060801021c0c05040e012c13020904021f0c0b0714040302040f1404121d010210 64
    0x441e05403003130f4603400c10300036055514000829105005078014101849a85450051440c26400c081c1c00780f40600314154200d04030078070300f190800c803d00345401b9800303250000758000c0c010014094628070482a0f074400744a5018002c00d850710b0002205801240c41c1c40c0100e40720f00c02c0d80b444075004480c8030181d000010100d102250020701c244181c403031004201c540ea07050000704c01ca051300c800715032074400d8400a00074441e44c401004404000c0d0300b04490a0150740d1039543d602c020040843c0c84054243c6207038400c008a6002d02603c1040d080c82d0350b110059280c101007400b8440440c51480c07070034107400d51110381000748540e1249040e2030040b40c00790300740029281c0103030049030032040154000141100c1d0311000c03800d900059650446207655420b1600105001820707410074002c014000580c440884002c481c01c1d07a4040d2030101e0000e00346040003000340380c460340c08120301e00303400284000c00c154001c00c010141c072281e480d0000e0301c50490000710030310400804031b40543d0010604400100203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 380705539 1250 380704289 380704297
    0x7021c08060907170403030e010b040e060f040219060e100c020604030809130f020327191407061205010e060a1203020705130c030501080a080a120608070608060405070305090c0402 79
    0x8a4504003940300d290012004c04100c1c10b490442c08280c440300300c48111032091003030181c1481c0031602849038803c0c40000d40c1d120f22001d032142c1074014865000031305546074801e01014400c0003030130b00804144d03100c500400d00515130484610030150030000421043c401c0d4030842c6130325001841c80349000c0c0303165181c030050750009088079081603070080400214505480f1703144140e0412600980d03280303030464515401032070200c0c48482c1c00b083d0148180952400044082c1c654242c844400803d07a4a4103000441001c0c9084000485c4105400814001d03801800d004a0b020b10401c24080c60741c030b90715505000c81c811a0255007101c8140c104102042000100c100f80b40e0007401515840b54031500464203081d0748850103d21035460745082030840c5d500d48100d60043c40b0300c4000c1e0102110b00c0c2da8a41da5403140b0309140302009000081280300c1724840e44030a008002030303070490303501340e41d50600a069403608481d1284110b01e000b0000740c819020340a0640300d001070401901002c4030007001c200003508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 380706789 1250 380705539 380705551
    0xb03010b070c03120c11040501061e020c1e0102120c030708070f0501090c14030a111215010806010614090109090c1211120c070809040b060d090b07021c080609 70
    0x103550600080402c1d41036100c00e044a104d0b80d906203803907055080c40070f02c8402100840d8040c0d85441c0040001d580e20800781402c405d055040c595180c0391340e0008078584111003100541c0410b4034141122032140b222906d00186c02d080e0280d81491014100e440070138081d800c2241c070030740c204124020000f00d555008000319441511101c8070720301d02d501c0b102c1c01c69045090450710709041c0d14043c01070f0080e05146100d0450300320300a020080c101d503510204020452291030040084482e55500003a0502c0f1130500002c88001480656944080555840000384a031a002c241d800e928070342001541d5046a03204041078644001041c079100d5281c00074000c4e8002c072001c0004000d456450074100d0702941fa11306a00f603080f141c6800d048036110509a030003829001907000104006c00001e44076800f654014001200d0001d460308400010900343d10404050044151400d210101008102c00e607190141205030700712021481921803080b0b91303d0b4840303a410701040203280002c4280c038182891640c000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 380708039 1250 380706789 380706803
    0x402090a0e01050a05071d18130b0901020a1701031211030c0a0f05060c070f15060b032401020303070c11040b1c031b0b0f07140a030603110a0b03010b07 67
    0x6485a8120b821940c0076070342e03142c086448005000095900c08100311a1000304c01d07002500741e0003a00005e40441e0a82e0015005041d1a400180e1070b1025550207401907801441ca4034103490320218540c001d520030418403012402541c0035450825000c0c103254140c0350700200c010000d020461060300d40081c01d8500401e244010840c1c04494101401605413842c842e033303104c582d568018034005e810203e0040c00ca82e12554140080c401041483c0300c504085504040e10916929202e4640800740400303407c000e40000340081804080d2494151903070034031b511544041180907406004917124170060b901000001d10080481000c1004a6203a1520040c02440043c0001548001c00c10b0031800c050056106211044090241741c4c220700d1000001c01401100b500050031951071802c44a006800c2c00c40d011207000001c0c0c0c0960041501500890380305071a00d480c0e90400c1d03001400307410140400ca40446a084c190403007420414848401c1e00d0b062141c003421682000c024075619000464180d902c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 380709289 1250 380708039 380708051
    0x90108060d05010e03040602061e060618031f0b03070305120d140705041701060305070603050903120c0301181404020d0c0e070509100f02070b0f0408010509060906070c0b0402090a 79
    0x2072024410310551a0851005e144c98901d0140b019041100040001d043c501161268031600b010351000a41d20140864001d52a0341405106581a4011305a1690503110f001683d020b041a00504038400b04072091080c00081102c2e428951901054400103100740d0120000040c000314480c05031012440728500014521507003400504012400d50703803880407170360018051005070300700c2d0180d10390303000100028010300b851507a5040c1d981001d40304490406076a10041862600e09004481800030356903000c03446414005004040c5d46e00a2080e41c201200400081040c40700c203000700e0f5610103000081e00855070701d0f5002c0c454518280c690441e80000600c001051801c0110ba076180070385415901c117900d4007a035000340410040b400c00c51401740013103c107417124034940c0002d2031416581e47c401c403c0e0b01ca104482603c0564015900301c8509075082c43c040055403000024501d100f41110000c848054403000c84c2922064101c2d034011341400c82480000b40582800100240c020507240000285 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 380710539 1250 380709289 380709293
    0xb0402130f110712080c1903020d2a0e01050d1a0d0303050115050f031602070503240105060702062b0203010905060102120a0207140d06090308040b0c040605090108060d 74
    0x1210300101e480700184802150480a00c005440d0b80f0240c911903080403100703170401c15403c20150182400c4080b400e801f512132a0180c6211b90141c41460209820620613080700c4149290b1b01084600d2052100c101703251803c042c0392013a81082001641a16000d02d040b0160344010081d20b030302001e840e00101d1440084409860f00b4146082075030003a039000400b035041025a002a40544c18180d0801200303002d032100341c502e20b13422250000d0b29800036600303d410a400503802d00e08154031142d0304d4062008030035441d403040510221b81c1c0c1200111000c03260388910400c031042c0100320010750003031000c1c0f154050021100440381c0d4000c03021525960040746a910380c00999100f60425045280c458080c0581960104003a038070669040d42d84500704003c980c0001c2d50766074a84030308580400c04030000f44080e210220460714042c0c00c44c03414840c0b01c1a07410054000042078a0031149242c02c0300000300d1650070441642c040e107030150307185898032403820011168200060f040780e6000c0d24030b40c41a00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 380711789 1250 380710539 380710541
    0xb0a14040e0106050c070b030606161406011e080303010b0418061a1804090308130f02090403200a02010503190e0f0c040c0206010509041b0914010f060c0b0402130f 72
    0x30007040c0940d25617540d12020200c16081503a10750060018810910a10103159107003010741d0b802152002c49102c0d1f00031181400d114045c2940600794160044c24008240d5203030140c04000000c0c20148580740d4a95100100d9030740380310902c0303a20040c0c0c8003480240401c00300d40c081e40c80c09120745040819015101c1c509484101e14194181c080d5501c006558074040c2d00e01d40c000d0a000b04222402c00122100e85c80240c1707040c200810701501e21401d0941c03c8104080500401d15158020340f5022a40c50689000f81030003103030102c0200f81045c4104628580900041e00d088002e506079540c0742580c9034455080c0b1403141c0580403a603816115881403420060400035408481e001000030620440003d050104603215910408215004a40180308541710001210340055100c15183c00c0c840702c20340c82468440c0c598001482250901414181a0155250b018140d50107001e01c145403569a20301544c071601100b0008200c0e003007140000d409490070254400d0404032900021030161046a1418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 380713039 1250 380711789 380711791
    0x2160b0d050105060a1d01031e05010303030b0a2409180b0127030f0501180506040c05060a0e13020f210a05040f120215090309040c05040b0a14040e 65
    0x10400086562030200a50380142401840c040c2e82d40c9103812801d10000f4456003080e10b108500030744480b02c6a80c00d0348294403625a03c64102032104a5840d81c11080c40605400c4c80242c00007410b2100c1d5100c20301d840254401100c6400c1d03840d040d41e0550400c5060200404494941401195100002d910301c103203800d00034400702d6900000301c100741c1c0c1002409480110340303810350b9901180c1c50300744a842901c0c0c40c84181c0b90811440c402c020701600e00309001d0880700e425584100a800d54010421100141d42401a841498541011038540042c44018041c210a1000082c2280d0000b1110706008204890640c2206409072a1082c60200c080703455024003085800880d02009d20b0720300101444403107411040070b0009102900f45511005070a500302100a41a581d07108902c01c00540200325040d240c0c03240a4403411a494401449a20b0b5004020618011410a2030b24800d15103d4000c50301624421165642070030010042154401008505c028030134200700000304040454000c59 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 380714289 1250 380713039 380713049
    0xc0309170604150b0d0303110424080702010203040f030e030a0602131703090d080a05160c03020117061c030c05060a06030317040309031403130b0307091205060f070216 74
    0x2420309003420f180c881030340b00003400004032007458400c0d0813801e540c5044040030300c2d540520780072401c2c0c041c1e081e00c04100e1080b0742c0003025a02024110040d0301d01e29521040c0000b9051701c40709519502d5900070380c241d00c07046400511700e2050303229000008c0d00a000c001302c0f001029045a100e560640d07645012a03000314200e140b0507a03c4c0b201089098a90340c00070755001a030782d0145042405071004503034060384400340105600000b045078002c95200d04155042e00f00a003004943c40400307414107100142150105900040661200000060305003440398040c0c903020b000d502034046240340400b00c0c5801e4145c00c81c00c104044001d40c0104808100d024061410a900028000d10310b150281031301c0c00b040c2980d41401403020810005ca80c00940c90001c0300c0c2c22040c0f03980448002c91382d030341c113610480d29410801000c480b0040307461180030008d188581c40e02c0d11500d0025860741e15000940e40603800041c01035000c6000901020010051541c024289004541c010500b0710005219044145c00c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 380715539 1250 380714289 380714293
    0xe151324140f0a14030a0f06020405011b050a030e0f0901092a12050a09020d0312060909020609060c0319080702010507030509061308040513091208070206070c030917 73
    0x18000c880080c0007203981040c084451402ea0030b02c180100300040540c0c030a14040341c0d910015400d0603201170010341c44556008950300340a020925040d40250480c1c00f459001840c110080310800052190310349103035800000504200095641c104d5007225140c26503500b0200d2407a80ca1038070b403122040075028046250010170415160903140e01c87d1040c0d101983c1d9810f1012507459255034000c00980e654042a039404034980e60354072400d0015040068000790094005076440b814907170310540e4120f100039210018072216944015000685410f0385d0084c1d0b000908100c1071081d03280403402008445000303802e4034184a04015050701141c035001c610004112080100101d40b40e0a00c5010342c0500c160404200c3c50900c10f41003641c44200030f0465020741c1500381c44406103c080d6056500615004200d10309014242c885103015000d206002c884003070007540486945401401c6041c4190721650042c507070742d62500d0084425040207203064080c8075a485020802d054418030b24034041c0c1040b40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 380716789 1250 380715539 380715611
    0x182004020714010c0c020a0326040b0c1209010905240f0d0507020a0b1f03050d020706110c0f06130b04030b06010f09030201020c1003020c1014010e1513 67
    0x402d050070756929030722050801c005000c035400140c2c1c840c05c0d1002130f6600f010403d0f442c40808889050350300861544085c15250200d00014044601c030300510801140f9400d03280017400440c041e02e45405080c4006004c41c2e5400b0052000b0300304102c0d2881502c81e031503202c091079814406030440c590710059002c540310000190100030a40b042c02426003101040c401004403020710b88401c2c515a00141000c402d131080421103040340c0d803451040e000696000f8082d50300000c0d603818080d40c0d80c5c50600c00c1d10f02083c1c011180741c645010200d404400f9000c003800c0b1101d048003c800300081c9510200d0010f00803010188081100f1680d1406040030710300c83d100380200c4e802d2000001d00b042c80c0d284425820010703030442c10700051340d0110303c0c041086819140c002d115400c4c02020760281c0030390b8007420314074030565080308403149041c4c0080c5043c2120110341d041131790300c58481c0007080004980034071603010484443d02690074400045032101440c200001141584541c0c0440f80d031199150200900460031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 380718039 1250 380716789 380716823
    0x2a040f1415060307050a050c07090c090509090d03050709030501050c090a050301020c0a080901020a050f150f0f0103110109081605120a0b0a09020d1209181820040207 73
    0x10310099007254911569003403018141e4002000c0d4840101007008100c03002c5054681c10340100203490200300141d040c1c07402c294803480b02c5002001c1c0d50400e04001940510000341c03608100520030b014a07103400140603031140001c2d044d009000f000d8182802c00820700750000200301c0a100309401000011241581e03118058100034001c0c07410340040348a03034410049a0604c2000144589480c1e0f4080d11568840f044440140d04014250f2009803941c003611400861100e404900381d242c1c02503c100c0c910268850b0a504407481104480d0103000050fa05c0042c4007051510b86a0441d600c0149090400951500b40840c1084400014008070303c61444040c0050320b080301c03c40400d94260801403070040d00c241c4400b880c0040c00380038200401d6440f1140f10039516000361191300342e41c000300c1e4540c41c0040568024035600251040904c400c41d0b458a0405c8160540110440c940c07841c41030042d508010303180c0c418101c004070b40d041128503005400d184552201c1c0080c000c240d0040e03204210a138500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 380719289 1250 380718039 380718071
    0x705060108010e0715080a0f0f090f0b0a0c080705070f0c08010c020717030f0706060929010212031f0504060b0c01060509041e0c0305161409092a040f 66
    0x54000a003003203150178011101d15030040501d80d010599000205020581c030040900814141d500d2207103281c1420805c400b405011420090118030801d165003503940d4596a44c0c040342d0701244e04038005001000415030f11032044014000c6c0b10b00410342c00003102819596441c4800e10b0754440c0a103a5190240c500c006601806000d004084880d030260f0b42003005c0c44415102d00c074038030003403446070320110f41002400826070025002d0850031008210142940a038405407120041070b0b00046c41c03040c9000c01c003030752012501000e840500340c1c02038110b846d40320300440e0f8000c81510100700e20191400008640ea91809aa03006044078107013035542d400d01d030086d1420f45c0c0c42500310a0040e040d490074400010503011445180003601e50b03181c03804441a1a00f4448180b003030f4000307491449100c88041e956400b03100c000044a402000035100c406094040c0001a0300c01c8038624101d821002008114943c078902d5600040c2044114180300b504420000f401c0f98030712044804843d6641280c0c890707803401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 380720539 1250 380719289 380719303
    0x30d0f091a010f170708010203010608040c12031b0f05070b030a06080102090906120a17040f09200a0c02030601030f11060712031107060f0c0206060609240705060108010e 75
    0x501e02041169030408407410101280c1e0711031818074441101010004e00c0051041c140500618002599a540c2d6004010300000080e613064030340b540010400540c0259159000d01c00e207605403214107206090316a090348160b02114203880186030517a00200007042130008501408042e14a02d0700c6c2e003003100b142c5040350459001101e07180c0c030420480380b19968110405138007120417901040e500c88545582810810317040d0005003201d415241031008a0000405031058501c0f401c410400d0940d2000c1e050f003035603055001c2807407a1003040e201c80c400c0307000c030001450000c0b03150502e460140d2071540030a24004099005880040200b080c0b0010040c1c180e400380e00401c806c603005810182c09071655032507015a40e0032001403503681ca8040d00c0c07090301c1324203584510b0b41100b420040c0d0350400e40c400d00503008040c0310800502a0304d0000c0d06e245402e4040c0c2c0c4001ba4050803000c14041a4070740d560520600705201104a0b00600c05400012800c001c0740e800f8140782e100206520854000c030900d4105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 380721789 1250 380720539 380720573
    0xe03040509060603070504031506090b01050f1c0b06120f07030c02030415140703021501050301060b040509060a0302030d11060108060105090c030619060e031009080318030d0f09 78
    0x420001041640e941010140e0400c404071042903491321503080c00d580510a0b80d0000300386490004003c80c0b07a10440e801001100c8008505006a56801004640a200d00c00c001800b065040c0016082005480b4005032200381240f40020f18040c0b00c40010704c240c1200344040c01c1c2d441800200182e0303007107030910180c1024031800e042c4149034860002a4681c0142c2c021007281c06800705c500103100d071103803140c0410500388148242d0f59003514203009445401407000d1495590304400001101c0c00c051041104a4400344181360030b181c140400c21400440180440340d10110031040440507075010300060100c42c0c1162108921450800001410180164070208080d0803420040100c1d440d8503210652013a00340d0040380c0d99a50f91000208001c260600322000020414000708485820800440d81c0c03400072130854800c5a42d0345074440a81d00840002010340350140040350310101d0341d5004000d035580b0740040e00c0c01c2c110610802800c4450b10704000c0030b00c1e03446400c21001d0003220041400002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 380723039 1250 380721789 380721793
    0x150108011509091106030a14010e0f0708150d030c021e0316030f020904051603050105180307120f02070e090105062107030b0c0405060d05060102010b010c03080f0a06120b04060e 78
    0x2d191034440c145401c480307035035050151740000001030441685074025642e18046041d004095611100304204c0c200003124141c400d29101c40204525034050703000c1d207200385000001190b030740200345c05000d01a0440d00c4100d00303202a000c1400016a642c817520380b08030b9100702580310a426140101483c1940c01c1081d0001c0e203803000b00501c041a446090100810b80642d0007649a4440e0300c0c045240004403054500718500c0030001204019040d00980d01030503d200000800c40040c50f01d198891083c0c2500408010102c2c001c503245a014200e40507520100e401a9294940d8504480b07000002c116808510b5965440402c141851300004442d091040116203202c44200042d05503511101c0d4000501961100c0c0009004050500102c8000d840003501d07503a04d9a0640014001805055540034050750030074a1420031948078262015541c2d0b016a5480110781351006030005144024203d000441e0329490701150401d0001450b002442c498417003006076142508000007124400c0151100329 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 380724289 1250 380723039 380723051
    0x2214011d240403050702011b0b130201020f240901060e09010f051e27011112150d03081b041d0105040203090318030f0f1f090c06030b03150108011509 66
    0x2c03a138840143c07981c56a081c00c1203086003104010b10580c0906903074005290b8030410f4104004a03072000d551030f41e114800e8080358042c050402c1044e0321903411820400d003c40c803058003800f511078440810b03900b20050300000901c46841d04885001ca1100f21084406a034580d10420703418001c610442d94860702b900403000c803144421001d03068000d00644820b01110b1490311b03414860341480c0c091030140d034008008218400040a0b4801c0c035801400941d001940107600244002d18030b00501c010054000300200c084500558080d558180c000c0c0420030912904c1d000703444a03400903c0103001620f14a500504280b080c006022060031050300403e005500610900245c5a030010035644800f500030000031b1000060000f00c1d02d0500c141e40707060070300e20074131800407070050002c50b40c0c0c1c1d416244a40311504079640d071469503090b2643c580000b0304d11616040d003001414031a50040c0305800000341600c1000c40c3c6600d90791003505084c1c20040159560b41c19003040c02242000000c000c0070300007428860 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 380725539 1250 380724289 380724293
    0xd0b070203032d010b0d061e0e01090516110f0a080d0f0c021002090420031008010905070509133c0503030705071406041104052214011d2404 62
    0x110f03a0610510f1580c00e004500e055102070b16800480c040c2658045d0000080003000413199904803030b1250007140081d62002080001003405184d02c6680510318070041190000400c43e14036a8000d06e40d00e49024070007030001001c60510164045501884026031241c02c03404030b481c00c80301500e4a075541c25140c41079000c002c0d03801180304100d00c0742d813102c0141c0301d2810f03d0120300a80300d520341044c1000b007100346d205541103450003c1c60045183e540003500140d10b81804c217003203912070364010f025644200d50401c1645031200c401ca900c40c81312100c601345082681d8641c0a1042611842595034a071508441144c0303000803401c9200d1001d11a00100040071600d4258486c07202a008601308400041c1d04002e1080b50021904103101a8003210490720f02410890072904070114504c0c407841c1008041400702c201c903d018607482d2103484412605d806240d403070712200d810a41b442c1d00c2d15500c40c546020300a0003d40701d01460290000907255281e4400d010f0048051700345c20646c141c9850300c0501c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 380726789 1250 380725539 380725621
    0x6090f040b04061e0e07030302060108150c03060105040b03040309050910030f08090102071e090c110d0806040b040f0605030f030309150601021203010303050a030b100e0409020d0b07020303 83
    0x80c0103504903400080d9030a8025150b0080300084684c030381500c2c28000341c420b030080d000820000300d0b4026402da0300c1603600c5403c010b4980440e01400080c149401d0003140e003039104003005541044050501c0c038503050350f82c400b001c00d0340c10840d010340101d640c85000f04614102940c01d2940414010032080c085421552120907811410350054040f004c08541e44515900800c07100380500641e060b260340c1305000d0000e0b000c406503180609031805082c0300400341c966000f1141603603034030101c0c005408001c0610900300e581d0500280459801030312001c40e104c85440d14444d40300c00c0c86000e500802e125007030905042c900b026103512140c841e4820002c2151900000c82c2c401c1070200c03403120036459501c91000407441c19042d08110100d03800000000010550808024040346071152824031030080748408011900d01c601c1003d1011170f01d4082a001207103401d42c4000c008901c0108643d201c0340c5540c4898414a008803481000340c3d10000c140840d1102070301c40d007091441b40c03000c0c41c0c040b8051418650 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 380728039 1250 380726789 380726791
    0x30c17210a06080601080607030c05090f0d0204140c0711060f0a08090304050301140f06010e09060f1207090c120b010e011110110d0b03070b0306010c08040e01090506090f040b 77
    0x40000030382680425001500e642125004018a0003215003070f5840f18522078640e1819190500031034501101103000c2030061064600036000206185003840d035076014002c040030341c1d140490f842a41c810144010351604c3c81018081c04200603100e44404551421200248040c29158800e41085c8205080c418200088030003409c01c3d17142442840c1c4513a44070b0392039402280c020a41c15420a00d031117410b04a207000c4648030b4030780d080301d54106813a00401910a0701400e40d259821850640001d0030905008030540c0c84481e01034a550f2124030391508450400c900c68010300c0c00f464482c1c040c09080d038bd11034020850700b9422441008107590940c00038000841042c5141e050098511014820380018460a542142080c40502c04421052021103050307018511446c031851600c08001c5150034000340032020340705505a07051443c0c0f20440151660054454103c41c008410080840c0031503003070810078000c0010810204641c2000c5080010308440184a8200a11290100004560005102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 380729289 1250 380728039 380728087
    0x4050c1002030d0c320408060708070f0507020102150c09062709090c040f1103041a0a060303080a0911031c030b10050702040902030102160b010f081f0b011803030c17 73
    0xd81104034103e85d0306006006903408800c0310b001f20820030500e1354104c0e210030f215000e01d40d2080c3e0810706130a0f061b0307000c1c0244100607005038843c0714a003206c2c903210810140c000b50360892440c1040c0c01c1030005100e0303510000702424a503240b981490320807641003e40444100003218078070710303918141302d509540d41c4460300b605124036282d00d00d050406505610911403144400e07a995564079150504010003103c44070044c07414000d0200040094095101340c8013540d505a032025202e8a41441080280c50500026500950a0500c0c0c00d4a541c007040b00e0b039543e020f6a41c0d014110f2a03c00b82c003a00f01c443c60301c01207000d4006c103606200c040da403040486050950460780050740104170300210b07009020381c40c42d500500d003008140c1e906011588002e1030484654036000c51800c2d8688500795290031030145102286070500e0558a0415000d03008207a071400c045c90070030b0001e803000311440ca480038154429000300319128049810b00601900540841e920498180c0c030340111032240240801f110300c0380c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 380730539 1250 380729289 380729357
    0x1c091401080c1207050d060905041403030c2b05040516050102010603020105040302190314070302030f1902060a0c0510020c010b0a1a0c070306240905090604080304050c1002030d0c 79
    0x15113072801070042c1c0b841304054020402910b501c0f0742e00f0700024042642c0c10340748400e45c26a0300340c4042c1b001040b00e01c50000780f00a01c0c10314480e0761130880840680028601c1e0400126600504042c041c800d0038032a41c0510002d081581100c40c8214618505411050469051200c1440540d03000001c85045940c181c0f206c031b80600031804150808030260b00010072500e0541210404200005060f41c1583e0080303058a2481058025003070365901c044d800225a0b000d0f0207007030400751078080082c00a40403103040c030b11030202050750b03405e003045100c0394403900c059404545c1e5996501e0074801d040f000501900c000100c01d0402024541441c0355421903103030104001110f03200d0b035406214140086a00038018006818101c42d103803d02804100b04a0603030f030760310000141146160248a01517005213020701031607100c0e0f8035220b00c50341c4014400d9800c0e1040141c1c500c415202ca40c08010030100660107543c441c6144030034102680c0c1c00c83e428602f0004107242c10402c90260410803d181a02080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 380731789 1250 380730539 380730541
    0x30301060e0d02032a060909010306020a170f04150218040203280207210c0f060b0d03080105041d060c0c0a20090c030f070806031c091401080c12 64
    0x801d44208080c2c029058040c4250840c3c030407284e0807a1704610302c0700e07041c2c039100328540c0d0040c0102c50140c951800c0e4004d60410042000c50040d60082c001240c081c505510750f803c3d03500c6010100401503d410503a08543d1003040b0a00c81d501e4414007413044e40a1302540750204402c220b091003140c18002500c21a40080480c480681d0b10010140c8001300030340504d607102c504120400250030121055504880d1317100c20142800203612a0036032407940c0d80b2a9401600302d511000b080303c0101d02c0854105555400442440c0e0301d5501a8003060300c01c2d514100780c0d6040134113210a452550b62003946054590b25001401c00d40402c5940d880440c465400b5120388030540e0300e0303107030694007440500032021444481e01c44c0301d03060441d101500015100541588c50b0140c1c1d00c00c40d0300c0102c0d00f00100b0740081012a07000b0380f00e2040d05420507801002ca800c0400d20603800f0300f20f0010000c1c000c01066189604004180582040c140080801d090000d0340e450038000e004414410451340010042100c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 380733039 1250 380731789 380731817
    0x30601201c02010203090601090c0210150b0313030e030c100c050a06020301060206041b0b0d0e10020f2107020d050d02040b04090606020f1b040903030618060515040803030106 77
    0x281d8940c03646500740101c00c60368221000e4000e52051721080c905010701400405c0303000b0b180c010425840c0b0a58000c260b40c1ca40602d07581c0c010f080c3d80e40009038081c0c40410009032200d440024600030407a01440c02c0340041e5071719001d00402030000c1d04034065000b440d511201d503521103040452035440c9041121b01506980703421810010801001001d0610100c00450010740c0018a5032080d0311450407504100d03c54110441005418400d04d4141d003000c108400c070303107412078014203c40c0010748222200c0d00c2300303401c0d814141e81040485a041000c04991102c07803180204004003c10f110111241090600c071301e0094850f847d00c8295400c0c00000220b804516600d941207a000300603000c1d400b0344a80e00c2d40440381c05003031181318200c010704c40e4507201d68401c400864141e4038900c280e085201400346110034030028001c6080154181580c403100041c091300003007013100e0180c0490070002022414a0b00f04a40020b440d08001d00703180c4280401c1c80b8841700001100e054420900744035215240b42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 380734289 1250 380733039 380733043
    0x406150e010c1a0103050f060921133c03030c080d15261b040e0102070f0515190f06031203060f0501030c140d06030f08030a050a0203060120 62
    0x80c00074400c080ca2103418120f0008075003884c2c1680d10540a98044003a591915079564005584402e05500310300c0b110702c0075440c041c1c0321400c1d1002c4002480c1c1011042c1d01d40c0d403240302c0d40340e01c084425008103400e440038a07a410505203100011000c651550f000c85805040307600120300001b4144030403840c80d5010b1081880a40d454503036068028016800d00b8601301c048071440f481240a00f1a0b0303541c051800c1244080030360307810f00004004000c1d210442c1c07680c503940c000710030791150490354442c07030840e540c9400c0c001400c100d40224004010b02403140741c0380d403034035004092031010640c0541c103004a22246151003103e240c007a44020644120030740c840fa0091100c2c0c2c0c00100701412024004450035055000300089803d15420348148a43e81c00c0198252150a0301084c006020603403240000ea60301d01c0508040f04e181140080c080762240d8500310401180034007520b0707074803001c01040356100040c007685500030780d0304c403043d070660070f00310000303002d4009124541c4000000081504082c48007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 380735539 1250 380734289 380734307
    0x150e03060a050f1f0e13080f04150c020306190e070f0f05040b06070b150913021206060d0303020f0c0706050414040207020d0b0712020307030c02010b0f15030a020d1401050306060406150e01 83
    0x7030865550348c0500381c00e4116682c854441d020160707d40481811101e4041c5084e5440309130090003030b15131550381c8001c02d890351400550184a156072100e94030f00310181007181c0800791000f00c200581c42340c209104150310718443c0d80068811400e042c002c200c1f94035074105544140ba4060359001d0141c452021404980c26540380d01d0344c20490a00811421034288485265801c1c000c0d00c52443c400040720300b060b100c0c0421100300303401c01c0340f0280800000b8481c5c0d000340030710f045090010f424528440c12513400d0110661144000840124082c0b2407184030b211800500c207400c8400b10315040080c2d000c03a20301a041c15000e0071a180550024054a003e00c0c865a0031240b1840215500d262040028005150b10102400107610f0300301c015459041c40e040c07482070b180c0b00901c455208144413403c90004d40c00141042c81c6103409100320600b95155006203940c001d1120b840022540c10310f01414603000c801440796100e035040c030600300b101c0f4044076070341c030340360300c020b241c03c00300340901400507a06800c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 380736789 1250 380735539 380735543
    0x1050703030f0504080306040509061023031207020102060903180f060d0507031508120906220608070807020a150203060109050607060b040605150301150e03060a050f1f0e13 76
    0x4140f904100400a202000f1071080078116010402c0c0d032280c3d00c1241d51490201d5105408140c0c1c41001c1c41039400d4686898a041040c102c488292844c1c4004241064030320b0814a44807040441d4100c00c540c1c06000382d44d031010003030005600b07014044264510103034000d40f10030f002e2080c181203481e0946581044a081205142c01807055060820004006054034031408a05002a913404100c0c0c0c0400b10310501410403108400d4100031080080042c0d50b8403900c400740350061882544100d40364402d490340014034080c2c071040c990780740030b80c0c024080c007000902c0d1108541000240c000003591140000101c03502041c00107889981d002d0043e117204040780c0000754040408141c1d1810842581c102891381c03642034400340042a500c0b42408505002140e050380700c4c0d1030a10040c40004003d40451003800700500c0c080011a45042c080790074650b0650758038840c11349a02c1084402d0301082d2000e40c0000d0400d8040003080c036050143d0848a480d80152100c000450001c184071b54400c7e01d001091035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 380738039 1250 380736789 380736791
    0x907170f0103060f060e0411030f07030501050f06011b0f080409150305240406050405011e02281d04060f06080106022503060b01031b11120403050c01050703030f 71
    0x10425400c0c60304442000d1104540c00c0d4100101c009041c00c0d140107010803144000d850034240d44840d600e440e0110700450b005d5030035201d0705200887c0d011041140d4030040d03000c0d034000291403c109a45000e140c1c0000c06850600c00021800448110041d400700c000d40c2e04219503201280345450300a4486c42558490000c1c1f0b81810001038902ca07113480000101d0f40300c0c034226140311103d100002c1104006104820342c4148640004000c200c5541107142c0c4076124500005980148003450079040005580e203106880c0c0c0170561040d01700c3c1c910151000540015120080c6111901c4010050001c414204900442c10100040c00d40c0301c980045010742070740340d070303240c0300584601000f03060b42c20034800d50005100b4587d804000480140c480c4904544001c59140010305545586000e01005400641015070b40c07151181100c11075000008011040c0d81d80520f1600080c81040c40c10105007030501d1550805c001c100005040090042038201c000e0800340d0b01c0f0381c00380c14240d00500703039900c81203540c5e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 380739289 1250 380738039 380738041
    0x9010315090c081608060c0a0f03180b0402040c08060919110406022d0a03050702030a0b10050a050f10180b0304030503012103020703110406180e011b0e090717 70
    0x100f01041c3c5001c0f48070704105400703501c0c0da034121556031180c0981e403085902c2000c20135100b480744280c860013030340241400c0105030329402255152440d103c801092714000452030900c0704500d01400303a014810240d10781a44942003000c0003640c40940a4594011101101035441800c1500c2e0001142075080c400b44c039480316600d0b0304c080e40310400714a03001640c02554920605103140d404890a420710700d00020145215a81d41c00d130f49986c04180140e0b031504c80c010001002552645183d07100340f640e0b0003803500d0580f400040c050011050b40103e44207400a00a10000340ca41d0108500d04900340d02d8544024540004401c0c0a4680e540005074896000000c004c1410381190040d4100ca60700ca203241408a43d07107490b0302403414210b1009005030054107013000450541c0d40008542c9000078400a2a507644080121b5041e03902c00400c005980ca4001c01004c1641c00c0c403408c0d2080211580000820110b034000504020643c190307240702d850003802140f00310744111594080c0407010f103074071809 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 380740539 1250 380739289 380739299
    0x50910020d02070209160c080f121603050901020f0306060724020901020d11060a1505060c0105040203010b0f0310020a020a020d110901050a0b0d091106191b0209010315090c 76
    0x1a6003c228180d0060781400089107a00300ca041643c0c08445c25540e481440980d555185079160f0702c10181100d410800b0302070500d45082d54038815008140700401c15a0f00f0403007040c00f03000d44600401010107a441071202248120054045a9022008841c296901c00c9a032410120301142c480e0384210030320183d607241c03e4900465005098031402602291030340101c0c29810cc03000c0100b00703561034040e00804045600c405041c2c0200d070000301e4030721030f1045441c0c0351004282c5941100c010411140c0d1290180400d508082c415010341c040305941d800103111403540825038a00d0004040c50304183d0004242c6005842030180a1040c1d500500c0d41034250001d040603101e1080340d460b8a44680c10b503034000942840e260119800b12400c5035091404c194042c180c020040c500c0c3e1400b510255075400c400b885994640d4001c1829941007100c440c18002e0a45008004c00030700441001c00882c08040200580c1c7c1d05400141101d90001000c2d0744440d6180c60300025120700e0000501c03000d03050f100810 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 380741789 1250 380740539 380740541
    0x80f07030809060105030606012a05061f08120708030703060518040614040b06010c0819050301170c09241e040b012f030c030a03090c17060a050910020d 67
    0x200a15481c01103900a03605d5030205500d40e6400d50ba0240400c80c03185890405852000005107a03281c000c100c0c040251064441c03500b422405c603a0100c184800d01d4065601d072400d034810380050030340e80c0002c1600c2c84c07200c45d071880940701b00074024090610201c0000d08241c46500f0400c094040a0005950302c21400c90511341d944040d102128034500702180f01031f1410407050031500c103a4101075416170701d407605c030015140c40406040540340c0b070300108400710420038500c1100720740c801641e0350326130340307614124280b401d1b013016401086458000040d0100c25540c0c80d00c0e0039400403550900d81003e0000c04002c1d0303682c41010720059170800c0c0c0b41d030008005941542c8014040100a8a00380300c14105c0c440119406003088180301031021450b00d5500a61796125070580400c456081168a08070820b200b2078510703040140d030240002d4a03030603045c040111880c00312000b0040414100410101114200e07120000100079521440e61a400a1442c1008221300440459401d00c00c559a10521520780 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 380743039 1250 380741789 380741791
    0x90402240f0d0b011b1e0203030c0a0605070207080319120e01050901150b300103050a0c1a1b1c020601030605010b0a0203180609100f030e06061507080f070308 70
    0x202c803841c40e050903484194024050700c0c5185110001c42c0d50324020700c0d0b131840c12076040c0401d002046600451400010b0310104024041d1003140d40061880410f580742000070f640c00201184119080500c040081300b500106035150005e05d4400c508180d124680c0c11115164003590480a05081a4802e03032802419030000d4080d00040c1c0081c4540d0000041841d5501004e00c507803004d06000702300005400510305101448245040311008540280203000c2040c00341c2030700151500c2c3c02c10000b00741001180c0720344100600c0c0d26030741d80ca80c1440e0030101207018091a4044181129000340b9800304c0c9000b407000214205444000c0d183c05411242c00a613500024001218050b180c00008035003170456606807009801254000c3d40740107104054600c58003200d00105801803418480d0754459512400070700c0c81e21500342e80f551004801d21000405440e040b01d405500703900f01c1c4050003182d03281d4501600c03000e194284c40a64a00b000d16119403240718a0a4921000001090210400da0f10401030b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 380744289 1250 380743039 380743057
    0x3050a060e1603120e0f15160602030f090601150504030b150405091513080405060d0b0a0e0f13031e050d06080105040c06030c2109060c210506090402240f 68
    0x11551020740c5c201402254581c4046003a8404c038000c44c6440125602d40060440e0022042d0440c076050321903a5100aa03082a0303101c102a6107030104020702c0c100c040111600404401c1044620001c0400700a03003144114040a00034060740350000300328260280c40c8000944025004204c5403400c0740c1020b80310021652940082062800403d03409481c002c1e40820068204810701d242514100c2000710307a901110001c9140c41c6c1710ba018550959554101c80c00a11800301c40003035170302d400c4000683e54000207001c159219440d01c0c1c018042070b80150041e25203603180e40e05071217001e1f6112060b21280070364480c9038000ca0a04d02c3c040341c00141074000601541c0300b00c01c00c48031203460f0340b030a805682c10050510009000c05032094804e881c0003640d40c0e9007a550080016069460361982002d8500c2040c900c008144010307000707000e900c0f04603070041010018403002c210170304120001030b01140340030b03001911030154550350220402d1048503200103000040c042e0750b41d0340d032204a16101e9070404090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 380745539 1250 380744289 380744297
    0xa0f060501090506040e06031002070506010306060e09060f0a110301120c1d0604091707050606010e0301021303081b060f0703050a0204050310110d0f0e0f0703050a060e160312 77
    0x20000d06940580802030030f440c2c0092109003083d0900d81c030b41e490610001d0596606118040c0007816030001c502c001e0906a00a0024000c00c0d030660a21005441e01540304056034454501044043c020104035a0b40201c1190034508083d122081030030094070500003001c040c003000200000741d0015503e500419503100b13983c003842e807a54800062080c4d10a030001c0320503065040c0005501803500398070801c080da10400c0c0c2c511000e8290824200301e07810441e03088a2503032200c030a2112540c0c20021400c020711045009614150000038a00c18810003031000400007000812506c4600116402555120f076040d021120145400d070000500040c042d0361000c0441c1c600030100303c46411600803182030702c601400400c01100000010002005140c0200d5a00c04044c0f01d02600c809803402400c00354118604045640207200441d1818400c3c00d11071142540d001440800008002180c10b40038103402c0540001e080007071203d42414606d5401c51b0171070b080d80094022040241040070209082e0003652 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 380746789 1250 380745539 380745551
    0x509090403030b121f02070218060d080c030909010503010c020307020607080403080f19022404050703080a03020405040f02033102131d010507050f0a11061303020f1504021c0b0a0f 79
    0x7400406c82c494580065000480c08560754000b0111801842e000080604445000601502c4e418440d410035414901c540c0c0002485611a1420921441c09010114001c000c3d07507000030070103540e0344140c2500034080c001c042010390600c40c028080d24011504489860380c0c400582a1020140c0d0012511030303403000e64280b044d41114800140640101c1c250404003030801480803a260100d10010022204c911511001100080d4030b9406040d030b240b690b032009602c0310704110070082643d03200c003580d00031b40b4810b108010781c440d0340c00071045480030011820f9410144403a0480c2001e0305400d400380d04800078010026007600c660744101c0180c001c10203101c100030040c80c0d4a50982c0c0003901c0c488002441400345051103046203006203021509400c0001030141c000600604000c000c40b1051340c03c000e2880444241038052221001c1d0b0703955200034002501d186030101400d5500603001902030022103ca842000a221156104282d00030800c50040e01e000c0703400c4000b07004d03c200700380c100c0f0741464 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 380748039 1250 380746789 380746843
    0x40f0602060109021c0203181b0a05040e07120507080d051804021201090b060909010e011d07020303130c09020304200301090803060d060902061309060b0a0509090403030b12 76
    0x2c405d4504203090340c4455220748076038800c1d24010790805044801d00743ea042100281d0007800300f08200e0380b034600c2d0019903040410801045100f2140d035001a014504044a07d07032007840103d400c90039968017000c080c01c140414103102d46020299044900c1c00e01c500078201410581000280c030001295031410b0920a80201c1800144c1c01100381118690390400c00603c650903643d08841180c0c4000f03061941048616030004403c0a82a1720841c01ca00c0164014011108001611188000070789118103103402d0003035000355603200043c0b20710251103c01c42080104620003090300018042290f09546034182801c100c000306441c0c09a1404c40381d01503440c40f210b41410f0191007662a04001c0d1142141c0c0c030030703040c0080b4107010303082155226a0b0b03440311401607032660090441c0306001c40d65100d610341070074010b10840311103801a421a8505002c82060560f00ca0212032080106031000d810079216440c0c2a4003034030501d103003213a1002411100c85488000000c240c1c1051035583c112000c011014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 380749289 1250 380748039 380748041
    0x30209030a320718110702040f0e0706091523090a0b0c1c021c03090203010902040c080a05061912050f030a0309020306060d03081803090d0b07020c030c03060a110f040f0602060109 79
    0x40300784417603444018003c420151a00f9444022032501c14040829603200c1000d1103030034060306812045c0480c0134010f09214034081c0c000300301c0e107c80d51400c145035402c1c1204145030005042e000c0306000c140b00061061165116849000010b01d841c82045454030b00000886442c3c014200d0003010243e82290441c0c00c0c0c51000441c5503403c00420818075014803003140480240c881c59200ba80c043d92500e0341240143c5482c828288050800d584282072070411440004c15118050941482100107000c120503083c1c0c4265107804845840d1107210700890315143c03503403c110300d0284454a50101082c9000c8058054210320b0285100303d00f52100f90351180d0820510749000300020340001c45480000304411103400d90401098400300840c0c4c101416840083e540284400342243d0b40000102403140007901000700c000c0003641180640540030741800800d5803035000401e44c1b41380c25143d080410301c400d0040308690110304161103d981c2c89454034200e0300001d4070f500c2039900500c00c04000141007960703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 380750539 1250 380749289 380749301
    0x3060d15181a0415110403120207170d0f0804021809030d0608120702040c02030705070f1404090f02040f1107080406081003051b0105040e13030f030209030a320718 72
    0x101c04840f4104c907035060b40030001001ca1440d10303264200c00b0800031000c50286030030103440e07940743d40c0240034180c20081c400c0090b074115034620101780e200c4c1040e000116000483e01505510a1801c02e040b0759903030001846010501c941e110300c01030900240145400c0100042c060000f1a190074000760341d540320056a50340000460000190040c890880140340907044826a213000b03104807418100f494507003500b03003001c640c0600707510002600c013004942c04200080b00c8014040320200088515521492202a41c2d0740303000740300e241e5540c0c0e8480d4280740d952107202140441280c00d82c0360046442d00e402168000c1c092000880d528500103201c0c000f0600045081c1c03a880000741074410800304500201c0381400110606000c010300000c1a028124201544909006808401c054403642006011509840e452208060042114030516140018550422070b07101241c21000703510404418001e5805006070f003074004110990341c03200c810025039182074030100490b400400c107090a0000885007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 380751789 1250 380750539 380750543
    0x50f040905090f0f1614031c020d0e0d1227030f11030106181515020102090406140d110301020c01020c03031006080f4501050109060b03060d15181a04 66
    0x345a142400142c3c106c040810800c0310203001c407036460107c65000409840310360102001070f40701040030701c034880c0c0c00012b5403141441a9105100c803100b41d03d8001ca602d0305280b085080c0141c0d03ca5030301c91007600718140c0c0c010225444130f0386640d5499203806803403010300c00000d03200e4001082c1c0605203031406101d000e00315a0a040d00c1169074050103890005440310702c910f19919101d000000440403030800d400b07078119116a00040e81c6810130000c100894034240c01050002e400d420303502813691a05281740e110150440d03d130001142243c00024003902c159112010154000300f44e20204607000400345000d210205260000141c603050103c0351510120313100920010b0400220300340045a00c0ca030041456000c0300c6010241041d144107104e60031000c0d10300b0089004d070341c0c048a1200207201c3c481c0503080384401030283d1460700000800c00c1c040038001900c620341e000800003c000144224142c0b0942ca544181300c5c5c45000316042c1001584400309540400c41e90815000142200c22610701c215 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 380753039 1250 380751789 380751823
    0x1030e0106081c03020c0724030b10210f0504021503060607061a03070608180a0c032d080a090923130606030b011511070303050f040905090f0f 63
    0x907040c1c000c8011001c0b41100744414940d01b000070010104091101038090312401000c0388c0c03006804215030904480001d0540101071070310540e41607568804001c80c82d440d420303107808001e00d0f08014640411f0500e10201da8031051400f021201a2441500950300c078900031646000d05000740b40d00c1860b01c1c401103410343d900880070011a80010301540c00b96080c240c80c00040080600700c2d001003407804100b0b40082003c04c4501e010043c0d0140d07400405008100c01d080a40008072940d951000500701707600008100300c0e01062541a10300504049000b80c2e500008100641714080c100034502e64409103a17140010224080451402030034083c401100c044540c070300d1000302c001d050800401c10040e046061400c0511803c0009c18a1801220041c5020b00801c3d6020b51400e10031080c1070a002404005008405ca4981c182802c04500b010440e60541840c0da940d224a5440d4040d510441e005080c03050b2030030041c80185c000014542d0640c0c4800000c8a11031204904820340e1031110a602950103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 380754289 1250 380753039 380753053
    0x110318060f04080312060a05030c0310050a241401170a110d0908030a060503060105091816181a0f010e0d0204090b0910061805100807060c0201030e010608 68
    0xd0409000800201511412407410291a10074060540e80002c4c00081070000440c248030301340c94240c0e0300704001c0070200c00034610401c602010948404e086000d44010a13540e8000900d4251103412460304200d103c3e0452104081d000300c48001354007580116403043c3e0f6076054450583d40155041807001c0b0074800d034007400c2d59502ca1050080c012942004203003400910042c40c00700b0041c011204464400c0c40070548074980440701800301c03005a0b000c54441d40c0b1030001008903440d81076180d9002680183c00c4025800000350b00c9140c0102c00000705040c40f4409000940306203460840c15000806007000d0202e00301902462991304002d8040741c4d401107004130300244a45c05040030245105014140c1c610303030364964001400322250f0f40801d4420b04080c0003045065001030024442c1d640d0740b200f040000b20f0608640e40c5540d003241c009014941d9468000c036603003030451030b80340c402008036800701c80d2080c1d158031700140380b00b010040490201f8144100e6107210b52040c087e042c140e8955000620300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 380755395 1106 380754289 380754337
    0xb12010203040f0311070b0d0c08070c0206040510020a060f0207120c0b01050103090305120a021e091507080c06090c01080708040308161701080d1103 66
    0x115910400c1004001001c69840c1281c86030145001c00030600c2d244c0b07030301d46819025040840410008901c0c18541c80c1640c03c6011110016a84c0c225035480388002529000c0c29400000d60140d001c1c0800c0c0051704051510500002c020300c1100d145210036294542203030010060640d10710303000a07c020a10201c2c0080c3c1c16103c900d441c04080040385a10740c4c516050045c001c81c1e0406464850800a161080c015100d40720600000c0310400d09040d2184130096104440c414035450100c650460303106d64640070703602070400150200220609134103054109501800c01140c02040c10b0200500c0c1b014100102032245003d000140b51800940c80050140c0000500d22020400c005041200080d88094040c0e007003000e10103022000c210007001039988681042da030040e46078020300002400200000c155440480a0b120303c001d5808054020f07480f48149002500850600f030284030b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 380575539 380755395 := by
  have h0 := BRFrame.cov_init 380575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 380575539 ≤ n) (h2 : n < 380755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
