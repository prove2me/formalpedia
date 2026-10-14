-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:49:01.042479+00:00
-- url     : https://prove2.me/submissions/f9bf8212-a8f5-44ac-9ce7-07118b3bd3be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 387769784 ≤ n < 387949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 387771034 1250 387769784 387769801
    0x1005010203031012111f020f0d09030201050724050a0b010320130e0108071509030c06110c12030d0b04060803120c0c010608030901110d08040204050604021209030918 73
    0x200807130701e0900302103075112070350b05208003010310800055402c03110341d40c01070a5141c1c2901613440450041d50899010301c021414903900c4005103459000064100c2c0c90400c0950702c14030141c24102d0280042c183c014802141714861100e11400c40700c907154840b4200225660144590001c0710003c0c00c007808950210005190552036000d0501203010000c9059200c1911281318000034045420700da4417196198440f80307940300d00d64880c8071101e051000215550600c2010103c0c04c480e44480510b00b0f5a051207401d0340d03078038002c08807105640715600308c1030f4a968030090310740040c0c0d88000c0074581d190717540d08810b410340b4184145da6001c2e0342400020020404008121401c0c0f048021400b1a00e4803144030305482031140c0400d0b4000b075030a00002091581d030200c0200104202600c41e568405520040242c4401c03059807050040380c00400041c0150030035400450340550000d10052402002004c83c4d60203007026142c0d0040c1d13510200e8540703014100483d444045055454410b412791412a80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 387772284 1250 387771034 387771061
    0x120c0f021212030f010f080a03171e04060f060807050d0b070320040f06170a0c031104182d150506070303050901060e090c01030e071d100501020303 65
    0x80c011035421101c1c5185010511000c9002d1200002c00e554a003054a2000c80c0582c081c080c0c01c07032100c0030b8000043d29050000e071700d0701c4d8240d061701c8808403501111250b0b148240010400c01c400c0c11035180c801141e00c80801600d20451060030300180c40d003111083c90341102d0003a08000c059a101c01d405000c96903850b07007041503150707120f404c40e41280d60f0584128060134900311031101c4020071528111130383d4000d60250081c3c9031141d0006002c15640c0c1d004960788030703c0d0b0341c0924041000402113410f02e00c00e6040312003902c0031405c2c082084000e01e46c1c000300a45c842e502c400ca1201c031003d0380103141c415030b0241e030103c070710010b13020f8485208100c4098028000e030450080c0083e516014580a030240c10040d034020f00300142400d4450806e81000740241c0f00c12030740c1415652a01d900881c4038808402090700400f0040000d068030006440103500802c6d2210790901700d0320415100140c54841d4450041859030f075908200418200074a00301071441d80c1c3d030411412b642050041054460440e034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 387773534 1250 387772284 387772313
    0x60f14160509090c0f1615050f2214030a090e09070b03040611030a0b03011407051e040f0b1e03070e0d0f0204090b01050a0506030c0a050a05040b070609120c 69
    0x40f403a0600351100702c00748205100b100f054542d50040810503d80c10b001900340061400d0240051034640060689050201d4004503a29098140e5540100c0d0703051220040001007040045000a06140c0588031180c40d0f0840181d428400c0d0f01c0000d400302a00e50100c5080020102401b030607400e402c0c50200251078200f035006101108a0200015041c072010360020030b9820120794840d0350380e003060705100c0d010f00316004983d8000e60800220800c0d4050354089248160640d03a903142c104600030946214014601304800b1b007901c020b00011400114040801005000c4440d080769075105603402c4061f07030510040402d040e9a0306004018102ea00301181c1040001c0444265158110750318000c440050013490180d001480c2410030700402c58400318590603290200c40ca0301031305c1d07a0b44041082d40d12044035921110103042c48481440ca0013103010b0070380c005540c10300d58103081d11544440403c0e00190000d955698403462480c00f84483d41d08490003944691034142804909521107200c10340604 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 387774784 1250 387773534 387773539
    0x5030c03061506070305040e0a021e0a080705030705070c0e06180f13020616150e010207110405101a0d140c220902040914181005060d060f14160509 65
    0x181312003c051040b81150043c0c03102c9124047c143c1000076401c0700a41249005a041406446402c41030000800030b0f01e01e03c0a03039a80d11401075881c8901181c4541003c1d08030010701c0b4040c01080001214100358074080c005d1030341141032615041d410000d950044140300c4404103894420300c014144070003c00c0ea800f25903444896418640c910104919115841c8041c0c40e071925421610304110180c4c6001c203800b085131400740030a490018030300d400c0f4070a036000100503903c0d9060803d65400c02d034003c294090919a02100c3d190340d10720104001c003a1210f9802c0130a10300207500800099544103141100003501640fa10754940340076049698810f40703c40103590302007800d02c00e290700102c1404501901e203004096482c0c958501001c0c000c4e200356800341e00180b00210004214045840f281d20210500000038900e40c030000c40400c00074540580241e4000c81c58055000103c2c0f2580a00141014100340002c0c5828404883e0b85104401410202e0381c0001e6211307034540254004191030141108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 387776034 1250 387774784 387774787
    0x2010f0503040c0b030c03100806070f0c02030f0609060901050709050d140f120d0e01020306062a01020a09060201050f092a0a140a1a040e0903210105030c03061506 72
    0xd40c18218400c1c0d46035130081c040604000104103e42040e07601642c041c0850082c0003000c0342e101c0680c90f0b11601c0031a0400000b030f00240c0041c408912500e50015070074005410741d40390041e9600100d06043d402c8900e4420f80c0d1225040c002c0007039091080700d50040031032612404c140d0038940003c91f401c40f4844042e0001c400001003407415001440400100c4411900b242c400c40c403266151061508080050152280307047c907118134009041c02228490280100143e103082c203003410719500854425101444c1d840004a44c0408020910051040840544401c030185152500007401d45000901c3d48000d002c41c5814480c0700a80010264084c9680d44440340130408008414203110b5001403000384d0007400c404000803003081254140681e00d0040d1342407401b4585414490320403c0030701c804684520750400003080f20342d0803e80000c1d08404031501303032403404050303107a5148614020890340504400180c01000340b49400c02c88450708043c1640545010b2502c0301d0307903049130141c003041103004480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 387777284 1250 387776034 387776041
    0x3060601120e0f0f0d090b031807080601060801051c0201080a020903192907020a150b04020d0f06080c011d010c0206040602010e0d03111c0f060605070605060d02010f0503 75
    0x1050303000709402c440c0c10070480e9207060340a610f040d90f81843c031014290900454900e0240701c2e106201c0c520540d0404120b41d881e54580030714a01e2114000c0342d00b1280c600030490701041c014010310000b4000c01041d81c030000254108020082d074a004065100c0c0b6211341100c4410041c0d80100460b80d02c850b409500580b125540f101180c285a1101c503503042c1410b6501086080150513203080503500d00040700e904d80c41035107901240c00001c082d01c420025901007035650000510a00030907501200c50840480d1070081240400c040e40c007c052100072203904d0745403c01e450b2450744602002085240002c0054040380c4001804041402d40341d0610841d01c1c3c0c0c466205640500000c54000351b001e8481e0b590360382d690200038000c1001c101c88052a0050041e40900c4034860f025030900c140b070b20035040c0c3c903000319040740041c6d40124000f490070503138403070845031421011031003440010086a00c03070655943ca01d18200085420080503544252000c0c0c01e42005030344d00800b0500e2402d51030611655988 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 387778534 1250 387777284 387777317
    0x160305010b0d050604030804110d03030e0f010c1e03020405040f090506330d0b07021509030301050922060606030b03062d09150109060302010f030528021315090902040503060601 78
    0x440031026070090045142b000800d0b034558800d0b04080390b407400b6200c00b40819840a802da414480328140091a088084001682d40201c80d989482050500500d000d6880c070100c1c0540d40480404040159113511190900509002540d88440d520381d01c0c9051480101c0200c007240c11402d42071070032103c14070b03850703019485d803402092905400034440c1202e8a001c2038000d40ea1a414a25203400c4410341c070104138529400416603042c2c9000400e007800d260f4840c04801c1040e100341101c020f034100c2030249000450704910820700501000e950100302503060806040c80c205014205000461403610111050403600d04842080c2240340b540c00d81d5501c0340083c0500d0008100c1003010700c2003c01000049800851780b280085910030303207480e207241c941c1d20360640c101c0d0402c0f24811100d035882ea00c10080040c105c6489582c0c088080401810001d540c128411407403040d4211005032103004822010464003e03c40500810444000350320707103400d04022070f44445018003058184040045142e5905 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 387779784 1250 387778534 387778553
    0x160803041217070b010f0e1509070215010305160605070809060702282d0e130f0c0504060b07150207080903030304060921020616030e160305010b0d050604030804 71
    0x42c8036140003507441e560b203820208074002081c89207080f460b8800c07000140b176021554085102d06114241e10002000740c100703124007a81e0003007800c01180221012001200c0120160b1070184d4041c0000b4101403018080f042550710250300f02ca420b0200a0012100052015084500398501555500c0c0c503003e10344089803108540800c0c0001d03070ba00e40f485035805071181c3c4000c48201e5016441ca0f1003440d42c0042c000021a40c802845940c0710303840e14003131260415542b4a076400c07080607400a940040a81c5030030a60409882044030304000c0d5000410181c45e05004010180c11080803c9190101d03990f0740d800c42d6102c2801440e551034010032004184560754080d0b900380000542a030742d40f490b06242510003032842c998110307600384070a04101801302000742c044030204550f40003040c580d280c085544103007a84440008041540300c7c0500122114184540366944409643d55014181945040c900b582c02c0c0805050180c0d648400e4800411000926241c0180e0141800711440c0c0700c42c202507144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 387781034 1250 387779784 387779813
    0x60d0b011e050619030501090b0d1103070b0703021b0a060512060112090308040606060302130311030a120906120c0e060901110d0507030327021c0b010b0c1608030412 73
    0x4502c02140000c03803610b01c10000713801416107507401c1200daa21b8000401c101c1d1078400a060b0404050442240081c142d81c08203d4103450040442d0501039444044000c1a406020120016001039440c1807504010189400c580d0100b00c4940222a0500c18028072a009415996400c1042600407520b5a4000c50526a400000f0a0288007130303141c1c0d0402920002d0242c4044a50514004000580303900c03034800e48001c409034202424800b0718540303501c0c40d00312000c03020b1030313050041001c401c0000c1d18680d04607181c1d07101625081c550070714000340034001440f50820219041e00744000609290b5000d240d034290707030030101ea40b15101c0101070012112441607019800c11840b6421407041c042c0e80140140c000980320340e0382444803204050140d01aa035100d02d0170b0762820300c45c8002c20018a041101c8817101061052a0304120106483e101400a02a44140609034000440e1405507400b40400c0b54043d01d401441003400d880c0c40d44a940d0791007184190283d00355521400d4040007143da06d080391 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 387782284 1250 387781034 387781039
    0x90c061903091b140102011b050901030609050a090510050c0406140904050103050715091802071401020a0509040b1008160c1505061023180d05010c08060d0b011e05 72
    0x300c003560ba1a0054890f581c0070ba800c24254001810609610501852084000880b82d85848290311141078420ba00300e9145181030585414000c29a02254840c8520a00000c00c01040008942c20194201420301e01c5503404c541c1010104410700c0010300458045500718600924146070b01e40141803940200c0c0e0141d6401401c0100020505c040042d01c0c409403601900c104102d45402901a1405450740c0b0400700c4011144014100904a0b81d010f4140c041c011090310802148a03500b050880c1d1100c00c421010800200d17941c030381030409100d8914100401d442c0c40c03a00040840015182035401809140342c4040c5101485081d0710400e070101c000d580c4a0080c64680407101c02e0f40001d024100c0d003040c01041044442020503100304840c0b2003000d109241c41c65405c004415041895000e08041424071f01c100124000c580c6584540440060040e40001005a14003000414807200604101d00c2040011802804500c01541c418111200134081c1e41ea01100b421001c001000c07103034413071a07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 387783534 1250 387782284 387782303
    0xa0504030b0a11070c05032e1104051002030d0b09010e0f1906121205040605160203070302090702061801020a0e0103090224030906220f020d060501120209090c06190309 74
    0x42101740c94000c0140d90084040c1c0d02d0905d405412020424008100c16106002da42203100081ea1254480c0c815070628000032440c0c0ba84070340200b00b060043e090074a005a000103450040d89003148914105c0c110111a04241c951620078054954000070b041008480100d00100b45040f801c5100c03c64400c4208070107005c059620000407002008030720003a50380c02042c03081041018414803c85094400039101c036030825002c440c40411102d000c9500301e0701445829404405a510140030900c60b640071350040a10b460140f00c609841111440115107907070052000b054501e8001d1504900118207117800244c2c4940c070300000380c1c0f05000380300038a140c4142ea40d07810346d000883e0740110301c20600c140c1150030b03681b1144000c00544420b038042c0051807550714044000244014003204284e40004e101c95040d494944682e42201d000f03a10504091210016030021402c2005869038001004005007881c1c00380a00800c40d1482200c2ca49003054501c0241181254020f40c002d031200e079000400c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 387784784 1250 387783534 387783547
    0xc0f060b030a0b090a1a071b1113020417010905030f0a050f1206011704021813140f0d0903081b2a18060a060f140d0209010906050a0504030b0a11 64
    0x843d00d940d0280c1064441446415012070710740c10140d00680039002e03e544000700000c0c50b0a9000300e40d68a1001102e80e01e010386da4060740ca2b0755820307c2404503105440016510f91a101c100240024007640c803410f580d040094039004641c0105c00e4655041480b501140d480c128224125014407910780f02401401010400303c0190307030a603c3c0c0e9446440d080e00c6a00310408051080f0401c0c1604550003035000841c1e44428103202c580055a0b41c000c8903204d04088880faa90390f0306415030190a040c2e02c4a40e1080b240052901000c008120841907641000c2b002507041d92641038903407082c01c1020340a245280309204046800301302007000c144070307010349000058582e0000041c00e441e0041c02c0307101c0c00d01c0c0e00380f004040303072480200c6001d120001d0000c0d04051034150284c45606550540c4002e00c840304081506071130155004044004201ea80140d4481c4a8000901668150380091040260511083c1740c0e050f00841118256504030070140600d81e56580da5602400520f103018035801c9011408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 387786034 1250 387784784 387784801
    0x21614030c130902030c0105131a190c0b0703090b060d0804030f06020a030b06030705070209091e03030109060e09060a0f09020a0e0609091c0e0a08030a18060c0f060b030a0b 76
    0xf9030304003032089050341e80b40d98442004480d00d00400d05800b07100c5156140170440c0f01000c0c104d015114101c500160f0a101c0c1c001018246219400c0f803038004281d00508803010030043d810005da01000d581010040071440d6200d005001d078005200c580142d02060862040c840d0481c280c070000d60748200301c0568101b003442d04001135049081d40c50007003414209980c03028034103d02a07074415484ca540c2c00d410000f060b0200300340660060160106401614120001c3e101c8041c8986500b078500e00c003c65a951510810b8822900c442d4005030482c0c408509124490740d000c246260400312a00b40442c0d42c03600c000200e0021300b02d5040096008860b0031001440ca052401c0091041004944190595580307015560700c83e41e40001d101c0b403003110001c8034a1600d0007241e22022030103001c0d1211291035110003c041c1b8552202c192807020403150344599803071b81040300310080130303040a00d08407901c0c500d607a94003192894078107002004152240f003d045141c82c200030300c1c0b801a0f004080e107039050504110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 387787284 1250 387786034 387786041
    0x170703020f0a35031c1508120a110303091507090803120a0b0f01120222080102030f01091a0103020f1306050406020d030504080301030210021905010605040c021614030c13 75
    0xc144040c0450400310f40d03070100685045c0003101c00e002c2103061030b51010703100502186044070303420f131001d00b8081095142044003400e009500341d8420760798210001c010388500e03480c40300c03020141e0040003001108503011640c0c150f00c1803040098015a00d44c994150784414407908800410300c00403411003201c0c2042031005018513440c041c02c00403c0300c0d410034880940f0140c2d4100d070104890b42049100000e890340101160000340104402c030802c02d040c2d1510404459024030b0241e03401100340304080d88044075440c0149845002000041c0c480f14000c411090b090030154103055001c2440c80d01208404103c400c11000b051a03543c4003a110b000152190b0443c3c040c610041c841d900342e01e114036009201d0240941c0d0003024543c21680b0319030800841c0d4101e5081072007107014001210003202e1401012100702031280001007155410401440700704d0310200c200e5400c5500108601d01220305800a507016141c0c040f8007610103046110100303150007051000c00d90402100703507119611107020761 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 387788534 1250 387787284 387787349
    0x50d170c030c1006150513050918010f060e0f0f040215070f0b040516050102120f1201091a0a050904030305061507030207090b061c0b040f061707170703020f0a 70
    0x303040171810311200004841e9405a86a0884203d040400520651a251410f01d03071203030046c40b212030041c100084040c00d603004400403590054849005010314091201e00d02c0d032160b0030800c4110310340781c6120030038148000030b080079004020784030900801355891000c0710b0166822604980c4420014546201c19403401c49003581d4a004410008040400070a80c10f800c60340305a000341408070860f0304925142c1e0240036541d0b5003100c101b029501066403055081c0c024081000c0002c2c00b451306105a0440c032103c940c1042c450364080030140800d554690030640c02030741614002a90341c3d10030000c00c402c52280490401140d00104e200f008040d03000404e032003030f1840d481c0700b401200c90b0b00c4c040c4440c90080300805008040754107442105582d940e80669000c1600400104446141c0c580c0202154259007180d150704903001c001a031010000c120302c0000305640140fa0407a8000b030500d80d0b459003400d0000034815244260449843d61f1040030000c082c0c001103a1800f102282544240d68490104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 387789784 1250 387788534 387788549
    0x6260403090b070b06130e0c09060303040f0f090b03120a08040501110c0d110609060c030703060b0f09031504150c03021905130e0405120a020a1203050907050d170c030c1006 76
    0x6d800841203215140101080103060200414546078048100000700324020b003800e40510050200060340c0c2040c0d007101004207100100d02d81020f0900a00c0c03010341c0e1112001b117000f640101103c1004154603021584058030b145880d000588583c40c10501500c8400700f1060444030101c1d80e44c00d00075001c6185410502540ca96040007040030050a464144c225032213017250304250300007003c4000c1c0c038008640c000554030340000c41903151000b5141a40081514841c0070001040e040c015080800c0181c11000c8032030305480c0c0514103603443c40140c101040d94000105d44400d854100c031802501952226400380c22200404d602e2410014010341100e040f40c2521040c0710341c00a08030341007021190159810002a11400240d044c0c810340390380c001036060085100c0c1200007800314140c0061204803074059038002c100d034101480d44030314104068008504c038141c442c1100d800079443c110280c0040c001042c0058913007088510184c114002c5002a90341c60080740050704860071239034818001c0d02d500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 387791034 1250 387789784 387789799
    0x2041e030203060f060a120b06090c09030a02130b09130507121a070e03030a2001020a0c06051003080c0c01081305060a09111201051006260403090b070b06 68
    0x15200a001842840041d4040d0082c901249816003207a107501d43c071003c00b82c4a520f8080d9a07810100400000c03400a681141920b024000a40380110340c0c25004000415058100105500080d4503003807000380082c80744407180c440c51840d540035002012241c0004281600c0e070318200c074000c100901400411500c6004591000c2184145840c180e090550416050a42000720021403801060058550424019508406050780d5000c00003410303d800ba55640d6480119841e030708490a019031040414680d005200c45802d00d5070101c4035282842d0002804565901d464542c1c41044082c1e07040a0860b02000440300443c000009103481c0a00003030f0b0312038041d60b83e0340c505000504c02003980107000341c000700c000c60b0b91403510350051301d5071500a00d61b8000414041001070801c83c404009513495944420800400820340c08012004007400d00b000403109072590b14440740400700401c1400f02c038007400c0206040c0741c4641800d42c00340501c0b0484c0303a903c082c3d83c2094041c80d00c0171210b0318810403c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 387792284 1250 387791034 387791069
    0x60806011d1b030907050409080d0c090b070f080c0a05030403050d021f0e1c12180b010303080c070503040b03090d1701090f09050307030806030706030228110a03030204 74
    0x8059001a2107000308044400540c00741e1524010b8551024101384c90a00c42c000d00410140d0703c07803046500d8030f40f0440c8030341c2c0c0d80d10704404950140c0ba22a0201400e10030043c504000c840c0060b4129424070350b01540d6014412298a00300c40d80d405450030200482c480c400000c3e08003c0000002d0081e81d0003802128880052000100d036910141402d44a010800c1d0840da403252904c2d4000300b80303000418054418810144501c200d02c0612066100d0014511501403070401c5103601c00c0048840011210b0f01c41c100545d290a0340b240300601c402400c101880c030005100009590a941c0210351040c1038a558599405402040350403d0314040d12a00074131041100782e5000b03040c60400f400b000091560144c1c81c00600d4070092004001000100381c0303800c40740340010f90910040108611a8541517040c3c10040203043c0b0b050381e01c0d0440c40c1410310400c9400134940082c18010300c02605a4000f00c0388000e8181d044030348115000c2d80620600c2140d0fa94020140c06802610603a000217541400c03900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 387793534 1250 387792284 387792329
    0xf0303080c130330120b040209030a0201081e190c05030907030b0903040e01090c1e3207060614010311042306040e0f071d0f0102010e0106080601 64
    0x401d410b114414800410400c000007001200e0003c00e0b2001508801808000b8101d004a598500188180010302e40e140c1032107140107a20585d4607031b010075030f0304504200303881000c01d950f181c1d9540e020381800048400100d03041d100b11900c284810402d54402024206505040c2c0c0003032000516056481c00c0502c200b560034816000d030b138800d0034041e00030008240355440d900c50210b40a003c242d243c3c04100300101c2d60004a00400c1d0090103180c0d000115038080b40d80c02001c10716214a100d10004095035035104203940009003951001d0504991082c00c881d00b084403c0d640c13182c0000c0341740c0c190040b0384075091003900d5100508407000c0c905010016042c000044088898882d200a8800300c04d0005010014160f081800f22182c1c07440366002c103000c40320005200d90065401082d55000b0001085000200d454040b50010810304125105101c03070800c06060b1610b04403100e0180c003c0c0141c03400c00e40e100b500440d81c2c0d01c0e60a0020810300ea2242c070010345551017401100f1000910714842c401c482c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 387794784 1250 387793534 387793537
    0xa1403010b040e1905010b06070302070e0a05070507080d1409030c010c0912171605070807050d0209180a120e030708030f1207031e050118050403090902130306060f0303080c 76
    0x1503c005000d041501e25aa00079004810f41c58000d8550759695603c0007600e4445000600ca0030f802600201031a515205801d00390140051960307034000c2c149000d0040c0c41d90044181ea815a501c0f4030404d1301c03403541001e2200182071400d0700c0349205200c0b00c1403160000000c0028422031406400902242d44a608181c03809403541c80f400d203030800e400403190041580001e10001d0310b181010382c00d01d08103050380c01f11141542d250382035826070010101082900005c0000c10000c02c415180c0350700f603810540002e180c1000c014540c070580b0100d2404900d0840081c02070800c181c0cad000c6564050380342440801000d00c1c04c8000c81c0380c000e20801202081c5140c000050310651940d01078841e141c0800b03035030b0036840c0031000340400007407546070750b80c0e0740c90b46213601c1c500543c01030440301c0040c0c40d41c9400c0e10020990a4905445801c030714200030300c404254081205415140001805039440d01240a42c83c0784200b40d80c4040d001529004002c1a400c40d40782c0a903048a020341c0e10008113890341400f00300c20703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 387796034 1250 387794784 387794801
    0xa0302071e020108070e01110604080c070e06010518040b1905130908030103060b0d060c050306010813050a021e040e010219050c1b13140610020d09140604050a1403010b04 75
    0x201e4040c00c00100041d11030706c4d85070f0342100185003991140e00120960703441c00806407021910f039540400d079211800400c00080e80180648400c011050030700300c0010308103214a6403940d22640d2100311400c0d0720340b40c1c0d170004c00030520003910718040d00100505030741e810b00b580d0144030f21a542c5d408130880400349038019043d40c00d4020705100d181d64039541c0c1e0540206191760f481600300e03a0040b07403800400c0c040d00c182d08030281d00f500d0729652803400704c0c0010103c0c031001780454909011080c01300301280700055440922541a03458216050070706542d10902111052101d90040c20140c2c1d6110620041d000f07030000440502e0b4200c500c001451065500c1e0282c15120061584030424450840c5004a600705200c28040c01035110342091125800c2950294111200341803084002d000c80c509140d001c54a21060500c082c0502588016000741841c1a5100d103226021040d006c48000b9603a0a08a9004150061921655640e1698115505441c64101c80c0c42546004801d11903401e150042506 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387797284 1250 387796034 387796037
    0x10b1201090f06081005011a07050a260a120b090c0304032105011514040b180613030f06060905040f02040216020910080616021e010b03030a0302071e0201 68
    0x242a801c0580040c02089090b081005054544100190782c01c014010401c106200708170120384d542c101221200c10004000340400036090030005000840c0c404118051030640c0492500e000d00d40e0503044505402c1c0c0880a907070403060008108010b0307608005034100e54180c025050003040814010460b5011003114008440401040000e0000c0c6c801c48030340c040600d0300d01c880243e43c004400800c0c1120003d070041c403401c0b4030740b190041e5155040100d074441d81400440c11440c0904107038001e00d090062040d070345910901a076002c0c0c203e40d540320680d81d807410500f1403c1d100ca60303a8288103403150201030381503d8040c5030007404a07170300c8a01d010360740c401c540000302030b100d4076907550038000254131204801e0b0b09601d1900c11000140d645000850248400700051b942c040c0c109800c60b400c0c070030301a0081c1510414942001c68140d0042029080890154801480441c14a810382c2c050401180714642c1800002000844c0c5501076010382030f501e01030b0000c1d1802440c4040b1084500280030030103130 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 387798534 1250 387797284 387797317
    0x6080109052206020d0f02040e0a05090706030e0f0307080a18080c13090b07110c01181a0705060c0301030c08060402030c13090c03080c0d2a080903100b0108010b 71
    0x2e070240c0014080590544205030061030408211507190466880c0c5000c0d407501500017030104010307860010880e4028412080c20032007410308c81401e6548891521584d03050580f0b5801442811303d0900c0840c540301203800c2030380d50710120303031600107400d80c41040100041026101a000c4000a041440d01500d000304c00070040c0200c3c242c1009445101c911040746002c0d240d0a8520006201d03201c0036000300e10688594070410104c3c2941401d00d0002031f00c1504010454603126580f0780550f440a086410281032900d200c000172008102c10f1040c00d102902c180309120030700a030302007450025030480703000c0c088800c1f000d629100340c2a19400261000780d415402040b84e03038881c2c91300c040703594031300140c4500010b5032041a550301c94220030150700903142058081a900680b1900380940404804036181a81001d0500c1f400604050030001005410601c1960918100240d49048030300e0002d004045980c2c90140880d01c0c00600000850705001500c28800010244c6010060b500305841c81c0103200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 387799784 1250 387798534 387798571
    0x201090e0c0a050d0f14070207120b0103140a0f0302150f0103111909060f17061b0702060d14180304050105042310050309010e07060507120908060a060608010905 71
    0xf1691500b104880741c0e01c040e41c03000c1e010b50750413680c0714403800c14403e01c0a0b81e1044c42d00201c042e041203036030303405440610003260503440041d50b1080c0c01410740c0d0780900c01008044500c0600f41c580850444010541c01c0c80c1c2078400241900080d480319802031680b419200c555a21114080c4400c00b84030040640f10300711900221841e01018115021002e0b00080c0000f5583d24214015a4801da100380c5141440345802c3c41612f44117261000d41a28540c0148104c0c140f2604a503c046460170148a01240c04a05501150303683d104a1f00794410355a024400144892840c003215035050b66408000500c158400006078030100030303601141c40585501c1d00303181c5421000e80c8612004204000e00340110311500308613503209511000c490341156183c0345c403031428507030160845039907100c01840c0368044981000840c0d4002c080381d00e000c0e40160600c070565031040041d40e0200503034000900f540030790f00800c840b4182d03e50200045804607035a0301c48d1666903034211001c4030010b850220b0700d40c030550400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 387801034 1250 387799784 387799787
    0xf03060906010e0a0f060e0a0303140708073f0815060408060906090d020307020607061113090f0f060503030d02030c1603201506090903070206160201090e0c0a 70
    0x20a078003a0060610b4001c240080000803030302c00c50341d00a440011013400302403103001e40c00035a603040d14409a803014103039411614043c2143c0711040d02040c40040c001100e4041000e1a810ba0354926882404100749040b846072800712450500e1b41881d00d90300e02e4800542440041302801a8840300c1c0e118080680c4490b001c0036004000400803a030003081c02c04c0001001041041114441e46400d0040d243c40c0c1844001c2c3d50801c20f5180404085500a21080000d603139504120b4520a52203030001400a200c1c507401040f9010b004001544074528810009688403190880c149001e80c0310400c02600b28503046000485181d4000c0c3d682561050041050758000d9500030f40c4c0140342e214140b810195000030243d48003446840860004140c40204209820060700d44a02201c540c0081d124501c645035200201c5d100c0144038900c94840d26010500d0502d05004407011245c01034061a5034040703944c000c043d0042848000c9000441964001400e08125080b0034060003070341c88803a01e4071521400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 387802284 1250 387801034 387801049
    0x1413050103180c151107060909051302040e0105040b0a1503060507090806040c06020607050901050a120b04020d0e0601140105071101140403030c030e030325110a12060605060f0306 79
    0xb081c0750042e501c15103050200b180000c2c214014558448410000d210110008010030800610100c60354065a0284011034200406034141c0c0c1416100149542d6069180078050b0040100a5000303407502e050116100c406400c0b407449a03008220701402038451009581c11107540c184200301602811a040c400650260040b641010551a00c400003030b448241040c10400c081d0b0b4101d400e5580040100103454050280303660052032828503500300818000060242e2250340d00c0c10702003103540300d4149842103140e0b00c04018000054005c54454507402d444c40000c0a2001c200c95141c031030040001110345985043c2c00c20b901044c0e550a0900303c031903451100650006824506210300f02c2c501c0710f02c520a103405400154042d50343c0c260321600724100030f00038030f54103480303c2c0c083d8000700300040504d1000703103001100c100440d02c2c0c0e684048450a290982c904800c02d042d07802121008001440542007000500490040c0c0f8108072540d80c030820013000d407180c0303003101854a10600000f0800d2600a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 387803534 1250 387802284 387802301
    0x50a0b0f030d230412031b030c0206130b0a05040501020c191211040c0e130903080112050c030709060e130b010302040c1112030a0e030c06040813090207060204061413050103 76
    0xc0560300c050211182c0d03070b41540c01603040581a5030385c2d5904002416844401e4024120706035546090034000c5440c0100010f80280c0d000c1d006100020300ba0500e00e8840700350b90b0003050b40d1040c0755211650b890008003650701910490b801442001042c0300c84c0c2c50030103280100e20042c040c20300842850810710340340d91580c603102525481d035035400d009016141d500482300703006200c0e81e8201001801e6030801a030042e0007191000703da458000c0340000242c0014409064440c0d100e07603001400c1e040d12b0f00c2d40c5030407482a4001e805025458001079040c0da03d0304043c1c241ea04442c0038030502ea40782d41c544000e61a0401e80034003101440001040981817941c0710002c2c0c09002d01d01040c0b03444404e41c51610782146400708a148420003c10401c8400b40307486441a407a0070400a1032402c40f2001d4000d40d90381d00030303002620124000458800846008600100904006809540341c1b043c5080c820001d40003440b419010514075044202c03250100300440f00901d50070421400114107100046000f00780c60b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 387804784 1250 387803534 387803567
    0xf030f1507091505030121030806060c03040305070b0d060b0c070303120209042a11150a06080f100c0e03030a0f0527150313030c02030a020d06050a0b0f030d 69
    0x600c408254501e81440f840c02c00c00759902c855540c0d502d0024000d05c000b114008502403191010307076000009a00400c1e80c0d4120324211040c9841e0540c581d0698114451988020510700c5450700010b080c1410302d003d00440a444038081000755a15013001905114280041d205600a01c100b48002405001c0102014811220050414080030045402c5511140700c1c114601c40c1d01c1503811540c0c0c203c5500b61071014140ca090035507505810805035448103404540c2241e0580000042e906101c103a220000801564085404800652200320703180c01d01c5079140545075003803981504c81e19000b12072400711a14060300841c50a26013110072120301d1051810141000020458041400720006003100300206a030741f0a140303c1c540c1000c11012035540080c44000100074402c01000c403464094850007a030305800d007840e03042901d200080c1000000503000303622240d070203082818070074140e000a2096800c43c00400843d0400ca0800a1428000400d0795156215415540700c0f980305400c00050500030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 387806034 1250 387804784 387804797
    0x1c050f07050c06010b0d140c0d1518020f0c0102040617090109080301050105130e01410909030c03070c290406110a020a0801020319060302090c030c070203070f050f030f1507 76
    0x910b0a6030032000095511107884030020071003271401c1410780704001880d0444103108a01d81e2070711840322580c1421095204029a000c1116014622104112413107107041000840d500e5441d440d000e403e410404a410030ba6400c034070b0000d81c41c21014400c4580c0c3e20f42003031801d800c6078604401190f0b168040c4404415056003020001000c080c1841d9480c007030401207140010041a0851a0b178000012190b049101c04040080d000c2c02440e07031341ca00700b61100680b003031011903803102c040e18910f12411001200510001840605000e420b000d070001341c030007180c11401c09054010022606040d684480003895500300404c11005020f0802c01a00001c40070940d450b890194000400103001903210303013056500041000207640b64460741c09040268580104021030858000c6181e40100510304098414000080b0340b140840030162500b040d03005044580721515041c81d801140b0807886500d0181004820700c09843c0b0b40458092039516503400113160403000800c2d58190b8440250525050200c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 387807284 1250 387806034 387806051
    0x3030a0218210d08310b0708060a080a030f200307080d0501080601030302100b04021612020601080102090607060c05070203070603050603070b0f0a0c02061c050f07050c06010b0d 78
    0x1501c0160084000d0500c501a0b0a04042c070480da0404460101e03641c1001651800c00c4030500c03150010440c5450446503001502d412400701a001090444004c0c069560300d800300315031142e014400300c0c4203040c2520b001a0541e580d09030150759424a6500034082444003600c11003052043c000c440d04141c044c680b6520007644000040d00b1940110700544129030001920004503003107014613401000700d40300070b004562460b103000352078170f1481d5418900d194841e030416580b030350389406865464124001811000b030442c6458203544805c40c00403c0580650000040c1074001803003655801a40a8420303031030b020300346c0c5d44c440041030004c44a0060000500c01c103005a101001400c0192071035803400100b07401d00c0000c00d0702c2d006940d848515488020400240d00b02102025180340080343e05001603802d900e440002c039a4051812085010354100210301d9542a00b50030480c003a015a0b01d000b2110b889200045445215005078040c4a81c0007034010005a60403000908014128000002e0b8400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 387808534 1250 387807284 387807289
    0x70b0a02060f0a02191806090b0a3e12180409060e0a0804031a06060f0901140a090906050a08030403021e0301150315060e130c080a12080906010803030a0218 69
    0x1141941c000000030f00840c4048a40710006c00c0a00140c07085081003000c0a180c005078141a20440f86440200100340395020210a048401c080c2048050b402e0000084c0f4003c074944031450010401070003c0c407a1846c42d215009041c2c08864801041003c46002c011403203080c000940034244c000c4455035543d14903030b00c503214280308626043d440f8540c2e075a0703540d02d5400c00880500313000070150794000c950010300482c0ea5509041303e01c440380340f0400384d0302c4030481c0c00184c5206000034112030b081d90000415101360741c2d000d50a5000da507054201044000d44503814805440518040d01c03440750710801050015107403881010030501c01c2401c00400d90302c1910007081c00c0d1900701516060317440842a00b4410030170b216109120308400d008003001141c0c540801000341400181900b00002c030b0f0095002d0511260681c000c000c0c001d044100d889129442c9058002d511b4000e602e00d0000e5524030229805510200e0824100c6407c0002141141c980842c0c01d4001e61083d001c10811240e0400200b034982c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 387809784 1250 387808534 387808567
    0xa05060106050702120606090a0f14040318080102070f060e0a060204030507051305040c03170f040807150507081804020702031606030f0b0d0b060a030803010801020a02070b0a02060f0a02 82
    0x3006690b44494035000a80305214100009544440f03407500140204080c98403030491070781c1e01142911010411901c900018030003030860080c200f407881d181a04001c18590000784602602104d600c030130010075900c8241c0d600700d00030604014191130031a010b00021030184d03004140c541508a068414540303080e0784607800c90348294804c0721190014082040b6524202c140d4210305a0300e800d0074003451405a5600040f40031601000348252101a42810f62a04100a840c032801c01191040d58454544240c1541c0e008117100300c0d500e4001c442c0c0a2120584243d083e1a0a81d90002d0f05901f090b00304c00019810000304184030380c00603804c4c044140176a0f4200020610000c030034110101050401c40020141d0f1200d514480c109420042c0310034a940302c0c3c00701030750700b80d400080048043c1c517800c00155292480b40c1c00549580404030000c9a0724a06500411105540b502102c10803940c5118842080c015601080c025820040008560440300c4489070f601c8002040d0051405404a289040700d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 387811034 1250 387809784 387809789
    0x120f0303040c0f0923040305040b070c050411070201120f020f070b0a05010603050c0913181415070f03090609150204060306230d03030e07030f02041521050a050601 72
    0x42e90032034400c00c46600e0101e4078002134030709240e06110100c1c8040490780e4180044a10807419a9200d00050500d88180e054901500600100541c6e038000c80c20040103040050041ca88100e103000038014a00010703404a402060b81a11241d07500c030f103c00340d41c000405001140d0203030340c0e03000c1000c000d526414600819807144100e0300f000c2a410101400c50490302d050b0040f406061034171050060700030504040c1d8a00310001c60f905802d00c10301044000190002c5004103032441c41740705089040086014900400301003060440d070707002c1041c0c08001240c00042d0f414001040c00c080090807034038829080703400349500960012402440b0782ea40d040c1180301e10250559540d80c08642800800c2e80b50040c44d00038074462543c80809000c4866041000c4d079102080fa21412806a44400b01402071f0400c05070202c0000940360000e83d2400c0a15003686020012446180781001098a0451001c00c0505591401c0031070441030b0310ba00301c440101410804180c6181c4181105100040d4040014601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 387812284 1250 387811034 387811043
    0xa0203060106120b01030501051516081306021209090a050405030c07060207090e0106080607050313140706030b1206011e0306050c0408010c050301080606040504140a03200a0f02120f030304 83
    0x105000c3e24640c0d40446010043d410f0405080000401440da28510580c0b01c10741102240b580e034100e282c100c4400e05003003000041c40f4407000301b00046034600d40d25104080361055000e036400d95000741170328240b41c410600c0203a07106594001248074034039681d02c190340c418802c0381240c0c54036503404405460981c1e998000d0006074041501030018100a008040c1089000f000a00c416401c1001c06030700c648000300140304000700480098030240b85140c441c036205401030b400d410700d2050f40075000d8803070400b805940003081c1412200f6020313007016588400e14100e00d002905031642401c1700700e41a100007000440d11070340b0a501c003002050ba641314076409011008100d5a9a5141c54185030035140944200701c00d2040a0004004207035010814903030101003140c1c0091a55603500d442039001d5441d028080300d603c10303544040209604098011070300e910640e1040c011050440c40141d81c2d0315014001007110145030290001818681d21006160100b002038961070848400254519001283c0554 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 387813534 1250 387812284 387812297
    0x4020d050a0f030201060f0308071106370503010b0d0504060222030b01080304030507170a0c06020c010806040507051803030706050c030a05010b0a0504060e040b030615040614010c080c0a0203060106 87
    0x40c201134091150900a010482d403c602c06491038a4444050040da81c000c2c00c40001741c0100c1d0481d0340c0d594104d03001c0c100c1e204280815419180c01060006a24440d0710320308107220000010b58600500a07039048030708800b406440d20403122058005040040d0040321000d03002d1190341c0d20403100c42141c4070711840f02c41e403140031640f030341c1080b8601e85010790090000b0313081004240080b800114454068071000c0044424001815aa080c86c1400d0380d840640b0005004c1000718026a0108140c401c1300d0091740e44549130744aa1041100b220411303a87c46006c40c100304038404032420603821035141160024282d9040003810f45884c0c1c05d50b0011203000d44219400020046039040e42d02c5000c5c09000180141c50812550300c002800ba0f2045000d0b0100f0321105441c03190140d990780d080120b4516000c3d051790000e0401031044c10303e12a80002807441a401d00c0781c0840d0765442c12000742200030050303440c051a5042d541742c80c1110703072204001c981c4500641070f250025072001c2086e42d00824140c0c0c0c0742c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 387814784 1250 387813534 387813563
    0x1436041802010306090216140c040c05040603050711100f1e0501150f090b0c011e020405041a06092e0c02042403021002101a09010e041a04020d050a 65
    0x6040340c604d5080080d0491041c00300d421f00310aa003a03002c6540d50b01120480015080a030350f523144c000c0c4c16100c103512500300228480f00c5540413002c3c100b100c0c816103080c00b050301ca0b01000d48591006031442c00407075000001c0508140c2250b040070b42c0030140b020001910a50400301e04070340f0b40501c0b902101454075580100b220440800428003a9080b270700c1c01c44501c5510800003866092280f058444451001c05c1c0b100b42c5070802e5100c205805600410202c03408007070045c0501075000341c40350500c5949050301d082e2028100320284c181001c0024026442e00b00024100003103115078114034401c1c4911282001024a07411411065017a41610ba42950f0001d074410481519503c40040d80d5054061904541d00c644160b0b04400340c0b5411660a450922010703000ca00e002101c0042e41c0c81c850812400710203c000065400c14850410340d0785507841da0329140040c41000c814be8000340446050414044c040f040c6007085074009200030406410000c1c6620b07590300e00058040c00359154119103401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 387816034 1250 387814784 387814787
    0x1104020c0a0c0e0f150f210d230f0a0c050303040b0406060b070302030d0c2a0c06020105190b01050729061c02040b0a050a0b0307143604180201 63
    0xc0c2e501100c00c58200016161028000c00d004ca078003000303140911750506e5225002d9891103282002d60310b030207007104a0b0625050384e8a580b01c1c0d0a1070680701250f0007000c080441d400c0b8541c0d02c104c044806002a1400d900c03041600800c3d803140048074100800442c803440010000e10007580254056108036001e4186414201c08441150303004401405081140400017034000c41500c1d002c0c400000300068a80912030251000002e0100d00c0300d80d0310404c80a10b0110143c0881c80d80e5060248043e64400354540506a088840507200101e03c1c0d000b034001c049107242d43d50440f00b41210107140c80c81c141402c5644a0010f0f008150410004529404d0000030f03440c2c140507501c1e40284111000990145102240800318031b01c4078029004a46941129505443d4030b50368200602c405000461260360710341c0c48000035002030715803000003170300f401c00980c8207010181518520280041802888402c92908001c2411814807240d030380c0014070340b102c0c0e0680d15441240c01145240359450045407140c0b00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 387817284 1250 387816034 387816059
    0xf0c051903200c0a09150b040b040303110304080604171207030506102c061c0e0f01200c190320011e050712020a031b0f08041104020c0a0c 61
    0x224400b01c0e9000002d1a0701a948514a0504884200c0d40c0040c000d10540700a0091713940c80d402100d0065400180050351044080041080740d020341e880010100c0443c840307507281d220b5445051402d912890106000ca020b40e407501000440e044511450b1000c0072041860840e8121082404241d540342002040d09000702c0120101215103000000c6401d007014002000e8207030f1064141301640c0ca000444a5283c010881d490340751044142010240c030824240c020f0b041c0c40103885c0082c010105200c5080c1414004d00041c1c0300e50040b04102074083e110000c3c2c407070300056050700301d030b01c641800d01e106815129100c460860180d41c40c00c035082d101d0202c20030503c1c0240c2e12069140c1c5082c2609100400c60f1071070b12280c07040210049000d48032804111840b003112a068400f07244001264000e80e1b80560103c000c90103581c01d0055030311000c07141901c42c40b00416200000c60b91240000300003c2c95140031070500c040040005041140701c408842c078220004030704482441e0200006c0c043c04040da403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 387818534 1250 387817284 387817337
    0x1330f0806060a09090b1518041d0a06020a05070b150a08070e010b0a0507051b0a0b0a080414070f0b12010503060405070b030405101802010801050f010f0c051903 71
    0x40b00b0600d003181c11040204400340c03a1003001400c903580e801c529803999072480c4c04482c035402d4070b882035260340c0400c4401d11040126241c41c0c0c841c2d032030f0104140c2011002921500300d0b8646a001c0c0c0306e110b08a454000103503124080940400801700f04140c000340703008d119180609180c0d090011801640c400344180303068650060030355030740031140400c100b440f1480442c1c15250840c0506071621171200b004d44040c0a504001000d9003c5c1000c01741d0080300d500d10145150008840c01140c1c95a00d01d21007004e0f214001c1c0d044001800400010040380c0b40801b0200d03812007070001c50724900e42d03684401413122619013051805440c0041c1c4000034445043c0701c0c0d40940811405031695080c1a500c1e82e603520441d01c2141c450a60210001c1c040c000c0a101101c2c54a030181018840000100110381080c8034448007203000c41c40801c0082118200402040c44403036068481c3d20032650814016a103100ba00e600c21207403486404918100f03100d0110034221003510070703100e05038200001585c50b5506036a01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 387819784 1250 387818534 387818539
    0x40f080a0827190c090c081b030103030e011803080a02240c040302090411040606030605130b090606160807030509010206070c0f111c080405151201330f0806 69
    0x8180c90050700402d040005040081124070600f4240c54891a810b14030750080c10b00c0c0d45001ca51a80164002c1701e901d10401100403000e01c0f41480341da401003e400280009400500c441031000c04c84e501072810001d41000b81541d032040e02d6034a5a5090395039104070002c00041e0000310040031005030640c0a44012021440401624a400d5010500d40c1c000c52001a1182e5440d001150501a08050308034480030042c000b440525140c541c06005059140318146c003807a042218201030980e10700c651480305170001c080421a0302d62404001c1c1e070f50442032481000000760480100044e40c484014100c040c0b20b40c50b85ea450b02400000a81001c81c0100001c0a00c800f10482d000092140c806030805180d001c4000320342e28441c03402090204000191f10f51f5034040c00714402d0107000240300604100c5900711503410240004007a8001c2600a0068240c1d504a1610040c440b20740302007840c02c803803850b04100780010012031100b16242c000612200d4081040c10f030701c0c076114550107000d603035222406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 387821034 1250 387819784 387819841
    0x903161e230309032d0d2d0f0513091a09010e040b062e030501031101020a080702040209061201120b0c0f09120f070617091c08040f080a08 61
    0x50901182c0c5076020407501c0002c058020000080b09800d417400c5059201c0764008032640901000e00103031082e08100c81d13101200108085020081a1090b92900c4040260fa1409002e00611205a8950f0418600088000012000421102054480c0910f4000c7c6004c15024100200c0e051003c0400306800060710464818100000701c3c16458480f500b20340103940e00e07016540c100041001c1c0d901c0e01c2480614900785804517114840c0e25400a6058030b003e00c442551003400c40006a9540115041c000c055500604c00d00015240c907502600809101400d13051411404540c0d00e40003910036088518035240d00341c0d554082c0503000400300d030f008902c2c00040e40740410b42070049031a80a0441054411001e9000d03c0046450078400002a850001e048507007054480c0700c080c28190300d8588041820703584c00006641800b0001d151244108001d0800305c5052845508843c155401007044d00c1b14500700c8210030004102000400304c4211994401045060201111409020340c0350040c00c000c01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 387822284 1250 387821034 387821047
    0x19140a0c03060317070501140a1d010c021905070e090307050d020303010e01050d0302070b030c04061706060406112505030d080f070f0c0501061d0f0903161e2303 71
    0x441d907941c80e110320b44c0c1e06103103503d455040c0781050142030540c00c0c0b0801d000b141028801900c005400c55000382d04000e03042c4140c109030702c1c2868200c8850910141c0180d01c4069054003801c0800c1580d2180c50180c0b0640d800340b0b464101d0f0402c0044243c400324802d6000086d40e5043c44803e004010910074944050361441d450b054044107619010b00a41c1c0c450402002d1550405000b0007040d0010720320307105031765100c2c0f80c903000c03011103a046813085002294260003000844201d104c419481598020084e504040c1420011940c0d400c480000003d1407003500e0303104000810031500291161512540140712034144030a060500f0710250341c3c44207204402060000840c046404e040c2c1c08082071400d03d58042d1203d804940c1c007079824030040d1055190400204070103c3e60031112103031032150b0141c0401510380c0d1070020002c0b001210352141c0d9401c107005003960440c040022071070450040c80b0403280660404006c41c01140034940032076151080e0070b6403220034141c15081c2120105440e02850801d074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 387823534 1250 387822284 387822293
    0xf040b071d040f150608100b040815040c0315050a0c03020c0c0f010c06020711030601081203011406040305030a0e0103232d150306060d0f030819140a0c030603 70
    0x1629a401d84501e45445681030600c02652002c0d402141d8081c410f1034490740d4120203000c6a0b015900d040c00074120500200302210322004640495107a10018000c01e40d114a102607540000f4000300d484903900c0c000000420070910034019040701e0000b0008590800c003110804945000a59106050060000d0541c0382c00206810160100998103402c6034101d00700122501313006600000e142501c042a05024400c415002003100802581220b08603601c801d40540e803000304100842c00d0400410051056990b13903112a554220054005401c180c0c80e580d406046803c07004900300004c0103161095940d40c0c0c10700a40d06100390000881c541b0045e5016002503400004107040a010071101c5401c50340c000ea0411091000135008411141b41494101a485901c81e540e800307101e44500008603805142c41b541039000c40340e210101094802040d50b041e6141400189940c0c4922100c00c421510807d030f50040042c0c1030324080001c01c081c60f0241c41c44044401c1c4070409000c15140100c1480050f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 387824784 1250 387823534 387823577
    0x90a090c1d130504030e04020a0e0f03160b1e0705010212060616111c050a03030f05220528170a17040c0b04090501060e030f0c190306050f040b07 64
    0x142c054040c04070320742e6218141640c0410f1309004194000d4400110403040d2548070240c408850000c884210040c0540c400f0956200700c0301d0403401d00340d0720140c410040000720741e009108983c403039010307131800c94a1307000408880e400054003501c0306d0350009035240c50340d00c481000660042c811038619007404540c0c1b29502507142404ac00800328002c1413101180e5988021082450f042030b0b4000e07085131401440c0c0281c079441c002030304a0120341001441012082240038440c03049a00240d60040312010b124500c1e220f2012407001d88450040e4801c640d000d01c458444038002c1101c82d292034400c0301c894a07102c0c109040c001c04c180d180700c80622218044552115a40c030071280300021300d080e641c036217040c9040c4080290380082c150810002d4006152442d03604140c2c102c070f1041d2101d0704402450024540c0740c00110303407031303002c26009600110114945210100d00035900e402d0f0340701110f512595850103c6100f074520194030400c1104100070170184080d92640200e00e840c08200c6d1140416990810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 387826034 1250 387824784 387824809
    0x140a0506040c08130309240912120e040b13150b070809040b030304080604050115080115050405070c05030c01020702090709060207060f110619180b040206090303090a090c1d 76
    0x1022444400c4805040c440c200c070101400e4a40c130003076580c6c030f8002c0b645403146002c854130341c002c0740b0080000140c5a0245051003a014ac0020204042d492420021905542e102c18a55800307513960564503001e89540001d085078010600000651a074107419140e640b50848e80080c2880408220010000f00f030f08099444041d400c1ea00460321402100009043d80544c1e00958214400d910030001072140540140d0b04400a040d0310210090711342c140a0700b614503601d586a080c1d81c080314108031500701640001d070b100e40240381144c40303d0019900c00b829030303000300c030300d8030441c0e4021480070207500c3c10501d095084a40c904108244901c0c014020707488008031700c01d010078003000400380036045002d003001041001a1100351000c81ca411150020004828802d040b034042c0b0b070485d80c50029450114460b240307508807003400b183e41e4482d800c01041d9840280495014041400b00d22202c0d154003220308050128190701064500c8102d0006107510a0305c0801c1895401c00b440b040c40304c1d200c401e180c090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 387827284 1250 387826034 387826051
    0x609050f04020f070c060e010f08160201020f1209160503060a0b0d08030403020d110d1b02030f010c020604110603070e0904031119051b010905061804140a0506040c08 73
    0x540803180310014000b4007403c0c4002c0441e480000c3c1c107404200c02c030501c240513606d0b140c03142c40840b80d0b0900111100da44c0c0300256008035034080d000c220351752210002072161042910016107030210914071822503400c5441080e280c0c840c0b260034000446024400c800282c190044560451843e0000080d40c40001815a02d181681c456000744152a00b4940e10441d0790040b08440d42c0e420140f40095840b50b54041100000d81c41c1c42c2541c4d9400b00c045030845c2601115a52008030b1035600c0c0440d055084000c3c400c03030741403140e580255194517003170068404c0904030350041c1210385401d05045140150410b04248030b40c900308104001250000c521031122b6800781c44501c01980c4900c0d09031190204000c50f18054868031050300e2030a03424000000b4403e1040341038400350b0700324103010110b0201c810400f5011071a101e400b03000c50b052800141c0380c003120442a000842800300d000c9400ca03105140d05420b0b00707504030100040390b401d41c0030352a0070aa05480c1004210700c551001814020054940382 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 387828534 1250 387827284 387827299
    0x1603050313020415080f0d200f060717090a020109091a0d0b01330e0d15060521060103110d140a0506070f0e0105030a0204230108010f060905 62
    0x3040c14449840000704a036001e0410004951000d44d43e01d20b43d00d2a208085042c0324111100058000c00714208a21999640300c20043d1016000d00c0d2020300020461940b081c400c4180002007403808015032801103c240e02e5842c14001503a151040c0c03104000c1c401a0070745d010401c02c6006076130090310403084813070106000949c00311161501d90104088000c6640c4613150190001c14880b41c038000604030f03802d03540e0316400e0411440700ca2103201903100001002002c5035070444044c0b0300038800b10342c1c1000c000b04490090035a541e90400038110201a402955035550070510450030014181c51040034140d0000f81400400007002e07a9440050200034800d40840c5106041364445205d900c681591241c0b02e8186c3e000009044e0340d640c20030303101c20754841c03180d840401c603210f001d01020b0008440b1075407696082c0360b001e4015140d6520140c84140c0082d82044005a181030301400e1a08040c2200041c440c1d84503148001460810103030021050012068000c010307198002a02c5812a8000d45444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 387829784 1250 387828534 387828541
    0xa03020a050412110907030e0303060d02030a051c09050a080d0f0509100c0c09020301150323040807020102070f21020a030803010f030c06030501060c080334020c0616030503 76
    0x4079800e0196600c48100c00207842860700c104061403a079207020140a0ba51048160394621045058030486540c0700005c1c1c1040002c50801e00303004810500311800601154a020102c0c0e840516244040640c3c00d11450f903440203268459105015038010310084a001f0896810054107a4a0790782c842c0c400014001140200c1550a003d481035803500000101a80030280b030300d030b001406402e4003403001c48202144180c04a00300d85240301340c9050301c5000502c9004203d150707038150700500c0c103071400c0c442480b0750002d501c0484d5000d03a08035125a109461007078445031140b001910300384154004240703440c49100c040c4512011100500fc5650825091f603d04000c01e00100b0311104560f000544201c80000011074002072560342501200e22400a00041e986d940724214111107080c090300d0005200003101c000071500350400b41d0f8001e40350303410703a003180d080a81e10300c40100c0c00c00740e04402d0700013a450f2621000d40c0502400d503075000280e68041c41d108030440d01d810420802a00102030250101c0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 387831034 1250 387829784 387829787
    0x40602010b0145150809031303080f04030b040609020f0f1e120105100f09090302030f030c09181602060606040e071106010815010605070215030c0d0f021809010b0a03020a 75
    0x188803800000c032821180ca030307407200082e8001104c034041c0c1c0781c041039140740414609200082100e22410304413500841c607d0840c1c3d26081580d0000034800d0f1070082c01d100200104540101c842e025074480c0718002002d510700d206000d01d56401142c401e10a0090710f10318180c40e10741481682110012115420507007510710001807400d2050600705d450356191904201001421608510644901c2082000023680e12202c2c1400e07158400c40040045c0c0040c001000020b620501968100780510b11440c01c04505101180b550600148031340540704c0300c401404a284012070322042e85480b940702600c1c01d454454041003e80c89240720b004c1807641d41000255000e4403404003000d0300b80c0041305854140d41d407008400d80e07480c04828110303800411000001215070181c4111141d06902405e02c0c2584080c509540085801c002d10500c81d03480c0811060051000070303c030f0307d0003020143c400180c1720010785241e603070b00802070054507006003070380c1005000d040312002c10b0720100c00c0580b80241c2ea9a100080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 387832284 1250 387831034 387831137
    0x60806030f03040f08060c07030e0f01110307030306240507080901260105010306060516020d0302010e0312041502070807110a17061501090b090909160803040602010b01 74
    0x812407500000c500414011080c00d40c1004880305241100c4064a50200d0302040d445400b000401081c00640003840c41d0a1024038880c88240505010078800503010965095a010341002c600083d13407580c1c28042c0c0d080c83c03013040c415075100500e06c01c010f94803100c000d0503900c11030b0740c0581a90408243c001c81c90303214044014030085103c4150f140c905803085c0c600803080f001c3c003410340400c0c1060340220303050b44140281c5100e8002180c0300d50680340ea0f07409010034903c0c15001a01103548038408007c1c0c82408200a000824508501040764581400c0400090740a2780e00401201c3c0100081c8012400040503562015044840ba066415a501c001250582194081c40300030840c0b8401d02e01094000c0b0b01d5038030030040089416003007000400119007d4040c1d0003540c0e0703002402e00580c0ca030350404040181e404907031001120b0313580b0701d0410000b03200d04c8030b54400d2095610006007409181d0b428010300c05010400e080c070761401d0a4010012640c6041d0810821b001207046c42c90381000f03022002d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 387833534 1250 387832284 387832303
    0x1704020f03120a0e011707120e01020c030d0b040b0102030a051602090103120e0f03030d090501061e1e06050304060b060d0c0806011403010e1501052203060c051306080603 75
    0x40441d005004150071948540d002401c41c240071815013140540f29500400c0400c20440701c40065158a6881c050203644241c81c003002450015500e0a036080b04107400d10003040110184402140c81d101000303401000e40b080803031064003e5003000038480890760004152141d000d41810401e440d50703c0a180520381101450340603502c41440301c00002840700d14198030150103455640e800c1c241501c40280400311b00348190542d007680c070402500c5520003240e030002000c14454400803464542e1107405800c1c1640030f00c4440b00440e1400da00300002c1c4840d01000a0401480d08250010380c50541d0161450200400c00707003c0c40d490301c40800d100d5440320121131800000c11800c0084041001c00141580030485e40f01d130114002038003110301d40310403005a038121021018481496586d6142c0a00c0200040e0145030500c5400e100b000b00190082c0280300303a8007004081c01c00b0480c07440c00e2860560b4861710044051140810011183d8074213000d690040c0c03200c0e03090038801911360001081c680207114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 387834784 1250 387833534 387833539
    0xb180102150f010302011403041104020d0f0504110109061e05130b070f150905120d0605090c070501060f031a040507050a03050303160201020f03011403070e01060e030d050a1704020f 80
    0x400c1009107444240d07100c60f042e81e000b0781c0e500301d241e40c03103501c008040d11040d14007278011048003803022413518082d0018070340b03822902070105494418843c40300c180c6800355022946c540802646542d80d5a1154078100206050318202500c180d1900540c00101458402c9c0b0007007040c000b45403850340207185101e07001484403400302595118a42000d41ea2010442d60845262400040f030044022050103488449038104010f04106200c484c3c0200f2aa844001d81152581e118030700021203588018410384101d05240b080c50743c502083c6011401c6820359000080540310482d802c1c0f010550310a81680d00e134019941074034054466003002031505980740d00c6184d0100020a0101c01c00501201560141c20607404e0310300030005190091b0b00b40d008502c0c0f158100c0d8010300040250354005011a03003088000303403d461070300703413284000c0100711000d801c000041010040c59080b181810445401402d54510b0040e040c00c0c4c4101700101004a000054001c940443d00410250340c0c84480328041140b00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 387836034 1250 387834784 387834823
    0x50f0c21070201150608160c170307110f01051312020106090f0e120f0921011103070807090302130c020c030a0c0f0906290d090c080d02070b180102 65
    0x10700024041c20300381c1d220b02c581c3c4810100000b401800740c10941e0158070301040441070152404c5e0201e41103d60300700165215200041c400c42022911001503015481a80d00d800d891089100e08030314150211600c0561a8945820000320200c0007810300e0044d9400005241d01300f01144003280135203101e41040c0c00b90f034500310140c58140b000c3d9000c001c1c440d1125042c0d5100d42480c4d031080455001c0c000043d00460380800252816140c00c4075040c09042116248010042c49071601038219040701c0b030509541c8070000144403513160442152070340401140707480c007081800c55000c25040c81c901da001d440c240b921028154520350080c00340c1003820001030125104a03003503040560000d20548502c0041d040610707000b148403d0709004d50b40644000013500c07110310014240c0e0700c2c018140064032441c0d0744d0003403000e1002240c3e40d004030f809aa015150a004040c245240319041070341514004080d54000d0390200040c41164054586403000031014003a41190000140d00b00301030111a0758003581c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 387837284 1250 387836034 387836041
    0xd050a05060903090406080f0601091512030806040b030a0203121e0c0607180602030a080a0605040e070e01050414060d170a0801081908090f1c03020f060901050f0c21 73
    0x82c00000b4041c4400211070034400955038030300d03c903100d09501e1401490780d0807010040c0300403040358104070f0740c1d45519400720070036540c0c070320384c14034000d003903050440000c0d0584041c0841031502d4001d08050300c0b000c0780900803010842d0f0001ea0b4070003090701d4034a0114004190904075464a41c140c01c05e803500740c100342ea96414503001c800d8943c20b085400201251905000204041011080000b680d460b50029440c03e03c02641c16224100b0003040e0100881d280d040101d0030340c030346004020400c24520001c03c1c62504142202d0682001608054020f031b25080822899800070303528203400003419207414013490003908010242034141c404110030801c0008113494100e85c000e03042412140b4150a50b10a4085c0348001c0b090071207035613000f40c00d41e40706004480081c074001c2540008854000c0c00406000d0004e000310321000c0341c2c1c080c00e90150700184454442c1c544184141507014442000800c11703441c00c8852144121000350070300200305004500e500c40c080a5240b506802113203078021004070b24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 387838534 1250 387837284 387837301
    0x80703060207060f0e060406110409060303030c0809010c1d0604030204090c09060f0509070e240a0e0d021507050a06050a1a10080a0f0b0a0b091c050303060d050a0506 73
    0x40c04040b0460320546444401082001c0d43e2040610307103c03036038010b06019102d07900c603d4060141c1300c04940c0344032070070080020001c03641c0c4228001144203440205421406031005440b0a000620240c0183d0406115410041c0d200705c03c8280640950030081282e010356011600d1400b460f00300039007242c581f10b04541401310300094801281c94024042c05882e803502031203c11148a40308043d0031100703500218200341d010300300b1050046005000b200074403905c03130302d02e0b00841d80b9000e050b4135113440021503a610540c00101d0b600490811f440003942c40e0b0003503010841075034801210039600303403010484600700321003480311030b41181d089141484503003011840f02d402800f00b08003c0e0315488000207040002d0402c06802c200102ca1501c072182180d58800c0f40344080c010552540d03604507074810300060720b591890010341c00381c2408203003281ca0340103010920030300c0e00d207840000d46900d404e1091600001d00c00401c07240d000388103881401c4609494500107140a09601c2e0007001805003074200807400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 387839784 1250 387838534 387838537
    0x1a0d0903030920030a02010804051c11010b090903120417120a050106020109020a051018140a061b0f06230403030c050c07330c1505070807030e070807030602 69
    0x440c024620100c0c0f440c1c0d00d1054503ca0324402c140b664050304140003810140d07000c0d0f050703182d100e4010016900f58500a08840054910341c3c0c0d1004040740031402e2030314000209100b96175032000299021421420026409540c2c3e00842100448458101000604200c0c1c011520b01c2c54500391010940c4900000e8501e03035140c20100e6144070081d10308400014218814014040c3d09500a015051280c4c200760038080c4507000c50744e01d901131007000444a01070b8601811804001c01460305022001c1503c03108004280d00340f40d0180080200b10100b0364000d10142400301441035124401c8205050185044406000f0760001c007080414402140c42290ac2083c0a10340b155220795800c02c0340b903001a10640c0e240c013842204907403e500c0003100344902d003448170f00070040503500d41032140104078442507000f501818501039030004080307402c548104001c01048403141c1040c41c1e820300241c0350240c1c005008040c0141568105510303121040700005050140f1030103841d445044c0d86075aa11390a041019 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 387841034 1250 387839784 387839801
    0x501020c060703141303020c150304060c020a020310020d0b1e01091e060503041703010f0f0603022106040b04021305091005090c0d020c072c0702071a0d090303 70
    0x6004200000718814801c0c410b62100801c3c1181303031310903500c0384c14090b4036072180242e04a0942c070840480c40e1540e40c803007a0b100801e00c43c02504541e64581440c15405413405100107900399881460258010380c1c0100f03650205e56200800140c07200c0d030010302c0c800900418400c69070825140c0419542c2e12040b05101c5000d95400e0720360800c41655001d08024000350001e450b0103600d076070003090000701d104800440d00300e0b0041e08040c10960250807400c01a0b84280e0058204d20300080301002003c3c902108800105a82d00f0218103100704080d50384000380d60060040b01c1c0c000074000046082c0d03075a521889020801800454443c83c4040c844a00d18044d4003425216800381000215400c225120220558002401040d01034441d06d0380700c111500715442410140e5002d020a60254508003c0340300100b0705c4c1c440c003240161440c40700b2210442401d10901d05d01102e00200074506400040050440340f4150701d10304501e086c1e040340e2145000b00c40f02400c1c000e09200c03841c02415450f4100218 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 387842284 1250 387841034 387841057
    0x50108010e07060504060c050c0a08030712031a09090a050d0e131b050304020604120803190b100e03070308131706011404090809030a06090b13080f2203050102 70
    0x2465070784019940e540035501c14980040c90400c4280300c3e642c0b08029200461703100314111074500e46203000042d001081a003100d60160b20115006d003e211006046100c21074943c10204480043d41d41d442200010007242140192400004101150340400421852075042010b407113414083d014010503890411100c98481c80f07a02d04a580c100c11184103d02d034601061a05101800b01440f00303a03000d0308018820307680070800b4040050a0442c406030452414800c5841d0343d41da18100c00d40300b07010584d4002510282d480c0c4480d00c0c080b51101192040d00b07030741c64204502001c40c65800030785030400303d4000a207003003c0420700d0b014540b51010f00c01d00383e40c90b0141c11095488800d00159540c0e00034407542d0128003102100020b281070030b03400410054090311103d494170400c000442c0c90304100c010b08480007035850b1284400d04c001c8040d8140c1011003041c4580789200c1c2911400302c02c6c01102e05100c0070740000920b0b00d0703082c8050000030343c004680f04104c4903402d41c0c174200b290007500010041d04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 387843534 1250 387842284 387842291
    0x9090c03060311060a02060f070302071403130f0509150609030f0f0f030309060a0c0309020a1203031a0112020f090301060b31060c0302010e0102030a0f06212a0905010801 75
    0x50b09854114151713141401c203503006001daa942d090806408000143c5400c0c01e0550800ca241c020800c1001c142d044040000000e5948a88000b1a43c0552400c0c0d03000c26050f44400340117101c80e547d02d200144d084400b403100780304104002c40025581e8840c0d441c143e50315120302404030f19981d402195030306541c03280c0700c01c1d94144038102c0540c58880c402110b105099801403800030b2030400042e48000113805440c0b400040c17a0300d041d400328152075141d400c15080003460750100010190f01d0b005030030384148040b5081c0c9105103807d0010301040704005c03c80c5141e680114030101c10440708015a00c0d02c01d8001c009100e031580c0c500100060b5032141241240000c090500d030b8444032414220340680107200c0307008414252401c141150012007012023101155240c003810b0340c5007002400030b14000e1812440000b0301000e44188101107510030b42c08035104a40400190380306000340b40068440035080441c9019802c588074040c0300c0322a020b1100c40c01c11f00700a001050f00d0039a5446030341641c5a000c000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 387844784 1250 387843534 387843563
    0x7020904020f06130e130b07140906070b0901050a09110d021906031b030543030b0f0a05060904021c0501030803150f030604060e0f0a061505060a09050d0309090c030603 74
    0x100080c00c00c506d020b0030441800e004554540d11402501180041d4032034001c0c00c02c0707002c60004102d50b11480096414420403000c2c440c503001c00f88515904846400070401c000c440d66504c504071a1906441a845408010350007000c2d51145219102034440c40400d80c010f00c0d440342006802400d040f0035100340c2455105400044501a1103181c0c001c00384029801510f00030701d0030840f03039118111100c111003464030444180000e10301180e00700540150b200401c1c10000c02c400d10841c64a407600c458854040d04500b0441900c854084070403100b001e45005d41c0d1400741181d001514000c00b0204460986040000014480880003441c0a103c0c88078510b040340030194100710982c11000c40c00d6500d80c0042002c00c00280c113503840210a503d4400c01d56400159141d0b000313041c03140040301544c03610345403651400002c044500140180c00c04441c95070903e1024480280940b00a000303030b0380a131000c58201c2003418003e041c1c2030020604130b4018001504c044030020041c22481c07000b25000c04011400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 387846034 1250 387844784 387844801
    0x40b0a0207123c03020a0512070b0a09080f0c0303012402100b0a0f0314010f02030106120b0402070c1206050604020a12180803010602031201061407020904020f06130e 73
    0x1a5070200f904a851403c55544801440e281e00d40380300010341d80e4450000e2108040f160f201140031281e80240c020300024445424a1410b01421590700000c040040081c0c10004441c041059042150040c0009a5080b1807a0424051007141800400e2140c0411410348000c0008004c5043c1c801000100315070200d100c2510a81c08020303010500980c01c81c2a004d810b4034082d50200201039401841414081d90301c40110068038415001034800900c1c13901070402a04d024000c0c0c040d1383e9038086085156615115000b401c808000c400c04400c50b88951a038040c030382e45c90f01510410341d00b00580700c0c0400e43c1d4031203880c10b07207810740003c481603800c3c00c0018519152620907101c17820b8141c1c844800c07480c1f40708605001030007010043c4111a011407440000705800d24003550103460182c006694940b400c0456070034240c4140e01074001c2107100c1010951313503601c0a00340c0d41e000d541901c2c0c603e00307a100c0d4400608004a000040c84d0045000b041c02140702501c0310b10b9408030740100146e0b40803521128103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 387847284 1250 387846034 387846059
    0x10f06020718090c1505040602120406020a02010807031e0b10090b0a0c05100e010b0321190203090d0c170c0a050d020a080a11011e1e09080102040b0a0207 68
    0x1030744280b000902825040d60030795003082100911843c0b000c1100360302c03401c01c04c070800181030744200003a4000c20144515501080b072200340b1462000500e090914001c0d000356681c0c0404d000a041100c0034020400c41d50180e006240040d0034046004200104a40240d00a01943c103405204c0c0040e100d07002d200b0740c09841d901050741c03c41d0300258600704044809652003a00c070380c03003220303684030364503800398140a18403401088412490002c00c3d516158000c041c98040c101d2a4494450b690081030004400124201c030100040c00604000c0e1032540207042e820340c01401c81c11a02b004101d803c03001085000301c10042580c8400c11402440a020380803a541c5265440c0700c0390b000310540b40144158034049584441c80d0344003e2240e0708a03030b180e44200c0d00300690104c3c21200c1c00c00395035500b001c0d03680012054403251448a0380d0a64000000d20040003010740605510480c00d07041d00d80301c0c5482c86891807001a080c000001d6544940d2505c050a103980080c9100c0018011803e010555619210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 387848534 1250 387847284 387847289
    0x109021c030806120a020301090b3102012a050705010f050405061b0a02060a0314061002060a05180d020a0c0f0f060f0e0d0b040506060111100e0a08040e010f060207 72
    0x70b581c039819949103010300c408044200080b0301c0c244940302c090b8006a40034003562500724401d8505001d10708203602803000d0800700b2081548503015400c0c080804014100324410001d070240307880104501c2e540c03101c420f4070054400480b021802108214107018000034107030f0840b842070340e42ca03a01540640040710140194007680e640304204005206500d250041c001c910f0b42e132090306855004d080d686c0099050341c02001c030000807a13124516100c40d1165030300300341c1c3d10200030703500f0f4503003c01075540082d10f60790000c0c040402c00c1da032000403071490701d800740b41080303044449004c80d80340007003014020359a40c10000c0b0480709003198001c0481c81301b000f01d0800007180d058403080386000741031681c1950542400250300040004002d88100207998102c1c2001920303014920002a60401e4100107091000c018081c60502c220302001d040c03030010010364505444501d4000291990800f00402e04010310325101410010021501145140101c681141200e685070000c0a01e10303914101030303803039200c5403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 387849784 1250 387848534 387848537
    0x70305100611010f020c07140316050909010e120c0f1513050316061a09010614070c030212060919080409110d0e0601081b03030307051c0504050109021c03 68
    0x6100811125000b8088200002c02e01000030444c002054101412a04401141641c550060f03008010691003661000702d0284103801130100c0140c01c80600420800521816000700b4030b540001c1c8040d50290b1280d0a006051000d85509a0081080350141c3e0003c01d02c200f140d000e0480020741503500003d904041e0304445445c810555240b9560a00d00542c1001c00d4540d4002000350741800c00ea18110650200c0c440c40740051034110500d10850344800708003883e400b5150401c0140001c581050059014280c1d24004940d21403481c60700d07807480f10069000a400c150809020b10008002140c107612a0309000111206052007038000880f04e043c0440c05041e00b90b08000900c03411800350406a450f1404101c0c00d440d00b4580070301311044900e209151446904850014055408240040031a030100180300160300480c51380026101d1002074003c0c018031100090042d920004420003190f01011311008203c81c1c80c05040040c080c1807030510480c4146030841940542c0d4409070700504016806 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 387851034 1250 387849784 387849811
    0x301060e1513140403080705030f0103060b0d06150e090d08060120150a0605010212090d02040b060c01060521100b12030705070906140907080c070b070c0506070305 72
    0x700101c01c00d81c0340000344074981184080c00c2c040c421031294040d1018082c1c56041c691001e1925040040c00b42201030071000c2040000c2050109450035941c1c007906482d04008005007a454000008a01c5900e190000b0130075410408815210343c90805014201c501d03203140f15880307544501800d40c0303e0034141d1134100403a00039400700d200d5511a5030814054038412804000038071000c04880d141c19075112000003001e28040400c040c8601d5070154500804080c001058803400c4001d611105000c0c021640740582142c00b00c4005560719904120000c0c44082c00103a61410301461150113004140140c80c00744050a0801c0c000c8908070050388810a007200180c14613113240c004180103090300b0322541c0d500445245a140c0c51034414401064090301c584001c150f021301e442d0001c4c00365010f0341d001044901d01600c407400651900d45409500001070300e012402540c610001031054001c0c00006800c450409042189035031700801c1c1c41c40c6240c06041181d0059544400407001d030345040b100305250300301c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 387852284 1250 387851034 387851041
    0x61a070213020c0d1812230c0d030c1704080f0106060903030e04020c21130f05030d0f0306080a120201200409020a0302070b040c0501121406060a051303030e0f0301060e 74
    0x824002d04400a02c400b00085c1c0e4150b440c041d80480c8140c0410a89042501040000e5220f9025007120801c0311640041c120707480c10a0009280782001e01c1d0040c040c49144e0b1040001c1003050401c1100c1c00404001b1562147c1d215101c50f1750341e590f1040405410340c07803e400820803a005800c0354084991568401910a0140701848007a4000d407820050314410b40c3d186001c01504103070b110707000c4c00003626010f0701c5a041c442140c1c880304155106080d100d103010001d0280c2e0314003160001a0030101d08282d48078000c401412001403803031f80c1c07100c20180603000d01c1104208a1246151142109900030b01410311091490414964208813484400b90204000c03c800c40703103a00500600c1e5031311f05005062000a84807088001c0048604807906c44036500240527542c2c001900407031141c1a00d00811241c041c40006290035540608468402c046c0403071307400665481001280c040600c410004040141d0300e00e406014840d6104c0300030700c5a091581244450300341445107000b11344000d485090b240d00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 387853534 1250 387852284 387852287
    0x901050f030c09012408040809090402150703030f0c081303140f030406020a0311070c05010e0d0510061401021203160c02090907050103050703090b19061a070213020c0d 74
    0x1080001541d018069a84040295655050b4550081400403e910030085041012040c9540601c3c080c0c02400a960107020100d0510415108580000c3e02d004005413102d00024940b140f5041c90364500d4103000501004160381508803601d101e43c00c00f424881180391441c242c441400c122150175020601c03d41150109110303c81e124800410040307443c0c90242d00c25201040c651003200e00381c880940019a00b0b910560510844240b4020403a900c1c0c2400d15070303940c0300c80c80241881030a0401611170b040b0080740e544d50a01505055001044850225614800201400c031900c039032030416000607032948855002040e408030942c484d540c5507240d5914122205480080d50061108000c00c05d10202c2c0161250f0510b503014502400085c45582d01d03080005003501c00040040c010036080a1415000441d140901a0811842c2c5501d081003202006080010562688502e446a04911000301b011403200000c04c0ca90b4000d03180f50b4503a000601c01d020a078810800c44500070307481041d1003003540703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 387854784 1250 387853534 387853549
    0x506060d091401020a0c110a03030c0807030302040e13021011072106150315020f0a030c0c06020310050f1807050c010b1003020901080a110f070c0302030f06090f010b090105 76
    0x301d1051982090341e0b0944a00b00d402ca802104601e400300c0d80c2a0844806e0044030107480503881011104001c58604583d0001c001d0728030101c00030888507003c0341460415001c0e4050354041e05803047d08541c030703181c0307220703840b50503511507106034082d0140d52b00c400300c481d1062000d00480d900200c000c020b802d01e082c201c00c481132117000c040c0700001c4440b003800c0c0000d92180111003480100102c14484241182400080b101c000000390740d2552040041c0c1c0d1b01407081e138003a1a1041058100000c140d03440450680e00207501d2000109560310000800c4015030b10800d103003060f00e5040d100210050440340a0007807038021400c0701c1e80714910315030020f600b0910070002090211031210010688102c0800840c50043c040c40684010a80104000490b940e00a0791603070320840800d070038402204080b100e501c1610496051688581000032294103100b044031840380119800b40480c2c008143c402c401903142c02c026110100b043c000c07040300680c4050140075071504160014005003d17a4030703180401000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 387856034 1250 387854784 387854801
    0xc14030604110d1a01090912020f100e390103050f0a09030c1502091c031d0d0c1d07020303071d01030e030d1509021201030b04080702030706030b0a05040506060d 71
    0x4d1001243c15005003100c8400e5900030001c225020070514114a02480c0449080f16080c0840d80f02441503601c82c0000100c1d0000d1b8890f40c0130005403038401001d0b00b0306104582100107904204002003040301510094a4070400b45038155140303c003c030f110011816500c0070349200c90801d481001007441d14000e03902075546540f207070910b040690455900d40b03011700900642803056590104404a40d03003400010410f11411030711902041000e942c1d001342900c940e4001d654242c04104074880e000d503c0d00134400492036040780170341500c20b1b81c881c0c00680710069900c00701091120304002c605800e00001c1901d003d00c0c001d03111100c004400364010035100055801150403d40c0b641040b1454000c00e00003080002c1d0103510100e10302c1007400940c5080001c540c07007400c059104101c000030101c0c1203100d55054035400303004600c80b5141d034148400d46019070381c1c001e5807502610000044a91b05079101900c000005d481d6407102e640c1d0344d000c000442c0e4044890035080a02080a032840050991080e084c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 387857284 1250 387856034 387856043
    0x706080a0b010509090f01090501050927010b060f0408070905100306200c0607111f020702060d02031618030c0303080a151403120a02030415110a0c14030604110d 71
    0x24410305a0000340108804e81b030b0f5445c4191100b0042c0503d1849002d4a809402c040d44c40f90101d05001a21143c1142c044184250020f6aa92401440c0d08207402000b203070304004058a483d100300c99040c00d55684544242d07a018844e40e02c0009000c859800307094402d040c070b1403075515603600e9138592a0141c42607038900707107290020003011411100404e02400541c04214010b240c1d519044102030500241003492010316401090701c3c038101e0071052000e5010500d481c001580f02c90702c61022404a005005c2280c00844c000b0040011548408800c4c0c1c002a03031607660200364920001940103200c00d64000500700e44402030703041c00840d01451089400481c501c50004541324071401c043e9400b01282c0000c5034201d032980980f15580741c204001030301d0080707985075940703452600b01c0081d5891040e40b16034440803400c005e40b10786160190072040c1e00381e8480c200f580c0a44009141c2818440018002c01d0000c408000258115080005100744100d038450006074441021004202004c941d00c4002c65 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 387858534 1250 387857284 387857287
    0x909260f0d0209030c0d050c222a0509010e010516060906020a0f05090901150c0b070810090207030807110703050f010c020c1e1324050f030706080a0b0105 68
    0x46000c0e24000041c1595605000d005849000c08020035042c40342d00315110740305a120105501c0401c0c070100c0c4840320007404840622221810104d0440810b500c5501c40c44150314003400c01138952001c1c0040c428154540902ea6140c20b680c0c40c00356400e02a50728494002400207a803d86254000c0c0020526440b12641384031502429035030b100161264000c08540843d00400c00d00e01c41900600012100004e40c103110b402c11103035102090316035a0501c82d9142c005000300030b42c504503000c3c40403106450b0b0440c2e01d60126141c0754070080d084150a4400d4140c000300810000b402080901c2510311259042e84c7e04443c640f9900e01c2200c0d4010b00d41e07440d405601400c0000000111f0401c01840e601c1600000480c00d000e6008004e4140118911801d01850840c8264002110040e00c1031280c0541140c890417a80403540d200d0004104200d2003c003196002940e26464400500b07100040b2070301100c424806001282c1403680701c01e410300c61100481c8050012898040320390300940c00e0150180b6029 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 387859784 1250 387858534 387858547
    0x90b0f031305010c0c03031a0f0603060f09041b090c02100b040e03040332060109110d0c210e0712140102031807060201050c07030807090506030108031201090926 71
    0x43c2111540d8056074081422103840404058140c02503507241d10281c441c9001c1c201c140e00100b8a00c1e03407519401c070310030040000013586c00e03901c1040100e0004400307003070101c0b1840c107407030203040010360818151200060240001743c40c04031030040003220040b1742c0c00792402d82c41c0703903040718050401c12482c3c0d070f40b05499803821030502d40c0c01c10180c401103000307492070340c43c1f14582d5a10b400b180c1042c072030001041e04216480080840300054060444103003000c0024591400051420070b0f009001c096403886091821410b4450360144a503582110f121011101001750722494030104e0b13440c1802c01f0306542210108100d02650501020f4505015007110707a142c0110041306400c9a108a4501c207000851a80da100d080c44200500009082c1c5400204200d041039842c0c105140901080141041344030000a218680700302c0c5484000c00303003d031440e51a035071208401500d80d001000381110011080d000026030000f00d010700c0860700e030080d158400a8040e800300c2005042c50808c4100f0b00703102044807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 387861034 1250 387859784 387859793
    0x423180c1c052b030608070510082d0403030f09020f0f010903060c1806030c0c080903010b0d05100b030604020a0501050a05190c030318020109093216090b0f0313 71
    0x2407a0414003c1d03800056000b11580282c03c40d942c1e43c02c046201ea00c04003091102d038440314440348410a841c140054650f844516204040f510103401c1d4900420141042e000400b0000790760b0700882c403a4400380900c0b000c07440c0401c100c0340d004002946c85040d2880722031003400e0101c40380124000600d881d910803038172078403030600b91003071702d0f80d0348000844203a8003107604403a0700c0003640031b003c4529040c0810300200d2001042000789140281110400003000e401961302540414015070000d081c0388140001800e03c0c5441d0016020000c880ca418151849054640481c3d40303407055500800161805003460f00440da03540200c5405024018200041e12403036102c00880c00e903555055641180780a42858003e05a40c0081828a443c181e0640381c1d200503a00642414181c8020a00001e220500484010900318080a462210030040c0c0740700c0038940d0f80103200e1031040000315a00c007514142030104a484040500ca5030b00881c3c0c052060840e004607440c000c50301314109002d170208003412501e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 387862284 1250 387861034 387861073
    0x1d15130b0301060e09160605030c030705120a0906110703051210081b04060e0105100e0102010f180b060102031207180e01090906050609070e0f0423180c1c05 69
    0x3990340508108104404240d040001030781d401b0f0580c2c142000c2a14015028244c1d0201910103410201c0200c002200f06100d901500c400d030303c5200e041e4001d0b003000c05c100c0008220450082c1c80d050f040c0508a41281007110445008036455590a442c3c507403010503213091000042c001c1071546034000c5000034010010802848403a280090410a0300f00c510100f200f03d81d02944031070300c0e0a028030010080c0b035032a4001400c58500e2410840e108510900c0104d0051407013202e04a040c0d440d104172030304c03202c5680e0080701429100d02001141603d0b9180103907524010942e0303603550440644005801103100300020000440c11408003001c2c1500d4922a040e0000240c0002c01075a641d20042d1092000c5402101e400c450103a5185525050011005000c3c2c08920740e00307802181c80410164040d25a94440c5082c1c020320040b0f180d2100c00b2240004890308241c411040008114000e850710400210b54002c800400602c6811034101c600d90010480340141000da4072401140109000d1280d41032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 387863534 1250 387862284 387862289
    0xa0609150602010b040903080c0702030f161403010203010e04021201020405040f24030c0611280b090c18060f0405070210060e040203030d0b03120703091d15130b030106 74
    0x19042211401d00c50003d0131a0090003403540300b42c0c02e19102d10003103600228020b800c44190b1446542c1c3e04124004a0318040301c9a002c890a0b10402c541282514914035000b0b0544588070200070f402c00c1c1145c201402e0307000a002c0e0f0395118500b0b03808203006141401c4001042c80404001504107599100041d0454010310003003000240c540d241c545280f26281c1000303001a40785045503201c0350850b220f400402006006460074000d85000301c03442d00c441008030b041426041c0300254022682845002805d403c075500440c1c25180c4403000c03404c144004542402c0c0e411000d41a50500daa901d00d410907015006000c0c6a004280100c403201552914019548035004c150003c003e2103c40050311400c0701d1079640321072a180000d405000041e6408800c0b590701e5a1b840a0110713a1044460010341071502c0203500c0e010740c1e100020316404054000c68154211105001e00c00441c291080c12f000000b141101c5c121911242142c080b03002d0710b001d480b650045aa030031000500b00c58101d01083c2161602d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 387864784 1250 387863534 387863561
    0x90a0803090313080a0b0604050c04091109030f0609120901090e0406140901020a0203092b060e06060405041a0a1d1b100903111306033f080a0609 64
    0x511580350b010004001000b05072080c020646074445e5200d184400300302516040c45141c03148049100c820310300040e20083c280d4284100085004903030410656400019200d00a0080c19a200010100424440e03c5501450050150200700e810501c040b82c1c072044180d0b041c802c41d52030204490304bc0003807940c0309602c02e060004424054144143d04047c0003080088170742e0040105000301c607808800ea0300e46100944080c2408145254104c0d51141003800c0c001c542d1003456183c83c00e104013074012804600c0410250ad001d516064140000d07560222009444803c0300d100c242c0440312883d60042d0b00490405000078002d500d000c201c0502d00700d094811803180d001203040d40454448600b0351f22255811610149903190f03440703000d42046800d01c4054101018200c8117201030729025814420311004220410117940c40c1c1c5880d44c0b90b2080503111040ca50800001000442071030981048182c0002e074000c01d4001701c850080f52100d84c001c20703410420b9141c00c00092020003c0c0102d151800d481d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 387866034 1250 387864784 387864787
    0xb0a0506040e01021908090a020d03050a0905010806010c0209100801050705041e0f05120a0f0804080c030d02061603090503040f061202031501030c021501081f090804060305090a08030903 82
    0x1000070082900c00e4050b40019991040004000d03000c020a010b081210050400e200c8641d680d030b407201e051903061034019402100d40300d2a002003507842001888002c07240d4072040c1e40a901c2d03a0046131070b58412506580400c400400d00c40251401c00115a8130034950406212010380f076500c1c0600351b910946411011800205060054402c0d0301000c0c10500300e03880c000c96a142c5090012270709000c00348036140c000c80384101c104040050034851780013032903000400890003a51a00c0c0c4034249501030302c6440c0d0b5078018007c840a0754640818408080340d240d90080486803600802e990703820071141142000e06945000e000005203090019100800d4400c40c0b0107082454140064000d05180c82882c0c04a4810010001c6001c2c240e43ca80da0720030000e180000b0410030710328003685013a13490200c0050004d000300001900d2140080c910214242641c1c80c0031107134864104440c00d5501c59000241042028002489024800d500c03e983c09074048085604141c4103440b401301591050300c841119400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 387867284 1250 387866034 387866041
    0x10f0f0b0f0c0f06010f1e0b0f07200f010c11010e01090e0c030403030b060a0203450103060803090f12150403030203101d07180503030c0102030603120924070b0a05 72
    0x1640c1e0002c0005007c520005200030842e85c1d01c9003c44201d030700030381d1340d072400216070750040d60752000c19103040c10390064042c0304448400701801c0f0755032401d22440780700740700c0d0f00b82c40700e81544200f0100103210b500401a038041d02440300150741895076520401e04004840707500085a02e00a500d40d4003a0300b01529496907400d1a040003070544040410041c040c0c442042810100f55001040b00c500c0158018034030b81c8404901041d4482c2c07800c043d010701450041c0492880c0441c03a09000e5142c450091300d081250664403242d43d504ca0159040c5030750321064a141040d400c1c10701188420711880041d06940b00d0031403001200251980c203541c15000203501004104541010074420005032100e030300c12240851001e059000c3c0240c0080c203113020030480b01802c81e480400b00d414030020740781c000c00303407500c035213010020714000e41003110164480c1c0704030001c04180340341d076908407541c03504050541225480c1740c40305016541c181101e65082c01404005580104000d42c40c04e034000c0d0380d1988013041e1400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 387868534 1250 387867284 387867299
    0x40c031508011b18090c1101052208030a090209041412041220031c0305010e061c030507050607030b030c0109140f120d030b09010f0f0b0f0c0f0601 65
    0x142a50031900140e07241440c43c02c501104106a00502d071030f6450071500e8040c800303000c8044a20180d00a031040b43c24201d4840313219800c81c15005410f1143e2000700216a2501c0600400403401c81350b490640800102940c00309402070000d5030711480e0a4404501d000499010406504c0101c40580c0d103080403100381c18061006112210f5241503424040b0f081504040d0070031a20002ca500060098100124000550714000c0300908114001401d442a421000400c04003905401c101c01000070f00d0300c00041a81b81d0b05450107405030320050041071414403a440c031945007102c004070a03800c0c8902803061000160013000300f00c1c418019a0303008150300c031180f024507181c03200d002c64003414809140c60602c8900d911058561240404582034000405240045001d902e1080c0210f81a4061340d49000b504035015004030601d45020b940c0e8800f41e85c0d0341c4084004c0e00c0c801d0f0042d030701c200c010048104450b00c0c03108080c3c21070100102c07a142c43c0a4a507009185006107890488070305410400c010007103035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 387869784 1250 387868534 387868571
    0x3021201060c020906040518060705030709090614090603070e0109090b01090c080a050601050705030403053003060405221109090703020f13143102030d0e0609040c03 73
    0x40c51070b414481202581d80d800902420350080001d40603e586400165010b583d41a64501e2658048241c8189090000d401002c13544111404c3c0042680b40300c001412400c1031144004507604024007948090002040140c500340c040c003a02da00d40704a02011645c0f52540640c0380c000e15610340c0004084030709240540b04504142d0080750510700d0302d10907280b9242c00000c40c45e0300510703170070300000d07076039128001a94203001d2040b01030304a01c4086000b10811800113800d2440c03a9421144400114001c8103206038000d009054162000c0c017480419503c0c20700d508150b41144080200e21485d8403038101190003206008419101000501001c9a0700d0500802c070940000620001d821802e0a5401182500c40003104503801840e81108030203034211240d200c0002c032209182c2038105402c00791000012401160030b0040141106422845074411a03286130860350741c0a000b130004524900d00581d0800301214007d41c10000401c1103002543d0755108400da848820348001415150b194070100780c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 387871034 1250 387869784 387869789
    0x201060f050906150c0d0302030411060a050d051308070f06110301080706051b0d1e0203120705070c090c02010f05090d020c090a090b040807120905010905060d02160303021201 77
    0xe08180c0d000910454850107442584080c00307983c41d802c010700300460302085219a40c5484094082d001290300019490380055015501a81040c21150062000c000781403042c0f20004001c41c40801030b5003622146034004070351140030b030400d64100a5075a1208030703041e803040404440f40d900c0880c0341010068a80314010342c800000c030240c0e0540d81440c0c080c0d5981c080710b0040c0820b2200c0413035a001107810700c080c000d40c283d0840007070302c031640d000f0340c030203002030785640e4005c1c030500747d400145030702c0d1032000050f50714040380103c1507101610340c240240c0c1c80307038001c1000750362001c48844080789005044c02080c42c8003d06500008041300140308920440b00c01a100050781c2d00010110700d0f0265001a10300005d0004942403412511203291311001400032000081c41c8000f190100000e20132048003424441d8000e1984e91034410105500302c40140250040c140810540c010610030b604080020b085040b68800c0c0041c6003000b6030582500551100318203e0010703400148200144644000e010f00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 387872284 1250 387871034 387871049
    0xe041b1a040e0a05060f011b06140403020622030309050a060509030d0606050f0301051903170a110c09010e0a09080c0715050c0c04021608030f060907021609020c010209120706020106 80
    0x117428200000346501c0c41c01040039041003221442c204843d03015403101000598812020892803914000320413134020105ca098025008400000c0c20f100125070700341030348541071095515181580d680540091100c644103981601c00c80b0202000501580300b130328000e515500055071a6a003d0700b03103030180c400f260840b0003004424024041c24a80900640e41500c900310f030b00c0207440700d050001c803035101b60320752000e00f102001e4541410340042d001c0040088500e2a5143c2034040c618032481a503071450500c00c10340005051004101081012103041d81050b41c4513030104c0d4618164a0310f40b1182c10800e04540c0c9901b086008110080b0071074007591080c015801e1aa0800b00c5d20480d807500c0f46d5403403c400c0d00450700090041c1a1026103c001010300d540406001d440741811201c0c065403e8048880d1400307400c0000c0481d41e42d07800040ca145540c1e1840403450794a6081c166440040c1d000700008040c10b44d024030070300843c0d566000d100d00507409135000030402d1500e0100000d080d601e00303910408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 387873534 1250 387872284 387872291
    0xd0c1116050d15110d02040504110c0613170d0b090106090b1903180303020904060e100515040801061e0e25091a070510060e041b1a040e0a 61
    0xd034a41c0800510309070b030410b2410f29080c2000031000d01601c00a0a5860380d07040016494030520229400344c002d6600690381040242480d00815109104e08240960954004400201e8407902010187c008520840e00d804040c40e0b1900903144540240d90021211611100820094202041d440740100814500301414526041d4525064441c10000d052542030580502400358042c0d0010740c24107a0600c01c80d030644490b818020029000400303482e105a042c800001000c81910880f00d0061544951598540b031030402004035851011102580c0c03000d007400f00060400082c42541c0c01000080e06030456101701510420030141c09810400054140c6014492032407035060509900b080e943c04081c0302d400f01c041c0140c4d003801c900d52190104912140200c6080b11a80780505520b0744988111601c102081c2502c509079003240c080c004c00d06080e03100140c0442d983d40000214298888038600040b52503800c020302c0740107000b400d20020200014108500c0d00340f181e005134071408860082 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 387874784 1250 387873534 387873539
    0x301050903070f170405031203060405090a150b011106040501090b091504080307030e01060816060207030f0b04020d0c0b0304030f030b030d1115041112120f0a050d0c1116 75
    0x502c03c1c1101e008094850b0010300540501c840355901180d020303100c000c00b107450f004100c09608400b0b92040724000d0113681001c1c00300c1c000c070400041c0060225403010301c3c080b100d1404035151004200c448400c50400000e0150030115000c03d03c100c034080d5010300c00206998206043c9034400c2c8401402811860b80031000e18a4648800c1c1c22082d0066030084c19640e4984440c00110080c007500c00000b40c0b654030300900000d540c400000c0c1c060f607100700e946c6000b0841756108020703070312400b040c030000c2c24600c154540d030300000740342e030800c030768045d1009184040d441c0154940d01060146500a1601c041300041407005050b004001c0d910060300b585024000c509080d0046500c600604400c0b1045c00f9011760162040c0c0414004455103c5c41445041290f180906082d880e0354074805a25018421040080302c4030200441d258089149034001140303400d10300b1072402c0560b4414564401004410700c090545c400c1c00d030050860a1a16664445541c101c1d1000107060a00c011a009420300120204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 387876034 1250 387874784 387874793
    0xf0501020c120a0f06020904022d07030203092e0201090309051f030b0102011803050306041505060a0c0813031112010501301a0702010e0604020117040606090614030105090307 77
    0x280c00d09660202e05807a04c0c02c0da902d4017402078020100890f900500200b180b00030551701c00c0c0d01101d0101d103074030110744849820b040e82107244140741000d00180c004004400403410410322142d42e940140250458249400201d81c06810300c6000e5600141d458402800c18981e0000c031100c080c0c402110010124450150003003000c060451803881850744a20045003182e000394401c1154501102c48001c0b8031600346402001a401120750510030703403a00134802080610b001d481c0e400e4400103042c2c50710b48010010240d40540020300c080f9552002003020341c0c54000d00d08040401148106110000d204a5008200b9401c1d405d8042000c60f038540401041741e1008221000300d810300b10401c1048a03d600ea0b8860700c1c901100c1c001901c0c506800203410608181e4000c214401e08103a4001c00042800c030041d6500c5840c2550040d0014800c00a2010a110b1600c805a0070920400740019010381d6001840e05480140e03110610b0218001854200c904081c068039500c03034200c0c40075600e4070140307545 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 387877284 1250 387876034 387876043
    0xd030506100905130e06070207050910030506041b0b0a0309060c03050402150903030c01060605031008010903020d0f2102180303030f1b040b03090a0c060f120f02130f0501020c12 78
    0x210b501c16055000c034001c056550307500c40c000340c074071a034199805031031f11440203542c40d9240c0c41054041d80208000410762442602440c041d40d030702002030595500c07261210300f4400c00e503400c404101f088502c00095106d0652000706100c6846841c00f2401c1d21043c1040000c507100c0c9000c2005050a00d010480141d0303a11450100c0084080303103803030310346550801281c990f000d01209210598605800410415000000342d88254640140ca103006910b03000418262101c1660080145e40b00790900c240e49401554400e4960304503291409021f042d203118042c5141d82d85081080c101d60000b889004400c81d42c00900001c0c40c02c0d4025459800d051441075403004008200d211140c401154002c2c40c41c01850485004000881c186c6803242004500703039441d0b0201c46800c803034007e03000000041250040c04550303104030042d2150459449c0a81c0940090301040628951032542002008540e003010780c8200b010b0040d0125000c030180c10a0b0019103405690341009201740c4400c040180203c0c00080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 387878534 1250 387877284 387877289
    0x60305041104050f070f02030d05040b04060e03250201030b100f0201110a0c0f0201111f0b151611100809190807111309050a03020607030203061c0515090d0305061009 73
    0x1400a400846d0403004a0440c040d501c2128420790801c2c1c14803042c0128070301e5080c0680c0c0100070800041d00c07107466541c0d032841141c108403405001e1840000d400c0907014200a031050040c14081580075140001a1a100070130f061480410800b809081181e0390910481c00040c1120758298681504004060048014010b0041ca4803010144207070869100305210555412100122442070b1000030791058421442d00385100d0062820040340581e1400061a070405280c02e810946442c60f0040112070220020303405990980d800100003106444030b08100305640215603c40c0c1113821f1140704a4100b520304a0a107103100708144240c00820071030b0048a40f5541e110303100000d0f41c0502008500450300007040541d0300761134803040c60300b80403000c40c01000c054440e6003500c04a94508000350228001502c2c9990007588000d400144c1031011000f44400c2c038000c00840d4071f1550310b02c0012034404011130300c070003c03600640f60414203136405010711a0051011260b40c0300d06411507600400300c203402d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 387879784 1250 387878534 387878537
    0x10e06070503041520010c05070615051f080a1104120c080616170f01120f210f0c0b070f05070231020c0303040308040318060305041104050f07 63
    0x200802000002c00880300140064403110a14a84410003d0b10700c039041050b91142c21028010560003081c184140805403c02e0345a02d070030080c454544d0b034014801c072050f007078114000107004103d1380e44903c00501a2004040910700031350001200070904c0300044c2040318024100121100410301840980d1f00b501c0391104004985c602e0750074030700100601640005081c0c040d0b902030010701c0042d8100b01401508a0310f601203078101e4000c46400c190000c0716800c00901c0594014007141071000c01041c461801104480c910300f009445404645000002010b0f507040c20800b515001e0f900b011441201144501309080b6580440e212408142c1c40242940100410404e240c05004d0081e010758140940240c010000c2008103082401c04010180c0e04c03a5518a094031020502802d03402100d54100040014604640b200e503425140d00358042c00071410b0021442411221011007a400f00042006541c00301d42400c142c10044000b05200300c03035501450902003003110b00c0e01c2c000381d0759030403e020307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 387881034 1250 387879784 387879787
    0x312092b0228030f060617120903030d020f03060a0807030f03052808010f05060408070e2a0409060b0a0c030e010e120606120307021e0d060203090109050d050405010e06 74
    0x940d5400b24646081c10741c0c010086045404400c1c00a20704420012134030030f540404c004c5440e002c1c1e90303107898210b1521480c2a48459841141c0010080240c121244040c085070b0404114060901c103a8201c1b09807800306000110811600e4030f030500240004001140c0a00402c904513203c00031051030102028051000000e80d0503040012102d00854100000012808207031003002c0040282d8002c8c401c0031105104104c011820b4648102103500b1210158024a070b201d103130807803520350f090000340304503400c1000310702c03c0c0c0100825010084030361500728909a0b1340d5040c900c6900454040f5003248159450034840c0c0884613400010020006030142480a031a0fa41180100c805201060742c00d504601412101241542c000600c540130300411205040d4540d80030f2000c6503280603000020b580004110403507030f02c2034101c14100e1010903003c0e0007034601544c0c2d44c55003c00d0364015a00302c0141da6603048580d05000d410300c0304058140c0d4614280c3d24188c9400d0000309100b100345c20b03440c030a000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 387882284 1250 387881034 387881059
    0x191e030b1e0f0d120f031a090c0c060c070b09030a0509040b040605150c070e1b0a0c060204031a06090402101b050f0f060c07080d0b0607020312092b02 66
    0x112007881402c4090010981c40c1c401d0810714042080703214400a0101003200b40d400c2d40c07105c0d8003038014859a50100121042ca4060f914100840c0c200094030b0094120810845004007400c03d0040510508400b05100d039214401c3c60000f0122030020701184a5030014000c00d40c1595108040b1450384004880c040b64401c0c840001a0041100c0d50055920006181d00910f00c594060058120032907254180c9800c0c80c0d81701a41e04900004945841845a242450b42042100ca901401e4420041d1901ea155000c940d0f403840e003242d1283c1c1042d105e220352120500c2c845152042e10035400402603c00042c0c41c18144d003c074560601c2c0b0080d11050190203032500078040c00320416041115040011180120000105c25466100c1c24103031407806c0c05034200003034a14840324129170341d40d42d01c91540c61900660145400040c16502415503100d0700410000025035401c100186214020001c500d80d6011310008102c0001e92906200384808811090b005050b2400801071410980654203074000d0701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 387883534 1250 387882284 387882289
    0x3060e0103060924050a0b0607150c020a0506010308030a05070e150c011119080c07050d0c080c060708010609080a0201090e07090302120d0e0d0506130602191e030b1e 73
    0x10034628034012112002c0e080004d11410680119004002c0030504200c0048900e0610041e485140409025181e181c1718081003064650b11500f0703d46903520541e5000c182e6640e50500b801030a13841075030400c402000b03004200c0c2041c0f081e15040300c018140510018914004690022420b5201c910b4807000859101c10b51a4290808200c6005070350720141da0b0341d0301b001c04202408101ca01000002c44440001e01c1c011000401c8400e20341c0c01000070468079450500481c1e000c03010040031207514900780300c15901840d003004643d005e0401d0740c03241580c640c103250300103007822269800205641c1c400e042e42c41c0940d0304080c1010a642d0070034003024040d42c1c1e0a5050b07420070900e44c0000d421100100b1405c0300750b00d021403450060302c0e480c0d82d0140410012810440540c5c1e1042014156800100101d001c2818210016104d07070f119503405402d0008a0000c1c4800018102610002c25400040d520b0b001d00300414980385600103003800c00000e80040c01140040e00c03d00498000e19640000003503135035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 387884784 1250 387883534 387883553
    0x19060806061e04060f36091113020304050105160903110607050f1f06030c090509150703061a0301030506061e09010603141003080316030e061305070603060e01030609 73
    0x940c0e0180c018800541e40c1d0b40d01c24504011441444c1b02c84000c410711010780e40c0c010310030550035030303543d410300c481680600002c0008004084c8101c0d42c00701440c1c0401d0f41604c8a4400d0b190400285034010380f2461706080c214291803005010b407541d828480500b4400941004181040d00d40012007550502000f078041281403142070006031043c419417414900c00300001030410341c0e02622411102038519200f201e02d0941c0d506000050282901080c10b0003011060360003264440c5000c0222020b0940405c1450315184042e00c80e0400652180303020711081d850b6103030f10341c01c900c2d610781000d1556265844840d142c99003d04040c0c41801c0307907044101d040a200749040c0070320309d0060001c40c41d96500c3e00090010101c150320241c000010000184842c44c054080d042260b80003008276185507114407a00e075980101c0340c0e1150500d03a1314040b02e0780304582000720a100e00385600303445c5161000fa00780300f4034120099101a04250500e6003e001040801240354112a803002000c9850b4900746000000d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 387886034 1250 387884784 387884839
    0xa09060b0607141c09060c02180a051b1602010c0f08030106051309020c1f060e040c0614032203030e01020a0305010501030e010b010503010302060c1905061906080606 73
    0x2004010038200c0c103120b02c441045480000050844d40d160143c0c4040301c0545010100d41030110f41013540401486000d2143c800440344024103125000b04121800c00e0350301c1040ea0401c281684e10b004003d00404103050b5034140c80315510a00e81411403032900d4410340750407200c0090400c2130080140f8100001400911203c1d503220308140d843c1d68560301c0090042d04040203500201d00302d40000604052244211070030200614050302c0d41284106002018911001c400714040b90f4032100011125a02c043d1140a24810380c11024010302e400c0c0c0c0200310500c48503130b6151211f030410034003032041e24500504022444958140b4002811424181c001b001440308012095000041d4901c03c203030b040d4000b0781a00d00036201007001c1140d6040c0c00f401c0311b40340c81030180443c4040006002602d8140098070010128004848210039280301c0000d070f07005411402c41c1e45500c04cd007842040da0140c4500040716002e080d040090a01d401c003020755400c0050421400782d84589629051102404d058855 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 387887284 1250 387886034 387886039
    0x4110a0e090607020d0809150c19030608150915090307020d030c021302030106050a081005061314030a020105040b0705010609150305060c0f07150204270f0608060a09060b 75
    0xa1440c01c010702648540d0122102c81c010701034a42141c07001802002441c1c05071070068010401c02001d42d40003100b01c08054103c8901260074003502d0400ca4180c41c010304d0b644e00f1907034046100c13443c0004161410020360b00040084c40c086080190b840300000c2d001e1105810040d00b544103485031114103007903109400300070750090b9050580e0340c18150440c10300f117280c51081d03940c2c2111a90114400040340804e0042c1c000040c005c100d901d025920403604181c1012614245030b4810b0740d07500010700e499200c03104d2080100c1c14076400b000701c524503040071640001c00ba801b414540c030366540001d045120324001d2050100010070712406000c0700358440c401403e45910308011090845655540030300441c442250b50748107002c0003401d4840d141d400e03980390302d100c41d55079402c051580d0750300b4400c490701c1c0d4101418590709100024000d41600c0584a42a110760304450801d25007091050540da81c0d80786c09401281044810407080300e0016096900c5401b03d040042c90354028501400504003000c00580d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 387888534 1250 387887284 387887309
    0x11d04110a08070206070912111e15040305030405060322050609010f0204050a05120f100504141504030e04020d020c0615090c030115170412081005060304110a 70
    0x110100e11000200504162a20b03841c4071982c6014003265904d00444401c3c0005000403001c00c00104a5080340981502c1000700303858010020380072070464010000f642c2032004080440200303500307011070301d0102440d210741e080740740604684400d6900c0c85144500ba000d9500000001d210f003482080380c01c004840900030030716906050809a98920040d54902c802d5460306001c4003100c8090301c225802c03240007411404003103140504004800c0da2262030700119015400050783c420f80240968541020032450005690a241c00c1200360100c0c4400540310b1544004800202d90960110b040c1d4031070b62501e41414108a0140882c01a02680000a07055030000c96114814103012540901c00c01c181c01d0b0006400b0781110401400000c103950b5800d040c0810401400105c500c50704002a08ea224145011010286081c95040b60401c0301c064890b0007820007400d038020b5003c1030540c1c000d90000344c04603425003060001842403101501c0102841000714180c00c0d607456070304210001f0a0b5404060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 387889784 1250 387888534 387888551
    0x309050f0105070306060302123601090b060604061b060b030304030302070302090906240102150f0a0606091512060e01060c0b0601262a070c091a011d04 67
    0x40d8060441a00c0c0907020a007086008110b59129200f034034503840c0d41020184590315410340000d545034a01c505542c0d01490000c03001440c0443c241845111000f000c0000381c01c0d0b5040c284850301400c040c0800c0d01ca01001c0002300319050344860003a041717040d481d404e010b41c03596520f000342c0101007400f4440d070180004640017050680100d99101120700a4810f804255900b03a00c42c1d449110448904010002818001094101c0d0071586085c2c040b041c0111405601d42440b04036809200700c5107440d40046d400104511400c0d680030742002031140342415241e907400c0048044107848038481070300c01c104840c00c1ca6075a403812504044020000c000203c046541c580c200100800701d07115090781d8004210b00807890a5120b8104180e0311000407020450301002d0f008480e1020b4800b5140480301000141c18008040f40c80f0000c0300e0302e05500180030b5035000710f441d040c0d580740625481451050b240c0090440d041e8908070b4107174041a024a4820004603003000c0c5180d02400030512507400ca850061031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 387891034 1250 387889784 387889813
    0xd021201060504050901061d04060f090f03110604052104032114070c0b0c0c0405070216120209070507080f03010f09050c1804021305032a03030c0616030905 69
    0x3540507150180c400b4013071541d81d21507150a0382c03001d1140540b503120801e40c1001e4405c4610015411501c200c0c00030031450b10303040842d81550b840700b80c15140e95400100505c2010742003034a140104001c0005001180b40a403940780d1640e00d0500f2895110158402d800c40280100b41118003071a404a04008031064076514103001f00d05032001c6002084121500800c40900c0708240e40003241d00003058035141c1d080c01c0e43e0070300c1034000039214000c9100340700255059a03640d004d940d00c0b0b941298001e14185180035244510b01065a000c28501507501c01c0c5980035031100310145038004820b0509582c2c5070820314112041c0d1150070b5120042d410044008140c400030040d000003102e130720507401c1c4600d40700c01030725030044d205000303d160070f59010f22001c440a0600c2d030003400000c0005c005d400344095440300420f04126a40e500c0d461a41c0d4540d0800b11042c032285d602c45841c1d082500103508240d1030a00701c1d541c42002038501c01c0e411400ca01c0001000b4400d800c001e28403030f0322100f6140b010500415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 387892284 1250 387891034 387891041
    0x306040b0405091b061806280f12020a0801030f0302030c0d020f0d0f080a0f020904060902070221061f0b0c06160e01140906040b16051b0904110d021201 67
    0x1001209916545138846003850310a0503a000c1d01001c4480c031100740c45070b02c104403042c2d00031885083c9804014911009506500700001e03141d07405512404048a4a000000e10080202132032118452042c40001301d0315a1000781141984d5112000748840b1070b0a00b000e0f031843c007d003444100c66110b00c40302c000e03c1b1030f4041615015039880c64112040c04d0440d61040d00c000950b40320200020b4500300004860f1445030b00156a80d01c1520030051808a07445c010038150380b0240c02401c80c1d11703000944001141400150115001c18158100000d602a42c4066840310b8002d0464102c0c0801c00c21496400403405091500800c2021445aa5000d180601c9a142d02044030488504803024894411003801081c0010441405035100b0000c00131007200140e0b183c100d40c80d4030307401080900001c9017804100c1d008100f181c40340341484130700300c0b0f9514040b86840015101c02d424440d003618042d910b0b85440c00c5a03500b00f50300540c0a2400c81c01da502264180c800c0d0f001c00f035481803000319030300e001520660 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 387893534 1250 387892284 387892303
    0xa0b0307050414030d08040b04020d050105090c0307090e07180f0c0e2107060c0309210506130803060402090111150105030c0a030f0602130b04090204052707050306040b040509 77
    0xf1003509030541400201030700c40040444840100704140000b90010300c0d041c650361b40c0a84014403003085480c5a80701e207804c44000b1264034505511810b00300d00e262030100705040c0200741d1005d081c041780c0b03402c00d0196140c1002d0720400b01414120003800d00f10344d910303030411100400121000c0025034880c030402000344282c110f101c1d0149115600d80552003e50a0015000384407030301c02404240d2820802b03c8000d00c03688426410040e030701130701203104c41c241c0d201540380b0014155840c1c07122aa81c140f80742840005090307030700c45402e9006584000341e918810b50b07a0200c41160b0040c1ca40701908016519203d000030000320750b0041d5820204104000075400b4140da10580483d80e50254000502c007405042d4040940041410b841d550000758580d0000c29910f0450414956800d541e052000311075049900581081600810180040d0074803550000c05a1036203221041c0448100c203201d094400058240f4040180010006800d511150800030940c51b0140c410130a45ca0001d4400f6200c40508 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 387894784 1250 387893534 387893549
    0x717220821040c1508070f020304030c080d11061012030311210a0b03060a0b01090803030a06061b1a0c091c11030d080a090213050a0203070921060b0a0b03070504 71
    0x140310108804c08001d0070700c1441d90759600c540c3e01640710b42400303503180d005100e071901c11444100004000283d4404900380240700e07080c01401c4070080f2000150404004103c0e1003142e078804010410420101c501c03106c1242c9440d11a120b00000504084020b0b081d828910040a0000150001808a02c15000350100291074501c100c80e1942c1103c0e5044d941c1203800c1d039030305038444808103c0f800382591058547c4801414900341c100ea40751646402c541084030f195265581c0c450040007003d40003c41e54000d48032aa4029100e94100e50711102d20f101a10004045c002c2c6160024100800e040111150404001d0002c0030f0811004070980b0b80550300b42c3d00305d078280c40d0b40d20140c0060400103428006403035691210a9650385071001c00004001500041e64003042500e00941007166500c0b13418001c0c88070503400350b40e900c0d0501d806401cbc200d4a90003521010300c0b1210220000340403264071203071140e0121012407050010400244040460380280e460b0001c00828000c50a403c10018001c03100746 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 387896034 1250 387894784 387894803
    0x30702070b160215390a03051201080706080f07110f0a021f050910020a0605040807030206060f0306010911041e150c02060708030604090c0905071722082104 69
    0x40d440c94164034054044a190302402090307040d1403600c0c480c043c03048a5180c5c00e104050490000079500d1805001e1081503001c92800903061a4031505541d44601504104000b4865281381050040c14040010f0451204606c0000450800c502c50030b0b420060b04c07010002c889425551008040d258400d9001c1244a00f100f406480d0060400f10301d00101c09210340c0340c0506009034801404080d1207520044803c5002e14140c0e14001a05403182d1401540261841ca844580b14034000c0d10340380015020710310800502c004c0d01a6580c0005005041d03c0794504041a40e171941090b00c5664000d41c0c1000e040041040c0c0d1418041000e846040100d0700f010391a902d00d40a054420344610008000180d0003010400401c0040307168480203540040020b0070000301035120340c80348400d4039929000301242d03a84070024420300942c0b00020210104103490b43c18980e04107690806440c200da0501500c180341034001100c2030101500075549842c3eaa405c4040401c100c80d00c850050f04c4040710b08441034281c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 387897284 1250 387896034 387896059
    0x9160f08060f0f011101140f0c03280902120a0c0f03050a0204020708071401060302030c0102010e100513020604031202060c0a0e010c0c050301060605120601020607090b030702070b1602 81
    0x85661401e00690340a00b50441c0140b581062020044100d0302032414031041425048180b2024440d40600203a4034520758442d050031000465081c4014083e592210030074802e00c86100c004000d07411f1020346411000348420306d0303100d03004050940040003030f42c0002d041c8034101002c400403038100441c5105180101d50303240c981000d920751041c41d00001e007655105c03080342001403c181d801800c41034000e02a00e801c0c04040c0d41c84000c415206103000c0c440c0c1c0d44a04003042141020007207403180d54000d000038081c44402c00440c07603960100e4410b20610688540c08105200705a0344100042da070041e100c0c594440e22402d0800c0d0b0b6064600900006103d120002492107504030180c0e0841c68030f070b964001030050703400d0044851f1082c0f800207603072a2031101c000182c20781d02407242000808613a21111340301e1581807540740d0541d000070051819901300d1010488080c2d848a50700c015a00d8031091240c90b9200c0c8001241380c0102500700c402035010001d10012450b56034014450300520071107030f10800d0407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 387898534 1250 387897284 387897287
    0x34060302071a19020a05040509070203090307050105030c070b0c0c120c0f0c0d112d04180b011a07020319260d0903020102090a26010c020a030e060909160f 68
    0x900459840f110780e00755007401110303503900e500103000411007441e00301c0c203141c1c8800008604510995044025a000003001001400e0521040d4024142400e0481c118a070417281e10b4002c1c030a91500400d07148a910002c0d80ba0225a07064802c0326002c4411030b58208140740509080d80c0c03090990356118420301008014400c2d0000e0441000075001e07000280c070390020b035a41d02c0340c00909550260300062114500c1029286440c204203c6941d02950034210041c2c3c9080c0f20807908170201d1105007041401c405408950090000c0d0b0468100c0b408881141b0041caa981940f03014089009505000b4811515003401e200b030445140103009000da45402070400710403141a620841e126100d40d502808490706140c1581e0007243c4041c0203000140c0f81c030340e0400005501800ca41c110000d600c0e42c01c0040005040c203041c11311020b425041c000c0000283c4130f98083e542d154030000040401c41052810b40c010b450390030558400440c0a0f2110010f400c0526881e08544000d0489400040402500300700c6130313 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 387899784 1250 387898534 387898583
    0x310020a05070c0b0c0d030e0118060507110613020d02220b1c0f1b090e1c050f0405040911030d0e030d09060903080c0111180f10023406030207 63
    0x52080c0005207070054004c82c00758043c040008913102d4555032b6504609404201d0341c4d4003164a44248000585441c1031344002c0d1400308001c061030325a0703001e0800c00880c000c44404d820300d82a0110b8169040000c0c610000c3c088241c01240c4224800c0000d044038022511504000e01e0307180110342041c0b202202d826040818020300b903010300301400110b401c0c004a00316504031090407950b100d080d20707001c0c1c8a010513800c0d103415085968140c4d2190703800031082d100702d038a00304070110140780c8176190800700805200d240c001c2c1d0017483c0c1b2036a500c03410481001520140c29140351030142c241d403c03c542500e4060806061461003034003a004504030301c025148075040a43c1509d000c1e0300d40014040c02c6841d03074240c0350001d42c0341c21099036030340f1130380c400c9407407800701604003950b004902d90414600f41c5c042c0a07000001c022494000c03008071050503070158020491211001000441c607071011007aa005c060b80402c40d0394640003049440502260403070b41a0018507889000c0c00c6d00a070103100d00c24821003036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 387901034 1250 387899784 387899797
    0x504050c03060904050f0f030405090903070b0a0e0c0a0602150a23091002070c030c351606050714031905030a0b0a060c02010314240310020a05070c0b 66
    0x504904000160b203034600085880e8000340203408840031124419036491608500001506d0313a5400810100301c03600c0e020440c16880714020020f94101140c80da12581482c4024106100e12501d40303c0c40c0c0303c0b941042101080641f4000c0c075041c0c6490f940d040194543c00b0300ca107408068054800006c1842540380208081c2a40204521104689201d404103030b0700c00140c200380c014080c0151031262520680098001140034281418415240d894125007106aa500c40b01070003841260044420901ca80320540c2160301c80d080b221045040700f4100c0c1810310f00580d014101100d114042032495202001c0c0141d1845a50506070a490003a5015505e0244c0e40425182460b03042000c80014402c0001e9a00154404000301b02a13865000081a01c503088d008140003c0d086100ca2041d983d06000d086203003544600760720202e00f000300105040000f820900007030030b81003007141c43c0305803400c0001550290800f80c0840d12801c01d400010640d03840290290780d80a580300000c500803003c2c40c106c030003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 387902284 1250 387901034 387901051
    0x801090516021c050d14010509130f02040e0a060603110a0501091503020901050d0615120510050108070207030c0b030601020c0a0605040e04140a03120606020106033507030c020406050405 82
    0x240c5242902044000c0f1090484241c1040001e101c1880700085502980c400038503100301105481d07044c8024850045070013400c503071200000c0000d940c04100e84070001445560181c9020903495100c1503114900358100f0b9005064900c3e0800c00418092400c01c07103d9a1203048405098169844004458030049801601600282c100d41f00050a0081c0d000700081c0d281030501c58103045c00b001e40c000465100707501101c1c06c00103110002c203920b680901d071100307401c1c0124010007845c1004c00c2c201c6200501d0740140d40c14068014042000c03c2d0081013842d0095900c0f81e07007000340e00c0c1c03070324515919030b0815142980540b0031031980000500c3e0450728501617072030030390b034680c00c20b440c0c02e816503001640604151a03e003190203140c0c205400c140b00f0304000c14041e0f104c103e10a0710071400f82c0b0171100ca0790b200388116450100180000340071075881c40d024407800d203442b403100e41166100041d00411582140c2600000003214410150401c1da9812014000c64007003213000c1c0e47e0411b01040d92422542c2c1803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 387903534 1250 387902284 387902293
    0x801061710020901020c0607030302030714070f060c020316110f03030421060f09060203060f1905060304061b080702010c050a0f1b0203010f020c0c030a030c0807050c0a0303080109051602 82
    0x4403601059400380c04543c405204032817055a02e4004500f031a0f002c1c0e0010b0300029000020803c001750400b804908404c160003400340340650720f0b1280c1d8510088210700900c0c00c1c2d04d401c2d800c1c846501c01c000791403a20904443c0c1c0344044030b00d45046500f040802d90b416024001c1c1000d083c8140c90b011050f2011101001884941b8124607900082c10910283c3e0131104959a6641915101102e101c1c000030240b01c0c80e001682d90416104100d030031001580018402c215414400b200c5101400b02c1204951003a1400c90f12030302d951070190040c00b1040b0081e403590901030303003030084194032444060191146030007c101c5c1b02c200b03001c115440c0c8100c14a00010407100b030400c40009125001102d090425071030148a1b095031903000070f00f0b459040291200064020500601a4100b0302c00241c440300114003d0022108940d400b40407414440d1018051000200d554020b01000b0f00200c03178007240003000b0300e140030340304e18001d0103201c1c0c04e0042d5a281860200090758a14105081c0014851250010b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 387904784 1250 387903534 387903553
    0x30c030601181d0a05180d140708030a02070b09031303080f1b0f010c020a260409050a0c0e0108151005090406030501091412340b0108010617 62
    0x5403a02540c2c5007807224440b480540020380801245000c2c8042075003816900c0081c00d1000c0c3d00000d030307800036045001200b400340700c6044401000400e8903461000d070801c0d501558510fa040d10720303805000b5000c2d1800c2d0001003045042101c69008001692091110702d22940f00ca076011030303890242480d03a50107078071550424404992264007505081d105e0707000461910324200000c1410241c000111f18040c4c4c0300c48403840b550942801814404041032000306901c840544409007108100c4480000c000014442c045070840e20700210780240c2900030041c482800c00b07004502c000d1010150a07800512a1000380065602c500302c0280625131314160394004868042c02c103c1581c1460200c0c4081c00401c21414269440b00e0064500850080c0000920403440e82081d1000e040c80350407c081d140c00c540d1618544268000942d401d901090142181d240e2142d070501c41c20302542d04064041e030b050403040317400f00181001424181d40304080213120080d0f40c1c95000c07004030b5592550841c241c000b910304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 387906034 1250 387904784 387904787
    0x1113090506271f0b061201151d0f010c0f030c0201080a0902010806040b06160f020328030c06060e04061b030204140d050a0c03050d0807050918041a10080111030c030601 74
    0x2002d01040d80f42001810401110004806a009400d2021148103900040104a8000c1042034418040341008404003d140326102165003020040d00d1240042c3c1010510700c2c3d11911141c101282d01c4034413004290010305010303200c001320800c100d002070071810024111034a0b50181c4240594181c4500c02c003919164200b10203010318100d46904210103124020b403400c031003020030f0000340c0900d285004015041c0103040c01c1401007940280020002444004084d003104079481500340c2500c0d1442d5445020b10340b00d0083d02c4542d1003559581c54030828041440b1301a4480c180d509a0040d01031b0b6100b11031001a4103030f0040c1c3c441d104e40100007000404041c10444034901d840b40c411002d61f1714034512540c9014840c0016003040d40c40b90301c559641c003a815042402560021024204141008401c00004000b1100d650f0003a0f950083c2501103410800500d900010b0302c06030450505081c80e1940d150440c1100310f203e080410340c24032003600c030464070540481e0b0240103488940c91455880c0c000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 387907284 1250 387906034 387906073
    0x9090b0a0509072006070c0302120a200a060c050903100504031d0f0303030103030c050f0601082113061220090f03030c010c020304090506060309060103111309050627 73
    0x208448034803407201841d000350000c1c095107101b060300b43ca444d42c14012504000389018503096840b03002910400659240f140c102c9030001540054450700d0440d514034281e644d0800d255040c000b480d140c10451822000c41e04000a050405c41c19001c80b1a440f90103012541600d4040c3c0d40500864546501c603200c00c0c0890700c91029070f04000d8940040030700d221012030b245600981c0190000b914141c0f521040007402e01480c2240b5114200804440d410300d0350164a40c58203603400380071030203001070142c02010345200359410b028500101c00407075036a0b0326002c2c110059480a1418680c5403071343d98201d80399800c418000071906c4807400c03400c003804e44080c0300030000364030051503040c4028410f150038110f090250260058282d030103140c8072443c14401409403040603140c1c5224a0080c0200700000d100003600c40c0c11290083c881c64102c10300c0401240d8200041e444c120101414500340f2001e0080014041303004005100101208503000182a015410210407000c4541c000500e42c01c4d40001e51013 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 387908534 1250 387907284 387907307
    0x1e02010b12011a04020f160507091401030308160905030613230c0f060c060a09020411030112030309230120040308121009050a05040201090e0606070f0c0b030709090b0a050907 77
    0x40080c5401254140170314140447d00c0100e910340c1c054074060150b4802070244007403d00383c000e2001d51a5055580c09072111304020041c00e000780011000c032817264490b0101c0b0004007070140566202c0c0c00c000e40c544828829440054600400110b501c410400881d01515200c41c4c00304007070309180c42d0b502d080213282c003041c0ca941030744280c041c000c44201507414000315001e40240700c0c000030f40c2d0007144140304c207940503500300040f41141030004010210f1030000e44400907070b00d40790000f0400c0c00342c50f0410003036040c541011460030070f241c140b01954038154400c1d5200d061802249841c001048040c51003441036000080100c50140a0340021145c109070b415004038ac50014170101584581050013114000c5416444642d20341c010700c015540c01600d11006440007080d8402d19103070400218001d071044c010020040701d02c2c40400002e000d50714051001034892000712990302d080161004180700a80c0c000c0950840c504080840180341480c640011603401601012090f96031040c156040740801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 387909784 1250 387908534 387908557
    0x30f10081506060403051f0b0d02210109141b0301061a031008010203070306060f02071415160c030c0605030402031f0e121e04080a080a1e02010b12011a0402 69
    0x500010002410034080303c0d251f08204030116080b03186a01444003640c00700350000707024102180858000d600c0e100c10307950440542601c25040b81d0070201c9400d0040c4150a005400c0b4180a12400410080411000d111640c039440700c0001a405008040c200e07000391240d070038040d02001300d0030440c0f4881e50240d40d01104020f0844245640e610249007640d00407103409000a80d140303014412030f40c000c950b82c00841c080b8401019420300b08600010202c00c6401c11078860980c1074095010f4002e418111082c0d2200c09560110503165840e0584846a02c0e00003202c480150000c08229584221703750707442190000c004040d04c0000d0403100d1220030048000b011407503242e0b203a042c00c00e9420805448000030201e2b81d10380d110b80c0c3e84a401c81c00380440301d0404020b113003040204803505000417070703107401604081815034400714000f0607613401c040d801d049000454601c0301a0f40031a01136014100b455004e86010030b0300c07003160084d1400c0720307072181e24a21610001420301801d41426406003a0220300c3c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 387911034 1250 387909784 387909787
    0x3060f0d151e0507020d020601030813080a1505070c080a030b0d0209070f0305090a0201021b03011503060603030206010b030603100c0e1201020c120a050d090602070c0308030f1008150606 82
    0x3504084800d40d08100308200b45442ca1582500d2400e19034400c241d4072948500c05001d0303800ca5903000035115041071101600c0110301040e0020071030a444001c000030b00e035243c00ca5840c00d10034900110700f01c4402c8100451645020001740c0070600902c1c4014a850388018403038581031301e0120a4008003046075005803c01c0d000c59800340181c444400c00c5005078a5602d5040b09586000da005054503c0181100d960b80c00180d080e50051340c00050002c0c8544024040c4450401e05201080c010081041e81e5080c803a1003110020500010340e12031405c0c2c074040c0e42a245140e07220700c1110128401078030a103030140e100f1112a100d03403006070300140003609540f0304200040046000182182030b2000c0030f00340390350b00148207010303074404009064400205a1039282454806040a000d40c02416402070041c1d8035a0304180800001d42c3c1203e001da680403d12900b0035489040c9008150011100c68001c03410041c04607940d40d41e040e81d000304071034604004001c1450035000078501540c000d4029074210300c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 387912284 1250 387911034 387911063
    0x30f0c070504180c0f05060d0f020d05012d030b0a050901060e090d18030b0412020c04060b070201031508100218030f0a0309060f0206010e190e06060109090203060f0d 73
    0xc40b406688280d01180c144203c814005092a140c1a00c10380d0200c0024240700808000d60784440056400083c040080007654460305c000840191003099040e0007a5031901d40049407655050b0b40308051b2440c002180080616104020b131020452400054119002d6000040002d09150005da074415120400860441d696006c4da0703521620513282071300d0a8000c601402c04c1c65038032010b4420340301c0e0700412211382a440c0d611500750f00a4054005000a04005410a4581e0080001540b85071028008000e01a44c0f5100041035030014001240001d0500c01c00315004a07411409a054440d00030181604030701c0d8100041c002c1d03100020f410090402c682083d80c0c159024000d2141000d103540140198801614000b000b410041e0800014000030300a80c0810640c0012001d0542c0c000c6864800707262140c010740c0d458110751071031130510701317080c000310f200561030115000e40108400e03250200308989590f0b905083c0d02048460350b8120114600b007151514101081c41c0032640202c0280c1c00095 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 387913534 1250 387912284 387912289
    0x9060f010612020a0509130b1804080304030315030c0807140102010207021e031002070506270c011416030e030c0f030c060f22081005040317040201090b0a030f0606050309030f0c0705 80
    0xc440c5030441c1d2256520312488d0300741006040a07200d0341c450100f0305030f00c1c60150707039242c21800b0252024082540d01c203d0440018941c980910245402c420705200d0f9030f0703441040907980d03011360168084d540f43d0302500300d003954014000e440200760f00410340304110031b80030000990051005062945032240c948226003111486c4002d24145004202400007481c08c101d00541c8548440607400d02d82190f0076a221840c140441c203403a136100309181c020144240894840c2540c000c00c580302c10400c0b4001c1611003096004044036030705074426400d0300c2010500c00700f00198000321058441e00746d00a00d084100520300007000348440b02c030010866040c200d55440038001c07505030440c0900d40e60081c510600c25044100182412000c03204010310107031405580c000d10202031100f922140d00b502d0404182168026080040605440d4039803a8440014880080184c8113240a0300030b4185020001304403144560101c1c2e118035502d100a41c07500100e03034040740169000c1c10207850315004161020034141d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 387914784 1250 387913534 387913549
    0x702010f090812010b04050901030f0206070602030a0c0306080606130e190b01031106030c04090207030309050d030b090a05090316141002040501081008100c030212070809060f010612020a0509 84
    0x1d501444890b07848101881e82c100c21000c0c180c02000d072100f404d1008100341d80d118075415040d00c0d80a1010b0511980620200e001806212401000d42d0300100420002c1000c1d07500c1a4030315181c81d9810300a0b242e6a02210380c03208401d503801a04140d4000442c404d040c19a040008441c0513840cc842c4506104417000700030105240c004c03183d03000301500410030322568000320318030040203d0b151442e40c00c0c014031144952090b171080020321a000306802e01814001c0e0b208180d4581c0080c1900d0044d41d00903c010001c0011481d818131455a22000c10b030000d4142c4101031217a18080015440c0c204400d07613a012080c080c2101300e6407414203810086146a061111040d9010002800750700ca5041c80b001500396680240010719a00300204108070b14a00080c80810705010410005a69010200120060700c900c646030601d520060040c000c4099000070441e214100796010707a80542c4641040d001c0c141000c1c41100700040f0600401c0758030780d005174010103030b0700d42d0b40c100140380c0750440c404a0660f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 387916034 1250 387914784 387914801
    0xb0f0d060c0210050105060403030e011709010c1b080306042720011d0918160806060108010305061603020706150609060c080d09110307080f0c0111060a050702010f 72
    0x32036445003050105607404001180780d500c2400800e0050758105004541540100c1c40007500700729a1144084050340a0305200b400489030440030907040c5407070354405000e400601c142030000349412500111800d000303046888a658881581485e6450b002d08000140408405d1403011b24001007840220003003501030050103511a0f0341101c0281e2039030045c2840581d008a080b4184500b142c01024801840700c407054078080210364141882d110585c8400401001c0c881c4038080d889180c0e500342d03049045c000c140d0100ca8002c8100c0d00e45a030380300011100c400007840010301076070112002c228200c20144403080124590304d0010b040c08042d80b940c0d8251106005100c4075440204003e120f41c56018400b00090901800c000d00c0d001125a611200c902c182045d00d008240c3e14040441080010f009400322040d00908a415075070310b5031300a545034040c0010a0015104e4020800a15401425901d404c80b400d040500350030382d500c51245029100041c0080115565050f84580f20001d92284100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 387917284 1250 387916034 387916043
    0x906071406010f0e07080a18050309090106090308070602070503190c150e150603121201180605010507060e010906060b040e0a0e03030105010c1104060314100507050a030b0f0d 77
    0xd01490908490a001043e00400401c11000e10b0038001105105051034200c091403400b0280c681d900c0380d24600914100100884012440114205020000003c1c00040008a40038840342e42e840c4029102c1420501c001400c002041c06442c021031401e6000c1d001c0c140c00394041e6031a03c121400d290520030141c100c0398001c54410b0040c3c0c1c00b40089048400d0b00d01c0c4108004201075003500d00416680c0e0b40c00014005491324080c001002a2824892181a40c4000c4006500c552000070006d0400c0e40901070941c0c001c1546015500412882c040c40382101c2c41a1205031901c41d06454941c00341507950410390b0a50340741c50b07403140010f84911449000b4003050301880d44450800c00450b12410000e080e041c42941407481002901402108890441d002403c0c8080c00340042d261002007000300310181584149040800400d2145050240a0078240071080e9079000c40b0001d81041220780a0781c1c00400101c0911000c541c1c213000b5480540307070420040814030110401d4000941c120380c0c2400464 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 387918534 1250 387917284 387917303
    0x1508190c0b1201091b020705040e12070c05010206070e15090607050703121409030d180308040f03030f020a0b0c0903010f1109031c0507030c060f090501150b04050d080f090607 77
    0xa13030a458801c08515542c10000790501c90070002e4000d54032170040c0291703449642d48615140601c0020002000c0400c02d05003403584920860a24a51001d41c0b8451280075020f660300080d1080e1240d6895006520000d040c00e01403500441c4003901c54001406903500060100044400300d201000483d0046100300000240302c0e680c40402441c005090005034040391082c0b0900d0001d03039010410b0a44810300d4030304203038407101417051040c2e03c020fa03034009003c005001a0100703803840311030710040c2600c4c0603440d442d60320010350208030b07503441d400344026184805200214041114500c01070110b50b4001340013040715000d040f9000203c504034035072034801c5900000c88095905061007036500c5c103400515182001c01e101d50000d45079100b000c0c001410041e00504402c02c03c40f055000d2625120014000c00c00b00125240c041d00034081d003065200d01604000000030300a0401c0203c0781a41e4001d04600e000041d240e599554681100300c040800507401d11515400382c4680000c0c00c0014001c50428 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 387919784 1250 387918534 387918539
    0xd06030501181211120313020d03180e07081311063708010e06060412050303100b0901021e0f011401090506040b010c0305090a03050319031508190c0b1201 68
    0x80101c3c04002c0c1590103116104d81401500800491003c40107090040d035569241c2d140c643e01c030030071030099070003d500c45000c0c2036950516500c4210791380180c0031306841c9041c05440d080f40c0d075044842180c1034400180f0710400100150031781e900d041001c0b44218a12240c160708200004c0084d081b13900c400c852102d1a8030340400302c00340761441c84207441d0101000b140c60740005031300071321844050040d5440c1d0401400170455030f407156011035006198241c800164503044d03182c0303681c03690300649803000c5448a0510209103d102203040f00d045c0f41050300202540c0c21911240040f5a10700072100d00d02d8000c13030344c5c0d030151910213010b01e900541050b03191008541c10100c02d0b400b114400350050380103d152005004d080c0c2d0304140301c003a45030b405081140e240d203080c0c000580781110130b82004080c0d0202182c24000d01012a041d41c00104068600303000328076107d96040060210740c803400f00c640d8403400d14a0880810707400c061003c0e40c0036094400e00951203030b40c1359180d58811241000c0f00702000004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 387921034 1250 387919784 387919793
    0x105090f040c021005190b120c09070512040303050a0f1406010e032a03070801050708060103090f021003051504050c071b15120605011b02040b060d140720030a050d0603050118 77
    0x9035111f078071007241c00140c559400c5105541e03035810000d41c00c0c090345a64000c90000b5001c1c505644207480000d40d04c18071464545001009000c2c02c2c2d0310321140700d052001010703620f49980620307100d100d4450201c6503155110745c01100c00c8440380b42801e030140209220b04451400440c0d41103c40c1403810818200404085d050624108040d0300c001c038164901401d1104981d401001687c100000b483c01090540c81410075020312200e054009502500319000c4101142d0140c0009205070b40c0102083d514801000600059440441c1c10000075102080705100003441d0113007108800070740100107500c140e11a07005030480c19203010500c020800c030030107400102807240503080140400b80381c880070344008030002c0000c0c0d00308100020710940c0c5038611150592150015682807281c3c1c00001d1054046600060007010805d0326240002091280c0e0b42001100051000c1200111907008501c1e2840040c0101c84c0c0e60841640c81581c0c5403995000804613009008500014440380542074460149261 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 387922284 1250 387921034 387921041
    0x9090a080a030209280b0a0206010b07060b09271501090f0e060405060916050913030333060201060b070b04020a050907080906010501020d0e0f0a051504030b060105090f040c02100519 80
    0x121110748200007d1030f140c1d0b40414294111605011219250011494a0300c0507020f100102508901c01004018000c8442103000ea04900004c1d0075400d100f03586d050301030f2121501d281c0e03040f4945e03011004000b0030b03049600c03071800ca1088510004405400705026800d0034030544050f00d6580c013540a020481c0c100340070500c40290740d460a80e034501d1401010a18008005010000c0c0100403041441410301030f4003c1002c04c440700300c3c0e040c0080c184042c00720503a000d44200e080c291a0380000482c2da68014403070318054071060340c0c1d4281840d00c5030b034601e42001c00088c400c0760092284000040c080e212841c116005642c1c54070340140c03d00e856035044c0c6c03909405910985c1103600c800b8038000040d81020070045888401e8816082084411020801511066200d650400710820b8814035032410200640300307a9100e80172400c81a141c0c0e06c01120b1328000c0340c00b9180e014000b4030108031030307141951204800ca5564010388100708050b001c0101110011501c6400400442c1d8480c2c1c80350450f0b20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 387923534 1250 387922284 387922289
    0x405030301240912020d051608011103060604051309050105070e100f08010b0a091703130608010311132c0106121a0c0f07030e090609090a080a03020928 67
    0x1000e0031031100b240c0c14010403410052240550300e089200d0003100755104d00c080d0140302c3d81c11208890710601c01595028550756107102e150a01c2d4078020900d142c070410117003107a0003a000142100d050038101020480c22441d083d00c41c01ea050b80e50350240300043c0080c060544038485a0701d982c0c00d44820f4105100d040f181c0944a4001c00c14080400c02c020764110001e6410340e082c0d0f0a85d40c1d21804102da003510f082c002074005541400c2a5040600040000801041031121600b400820079940b40c000340c0d0340d981d00b0f010003000c0c10302300300040301c960603c000750b0042d01c0044440451070360701700b603420080c42d03c0503100c25480c0c0d8002c1020000c0b03801c1c01d018403001041c031042809a0104a5154400c110b4141300c000c000002c80d800108034030030b44401c10740c1c000c00400424941d0b1410545805000d056031404118082c504035400103580f07180083d251482807034008058040c50f5a16074030035505902c030240034001c1c50b07400c2c0704109154071a08c0c11640031006124200030010002241c01c0009003095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 387924784 1250 387923534 387923579
    0x9070e011e0909050a08030612060108030d1d0a0201030b01030906090c03061803051602030c030f0102040315050705090f03160906170109030f0e0a030609050d11030903070608100e0405030301 84
    0x4803c680029000105a2801038005041c15144e48441e00080d200e99036200904419118400020900a8000c80284054840c002d17040003881c03c15462146580c22041c41070205401042c1c544000d94040e0b0484141800d0524002440405540e5024119010708a06a401508000d42030040081c81c0c40f400207a02800400e40c155400c0741d40d001403641c8070341c000e038900c4490601502c1046490811904429000c0101501c1e4524510700307070a4000d420520094491070b005107030341c59007440c0038440c1a000f07000307581d42c0a103001d0240c400d004201c0380c0b80e0007082c0c152050714122f0410710050104200039003240750021070154900a40c03800d080c05403c00381a1507900d080c00b031900103600140c440c0804501820507520f0107440800103082540030364009054241006c0303541c030400001140c80d9041900c180c542e2507903030920098090703490182c000c400d901503200000600155000701c501507805031007090b07071010036500d900050800038000c0e10112a40d074070100052040d03036001c860240700603485 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 387926034 1250 387924784 387924791
    0x8030901033b010905190b0105040c05030109022a1e010506060318010b360f0a0e01060b070807020a0608060d110111070e060f0102150105010809070e011e09 69
    0xc041c0a02da211005000c02d285000d4800300c0c004080290440403113250010b00b0340e4062001608401c940c101400400c07205103080000215030342c03400f4414440d24100b56560700d81141c0c24190040c0081d401181c050035061038920f42488c0d49044009455007051001c03010301780011101e0055001000140003444482c0d0400e402c1060300d0301c540742600d51204400c001c0e42214038102214a00402600c1d000d2500040b4088440c01d00c2d40102d0800b41f410095480c03000c11200848103031401d80081900c0c0581c0c1031040c040850111421504000c0713281302000300004c0d0041e518101088180e02207001100c0c200f5001c81c2c041c00758500280c0c414000d00d03890a12042d985003810001e030148000c11402030603103412046150a50340701d003011051040c00001110000750b00d958410741d8150041f221680b0a448510410040d0b501c041442c43d08801d40042c40e01c420b900700300040d0b983d01c100a02d00121881041c10006040a121200c180240303a1b10794124041c0c0d010b4031050000c0d02c06500943c007010f09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 387927284 1250 387926034 387926081
    0x507020f0d050c060c1e0a2d0c061a0a0e090d05070f08070303180605010f0b0a050301210215090306010f0602100903030e0106061d0907020d080a150803090103 70
    0xc40c20350740c0810781100040e0768030300310510001c4402c43d005015800106c00710345101516042240b0b90000b40740c0c0f0b10201801c2184040310200e015882c1d048400148414510b0340c00640c058005950141090804403c180c006030003180104100e03510492000c0101070602110410a0140e070312403101a15002c1e2401503150ec56400141c160200104290390010b0b4034003c5c948240c1c0242100e0344901a81d40d42c3c4401c50038982e001d02001c0c024a0184001c0440004200300d41004840031102d140d101c160a5a280c4140b50004a261000a9101d801030003240c0005954051441e07103189940492252103000182c14980f4001c0140c2015244589080302030220b80e4002400640180207010003098209051030120702401402003030f400030f582000e44c04504244c20010b5246240700b10a9008011030b464070801c102e414068a44002681112411603030040c400d410301540600304c1040810008404021a1075841869208542680001c02c14560940e490f015404034007200f18042c4130030301c0c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 387928534 1250 387927284 387927307
    0xf0501020912240c1207170109140604021e070804080a0506010f1e0e13050d0338091803070b090c010903050c04090c0306050703050402150a020712150507020f0d05 72
    0x5c951401242281c03200400140040c0c41900b40305864000c020f1200c841e5652604400040c00281e44801185c24048000070071609080c4203031425a90020b0f10f45400741139940d00148558403120056555040c10000410b2144080101c00540c030712640c0105241e600d000700100b51100e40303400246582601e007800e100c90980035050801034401e520503000182c0c0b61220701d501c101c0c80c0c1210040843c001c5c0041510390320f41550003945568225107410b15007a01d002c0810340d00c01e0110607103032207031f0035520344016450411145a55000586805006d07550128490039469a003108800b00e411011000800c44800300074014075410850a080040c020b41c103594138680c40d4504904c5027030040303941c3c94100051110000c60381000f036800c18000c11090902d00320083c0a000e044070184d001c1d00c407a1884c080702203184e034102c2d991000c43e0360140036007a0500c0c11100048004c0e0300c0c01d448100350071142d48800c0219120305401000d0036001000f1030503042c070f00326041c800c55500d80018001e09004810086 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 387929784 1250 387928534 387928537
    0x6030f180f1228080a06080a021e0118030c030201090909030f030b030c0901090e010615090504050604020910080105090604021303020616050d0f0215010b070f0501020912240c 77
    0x4981216a83d10742001c4001449003041441d40310040d10015425002041d420032500342c000c0c0740c02c1d1340038001203071240c41c52582e2318203042c070081d00481c0c4180071400310342000d0302c038480700308051400d0103842c0c0d880310500c01400400e40064440c200d803e0002c20846d03805c2400c0900610400c6000d011104d0b00b070314007401500100c81903074249500c0301560b414a54003031000380b00d0620700030000d00065858500c1400140319000946070650b00c0e00e180821201150a50345100c240550383c2d80b03013498108000d000260402406140d000b030b80034481e06210ba51f4015022080b1074596036204010b40c0b40a04210a0000150030207010340d104000e103010151980c21b0007015280c040c3d0710f030b9070386130101040104002c50001c40504240100d264104510383d0060002d48400d05503403c07500c4c8803828010346804d1040c00e00c2580c10203181046014001024400400c003440c0c0600c00050810718036a0210b01c00241d84840304800740c100303500031500440c82404001c0c00d000305075a48101c503c0c2c0000e4501e0705 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 387931034 1250 387929784 387929803
    0x3030e0f0d03320c0f01050c0c0d18210c05040513060e12040e040b0a0c0503070e0f041e05090f0316110a0e18060c040513020906030f180f 61
    0xc3e4440c0c2200030034610351201070003504000860050381c0d18074a2071801c1c3e4581c540682c00305029420b00b4040f450180c12a000d41d1814a0404007070246440c0102c0241c510742c01041c0507021100e09607100085145044040c0d40280070205c1c4000080c04541c50800b00010f902c0d000103200304c1c0352000340455011b004003031160407940000000f50a0914015243c54221803e012000d04400000d0200342680a01c280a01a0380f0409408034030762200801001035070f4444e00444000b4400b0300c00189080e11914503c0c0040c200900f00344000700000001c60b081d501d011038030540b44282103001100c200725612401d81d1142800b4040c2603800000521075450f8459810020481801c2268103000d00c036401c07000a8400034000c0000359110350711b04586403005411191a881c1d5026000b280c000c5c040d02280c0140b007030301340f81900e610745030814081191415001904926180e8240490090b944071000158020041d000511809241001c2d0104106160180c00c40c2507400445034109100d90000d4032a01c07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 387932284 1250 387931034 387931067
    0x11d090609031603020c19081c0215070e190501180506070602090109080303040507170607090b030a0f020d0e0c060a1d15160b010909110d0503120103030e0f0d03 71
    0x102410f860070124078080d094411964015814803298030060410300d096401c85403101c058410354074020088444c18442c541018002d40c001c0c0074036401250310f4210b4150721244a04081002c0390a4001003481810760500b00e0803800c1c03c40e94140007541c0c00825003865200a942846001c1c0c3c1410b0104400d401000401004207401181c0034030268003c82d400303405401ca0808594980c907003810b01c03543c0d44842e80f09401040c1014451902115008244039100303443c251140440c07580b030b020610f50140e000420000c0314564a08000720317018011300080030001030030103011a00402e02c174031f00da0605495200203480740000300310490415822400750583c048003050101000004080403034001c1c000003085500020000030603408007400d120703d914950340141c04100c03642c1e89900c8848221400c1210251403130a0380c0b503041c0451314010f808503100c2c62142c01501c5c00c154851070320100341c05081e00110b000c644100784c544620b0030000c0301c40fa03001c070084811402d110102d8402425480008030005c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 387933534 1250 387932284 387932317
    0x1e060f03070504031407031e021c1704031a010f1809080f0403060c0305060406061209050a02030d020a170331081605010e06091e011103011d09060903 66
    0x8003920302440030f480045030070241141c070310fa0900d5029900c032180d6000440d00423000962174280d03e250f0010002d01954013a00420b12003c003200900c1440082d810b085881d83c40001d001d0b041d400003400600021803044011164683e41c0c1d600794540400c05810020104000c90000c0003d400c90b804900540410100000342c100303c0fa0505004520603242403224011000400100f0820306511141c1c02c0b40d80c0d99010040d40e214503040000395071286c418640095040080184180e0130f0740e00115019110342c0c116080600c1990110303007031111030b0600b000580c010307040c02c03800e2044000840840d60281c6100c1484e529120855986580b08503221844500400440718446000152010b404030740080d800d40c5c8032a070000700c01001c0d2101a07000c4441b5400c055103c4e030094000940c007401115001c1c040c000340c54104800307184100c0c692000d4542c0d592900c0520000750500c3c4001e49c041d101008001c03505001001c00109008009440d00c0c0041d030060040024280c000300c1600c003500c1d00c0360b843c1c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 387934784 1250 387933534 387933541
    0x303071e020c03070f06021902030304270e0105040b09010b0102120a23040611011103010603021c052d06010e06030a0b030f0d030c14030c0a030603050a0605061e060f03 74
    0x102d1900070349191003509445200c02c00715461341a45221802c0ba000307035007115410020401407100000e01004020341503441807200380440314000c08222204014100041604440c0d4900300e020782d0840c01c6404000e9643d1014802809005023200d0381c0300751032900034403080300c40707400003540c2c0e0032016030180380b0400c04100c0e0148244980400c00e12154800180a050250200325001c0395009204490214a02e403e8958455406000b890b000940600400d4150313032030a07100398007951148101c03010300000c02c210165002a6445580c1c052a070400c042d070f40300d181c440e0340b2040c90702c0b01154404040303104004106240c0e80c402c2c40d400c2442d106445103a1242c45007817180f0040c1c403001c0101540350041000001c1401c40010346140344009d030fa6010700400d041e4550a0340c0415154011302c145910400004a408030404020507100c0101c5c500084d62903074980b0303a5030421020311811141d090325a4144581407504000683d01d16101c0c403022a0100400000590b10340f0512100002846010002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 387936034 1250 387934784 387934787
    0x120912270105070204092a0e1302040219030c091a1603050c0109080c100c051813090b090d0519080a1103100806090307030e040b04110c030414030303071e 68
    0x156420291302070800d000124091501c1540d00d03003548454204da141410040341001e9403506403108407101d48111401c5516010321010150460303000c2a0b80068081201c0c81c0740700859151420102e1135a0782c00295020b03180001418000540e0114655422038804c074000400018116450b00b1582c152501c0301c60050319060f1290700610603118440c0d441d1000c107400740a00030b401030070002489030039200f500104c00d460008035a1412000300c0000d4081c49101c001e00003030002c50264042c01800d5040e070000c1074600d0f20607103080c0281281e00500b010103005a01004105507200750405d03051850800002c150910840292200030208000c02d88011a100303c94562281d94941108400255030f03161494002d07107800401d02c685012840b44500007500f4a0010041c0c0f444554181c0e150301c8404500e0b410000549600400241e1140da5070000200c42c2e68058007c0040720b03140805152540d01e800e07034102490512510b402d0094004004002510b075102d904801c90f2901002295203801c4c10540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 387937284 1250 387936034 387936037
    0x1206011d0a0b0702010e03030309070510050f04181b02101515080f0a110304120e03100b04060806061c0f0803070519020a030903030e01050d02120912270105 69
    0x400303400c11101d5201003190707002180140050360007a01c074030521036200428503aa91004413032000c05a044203105202500e000101d50814450301c1c54814140302103042517901c9588580d020072020300b10401c0340c04071000c050055651010f400c40603146400240384020351285e0f94032000d018001e0b5104000594512417100c0940a004403601c4004c821011040282c0b10079030a4600510b0b01c0d090b1000603c0d441d0b0306000d944000c0c0080d6045900b5500c442e40c03104501000d010030358081c0161100400d20644040143c80009001c00002244140c0c40000380070444109130000745054024400b0031119440f012910362010101c00340107003d92905003807102c0420070000004210880010500203043c3d40302002d0518040e01000c1c0b100100040101a60346400668005010580c00036082020038020040d1400302c01c018102246042910791004080b130780089231680d01050700406200002d00104080901039078070700d00c01450201c0c01d80c60716003101c0c0780d5010403a500e92080000070030791f44150b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 387938534 1250 387937284 387937337
    0x90115120513060204030606030605011a04060c1a090d03050a1503020613050d03050c1606080703050a0e071e0603060f0b09030106180504020405060603060a0603230903040e010803120601 82
    0x14800c5441755100c1ca0050040c0c0035510050f12030500700800032943c000c1407455240c500451902003031800d407611005640d640c8441a003a14484403003402d400115030281146d40c03140e803020000d000101240c03038000e4201d6202401a10825203040f4000c0d19201001c2000003c1d02e07011510542c5810b040c45040141c5200d5400c080d810a0b009202c450800d9002000f4003021800c2d4030a54014034600d00c94050300c04224803806001501520100e00028000e0340001c1c0c0144d0308210201c0d101d030315212454075003100e84d442621070701c205440015540d940d6450f01c0c8003801a5140900481c0d2400d101c8813040011030103020300040c0300203419140355509600241c01494041c0415180c00128408030001b001d00b11000d9000e41d051000160007071070940704492007440c00034146c480560401c50100c0c024400320324000e001f00040ca0685058a80e01d4124074400c8440d03000a43d0b4485c2007410b01d240c161010b074820340d200d9005000b10707410390340c00180613030b07000e902032030003210344903201128038546443c90 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 387939784 1250 387938534 387938543
    0x6170901111209012004060503040c0b0a02031c0605101805030d0c030e0904080322170306120c13050a1d010614090613020702060d021206090115120513 67
    0xa006441100c0b1140040e1148400d08020080940d4074402c001050000d100100c981450800040c0074082c00344014680182c0249520641280c80341989039607548490450301c0580d001080060305442104480c00300c880e070550b010300c605494180030411082c20015540c0501035030104c0d00024990254502c00281340090440d4103180550102500101140e00150006010301d480322095040003803906000300e03030020f00d4030300d5543d031100a481740029446000030120090241e20700810417500c00504242c44804449584c0e00780081004071080100c12800c0c1d550b0445c995400060b0740342c1e0703500b281d030100032000440c4583c0c62811500003402c40c0c181003a8086000e034078001200a0550040082d511140d4801215000401c10000d20200489039107038046440d00400e8155501600580031280c405450141032a00c1200000c060360003d0440880d4403e090741009918038022801d54018411500d4641910420340801441c04851041c1c00340314503142c1010900110010071010310760b2343c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 387941034 1250 387939784 387939787
    0x30c150c0807030e210c0c030307140c09130206030a090b070f111216030e0904050615040c0c030819020403050c090105040c121107211403010617090111 67
    0xc100c001e4041102941c00380c00192406035942804000014001502420030280c0680d203009a903500501d90302c02a03000c0c000d400381c10b1809002d83c4003000581302d1b0521032040e1003c0c40840a150614210549000e10701c5200701c1428401d0410031440e8100850350195801030b1f81e6501c0203680340242200c080000c04008640041204007984500d8180805046036906000d540c00d604440d5640d090141d261503500c00c00700001c90700d840400c5a0031041d1440b07420029034210b010b100141c001d41c0100c50540b1260052000c00c4aa1300920180c49201d41d0704440402c85003c02040042850000d010010140504040481d8024001440344403030944601403c0d50350750b0716841c2030340e00c84814941c0c45020b243e0020004c0743c1032030301e8002c11045802c1552503981201c042c290403006030003a01000e040c3c1110401511000c0b03a88501d0300403510070048169450650b40d024001c01020104502c040c0c8010144014043c2c158444214524441240014022034a50000f0b507401040c21060705241041c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 387942284 1250 387941034 387941051
    0x30f02150309010903022e09260a0206100b040320040e010f0b03070b270d080c0607140306060a1808010c02060f09070e1e0709050f0d05060103030c15 66
    0x1c150040d24032130380f19601740e600c62864180a0010600c021103080d07905403200c80d1311185401e05620500441d401528a48101800405480350a814045020744201000200204415010805907401045446031071044d14503180c03e509460160f40401440c5104600d40c0303404a0040c09070442c044400100100b0028075480d81580c021719051050912850400b951f04581e40b9011507010101c41c0c0104015142200358458002c0c000b02e14100d400d18400709201100c0745403920000ba28025100d08151540c50800c00d409602d89280105a03100704030103912a0000050070b02c05803500310700d0684159480b007900c0746069403d07988082000500c0e2413072600024500b00c054000c08000000ca0302130340c04a480d00540c91000210495640f961544402020400c101c500203845a00240c0340380ca1000c02e40c1c4200da000c0c1d001405079025070005403100000d024074500700154030000c01088030503203010145644c44d0b40c0c5840051002800f4440000c0300c682c144141d9226090310200d1071601041701c9003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 387943534 1250 387942284 387942301
    0x80606060a0c052b1b121e0503240a170106030f0c09050705210c0f1908010803070308040204020a05040e0112030f05042402031c050a11030402010801030f021503 71
    0x88041200324031030401d0a4130b02c078182d002c0d03000107200e004284a8190440b441e5100e41850411544c040c134204407100c0100002d00e40075821441c1c0001607951119542c0c10300b1603202d420030203406080c80d183c160001d41100295105a80c00080b198056805080c1503140036981d401490300d0b41c400340c02046c03001540c0d0104014800143d003a1510b03040100701541b50034800b12018050150440c040200f032100784440010f142c01a242d0107204d84080614200710741c0d0000140c3c5d0000600e49a49003803a00e51410215044000c0c5400741004200440c10142c40361002401c0000240019024640c00500310311018460b0040300e0190504009a00c0c855035104000c0515516a550a0740040c101c00b01c840c1e003040c403c80449085440f01030b001c0d411240c8200c11b20840c18a8404c050341584010000c1c041d03c1e01c0100c0b010141da88203400c0c0010b240c03900600d0801660310b205005e1645000801c10000140e0b00460600e0569030408100145080c051002c550942c40c003150910201401204001d0a003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 387944784 1250 387943534 387943573
    0xc050c1207050106120c03080304170a0302211605090406030c08030705060604060f05060d0e100e0f1219110303131509050c0f040b09010b0301031b080606060a0c05 72
    0x7144120000c0103241c0d600c0d080500402c1d44480020302e403454600d406c201090500001d5500240142604006144030a1400410f580710382d02ca040442d401081640f445600210510f14201c43e000c60070b01d161510300b40403282514900300c0141070250100d079200311501ea9030f000c0340142d58402c0782d205d91280c4900700f941c2c0c0d84e005404210381710f11490340000c180e41014040c2c4412190240d5403020a18203010400856030040288064216558003001446103000c0051180c03819110200040000301120302d2410100003140402a69001c4004550b50305038070310484001d402c51100c201541c446240c8221001c010b80c072201c0042e8840070007405046804003203440003c6d803007811031092180d52001c400e01030f65005403025160340c00c05151460310341442c0ca540004110003d100141128440d00081c05d00030080c0c0040c011004088014801c0003205400811040178465060785450300d060402075480c800245000d001e94001305088448602983c40000d14642c404c064445014540c030030b00425 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 387946034 1250 387944784 387944797
    0x110d0311031b0d020703050a03080a090609110301060503150f040f060e010b09060418061508010612021503040f0807061407020a03020c04090201020c0906031606020c010f030b010c03030c050c12 85
    0x40d030048030f040104650001603240c0481c1d610a010340902422510190703a250401809501019151840b03c000164036200d42400c1318802c2d840410074090030380030b25003140d100b50815130003644075a40c40903e22080c415100c1c0c0c041251098202c603643d40e4a0325880c03111442c5401802c881c280414849041c0042d0085001460192030111095031018200810f85500034640d0400c00885c444000109000b170708030071106a40000300b24951592041c025084511a80c09441c0d40b080c00c3d1695001c61074110300d43c00006064075003140c1503003441e0f1035644030034515a0005013a824001011020450a87c00c001c5140d00c80f10542007051500b003070301079240c02c042035080340180500c8044990350300d46886490406034040c8d00500c0704525030310901c110040060200e541c10b21581c040b94038044039551203003000c1c021990203480d0004132400090802d18081c0000700602d402c10050b40c0c40b03039074000004060140c051030f01260701030101c0c20544080c821101c3d00350322405030001040f03481810070014500e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 387947284 1250 387946034 387946087
    0x11120a0b010912061508150405010c0e132a030c080a051014030109060501120317010b0a0503250f08090f1c14030711010b030109110d031103 62
    0xa10006000440d00c5007000d003c0c0400c020b84030009200418074a502c0700701314001400c410403e007511810003a1034a03d80c1002c10030703514a520308110401200303015007003030260141003c1c5043c40da040002289595070044098805998402d0380940c0e40720410200c0041649640c00707951003c01c45002405043c5040d17681c4c000c00c0e4150b01041b818855446042e02c2420088860b0610604048801d9582c0e0901020190f0542d20381641401081c01841541d008003e40754411310440114030b406411180c260340c0f0f1400c40003640e0010002d140c1d80324202c5040300000d24200e583c0b60b0703401e240303109003282400704200c007030900117403158800707400031429075442e01c0e00e45885126a0318a40701a50302d542e40d074010110b030f80181c0c4060740f06a00400090400056038200041580d01390800011260011030324a40012a072440340300900c40c017071143c075031485000e400074401c284403502c0e069404501020b0321030040215014032001c0c1481408001d41341400340090301d50307540400d08242c424a864071002e40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 387948534 1250 387947284 387947291
    0x18020304110907050d09050c100908210306010c08160b01080f07080a080901021c080403030b06090d0b06040207020406030803150109031e1a100801060b09090f06010311120a 76
    0x20712510300008014840c15082c0d45451400e010411100058510000704907039503c90b5080c1082e41d9a5161010940080d056a900b903400d4504070500303242c1584032080703003111003490512405e900c44080031254040000c0c24868040601403400d15032520440340295100842c0c4d500078030411600a41c014100c2c1d1001c400c540d1503554581c1c0c00380e1603480c0c6100c0c204642d0310030011007002032000c5004d003125090500580349507000b0301050b4600a480310406200041d1201c040004140c0c0501c9190301c544010b461807030030b211024011500d00500028041c00c20100300e80054051b9071a6011118619800380c42031000365542e142680c81c076081a200401c010015481d0f0545039407290803010100d03034101c100140207070f05250348404107000c04507003a1003912180320300103003140f28100220b001d4400301440b00c42541c80c0c00aa0b908441c056002040401d000700701829240c4e0366090920b80250100281840645030840160020004066504102c0f41e01203110b04914541d95080b82c4540311101b401e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 387949640 1106 387948534 387948563
    0x15070203120906070906210f1d07050f040903120b06070f030f14030c0403060b06130e0103060b010201110f0d1512060f1a1002030418020304 62
    0xc20882e8000700c04d002c0c44e958081d08100040000c0e20300b8402d07810502c2840d01c8075414483e42d201c1c0c40c0707881d81e0301035a400089a0040e2205c230482010049400c401c00b4040c1c1c1c90f02628421140f080140e016000014203250040e10180c550564071002a02c0300714081c200100b103452a003942142c000e0003142c0c0010591300d903006080780242c98500315600d046600501000000300340c0b040d140010300a00c062580510291420349600080c007043e00c07007810002c200c8600402050b050940905600013520320074400f00da6068070301131345050003e1642030005a0a84a0441c0d01c016500410031006e104000201c1c060300000d2440c410106d00011410808101c41c03015030040082c2c0e00d880502001000200d10840c00001808442808691648060741e000241ea01d0030b824010f50340b60480c00c209070f01c02c0c011500a8001e01040400e030700803181d00c8a00039003040f00c00301d50b10703003c01c0200d = true := by decide +kernel

theorem cover : BRFrame.Cov 387769784 387949640 := by
  have h0 := BRFrame.cov_init 387769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 387769784 ≤ n) (h2 : n < 387949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
