-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2852
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:58.935315+00:00
-- url     : https://prove2.me/submissions/430482d1-19e7-4d7c-94e7-d1718598a526

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 512769784 ≤ n < 512949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 512771034 1250 512769784 512769809
    0x1050f0111100e01020d021b010605180703022b05040c0b0a17100302030a110411040305030a080405071a03010801240b092413050a081b0d0b041a01 65
    0x80d90304180c8446141242c56a25075450307021034000c04007503040d02d03250424042d04569802a594280002c81001c2034408160740c00c200000c2024188001001c5550b03a908080402a40300c030041500a03411541d021b100c1880c00d0440128500d04440c80c6100b1090010720010701070500d4201100d6086480c1c201d2000e0710810428a4205039005001c0c80c0b0100d55032080c074009849980d103a985074250b651029515125003108003003440300342c0f0080f61031041d089800708080b00307011540b4030080c0241e100184c0140c0080c00004001806451030385c0d4854802c5042d28481a21216070402c114000700c03c1c854403440100041c08017460904c101030180024904946c2201c814840c2c920066100d03000701952280c02041c588901c1d15184210901e068015403003410081c818403000000e9008401400d0704020114030008081c00c0c041d80038010340d10210b000d0017078005c0c101c2414008a02c070341603140d08500ca00e1304007008034025038529070150b40b14900a004850504866080103281030f000300030700249 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 512772284 1250 512771034 512771057
    0xa0f06060e0a03140f0601080304090b01020d08010303081b0d0f050903160212150c070204140108100b0604180b0a2c18010903030e010c14040509061f0801050f01 71
    0x2c0d02900030007281e5010180c181030036605813040d8184500410b480c40c643c42000000715990308080054016100c5110f0200403c54464004a94a0350441484008604000c0050020a1042d80f0b1b0381e40c1308403000007110900607103841011942d07000e2482c643c94071303070b40d0002c070003900d80c0c00c0c01100d03040407007100114107125401c01c03c1409140c5440e0700074400d405c45980e0340038171882842a03810215004603503807070703034a41a000075086501100e0200e200320300e0181c120f0800e103025808241038440440041c94084051006407000f400c1c014031103948001c0911000454a1148418540350b5601c01804209180c1510a10a05502a40003076411801054404c5441183d006200035540f407085407190f142d0300e03064031810904e01d44002020855007448488410300d03030113070440304143e15070750020841c481110f003084a600c1104400f20b40f1804040104118900d46a414035821180080c460424000c0019002c03210085140c7d201d0089070300000104624500311607840c04846080c2000c201c0c052 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 512773534 1250 512772284 512772289
    0x19080138060702030f070303031b031505060d0209040509031b06040503191101092f0102100c03020c0a0b06030c04020403151d0a03110708030702060a080a020d050a0f06060e 76
    0x9094550315805a140820410195581000950112060f400a540d03220f0385030f0900402510881c10b10503a401c50032500f005550b0310a10030307290618181c086030003c0314244010804194004001044180d4003800076028680d1148034250003100ca04c001503a59074030b412081e054a00144102c5042c64101070b08020101d01d02104a40d40c15078002c10404040181001c2680da8003910f2000c00d40350f41c40c14012004110440000b80c070900c0381070100300c0074101074081290312002c0f4460f516006800c51942000c045e4041e420002031a00d1508000d401c280d10442000d241006030350040d0341445034442407049500301030068a050074400d840a5207021308549505018840d0310300004002a0348640c003411101007503681c1c03150451030350b040c1c816840c60b600f402401c0038211000e619183c000c000000940c0c90000080b180480d6025100604000b1f000405540d4510024038514040e502080501d164503400d1180030f21401642d100050030b83c492007508000c44504e80c004906006240440c5913545c0e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 512774784 1250 512773534 512773631
    0x181b02070603020310090906200301050307030209130812100e0103030c02060310030501060b0a02060f0106080c1c0914011b320d200415030506190801 66
    0x41d0307010b0030090780e640c5441e90788a40030000f580c0a40001440c0150754820801180c100400f404501c564441d00d500340c0e040640c0e018802071092950641c400700d401c10050402810307456001c66031078040c129801507038840704290b03800600d018510980039001c00104a14000c4280d0103843c1802260545606642d009424400200350180c4100343c044000780d0500e805602c12005141e01c0002400156a1203c504001d40c1040020a0140c0504c1d000103482107069074009040700d12a6854580390b03141c8400320601c66204007410b21803050700070007400b240e0130705000b004412442001c0c107100700317046d0b4011242115030319000e840c8540407407592070341000d0340000500c141d203504000034803c01c0b948102c0c0c9a41480e05000c001039141d80854100142419540081365442c080f880400310206183c00850b40b521450203001c1c8004521003202110350300c6a4451680000c01401000c141030403145040c81c00c2000da0301c0843c1c0c607911036a000203052012030f80001d43c00320401d45c2d1030380c81c4401100c40780359 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 512776034 1250 512774784 512774789
    0x10806040b131104020d090c030b100909080301050d020d0c0806071106070f1809090f1a040b04030804021c0c030c050a05031e0307080d0515010507021c051204181b0207 74
    0x255008500340b104d40809a10819441e1f5000e440c2c12305090380da01c0c24000c400760855002107980e10000002941d040740e03014039451580c0c45044207245a091000b0411400c028004c00c1e43c0200341200303c000000d80c0c08001c403000c1d2280300c00801142c6408000145a080c2540010805400c4102800303101c0e90048030001f00c0d610682810500d142240b4504a9011019846540024103001c81e120905ca0344070386000c07005000d1003580c0060980c840480008100990f0024003110b40240000c0210380308461040d0400d01c010410184215991040341a000c68450300740c540c01141c040c1001000a4a8070290041809440c50580c0300e01d0100000e4651407035a980307161411a0301890084031100b44100c443c002c0d8026111038640c04801810f100400b401c40d03041c4903240300c41440006035800385042c0d4100d1a07004201400d01e0f04c0750045100d410181c0b840c00c0754148178112402c00851603c001510103804102141d031305142000174100306442200744003680c0311044100060320154089014401d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 512777284 1250 512776034 512776039
    0xe0a090b07031b0806120313150305190b04021201170c040e0c2e021c18050f120d050a0206060a08070b0f07060603030504061d03061305010b0405010806040b1311 71
    0x4c1d80d42d14180450035180e07070620b00c50306601000070340344911a041002c1d0710994034400d00e0000c21141c5580164210342d01a640302c0b14200f030204183c0c1207484160040440b0712400391000d400d241040070600c010401c00c7e00120b0000ca880a06040003c0e8100301d881c0101c07000301d6041c84040f642c1c0c4507050311141d0380200b03e0f000c2c00911000320501c0d20000c5010601140403840e100000156150003900d80e008940040e13106840c52194030601441035000701429296682c2c4049402c0c40c000c1003140c44800300303012581005005000580c000c2d4144801e40d984045901d9099540190700802420100010600c1c1c0c480e488a0500b4480c0b01d0f00003650000780d40703035800041d6946a40c11030750751244c052080000e249070f0a2101c003008065101010340708035001ca8544801318081011381c0180796001d4002c41c1d40681c401c1001400c1e1100003d104d118142c050800040c9424041c8040b906652090301318181603070000d403e000800105101c0c00d136211014100e04403203400e4541d21003043d040b03c100f180b803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 512778534 1250 512777284 512777297
    0xb010501030e0d0e0f04061505030402010f1112070312050f2706160c12021006080d0c020603130f0b010303020d05031e101203030609051b03010911040e0a090b07031b 73
    0x60701078481c7d80c0035102909641303480c54040940c00500038800d610898080307001a212140700f03500140640231100541c00f620002d0101d05001154102040d041088294104010305190a054204500c100e82c0200d5130000761240d146001b0700585904010a10110f0140140b0103078404d10340804546150014082c6c00208040103469204680e211400c83d0040d1000b00b540550440c0d9a40000c0d0708100c044a0710000d01c1141d50307030300741c182e1504011303581c10b4040f603c4075900100505d041b0000b180c1c810800608a982001541c03142081500d01110489025600c5130051081c50f40401c0300e114003688a1074014510710f4020300d0b9580303000b0311041c400303801181500850190040e0350315500141a0040d0701da0801501814014060f2010b03106415250385008041510a1200d409421420424548851869203800000b10043c0843c9600f0120f07030740140408121300c428a00c4041c040c0303c1207080440d5070f0590307091880c290310000d0011028503241c03c10301c5c100d4904401078015181742c03505220 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 512779784 1250 512778534 512778559
    0x603060b0609090c0c0a050f0a0203010506090705070f08130801060512160b130b030703021206031911060f0a0f0e04090209150411032d09031b120301030b010501030e0d0e 75
    0x16203006e918403001045030040c1c001c00c4600c0f1500260790500c1d58001c4000748400c1e2214002d01c0700111056400e80c0014600b044214042501c070109030100070310894400385090712400c05c0344820027040d00404110b9441c0c550030081032416900c5035803502c003141c000d445280903858417101c440465100d48108114040380c0303641e400394940002e9004007200c0030541c1d942c1c548150010020341c0903c0251052201d0200801c2180c1030014001303030102c4540800c80549603168503038001107101c18006a9101e10100001019850300d64040c000707003065502c0700261241040000350030454101351180c00780c0d00d040c88070400360f60ba5401d030541080118500c0480c0c4640750000c5001f5208520060706120000000c6c801110010030284041c0312010001c401c01c22011030a030700c2111016101040b59034000e1296006904048145540ea050312008861407404800c0540c03c141e0001d038401c5d100e006500004100d2541c00d40504030603841c01d80c0c0900884005284003500c1814502c0505000e1104000c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 512781034 1250 512779784 512779807
    0x7060509011103090d110907030e1b0a0807090c09092906071a09070603090203030909061f09050a240e040f06080a02040c0c0507052e030603060b0609090c 68
    0x1250355203400581901d8880703003941020b0032800c900a86c0709005a0b003000006080c107109124150850b54443c01500300c0c9101010009004118000f02e15800400d010740040c1c50007080144000420030502e010808110586011f40208129030003007402274200100718640030440c0f0b071031465580d096110106104202e40c08103002d4003681600504110700030035040b518040c0c01201c5485000020111032071151124001c405a804101001790103501c1403140c1012071904140455000341c001c0c0c0460400e0138400003003000e44034543c41040110f00080424020b50421200310400303490510f0750302c1c908030b079401514040030017101400c804001c0100c0c1141d403a40d8403030700b201051a04082d4117001e0140c0304e40c0c0c0c51391a005c00100881c415403820b0401d9440300d001c0c072418030110b904500036107407040c030700f0080c81840e80000c5000c0c900182e40e01110406103110b0250301495540955002403214154034100c001c66196400c828415101800800b00c80d42c0c8a02605502111303070343e202030302c81800111 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 512782284 1250 512781034 512781037
    0x50c181003032d02100e240403030b10090e0105010519081b04230109030b040303020315040207030305060310060b0a05070203010b060c030d0f1505010309020a05030706021e07060509011103 83
    0x2480f040c0c0e800f015018107050380024021a44000c0560800840c89410202075862001002003090481503008901d4070101c0818095403003406402d000c40e026800200086551b208070726082c0210300801c4042c0050541640c000b400f405003824001c0ca41844003c4052010960030303000420000c540001451045a03000c07800903158840c41c00e56103c645070b50341e04644510482840715075000e401090070166100702c001e40d049036003080011002d078803561001c4011f0340c0000e24480c00b125810300840a2500c1d644000d11200b40203640c0050a070904008050900107000c1400500c03d0030100c040c8400b61105d01210219945410b155a4075804c42c4046400741c81e00000c810352100001c10b040c4032003500800181078100d8801010040b20015222150071109100722410303215000d200103000c0765000364402c1001a000030900075440d65500700081c5440e01640000c0c00603040b134040c84480c0030040c40c4030071450001d00054100181030440041c80c500400308410704000521744050b28083c1c0510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 512783534 1250 512782284 512782337
    0x15060a03110309030a0e03210a05090d0f0b0f06030c011803151b1103030402060a050702030d0302180604050d110d14030301061419031508030304050c18100303 70
    0x41155849140c07100000c1c2d100c0d0440c04000d000308000506c803454515000c1801d18152020702c100801d10000200c0c12103094000791000002d1100c100070240182ea150058109101d02c5140424100c88551400c044104009050440d44010038018011300d07580214491000d03040a1900c2a82e10750740c0490108400303040d60003c0d08059000c100060005140e400410307010582c10941c040b01c00781d00e01f08441000b0042ca100c01d00b60030900c08a001840d1200051104513500d140c8a0705140a640020341404d0342030b0140e0022960004011507882c80a6856504821080750380904213441c08000c079880e07030102080102440040d0040c00d015a4900260004540d08003141414565180365419560b40c03003802030201050500e080d0207090030503d0129075003400081d00c0c4629003040c07410154080c0400f2081c034030800e00f0141c4040365090041000d1445503000328000c20410118200b4801310b2008900d0040c0e101b40944108283c0c0701100354a0b20840e0b074103251401c501c10101507650076602070003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 512784784 1250 512783534 512783561
    0x5031905270f0d051014040305041802250c12020307050603130f110102060609070518150706050619050604120501200c01050106030b0d0f02030f031209010c0815060a03 74
    0x520300141409800903401c0c2d082c45007017804100440320340300d9180302414102c0300140003d80412062200d07056045100b20641a0b00c00302604001c03c51040720310400c0038000110502800c1844102842000e00c102c200510804c021000503140320b4011984891160203a039026500002c0820001d100115443c1030799a0408054080080640381004140140d208003a0041c464000410501d01d0440001c501031b541c0e9454061074802e000c900f104020103075039034040d0b1011000d90020b444076941c60041400a00c21240000e103803070401c003040200a000c0c0c01d001090301d1400020721140d200d1800711020340315811009420300c1303880d19120740904188103c6558145000811151131480d28026040c40f2140c08024042070fa00c0c3d18040b421103000030300d1680d120381c001070f0701c00200b5540c4090905150020f0151241048103c6420386150300c0124140c00300d910040401c01082d1007031081418111142c50704035114245070f80301624558a1070001442802c0000d0b0800302240a41d014086240300d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 512786034 1250 512784784 512784799
    0x280e0c06090f15040801050604020307082d0114040501150828110705010506040c1e11011404140307020d0b06040e01050c0d2307050309120705031905270f 68
    0x21078000e1907005841788800c69820100450b80070b14045c026130f8803400b840d13981c07428540e032800b41c00e13040c81403c1240500350b007040080400190000e885039074041d00c91040100041140c440600045801c164444031901407036280301c6440c0c07540601036035081580708800134402d241b2704081821070380e0b05001140f10035180440d042c0c86204a6400b4010320b6000d50b000f04103039a00d580621003a160305041d10310020700d8201078100c01d100f8502c80c4011255a03454002162030554005508664102c000c014900c0e03103541c100b2080051402980508a095001960500e41e05a000c075039054800000200001440c10004001e80c841c0d80c0005140e0074454001c0c01030741081111850303140d100301c11081d001800c202030b080c0f0602e0341c1c02006a50080c600c85280e0326949424007200c0603000501103800c0d5000c0d031407501c0305e5009881c2c040c1080324000c102a40d07440020311178074011024642680c1c41404814841011024212000d034a01e180003001e44910780b11000380056a0080750048859200f00b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 512787284 1250 512786034 512786059
    0x2107050c070e16230706050f06041503060f020c0316050d0507030203030106050318011407030e0d02030d09021216152d090819060605010c0803070e0109030803280e0c06090f 76
    0xc6e0380240340603441c1c80c00716940c65150441844140e41d0b22200904060118580820010300c0795880407040c001c15a50040c201351400107032030b00755440030200342e88060f85400c03807205000c01400b880603100f20038100300340ba296041d600a91280014801c2c1c8092040100c0050358411030041d240c500c1c8001d4200800104c0209101e2012014041c4e414034002441c1c00380c0751002000c0007136001785440b0781d80c00560034030514104081c040c288403441242c1000003080441800407040003142d58003403a6030026a02c1c0d509000d01004903000003181501002401014404481a403402e1132680f1504800c11500102d4814001d64211106504c040d1551146003248010701842004001d10248201c0307044c842169034200455049501002c003500c2d40c0010404200140c1c040c8965a4507000103061010002e80d8035221072042d030300101c841d03002e070001c48620891381e40302d07180346170360b140d40300381c00412042040807a400d44d20303401c1a444601031040001e4800256031504642e0381010b100070701c117614114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 512788534 1250 512787284 512787293
    0x70e0102100905060f06041e0b0a050a030302101503030c140a0803010605090a0f0303021f09080409050403080a110f0a030209090a060f090902010806062107050c070e162307 76
    0x140464070084402c5c03560021413510302d414010411060418049510f56000a141c441e0041501081d401d5112944540000310f030380b00c0d8003030480118025009451801118080704090764044038000c8450f0500100502c00a608016002030007900000d20f42510031501800f9494441f40c401d0241940801000011304240e1100041c9008032045e01c10510310f81d600c0d0709400342c00304580801000b582007290403c0c07104030400c40046140d9034100002c41c0c0c088054486010503400f40d04041c08041d141d8042000b45500420340503000756080e00100210030340c0110307500c1c80b4091210322010000000882c4840c2911940664802d400014041140c60403c190010007d001c148590600003201040008007014580b04546125406845051541c0c3e203131420840c1950007c40c0344c1703d071400405030031000a2941021144524042d841d16641c8002c403010491804011750b03c02c0504541000810101d0020316407003249008950600308502c54400c060355414031002c005102d00100e001c1902c0040c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 512789784 1250 512788534 512788543
    0x2030904090605101a030f070903081303200a0b0a02160e270d0c1406040309030203060a11070f021203120421020c12032709061008070e0102100905 65
    0xa4030106101500280d4442046490340e000c0103002c03241000c107000286d0a461f266a646030f01202c146004e112040e100c1d69414200d4102c10311803104100c0c0720707006008005a119582608444510780d10343c08410803000610715041c18000c0d126002800301c4d118440e03500810001855074004401c0031022034840c100000c150008032404002c591340d010884850346c1c44c3c501800c40f0203004201400c0d500003100000d544003402c0c0c2c9021a01400650380c180b00200003807000c54019440381c0d41d003c0d1101c0c9980100b602c0d0a0300500324609080c9011200205044040300301c0360f08540c840c0b0007410340746407400000c0b20880801038580240c000001c414529486207403086200e40c0c864044407498140a0405420080041100030007592201282d18138500c1d003c0b141201102c0c0140450717117004a10a02c0d810841541e07842007442c09030003031941c60640b404801d0b030ba034440300540356088444411a40140f00c40e50240041c81846040c20381070481e41d20034004000c09510403c0144a46a00361074016900c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 512791034 1250 512789784 512789791
    0xc1b01030f021c1503120503070207030c12050c030d05090d08090907120f060510030e070b0f04180c0c02100504030803040f060c18360c090909120f02030904090605 72
    0x2550300d8020000028040e0384900d00a61b908519a0007504980b898150380a900160441c000d502c02d1010001c001501e440d841e00c09000b05041c1050300301c2441c0390081c60503003c2c4d001d0f070744a9040b0000d100c40c040c0c0c1c800141c40ca940380850b4000504215800d180300b5601c507980886030481100c20070804141d403c241d07580c40107104d00d1007c02c1036401040c4a0021039016000d16030b8461406104545c1d468801c0e00607400b004200019140c0082c2ea9011a00b034a40c85000c14503814003003c2010046a00c03044502e40e0a202861424004129803840c010800c2000340d100a114000204900c01c80c584544261005183d04c00411541d9052a090580c0b14400a010840d202400c0c9403441c2102e9204004100c000c8a8203d200d80e445400d21081003020340c60180380b5281d805110400701140f42c40240110700c80320b4148030003d804120100014011143c54004040303080c00c2c600742c1800556224081c1c10362000614140303a11600c102000c03429407180c0c000d8a41d205040c48800b40c203000303055002c10f01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 512792284 1250 512791034 512791087
    0x304030c0209100b03060f060d060f15030e07120503070506040c03060b040b0d020418020a0b13060c11041503060212190e1b010203090a14090105060c1b01030f02 71
    0x51075510040001070420f0f0138003c01200400501c01729071a8200000c900c2e03012100203140300d0500e81e0880c6150308a40440e88541004440c00c1001c0028030a0789502103004c440c0c5260034410941c6060341141c0d81c0034144030352108591400b00700028040184103683e071040e40002540e4071410141072503a01c180385400b0035a1107501d4805480d900b883c0510900417100005000c10703a504407150204001020300401c100000700c101c40b441c02c0140d42d202d4002c00a00b918807005519098500101c18034000b01e904000c05000701201580e000c41e401d88038148106208490104807400381d0410074004844c554401440307140081145042d421f509d50b0064480d0661124106035155020703500815180c0c000c0d081c80d5950440541000029800581400108010300490707181881d8100420340036078203644101aa104c0302014500d8a00d000d03540280104012035501c0d040a0100708410344800a00c440c0788620b034610303081e260142e4004d412041044000c40c10071034441110034000710500800c9184540c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 512793534 1250 512792284 512792299
    0xf06050406050f040b0a05030a0303091218031712090c091515031005060714071d070e03100c0c02040b04020708040e07030b0901170d080702061306020d020304030c02 73
    0x502400c05200768011180c0c01031418829407075010a01c070040c10030100d450380000720700001242c103450400404102510a036000a41c20384241071085004c40040c03045803c00000343c0344a40600f028005840a80e5000400750890b1042c0c62002a954804d00c0500545800d403501041920b0a011600e940c400d8015140ea01844d51001e003125090045460000e5000d62070400c07000703520703000c1e00c0916400b018154802a40c01c0c1c4550025010b50005241146c00c81c0c080651001610702c181f0201c0300070034203041a00d04004070f6018040154200401000c204200142e52a900c1d60302041001035195841d0760400c601d918211004200c500309020503401a820864402d8041c18940b080362203003500001c2c0642054101203400a054601400340400c01d0f40351030340c2007082c0d503030410064003d111103d940340c1000180980e040c104400302006505101d44c20080250310354010401c1c0ba407005a81d5002c003207100d00c40c50500000d019192501940c0c92000c0204801c00d5000b4440075103290080b140d54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 512794784 1250 512793534 512793539
    0x50106050d1a060a03020a0207050604030b01081005061c060b090906100b130509060a09060f1409071e0c0609081206031b13090501090c0306150317070201020f100f06 73
    0x101a0020300e1415540002040181344c120354407a45c0070f864079880c030788140c0344495030740c0c400a4043d4109400581d5400c0b488001009183d104114039156040c80000c24070140c6030000005240c1c000e410680c0ca21200c2c1c0310803440401000c0c0e4040030240340000c1240803a410140d460940e90841124540000c40c0c001002262040c011401d8a8a0349145044081000e003000d00f445100c102c09402207411040106c00411842c00a014040140862240580c0880d2078041d09408860300ca01459000d42c0c2e540c428130514552010380380b0070100c2c28484102200161f40e008550315480c0340406820117150411a50410100000400440141c224004140d44030781f000c00d07480b0451195500381c3c83d04900e0401e000e0342000204500503020368007000903905032640b551030070740d48021300488818603000da003402080a503105105d03000c14114090507050b819a6120000a20503050041c45403c0c08109042160b10800c146481d041c2900c09948201000410000c0681100021441400d0612402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 512796034 1250 512794784 512794811
    0x507030f18050723060301090b030115051c0c1d01050a06110a060c02030904060801090b0a020c0a0305090d0c0e01080f0a120e0102011407020c09090715080c04030204050106050d 78
    0x5000040750000060440e040c41c280c130784110403012007410083caa003615110440d55a528018500030450f8070b2010984050441c00c242c219400144250000b1000e000107224030b40318281d1040d81e03200c80c80300c40050203050b4180700c01024810707030202c02c40168845144800d0f000aa4041d8100e41c8203981c1500f2072911400180c4291034204002c0b8003680c4090b1031400450056003014000d00c61a0040e68640000c580c0400e00b510007039041030f24a80e4580e40310900700120401e01a80c0407184200c21800d00740048074040d12041c100303801a04004000c1800742182c0d461681c0c628240707038407110709244242d0760107080506d1402440340c0c030507170301801461640390040410044003d6501007412101220b1408082e10203500c10407a0320304541d030713030788540c544a8020041a80160710640061404001100070481e6010303006000005070742003050108000113130803190800500c0d603814507144d01d558100810340f203409a40e0001e9070041c00d00e000002c3c00d54200c2e0080c045010449414000100010403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 512797284 1250 512796034 512796071
    0x5090c0d02060d0e030d020c0f0706121e02030a0b030601080f03040510051b0c040b0319080304171305100c0b0c1620040b0a0b0a030504020f03010507030f 68
    0x6180e8000045002000040c07500c00001c14580804a0f80060080791495009203941c024055400420341d00007841440c400c0300300401b108078400540206a41d9003409002030032076003d064010310807501d61865502080001d60418485504004119140c4c500240d0113030190290082c52402030042500102d04503101140d442c01c0049410b000350301c2c0c0b074940014460350108135001c10040140c10f0000050007102c161081c81000c0700c41c5c00400c0d080b2500d904010880e904014503030702c85c0d402143d80008109220607021705164001e80607540b00c7d5600d0a280107076154900c0048024040010048280b84048104500744d5000342c03100e48071303000602070a982c0781c80d440101074802d9090b000007450100c03581005280f4054aa2291500d0034081d40d19000c008004002503000e00d4800107209005041030b11030040c03203071021550b0b40581441c180c0d0404180c42407119041c101601d0740001380941d01c0d03182d050808424040d00030025860300b04070041c010410307004401111818014001800d501108 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 512798534 1250 512797284 512797303
    0xf0e1b0a0515220b0a02010f1503030926031209010f05010506070b0702010e03040815130b010b22031b0b0301060203250209040c03030206090d0503040609030207090f0605040509 78
    0xc0b002d40c90041c03840741d07041400140c1e609090103c04100c0300451003040480c0600160a13040d0000301e11301e89261441000d5841410411074056050002080801e600404050480720f1001800040ba9107042a1035446c1c6052518003015200005803900d820500552a91150402e00002c0041e0002040b003401a54000c2c803c5603480f24040c8a5500810b41c0b013451a500900e141c0000200314039000d05032030840c0c01550008107190011070300010483c0b2000c42081e44007242c5060410340e8002962440003010040c091034501d1080481c035145010740002d5407125801592009803802560b074500911031085241c680800b00e500e03483c000034040115030a903810784074190051424800c401406003140554080903031403594981c402500581c54001046009501a1041003040c07800c40c2406403800745d020700060090390050003013019455229054039002503100c038010611500504040f840c101460f004440541d2820310004101075040d4031007803c651080d42c0900895907403054041d260510719 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 512799784 1250 512798534 512798569
    0x10f050103111c15080a0c050d0209071d040f0614030a121d060f04051008090a03050c030d1a100806030a0b060619050304062403060f0e1b0a05 63
    0x140900c1020030303e00b028414144040281c0081c442540c119a000c0b0a4041e038403001154000031140010300102c1301b01000a003505841880304d1150036400305002081c0142460b081041800119441002c07030840318140d40300042c0140568480807031002d00400440c071808095440c01030001d02981404110760601d00c2d00104001d07000002a041a1900300003200d10b4203d52090b58400704c1a5a41c21001c2d0021a103044402e98481d03050005101a07003400100103018091400200700b0a1100084c000e0149513140c6000380d2036144141c0b110b45180a615610900c1a00301407a031110b2000e011594890030000301c405900940000d017081d00d15090694030316405030050324400020035600443c89805c2800035001c103103004c0d10001d90544c106182e02c0e106000400000c24481800001e00030a1110041c0301c803100007018211404092032485844010303c0940c48848184d020001540015540203c1030300b584c030417041d008104000140010f04c5188143da40082c045000e00700b1019880c0c5614a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 512801034 1250 512799784 512799787
    0xc120302030307110d0c060b040b030118020109062a030e030114070e0612060d02030c060a03021201210b04060b1c06050c0f07030309020d08120a0615140c0f060f010f05010311 77
    0x4a0b00c502025108c4812000d400c05d4462180702c1c1e8645091080300e401c020080c0d00d00106d030040f0f10004013051a984e0120b410403100d80080043c02510622145d6550754403440b0115140307540c501170f582009504040c035403652808401c01316582c4a50403140c80381c102030f039580305040700c00000c1041c0e03400384190007488072580d41c00082503402c0118114071a1800101154800a15035000400a9003c0240781000940200d110310410030041b00c058050034659556800d06000d030050303456803060046001d4480c1d50210003281c00d0001c03130340c8210385a00c000f400041d150166401d0440200d850040b04031520f92820f80011182c601d04001c3e100e00040220302c99140c85034545007180500185042603070301011544500d000515480d00034003035162540c0d1840131916160320120200c0c2c0c1d0740c2c3d0190450111b4102582c50f901d50045004c001071500c00b0b040e644901c2c9024445181c00740c0c428059803140702c0d080c00c0c409000ba902c0e110034100e070b1980c5100c5002c3c1e44c40301e0044003900c3d0303945080840000c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 512802284 1250 512801034 512801057
    0x80c0c07090b190b040612060e060d0212240a0203070219031707121401082a0d080306030f0109030e061b060a0204090b090c030f040c120302030307110d 67
    0x61504100c041c50070007404070f8003000005280061428450707221500b04030340002c00308907494001c940700d404c01c0b0440300200066440d00d00382038204940200181e115120901d485821541e03540031032100d85021004861902903424808480c000b95030054150040464000a0414900d030003200c1c0308414a5020b401003481c0b06088140030a8098000c400740102080020031b1141141c4101e8820b07486580c031602c1044410a804086440c008010b405801007240184042c074000568981c0d890050b2000c4901c020070208555201240a00410790014001d50707843c040c446100d010b540203a9044003035540ad04030f00000386088500c901e5006000c0f807003003211300120b440e106010340000c4140c91000c0e040c00804180090a04e10100d9021351850740c045400d014410703031031140c18601d00c000e4034404a1030610b1181c003000c0740001482101d24001e201c0c001010442d05404420040c01d2860340344540f40a1854040e440e908101c0e00f2900141c0000c1003c4200080007402c140f2680040e22081010309 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 512803534 1250 512802284 512802299
    0x19051603051902130612051e060102150a0914030a0e06300702061f150203160c03050c0109150810080d11010b0114120406111801080c0c07 61
    0x14000740300030184070030b00128076140c12650004255080d040c02410340341c14108200904124840300380074070010315080c10051074030030340c0042d0a800d078111141091640d5503c030040740761011130f04034042065004024000c61440c10380007942010301c0390100c2104038501d0a007565030381c0036103030001c40040c2100320060141d080800043c040100d2031901c10003501101500400c02d0000349404510945540040081c0d00d581030001d00e4100443c4801c0405c0c0305010202e08010040b64003a0705401841c4401107107020b1b0080080311105c2e0341c60601045404424200b01d8032000c114030059440740100d00b0316170300a41c802c03a14881030700ca540081131014400c0000454001a00905041a030012564049156502040b0b0508031101c680d80d924011492070300c10701e003913a82e2040407606010354243c05000a54440c3c0030354200b080d1142500640e44d907581000c00103060240075140c2d044400048018070511b8151410000b49003c2c1c03034807107035a12000050703001485041c41b0400daa0700815000d10445 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 512804784 1250 512803534 512803541
    0x30b090c030a05191a0408030601030b0108060d02010e0607062c01020f030a020c07080f010207110d020a12081903060518010515181002010606020d090e04080f0712020619051603 78
    0x2680217142024980601409000c41700c4000d40f016105c040c1e02000b041801d40e454005c11012100a01e000e2909050a102190030780c0c1071240002d042c45030700c0019440c65160b08003901c0a0540082c800e000310080350102d41500c400d03010402c034118248a03488207800c0014001c5400040c0041d038841d18582d120720904009422102480b00f460281d05800550b055041001031a42d074410000141d440403a85002901d01a103d90350134042e01d9054110009a61648607a80480d44800300340c440b45c0400c6e242150a51107480391044000c0000c0c601d1a002c103a043e0f102000b9210240c42980c001e0015031a4081842e10074170540b43d00000c03031031505880884a00c0a4041c8106001c010428041440005881468048040c100503907645004010407503040164500e4071440b4104181d0303081c1800b41c50481c26000170005070444030b00103160955005018115a400e90b000303401c0406102c052080251905025641d6408124080c445240000d01a00c0b4090288008074458a2141c40821094010307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 512806034 1250 512804784 512804833
    0x110f04020706060b030a06080a120302030c13030f0c0e060d0311070b04030803060f091303030c1413080f030f18010e090c03040b070f0c060504020a0906030b090c030a05 74
    0x650203100c1c4800180050040101509241d9504c640302c0c0b81c1601181c04503a0203521400282c3e000030f00c0c44006c500244009040e4041e140760140e62540c07019000d040d41d00c01d180c0c1d000d0170144002000400e100400060743d10444c400da00c0c1c80040340e0f58651240e40c0c603500342e031002c2d0700120385800000001c0c01281c0c2100024441020744140a80e500750484480c1c015500c2520001d0001081282914010703a003c881000c0858840c0302c40c1c202481d0300c042c80b0340b40e458024141560345190400442c0070b0000d10030102410f0030b240390b54000f400c01841ca5210b852140160f280700d001d03901d4140040202c155445108482c01032410400c0d42c1c4074030b0201c001c07090b01d214184038a60500800d1501d40e10381041c403451106001035a6801c0610b011001103900404800412440700100104d5652282500466581014021400c0d49a5000044007040b140d1b02a20615242040010802075200c407032038403c03c3c2c548103440300600e04105040e01c0310740003a001400d80d00031111443e03402a10a000b10364 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 512807284 1250 512806034 512806039
    0x91109160806280f050607050a060f060e01031a0a110a08041502041508090d0912170d060603060f0e0720030703090305010c090f05040902030a05060403111603110f 72
    0x1010030094441000d2004116095800c1404031002c0c80007102d24113000c002000141c42c402c0c81e00d880b81e215a81c6a41548000030500c40e169604880d00c0c41103900031502170b051000d6000d009507581e01c0c006030f0001901d11880c02142000d00003030b49600c0684580045103030314030403039841d0080b4860110380204004008417401f000030505100200c10301d1016001a050010716100c0440ca480c2c00a84aa0030050094150340d0104003400c00080c0e0003c1c03c801151010301c0c4052100a01d807034040300044040800102403140807400115100e5a41c101408403086601c080190649401c4c1e44000c0c250740b40504446c03c0d6880c0f020500d02d9203e10400c0700c0801c00354001200e1040185401c0f8115400a4816400101402d80500900c0030038810310359031902c0740c2480c41070740e40742008005912410b4850540b10710394808260303095440c140954048241d01c2010742c0e003549403d1030003a05981c0541b02c0c50140e8481d003416066010b104d43d0003907007540c1c0c01190b1801201515000c009103501003000e05038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 512808534 1250 512807284 512807299
    0x9090b01030e06010b0a020714010e01050c010902031b0f01050f0307110f030d1d0c0a03021005040308130608010806090303011511100b040b010207120210030b06070501091109160806 80
    0x140c2c51041800704034040d140c5800c0599803202c10b6800207107022440d8000608200b4083c0610038a6a01700381c0480b101c100a007009529169030071940303401080041c401075014015040c1903508099007850b80aa6143c0c00c03118602320f0005240111000c0c0913401c182c1c40a800300b0004a000c80b4090308540c2e841e019240220f400300c0c04010000c81c1140c110650702c401090b00c6048042e5a040d0014a546d0810f1a0382d0041031485407036000070725002c43d10f2001900030400c60700030340c0c40940324a00b01c4010b142c00c004500e54440035680714110a0040744619000101a000007040ca0100410721500402040e00150300b1030f401c0202c02807004615180c12414800c0d40c0c2d1580a0044050122075909004032070000342849880050106841c0b104000030304540010005024484030b030f000c01b54485805584021006410f101d0030b40082900320801a8490404030b4100100031054201307024843c0b04030010158000100144021003a00b9502010101c00768210707040d03c144280c0740c06502c0900102800c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 512809784 1250 512808534 512808551
    0x70f0516110f0d080d0f0b030a06090c0b0403080903060c0a211d0a0c17070e10171c0e09060108131b050120060c0304030e1503061e0109090b0103 64
    0x40c0510443d83d4040310f000ba004501c081c84441e1606c541d038489105014188440e0482000281d29150792280050840755180041d40a2010420108014008002c1e5496840c2d889040040303480d080561018070030304c6503000103248e0030a03944c00e8940010554a0f0444c120400c01070120b0100c2c81c0844000c0200c1d503800c081781c690121b80039144003580003034010f056280c060341805102512250490301250401c030300c01030b21903000080c0d04070441da0102589056521400c0c05052034404036404000f81d0383c103000c05020300d41c03408a40810300182111251b104c24010000c140c42030f883e60411580d02c840160002000355004c2c6041e141e0110400c070085000704e5844c0e13a803002c6070000c001d9071781e0040040728041c0007650b0416589201c041e12920348a11980c0d0b1501840c0d590354008001400604001c0f001c68105070040660086141d00186130354010f03a413074458001c0d07a420803524103100d00e50200d02c000d0b0386101c40320240d80c8042c06a4558051a04291036000580808070f2500d040650740c0440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 512811034 1250 512809784 512809789
    0x20f160f2103052206030e010e010c02100c020718060e01060c020d0b040203101a10050f1b1e011415030a030f11070803090102330a0e010e06070f0516110f 68
    0x2c0b07005000c443e11b002906c0c0d0401c01c1d0352801c40e11000e007001c42d940e140c104c940480f0351b0002190032103026043c001003010990354004906007205540100182c50a458050300c4000a0340c01c4078003655100d403e0415140c0c0c1e12241104c0340301c004074029400a01e40b8421a01050300101080d900c54009070840e1010920f19948008442c28000140100c070048540c09100c0e1420251031408001140341075400c101e00c180b012030841c45103000b0790120b01c0ba64a0480c14a0794240a40b0b138916a03100c0c0d0540c00b620500c00304501a165080c05c03a0340c00c035030480005d00d40310840c900d07a0f000e440001d4000c0607040074070368041d40e034800200400824000310244441104c8000c0080360060000200655150f40c4042c001a181040e0203042070040003a065194482c0240045084580c41c02404440e00d02e880e601c6003035004054520b0700d2503403542845d0901d40800000203201e03005201030380d00c10101002c00d00c001c43c2c1c035000790000c910b500600c5091500101e59500030140010fa8000c1030b0003080c4181900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 512812284 1250 512811034 512811097
    0x3c031e091005010501030c09090c03180303060f0b0721030e0d0504050a05090405030a0c020103020d06140f0108010b180301060b1c05010905012103020f160f210305 72
    0x400d6042540040c140d001c591079640a21401807900f070030140281c0c1140c9402400c400814081c114801c1e5840d103400e05424801e40016046000c4100001000741003401c0090281119005200c69502560380c0040c89c0c549900480d08455041048840030568001369040c154008003e01010035072105680c003108081484425420081c40d102c407580d135413501d428000c0811103603000b24404c501c0700302003201061002c801c42d12244078920307010f25084014801a0b00a0181c5c00100f16140e00d00440400e50f85920340761490384900459040c0d6041c2c0f900c40044030312800c24042c0101d10380040c0032214120440c0000c0b00034100f0010004521140c8490b0b5a441c590003001541495182d0b40700150b121048510030313a4098600c01074144410340c1010983d03180300d0441d808452086d80c8403020071044c14800e01c94144038070340f44810340710b00d082850140b150950f0305000c0e1015000e600c60b00081c0d03107a8110601102848500c03000112849240c0b010f80e040d41201c030a00e09825103920b44001d41c03905511 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 512813534 1250 512812284 512812291
    0x913150308160b09070303090302060c0718020a1d030c04271a0a0608030405010807030f0f0203090c24090d140303101d040215040305070b3c031e 64
    0x15100200c92009080c118403d10000c2e18100b0582c01151060000c20341c0050f41009898040d40c04594a004003407005282c2841c03988619500c840820b0719140c6800c0940090041c08115038580181462920030a1b49a100c001c60060303050b070103a0110413403401e241d0402c003483c0c0225000080841461010104184085131003110100d41588218224041c85050039420161040040001c6418406103559038452801a41d0600046400050103a442500103507a0103411107824043e50400385a07010182d0030503181d450840c06100402c01090411880ae400b403045c00c81c840e402e291044510800140e4400e103407146c1c00804030004540410041c01e50528500308a90085a6915014610141740f00703141e0480c0300b400e0000180249003c0141c14426045501202c1e00142c2400c1d40d014002d0f00c0c404c650004009020b0088005a4108508007810004034031804008411605038092000c15000c01000a4960300805154080044603c00396078007a007085190040050002080003415a044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 512814784 1250 512813534 512813557
    0x1090515030f0f1501030b07031821020106090b0a15170718050405040302032a0714040605030d020a08070c120b0a0c02030c0c0607060207170304060b060913150308 72
    0x15609156642002c00c130b20b00d404001d82d80041e90365411a034942d030701d17408090712090405448441c2d8001907004290f40d4402194408c0c0e01c6021402d40d044810074608280390300300095460080002160003050080074049000181441005410704a22005030401c03c0300381010450407006240c00500d0704c103e15401081f803078030307810300a10007108008e50b0440c0903045980070743c0c1440140400aa000000c2d69440c1c00c090010b80d4070317010b02071688110348140721a62410f034031600c90000b0b00d61080224500290505032000d02106844005040d07039543e103044c4810048e480000040c0108a1041c040d048291048000c94621036031411210510003048506907500c2d04420103006c01030400340b2030a260514240007035401c040c0c218016980b289070343e0714242c3c020300c00011001c00700403081e81100c401681c01982c2d007030850700c01c01c0d000241d500200c40858845140102071070300740c54040151080ba0500504401c1c00003000566000900110f40d50540302600c024400300009068801400305030000c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 512816034 1250 512814784 512814793
    0x302010c111203042d03030f11071805010803070203120703030905100e010b090f0c07170a080105030d1b02060723010f0f050105060405060f04090c120e031201090515030f 75
    0x401c2c401805c0d0003c04030076045042c03140740d1000e00130103242040d80100c03505818401d0008198034401d45012000d81c0740c40d100b5000780c02020889400c5080780d00e044580004040005a8a070203a49540303200b80300c4040c2d4554088000700c0f40301000c1400625442e440303440c0115950f89580d403082d1404103045007406060703444d8250400d07041800d105034040e03990200c56180440c1840e5a180c801300e5009815840c0010001901c0c0080c4400b00124058401032090315954131155910018200c0b542800350b10f101c0d0040300c0e400503a0381d01c42c44418031000c6009070220b030754504035404c1120300d611616049509106d00344001101d40700050742401c00d007500c0800440c040080308488030488070816010701c5050314020051000b80c45043c281c0341500c4080d030340d02e5981d1070140e501c031001d40078551218219501306980d01c1c1d407895204403038216030007020009010181e048000c05460380608440c0c291700380c4013403004018058580d0400b0b903301c2c041200000c10100010046030a08040c1c10002080307074130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 512817284 1250 512816034 512816039
    0xc010e01140c120a0506061b0a020a0e07020303010b0702012105181f0209030a0c08100606050a1e05040b1818070c080d1503030c060b06130302010c11120304 69
    0x6004480c0359001a081c51624070f0921407450092005601030300c040801c039602c070300081c11621200c003111842e9502d203440c214804400a0381700c1e40ca50300800e049015030560100015a01c40c01030309031303014440030740195066a08080c00f54282c0d40200c8002e03030400000542580c950145480c0303400f01d000e40c1103c007140754a0950b61018648882d000c16200d1580204400d1448078040351030b85031303200140f16015071764a00117030019143c0384c6020030284c01c0e040e00c0c4d1030005400e04001102075200342441c0e001d000e000c0d0b80d80301c2603410380141115500482c107540041c41040c402c0c2c0000c1060341640341403c9040c9512034150416507080b0498040b041900d06068502c0b502d801d2000e0b10700150b03001c1d00c10480d031400c1c0600a280401908000b0078210000ca0140c0d0541101c1e0000300c40d1215000b51840b07400c2d907a0074018040e0740454025250340346420030541c01d07400c4c500121514420320055000f0350034956401151074119002060700c6006000040f020241c0d681d12961504171500300056840b81e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 512818534 1250 512817284 512817311
    0x30c0c060c111b0d020f0409060c120c08101e0305060108070807050301020c1504050c030a03031a0316061409030105010603150806040215090111011409120c07090b060c010e01 77
    0x1d000950000d10f80c1c58440d600410350360361511600715641585c900e40080801d00204000c0c000c00e500042c006030508141d01e074002c7c1c0c0b0040100c1c0701c054006040c0010030b080340702650011010744440c0f80b052035160040c05a09a002040c203800c0591b440550b03a1a556510307014180002a0011072081d00074410030803c03000100301e00030103048220000c614200b02240c1d1156107403008000f0780720460300c800c00603060000500c40030b003503010060107540c51071915207801001054900c200c01000300d2500e655030514280041d24080c0b107182c403001d80c0c2840b0b0a1400c01d4844407035080342c0d9403e460007040802c140d91428000c0c580206415100442c1d542104800d4440d0940315400101d40c6078061400c02001d40d40b4140214141070f1359200003981c840d440001214170001203505d40300c0c6503080441780606415503a07012403044400c1c0054920304400401150058400d26031030b0304550340084402d00408890ba07001101c0e0a4001341903030700d04040c1494580c00d490694582c485941d64aa4403100301e270 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 512819784 1250 512818534 512818543
    0xd031b051f02030c04090c02070e1006090e06010e1e120a0606060809060c160206070308010305100204050303120702070510020f010515010f0e0102070f0909060e0312010303030c0c060c11 82
    0x70408141e05508514088001c1c503818011849400750180e122140000464001d009140c0a00354445c041401403a200051008c0521107119100000703a24820020b01180a1890107000e140c05a4400781401102e40800c44590403016144807801c1562000c80d10b1580c42eaa108100209a040a410302112074144501241c0496004405122604c010400b039020040381150f0710041418042e5120301c20000445800c40d00883d00035044000020003805042c2c00c08070241c100c1c2e10410489643c0c03900400c0c04000d17030043c0c3c071502c0c1e09a031082c003d030800680c2007400303175510001074812508640d80d5400001c1c20400244109005600303c00404200e20000f0b01034150f01c10650401c640c401003c003400201041100520341d000c000c80202c04a0440e8030910150004114030101d9404140c0c680420000402c02240111805843d00010307840f6080e001c0265140904880043d9001da841d646040d0050100c0914803c10020b0000b0804c1c0010020700c2040d8801886948440c1401642d0b90383c140340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 512821034 1250 512819784 512819833
    0x506090f04020907391b050a0b1c090f051618050405101a011706091305030906190e0a08031c090606090c080106110601050d031b05 58
    0x5403004400c0001580310034550a8110090340b50035020545a14502070300d0b2889100840001d1010348042007001e45c00c0c041801c14180108031100390405825401c1c02001b00501c106a0020202d20003008481e0308500507200906200b440c185009034004014012640c290b02c1c00c4a42015004a88050100800c0f03041007080e103035070070015860304085504001c1080d1184291085031540c00041c204681481000080b05141c042841180f0780002490610480040024000b074007208600c143c050182110318000c0f000500380e6850350321507090413426400104415103031813200f0811804c068503103200601c01d152800b2052001d4052804008080c603007403255452141c02e103800c0c10700c80e1807004001c075914580d2f000941c803a46010441d07100c0190807544405002249425800100140303130707400c1202d607081d45588004441e0303240c00302690200b0400811840075407000005000030b04101c1c1040c1c4039540a03050051858104e40c041201da02c0031a481142c294014561030301d001417016201c0b944 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 512822284 1250 512821034 512821051
    0x7030f110c010c0915120209062a0f03040b0403170408030f1e09131512060c0305071b060209010507020904230a0f0f081207080f010614070b0703150801050609 70
    0x554520014010054a900c450308074601d42d0004850123556240b1040320038464210f20f03008400d507000e0303240403140066003991a04034085c030340c0c84001d00c041c084101c03401d8452203401300d4101801e54503520355220036000c810007400b070f08100120b052001000605950b40340c442005039035101c40714040501200e0f541c0041040c08092050440644e203528010003144500c120001d6500f4540400c6066103680b82d01c543c0008100c0c4d152074080c02034981110500201c96107043c42961251001110050f42040c040080140350000c1c0400140e655001418031301014503009042600e90380006900d4070003507800716118950010003001105107210311104000c6020090403100f1a2604c0702e03040248000b500030300944094500b0303010040c400303040e6002030f40782408402003403505c0c620203072070f00101352140e0380710b203540c1c00000456511480040c0071007884e03a203c02e414503100380c4e01d00407a010040d110300c061586032911f12081034038190180c030043c04110008200740c1850001e000310000c000e4024032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 512823534 1250 512822284 512822309
    0xc0b010f0f0f05060d0e100c08091603030203040e0903040b04080c04060803130b16060504050a05011104030c0b090a03080f130506041d040611130303020f011407030f110c010c09 78
    0x207a035030505491444c070700180082910502d1b030760658104524030710b1224045240c4070105580603803040c01d07103100320300010459502d01c2d280222402594441e21005005078400c000c240004190700c89410380003902082200d00702621031500b0092078016403c078000079482010550064a0300303001d802c008044d40d030042c510305003161901c000f81000e180a0b60b0740300b241c000382c2d20003e02e2224500003503072074112208104905040c540390f2f4507821480750076100c0d5070801144110b0b400011040310116036001c0c003400c44140c6004041e4036550408031989501400707030000003020441c40ea0040440b400c00e4149507540d00107a8030b000c412603625410584c020f8100b80400d02105110f804c050204c0c3c0340c40d00481800340e403240b500b040a807480030120f0074441c4003c6001c1c9002c0048846010075a4480d03000e6904107400400d40138200e40034101c2c0d00c0d0124000c40d0115001c58003d501c50070504400d13000219a0035440200c000c0b0135442281c0d064040c1c4e40d00c81822503d2a8443c05810182c041002841c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 512824784 1250 512823534 512823539
    0x18010e0a0b0f10050f0d020109150503060a06080f0612010e0d051c0227060d15060801050d1203050c0d1109040513241803020106030b060a1d06010c0b010f0f0f 70
    0x10b01d80c460ba80c03030307a5801030a544006d1025680245052001840f0800c4401c0100c042c80500502c0d98000b80c6030346000e00080071000c15002e01514410b4442c03400d60307200c440c40d1341d2480108445803003c031005103580e5603201485962881c0a20040d00404a00d4032015a0360180b42860300300700c244905840c04132032050052000800308107102c102d0071030700e80310034440100380140003032030381d02c6815484070000b40740101030b0017019028030450080f01c4c0c0980f100681681d0714030500c92260b48621005102c80720580801040300c5c0642d000b15080700b100100d017410800b103c1c21000454016010744032241c1c0020444500503d414012130b940800d032048103d0251031103554a0410038680d009102c1200f416850440881c01c255200d015554641181162031580300d0401a0080c804d0380000c0d034070602140c000038418101108400111050103410781101d03d90707010700940c82240a030045040016000e28000814000001903020300080c240c43d507070651400d920305050003210740c0010310001002004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 512826034 1250 512824784 512824789
    0xa060f0e0409030e031f0c03020307121515080a0b0a0302030304033f0e0901180902040b041d071a0f1e0a020a06050906040b18010e0a0b0f1005 63
    0x3190440041c0d40202e404107140c5010350f0006600c1d09426003600c551000403591000500c6000020b0034404c40c104040c2400c00780880c241c1c84115607c1c2c0104682d5544211002041d034400c1e080803c1390250503040030b4440d40780c0580c6140f801c400100044004062000c601320600c00c5000c603842c2140d510506920723542c04640c81e8010781c030000c0c11050380b410f2003c1c4403404200005010b03403011480c1440c1c01c03035848101000c24540d099070b600041c54012100c0000d00703060149606031380100f01d50a003c1c2041c809803d000d020000e1040360800d8442e07003212003540b128040c43c1c112000f80304900f400c1e41c4032000700c04d241100347e50203841659548180200702d1044102101c8100c030804016541e154401603030008480740700000d44a1a441c000340749801a40d000c0794207506c5030300c00d000031b12441d203612004070740d103080944002c1c0200ea124008140c0e84103c0701c1e580308003403411000208000300c0740210103052101031441580c003070592038100030204001c01c81940d0702c01031408000d01700f14104000f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 512827284 1250 512826034 512826047
    0x50913141902100201110313140a05031e04030b04050604020306220327080d0207081203060906150304050c0f04051014131d010c080c0d1d030c06060a060f 68
    0x41c0a4028681c65040c00d0032035100390070810302224800000e41d9a814021911400d0100988090380e01c40c44488084601283c04540307003010503001401141000030b408400d11024150b02c032140e0282000f00700000c0000c1010301c0581c419030060004c0d21061500340141410660010070040540703820310003c1d221502e101c0540d0392060341528012004c4000c2440190b140d01000030035224240e07030390740d00080040002858003200143c51313080c0c90b51a40d81d100026913400c025400c1d202c034a07000340000b80c0b03903050a58103242d004100402400740700d0307184858040a58000e803015200c603000143c03142030070309204085001c0f00e1000c2d2001c00c203034585540f413048101b0300c601a0500200e1074a000d01c8096540349900c1035810703014802081200c8491400c29000d1000701002c0b0340c25400c1854440486020700106442403600f22840d510f440e02241c210002041e001004d00342e5000c407020302c2d100d5050100003070402d03882540700a007020305000081202c00c00e86688000d0401c1004001808010f51205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 512828534 1250 512827284 512827333
    0x314131202030f0412020612040c1403120d020c01150b04081203040b1b190201050613020a080c07170d050f06091303080c070209070c1401050606030601050c0705091314 74
    0x40b1040030341e00c0303610000e1494415103070980123169040c0203210920070b80c000c0c550216030f07801a812090040031428181c07521450f0103001a1944103000403500b956aa40081c803050300001d0000403201020030140b04980c0c00c41d04102512207011409001c1d40c0010030400b40318142090745281140f806503601c82d500c00008120030f101c0340810b49040003200000c0d0541d805002d01001460b0b2170100f24074002c1c020101140c2c15846135141041001c171880480c42124411b0810f43d81300c0e04640e076280600442940000f01c1101c8400450000c04281114203000d03241c650060301c0b022511342410000b0814a18014103014428200c80c41030100d110102401c205696615003402c83d62581c50080f000b81d18003a402000c3c0d04500c0d00410000c039198001c0302070203a14400c1900c0e8004542000a0508a034411182150080344c10000b14540f58041c00c017400e4000c008004507141252a54003081c00b040e0700381c0d40c660b22460944401c00406c80c100c0d00480800402d913000b00700c42e201811411340307045a80b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 512829784 1250 512828534 512828549
    0x30708070612051506070f0803010b0913020c030316090e0a0605010e030c01091406090a08030c0d1106072001140106030c0c050618070b03041505012705070314131202030f04 76
    0x5080040050651347e0742a85c0f6041002c058496949000702a0345902c1070f400f55114080406200c107c403140c234426500034984220082d07065540301c1529025520a103100c00050116040c0c00203440e0315101212441102c1c800c401103801031074000098400c98000d017800d48070f5000318007001204c0c0d920052100842d6028040d2040020341c840100300c0c54850b0400154010309400b07404115036100000030041c11001004aa0141c0c0b1075600440d519840300441301403c2d00700e03002250314032380f299403640341107a80e0710300320203100564060705800c44420310b5014400281071401040358036058810320030980c001d400c2c07003110181d45964940d00c0f090010014220820300c0102400b1818042000c0005400401c040c140d0328102030420900f40400380c255588098100030020800300c1a092900240584004080040390202000400031304001001d010406a90b24414402c03a880308600b0380c00740e100d8034400341e140746590514140e52130805a0034070946d0300030080070800c9030165040f0390456428 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 512831034 1250 512829784 512829787
    0x190b0601021c300e060c0c070303050904022a07060c24060b0403051f06080a150f2d020a0c110d0602270301050108151005030708070612051506 63
    0x10360a4014540b80000e0b41c200c0030700e05014001c92540f4403a07012441c103039000003c8543c03581d5407051040084c456080300c001d06d50441401000003900a002a0510460040c8050304040d8007805490b41a07118100070620ba113030000350014080070130304c00c40019160501c0c2c0000f81c01482c0d2034502ca04251740621007074141e02d00c104100103481035449880685001d260490f40d5036500e08102d9030702c1c064080c1c0380c40000300804080b08030744614400d22003242c40c500082c103036514481d2600302070b03003070000d0005803c0c1d525403503072829040031440f4146107003418440c0000c01c0e041004004540c4c80c050310548907110b00c10000e1108058000080105940c3e000c0340750749403012950041a0300511107000101040e00215001e80a040d082c0103512140c030460001c00034515002d0105402c0e41d60a02c1901466086255800b41d8001680200c81d880f009001204032070941d16008689800340720381c003004294106050501402d036121469402514210b00140040e041814968147d5140055218441d410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 512832284 1250 512831034 512831057
    0x110a0b161704081f0b0612150f060f0d0b06040503070e040309080607030e1b1c050f1902120604121110060306021b0318091305190b0601021c 62
    0x2400085034040d000c02820713545440410003149a40d004401420290203003440d81e88403d0741040b400380c990f0301ca002e101900c9240ca50a444500e80740300020103e40203032804000c5c0300c081e00c800d001800383c03210524501d642c7d500c40340d140d0713402c0b18144030f0500d12680080204004c95500086c08106540d0182020003180c0c42d945010340d0107808981c050303030060007400c080200e042c0d05030f48140100703c1c8000550b000c040e000d403001142c80c000f03000d0702a031009800d54210340412a582108071749a108504a542a083c40b00c0240d140040c404451740c1c502540505072400c43c10025030041072040d13000000c0c02d4170305141e0307509002c800601ca144420051090722003524454104007610392088100c0c01080041d8580c1070480c00707984112405c05001401e914104101500007003200c9806c81009401040751102c601008034080014080048901308602e50401003070090108802c0c1800d411030404240703103249840c0f03e100c0b0f0010b14283c19034000d040800103800400c0d51080720034001c2c2c41e19002424 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 512833534 1250 512832284 512832323
    0x301080a08092101090c08011b140d050c071a0405030702010f0e180f150102070b1605070e1005121902011e050705060603010603081801120207110a0b16 67
    0xd445000d54003140780f80e501030036100301c0194403c0c4801800741c600500500c1d25041031500760385d0000252030506105a181c00c850600c00c01d8844844c02107066002e1800a0f02030f411015036200742c401c1c0d184c1200000f05041000020b40740d0510403110003e07024280d00d059240c16480e4016290044d040c4514440e4413401a403194500c1e506600c0e006111622400103101c40e08a0314004803401001d1003017240108440681c202e02440030307004c2c142e000b030041c58200300070009180c000300d01076800307480c40308100390000714180049006400110701285207894100c1c1e804059500581c002c9024200e144102c01d190100440d01e00340d40c2c902d49400700c1807250548012105011104991800204c80107105100d03140e00c00000c001041c09441100e280742c485204140c00c840c89071000074005001084103042c50401c2850b03020040c041414400b0485104980c0c12013a80e12410044405010040c00007011703103001c04520780038040b40e6040c1420201e2003840303140c9202c52094098001c00d1208084440c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 512834784 1250 512833534 512833549
    0xb030a020f12011205160f0b07080706020c030d0b1e0402160618210203031f150e040f090233120f13031d010c061416050301080a0809 59
    0x41e040300d64140c038541e5144418031107212088011907041c0146c2c080c0781c034107402c03d521203030643d90320a21080d540c515241d00c9038980d03440444121001e80f010301003600402c84a1000c1c102c0c04800b0800355560302605040001141d0f8494030061185220140c1d02042c0c10400310388000310380c800c0e50700603a21039821250226240c0c103110000c1005040155040c07255a401c10603240c2c507403240c0c022080f00d4230301c2e452081070000803014800041c0e00a00018a0100c400c20b00007a0380f201c0f9425100c1040d0b19103001071562212402c0300e202040c0c042c1010b1140b0b003032600c00d03200c62003072400701000714500b558001020941c035840c1541c0c860381d11030481408172220f1803850305400c0e03141210b941e0310340380828401050700c0200d0310545d4940311100003950003031f060580113200b0f55060b91281c2c0c82d595000c4068510340054409181084225502c02000585c039111b090000a0982110000d0b40b8181d0003400b920741d4408281d00800a06200411001c0000a442c1c8811a80b0070344041d12040000041900c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 512836034 1250 512834784 512834797
    0x5010b1026090c040e1006030804061d060703031805070e070807020303090a060e0102040f0e01050f01021f05070318060501091b090b182205010e0c07140c19080f070b030a020f 77
    0x4003132402c7d10010410220500a204032803050700d425a00821412500d5100b0484004480d0019010403001000074820340c0010080403440b41500440941502c070a49012003680003101c60300040828402407030f400c681038507030200503407000394510315101507029290850b80f2030045c8840c0d01c8200000b2103410130b4044d00d014184c050040003e0b25992111006081c1c0f00380b20b8a4000c00d02802d64900c1035202143c407104101d5080601c0080101e0fa462017401440000d0030a403c0503541c400c0d1a54450740788030b16200c424050038002c030710365040242540403150069181c0007a0f01401c2501c850050700581a0021a20461926625000c5e007001c4411000e0115024a50040801c07540c0c08429189042c6c9228455800c1420002680c0790104602908001d40705245401010b0100030f001a003100d2028003100d50343e50a481c50204100042424401f1982400c403000400000038000c050040000c00e288050890041040764982030005695100c0500030b000320765000035410010045803402c6404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 512837284 1250 512836034 512836063
    0xb0a3e010e011404060605010c050604080906070816020a0806070905120f0106081f0c080a05040c080f150c070320030c1207030f080408090d05010b1026090c040e 71
    0x610f00b0b004160412402c21182160203600e0001c0c081217075440f034040d144007140e1043c004e00c159100c50315100140c0d00843d211540c445c0d0b080061400040b40706002c1c101d40015003501541038802803040120444481c0c01031007046e07003da01000081c42e8420b10510484a00380d8800181c070203c52007507070500010715a628a03642c240000082c20607800030342031030403041c410004404080100700b4442903c031005100400a1014070104010420f030354030140d0498401c2004140b4551781e0340c2445c1c03e00b0b0161400d8a4190440f802c0c2c01c60103020303414240d5110590031605480c0404a540c00380c4403141001e4000c103c1020a070810016120400496440e0700c20142150644080d004046889a0207010100c00003200d51100eaa2070b1405202540d01440d4000071084c00c080d900f8060007142d01c0078220656156484030708109040d1210300b10200c503101156240c0c0b92600b080c5420610341542c960f180c86c03902865008000c6c4002c03011500003503902084070003241d0520080011450300074640040789 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 512838534 1250 512837284 512837291
    0x7140d050a12020a09140111060a1b030e060a05061c080d11070c050f030102040b0f09101707030b01140a08061e01090905040c0305070b0a3e010e01 65
    0x40029421a024103942112952022401c040160641042e40203180d0304101003541c40da81840203c1c205090b080c45041c06143c005032044144004c0340c50500305680f102c2c2c41555800c07400309950401101c0d500c09031118101481110aa0750b0340b5583c80000401e038000f810fa42c0d001180d4a6603500d41003410081341402070365001d804a0030002250342c0115002c032840303440d00e1504800490260705540b07080743c12441c084030b490300d00400e00c04003074418144c859240d5400c200224100780e0710005042c524001d03c10749a100c040b10310a05c01624807414400701404141e520300501e000e00740100f69400300d0f183c07402088003802e240c010388209860964084141e100403c0004840c4ea02080091184000b103c2c200040e50708000c000c81c03980c005480d90b50005407540e02c02d101c1413041b40c2016230000d04c6028042060fa40d680c84050402805800c0301c000314100280c602d00042d0702c0401e110802c486a0b0168040d8039005900d108080c0c40d40307401107044082c159400e0070b83e2001b0f42c00980220901402031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 512839784 1250 512838534 512838553
    0x20403120e03010b0901030203030a030c0201111602271801060302120a02030c1504171c08150a0b0a031a1f08090a030e0d14030d0603031e140714 64
    0x20701185086020a8042d61800e06020310034a80b030076826040701e0300900030714505000c0e40b5084001c1c00489006c0c0c000e540d280c00d5011106402c1200411259600d11211607483c00148104039624140f00800d51600719015410200c50341405002900284092180701c140b00c0440e00da41c5c094807140c1d0005e5440803000003c01c80c6014041740501d1442c0c4202c05403101011301c00104446040c02e070503030a8201605200620020032141c50007849600b03514100c403c1c4810400c070702c01034a8160480800086c068109210f036102030b0703902d21402d03083e003100c5030340c0410b05050100b2114016920540c040644445402e04000306081040e014040041c01241254000b00c9203180b25035068078414002030301001c0020300c03960340030800c8520550703d940d0310f004020540c41004039010f02100c0568080c00c1805940c0b104000400082c1840b448004021803403900e1418094004c0c225241c001320820345030000b048081e070f03014403000030390310904045940720701490030010300d14800e514088904e40b00d000101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 512841034 1250 512839784 512839787
    0x200108071209060c0806030613120e12060c1306030e150c071709030f12030106030509101406100c0203122109011d15040f03030912180506160b040602040312 69
    0x20307506c202800d03400ca0b110707a1521400404c030794401e030300041c1031a502e02250a20b07640c030594510041d04c1c40100b10201c40b000060071941800c0c03081c0c2e4068401d1800103014015800d2348031040b001805581010010107070700400850f152608ad03206240508000f500180602d80e03000c095841aa411a5140209416640c2c002100f5800200f60714880c0c4182124100b07180c1d400203240030041c1c015800e980c1503134600a001e034080e0034050003801041c0220700c5140c006204a210b07107000c10781d40710b4000039070341001422700c040e9516032140c0e00f0030032070003805580149c1c40c0042e018248003841c0501a0b6200c1e03192000341802e4030304440d01085000d0070360500c000180150001051549000d859043c85c80d085c600e003950703600c1c170001034406644050000070041250b8003103400b00305000f4280469142e0341a0703550944118660903c20104200b058030f182001d81b6a18000080e002c00c0e9096441c004101104600030081c880c401400d82e007201c40041c04100860b01510000d543c01442c40c074100603032110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 512842284 1250 512841034 512841047
    0xa02061e190206060a060903060509070b07050601030215070803150a1205010203011e1a09041104090c0807030e070b030603330f0f01090906140106020307200108071209060c 76
    0x180c00148545004544a071a00010170821101d0503260084040c0c51981d909001e0b000040c51100140a542c000054400c0312100034980c00388258040c10041d811b41c81004240c41010100342d01c41c43d000d006010002c2c02040480342c208006030528000810850009402d0804a801c40382ca02540c01c2205820450150051030607038001004541c10700031901041035444500d0301c100207000c0401100c9145100700ca1004217900200904013103140500d1010903e11903000f940501410303a9184080c2600030342c8108950780091036840e050005282d884005550f9501d18002c44031840000008034181d0340e010040c0010142860010ba00011151403040303502400d4410703a511001e81c1400024200c035507010907540304070140c100c984005e90030b205403000184090340d002c859440e61110002d17040a85042401d008000070342c001d5540e120246060034000d03140b43e080780d030b444240354020744040c1e0f040100d1a80c0807516240400581c1c8020b8819005044011000303407207a494842c841c01120750016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 512843534 1250 512842284 512842327
    0x703080c030406080108010b1f03020f1204021311090120240702010e070303050a0e0d0507060311090d17040308031f060c0c09050a02040b0c060a0e0f0a02061e 70
    0x301c400b0051781c1c0e20314110342a0380b04103910380c1c0d00040c022401c8004200e02c07140e5603c1a2401e140050070702130f45d9000c0b14030641c00f03140c140300e07094603400c20442103107828403c00300305601569050100c102c82000c49000c41c00f952001e1410306c01110303c0c140300f0180e591110f000c040480800c4440900d00e40040381110308050000000440b00100007c00040c014010400c00c01064002400d88a165032011142504a03400350820031034907a06000c00740d0b5440500f141d544d4080c8029110107407414002504591000e888643c40c20000d0000d032080d580e440000050365600865041d012444100c0411014402c03500024071036100401406416003841c0241d004020034038002c1e03a90142c4507003098520110012005181010590081c400c01c00300c4d401854100c0400c00c0094101038030b4020000d03644d0803800a4000540c007100411440004d10300545e40c145a0110180081c0d00303110000584555030600068040c2900050341d0066001204244c44549401c4203030584503040c50510443c04030554 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 512844784 1250 512843534 512843537
    0x11d01230d060b0708030a0c090503011407080a061d091c08090606061c110c032b15090c0203190807080a0e0325020d08120901050402060a110703080c030406 69
    0x180041480f550386801c4a802c0d82e081000e4038150750b1046030000140142c0c1220800f04101100700051640b801d00a107000f40d000401d0511280c900500f005185e00c00081010400505081042000710640c48000180f031000030424003040e924446401d15082c41c81c0c1c601201602004034210b219a486803096024880000c141c03070451300c46c03030700300302040c02404010050100c028513000600340310b40d800300d04520b2000030300da42413110409580e410342e000b030080c220501442c140030500740034075207841543d80803030f190b4200401d4100907001c45005800d4090090059501c22105c0741e01402003081d108541548105688007650070b0b40c005012100540c1c5101c0813880480204459209602407084200689402541480029a090300e0b2035001c01840d6682c031920040c081c40962902c2e040015564054002141d1782e43c4401d1300c42c090070708010112091649860240070051b61400200c582e60380711490486140041408a9410b096855000810f06030002070001003004020002c0c00407243d15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 512846034 1250 512844784 512844791
    0xd08010501020a032c03031b12040614070f0204020703120506030105093301060305071106040b060111011d010c020d03090804061817011b030902011d01230d 69
    0x380d1006a82d1400d0704480200803031650310038002c040c02080403100c01895424000c1c940d6002d000086400c42d80100e1180c500210070600180300c064040081c0f0420041008146191a1906200600303c2c00589681d007903c180c0002d1400c14040c00394500804650002c0c411076550041d40f80c090921000419240c041c00d04080000d00d840c42c0610400b44105030800260160110718050002403c1c00c042810300c08902281010500441c110b404030b010b0b020719200002c2c9402c00c5040680412910714010303a0079030019080000080c01195000d810403001c1c02d0112042200090b10350251075120000301d0403400b07881c16000c000d04150044000c00320940c081d290007a204040c120261009240c02400102c010441042594403d0700c1780340402c0e500c1e41000b03034055201d108c040d844c426000d041410aa4581d40b00440b0038581e44008080d0031201d040812000c400e0b0f5002a1480482a010043c4c21000021a1181e40d01403100c403000d00e11605036901c1941d1081e03016030030743d0308061542c000076441e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 512847284 1250 512846034 512846039
    0x1704030201082203050c0f010203130b010b0f090f060702030d0f03050a0603051e190c1a0301061e0504080d030603050c0301020c03030c031308072006090607030806030102040e01080d0801 82
    0x1083c0e00001c45040041c1102042c10400f910291500e500c445603104880c4100020113100150a00c06980036201022842c00c00040c9402d0204951b42c5c1a0000d68000d8000c202c41b8847c041c1d40c0003228aa2042034038540c444001c2000080c5403400b4141010b900741c0a10101c030282c40d80c0c44500ca1843c03074480d8408004a403140b59440003101d10502004103035500c6201c8030000091140514121000300380101c5a040e03800c00310b144002c0e001c08104940044c88030006202409419841c030f020b1000e0b1241c90781c01d43d858031200500402425180c83c0c2901100e198540c160b9105100700c0e809000740c0000c031540d40741c160500030000c1c00725120035603180c01469802012843c06000b2201d240120100850550700c9244050140c2c0c0d00181040a0314000ca011400c0050040800b518840b8092042c140d284e20310320202d1001d48064004140c45684100328003840f0369190010f540800303825242089240d030b20350001c2802845550440d0449458110002400003000100c5d810b00e41c3c1250344074126640d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 512848534 1250 512847284 512847301
    0x70203040e071e0e0d020d0809060f1804090b060108090a08030705041802040e010315140f0a0c0c0305030a022101030f02190f050909032a0106080712060216170403020108 75
    0x1003424864985c8480404048409854010440754841c1d00501106103001c100800041403030b8400f281500c058240820903003401d80700d1600a45241005a0701403052203029560131652000044c034103414041484081840881c04100c0c200d84140d20108041d501c1c2406c8074060304170f80143c41002c26903d0902d4456003080030714002d80d02114180d00c80b150059080da82c0740c10101000c01c8505010380c4d941c0308003101d200265800f0900803001900c1544003401c0c45120401a120525803807411303c50000c00070300c00640d0050841e540076005090050711000649070744526050102c66010041e00d110b00080b05204520340c01c03007e0b4502c00c0343c0c0b070906110119a81001c40d001032058942d40d00c540081000181803041d1505c0d80071480400b80ca1910040300048d042d4262600c4800340395007451300c5040e29422003441080d010f0b04070700c001400a00c1ca81606107101941601c0c0090071560007003400b1a0864000d10000e41c120362211008a080f10090703501d40c802c0d0010300c400c0c2e00041c4410003049041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 512849784 1250 512848534 512848547
    0x201291003022502120a0605070311090a0e09100614280510031e060806010501020102071718031e1b0f0405060a0512070e06040b01080708070203040e071e 68
    0x428495000900181c004400f030000315a000c0400d07600b2601d84485030020140501138031400e58403912001940342040301009084032800c0b00d0b1103000110400c41c0912940d240c3c483c10781120305c415002115070380e40d464a60309001080c2440030009040040106a06540c1903640c0e80d4410281da01a54141c0c00c00c2510351039403554042c80c0b5030b5481819003400542818048000040031301d050100340c10525400c10204664202c142d400d40c0e66031180309001988003808024018102440298144515038507000d21f140494801c0312038101c80000c2c814405000c0500b01e2074a4a0000c0a071110003455a44071060550800e064100d240107aa000040c03488400033784800341a0b02a11b401c5914007680c6c1400004d12003c0d1080b9848405044000f5282e5603101c03110114040721380203814a1464000594080180608002d215500b4440590b00d6664010319150b805000382c40c2011403a103540300e090b400c1d8407842e000389071100d40f114100442d0301c0c1c001401080560038000b08203909120075a0842e0308 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 512851034 1250 512849784 512849797
    0x303130813080f01050c0a170604020f18040b24071719031b0c02041508010f090204140c0f0711090a0b18090d0f050f120f0f091507020129100302 64
    0x4c11031510b00280c8010b48d1013451a80414094001031030f20022010714034494100035041e440d04c1c580d294007034415040c14015071603020f0b02601c1060010340d8102c40c2c92403103401d4040711348810101151213000e014010340710507048020241401e41c0c0e45c1c021000d0101c0751101c400300354042414800809840154091688580e020958440842000e00e03401c00c00945030303001c004210842c0e1034a0100b05282d080c400c454035100c00d680c0c0010b016850f407060000303031410301c4041141c3c0044001002040c02c4064110b0b07424511200c0581d40d5215180780c8604061440703103d01c0c1d0041d1881082040e0400740b0750010b001d408040322060082281e03514110100c6030102c42c440b07102e801224509070b03064024280098024242d08143c0c0c202081c44c0e8030540160011a5540240d581c10004e000010400a20454010070a50510307406803034030305c1000d40c2c1e40c54102c84841d80c2962100000c1c8410b4800e5100d51b903482e290000310f400d0803440395078686800c118030030428805d000828403000b40d80d0280c801c4400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 512852284 1250 512851034 512851037
    0x6060e012d1214100e070609140609010c0201050f070308040c12030c03050c010612120305220b0a0b1e1c0506060d0305090d080c0c01110303130813080f01050c0a 71
    0x2c1e4860300e583e07408050000080104100e125090030702599a0741d0380124020705c6548030060100c20b1070502c000b480c1e2201a84030b011605201c0203c50341c40e4903003c0841b0301c1d007042802e002c2c158052520040b84e05110341201006840400f180f04020190f200c1c10b018002c60141280740b0116840340a42d81490541450040104819a64040020b0301036400390040f54104000080d065994100070600c0e0f0700c6803c012903414440103407000486802d4131a15401402030203462051518543d04070aa14201d03210103803008090b40c0000b10200035941200c5071100b000b80c150100b10300402c00d0b002c80250080702d9188211565588959a24072078041c0390021a0004001c10060300d90906018901e003e040d002d8041010800c140070390fa8803683c812051580c80b9550041d5160702d610521400d020000c1b840070b040258a0410403950040001603076001108028000d080701194a03008030f0074070031035a0b140c1941d0854100010b401c0c070701260a4200301260402880281d5078041100c0c030703601c00c00746d9890 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 512853534 1250 512852284 512852309
    0x1805070c0f021215091b03120705070f08010b040c05160204050a11030c0a02060f010510030b030f010f060501031d030a0c030c0b13050d2a06060e012d 66
    0x2000700390510075141c1a9400503200050031003d00c00ba2904203035000181804100761a0103000c05a41d0400c0506000c00c445980918403001510009485440004074490312101c08500c550030702c9070a0100344020003071140c10640c410350310404140684002c01401d40300364540003c11601e540101c0882d0b502010080406020102503400c0000421001e0400e461040e030700c0544014650172040114004c46a40e0015a15244003960091400324010300300da02600079080100030036164030718601003550941c10081041440c80c00030074034014a03064591459030030b00004048060f810b600c160309035402a641404031032091050124401480440210303e6031040103c105060301c101a1441414880c0c9400e0110306019242d28810710700c00e4601683c4058006aa42c0400c0000c209002d40d4940608012020020040d00e030040880d00e51940720302156440300306010411194808405484240c03410002942c44107a00b480540c0c2100d5800d8080001e41c02e110408021441c080044411851407074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 512854784 1250 512853534 512853557
    0x131406090705060f0c0109261207030c0e130204061403010503030a030b01090306150e06040c08010e090712080904050c12010504020d060b1b010b06090108010308070807050313180507 80
    0x543c55102d000101c0e02c0000c2071100011603182801100b501601802d481a50902d5001c441c003050040e08003600d05100c0108541c44a13144500f411551051040c28001590b00301c2444c1a01d00c00d10010340d01368044030b02038800030223407036540c040c005680403580d510603051180800c20056110030300450380d160b4024492003180502c0f0780c100449121041c035041038426541d039207042c25140e00c03e0803841402d0411800b40504142903001d5a1303c82011101884145480b10b8042c21420701801125a140d20f0380000440c1e01208001000041c01820220090302c135080c100410103801c0440c02c0d510513410207022a912806035400d81c0c001403242e0708000c0840c0d190104202c0290700c80c1310105c2c03191707403107410000301c40691201a0015401215024140c0d5280c09800c60840d242210010b200e402c00788040007680c0d031702a0f416070649a1001d6650780d07400c450300701020a0301800200800c80d02c00014524420629001d18030200c41061a03010a038540c004812810386004980050016043c010034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 512856034 1250 512854784 512854789
    0x10306050a0222150f0c30031a01021f1a1201090506012909041503120f09060e130e01060b121501051c02040e131406090705 55
    0x855006005510014034003505420f10443e140b01904080010482d80d010400c5110a04007103184500280c0c5400e8400340855000500b051203018006454100801c420500c0c895000311203684d005003030481210f82c0f041c1a07400030060040000421084101081c0c0040c1a5000090300400f540e208208019004040900070000b800310b101000092074a10007041055140c401280100d401d5000000c20301d12002d04100d882c142c01039010500c4045101c0081e5008400412a0415000d02560391603440840c4000140588612507040c21164140000002007000c1003030810107501681e224415055007140064400d10310510550700441c10f40140e800c40c030315064107130f11101c8a0900d00095422130951394942180c00369003110b0301d02500002c0b495080ca0303802d519281e0204000004500794a034140009187e4001d01d0382c00031106600400d0348109070305076016103024007404d8144002c10b00d80160f80c8010f18142a4082d28040640e03003410b01c12000100c0d070301d44122401d000500d000c510b010107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 512857284 1250 512856034 512856041
    0x6080d080705210f0a0b0f01020319050702091501020706050702180402060d1a1c02180601050c0d03090212011503110103020f190e0d05070b25050f1006060206010306 73
    0x1102c0f0301e0203180c0481541c080600030150b030b00030480c400c0240420b20345940601e08444d07120010301e100b0b0710100c0c3c0c0300304540c1c0e0020403100352540e2402c9134880a100c031102502c980c051520003d5004095104002301c80c1c0c2c414503400c1403043c0c2642214129a60303000140c840c1d200700742000c1d4101c40121054120740d6045200340741c000c0d2014081b1868036018030711600c11503845c612001904422801c500340a8580710b4641410880d03019207000011145500180c00e02c00d003200b00ba180403004000246d007580c003a805a0703d42d00c060f4001e484410100b0705004004000c0f500c4128466001c1d4854184940782c140b089141c80d00850180e202c501d400c503210b10010809070074580e0304040d020042c0200040918000e04181c4035441307030f81e001c4054014006828500040c882031300540e1581140404100c0c0007803035100303c2c0d000300c0748a5a070790841400844011405c05000030080304030741401042040024000c83c50842c051300742c0c2e0307060242032490000c0d204940f0444d00140c2c0705100500100303001e940b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 512858534 1250 512857284 512857297
    0x91b060f091e0904060525201207080a020d030509031e21010513021201150c240f2c0102042705010b13091d01110d06080d080705 57
    0x40ea040040105800050f80744508031002c8070899143c00501c01480e001440ca04200001401c0c0c075000000801c2d0014002203072800c407040d001440b02c1112005140a0160800701000b80074403544d900d0b424107221110b64010010f07040103206190103031f44072901c0b03442564080c0022201852a03c3e266400b480c034201d986400c02100d4400402102000c1d5081c150036513004854481d03a00100e42c900000c00c051010111881c4081c10300405c4240180691000d0050640303040c0040128100b904480c01c50b0305d05141c950080c0003042090b0301d00c601130700e403000440342c1408060b000c1c08040c01c4c0a04034000c0e10245040b0700200b01104003442464407148065170700401c50803000505140e0745103101c481901e0302145400c040c802a42000e100d0a5090181601401c3e03240e801911301028034105146141311445500305655940c070982d09100321075030030547c84003c880c00a201d4080761001c501e00662100280001c058a00080052038000100e1510505030003502c400320300c0d40d070b4150b00751454cd1110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 512859784 1250 512858534 512858569
    0x8010608010f0b071b0f170c18060108040c050a06030b030f0c011e030917030f180703030f120c0302180108040807020f12100f0e162705091b060f09 65
    0x7034045800506d108812000b0803103040c504040400c2106100d0800c1c42c00789280d0302501c2840300f0320341245000325402d6000a001c0c60103d01c20b994a081020884c022a00704903400883c030f00000070402d515070419400321404074186d410280039581c005a480c00c2010940780401c45103070803000702031001031100c2c0b2280c9003418040748550f010380e1032443d14001c01c4d88421100300d001c0244140d89500280c41d650224620103408258422003144a9a411842c44002e0403c40c0700b0311400d000034862410040b0790000c020f0140440c80034208094003035042807005600c641c1104280d200c0a41c41a02581e0286030801110b07031825805409012140001d4420345402400001c1082071401d01000302520001c244400096070b1043e9400380401d85428082c000226400a0b9400110f005026120f07400c507031990000300c4201c01100c0c2c003042e084400c184c0e010b400ba8602004c01c400c058000c20f18a02913090111100007000030581042624060003c10003062130b010b01110b40381c1d05281006203c8105003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 512861034 1250 512859784 512859833
    0x90a0b060f06070c0801060b1608030622050415090b0a091a040809010813030f0f030608070e040203060106051912020904021c050108030301120f140d08010608010f0b07 74
    0x1d8401103103a6074410302c0221111502c4c02810400940d080c86000f02030301940c03210a25100364032050454a0070703802c0c009000340c403001010400d02c0d034401d603120440c43da003a0140c00b000402d48201e10020481183c060310b05049400c02c0b4140f000341441003140e0320b5440506401f041d11421010001441100c400320ba40e442c82c404180b140d881844503a40c41107202d01c24090303580c500360000601c144070161030344e260b1201002c16140040d4000070440569000383c0b801c503844080a86084014052541c4074803980d025889000c1060014102480d01c41c50003030301142c40304c0e41d179900200ca01d0310a80740c00010000c1780180c0d14118510840c201d10384100044030146c200315804c40020304981c0f00c26200302500c8041c140e26a0080e800c0d0040b980100158005582958941503450207000702c0d488004000d441034040c1c000030084038450301034007207030203500301c41c4440e01100001d00655004c0c0518404100180c0000a0103080c0c0c01c020010794032500a03140c10920f0702d5441480d1030028080400b18000c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 512862284 1250 512861034 512861059
    0x60a18030506190b0a0509010b030a06030b2a0301050120030f040b030108011802100c170301090c1d0303040303031a0907021e03180d2102160509090a0b06 68
    0x100b0a9500820082050302001448401c0d507204968402d50440e000e583c03c5002082655144030015045900300d101c010360301e0383d4618026006207002e4100801c021200c40c00e104460322520189101c41c44480900401d01062503da242e150100b4030401d800545e02e1282070004c600071503120041201880c1c1222700b4410341c2d00c0da0701a03a4110340c1201c441c11001100400c46d03030009004202194002041806c0354100c81d401060340b50005003401c0050043c030040a008105010300441d202a061811503600c03940c40361202e4007d00494060755001500c0d4121809036104007103d41d080002004005500e01440c640c0e01358081c1881d1130510305115104507514079a602d41d000c4592040c1d54a60207095a44c51901032100c0c810b6980400c0103443e4014064403800d03039036481d140c98154400f102c40084609081c949004030700007403054050300004400c0d020b010aa000113480050b4228020b08c25603064070780b010f010000c0b0341101c0100065201480e240089030903043d180e034104001501500b0b0054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 512863534 1250 512862284 512862293
    0x219180f03110d081c05072c1c0b0f04030e03030a020c0f040b040c020703020301110c0703020402160804090504120c050309040903200708012a030b06040504110309010e0c060a1803 79
    0x1410305d9105c044180c0c55004005505070b000b08140514007805d100c4000095062104c4045840f100c907620703002d6803241e40200700c082000009905030f00c1c1d2080f9a0407840c902081441201c0d00300fa9002c0780810405800c9026a207408401e550889200c2d600600d00c00ca1143c04200500801c141c40740c2d0840c3c1d0300e0b6214440c0703880340e006441a0841940040c00d085245105050850b580030154441d010000c2c0404541d150b008102102207079012200503803100c40c5944a40da92a15000340104410030000740007a994000d0b0b080184618041c120800038660020740c00d40b00c1c040760580040c940d030001c2050f240585060f51011982c24000d10b0440c0314148218088011400719001c03c10302d5500c03030482004400b10900070341000345180800c008520a0210440c0028141480c10106041d16890340d190303a83c40d0708040d6070080900400c144881d81103c401401c84d40e01c144e4051540e9420118050707501c800003d240b0703901802c0176121500e0040584411680444004070f545841c8814000010104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 512864784 1250 512863534 512863567
    0x120b0f091302010807030b1014040e012c070527060c012a020705011d1e0112091e03110a052404020306010308030a0219180f03110d08 59
    0x301460704155a000219000161807424014902801c150030403000c841d03691102078005c6040e501e1814200440c00303907250422000c0c040c6400420074144200300009823003502150546146c60a1079800d1101e112030028540300150494600010850400401c01d20044801e94024010b01d95800c10850840ca807000411031b0b44004c2084040e43c0d1a6004082d1541d418140c035070070f0720303010900b00d4456048400b002c0d4075040e49210302410301c246000b002240c2014880366241c040e40041c11451422402c40d64042d884058846450000c0c484032003010703440c5400d215886410760002200280900c040c600804040c2e1035850440800038042012950080200004640c061040300600380020491201035000511146210070404000043c000540c13000f050300c4c3d054903000000c0c1c5540340e42c0d4600d1040030384502007450f215624214880d0746d0340b030f40c0660720304003803d200c1d00c40c8001d040c7d031891900c52459503400064006140c200c41c40b01d01d4030b010898240c0d503a105040351070529420b1510085271 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 512866034 1250 512864784 512864791
    0x70506070c030215010b21060d08070201020a120203030703050939090c190c170a0903121106010b0703050906070507180506090609040f0f022103040807060f120b0f09 73
    0x460b400807810b03003000a520f04412007c0030344800000041e1405100213038008000d54005010300b070001440d282564424000b0901e603980084401c1030506400c5c1009640382d00480e403d80010f0301d81400b090001001292503444400d038a8bd02c802682c03070000d20000707a81601940102e031904480948503486d212122114864140954000d494442e040200d0f206480c0c0401801d00b005245400d2000041c500e00c41c054200c0c2c04002d80580b40c2500c0701b0243d4007801c0c0340d0070241c4072484042e02003980c0342d4015215448800b01034180e40880c1da039201c2d1414275008098008011800c107201001071414580c014081c554054012520002ea4480918280c80841c0341480c101c10b0b01c4a041010301d0914400315900280150f4000740e0303d10b040d488800700c0c130526160007404010201e82c08810f541da01c1c428501018009020b41c031107442907580669580c0d025100d140d85500484900103640760143c20548541e8155444054032040036085a20041c01244c501661289440407500c40079221300341c05610 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 512867284 1250 512866034 512866049
    0x1005010c350c1005160804050307021305150306070f211b0f0c03210b1003140603030f04032402040f14090c0a0e0d0602030a0b1302070506070c03021501 67
    0x15982c0d81d010706107040c0b8000c0325043c244141010b041c041305c0322200c4e040c800c0b449401d1400c005161a01d2a000d41127205d0314001940c010110b540210b0f54599071303404140900300c801c0c80c2007030300c03002c1105158a034039080752108082950100007409950181000c46400e0480c909440f15004008121408495000c1c00e007001e0320030900c0d86115841d0b0000740c41c100710316003420680100300c0c0c03541e0010502d280b02c44015094241401c0d030890b00c40001d4000c400d182c0300042c403007007d828415a00600a0482d4554800c6900c0042c1c0407940030308010003200c800404440d940c91030a401d40d250700c182c041040450701d480c039100c0c1c007200c46c1e40705c2e0b148042c0001c2d111480c0347c010141d20301941c0c1d404460810420501c10318105041c002e0000462084403580045820040c1e12040c58500245043e0180400038003541d0000041011007074041d40905003100c0d040320620810644182088201e02689d036006196500800100e501c00b8020425030074094828411100405540514860345074000e81c8401c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 512868534 1250 512867284 512867287
    0x30207050307290301050604060e060705120306180105300f10050702011b030f09020603040b040c080a050304230315150102010e0a11010908031902061005010c35 71
    0xe03142c84000a1120155180032440f500707550400000540610580c42980e05103d042034081d005525003106440c120340d0480c06032246c9441030140c4200030fa00864040e4420100c01503031441e25145041d5071410380320040c1000da4004100017901401074101c04255806d10002070318a0242042000200c001c0c0200102404101040d00984400d07254003901c08030039a410107000b41c1ea408400b0038140c40d450300c149404a89800401d0840d40141460800a50000c80010411043c005841143c0c2d02440c800d19280640c2075503900265260302d80c0500040150300200810400b90419000300c01102000041d01c04408020b540068035080d13196401400e82c0701c00b9020015020302580244801c000e01b80020701440307600354500790304e4901c2e1040c010940f28408900c0700c071a92094200b400540503001c101e941d10135a07041e01c440c0940d1046c20381c000611070745d0000744d03401010801240450354181c4544c00756440703070b0b601e13a40c5221a80d829800000d054000303181e07440100744c40e1000010505619907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 512869784 1250 512868534 512868569
    0x6030603211909080a12030608030a030b0307090b0d0f0213090f0b010807050a0306270c0305191205070f061a090f010305120705010e06040b060108060a0605030c07030207050307 78
    0x101c41002c24400c011040c0002500c041244040200315a14a194041a501180b0000180c1640244856000391005102c08102810010b030160b00280382d00e04200e046a240550360311901065542c4400b020343c00000c00303110800003484103051241035a1008002c00c07240c4982c00c0105040360608842641e81c0044400910b0034850725400603405080ca80014040160070100410700911303480c88014001540c840038400e42410fa4003060040c52141c421003100210b241c10b140c14080782600044d11103000d54454944119404520a070b082c9510800080010040080603111900611010b8801d081103881d4000028024803461002000d119244031458000a05010003060020300c0302544905140c01400411000100b403590103104499031551070405241c50340c0500301c400c0100c0080c1c072680050004004c58074801d40e1180380700f80c0e5000c03505e03070f2082c081050501451042001061080001c0f9403142107200017064114000d0045139500c0e951400403034908281c5510100c0e0349208900f24 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 512871034 1250 512869784 512869807
    0x30e04091110020606010f05250c0e0c03060f1302070c0e011a0705030301030b06120106060e1023031314030309010c110606010f030e010c0e0a080d020c0603060321 72
    0x744501c042c80c0c80242440e15207600060f0003017030302000c100300707000c0045001200c0200e940b0243c007011440c641e081040d0202c0345451142c1004038081c050b400c8040f44001901400240150ba1040200038a10b803540b21108007413243c00c01c840301010307100503001c203c001d01040c4210106070003804900701c0300c8155890518180c2c8010500d44050b128007404200078004903100209070b071f0649410102010341911341c000014400c01d5100d5440300c0035400c1820029403076800010b01c1040d04402d845c050701d203004202007100c0180b4540420510035440a0880c0302c445244001707160703c1640c40300f02030104501d03034079402580742e07000a0308410b40d800002040514903081c0621880c441c884d0a1041c03aa0203d070480c40d4030b5450003040141000020740698070a284281c00c1940f80c605100000c210140340c0010007403082c0b468688a501680241c90000303071800c000161050f603000a517029010800c510020002c10b640007401841d41842000b4824035101c001c2058814000d000746401d540e00c0212499 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 512872284 1250 512871034 512871049
    0x18121103040506041a09150705160509040b07020c040e03030604060909080304030f0311160c0515040e0a0e07180509150f0907150c0308160f0c030e040911 68
    0x81448103900180410440c0c1d4842c0400e6030195404200050803400d0401800c0c40175000703250445600401d179800e480c0f16107400c0d0f0000c10160f405a01a900942282c86462501040d54032816400c05445000200402c101d0022280c100c03080740b041e030300000112400142680c1e0380720790f00401d0390000000c3c464146800e205410051420b994184050300070364982100e42e000003030001e010702c18102c10321401c0b10720903032294000c01000e10015484240c81030428001240b401001c4a42c01c020900204403481d1144207030b00e500807041c11a40c035003828440c40c4d40c607550001d000002420b883cbc080c0c10244090038070500001c0d107455141000001d00180c41c5605071100070740100304c585c00044181d01c0c2d030b1441207003082d8001c8400301c0701c920701d0b219007104c6441c1c60b003194400140c00003a840d0141c01680d200e03a00000c190b000f6500c034440340d1101000702d0703400460300d24110302007000300c0d041c041c4140c043c00c1c1100d0054024280749240364400008503090324070036802202c4c50740001d4072741c7c88070345000c46 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 512873534 1250 512872284 512872307
    0x50c1006120813030b0c210f07030b01050d06030501021314060a0813050d020303180705091b07080f0a0f0c030f030513020d1101080106020d0519031812 67
    0x200a100d840e16110070321100050100d005040300e9800201544680c000e800030400840d030007602003650385050342c00810740e90401402c2c81e02e0221004600d801248100c45110b0194520710b002010a4a41210036401004212071482c14400144906c03080c6954912840c00110b0003200007590703502600a10b102c4101c1250403d0120041210030158180ca07448103031014081035060091541d00c950011071800180700038001c001d841443e40c00c000580d0b02001460041001009e940050140000d4240e159003880c0152900201c0d0600010a0344049000c203518904007101c070780d440c00010780c45844407071b0b00c035840c0c1e428800707400508001c00640c00300708400c10865501d00103c0301401d0796401851541c45003900001c041d203400c08113040280a030082da05440e030060203140c0ca500d0a24040d21400c0b07600d05c1d01c501103810b1100006005001040075000400150780d41849c0c00314814954012041c8070b1054020103550710f402a4490181c1074104031000d002d000070150703051000340003d0400410b007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 512874784 1250 512873534 512873563
    0x1201091a061f14030604021605070305121e0304020103020702060304060c020c0a15120b0d0c1406040b04060819090f12021b06070501181b06020109030e12010e030a050c 74
    0x8080080700c0c0d00050501e401c3c0d08001c1c031140d0f01d843d40c03000107010340600d07002d0780e070300b0080101030383c0c2080000100c05044901c18415588168101a01c04a2a000300c0d50b0442c10440304034649400f00505200955105105040040c02e01c4220b8010400795001182c00b1110580d8a4850144070350b010040461854000c40f401c407036850826030401401c1e4a40307142e032401d001c28414040c4100440b50004481c1c4036001e45400f00e200014200344000c00c005101d0000e15144040303407002c1c5820103204407801c3d6150503a0721840d2528180d000c50b034a0000902040707128241d4408000c0d800450f00913a50b00394018034044035078200034185260a42581c40c854400d5501102c442d00e40e44284007280700028030201d800c030782c0f03c0d45142841d07409082e001d00d90030309141501c4e282034108030760b800c5010720303443c0301120340c031030203034843d0340c10b9080317942e540320180204441001c1c510f450f140010041c002e4a09240c0041054514440d01034619007001c24410082200800c103540c4604c000c20007441c40e540031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 512876034 1250 512874784 512874829
    0x314070810090818151911030403081e071a040b0a0e1b03120a0305070f020718020309010b090406020910032a17040f1103010506010e1201091a06 64
    0x1d0b64808000340704050001301d16140c0c918078032030241e48500c3d041142c1c1e0810100c96940b1070721624081118040d41c0100c00200d803c030317000c070302514000006845c160ba42c4464000d1400c44855403010165100310203264000204200780c0000815150912074240c09015459419050170703c0c02c4408000000c0425a00c245051014411404001101c800700158801e043c003500030144042414410a02070300303044801c000601d00c0e195075050348194421109a65540c2000542e944100e85a684030b210300314048241c2c1400300d81c4044035900842d0001200c000011b1501c0d0030302c02082d000507045a059036050b0340070412001e5401e0803650810400d90310b1400b0089911221038108560049030341c04a841868400c00c038450500418209071443c40955004286103080c0c60030f45000200200c04a920400c0103203c50000c0c10140540c6001d494161105c29901203a05d0920180884103040740c0c0c0203640b904030b40c00110b010341c0034407852800f103100c04c01402c1c0760000c03d00c440c4040c0009144c0082c82c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 512877284 1250 512876034 512876051
    0x406120209090406020901020f010204080706020c01020a0c06031503050105100f09060806040b0a0e06041212060e15010306090c05031608011a16230c0306100504050c040314070810 79
    0x161000b840c1d5009910400060f10303400750500407860403c241038540002e41c400034000c50f40c018006810021200980d086580d00d580c1036004a8032403583c1100103001d1441c3d05400d2082c0c50281e004110040b600e08801e10017240c0d03030b468031803e580303040d200f00e000d003000031005000014940c12801c000d840d03420340600c1410b1400c042d20341d0311003004102038408031280c3c002c00e140c3e100c1d0b03130000c1b4164581c82c1c0c22140e4900340383c1001a80d1143c2041ca000200c2c901140b00b1012801c64087d000c200c070382c5240d1445195a034401024068202c6070242070405590700c101250042540c40b41c46072154940e0703038a5803a86841031034280403820160103d42808680e500400800111410f513401146e00c1182c0c0988808407042c0155103a10300600040c80081c4031450b201c085c02810240b0364000081d4401c0b00c19030940d0380149a110003054520b22304d4004a490140500e0a0a8000e00e40000003403c40c00c0c549941c076191a00546001007100303035140c00c465400c02100600f08411854012402c40c100710600d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 512878534 1250 512877284 512877289
    0x20f06040e09071406180f0901030c06030f15030f05120c461e080a08060901060509040e0c130b030631080732061605130b0a03020406120209 62
    0x900e0303910b40d40c1c0c1c259002c41081b0303d031182c03c09201c0000340948450b1607540c491030004c00c0c1900705d024110010f890a865180d81110358040c00400301c0c20a001c0c0a813060850722a03c0544400300320580d041c1c4564101c0d40c40303021490005060324811072019003204c04001c05004d007641010505102c070080c0c0950140301d070303c480c035280c1d5100000d656040704ca0340145c1e1800e4034400d1140b0320a41d00c030b4241756450405002001d401071004a449039030f008600e690781010449503900a0145c840014000d205226090501c0da001c60800a02c030002c4030840d104090011743c005040e0441004125103960b5400e0083c00c040000701d400c81e401e081855a881c07840c0144400706c0c0d0420741c240c41e0300d01841c0150418080b0340d00465608030742041515800300c0b40c00118044140c200112140c080950980a401d08031021440c40d000d402510811034184001c0c01084500c1c0c3c00003401c1000c000c2c1d485c6000211501000300800d5204a80d49000d0384603450045d0140920001082070034015004120340c85060303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 512879784 1250 512878534 512878537
    0x108010c120504081603090f061713120311090405011805070f020606040b0f2e0c2a15020f0d050405061909051e0301110a020d0c020f06040e09071406 66
    0x90100c806401c080700c814142210100c0969002c41d613940705002009c43d6142d0b120511150100e00c42052803002d4482e920071070043d903010382000d80301c10400140302244900c00c2d044014818800f65144d41481c0f40c02000a00722030080e0320984070f01004c2107140501030018015154032407060708112449203000035000e03403200402030040384120340c1e51881508a941300044000c01c8000604170f5002c68100c46088a150340d110301d445804c8050030088600480d03c150b42c50007040e42d0021042c4030307540520341c0c1280e2000d503000e10a6504501035002080f80c01c6107000300c860041155004014504020320200e0814002c4001c0c94100310040201b409140c83e500e0440c0d030003100c1141c48446961103484c085480020a070003d55000540c9018110080c020b51b441c2d24a6400441c003c00842d08056907105032413043c01c01038005a04058441a03c80d8042c80c0001d80307c6002070424800b40c8d6070800040c501d1f92240d000b000c4030580758814403000c2101009140e010300449400103900144400025005d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 512881034 1250 512879784 512879797
    0x6041d0a0b100f0801020a1107060504060e030307050118030806030703170c1507050c01052a13033011031b0a020303040801090308150901090b01170108010c12050408 73
    0x401c08400c0108040c1442003100c070004010710103481c05001c3d00e83c02680d01035441700e801d90000800300015900456404035412040304d51a48809103002d15019007602e0100c940402e10303605000601c40c60700800c100b030007840003000c1070b4036441070030100515019280c40d6010302540e000f80d10250080c400201003c0351100c5041e90b542203a6141c100101d81a81707440340e1031001002c082e03019024820001d402101400403060410001e0010380d07580d0900d030296039a400b07504000826925101c00c43e0810b4680100307a10105440d80303010107512074841c0790340300c041080b402c418480301422850711601100007107803441e00e803460301e0780f00c0d000c8480c407150b901d00034608030004070603400c0c1a4006040d82000100c0c0351941c09000d891b02c6940d02c4031a00d000303101e440d60079008100c0c2d807000514100c40c0c812060f0080c81c0c0003001d8412907420304078500d0003404110403040c140505075a04c01540200144d00b14000e005280022511003c284001460b00c4101082210032900349000d00000564550941701c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 512882284 1250 512881034 512881043
    0xa14120a08090c03152e031101021204030c1701020702030c04051f0e10080f0a06020f09040f050702011a0d060510030f080a031d0d14090a090506041d0a 67
    0x91615a2001c0c5403d0141020344264180b041e13040c205804980d84590903c1038500c003070040f40b981600c1142425041e445c60300b2801d042da4004040c400a02c20003038100e4229010720441e04030f400c0c0c2800303680442d4441e400540e03a01740640010040100740403100c908100c901310003981000341d581e01203551001c020381c3e801c2c8070f070f910f62000801d0035840700c00aa00c403103015500d00107001d640303182003400130f4416100c03e450300400030408907042e080000d6048003000380400621000c03078991142002500070074081300c070b1a101001804003568460080b00200c002c40540021242072050000e401c40e100c08044440d001142c1040b60b40550b03c03a5160a0007980001011606a8a09031020411403480d0801450172051102c0241880002006890b058030a034404220151403400b01842c20501c02c04500c0c01075102c83d9200307000c98030422040201e05131000106080036030070740c009030f40302140d40c0200c07044c1c03980d4104000b8685031500420301d51011544801030484000100552140c4a4a070040c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 512883534 1250 512882284 512882297
    0x140a0204110c19081e0702030706090812180406060210051012020904081204080318060103020a0306020a030f0204090e15010b030f0c0d0c03050f09070b04120302030c030c0a14120a 79
    0xc184098001210701c4800045410700441d031805618085e6500480d9050740070b40310300280401c0707042c01040d881c8140c500c407200800e00d01b50307254140c2c800c80d442011070608030480c072411044a900c0da402080041c0c0517980250039540800203844080b070f2402020f007605e01440c004100303c02c0c000c031100c11f0805c036015500000281d585007001c61750b0b4807a600204a01d190807800700820300c41100060350181f80d200e42c43e11169605500d01c00d680d03001c00e000c040d620400c503800400014103568000d24464015040100304911945c010308100c0e00a40e0160352011b45621f0000d60485050003104401030404600c10115410840c008038a13000082100240314480b80c0442c240346116401c0c0d44007040c0000e0309201c40807191400502400003034a0150f8421801008544038100211741d4400345c80019810747d042610b007d481400d004001c1800b03500f540020807016035900e005000402c60700111000401d17440c2d00624140c400301c249050141c01c240c0000221001520340b5108542c0803805c24541310 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 512884784 1250 512883534 512883583
    0x3040213110405040b0a180615090b0d0203151819150e0c130306060f060813030806280e10080a1203180c090c0507020307031e140a0204110c 62
    0x1100c01d156a0031400c0c07201d00340c028140c1c51503865007023182902d0448103000b0240011038016540030a06028540d140c48045c0010740c2044c015901960307001041e80e0a0034224110300b40881c0003c04840180b01c0000480c1040054001440c4045100001c43d6401001250304e10110403500311110b00605100100d0390021401002601d030036103402d0400c549104071019034910f0314000501c424030554100a20320070000030194092013550744a004450760f00c120070013280d034003110030a4004006135440800c2c17906100f00c0ca5104011004c41c0000310f4080030001b42410809507000c0d4000700102c182e06040d010031700a49001140c100c43c4c10b644003001090780113080e201074001c2c3c6090101c0e603081001c50f400103400d110910241d0300485200000030000842c50050845861186110281d01640203e0082000a4000d100f1a074a21078441ca00c55803002248d442d80ca108108616000081d4041d401210a601d898445e12040300319850782c1c5032070f0020500070a52681a9009020045035865200c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 512886034 1250 512884784 512884789
    0x12c060304031701140a0603052404021c0f140405100213052701050402041d04050f0d1115010f06050a0e10090f0b070308040210120c0503040213110405040b 69
    0x1018a10f0100704500041903856010700040e070392500c822140315100191001440c207000f442064016080d5042521000c0300300d201c0032010304000c407500c40e0466801c0044030108880c02c0e91150b065413110b170001c05c0301c201180302101925003401b00342c19280c80302070500001901c00105160050b60411000d6104c1c80c40c41210401000c09620154000e0040708e4410f0071103170003000c0103895000f000320720002e0366207400500c002c82c0664054400c660104688070b8220081e600ea400b40e00c40c0c07117001290516180181a541000009401000171a80041141d46100414404003400000a81c80350a0940c5042901e80c0c921281c3e11505003405000105c49004500c21000311000b0400503200400411351410020080c030310341e2103026403c000b16980403400040c070800b2501d0f16078147e5a2851241c680e6020070901003c45d103685c100380141920282070111441c000d1901080d400d45a02d0b8403454640140040e9024044117500c1e034a19154a03a04d0304612041a1070a8581c01c0e200003c04000c0d41d4003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 512887284 1250 512886034 512886047
    0x31501080309090417030406050702101116020409060207080714061905071101140a180206090108100807080114090d020d12021c050109060509010803030f0a0b040f0b012c06030403 79
    0x5c81e803808180000c00c0005000c0c00e500039901401c1158203d034200f40c100482c01e030860b41c809445c0900b40c2400c103d0070340b003a2000b149010415000030000200742074195100d40481c2c0c01480300712118140803902c04240110171b00c400d1080d6500c08040c200a180005030b0001401c456050b540318030355200e010840e02e03881560b680401c1e20b01c5400801c8801450709a2120002c0100c0303015441c0e90030800c0740700206204400c00c202c8958050062030030b2024120056403030410043c0000c0c1c101e25100c81c00209440c007046400002c0603100000542c00e644502d803c50b100400030900400e030b5001880d161a032550018100d080203850b46003804100c880404401c019100303402130680d8000c082114a44101002da000604035880c44108220480e5140c05010540000740b0486c4c0381d80c0c0050000400c00c0201180d1a9840038589030b0000754249071500160071240b506419103e0a6580c3c85100b01c80e5030051800c2c228441c5100c82e030b0b010300e81d420481c151446c2d600102e44d4062400400070400b090301802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 512888534 1250 512887284 512887313
    0x3180d0f021c0212150a02161b061b0503120405030f07060e060612070e0c070819200a02040e01020c0717010f0b06040504090c05031b0315010803090904 67
    0xc0c04045000d010302c1d10880c240303500030016071103140074650044ca01c000025841c0c0b00a200701d0100c40340da030b441c80112402500001802e81800034000c40f0440026054240000b240e02e84410030003105090420040807403810b690308510f40105810f01c000800ca0001c1904d5840211941e4900705598900c0c00768118080c4011117090341e0320121b41c007000c02c02150800780c81c820380003049031b00740da40383e004022800b80341141050540d00407200600c00901000c10165100824a9100d4a0704100390303216070040d070200317000044482021244010441d802410a2803901ca140c1d11070300200001c0b900c154503010402c00003032043d9520482203523500e1080d010307a18083d0040c81900c0c48a235503800701c59251170b071654645400f54a4088a115818014455400c88800c05007101d810a81000c0600c00206102c1900795102a200400051541da080054442c014007410002641401d500c040c90325103140002c00ea13616602e50001481856000402d0300c001140440d4160011349980c200303940c9904065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 512889784 1250 512888534 512888539
    0x60105180f0406090e0f060906040b06120309030321100b0a1d06030106030b011e02060c0a1e1112031b030c040e010803121501200f01020318070803180d0f02 69
    0x144490410b401702080612041030707203400fa95503d580e4042c044c0d0710342c0000ca03401001354901300041102c904020300368100c080a000103ca00e0a0340d4140028a5500241840381418031580d0080540718040095150002e00d80340c00000024281030303004903240030740e070a14800c12082001003102d00f91049818105891b0103803c0f01c0e50ba5031240001000742501115040c042004022509415060003041a211810560250841c4d03101d00317080d8051035000559072402c002d11301c080300460302516580145600101d4603041c030154203080705c0c903042034100051449075400500402440d42d0055030340e800e07010f0081c1080e50b03480c1d48451a40b1130b140510f40140d108001d606001103409000040204221240303102d40c0c5040e83e1300c68180030903201001e000e207070004a901d19a12103901424880c45d100c8540102038a00ca1200300d801e090890b00b0071140902c012107102ca9550441100b07002c10405003000202640c40d10a00c0c280c0b090905501d101020300075150442c00f90b0901000c5025285002d500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 512891034 1250 512889784 512889791
    0x8160f021906050604140103080901120b10020109030e01090608162106061404051c0602090d030c15020901020d110106030215030f0a06080d030209120706090905060105180f040609 79
    0x1079040c408001d00303048a40b207020707518004104142c24259241c45040b41e0780110344525020030003004660000d810303030303600702c01d00d884506901c8540d58035400d1445060082c1c0c00002c6904143c2002040100704076003070b034140400300740140b10bc15401030059910030052070031344250182c81c5408481d0305099600308a01038403403110111400c170294000038202c0d83c00d941c5030103031003c103984660268401d51258075880412200705103c04030345003400e000454042d80c0c0040c100350100001c04c80c0c0703444c5880b08800060324030580b0410040c80202030340403084611011428070041000107585e0301186410401440200c000340403460500750000c1c000303142e01510383e40c40010b5010f0506200c1c1c00540710949103045050004030000c400348241011940c403407001b8035180010203070550003940003d5919800c44082a581c00a0300001c00c010b100900040c1d40d480941482d02038040212100a4500c40c100302c0c0400c903030900c0e0945030705409100801181c0c55203a00320000300140007810355501c007910b12401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 512892284 1250 512891034 512891083
    0x901030302030310052706150f0a12180f050f0d03021c1b030207060b18101e05060d140115020c040603020d060c170f01051008160f02 59
    0x7070210285015002640340d03229441d0302c9100708114414014070380070071031406aa004c1c001e44942d00c0740c2900b14001500c0c00d640340c840420101d10b0350f4010b05c4818600080021001c403460b0f80b101c0b2645201d00141800c2281340d01d8a051040086036025001d001400003564540c240081401090040600c282c101c9040c443e0020010f0003030b400180d22040c106c50800005a40c60034540100c0400d508811f9210a03850380030281034000b03400100d0142c0d00c081d40c1c0c42045650740c480c002000c9000c50342c4546c40a4a150000d40810202c131700c4e402c8005011003650440303165141106104d416284115011501c03000011900740040181443c0302e1458511800000f0b90082c1c0317100368180213000e981c251604003007400d00b0300c42917a94134400207402015030107905020030500d52040083e18428030340301a14140c07101e0517107055030003640c5006202840388010031441c41e04d41c42c0f0072031072001030501c5000c40c5404403e101255183c18452020300c48490100304005200380400b501d904003440801c001c400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 512893534 1250 512892284 512892287
    0x9060f12040b0601020a210c0b0f010f0b0f04050f180412090b0901020601140411030703060806070c050d110f16030b100f0b0702180112020f100c061a09010303 70
    0x4410748050742d00440d61004102c00e544007150101406410506201e50788030904032040c6c004502190031030030001c07120a84c20016013900042030081002581034034165052500c40101c200c03180d0311100342850100911483d50a042d822f44085800403200458a00c3c544401308000d100700700c1c0c1c240c40144109003048108580a82e040e10310500590ba034584140d22941c1004461203905011070241c3d000e0302c0100100401103070045441c96010300b0200c2c0054955084220b183c00580e144008680c8403075090066800c2008a01d13441002c41c9000c2540e044203454403501c558a10030344104000304500d41c112405010046941d41d21540c1c022250180318031580c124481000b400200d0f184048000491501012002040243e9010001c5552000c6c034080b0100819407120707008a0b040303001a8610094a6040c2003801c0c000c15200b250702c021502c8c5032042060984041c0394040c42204103101d40a004e42e40030141807507a030760289000420044035403441c40f10098400c03030aa80020a0b070008000c25 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 512894784 1250 512893534 512893567
    0x221703060607230c0108060d080c1e030406020d08070801030201050c0c1201090507080123070e1003020a0219350a05070309120503030a050a0b03010908130b04080705040209060f 78
    0x400030303400762555138605600441d44070409950300c0354400041010a404a00c840700282004404101215031b20f07000392092032041c3c1905014400360350004201002003540505c4145c001000034a4901d14030715102001411000060001a0410001050b400501641040801c045c0c400003084800f0039044d0707202646c0680030602e0120380f030380071300c80000524042c140103c60001e400c0e20503d9840510760492180007482c001c040070f0070005151034502d2240c03900000030040c04041d0741c015a0f14180003402919001086002030810000c0015150214902402c1e041030100c2c0076481c0691155401502e40ca003400d8070102500310500003406804080d04040241070f414441e407206400240e48890408070015001c101800d07580041001a2031002250b2006900840f00f6400180c00007031500400c0c212186d00c40221507896001074220740310191000800c0040a00e5031f00705243c40d04054441d52100b88500c51580520b0700465502c1003a80c03120181d030a005540c20796952150010340c203543d80ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 512896034 1250 512894784 512894843
    0x14030c0909010606110703020d02090705190801050a1d010902130b0d06030b100e04060507110f150a0c02030f03060a0e100e01060c050a0201081f060305221703060607 73
    0x30445c3c11500010780302c00400c12104407034005101d01d115203210340920000307200086c008420071804002c2d610072080c0556000c0041d84d00355131903070401e40c10041030103006d104581103200c00b070302d0308103d1b0f5107901c449100039070545076001c6015856500882d03c010304441c3e184c108101ca080f020031408801c540366407050301228010802031035251505184e2121b01251406050a060b510400103400b14400350002504a241e9280c142c030500440c0310b07482c0c02c0410f84200352040b070300080f0303a00c02d4061403005425004416000104031a207071000020759640700d40482c40300ca45d400840000c10310303070781e80d8420340040c41c4460707204c201443d0000d04220260004e000361a058a03402c4008211701d032181b000400036a5014001300000c0989400654a81038000c09003182c03000c0341006246038100110666008189944010501c1e040680d0014030b000c1c82e04142581c114071026508011503003040403410440103000b0101d40d00c1e01c80e45c3c08169142f05203a130291540c41c00c02c12050842c032011110601 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 512897284 1250 512896034 512896037
    0x181503070f12110904030206150307050418030207060e010504050d1104020f0c1002031b0304150f060504061707060f0201020c1506030d08060a05011b1e021903030914030c0909010606 80
    0x10081c83d60010001d000d4020344010340140d01100c00595812071800007101c40010080032505031aa0b10b00004041e0f80c100c00400c161745203030307520072801c064041180b40044d181c103040c800e010b400800c00003040c0b400b45205140c17090525403102d405000c840c3c0c2491100c104080c1c000e644d5a6640e518000d103a500c001405280c3d03200d8600700600c1d074001340c400d03a4000e035500f10300540d46120200d0016040d400c094000e541d140c510001881c5141e009108000c5600034080011501c1c600d044200411074000e50701c85281e103903111601c50703048240030580e5019598207082000e8841d42e0003004a0081c00b80c3c08100c0e0042c81010361050300c20040c076241902c218012012940180191a021540c0100030389201e6000251040f05015540c020841c1560030207020340701080440ba83d491705030030351000705c104d2140000000704850a41c1048403869108000c88610825034038130f556070040c042d83d014400d40c521000078000c01c00d2155014064000120030040036003403075003001807103a030007011188107600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 512898534 1250 512897284 512897303
    0xb0d0b2e0b04062003090607110d030306180e030f1617040e0c0a090302060a1b0807060506031603060902010915021c11060c030a0b060703080411181503070f12 70
    0x40d1849101080b40c0700c4407200d4003440c00c001b2040b00b40807036600240d008035030400e0724040814480e00c07460b05aa803094066540851841c1c80c102d42c10143e03483d161400810503060800c54444080e000045a5040890101481c0e45800c1c07624180302208502034010a101c0d40e185128003103803980070241064440c0d06200581d503172110034500c04c03944280f0702c02c1070116180382c004002519000015000c24201401c0c00c0500c070f04c42454004010082241c2251400d0700450f1a8050141c50300c145c6600c80400e80c01003650145000c40b01c907100c01d90b444014007035601c0d602c4000469100f03440c50401415864000c0781d4950003518060b45500c4030844122048078030044680c1d10500c118410036901d0005009004540c8400d101043c1c207078001845c0304030040c0c841110072601e84030503000342501800b9945040103401d15113440c0e030505035003d900c144611143d00001c80030500400c034141d0816014216041302c040c1601c0864108006039002c1041030007049000a894201d41461180c22489400000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 512899784 1250 512898534 512898557
    0x2061b21190903020a060504080c070303020114010807030b0a020702010212030c030403411317070911030601050c101a0306090105090d05031009050a0b01030b0d0b2e0b0406 76
    0x2201250300544018006174010740c00100410003d500903508207020b0440b0b140381584003500a894080385a10490040c3c2d0342d40c8841035a41c0c20841034030b0140040102900070711345542c030b82c90000038000d00020511607000860343d085a000300440820003c00442881d180d1911400d60012500121025008240c40444441c0d88100180f10051074880c1801c02c03010381c2c06142080401c0300c1c10000d4030401c4003010402840c0084858446400401c00300c032132000e00700c12521882d4104801030b40030000081c1060204004085c2450560b0360003942803070a9038559207400422480d01400d9400f6048440c544030241c41202d0361710049500e560425400c440540c0c946282483c200c8008440f041441c1c2c001c82c410f00c5415200300011a00b000e507542d03e1401c003e0301c4030020011140f0580c2c0c0b1807011a61b0b07044601d078550309800b458580e084116420840c084c0140c4458840010050420003001d08404242c560403845552544401e441400340e29580c030780302c0f01e01040f10350041c0100c1d800f141c04003141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 512901034 1250 512899784 512899831
    0x150b03010b010f050a1106040602190c0f240e0d1d030601090c170f0a06050f1e190f1703130b0706092411070302061b21 53
    0x14108041010f03903c0000724241100201c4e096003141312000200003c01450841078003041101c0c9000303901840b00160398140b801070600b000d03c1d25008150500440c1442603020480305001228059000300c100140d54074081194030b10756441c00b0401200030f15202e10b0880080340004c0c48a07525041d078590800c05000000011058603c0350303140c82d8941e00c06401400000d525800c84810760a040c142040d400000c0a028410311604840da1101c2001c02020452542900c2c0100002042c007516046070b81c08014003c215032081f010740d0019151540c4501d5075494540070440326620240c1402c040d11b0a485420b00e207014030032803040d0344030030701d1032140041c0865020007140c402407051150364005d14a48000c0e44010b402810069442076581c3c40400041840d08840c009601000d40c0c0800324001c03a00d0308507086400c1400781044040045c401b8400094000074059040645000000c1c403401040c99482d14a1185100f0902003e241101d29030120040685081c041c860415884a150740401da2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 512902284 1250 512901034 512901041
    0xa050301020906030105040c2d08010e010e15060c030406081005060309190302010b040f0b03250b03090a0c181107020a12021201112823040909150b0301 67
    0x2caa482441000100114540b65001034a140e44609107801142962001481715014010807860304503400c0404003005503012000b08d016010300c160648282d4113012200d65044001002d101c6000c5214110200c030303588400c10389e400045000c084a035990340300c1c0d10003001c003181900c0b500b0948403000c0c4003041510780082900d2103055000f00610451030141a0414520200c110a6096543e40c010105403502d45000362018049440c4011400c291400c0900d480c7c40701061b0840b40500504000c440a5076004a03c0e104540041008503140c1d02e407003031840e0030504041030041c44000c0c042c0300000c03155075078040b0303103103201150340e0420500c040304041c0080c51090760b8009521900000c02448411500d1141e40c0b607990010f412440754580c150035030341c01c440c020303610b00d0072102e400b01d0841c0001d10f540f1511040c1c1c1161100e0181c603002160000f51061114182c0400046c5c83c0450050015150f81c05840c001c11815105000000741800d02404010b5120b84100c81142449180d42c01f9060501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 512903534 1250 512902284 512902297
    0x62c0a05130b100e010b0a0f0f0f0c030215160912121b0c0308090f0d0f03080714181005070302070515040504090530040b07060f0e07050a05030102 65
    0x481c20708140a40d45030310701690000e10a038000340c0d40394004078440008205440c082d01c40703010085e84c0d4100e1180090941c3ca140c0c1c5c0c921081001000985000541c40f9514110111850810703014158281c6003e034108040c6200c16140c2e41c64041c10401512010788120760000681d03280c0e901501d440b10300e000c400c410340000c0030300700c83d15514810459a10580003403013045604281810484625650400c0c1440c0c90b9200340d80011000c01e840000745030100719002039010480d4255090b00342903071152a00d52564401030284101d480005002a008002c0c1e4003010000141c0c0c184d903107030f4282e542c68644416981c0d031030040d10400c9500d80018058401c0312595901a0010a421442c0000700143d440b1042441c035200d100c1844001151b483c1d038002c1c062901d12a0026198031004a464001c600e920703110711008514054040030718400c0284111010750340b81603000c46c0d481d189428120017030100b041441410f28035011004074000340119220b41a84c80854244d082c150351101094281c0c021038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 512904784 1250 512903534 512903551
    0x9180f010b0a0f4a07120605090a051302031009030f140d0c0302190309110d0804090b0a1a0c0d050310140d0615030c050901060f12062c0a05 62
    0x481c58881c1d4800845105a130040c500e400c980d00681410310a00c281c020b03449024003001014824071003516084403851900b0034445800300550307407500001800075000600602d14441c1d45401003100c0101c030700314590740c66801504440307503400744100060090920b1002070300000c201300750951286210b1041c00a510210303c0d8610b040042d0f41142d107000300005601c00050503402c00c000700701d5010032450031001c038100d40c13400640c1004900f4030034690a0320031260b61203a47d0720140b841c001001001590141c031540500005c2c4640c109001c2428060143c05c16070400e0341007404001c031503032008010030102c003030102659060404a034003a141c500087d22102d8a010709910b0a02090000d81c5000e10084d800400d041c14150440d01c2d020101c401485074040100c20042051050201c100b10a20041500f52607000ca59894498024141440769504104102408158001d619000d80000000d08068840c0640103c0485000c0d018010718076007030044103104d0300000d11400243d01c02c807072041d00c21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 512906034 1250 512904784 512904809
    0x50a0b0f0f1f050913061a0f04091a070306081204080d0201060303090501140409020406030608160503100b03031201060809010f18020d050712300e09180f010b0a0f 72
    0x10b03d820420021002445010000d0164011a0214556015040c5581407181d00404015045414060004e100d62400d500907401c10b00d0500008a144460f2416103106070800f107025201c0b14000c602811080e48000d069118026078115640072880c010000c540703401c02181d40c00461102d040e0f01745d600768800540460b000325000c01165020b0006901c140701c50711030244c902a01c1c0c0040f40e0880e00242c0002001036510181400060010880c0002c0c0c0c008841c1c41c02401d81c82d00700001d50b40c0b488070323100d044199104e81c203105064074204162800308030304e001c080241c1d60b15071a0040c201401207905852030341c20554505011030081c0728004003191300e411a00401e2006400703000e562000303000c00f1a018801d541e40010a8000e00d0003a04c40740e0f10491103002007100200c01c80070712945100c90f0b44036080300460410b6400340c00c804601c0000b081522603176026604e41080d204080900c0c40c01d6844c0e4003420b6040c0503088810741c00310f0004181110f403512620b80318111528503243d24003d08520085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 512907284 1250 512906034 512906039
    0x3141902090117040c060221032701090614130309150912030c0501140f0402010309060f150e0907050d03080405070302120a030e04020f0a0309050a0b0f0f1f 69
    0x1850380007441c41c0c10040c14001045284407004603003401003110b0940b0b40c1400c0c11000d024042c0c2c144040307a142c1e1490f00d0580e2000002d9118a1600d210192545405605030300c80301c5281440c00031000c0301020040700800800d541400c261001c4d25118120740702c0030282c1c900242c102d10b1840c01c0b40400d00d805507141c1d214142081c0040f1a00140c6101101c1445100f4600040e1130f03006d6042030380d6080c0310b81e50b411403448440c0b910f0f0b400d543c400d600c45010103203130380100088002c41c40a540c5c2e0060f024600441c2001450410800500c1c20321241d01d100350411408c030000c52010880203048680043d10b140480da98042190744583c4607005481d131080c174060300680420b1041c440b10750440c0c054001d4031559650790303001901401d0044041580c40c0c00c6000803006140d000106040c0210003650154984001e4201038507580c0b1a8849510034141d44444010601000b040807003145a4031400c946000e050910424150070b200b00c0c0d882d407407901c0c4280090b40c448031101c1415004220109444034450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 512908534 1250 512907284 512907331
    0x22060f06020312130f0f11100e1009031b210b0c0c010f020724090809040e162409030b0f090c090a020c190203070608091614010314 58
    0x7030054150204d240f03000c19000041042c41d8603140b001441031544101e44d5506103801217a1141c000d403001d12680c01101411005e6800c0702200e412600110b8a1400e0021021821b40e0341d4104c0b0380002d0501051202118038101070312a11000340d48030850350107021082d5594420750302c840413200506964060011038040c41c40300c400f03000d00001c040004940010b504455000720307005904191180e40007001240c9a140000b40c140d000c402a00c20244199070194441c03450fa44034007000d15000e66626812480e08520070b200c60b0b2850b042c0c3c80313000750320385170340f1031450f181013400598000c9204080281c94011030701910038a82100e40c440f032000101e07590345010483d0030100400f803400038082c00285680c0f541d1461002846140b0a100050302c861841c0301c0240f620040152401035003060030064800360360005140310031200e40b4540004103541e0790b03034003070306101445800c580c03891010b0401250450190020039505130080c1e070304011401008500508030070041d42e1258802440d50544000c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 512909784 1250 512908534 512908567
    0x1b1621080904020f1e1b032713050408030108010e1906020a0507050d091403070b09040f0605030f010911040b100305060f130b041802010203190e22060f060203 70
    0x4000300030070f428091024801728140c01c0030381000f21245e03070000381c0b071101d02000ca407806100d040940080d030030000b0880c8650008010040855040c41c6000480c55031991003c01880c1c03486140c0c4410700040c01c051403d4401d82c1c00130701969005500308100e03402030510025542021b50074041c07014102c1180e03501d51000035440800203c0c02c1000c00c100d00404210100015030300c0480c00e60722031010615240158007031070040c03518941310341c01402c4d0400c0440c1115094032642101241c00044414220302c880004240d01c1c1c0c481782d014002c005452500c40b00641c0511032141c020030701c058002010204010441d0040c0340b65a0303004018410a0007000c2c4281e106580c8a800036114000341f80781c0d5000200013020502081d14501d8072441010314608180c0540410b02000e903581028026190340041d4413401001480f114507449004803464052090181c02d60410028180815030341100c020003100c91004000821450704141c000218111030b1220708040342d509902031030802500324490140e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 512911034 1250 512909784 512909797
    0x150227060c0a0f0201120c20160b0c0109050d170708070507060f140c180d0c2702070c26071401120c020307020306010b16081b162108090402 62
    0x4100b207886040200d01b580c0c1c483d540c07010217a80c0f1050408440c402c0e61000c05489a80c0d10307007064000c0c82c1a107001c8403015403c070042c0c400201c291034032624540103241c01018030f0035002e08280301d20003010ba9400c0c2c1045c0300100c2c0600304210f41305680d6909400762005201503500c070303002427000c0104102068499000f40c020250038000030484a41c4007a0740e40304580d0640d00b400e052040000d840c200000092030800b5020801d650002100390306480c0c0303280301c1400f48031325207844100d0408005111403903035081c002d40d246081c00715210401c41c01d08035144180742c0600c140c1c1400e0100741c0c01101034503245030b0301044041d00040c52480d00b8007040100800c000080141444030300c911b102035007042409070604080c0326a00568031101140101032030301606a005030b8009070704003c2241803080798001281c00c560030450055850b45400c2041c1141d41d01205504118010642924843c080029003e02103d40c600101c01c8202c40c141003002c1e4a20342c0c0c035802002040204203119007420305e41c01410701d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 512912284 1250 512911034 512911037
    0x80c030130060c0e0102160b0403080f07050706030b041a0907030c0215040506161d150702060d0c03050601030209030c240301060203131403031204150227060c0a0f0201 74
    0x4060009645000545180030107460114049070107040071946e040288001c000070880108030198902550130140d880380e0300015001000018000c484001604100e404881e8041c0407250003036625030b001801000c142d14101d21407801c0c80d9981c1030030402008840c186900c0280381c1d180f00d0b11051800d40c02030100380406015030041424074030522900c240034622860080001e4002494a9040300006103035600f404800c0c420b907540200c40c0c2d0034004201980041d030903100e01d6401c1030358030114040c2d0300803200000d504c900005402e075001501900b00943c0303600c003901d00b84529110b180c0190140e00071030040b9601a4060484403e90b441c100b0038625540d6034100d4600e12103e010382560701c00754402d07008500503a000190040d424008000c1c0e038001041344200384c1781c01118040000791244681e0300414440002c00c0b0208082c0f21500600e43d0b1101e030707950400c5503134000c010401c501030300c0700981c50000e0182096002900c1d0601c1c1084503800c13455100680200e03203281e0340300b910b4240d03010820390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 512913534 1250 512912284 512912369
    0x2100c0521030402030106080115090504031b03020a05011413060906020f13080708031207211506120b0306040b1b0403061a101b08090a060f080c0301 66
    0x2001904007445288503204848885680d0349414014182911940e5014400b168501148005d40001228400c400e0301d40c0000049002d03180d604040b982410b451940007a88080c44c4d130f5003070070150006071b40c00d40c4503c2070000784072848081061290360001118051380c881011070140c0c0002d02d1903400040702500c03a8000604104040b01000d000303800c0740c444d01c07012802c00c280070300441d6801c03c5400010064400114603105c20010254040c200c0a40200c05010390b01182e1aa0510308104d4151800c0d64a5010088c00c44000c6117030b614002e041c810400402d08150b171143c298802c60144200800020300181695191950380e541145002003a41810080000d00d884920040000400c001c50043c00046042100404802003d55514803000d00c100c45041d040c03002560881c90044640b580323044080d900310740b1414034248601c1240c10b03c642c090200c6001060b082e401511400b4081a190b46e840d499560b00d90442c60076201c00c3c040c0d00b1410b81c00b0001030300520001800000c60150210301c54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 512914784 1250 512913534 512913553
    0x71403010f090605180718020a0c14100c020c0307060804020114030103060501060306080303070f03052a0301080d0f0c060b06360a0302210f0d0216090902100c05 71
    0x4100c6102d0041240e955803288184030035145d0102c150a2030f070603100040c00b01d02c0e1030210030840245030140001c040a0300800c401803107038000c48402041030780054490881401c1401807a071642840d20540360036038603191521910500c0060001c2503090094028240c1a040c00c84c00d55441d44000c0040f410050b980c1c44042010700c201c0e0203503001b540304110110303095050480c098141c90464102041e10b500c02d10400c03107200e0f03101d014043c1551640c2000030303040c3c540307181829282411400d885480304107410076400b80d101e24030065049401d0b10059503a201c400c1e241c21184a01d25030240f80006007a5010f880200e80d036903100d4229010018600d0b1f2420303500045520f201d41c180c4500b8250344210a002042a610006c84101c5402e000c0350700750225821540090100340c1115002081c403030050004012020301007208100d0880ea010803907002039600c0c0002540c0d000c5040e000520107910305400039072000309000322400d455005103081d8035a6070000c0111540d8062580a450600c601c202d43d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 512916034 1250 512914784 512914811
    0x6020c01021e0c0111090d02090402040b0d08070c0e090a30050306030705040219110c031912020604081b0106050a090207020a08060c090d0f020306190e0f07140301 72
    0x48100d1000094840c540f140000700c442401c40e007500c11500c10112040091004580d2820f00d0115101d504560088483d1114000704004041c00d003d2a80c00441c0c000c0c80c074051181c2c03a00a00b2070310b446008081000d07920380800381c0321a0025034146903d9030142501000099034100c52610707260540c0309180180316441c0b81c24068054000000011802c00414040c85050501085010b030500b9a401e61401d0210191050716822030b003034a0040107011815150201c800f44000d010080c0f004048400104280d0743c64083d4174003122048440c20008491158454004101244100c0c0c1000416040c109110040544d40c00c48034690314003550703030f42d0020a49644035130048010340501d500068441006206101e0390701101d40044140b540300c40100324981b2266400c8640d0080143d03411051200039140201818040e684001c0d41401400100824056109020140340c0321850007807026024140441c0e0715000a600f07000b0081e00540c0e001e0000c0b101c141a8080381c00350140000480300b0b810365a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 512917284 1250 512916034 512916067
    0x80c0703021f050702010e0127060605040911010809010e0606010c110901032103020403080301060c0c1802180117072007140111120a1b060207050f10090302070306020c0102 76
    0x1c4500303d40d01e0040c003000315030907c214010a400036000300030380f90100880101c00500c901601c9181240c0e811182d04101007a0400002424080e2042c401d102c043d241009011105402d024002088540000c85090050003141881c82141300500003540760240111200c400c1b264043d980d00150303100f004101c0c3c8907200054001d5005030135000405a04d0081c00003080c42c4110707004205401803000388042510101143c2c110f403100e041001c0a841945030403e03400403180e2000303174110400340000c1c0c065040c0750020407060440124083c0e05041c00001554141000240c0a41203445c074800207038258001c40881d1580c0100900b20340c803440c0706112140c50078002c0e410828002e00c0c1210540c4c65940c100d5642c1610800d003030068040196565035a201c80d001c0c0408000c03c000c464034201c80725102110b0316107a03181e00040c2c19940c4600d01d0900300e0f90b9403110305841d0140e225102602d00011064404d01051036410f0b17011b00f084d140340d5281d10f070284d004000349001d81c3d54200580e4041c81030201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 512918534 1250 512917284 512917333
    0xc1603200601061b020a0905070905030a12030b04110702010e12010905160501090602030a0e0105070c080604021201020f04090506032401240903060c110709021806040501080c070302 80
    0x24141d941c140a4010f1000004400c4601c01540102801c1d0059440b1030030310040d9210000002401d961b0703004102e8200c01c840c5c9c00280c05000b600d00420600104c5000c5503132104003910148881481c071070a110071101e01c00c014954190341030101c000150b114844c90b1645c82e8008041c080780e103120303448203421a60211811070720350340020b85000700201c20804400003800c003428070415103403a00002035124410011100c04000208101c81c1440e030043c010b40340443d8020040e05c003041d0729501119503d040030345081e4803c1980c400c42220146050003150103c81085582c4c5081514003040f8070003a160180807998107001e070305112448813211280440d0491060200350566515209269517540400c049444c0525400c110200e07506410909510450740d0005000889801b83c0c40102d0b0f4401903003140c035115000713101000480e20034580185c01c04c0c807502d040550000c0429010084244030720321540b070200d00e100340041c4148000c840900501070090042c0c40d5240013183c1c900c0122170008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 512919784 1250 512918534 512918597
    0x41a0601140c070e01090513031803150b0103051b0f18031903080a0b0117040303021c0b0a09060305070e09070806090a0c050301050601022d0303010f06030c05030c1603 74
    0x3c2402c10042e02210b00c01401444e05040c10881e5040a80701d018040440c01400703410300c1b05d0040495070038681038100c00d00550704442e0785010b1030400680314000c0c0c86074919060000f0f080501146101d501140b41809100003880720b60b1804201c0140182c590300500c014010950003071319041c48946050003000c0c0b4003160810030300026800c41c0340c0503141000c0900032038841403402d0101c40300340e60011854048681c06005c00c01e8590f4070792070100c0291041c00d0800e01d100480d00380f03039890015a6045100c0c5683c0440c0c00c080000d0700d504550003118a0744c030014029a1040d1002c0244580350440c0a800000c180155440139848081242c03404509480561ba517501c016400f5085c08051116400070302822002442242001e0300000d50343e2102011980e552160701030360160902c102c124214030404040c043c0d03500c075030b510402e40903100342c680710310f002107410a61200386c2d5070311036411a4450401da02440d81040d810004a03151404030381421814880b0340d203117042000004690410002184 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 512921034 1250 512919784 512919793
    0x603050106090c1106040609061b08100b1c021312050a0215180103050601020c0d051c0207060819020706090b370e070308161109041a0601140c 63
    0x410740070720100c8103402242e0f8100202101d108080c5640455459000ba81210000c92143c0d1141440e9000740f14240e030700300140c511480600031054102517000d11641050584081d03080c0e0742d016491300b52280c5011100945050407416a01c15000c0d405400c0c40b029034040d09994036190204038410000e4000140c8060b40110302d544118a4141d4108201b400b203101c070941044400910400d000b0810803d85041c9616080050781591081144103040030000388010382425070b5051403619112607024100004800000b4000d200780001800b5007200c3c0d4030b0341c8200c0e056440d030090401e51140e20039914002a0200801c4002ca41071f40a020b03145805050b80449038280300c0c60b40d044041c9203d5041d003100188004080490800400e009903540e14054081440122040d0cc5814003415410040034041c01240c54040e2020061210156902c50100c80740404c030751508102c01d81004580050007018000007030354141c2040c0842c0d9400081c103040c051442c44200e803004809820010080703c0581c071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512922284 1250 512921034 512921039
    0x41e0602060601020d140405090124020c0109030201030b0d0b0c0c15040f1e050607051b070302060405040b060d09030e031b09242214041a070203041d010609450603050106 75
    0x4034003005014152f900052070902400c0001130603021440c07002074145660703118150040e480349a0a0780c80b03694010742140dc80e28002d41c07aa82250030051a84515204000000c40481c0416a009000300d40114011060900c21796440b484407844038500c90071894140c03803c10000e40c080090078028081030300e0b416124095041c488100c002c0440310801c0641c042001080075850f0071007154242c40058a01083c129102c901180c128860040c44082c0985450900ca06040d4031480e4400040800c4059441c07110010140450b802550400c06610a54100200d00102412600107050360080511210344090000c0000c0c3d085105004010315078000c0c0f15507030300c100d01078070480c00d0490887e07a00407520304082d00c4401462803020582a11081d803400800d58080c000c2058600512b00f13400b00301003e04100016076400034081c460003010a0000c0404240c030b101d0321600b5980384030150310418440000804020034807000c00b44520102c4142a007817031201c5114001c240240d400b403030002c2080b07407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 512923534 1250 512922284 512922329
    0xa0b301501021c030218090c090906090403020c090709050414060103050a180809010c02030304180c030b03250503030c01060315020f1c0f02041e0602060601020d1404050901 76
    0x1401240d1141107412444003000c40701550090700e440301031a4030f00181c5408103605c0c84140307407103c0d5001c07692025120040181c61018100105072801d4103451080341516003109002030401c0a07240240542c01420143c0450308052404980c041031514110854039502c20100c5e04407042c0340c202c00c41620031041044080d50b0035001d025009200c08000b0491403104502e001c030040401080240849800986645503a11400c0c2255032160000d054a59490365695040e40c052001500c0c2216181880241d00d2024000d12500e61880c102401a11354480204002d01d1804660500c048103544010404616500d0070009805081118800002d106003542007030000c01190009140000e4010450721031300c614000701f80c900d480940c1900d58414191802040c000d0044160f14400e220f00c00304000440e010b00081200b02445031a2200b010303a034a50404070303100c800c00c4440d140560f0003642d8070040036118812007421000c034040d000341005e480e040020007a0000381d0114200400102120143c030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 512924784 1250 512923534 512923561
    0x207060c1104022a06090d181a0309010e070e070c0f050613020102060a0504170a05091309140723030c04090303020702100807080a0b03100c030f18020a0b30 69
    0x40c640009000030700d0b00305400e03995441d400042d00100000400d80235488840c121510f005800300020741180b007003c06400c50416002158a00915800c1c0b0b2004580c2e202d0200d0302d203065502c0080701040c642c0c0c448000f5149914a1702045174000079011100c00072032024080d00d80030788202d202c203401406031400024502400507003400040f038903080a10000441040c0c43e20180040a40907546421550009503914080d01024541200000741c200303510200c154014080544103c865000151048200540e140f0050044055032662070b1100c1215101c09280030344c00b1000101190b04c12640b95003c0317015502d040404801090700426028210710f00b115101c2c14014451400310740d980780040d0010015800503290101c02a51070003002c5e002e407014483d5004071740c501e14091050462920b40100140080810401c071140303807065109003101030140c5450541c1d0014080f0003810f04002c6100026800340c3c0001200c414001910600580011042c52030040b00c040e20301c0103032908c0c21000307042c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 512926034 1250 512924784 512924857
    0x1b01030605062107020a0f0c030605070201021e0d0906140f09030a0c02010c020a030516031407030206071b12060606091410110c031006080c040c0207060c110402 71
    0x5208240190401c5189100c1d512a10120780f000520503030b15494001c2c3d041410864014100d058040e030403105002084e4000021248512010403040da98000224200d0140390611504d480c2000804401510030801030403d40140c09400a41a605580c0d070b50200c1d58030701c02070621009618100951a4490040c0c150300040c00c030051407604080780c40043c541e801a09000313041c4001c08626205544404280102555104044800c01c0b50654681111142984801c8039040a444171090b0503600121300c00f0704490340602114208850f076514020302084408580038042145440003400c2a002c401d41081e541c09114009001418038030001c0002d10b90380c200c0316290500c40280800d07911121801c2407500a540ba040081440c0c800d9803a042140c2d402440354036104d901301d22202d00806901c84401c4801003400c40d02c1410750350b418070003668204100c25004da0815001000b989008140744401c007441200c20912119200b4001130890300400000e0000da0412403242c818038820442a804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 512927284 1250 512926034 512926039
    0x306080c0a0e042604030605040507080708030f22120501050105190e06041b0905091e01150201091a0702010b150301050607080706240f080d0f111b01030605 69
    0x900c24201148003202d110003410081110f44d0002c02d03840c43c2103100c00140300e200c280c100482c0d9200d60301d080c001c0142c04150303400d50b01c90003501c10000c0c8e00d20300095800201d40030f00014508104940f2017103103080d0050448000050400c58003801c40811814103070014241d000c00e85441000203082250868805801070741c0034650070031201c0340481480c00e06a04807164101081290707902c0700c02140150550890300c9407980780c4228040d14450300300a0720800c2c3c2c2d0050724403050702e60300e40c002414030b80c20403c0928002c0f0741d200c0c014484c0c1150b00c401c105402c942400080707040c1e1030340d40c1c80c840000400031300921001900c205110300caa07420b00520341402003c5904907024001c1c0158030340b09100c1880350a10452001450f201004440e20a5074402a0000da0421804900510010dc001841800c4000c00ea004490115407034914010000560701c1440003003030101003c001c2074522030031500354601400054081c01050040c200f0070001151040c002610301840110005001e450303164000a1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 512928534 1250 512927284 512927299
    0x4030b091606050a05041208090405040602030a0f05060d0303151205061e07141602060f04060801080d1d06091009090c021b060f070c0803041e031a09070b0a0306080c 73
    0x240c4c0b10307802000d0341d040d00c202034190703c5c2c03082541c64250720034841d29143d280c0040c01c00e41000280b003029400365200d90282c160902082e820b014940044030382c1242c81580c8614546029800319100ba4042001e00e1410701107081425180c84a000180d0040e940407030b2aa4091020030065007110300713141c4081c02d00340d81c403106141007041d0f026140904a540b4024000d4010681003260480b2080e80c003c055005080d069403980d40c0c00d50390b074440d030203402540041500ca00000a00090005090814004507941e02d074060007541c50700041010081486588040140805861503460030401151140c1d15100c9240040c0350200042c203a6443c54544415908418040d40c0e0f500b0084001c5091800308480c00c654428001001c0e80d400e003d0041c01420202c0c081c02c010030400c4000004206481c1ca801100d1001e80d503800c80c4600044081c00020403041c0140c040c2c03a049280c050285400038080780c10388032903e840f00403003e22a000300e040400001c1c0c55000401040b5018042424004c0301542d420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 512929784 1250 512928534 512928547
    0x60a05090603250b04030c08071415070510020d0207021806010f030b0a0906060203070c140f0d05151515070503041208040306020403032c13090201030204030b09160605 74
    0x10782c603603241006000d9610402c0701802c01c90400503c10f01e000d001c001420765151034032030a19240d0385407503005890052188040100b440e000b04c980c40c12200500030600c5250100301500b000c016084030004980c039118110081c6841070a40c00a03040c0c804c4034010040c0c403641540108000501480d41101c084120841400b90b00d903030155140380006420708000c5120f00031440031a8001a49034482c0d01c88030325040000c140320707034040010003016020741c04041074240c40381c001c00190f608405800f0f60003010003500c00490b0502c0c09070110701d18000c44c00e4036084000c400d042c0302d0500084407032244a09403090b55942500d0000031b80401d5100c0c90400e541042642d5480310740e02c0c8524062107159140200710082000b007100b0884029680c4100155203c903664903024001100040c5540400000d54082070390004007100122040c181c0104000c0d00d054290030100000c094440090303040507001c000100c0481c001076070f42c50290440c1c1004041c060740301c460360700d01c0c05156000482000400c00c0003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 512931034 1250 512929784 512929789
    0x301140f060d05070b0a0305040c080304050a0509090a140c010f020c09010603090f080a0816050c0601150c0f0b0612070e04032d030b0307060c030c0f0f0b0f060a050906 74
    0x106501481c140c41c00e50400314942407003407611300b41d507000195030800000e80703c1309954107070010790065101e0f05c221468941c82d0b198180d2a80030b130b40140c0e80c204000d010100710610f051450303990480c0303a9078280c4c0c1500040b5241d00c020000028008803182d03000c1441000d107035030f2115118040501c1d610107000b00c500e108001134003507807041c40f4100c20140c44042e01010310801c11031500007191300c07850f81640d40850704806010110704a941907180003d858501d02054000c8048500080c40000a410660b0812602d4000300da17a000c448003c02c0b03421005500080e80300300c0a0700101d801842c03480001e1070254100300c01150500c11206190300102010025080742903005900160b050800d075140000c5100040d00d241c44007030981200b4010b24500200251b0035600c03440101c4003c0d8192081c254032110151141d80c94000b0040014558654000100b0165980c61403004c1c8280c3c1001c081e61003603140c40000040944100300c000e00308009114a42c41c18010000081205482d400310a180c440700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 512932284 1250 512931034 512931061
    0x4020a0504030602030901061d040b06010512181c030e0c010c05070608250804021008100603021806040b0319060f120f020a060203040612060806061905040f0b030114 73
    0xb000701003a07008404100300d40000c0d007220024007403040001c2d2044000c4131941c20568070949054801c1c6500c200800d4580d4803810807a5054440140340000c141c861b4629004000090490200e4030300480340a10b0000556011894001c1060340d0003103402040340c0c4d011820822159121814802a80812800154081004400c903a03581c00d0102090b0f80c3c21440f080314840003c1a14680281301c50790008850300460f1b0507000354001c1d02d01c0300c00811460025662003070240c407401140c0d01e607080204080d92103600107004800d0680350402504220a0100305e00b6003003034003d484010303800b0040050341c2a20150f42000c2c030150320b1041c02518541201c400400145014401d009140500114140702d100411018000d03800782440d2001070381ca041c000d45076001400b44000050720490030300740c0c0502d640103600649a400c0c001c0c001c180c07518403c1025001c40c05040710101041c8403c001480da89034458802c040c1c540950104598980d4010542180c20306491010700901c0c07002446101c0c0710118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 512933534 1250 512932284 512932289
    0x27030a0c0e070306030827180a09050705030a0b0108060a02090d03050d1e1a09041101210c0f0906020a0506010302120c030102030c0703030b2e031e091104020a0504 72
    0x705031260712410001c4025019540002d030003e600040e1101d6034429988458030101e035a1403191a60f10301c08010030a0190002c50980c5041704101e010500103119030380000c2c0c00500c14401c40c0d00e46507403100840c2c02c04000710ba00380c0d0598103c0c0010070480b107041c0640c4ae4003a6050f8800c51070701d002100000d841c0100c1c1d05d03000c1c0410201140a4818542d217602154032146007600804c0f003103400c10b00d007901618100702d0b01000b00756112064a25410304100c0140582d91000200c01600041d10045810103500ca11050301000010880c1070560f000e4030031410754681660310a2050f80200c0009009500c45902c103204640c0005041e03008254045074142c192a41103c03148210721040070480d2070034200c80b074080c0e41940300009004500e2603480042c01490b120b5107080c001201e01000f001111040c60801c95144003001900e0198901c0a071a1603c250202e0300b00001c2184802c16080811548690300420700c2e5a0b441560052052160510003880c0b0120b40a40c60404d0a43c401403560050780f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 512934784 1250 512933534 512933549
    0x50f09040309060f11100507021b1507061b03060e01121a06010203041707030c150503040308270f1006290c1518010504030503041b030827030a0c 64
    0x10350b460031308584918150f2601c4200b0b541250320300058603040b40002c03d0251007280c09803182070b4a03040f0880c0c18003e02510400c0c003c0c043c0c10400c007640d1380300b1840c0e800742208480f003036950380440240c1442c06800e0741812040380d500040319420302514007100041a0001943c1c0c1d44520106000a2100cd2040030140c070b41d42180403040d25164011b03491805160402030b503d210781e07002c02110107000140c0c0000c80340600b0b1000a1190360b4118415440f040c803540c1c10001d101000090081f0b40100d50154000042410b18030320060200c0b45101c407000524283d1b00705030003140720005061000c200382418040f00036020008203142007540c00c00d101e40c50503410440043c01040c01c00300540c85041d1015003400c5000d84450001804c200070311400d0480e542600515050400018a01c1c14420b40713100d04d83c1901c1c0c2c28555116501e45550810304490715861165100c580803000a94181c0600809150441c880e801d02804201042c000120720000e503000340e00c80207041c0b01088141000404840702e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 512936034 1250 512934784 512934797
    0x206090111151f0504020a0912081207030b011106091c050f0406081e0c0a0e0f1002030a03060621110f03090d0e1e12010e0115050f0904030906 63
    0x440154108054400401a0030b48a802040300c110350702c0a40010215141074100c01c119100c0742080308074015848000002100c0040074068107420410401d03c203400343c81503e003845079202c0300aa40580840b01800040e4442d0000c00541d40c0001d070061600c00404082c0100b407500d5515940d448020b9868031401410b4484002106400b40e41141c41210998600c0740c1d40e10784405024101603c01d41c4c594140d0318000c0c40194400b003200c881a0701404c4004049403038400d00b0041254103202071440181e024070402c230424100d80d41d000c010400c4000b141c0146450b140150009000c03110300d03031b000c08144504441000c503000840071301646451055540003964003900900301c00d1900905270980c2d030900b800810721a0800000486a500181c141e43e03003002e0954041c1030010042c00b4020800c01e2082e5200208120f02d0a080d03c2e40c118001e010001030020142a140c0b4203440d0b0107041903a5000c2c030a0000d03c0142405241c48103000c0040c0c401e0700303075411320350340c018111031007445148108541d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 512937284 1250 512936034 512936057
    0x603140f04050615131404030e0a031106070311010207030e010e030109030822020d08090405010f1214030c0a060f0c0306080d18030209010b030f06010905010c021e09040b040b0c030402060901 84
    0x440280c0b401a690b448178041002c3c0780302d403400c24030084040c1c4080d0046824018a0203403031a121221809690740109114400742c800402e00100d0b8204820032418085c1f0f2990303a0800707010034400b030901c05000b0790314411448030110000d009203100100090299051139190b0700440e4001b42ca40b904001d4003e50305801c00d02040030010711842112009511207800c18001090000c801d000c0c081c01c0310b08030b03420040c5076a2040c041c0c680d148988105041307510000026808500203205828100b0920415030f860302c404401382c10f0034050b2282c2c00701c1c0c09603592203441c1070115043c42144961800c90408102c814200900656660106549803081003e0101e02d910031300500040f00000b96805480200d00b561201128002500104c400e82410315914000500035071284420004490040c0c4400943d6645502804401805040191851040c28400c0507464490324011449140500c0e601010f9041500e440900c5c48409082c4081300c1c807050080c40090781e00c00c41110020042400d14030054403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 512938534 1250 512937284 512937289
    0x4c05070b0a0209030f06010905070801060903110a080607091802040506040b1e0f09030105100e0a0e01140c1b07030201080a05060111120c0c0603090a060b0a0308040603140f04050615 80
    0x4569070f00c20f81c040c052042c580007040350014a40d8107170769060009002e5961401d10441d2510000d111b05000500824010030115990058015818101030020300b10b50783c440580038581041610010009500c051b41001420080d01e00e03607104803a01403042d440d0a1801e000103150340a2801480d64403240001d45080c4070115a0741030341100035502c0c5807502c8014001c3c3c204525004400c0c654080d50802000441118500714a04151445200247c4150f01ca01c4079040041c42069031403403913076584440182c108151500741502c41c2880c120a25500c3c2081484041d1b05031085c4460043ca5015010030710061780c001d80b0cc264070011182002030a0f55035100100c5035503003032242039002400b46000c1041c01281280050424640d0300c41100e40c86040b00c0c007840080c0c40704640c8008550130a9030800009a01c6e13410007144c10200502560582d41c498503040c900e42c1c082d500440100c2d550701d0040d5440701901c80410f07400301d6400e0401b1140c2c17038183c844039240c00d40107101d000c0721421200c510a155 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 512939784 1250 512938534 512938537
    0x30b03030c0105090a112707020a0c0305030406230f0a0504030218010806070e090612070b0a030207051204060215040516030803062803060b4c05070b0a02 68
    0x10703060000034400c40c14078040346600c0751038140c0c055a00030807400400d4801d06140100090300012002c440c02c5600da800c00c07028040070090482030460241443d983d01240340460040b01460044015650341c0317182800103000307140c248001c5011401c088524640f10900d000595400100c5800741c1952040800f0045450744920341009500c10500780503808541000b0301c000d4161130b800c0c001c031540c54170780392030a03201d54540411031a030000381480000c021b030912810283d41212144112600d09444100201c2d030fa8112200c0c3c1c0c400207901040d100c3c148082040b40810300601d80b01c07024a040e0400500a4803104001c4480182542c1c95002c1010004100700f0038034240c2c0030708821401c05489117071002d52a4016200b49220300043c81c041e8041c100000c05416003500c0d1040320288803803459036040060310b03c007a070055200c0c6401c020780f00d0002005101d0390803c00454044004c6140b01d0340c0561001c005011014652059400d03d80c2c94246c02c44201d5406a400010481442d964030b1491b4019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 512941034 1250 512939784 512939797
    0x409050a0605211006150306140a05060702150a080a180c09091104110a030b06090108010e07121a031902090703020d0b130504031205060a050628180f080c01030b0303 73
    0x517140c070800158003004010110b80011040d0380a1021503a81c030940b200e05c0003031205440c0d0144419508000b545042d0008150891028040880350355031003100301c02e41e80107244490003107003428040050041e6a0320801d502a03441c111105d25030f10603911481041000b030f0007840160b680d50385590051084405c540410307000018020301a00c0b003100d121120680000c80c0c1c10300031900703050345929185450000d40e0a641810394031500c7c04d80c64000300b00c07138071000079000c0424460804400c404600707036809122440c1c004521114001001807081c1840c1400c0b089014400300d080024210041c0d0314100f180e900b0101d54500135071194000c0c00100e0007800800da206034003000040c0155142d654039000305100340c0c0241c440c4000c0401c0c0315404401d40e60304a80700c0742d200d8000c3c4424070080c58040090300210030007003410310301d0120006644210060303081580c408100480e200000c400304ea80300c040c2c05080c0358501d403d040c40c071741104607580b034a0000c0400c0c1455141c0d41c0514094070200281e0341c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 512942284 1250 512941034 512941063
    0x30d050103050d02070f121e0828030c14210115020c03030a0203040504110412061d030a0e0f010c0c090b09060406030302060403030b0a0803040b0409050a060521 71
    0x400c0d40e40340342c02955082008421009401075401c0007800318903080c0ca242c200c401402d01c00b1852201a80c69800c90030a0741e00310000381242c40b600c2e40c049502c81026220056004800030321a00c1003400802c0e180c0a19800b0f002003509010719100e017958840c6642c040410342000c09915036403150380040440c03460341e1103507051a66940001440d42c60801a03540e010446409952510850905054032072243c81d0b20100542e00c108820002d40c102036110001c2c11400245150400b5166003048409905914081d1055a2100351804104101d4480340c5102c045400055281c034242c06000340207940124602441132803064090205a4058842d0024403a0710408510302d594a85000301c0080c005075107020301502440001460506042c89000c042c0c980640003840780743e43d0303a90103d01030061240b0303154002c1001d000010b040316080014002420314901000e44036800c01c104601101d80040039044400e04051041042d526105c0c1d18a80c03480903c1c200a144003c40c2442918040340000000c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 512943534 1250 512942284 512942291
    0x7060e0f0f0123060306010303180e070201091209121401020904230603030301063606020718020906090618190e091b060d150909140f060f09030d 64
    0x140352010761003040040511070f0440074103560451101c00c60300f000c90b0400c0e010b07403002005001090050700442c3e18040720355020040355490301403051040070300392014000b61f91180007502c1000050240001070810074601402181c1c81d0516880c210180131001800865803640c2c1d003d140740d001e4040301c82c2d45401410902a6040b00100e140042c03409402480104418002003101c615001c000c680c120b52160759044100f43c0c42064254171008a07445186445c2e58030320700000280e2150358a00c000744400e801404982e8030700f42d64248038071122520a0016481004511499a030341d00545041c0c00342518500c0e00c40040110110080681c001c0c5564000d4810000c401280c400806200030741e510300c029500710351203403120701c1c0d61000a413150107a41c81d0480c45034815828001d0107049038042d6a60b012400e60000d108020780b800e210340080d00303003a844415140a10130341114204010140d0001400d801102d14412034840d2000303000c030302c1c1d82c003207901c041500300c07508000b13550980b50440002c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 512944784 1250 512943534 512943553
    0x90309150503040b01120803040b070e130203090717031b150a050403030c0512040209060105090a0308040609050a0f0501030f020d0509070317090919091403030105011206080307060e0f 81
    0x6407540d001100c0c201c6284010070000720b01d000d00c0c3c0c2400181ca517071003502181542c583d82d480303001520b030043c000420454413601c40a503a96404405050092141900507a6810800c0380320b03003419400c1e005a614110207050750189000000119042d10b2030003085041801440700c526410100890341390800c4940b10b006101c0c02002ca540401d0140f4425102001000c2080d40280c0c0c847c0140136040c94003008640004000d81030801d40c0791b5104c42c052408500d80704401d00040c8018100f41c1060351814000300c2e050101d5508941d284000e8181180c0c42d40b441445d2144018003031449004031030405407240c0000004c460290152640c10942e245c041c091440d0900e1150307074484c801d1009441c41200b0141721110380b00782000b01d42410f90050801e03400c03903941d0044601c10031050801c03204025540e5840e0000b24058100c0349650346620005582d99514050004100b0a030040102d044540f400701d0400c03828100200319617003203502540c04a82d596854180d1801c068007140694a01d00030014603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 512946034 1250 512944784 512944787
    0x61e0703090807050a051f0516050610080c0a17011107080a0f1b020f03101b080915010e040c0b0c030909090c060304023c09070305061309030915 64
    0x40e000d4510758803c5504140d5900c0410410080341c3c81000d41100c217801d42c5d24001103c030400701c21440c2060400c60314101c200d02d1003e500c40201c10090318260048070a0041d13418850034908000c08116000784001402c0c100091300c0340c901032082d280c0007004410030720111070080d04428640f0412a19607500c911160402030302d0790b0b0140701000000740303480120703420690254881c0c00c1c5600d00c550070401e5903032080d4240b06000000c1500c00d90f242c031408201a55070511806001c18550b44012034403e415000b91000d424144090300c1c141581e0414000d400712844009203a50442d0041c017a029800e848609000b0b26480640e040100b41502c00035000040c07030000001001c02c901c043e6560710350341c0d07146452076485182114045501003000c10101c0c000d403815081501d5450443e02982000620140c0100c8032841404990420240c0c05444240d891400183c8590700c082d160a0900c0f04d442c00c2c00000e480c0c007a0030281100e803035541e0b5485000f4184984000c20190001c1400c0100002c08610f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 512947284 1250 512946034 512946047
    0x70c1a011206050711030d02070203032503110d052703010c02010218060c100c05041215050f070c0b101d04060605011107120602070b070818010b03070302061e0703 72
    0x30107032501410400800c400e075200384a80d07000602c0c00300c044c50501c0007c0303c685010750700540c0143d9040c4410b110544030004040c00400d00420300c08901c0701c642c441490080e0403020742070030038025a0061840c1880c0660041e0446800a1400d60030f00b2040501083d40f0000d0f140ea80e400c82d03015841d104580295030380541c000c11500d080850700e1b4107902aa1741c1007010521805440d00300d140c1080c0d62149110100e0380001c42d5000042c1000342c03c10f500d070603000080b0140a0030645440300d010690080041a510076550031050480c0b69801b40e02e06040042c1440740c503004010410710145001034401a00400740340043c0c100040c0a103252625510f1000e001030055074103581941c51310000041030741c02142c444d0030038411030b4040e211440c9807446903900d01400c0a0180c440e540c0130403604000603103c50500e4818072564a84ea191070030701242d0501d00044032820400c03260702d04090203210365800a440001c83c1c0e4100c031200c0e5200e00444d1801c10482003010648407a20010600e00308040d00f119 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 512948534 1250 512947284 512947319
    0x309051b0306060d0203150a091712131a09031309060510030608070b0304060906050702100f050606070215070b04080403030f050306060d2004060c15050609070c1a01 73
    0x3402c07500c890f10b071801044900d555100c0000c0d45644110138500d010054a0100382d40b002d010785000401202e181c07540381508150046899035200e000401450340702c286440f42d90050110364800e0720208150352194482d8030319020f00c41c0d80c10302c2c40c40014583c1d031040045880d2040204520603080e0745c0c40075440302801c01c40c080c151040b40d10201400502e41301340b04034021145918002d1660b54a4088200040d80c0f01610580e80c1a450340f880c0310202c5c96600030f0f5409038010358010a15207100081c001c048465083c1442c400505003070602a503961200141c8620513011101d54100310a001c1c0c4900740d6201c4c400004007141010700130002400841c80c040c00403079009444603550040d00e444c0031a054441240d01591000050200d445806182d521901600d410303010366058030071110031403801740c0d08141e0000001502c130012000811121000c031036001015510180700c02d0910742d0000b024000010014010441c1002d1000c092041c001020035003258180c28212840d41c4a03529007107140e0300c52 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 512949640 1106 512948534 512948539
    0x12061903170910110c01090602280506042a15050306060c011a033007020303040e09010f050f100612060f0b0406020f07030b010e070309051b 62
    0x1042140f010030269200e58002c1d18541305902c0c41c1020f04481a410054541c9042060030340024000140d8144804418454191b030149100003401c810005000d034820b40041c0300a0242d001030208190245101751301e40c20101100354410b5404a104010b0340e01c02c01d80350100751074814400380d50840401001c0c1d074178104c1074114041c00e540220422148001c1d29035401c200d145400c100000344000804070000700e1515a1005000d40350800c1501c1a41d220300113004011950148100e50213880702488940140c00d00010b4a8024844d01c440c40f00558581004241d1006160050510402590814031465801c04034211030080d4580d602280c13403516503501007581500c40c21028040c20454043c540c50310318154000f0319010240c0060f03606500030003400d00c04103101e00b0825042d144e12002c030f20116100c01d00300700c1c01070003202c81c00b801c40d0044802700050744488284170901050708 = true := by decide +kernel

theorem cover : BRFrame.Cov 512769784 512949640 := by
  have h0 := BRFrame.cov_init 512769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 512769784 ≤ n) (h2 : n < 512949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
