-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5197
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:53.610186+00:00
-- url     : https://prove2.me/submissions/d66fbfc6-694b-4cc7-a1c5-fe7e45e2681c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 934532374 ≤ n < 934712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 934533624 1250 934532374 934532377
    0x71a0108010617070b0901031d062d090303130302070b031e010e060f1207030c03060608070b0a0c0b040614040f02040c0e06030a0c140309010204080115290408070605 73
    0x3d40d50120035200c080d911121440e150340700c81c8a9000e0a4108005c801c10543c400d501610008510109890308225210190392400d030040704c2c03d04030000601110052042100368a100b443c6641002c0c2e0080c1ca4980c60742e0340c80e400042e0030030101c0c40f034202013081054028441000500700803808a0340701c3c6410a80c1d44000c014441e04d400390002000000700e8040c404560f103510583e00034040f8140482d80402380080e01080c011040d030707d4020810007000041e8081c04400c0114000c0d040480ea031030401c0700180c1010055446440e591104000c4050305903042608010300329000303070b0b5828445c5e0f1142000c00141421b8020b1611845003903003040f0400c540c000105990702d0017550304010300100d0990079661054032034250703a4403010620004030706d6000c98205070107040c624039110054442001040390242c0050b41c0c007102d11f94001c00c061040803024130a114a40b0b51020888504034541001445a10b6400c1d2400070480080c05203030f810040704c0e1013140c0c000e000b90701c11640529603490000313046 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 934534874 1250 934533624 934533629
    0x7180506010f050c06071206090c030e0609070321020c060a120608061506070501020c0f06040501050f190f090c06030b0f0603090c120f01050f1f08030f071a01080106 73
    0x110340302d40900a81144550700755603220244800405140e01c400c0707800e4401d590406980301c00745845030404501040903020310043c000c9541c81c08229166400001410001c00828821071580182c0f01000030031300125100041000d440d0140c010301510040c104d0408070f80c00703005030304000d0010f09481c280342d11042c9020300c0350309043c0030000c030381c0c903811030640707561040c0c904203c40c1c160002c0922041c80c1100051114512a200051031710058000e17031424841801d1010300c803030300060304100c10f2120a000365940855142c404804500c0d020302c00181d40754420b03a0303040000703607100001c8440780c0e1a68440e80721b150f0440504200e4964a1078000d000d88064000300e030040c000c5011000113401c1c0001543d00034440180a06138840045090103030007654140000714600c1401d0004080040038401c40740035001c3c040c4241803500e06003420000c2002980c101c1c0e20780341d03801c4030100210040801510b40d03113200d801c00140d5644070750405050010040d9140411044404000501c0e071f80158088001c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 934536124 1250 934534874 934534877
    0x10b0d0b0414160315060501080a0c0309020414011707030b24120d1d0609010f021608070e1305061f05090c040801050c130302040921020a020108060609031e0718050601 74
    0x803150071245c4c0724040d00c0c62449558003042c0d6910100710108410380145019507224500010200c0706600042c2c20748030b40200904400300018018007900c524800002811500d440050031513515542d070756201e40c1c0740181f00c1540f00c20036901012409080c00c019a2000e04028003015554070840115600c0704e1088600e080850380320030251078200d005083d01000404004c02103400d1954940064414030720001e0068214000d0012099240140c1800311000d806900003c5c034034a81030402400d89458003500300b1108907048500740c00021380c0001d10592001100340390700560807111201c41500d00300c2e9003020744e018002d90100048c40f030f800e80c058011140c210000384540d468102400000d4414041a841c404826074014805410240c0207294034610400311745071554003502c455240130900351103000041c0c100c09043c1040d9030b4860b801c0c54020000300d440ca0320b01000000000d54034002e281019840c18003d03a40c0c540110310034801100200700d800032031602042000600c0e0010141210b8550 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 934537374 1250 934536124 934536143
    0x30110103050601090b0d2708130b0423130911030606011e0e1f0c020406060503060a0e0c090402041508090102030f011206060807090b12010b0d0b04141603 68
    0x2441c940c403511501040b60517400350145800341d000039910140c200702c401c190b02510040c0c5600f0b045207600c8040002079000b42a980d459011243c45140490303002d42c48004180c4003071105100000282562140c2d410f0a000c0e44414024000f02095040c2e00c04089034a8181c5000280014001c42c01c42c144102003044042d203d540c3c0d80e0100655092091400f2000000480d80c0306041c854040e111079022004000c00720f00140300d144444c0d24000f020284400c0004500e00740c40b20844c20a401100c019080c0303400d045046150140108070314800c90301c1900c3c0d901c040e550108800c80c245000b15007079010003034404c3d50303215200c0d00c58188803419600080c1c00102a03400203401010188241ea00403100981100e24a0740703044911640f0030302107507043d43e51954903407000801501c100802c3d40103044c102c4000c036800110300200301110781c0e0182c0c2c0d04450303410469560403d0361603210640c2d042e688980c200c1080c0c0c8580c00d008003221001d00650405c0e10444030460314019241da07060040b603102c1d20180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 934538624 1250 934537374 934537381
    0x3050c1503040311010605090a0c0e030607020316020609150c0706020f030d051504050405060727060f170406020301170a02090105101103040b09010e0114043011010305 74
    0x2028600944810040e0602403000c01c1c0000e1081c521008629403800000c40c40781e84440000b00d494000303550b00412aa81d55110780c15564104d0041402c80d170003180948a00e00e05080c0181d224440d44007201c440500041c00c1ca000c556880c0305a40051101800c0000000e811040c15401503001e11307415917080c0f0a9a40c0090245e10002e522000302e0306035409581003061510041000e0500505480ca100003804041042c907142e5100b200c1c8158001c10040925050003240540500044032181144007201581032402c40c201c0c00840d021078495203030281a02d0100c08040345c0e20000020102c0307109002406000920250750043c5050f0794045c3c1461000340440d10419a03500c0c5a4030700207400105080041103d8030300002846035000312420214076610034080d0860455000e03400410582d0804601c00360360b941e000341e8040d503e50302030a0440901181c031245841074011482491840910b00303103240525040349042c038180358140d0b83e02da00c2c040e01624110144c01441c0c22a030780000e1410000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 934539874 1250 934538624 934538629
    0x118081c2712030314070c0309050a0e0c13170c090105060903060a0b030309030109061406150414060f040905180d0f2604080304061a09060d0f02130603050c 69
    0x12004004000c062480a09140c5002e03107000c0602d60500b80c3c00c0c0740d51003c00902c06400e40710b006100e03210550711380c2d000c0d5410340b0700500201c0b0181c2110340141c941e003800b131044088100b8030715040300c4900806521201c6006281c0a1100c80c2c0d003194204d40b404100c0d03000d05e01c40c0015039150450040724000460303a204c1307061007a1030203082d0345c003a4507500040109052010542c403845550202400b035030f1400740c5200c0460309507665004210b5010f0354816044291030040041e10f60400d00440305901898824056040b183c0202d0090304959a4110703000109580d4103022a02c400c0300040c901d81d00d03030b991210314030010003084581c2000c0c002d1501a2014054010400240301543c0380ca03001c40e10b40700c807181100d51512400d1513040c05000d2246088034124000e0a01e4821841380ca0744a5503407800745080b10544107251042c0240b40d403201e0300c440f0750b0b54aa406c55940908107860082550244d410710030010040c0c0000603402c0819009001841d400c1900504241d034015421140114190b005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 934541124 1250 934539874 934539917
    0x10c050a0504090e161d0c18090916030b0603010f090302030a0e0a0b0d020417060103020a0b0a0210050f01090b010e0609040209061e030a0c03090309050118081c 71
    0xc0e03000080c010481485001d4a690080114030070700412910b5441461019000307810301a0072404072425000a041d0058030303114401544200b28028540c20008805103ca0108000010280c0700c1c038500c40008001101c10840445808031520b100e10700c155680c20100080c0d40203460450095090181130064201c0c0380c0030340c4040561641c0214a40020305900f12005080c0f0044568002c641c0407001034131001c04e00103810391528046005a0399440c1290485001075600710100c150b41202004001581d5a020108101d5008021540d55004506000ca040003920315004000c14034203010b0025040c1c1803280541a508011410020021060019198240001c6005034880d40c10803400d030281c1415005454071a901500c198101001c07007100b250121007047c0314000d442c0c804402c000c0c034008240240700201ca214102001814600e0f28001c0201005008280c180103507521813000c81c1c001400710302d0003800100b003501c940b00410b8451545034803101028000146101c030440180c07201215 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 934542374 1250 934541124 934541137
    0xf0904050615010504030203010f0b04150f150c0807120809030c07090f201e031509090717070504060e01060c030c0201030908031503120414041d070b0408010c05 71
    0x207024541da1011030301d011194551074141081418080040140c809001d81c040da035407904004a108114241030100b01d40320b1821103401c191034510108102440c1c41106420f8894008100c0102a10807000b6242103c40f10002420715100046850600c000c000d004c01c81103156964141580d1500c0b00040d560740034140c40d00981c0d407c50f1004202c00d41840e400b103c003050102502207507420f4403030203110300c004201d1000d0b44210b0002584202080110905070f006400060f0340605608001058182034110075401c03a000b11a0480481c03840030341001014020001e2100e89e2043c0465906502d0b15100a8400d0342c1c021400c1039804600c00c2c1e8030032040e90580d8030607540c2c44a050810780b01150012400c040907030500d6500d00b1124007180c03400d40214490b116120501d2a070441c0081494a0421408084104424140814410400311080841c680c0004540100d4100035144441e02420100480305d03929115400000075182e55142c080c004031000a0004c0003082d5012006403003620880 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 934543624 1250 934542374 934542383
    0x20609091947030d020607081f0b180301060906062613030c0b070c1a160c0501020903061e0108011109010c080c010c02010609060501020c090a09081909050f0904 71
    0x1c420400c000d880e4050b540340d49100101c0200d95a41c0c880b01083c20480c0405401d001604400c041100068000d0b9800b41c00c928401e04100c903100140c0b80b0418000c00a02618005a000043d00c0600c0d6001050b00619580d004008108141d904d0b03903000300400f030a00c500804900032038202c4601d01c60040c1a002c40304079107040442c5550b5400c001000104005404605010b034981c03000d004a01d5840c01140300d804262107500f11440d00c1d00344a03054008981421005c40b03c0801003050b0503e2038040310400c0ea12174141000040140c0c0b510901901810030480c0d054400e010400c080765500b2211406003048110400d1030320790300c42c2510742c261401032900c401d0b0b402007040080704951007414103001c4a4011000389003021100302c811800d41d16107168880041c0e440c0c10084c040740495101b0300c0000d0400b400108003070945200450040c0034000c1100d00d00d80d1762082031303105100b1180100c541000c049500c070400708000540141488201d40122400f03107000e0282c14066082685041c0c8c00b65801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 934544874 1250 934543624 934543691
    0x7080601180603150b031002120403090915090e0c13050f0f070c0f0218070e0907021501031b030c0308030f0a0902010503130311030f0309010f02071703040206090919 73
    0x1801c013000203044085862600b605c140300017090145503c0c80940529030144030710290506041c18001c001c8201c1d0380000207c075103016448004014900f06080c00c84050360400314203a01001d1303403641800c4012020744c1e000b03c945070240140c121103a0040d40b24251303d500f000096101c44214070507400c42200c20030041064013800382c0201d86140000c071240b602c0240000058502d0fa1a2900888003d9a54070085a03080c4d04818480c500118020707809401032005080450600001d05019501840060070301d0700401101c0004052940414000d1a04030250040041da203203404900b507401184d940300222107000203c1e191001d280a551400d40e0142e4a103819602d174500781c46508096403a00314103000790080310041e00f20043c0080e0915005004180d030b103d00d0100c0c0901d0964440710b6209000034030400c2440c0010b004a210002920a60080d880d140d5541c4d1022500380d218481b107295001c115101000450041c5080b1200c81441010050050000c0c40c503044171321008140031010300f20038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 934546124 1250 934544874 934544903
    0xa0c0c03021b0a050d21110d05030406020c0304081b0306010605070b090a020909010e0f0606150a2c031b0112020702180412020d0e150c0c0307080601180603 69
    0x489600342940340b0b00900c1d402036507075100700040d28180d52141c1120303485081d00101d100344486510108104901c1c0c10402c40300d0100060301e503110300b0030000d500288040400482d0602c42154140d81c1540c40d000d0403a40d559032521600d40c3d2b110100001f40101090a04083d055810b011541e141242d20030f40350740c0d0a100712035071a00d040b1400288143c0c0144a017284810140e5030b05141580151141000003c80c580a102c0450505c5007403159600310f948200d040c850543c8030041410b002d4003a400c1442d8a80101c4481280e001214441d810701c1c5d0b00309919065810025038900ea04001e004608a0382c092401d1504088401d1803404081d001c0703000612030540ca603a6540080076440c4c8014403825003807400c0300b91180001802c0d141581c0320003407020581403450b010004056150b030310341001821400200d0000d401410301112030508420302090300d02544000f0082000494001019113001c107481c0c0c5280c81d42ca401c24864044191700302c001d500c28140491291400b900c0c1c008580454418 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 934547374 1250 934546124 934546153
    0x50603060a061a0705010b030a0c091505030601210c0602030d0c0f08010b0a14180f010c150c0e03030318010f060303020c0409081c0203010306051b090f010207051302030a0c0c0302 79
    0x10131050080c2c0f455500c0b030540c200c1a035000c1c01500026403117602c039803056034103000c0301004840f4081c900d0011a80039076014021075030005030090460b43d0100700d82007103484005003910b14500a0500600c4506140c0000c500543c002c00a00851a00d2100402c440012408100c6e500c0c90303807803d00c0b4081906580180920220240208000000380c102210811454490b050f074582c8111400c0d80408030b00c08400341c00345092021064401c40910749a800401d050300d40b60440407200d4990868503a80740100f45d6800d0090300d00049010000302aa9100d01d800b071400c0801000c2803140740141c1d440d108403a4202c8981d882100240da40580c001d0004800c84400d22008049040040c0c0d00c800c000d106004c1228440701601e040803c50304c6015032294510b16145003501c0d005001c0b220360f5110680070007218202c003070a80d0b2801da01150144505a00e400040c1d09209a0b6040140c002c0b42307840d1140d8070465260003c42c052075500408100d4007842d00c1d021100f8000700d1000500603081444a02c1c11039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 934548624 1250 934547374 934547377
    0x209070923060c0d0e040605040504030906120f060909020a0905101e0801110d0e070b0f0d0908030a0b1509090711010f060e041203060b0301120609020d0303050603060a061a 76
    0x180d9020780003a18000d03452070081e182045003600303440081c0440044000e00c0c20140140001048d05407030034040b80c03c1587c0c000e040010f490017200d0030480c1c0c040d010400e00c001500001c04944600d03104006140d1500c41d0303003029052a81c010b0707004070010380d000103035801544200c0c0c1c46410b14100900c2903509062182c101f900c150000c46c400110520008a00310400b07100380c2511003413180702c940c0c0e901c003150400401d954040703096190507005120100312a100d0102100e0b00041400d07074031a82e070000120310324010900490050301c030003804420045418200d0b400100842001c5800401400120b0586509441360700f41154219080c000441d1200c3d0044851001c000701e504000700d03c400d8074887c000129006079000080312a000303410700082c002e4002d02d0319800e00842c5400d21080b4180b01815004c0c1c07006100c0c1800c1c02c1800c400381c809018042d480182c10340d0b4002c04030b070841c01460034010058076060395154072900880010404900e0680300d26070883e001c0380510711b501d500003402404607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 934549874 1250 934548624 934548689
    0x30f050c0c03010c021e060c0d0b041b2003160b180f010609050612070311041d10050603060919151419061215021204060902090709 58
    0x310701c150801901c00360760a001e00180f512540d80102040001c1c481262154802001c1c030040d01c1c0c000700240703c11004003d085440c160000a004104d1404100205005011031400b4406001c01c1e2000040700c0c80d400b000000c3c030200301507184030894001204250700c0b480f0f800d003001d182c070b5a036189220025500d84501680241e0424002a065074107007405820301d94580c07041021650b40c0e6905204000311841b4072600f02e8001d40d940c0b40c020700c80404c00c0790358801901019041c090b07181042c41036a5100c4e009a40b0400240130300c0c0c0344c91203410083c1a910f440e200518070f807403402e150008209080000e0002d210303045100040803002e1002218080c00e0300c450206403103d00c20880c0e41c03104c64030b0a000303090f5407031803000007620b06103040e8540a5402d8104d100105246003004d00c1003100d140161501c0840340e07000003450009240012541000b48151400542c041840d04104420300046501401085000340c45002c1e80e907465850499041c1d8140c000e0014464041e140d0202014050140c2c003074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 934551124 1250 934549874 934549897
    0x114010e13050307030c0c1205061326270a0e06030c040c050903060f090a06020f0403060c0207060e01260901270c050d08090114070c1d13030f05 64
    0x499010036142c1d18219440380106402140e004807040342000700c004240c0e002419072011160703500095598481d10f412006d03143c2502c070f80588003050284507685034050b400a200d440c100c000e080600c0d0711001290400000c40c5503042000d6a409014041d0614209801000801c1285100e0401c0e450072001800034201d182c01d8450511070400ca905e46105195a0440c903803202500c882640c02050b26005008018502e81c00c815000d01807102000140c080f0010717404140540c80340b01010050413107008650019200030b0900785409070003500403c020040e500181d554440c0311020340c005480b200041428581c2003030404420342404050080c40d95040407144c40081500198424480340e0a042100c408444014000ca0035080003200028400100310a440e21071020b45140c9815006000d0304404505129409420304400101c43e4103c41207c2c0d1300c0300b0820a0952168001c011204803001802c541d203d079480803480503404181c0307642449526a859403c1e6a40c041002c46194000004066 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 934552374 1250 934551124 934551151
    0x5030a030f02030c0706030b0306152b020a0e0108062a070807020a09020d060503120a030b060c0d0e28141302120405190f0816150b010f020114010e 65
    0x4c01605041c00914000c02080c0d402241e4080c005040500f04000034140c074285451160064a881d01d0300c180001800000c50059483d141c1c54001c82c1201440d80340b0000c0d8000c26407007004c20758107d41e4a5481c141c801c02d4042359190303541c244a4000c22418080500003440d10650070001c5840c01000400b0302c94402c101c514180f060a03030110f000030f150364001d0030b8895000300d01c880d1080d055100300c41c0244400c500800101a07421009035481c412807240004058403203100396a5600c89504860380342c110007044500402c6038240041c1040c418001082c82907449500c44104078005100c0018904105c00441507910700d00b03554039268403488940032390081130140003485001c80701e10140182d007111120309440c618080c507106042c10132910300e112082000c54800c001260111000441f400d40c0b03c201b03159a103050601c009042c0041d400d005200034104030180d103020041d40c01242c15564282c8031600a00b5408a050b03084c0d5039420884440038400c0300040203940b11500342260852649120f81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 934553624 1250 934552374 934552387
    0x120b2208071e060c0f02011e1802030609010608060c12070f03200c10020f030c070f06020703020d1101021e160c12030801151b050f190201090b0405030a030f0203 71
    0xb1891008000d000d5500d16079840300c2d041285d07080024840d039800d09100810046503001002c00d83c60049040c240d4035603945603510001032000e44121611660010f04035032003441c1001c080390203002c1a0180c035803a4011440404c24100b1200259030310601c03694080c081d03951380c41d0310459030758140e901c1340e20030540c40d65a94128000501c08680300b24181e582a281d50b101c60040c0ca900e02a620105009414410081c00307914040c14400e80f9080710440035a165142c00c6400c14582c0f02156a401400392440041e6540c10543c0000300025007420503110606001d07a000845403c030f018031968224815903003924408142603440040403510950226068209a65103940071036015540100d060404566004c0b414180c10020160060001410f00c0988040303080e00140b5406443e860310b0b9094144013000b03000c0100c140104000d05a280c8115026680c102a000303040340000305060780400c2107182c0c04210746042d40704907400e0b80c0010b00100f4000c00a50340481d03110400b0401c42007180000d2024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 934554874 1250 934553624 934553663
    0x609110f1e040f0617130f0501140a0632010e0a0f08070812041203050333040b0406080a08030714120109230604020c0f0601120b220807 60
    0x1920140c942c000c102d2603044c0c2454130240c000c0c0410250b5400d000241d00400403844039610415900c40da10119040ca842d41501d48030b80505458000c404000d000d041c1003141568896004a08503805806106040300f41d81d16034440081000c5464a003c802c141c0c2e1036940c0d540a08011004071001a243e081c404c0d40d074140310341040719950400b19031030300841c40801c6811800c2210488001c1a242158507081c5890304182030003a201c3c000034240070020000401e05c0c01882180c00d1f1038584040404400d0344844040c00c00030041050061046182100c80c01403403c0c039126010540b0840c8004240300802611032170101d0300000c103158200b00070b220a1000d800c18940c094105c1c0c4e090400d000301107504200545050b00c0c1c2540458014000344080c0f0440d0081e031240041c2c000c13a0035500140d2300c0104101450805e5510007200017140f149034000500080050010303a00e01e07008800c101d1894560b241c210b16908081003134801c800340070541703120110b0401030061000c988a80c0c020081800002c1d207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 934556124 1250 934554874 934554877
    0x60207060207021008131203062402190203100e0f1009020901050402190804020a080a030203040f0503060f0f091009050a05060a0c050d320a0609110f1e 67
    0x1049603420780106036a41181000760741810042810300305041d1030315040c004074481048082c005401074105407aa210702e0f60103a448000580030507210010b0b24011b8012201010180300000380061064062800c00b51100c1c05a1001d466070040180400e1031006203c003010b84444400103689010300715158007c14020031541b010004c2c4c040e0081018043c5004000d84010b05a209070701550040206136902c03680c80013401001d5506040a04081e00c0c6c0d8004105e00341c00d950441c1c441c610404540780c0c203040d0004003501c1101d10b4911a10351180c0c5900605845170020f42e01c601c0084402c0000c20580d407040c1c44155480b1100d5011680560002603807001512201841a502a082501d6410601205100f02c0d81d01c428100c0d03082c030450100900080891044607040300c1300c2c40da101070034501d00c1c90001d5048204441000c20202e000b08a0a108220480984106440078641140022168170ba030040c03901c0080100c01141c200b5850b5028076000394000321040c0340386200c03e0a111815144ca10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 934557374 1250 934556124 934556137
    0x50706110c06150103020306130e0f060925030807150e010f0c170603060106201b0102070e090d1b02030a030302180f1f09181505090f0103060c0c0602 66
    0x7008000c1401c194920090380703080701207018100740c01001048129103400304c4182d0f00140d20780000580c006440507980c01c01000424404a40c010302042c001c0c03035030300041c017620030303500042080021270786011000c0e0b110081e9100003000224203101443c0031854040b106041314800000c046a90407000c0360150868000d0040d54001640d20b0042050080d0f111b000800350031041201101d140c14031900096464105105103407c00001c403103c0782d60503d840081003c5001a407044565500303295a0208a0100107a04140148580c040c001514154100b03000d01031040c10b0b01400b0300303141105049655100f801c90b400e0309c4e001d0355a049030050310204200725041d0f02a5a0050b1112400d05031f4452200d00d000300a8030490320802502030301e030766009180c2444044d0754941044002e480d031044c0d40407180781c0d10180303050300201040301d00500d064100404100e00071149003070b0380b03440c0c2080044111041c0d03881d610301c1e02d4410040c0300043c41c55201240c1002c444c100642c01e03d2403681c0b164266848417 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 934558624 1250 934557374 934557397
    0x10f03060e0a08040906091a090f06130207110102192d2f100207140a0510080610140304141c05130506040803030a051509010b07140105090d05070611 66
    0x3c1c00308100100347c902c0ba003440e0481d03201c50389414401e20000984080c0002e003c4909901402c4c011964a0361072404e0700008145001040d03403541c1203403c0c200d4096540c4200303a4054010750140c10501d00c00300c4080d0000b280d02801c1400600c3c20b200b4141410a0a11003d02911004c6c070f0080001c51032603108140081d400000b1640e041550a541580996895900303a00420005501e02c0c11160007003901801c0c0c82d440080e03050031115030800155103800c940d20068008400c1801402e055038001c40091140381c0030baa40000c1442c2141c0300303d075118005594a4044242400880d0014a004648408143c111000c94200c0d0422070340002c1104100010440071079800a02d000e803804103210341c0c80c0240002c9a01078109890803d41c25140e10006107400140c6a0303070b0000440e807a08100c2c0d840d41c60b0701e000d0401c020a40c1c50b11000455544404002c0c3c0380d81e01605980c0d82c405505004880c400c40704c0d030019007400f001c8050166819048040f0071120240c4410300f00040003261f10160001c01040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 934559874 1250 934558624 934558631
    0x201021204031b051e01080a060e0c03070806030a12050304050f060907060e12070b0c03070c06050702120a0c05010f230a090e04030509100507240c0503010f03060e0a080409 76
    0x1000a10f480d48060341d10440c05100800d00004507104095048080000282803030b070300b03d5641c003c1400c004c180d250800007150b0714000a102c84806204080e511640c1241c443c3c803e2034554804055541c291440300411900c024041c00f00000e01c50005190414400d40c121000c84034026a554186582200c5020071075001c540100b01d030781e0b400010b541402c0c030280c5040e09980c02510006403101000e02905000300c2000444402c8100c04000311810b59401c42d0804083c261216001070196004010684c41081c00f44002000a200415280d526643c8071071440b030280d01c1c02d03005440c0702000c40110b00500c4501030711010592580c00304002400d201c0e4088031707501e154a1402401c0500250440c0c170700ba000c1c0c0410400080d0308241211003140045841200143d01d0401c112981c0c424150000e2440410910322200c1038880c00b00341403c60701545084c0003400d100d00d1f0840b00c0740003d00c5401c1380011440300800101d22203074460060306c4105810707110601b150791500d4030981c2c00b40d0300001105a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 934561124 1250 934559874 934559903
    0x221010e100b030c09060304080c03190e090f060405130c0b191b1b03080d140105030127110312030109050705090d0b0a180609050d020102130909020102120403 70
    0x56071401480604141c140c11030070340c14401c00b49500c0b40180c552041c01200c000002c5024066540d055649035540c810880e60f0340c21080c013204071344041020300c0c90301044a80c10341c01d080b860701c04015403145140d80010b00c05940c5140c01c00c4080c28000c4e04000080a8401082d00414503894000000e040c10f1441d1540c0c4000c038120903003c42c400118510100007508040d1086440d000513180089500008440410f14011040403444c0d00390343d00092060300b000441103141d076415084281c4400e1b001c6604280341c2e82c0d40c070905081c0d58141c44514880c4055100700f6229010751541840014040c1c00b5402c5260301a50200c0c3c80d2481d0421800030003000403004004030806070240640c40601d52034580c1c184003804003c80c60b8909400c00080590380040d000034a4824650f00c01285400542400d100b24542414a1b0740201302e1402c00fa078550181001840c842070050088680001d03804150980b060f140c2903000c00107140c1410103c5c114060300c8400c40c0d10f80c281c44060000386015a111103070440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 934562374 1250 934561124 934561141
    0x10091205030c0606030604031d030304091e0e010b280e01081e011401150e0303130306110a0504050d0515180d1701230607030201091209080309040221010e 68
    0x84c81244030341e00078010070001992003403014010304410320a41000c01854800642903000303039002002c1481c500000c455100160050407001031903001c204120041d076040c50316003a604c120b052241c0040563710768404543e0003402c046264040300d829201441e4444401d500002000e90000c1c6a5501c901281000c10b0400c002421b0800d01c07900c0204005080003803864210380052051615a407806000070b804103009458551301100020141c9540380e100340d421284114050000b901c0305460181d100003040a188111a4540800d880341800e00c0c0c580f10800800041c4144102c40d240101109407400240480c1d0b9107000d552400640513110b82c11025141c5881040b100c65010821016142114821074401c5e06040d64054603400340c103130907000d841c0b4500001145980390041c0000070f0300001d041e810762002d1403061051340740a0350f810340342104a522007428080d81e90150002c0100f00305521307096008080101d0340405043c205d40f0007407000300d20020300360700000c00c40d400c40e4104084074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 934563624 1250 934562374 934562383
    0x6010312080c0a0813020105091008160305060913020a1e240e1e03150103120804030f05180603041b051c020f0a05100f020105011d0610091205030c 65
    0x41da40326040b4203102030f14000405410020300401d1020070401c1d0045d0643e44035404030303081c200c4050300c041d18800ca0000b00400c40d16040f1884990390086c40e903003445852003030003200d000b2407004003185156128604465485034030010101e9004411100000d032102c5e031500a64819240c1d1408000710034680030040d82c0c2d03070b44080044460021410700c84841542c2101480905400c02d40300409a20500c01800c0c459070708009209a00d84501d06a40f00400040242070b0305880c412012070341026510a0141c90001054800030045045c03002d91030266489440540440103815010041d10f511000109a20384d00546054441c0009403000e4204581030360034110062100341c8461612400d1400c5002034110094402841000c0b8461390034400d03a5108503000c090280240f0b0302c85d140b002e012016080650103900840507500340ba000090380042408484202018179070390003000da4580c410001d0400d01c00c0711040600442d0040822003801c102c0e941d07840d45c0e1003440115640c9480c1c038509840c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 934564874 1250 934563624 934563631
    0x70f0b03160302070b1b0c01020711040c02070b030c0a0504120305091f050f0c0102090303030907030b01140a1404060b0a030606080112050c01120f15140103090c050607060e0601031208 81
    0x505004110750300004000c140031981c00320a800151b61981300c00141c440451080b0302c0c0c200155800800c0038003c1c050342d800035680c048411101044800650034061780c60344428455460804401d00c00504201380000042002d11140d2801324901078850a80007184403a03644150009540800d00300014100320f1405e00580704c00080030120350550b81c2c002046403143d101481c8988001040400d071542007501a1101510018152512807401407400c036600e441512090303881c6018000002448a030842c1c0184174080081d2084185508122442190302c52034a900c40d002942c0b000c0c001881143c0314041c145148035560b000c5075417894a503004010300810303004041d020100a81c41000644005081071f106c11003070800103804201c0d00d00c1c01000704601c0c503100a80b0303400c0107000780415442c4080780342603e541d058174544c0190031100450880b054500014901c4031071420030300907854081e020700005841982c022404540d6080400d04140c03003070780104d40c4c410319110446511038121545950 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 934566124 1250 934564874 934564877
    0xb100804050f0f0309060c0c21060f01030b0c07020f0a06080108120c070303030c051c020304200a060806030f010e030306040b0105070f0215040e0f1605040f030b060102070f0b0316 79
    0x140c1c0300c03020f040b83d44900c503035034140f4840d4800148194111105208140e10780c4002007000303490f0920105480005600400c01007a41c0c0240c10000301e41c042001d542030f0503a43c0182841c40300340d903805440e08075540940d07010f07a8400c080b40c045101640d203211011000e8810707559000143d52500c0d090b14036001c59441030542950040c8480c00200300d000031800200d9400d8940404c034100c00090594052007400c203440100180300489041c07220f0146c004600440c810045071109a12104060308058448421180d01441c442c0c01004207030700c1003001030f0f04400c00605803080b00c503c46540707508440514165005680003c000c002d010325182c8207001156001b070a1082c0340506c0380c6d40c1c0486003040325200a1080b8491ba2070000c210317900c00d0982c0c3c040d0601958420039030501400c1740003814411039000c04040c4c1c0d0010342e481070b01e12481c1920115840c03a48104c0c800350446c0e59501030414000c00380f9045203c0e0920005032031003c080c00000510300c40348400d07078070305000c0040031400c0c0740c411701c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934567374 1250 934566124 934566133
    0x3091b08060406020f0c07060f1412180309060c070f060215010308030703021c022d0d050a0e16172103040f02132f03060904060b100804050f 62
    0xc80d110000c6491580103602441c010b0b031302e0003290501c01c481d00030b0040001c80c500c02d12801040594010402d01c41c2c40d811030301c07010340d6103c544820380c4251040960f0030066614880c08666200414040710032002d4403403045d00d080010110110f0350940050300c2c2c01505074024078042180c501c00b0190350015100d2480541290b03c2c4043c10007091060620000b09000c20000004840c0b034801d0b030554500c0050381d071880d6a41014011901d02a400c42c82c00d891035101c1c64240d0400d008205100004c0e840050085281407669a900f914010720006003801d134403e4440400b412040c900748001c051382c4982024002209040113280880340503417882d02c15081d8072001802e0210340c1031188014164a60180d01541c0b4dd40368540b4114110402000a4100c01c1c41030010101450a410a1100c500501e6800390449a1108002003c942a0503132420030787c002c001140d41c0f41043c110403640680100380202e030004000c40800c9135142c41c000c42c40001010402440104001404442030b80c48040b0001c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 934568624 1250 934567374 934567379
    0x31e0605090a1b0f170c0a110d12111c020a09090c121d010903050c0f010902100302091207030507180b0f060d15080a0614040c030b0a140703091b 64
    0x9419100040500c400c2c00036115209004e584a080d0000e038043c042004481203081c4540040f40a40000d201140420540c0d80715100744200041e044582e05050703650100c00b50424025400100800c00316200002404c1284044210350001c0c3d81030800c11200d8014ad0f03070000e44400410b01802c1c3c3d00138101d42c80c01d101e8800f1050f40c1c00040c0c0c40300b1407008600041e003c400d20f49110034880d20200c40350002e5090541500506030048045c0980c02c1743c0c0c406542c080305036032496600b2030320f110710001d40c000b41c107484d00100a446540908001e48010b4104058203d80c45911460181507901c101c4580d405590140403c80010700107811441e207009040c0070103900c820005048280b4540c010f800381c0300105240f040e42c2d105030004800510701c3d41d1851079460301d0741c90717071510388000d9002522482d04001c0414a000e01006540c0d12036070f0005007021072103040d5030307036074100f0040500340c0650180c03195058840b1501546004c0d0042e031740e6440010b405000c900c0c10382c210868680840210341e940b000b04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 934569874 1250 934568624 934568651
    0xa0b09030a140a030b030d120b12071403031b031c050f0411042403020312040602030409110403210905090c0d05060a030f15290d03031e0605090a 64
    0x1607101c0030200c980e60748808500c20104c1c0100000c804860785403080345030046046410603105100040b000c1c03028425001c2d01c00c00d01c150408103003040422540925020007061403140c902c030802d110b000b401c0c1c0c4d1505640a100b160040703940c87d02140150000508511a07144001c444210489600c500f84820700d4940c22440d8080002003000d0071640d000020104140d8599111101c0c0b6a81043d0415841e8180140c0700042903190204070300170312a00350b01504a11034642528207c40a66000b1807074035007898541da01030512044003041c40c11007071001000040810041180030100c0c01882c40d0546070071007008181a90f0b40d88081e0262003100c042c00f0b0440d103d81e08603000302841610105541e00d400c00850780c1c1940c282d101510740c50500410368200f0000c050503511000900400b40a400000c40c051a41e550b1658000040c140060311146100e0412040d03407540d15010b0300300010441c0043c215081c1c1031140900c04000c880c2c0c0c801c030512082c07030009003150b001002008108090011081c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 934571124 1250 934569874 934569887
    0xa050c0f061e130c140f04110a0e0402070807020d08070f03120f0e0304140111031602031b0d0f0501091a01060207321c030206060a1202011202180603090a0b09030a 72
    0x240031402c1010340102155038403911ba05400040c0e0150081002016062042c8800d800140c01c0b00009404802521010300c4e1900a403003606030419012450400d166003000f01545d07243c1d078203c450440501050010503909851281b10a019031600c0c0c0d400c000320a0300e01c0403182083c41d040441403520703050358140000002500d080d1124104022038072601b03100140d460503040d041c0c01409110001b0120b422500f0100e030b5181d0f2a100744d086420360f01306540b40e0031154400038a000e81200d00803079580081ba43d40d20000d00070a00400000806e20900c2e02c1c3d10141000c100b1440c142c40070481c00400410b50304000b203100914402d12800d044c100b1607080c642d02c10340c0e442c042c1403405c03d181014155941e2001031141d5210040c0000f00c0c00028980b801030344840007120100c1c424a0344200c0042c001c00c0200a20605a0381692040b445807101058640290007030401c5808800003000c0150040e01d80c807000354022200c0b50002c001000da2031a00d40d21003c0003c000003000d4006000c4148025040382 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 934572374 1250 934571124 934571129
    0x190b18011a04050d0c150507050c0f040906050a1d030a08060f0a05090f070e040b030c0d0602041a091002010b1c080d06091406040c050a050c0f061e130c 67
    0x3a070404107500016501158095604401e42c400a68201e40c0704110220020710106c07465004440c0000c0c422a1065a450103607200141c031030340000c0d410f2021860710380e580e040000b8004200050408031a1600001c5400896074400222750f61031515503030703644050701955240001002503140c98140440101001c80140a181c0aa14009070980390707541c0e840701c11030180c20080c040c443d02d481c120341603e45e1a58182e5895021071262066808a81002d001301c081f0110301800601d8030400d29070511500722025a0140c807990b5090101090003491200d66a020000b080855a25a01904100804400c000000800b560b1503c0e41080c510380340d0b2101d00c0b2121a81a00100f6840716074105a07403680314140300041020b2a245001c104542280d000354442050340c0240141591448248011104105400c0010843c2449440415449070b0020140090a0810340d07511004040c91030303103000c400307943c10b0405d116000c410000c90201303040c5807a44100d0991030041900420b4444d680204850f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 934573624 1250 934572374 934572389
    0x10b0d03140307090f170c1f1439031213240c08060603010e070807020a12090602010c020a150218101e0c020a0510051201091e06030209011202011106190b1801 70
    0x14151028400ca0341042c0d5250400c845d148042b482c240b04200e030b0042c003130f80035280b44130b040085135042c9007e00041511224440d1448455a030b44803641d200c0d21a0f000044202d031001030546446800303040801ca0101e2180480c1c90202d0340002000014240003001045c090254605000400280c0000c0944503003000700c41c105288a52130304a0102c1c209014110040c01c8003075806080c01026920003c180105d0341c15900800a000046008980780d02d00c00d42d0281440710f6402001e81d0702c111640c001c01400381914020807804440002040401490f03030121004215401540c0b54840096410841c49003050320702170174098480c0e4001061101e40380a09401552003a041c0d02005028004031110141c040080c01d080c1d40e5a42828409000230b90f10b01594510201c0c5010540d410324002c05040d00d90081c51042141e0800c150000380550001040c1d04200030b244051140070300a00100740a004424150301d01140141091b50943c0e81c1200341c540940c81c1402a402015000c214050546520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 934574874 1250 934573624 934573637
    0x90608090c0d03170f16052701020c130213050a150f030623120102040b0414031c0e0f010c0f150b031608010b0d03140307090f170c1f 59
    0x1207050445044c10491411407042a2480034440700440c4090214862805020305800d004c138030b001c0c00c0b2020700030422824810030342440f4641c002070002c08a001030b040d046c4110384146002d40000703035403516840050000290f0000d8083c8418040015030000780c90700b40c071880030a81ca4040c40b060b80b204011148020060000945802144290010002090090080e600f5a007030718800c0c0b02040b110002640c80381e80350070381000400c0018000e6030100c8079031360401c81c00d0a01d0500000b03402801c0c10070517a414000d820904030005c0c4d1144071442c0594169441c0300e1122564024080c0e58201d010520703040c03000c1900007400040c8803809921950f613009034049151690464184050b040003e40107505026051105080030850b40113081202d04180c000e110440f081d07000e101d001e6001c2c15001c1d001035050700da001c0c00c2542000041d43c0000a5240186a86584014140034040f1a800407403100d24a001c5240030440100a15403144030121543e80031400c1c80c03102c24cc48503100040000c180100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 934576124 1250 934574874 934574899
    0x308040f06090c0303020312151804140717010f091707051e01090c231504090c110c01170105040e030706051f12020d060f091a0601090608090c 63
    0x107880e0000146160320021502000e500ea140c06910f80d0055503024200303581040000b40500070b4415017818513440600220030b080306448501640700d02c0140709580303060041025000d240e500b00b04000c000e0405003040e0400b034860030b00c49400c1d9000519081c001c2828418001c0c081140c0c900300b5100d14981651a5a840917070f031810a00389202c1e100e600454a400440c00d812004040d08400e581d10b1181c100c024241e43c0380d40b81c02d0011090403000708114003941c00003030118104500030350701c2031400011550415685140c3c5a09071380f00400c0010005041180749010301004010211504d002420b2210700c14980742e14640c01d48005100c3c1310f118640b41c07002040d04030010320032a050340d40c0054052020f450903020a20a03001c0b4500c501e100c1982c004000950100d201111002042d8020161707401c00c180754a80d400038141c0405981c3d11960b0b1400c0700d8001030540c81c8600b00f50402d21560000c40e190072000541000600d41c42070042c00600302c20068002c4022841030b00640040310210022078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 934577374 1250 934576124 934576133
    0x90b13021e07140a0302010501050120060601030903020a0b010b0406080f07120f02040b121005030d080a0203060f09040605010e06030d0c060e0307020d0501020408071203080411061603080609070201090308040f 92
    0x11003d0815a9070303004040149081c0741e4103400c100e058580c2a00c2e15044800404080e200702c01c9241002d031555000400401c9540d071180e08940d00440c020701c11140540d0548d19150780d01d40c0700f0b074840d68240800160401980f0b07080a4420360004641142039602e1429038009009032021052542c1642c1c0d0b923110b403407100c12456040d100a8003c0c619030301c0d100c1501c041308040014050f40c030044c0c3d60a83c00c40c0040d05180c00240a041040255a010084c0d1144040744029403c05400194000b100c0710100c0b03483d480c0c20f440c0c079100314000c8001140d5035140c2900c101850502600c841d020340c221300d50b64142a80c0044400100ca43e0240740051582c0e0600c510505602640100070350000c0c807500420144241500a00150340d1600c003510003083d42c07803890022520381d499000f0081154a00007038040746200d4807802910002400c424030700700104030001090400044200c01090304a414889207080014010340d0010f40c60000b04a180c0a50700c01410b1500300800003048200307503003038600800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 934578624 1250 934577374 934577393
    0x150c0c09011518170102040906050a0810020c07090e0115050a060203071704210c08240712020a03092904080c03210426040501031a0a090b13021e07 65
    0x91400161019214213900c003418041d52040c0f00c2d4500307590400a000c00c00b880c0c22100701040761029001040b04005524002e000307504211005000c034041c0220015404246026000302403039200d00000e00310310f803030790b202c0c05500e100c1d0003190040d00c15081c28007100e6000000c40b00d10a400103d0721100714180c0076121450701c2503800154281780360450340c00403021402142044240302d08180110b00f91680d5846541e0300c01c20741032000380b07c00b498684c1c0314906080601900040c2a240c101c0e0110108071a10080c0e81c0314500d64400256181c03420b6060041c81100d01c4400188641c06608803420020100b2244001400c0a0089880011306100c0c0d100c00b0021100340d441c81018000c0e2100c3d81c400c00c1d01181c00125425542202d40310040c10b80c4224400d4606000111030420340d05040c03c02004500819094003001c0400401c0306601030315a0350b68134414020b10340c031040402c655607001c040c0849189102501d800071401486890514011203040300012a94280c180d0b44a0141d800d006c40320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 934579874 1250 934578624 934578629
    0xd080d0f14011824060807020f0601170c09010b090406050d0f0201180f240203160b0603010b040906090c0e070e1e040c0801140a141e150c0c09011518 66
    0x80004081e072103942504441c84d0030200c8009403241c9105a8a41d0000d0b40c03111104490562281c1100e0014014104480d00c480784000c511002c0368240002000460300040d000e0308102c20200c00822081001d2605000b010060001035591507440111075540c21444200b581c0001c3c14025104c29440310060b0640b1010024143c26841c071200b00d903a038040c040580c130389400c0744104881034204a00314030300001c211803240502d41d600584480664450700e04a010103003456a2654854280c02e0f500c0d40c56000780707004c19029800001308442d05191181c45040f1540c003c03103480d60070030100302c7c1c2c1e65004180c40c09145070944045040074600c05209402e0014142c03001d900c81e151111040c4005c0d0720095550603500c91385a08900c24200c6810080102c0151045ca80101c07400340034084981480391101d003005142481d141c1c15010500300050010045051030040d0400c045100848500c0030840200c5540c4140c44007500d6505101000c14031680c100000c1051240390704580758110702c810480c0c0300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 934581124 1250 934579874 934579901
    0x909030917010207080a05030412091409090c06040f0f06090518060f060307050703090b130b13050a030b09010513080901050714011a0f0301020f09011407020d080d0f140118 76
    0x981da001048094440c4d00159002c3d4ac03164101c440350b10707117140a04010416110580800d2850101d128200702903148003c200134503601800c811a034080c3c540d80061301c00783c403814140c0c90059080c40d13900204100641e1004040000c0ca440400c4147ca402c00b0510426904030171900075580c4440110721a404140302d0142c10010020400501c241e000c0c000d0845240f007640d800702456039a1300380300b4040c003079030107040903211107030000b00503d441c201c00421403038407070030504200c007544c5030001400e100981c0d1041d158859014200544040300384907095020f07901d070205003400c00d81d64652120350700031180a18144100040d0333490900800c90b035200050003586d4000d005411074040c1408030f01c0007194800340100c0070fa5407850158a010700030f4604028051490700c1c2403000381ca0044400c28004d8003280100d40c4208080c2c1f000d6280d1b001840032850041c1d0801c0e555a0180803070008844610420071200c03460681c42d204c0b10600e0f07000302030445107541c2c444001da03d004801c10008148580300d840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 934582374 1250 934581124 934581127
    0x320031f0518150a0305060705090307030803040515090f0c06090607020406080d11030304020607020d0201050d050a050f0612070e0a060506070c03021005030906010e13080a08040c090903091701020708 88
    0x11049440c05169603ca05140301d00c800440d410001031280b04082400010101c1e0000400940400d00c0350002e40031800004003143c01481e5a81c039450462341c010b44041e1080e4211101101c1d80c1c180c04949542c00050010080840d905c0d80c1510580b105c000e43c0c01076115641c0042cac1c1004035500d4500740c2c1e179101e4009200b0400e003680d8050841ea41c4600150400228a00c5903c11400150101c01e0b02c1c810f9030050700203454043c1f01c0d030802c0141c11282004905000c070510a40c50200e4061080e81d124041f100000209410950703100008000020440742c0300e42502084000c59a10106001c4100c600320f00b042d05c1d980d00c1d00700540010b495541c000d1900f00101284410a00032480f10a0007281d009941c0b404c0345c2400c04904031501d101c202e8038007075164070010040080380002c0800c540c0c00220712403407407022082075646035905e80c072080070b0b4000600c0e0802400180b2507815620002007140c1d071010005910309640280c20304280c1e2062503110301c0d00d0030752010461405e40480d80d9450b40060490b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 934583624 1250 934582374 934582399
    0x60807032a030b030124170102070b090c03071418100b0a05090406061407140109060218100f02190c0509040302061506030103110d260403030320031f05 67
    0x103000f091140c041c01e12940c00c1c0441400c3c00088000d0555000c121110500f42d010f0604008540f41d01501d040c050301d5660030407103071010529000100e800707118040d000c2c1104030041d07010507103407005941200074000f401540780c88055079405e5200c00c024422904c01d80303840d510a14030050130a0143d02555100b0000141134541581c00001401001002c07901042050f031980c201300c400410100810a0491080150201050513000d0290101506000106840011ba03039508140d801904c421140701c0c9201800001a261440d280c408000c003500d0b0404c8985401c10001303540d0340340009a0f48002e2107400c00c02050200740f00e1201d02a0a000c0c28030b443d1402c0500d0300940e1182d0480e06010800514080300c88240307040c50489049a401610700c00d0b0310004a801c00c683c0e00e00c0260112400d6024101c00da4032101da500708000140180c410454840d450742c2400303001d90304540c112080452070f6901441c0c820446d201642e402c18501004843d4080c2480b281c0e0340b221041e6003025030700407088800c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 934584874 1250 934583624 934583627
    0xb03150415170105090a051203040c030c0b041409060a0623032a0901080402010509060d0c0f17160f050403140109030f030e0c09090c0a030f0516060807032a 69
    0x1041c074a20400b0001c0000703a0340c00805d03540311200b001005103c0c2e00300d050502170003c612000f540d08a0700801700c0c01c15aa5030703640c80c80041d0741180d2280c10b4030540401d00300401e013940700031003a03c103409849441307951910700b0015040703a0307141c005c4400b84400c0b00614940c3c600d40c0d0302c200003251600038078036a0302d0510101d000c8680881412501110824280980a0005100584150001c1a1075041140e151680107440c0c540000c40c02c1c6070050414014102941d000b8040c49400c214a5200c02c41100806900100240b421505400c00d5002c0cbc3c00c01e022480016030741045400b051807078000c52255010104070b0750761250381d102a10320030810304200b005a00660010706054480e45501482c0f0440e0402035003502d05040030944c003904520b8071040d5904154400f640e002c041d5800703503030b0405010b4000408a055640043e904022600c0840c02044000c1002c24003441c1c4200d8000c4030940b9140b00213100700c900804440405848048009004039204440c80714038030100e0760031140c1000b8050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 934586124 1250 934584874 934584899
    0x50702060c010b190f0e0a24081908030a0203040609020a08150709080606100210020c10062111030c150a090b0f090f0612040f17040b03150415 63
    0x10414452282441c1c110800d034500c204042c03c6803c100d850f241750502d000911000000000c00c0701d1034554840c0c0790b0a0014208c10382c020300540c0c142e50b1254010781007002e01464242121540f0741d1150065826101003001e00050369403100c9070b00c0300036942c2d9642d494040050007000740020340102048801080b0b2060100701c0f00c048103a201c080c0d03940c0e559200812201401d440c0b0800c1d169402080205480b801c008904080c1c0ca0180d0044070190380114401c41e04a81c003401d4001d00035088440e8402c2e0100d99400741e000106800b6000e02c2a030b42880c1c028800900300340300018190b0b00034a6102007540c80600c40708945410082100e2003000c5070ba031007000b540d03208514850004182860100d944801501519003207a0f03d4035106082203083d80a000ca440d007403400c031a03440541480030700c0703400500b81e5072140708510405050302d041505240041080012104115001d8001d0006006200384c0c501600d0340901c40780078040c04903680102207002444113194104400400281c040307003c01120a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 934587374 1250 934586124 934586141
    0x60706050c0c15040804291909051e0108130819080709032d14011e02040311010305060f0406081e07120305071a041a0609040b010312050702060c01 65
    0x7900e03880c0b2404583e01c800d0010407100181110f400f4003090000140105404081000400c09442c401f600c2c001d03504003d0b0092407010489101070050249a56440b4000c000141400e940d11040385c54041100082480000283c0741040f0760803000540414100d03615403a45504981080d0356180d140307000e5541004104141008509031202143d441071190905008403900002c900040d00c001c1c002d05008071000c450800005550300024801007240e103401229210030100000903007154240300007a4868001c0b0151100e03510500c010400300300a8004035400d0326007440c000442ea035a00c8002203945254002c001d41103458480e000c1003078200000c4030f05408002404006501c02e0307014000360340e1a0f40d405042c1401000416410010740038001070540391344a030303170710007001040c01d10400c0401000300d5043e1040070000111280302c015810b10349800c26416200f5104518103a15030b0581468103200041002030004a24001c030b51080080e200382d241e0041a0913035414900e10054080c18080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 934588624 1250 934587374 934587397
    0x1f0e01030b0f130b06071e020a081204050415090f0f0506100e210a050a0201080c03131502090310020909090d1d0118080a030807141206060706050c 65
    0x1c100c003103040c580301d40d00a8039500e0082502d042c1005440e450805041c1510b06a904001305028100010700c80c8103600200300000741c0180303c41900b0b8010055001d00e9544408141c7c0c120300070301ca100c0a500340c12142901e01c00c0c2c3e0049120012a080800c00c0b103c0c03035101c4240f880c82c000c00251f60002641001c101d2138110407040c0055100d0100700441c045d4262840c20100740703000d4400c0554240043d540d084004204028201c084184000c113060030040e40c011105a04440e20b003c08541c0c0103210182c006109503981ea0071480c0c01c48c1c50881c070301c1c0103203400f40c951039101002c0700c045045601290100a000750a030b9003031000000c0703010043d40010031210300c5500c8840000e1107840d80050103030004845991452887c0a2241e001d1104210b030008540c100a0024250010401e4100501e0020322648004003103404030b82c01d0041411001400500c104145030041445600d148020b4070348007007413080c0c3d84034651034241c0010818894103900522441c10300040080315924007003e0240801c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 934589874 1250 934588624 934588631
    0x3030e060c04050117060a0302090106110d050a08060112110a091a090d03110712080702041b212c060a0203011d0402120f011b0206010305100b1f0e0103 67
    0x140001e1800034021030084038009415110845009800e144881d5000000039142041080d165004241280000d0304082c010505503070100011070020000c05500c1c00c0c1c24603059040c1003c140c03004004000240c81c0c01d040001484c4030728120400e56000c2c42d800c411303400401d50f80c0c81d4031000c06010b00044c0c0c41047e1800c8120411170704c041c901041115100315000300388407014045030358143c0e060309d0750188041c030038403a00c003010400001151500708128040c40304240c03600b5042c41000b0503100c1c0404084c0c030030607020000c40c4184e50405200c050028240a202c00800d0245503a8001440209000e003501c824244440c0c0c491031008482455800036401519020382e501203525044c0d12080c842c903488240d07201442e59000341d42c1c80311240c00c140b00424560410a84903d070078a40106e0f0070216941c0c1c0d640d115a0108000c80c0140c0c0200c4900311700203420150b1468545680f02c0703050000fa54915911500d0381610303607903480346070914202c00c1207000d100c07902c56150050080d9260380c182d81c040383c0f5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 934591124 1250 934589874 934589881
    0x7091508030f03072001060306060e060d0b04061a09010312030e070e04020103020f0d2a020c011706030114010e0f0a05130212010f110c061b040e1306060303030e06 72
    0x101104882c020500c14048a00d5074880e80d00440701d6500002c09414405c40c40654030781130500a0140c0030045d4010700703001c141e86080c10003003030035424003900c42e07807194a0340c2107284002144510b95540c0305822941c0042d080340c0b0394005071a41e40310381205903400f03084da100110400000c035690300503c2480c0d940801c480850081c0c600e9841081e4040c3e540c0780a4254006070041d13101b5002032050007840030321036041119610002c810344c2c0c2090110248104000151444d40107800040e680c8100144000c02030f004001c80040c00601100020300407501c4c4041c00902181c82c25000110782034018044c907100c1c7e42c1d450303040f640b9540f015108c081640b00d078100030403400b100d1405628080d5030800700c1d050300c000d131540c00c00c069451610a41c406d83e541fa4821000b60406512a90050084180d00a41d84a5440313001c00d0400d80e00401602c50100007031012108c900301c4409550503601c0300740e206403da80b60000c09001411148500800c818288803000c4109545038000c001e00c030000d0030494810783c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 934592374 1250 934591124 934591139
    0x1b0b01091802030a081309020a0f0f080606041206060506070f03090608060f010302210c0c010e0706050f0310091b020f0a02010f050a030b04020d0c12050408030a020304050f070915 79
    0x400201d03010354160b000c1d58094010909500080050411242a1589041d0b43e2080b0000f603800030a811070100b00d004101800f914ac001d4840c2d4540641440c002d40b4500d046000100c590181c0c1c010030150250b8640008100905544100003421009060a8440c0c0b11442c0c4514640840d402c210001035192200051304c0d40203003a00b074000e5900a0090000091002c0110025044402150051b04050050440320075a40490500610a08650700e90720810340851a0954805004041040d441000104901d9a01c4400d99801c8001d54021035980e407a0100005001c48480e00a01201f40c9000201d061605500604021001e45a000d0361892000c440c02262514003a600190200c0d04805d00304030410322500c02032458082a00300011205242070200301240c100c154021149079680c1d2140600c103800540c241070680c05000103114501d440c0d030343c1c0c43c080d000160864011b140c001c4046003c02600340b040c61310402904040712450780e5925090070280080941446c07401510740c00100381715 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 934593624 1250 934592374 934592411
    0x90e010e040f051905100c090503070b280e100e090a1d0a0c06090f1410210b010801080c09040f020f1810061b0b071b0b0109 55
    0x200e401030860015070366552107002021125410840392405210300312400c81c4540950a41c809000d14010424800c200c20041e0464041d814004180b101d0b04400700312945e40000c080c3c05507124011800c1e190080a020204203400340042c43c000c004185500020490b071050306d04030340020031100746040131029081500d00703050180180d900b21104038005086103019401000c040000c60044010480300d60545034241800c11800301d5260100110421646a02201d5140035043e200100c2502c90314041c220b400c5010100f0882c0d009812f000c070a200000d02402050096880c114590702520800915200081000c02a9a80881d901c0b50011514010025940210f500080d010742c195840320f8a400400300820b040403a071001c0041c0c02d240050f1118144117240088105100b01d070707414044c403085003200f044c0d00000100240720b083c415907100c2021480201c6900180c12074029101c0102c1214024601b040600c00701044070407020405c160f180d0107d0403034440c000c00300801c085c10003200550b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 934594874 1250 934593624 934593629
    0x1221031a0901032a080a05031b070f032a0605070240020706090f0c082d2109030c0928090606091b030c0917030f030115090e01 56
    0x205444113455441203180100b00c181c0c04042010840c0030f65580300080d2402d00d28100071140c941010484030380a03048405103c480306500303800350140608100d010046080c00f03200240c5a124140d00c0040c004a040903690750740400c4c900388030600c607210310010b403242d84642030480c05440c02e50700c00d0190080941ca006170004102404203007600720480c000702c00458452030300510f07039420401040050306902c40e49100750f21451104c200c81407582014040c00307205030300820441d005207008182010b100015400c10303102140d60759040340c80d0f50749211300d000d20203800c0880781c00d007108043d281c818406000e014030480841c2107400c0300c0b01d040144494480142d805013031700c0314100c4c0d0315002113003100340c58a03880350728060015020907180c5650090302d510358040003141d42e4032031064083c2152814407419071041d0781824048960902d00c0100001010701c19503034200b034075010f040e04031082841214000310321083d0180e01c9585034001c0303081c5818504010301c040755046000103034485106908504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 934596124 1250 934594874 934594883
    0x120f14191401180f1a09010b0c03030a0c170a1505060f0d02030603031314040609090c0608060312030c030718061403180d0f020609030c071221031a090103 68
    0x1c09910700680784140d0030b24041000304064403040c00a03d869594483c001056801041e0b10030b1216600041c0f216000041e003000110490802820a20403800021640c003c42d141c400082c0700050007070b003282c545c41c56000400c5102059014008010b03040d8210354014a542c5001940b6203a40b003003044544d11507003810300d24080c820b100301c201c00d0366194003840e1702c003501406480c83c041d1b003200719196001c3e154102010f544580c407403000107410705214070005004a49800c03c4240c105440c1c0100881c10ba01c120420002c0200005e070854405004118110461003c90350b01c03400c2c0341a005080e60003c039a110001a13204100d440c070000e03084000411507903c1d4907070800b10800d28406140380d5100070140040c000c50240010120b040410081300400c4845d5104e18a02c00035480c002c0c24404080c0000d125a4028800309402510200344101100c00002844d440d6440c585010980307944001c41d04071071401203048055119030141c00030542845901d01c803449003400f00040000c1c2c540203000150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 934597374 1250 934596124 934596161
    0xa060c030b0d0209041a090f1501060c0f0204110a11120a170604060b0706050901060f1d09151815041208041a010f0501091a0a120f1419 60
    0xb0050300780b031100d1940244c040c00c200c040d4140780b0802007070a00e01c10b80b20600d5039402002caa9072070210520800ca031221002d01003610343d5240000041c55002d121001410308940b02c4a21403c42d034030f82d0b0020300c1100a0400b0f640d00c03410a50406000c084110405192034003400400e000b001c44010220344100e069034a40b112462041031013451010001844a41c0003903854002040c85161030001d0080b40384165004502c1e0301d4820029425111281d0100c0c2c00d1508070b480500481c00504604100080541803c18842c0d40d403142941c038001103045402e4440d80b404041c02113a2038000a2840460219021140c014081c0d280030300c64070780c00321805002004c07024040b1034007031b110b044055003060113848105507104500800d032001080c00e0b80200162803000c40c0030449540c10000c00b80040013259007903400c42c020380b03203540c1852054030940000c20840c00e400e00740d8400280d000d81041198040c08000034000d00118190780e080607510f00f60291105803140e1400c0d1103c0c0079403541880c002c00b142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 934598624 1250 934597374 934597399
    0x227150406120519290a0f060312030b04090204060b070302070e100e180d02010204051504030809061309090b04020906041506080a1409010c09050909030f07020f10020a060c030b 78
    0x204c0800f40000c2101e07100ca00e490111001454602000158504906041e5240c01c2804000040700c05102d041104141030510403c0440d00c101c10107201c0b200300341004680160020002002058000d0000303500601e40103010900b640b41c1030141003080c1c466002c4a00c601d0301c030748800988102c110703007000040198a02c00d02020046602c0190080e6003400389109428840740074a06000e0300729540310042c0c0d40810300b0031961030300d4403010a205d040f00003014a8681140c07a81212445880010390241c200000e1030700e49c00d0350b0075400f04020a90542e0400180c0c040703150041d4450030644050784111194400719909203440d01c1074482442d91a5030a1402529210381540c050800400300da04d09541d410480512240780203445201d05400c500001da00d0012002c0075042e4641e9400641c0521480820000c104200100700c0c2c2c05000d0840705c1a07265002480066107030201611001e130007000300c000c1c5c003a030103400155121410b889400c05101298013110201d0807100e210bd0071079400810036054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 934599874 1250 934598624 934598653
    0xc061d03220e010324020c15042006040e1015050307020606010302030c120702030904061409090f060a0f0603080c0c1e0d02040b040b0409030906080114060702271504061205 76
    0x7100171751300c07000070050700345401c200f42a41020250680240c8090ba035204201c03c0095049917000b0300143e140212881d1520940411140c0c080c9000700307042a040240880d00e181e400152203002030580070401c01c0480b50040c4d004040340c10039508800035118000c0410401d41c064000d4a21500302400b40340d0074102032898444103050050403500540c0001c204c4101180c442d400b4250241c00c128460103159481d0b401844086e800003401c2d60640d800c0744400e150640000700d1100e030014848080402e4608010600c40d0092141c0d61008041c2c0c80300250401e00b00c980400c1c1a400794004880344c40785480d0514400014002d030040d1642c0c440c1c0b100c01c114005181c1540302c940700210180c00010319107900004241280c612110603004105898810407185a000f0480c50162608115103c48040a04049240d40c0101c00d4002e2107000b02412510461011100340c074046c0c400c2c008582c031141850400000716102d03030312445000301d0802d08081044000305102032403455210001b045c010250381714 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 934601124 1250 934599874 934599923
    0x1050f1005090112020310031703070e1e030a03120507110c010f030b030a111509030a1122020406031406090112051203041a09010c0c061d03220e0103 66
    0x2559060100200e054040c20031380e840950710031449124441059804c5091103c00ca0502507608201440d041081224442d4815a00b10b0222030954081e4001c046418041c1d07504049094910f415126034050388081c180e0059540511029190042009444000d030071902502c0800216245520810444c92154441c480d500b100c11001d26001580004110001c0c0c1402c0c0e80c01800d0312489000c90007a0314a14000f055545954100c0c0e011602d0200390001198659440300005400e4110241d00d0003403c0d02ca202010041041d281d101304d15008141070040000c1d00310380a0900000c2c9049110400c1c2c03c001884c49020315002044598281c0c40c142080240e1000980200c3e814010030642d5100c6981d84005980901c0c418008100c0112200c1003203400010300401201040c0e060914030000250000039810b140c9401080100341c3e09684121015040030001102e41140300c00107460b84968070b210b90903910181045100c584640e554880c12084207401c1c000a4041d680301e80d1142c01c00e002124 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 934602374 1250 934601124 934601137
    0xe0a2d05010c09260a080c07170703060b0901030b070c23011401120c0b0309071805040b130b060103050403230d1a030d0c02240304050705100522170304030b01050f1005 74
    0x1411650342c0c8d91070f2480d038501405900c2a80010340e100602c2030042101a004e0081040e0b0181e072070380940d40c03641d26110704805000c2e102d20140101c00840c0c505004040504000721007145907a00359888006590500901e410045100700c1294030001094030b4001442c031903891500308071202a8107007400d21490f11940040e2040095103c0c0080014660080410030303100320b4802200040c130361070715082c0004031080007080680381e04038040c09140003403030035005190002030038030300010b460303131189019581e6024584003003080303101e03403200114081000002001501e620300da051000c0f0010b07945009442e14151035195150300540f100b1400c2d0380c03140b1b550419250004084080c2009003680c42010a11401096030f032807200001004140001000840c00600301580e804081509880c4024158060300748540b45410f50421403202d00d0a40d8000031011f4550030203252450a085281146c0d254490f1008070f41e4000300c07500004841c608014101c511000180500300c2c80d1002c070300708494551014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 934603624 1250 934602374 934602397
    0x30702090109291207230103060312050702012d11030a0804020d0c031b061b0510110d02040b1b06090a0303020a0314040309090e0a2d05010c09260a08 66
    0x44c0702283e6041c1d0300300304190080040301100301c0181d81d20b104080407020744201003411f1604085c010800200301307181034400c5000928200d1380350407903407004840305400350542d91390314030b00b841e402c481006a815020b4400c2c141d036265031041d00c8208150a80300d0041c000d400c00840d812100180242c20031212a0f01f2940c403a2a5814803e078580d9500b62002948070b081050214030440305102c13250704810f81d828280440c00b0300c00101e5120396a403a5079010f00103031a01926032103181c910000e400c8442a203030104e48041c000d549580e01c55103681600d4004201036641c081c8407000d0b080f164080030605a001d08040ea014000c4940341d45c806802070340c4807070004c008060f5a010040c15540e502c110032401a071095071a0b081c3c22340f41c07000c00020303102442c05070f6215802003405100020541481750000207034403030149100c5080035426907014012200302402c83d5003862250524154032041d0707102aa082012901e00ca603200e6a14200c040204c40412401540043c5220001c5003840f40a08001440d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 934604874 1250 934603624 934603639
    0x30108100614100c0501020403061401061715010504050a0902090406050a03030804060902062b060f080319090b0f12010605070305032412060907090c120504030e04050903070209010929 81
    0x5d07600c030350880c6d00a500940318a41d581c941c82c41c0044600140030300500707584c60f00e80001602c0d5030580500d210302500410742c0014509022490364018000d590061000900e400303c20b940c3d510400c0d02a40c001c40c0c02a2007a0f10341b18000c1445c5c5420000c0405032174042e9a00c103840d1f070f600d81d1010014541e0301c00c180d0348440306000381c9880c001003c24901c03e8200316110036420025a20703540c416520315801002ca805450041030012007000015503d5040d203a0f00c081020302d204240960741c40304c1c20f8020a04481e400505003403580015801000c05094011000748140c0e0ba0760300884036030103410001000034600f080031441c142000b16840d12446a0840310380000c504810014261034580502e240c06900501c040190303818041c800800182240d0805004480c82c5410051080750442210101141c0c0c810105007454030030111b040022078041c7c4108098103080300c01d0341c2d0300d410046040b4400c1c2c2200c000072640e0005801154001d44000589041885000d80520f003000610008550481c98 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 934606124 1250 934604874 934604897
    0x220506220204020406030b03010b060405151b03040e04210c0204050411100c0b0906010f06050a02010608190203010e1f02250303060515040e0f090109120503010810061410 75
    0x8407032006000900c4146c90004201205d0401e040c2980c03200c1a440d480783d0024841002a5103c1c03c500303c1ea10854003124507640e001c0050601184015105403e0352848081780101c2d0680020035980d0046026140840040301c032401e115951000d50b0380c6040c000f6032228030980050825400241d00b1038840c1040c019180000c1000c1f80c481d5200da8100300000b840d4581e214140840c050800f60840140b00c0502000e41c100780c140c4105030070310b20800040120003c1c00d41140d510039404403000d01403040c103445c03011484100d549803a4040d00c0050b0f11070b52800000d010740b01030010384028411a40090445540304a1401c20002c0d0010301c40c0a442a003005a6403121a5504820b07020251003600d002528a00708000e00c0742600081506140351201000240404000341c410b80d0b5010310750b10302d59000d40e0380d81443c450141c00c40ca00b000b02100c40b260384001e2100c0d0081c01850684200301c048800d10050312450401b03441d02d42c89940700e207181e4040c800e03d180c1049955403900045500340940c1844 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 934607374 1250 934606124 934606129
    0x90a020d15060e0f0303250f05070303030f05061f0309050102030c07060c08070503061311031015030b060403081e040f030201020606041e0b0118030303052205062202 73
    0x200c030111400700c1800e905805000441c3c201c40d50481110064898540201242022030399038130421040700a580030040c40440c5401c00d1080600345554406aa0000004e07e49402d60382c0d81c003a40011000700b41003074404044001588200f500c18080104059400c003c04200d00400c20a030111443c100b548070501d8074007084090000314040e21054480603969512070503c4000c4234140104e0204114181e0148608543d12005036908101c0449074041c1d504128142c10008291000c00314600810102c204805003080b41100c1d0704862001d080380d0030324540310204508807150502c0c015031045040c0401d02c08241110094020a4903000314582024090180d40d41c1c5500158007205100c10607802c180300b196814401c80340c2249080d20240481425084c08440c50014100c00324016540c031300345002c0e00c0e0320a801112551982c282502011602e07814002d01924044503161410101072224070250b425030f45840301541e807c000540826240d001c0291404195445507040311100e007582c000240e0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 934608624 1250 934607374 934607381
    0x4020f040e041b03080a0503090307140c01080a061206020706060504050c0c070e100306020a1e0228030915110102041403011503080915073503010311090a020d 70
    0x20070072940081910300d840d241989160380c0da004409a0500038031800c100081001d825143d4208841c00c0003600c9584800d030b07013440c40c01402400307000c01c1603c048808182802180038280c0c2c220030303642d01180d5519040418280d860354440c8010047c3c607065418007064555014204a62240002041e81c0390303924000f07010b981c0161a07141420340300040c0010341c580d04100c1c400050180030b001c0030991400840da14a800aa4440078040d40d030001210103002e48101580d0304629122170f440c074103031407003c140250760300d440f40c13009a90030340e00c000c075000794801c0b603c124280154140e841d80700d01070405d1200403140003142c3d0380609012003070660201c803590a0001d00017520080566120095a1004140c00d46078280286807140600324014000305008204445070080300780c0d00a04008545413507540300b4895510080c1c00000034425500d03103620390103480d410300c00340c40144e074000b003001050b8004144020311005210040c4170a01c0c01d400d0a01500165000c3c140110050800b2144913001c07094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 934609874 1250 934608624 934608629
    0x10603050d0f020f010b0105040611010e06040c1a04081e160e070f051801350105010306051813020a0b07030905010306060201272a1805040b060f04020f04 68
    0x100d07000c00e07208400b42d68104a802e40c0c02c90b10100a0000115000010b007151296000e41030402180020794005000250032100045041e1412942c1d1392401e414801041d0009004d0f4414103c0d1002c41c0441032940901600c1c180c0d08010702811761544c881340d400300d08070328803250441503004410b2000e06085500d4030000050080c03043d418070314070b0f1461000349010007000160b014480240b0040c2d2041e040d006507800c1206003800c0005043c100c0d039600300c80c0800d0700b48104c100000c0850140110800040c0c1482c100c941c203881c2840600d444800300000141c420b60300402025403000090082c1d043c0d8010112141d0000d059052010340f12000001d055000c5001a00400c2c3c0342c00c001c0044d944d00d40300b100020310f100e01c000c1003444c0303058a091054000d9048042c07003424002d1001824002c01d000c298451000c014050030700b2045045001e090188544540e09a4810840401e40105558041d45106540c0304090804580e240350400203460707002c2d1001600300d9424005085000c5221009101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 934611124 1250 934609874 934609877
    0x60f04061409010e1507051c110c15010b0a05070803100b16020f120709020d060906080d020d0801050603062710030c23090a111303060b1f0e03010603050d 68
    0x2803c58000c01e1300fa15008070620640d490114603001c12440d031340d1003410f07030b80d0014181c068140030440c035240700e201600c104003103442c00c3d0b40300140300d042c8060b00052202101c42200c110003c580c2c3c1c0c404007481e2038000c0c0c0002002160782003000364000b4014000469014212510030011662203000341c10250b0410f08042c0d400000300c1100d142513140142030340003286406c0f60180801c800d100c1e031141e1561103511804481d180c000c11160880380454000f64090440000300300101d40e950784121356500d035440d03205009802580312405c01144101e140318180c40001d000d15146840b0002400003548042c0ca0003028890f00003c44021020315803001030003512402000c61601d0f0560404420160840d80701194424000400a901d0302d480040700302c2c206001c4a441c035556a508600601501818441d003080c2c140000b101040748120301a1a016240280010480311f0310f10300901541454480005040c54003a0800c060118840d1040d40440c0c0000350000c200d00b940d03541c81504c0c19100301c0c1c2010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 934612374 1250 934611124 934611131
    0xf05160602040302040b0927012a09120507061202070b010f0f060c0b0601300f1b02060a02090103020d060e2d151512090d020a0203060f0406140901 65
    0x3040d403601c3d00501b810075204035140c01003400c2c2013004a0140c00300c1e218550307103580312400200f018a002c4d4401c81c43c3d5850925005d1103450f01d050314040005400e1503080101d40404008124200c100c00a1004158400000d0076114141982030b40c100c19042c0441e4005038007044403800044035129014001c1511641c002a09400d151040c40c40c4034158110004000000c010f160124280f4031142d0781207002070030404140d5000088901603115125915408440c026440780c400450701e500124907900c0e800800c01100f0441001002d1a079541000d960040cbe2000d000301d41c102002c0da004041c404414100149014003208158082d921503910100941140804204140c210759a0311164803045c440c43c00f4040341040e0f012001c81e82c0c007a2240e024100c0440c0140c041ea03d8011100fa800d13a131910030030707486256410307603291503000880e01e01c02c0901600500803d041c1c000210302c04001d82c000c0103404160340d03505060380040c01c003c006481c500d4981e80c400c481d1804000500e4040e108440c00407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 934613624 1250 934612374 934612379
    0xf100504171b0601060e01080a0e070b07110102010c0e010203030a0f0e01090606090506010503040f0803270a030e010f09050d1704330c0f02240d0f0c0206070f0516060204 75
    0xf414410140d0110040c00749641c01903036142c0c2d1091181d036101c4180700f80003900c04148000c1c6450951a50404207074000f0000301c040c04c2c002d8001a10100d114245d0092010801c2101c0403141c00148540e01030240c1d10a0001c02c2001e8615003010904000c0e04d070340020601e03580039820f82555980d410955002e595240107200129803809016448002820314925506080c2e0343c80350980d0960501910300000070011507510349003640c540100c5010f108400c1000104a61240c3e101c444004c1d0450111758569010801c0c4e50190032900e1120301076032500030080346004144840d203480400100c5034860b180e0a050a0400c02e01d000e0805400a0301d4040d04001d0440140442d8401c040104103a610062010441d210b0380110803074003165001c40c420005001e0741c0f01091200444206508201144091720031034010000e014000ca4056150240900028010540304948925040d9001a044003000450060080859501034001413404d00c1c6000c40c15400e4802c0328003102421954190005002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 934614874 1250 934613624 934613677
    0xc02121222080109030203090907090b0711030d030b031e1219110c060d0f090b04111011070308070c090203010b03040c06020318010e03011404060c020f0f10050417 72
    0x4110103046210004c00055007585c0f406580e900802d0905c0d4802ca018000042940d0b1040460b1f0005102e008102d54a40c4603c4c500210100340c0020300d03034020f100b40701200000314480d0095010040014001d003092460a040390140004800c9864060b03120344c0410f0510b07035000340020081881111300c01d0080904070000285009034400c2008c4890303114500750851941c400c8101d5255540fa1000000c0c020301e5603508501415022502030001e4003404d04210a0100d01495070403550300440d01c1b5401d4041d403240c140d848800b1000c2114103030740415401d100040220008081482c01401010421903607114640f0591340243c0040c1403500d004003d000801100c0d648040c09402c240c0007071420084465500d40c0307a0031182c2c0002c1c0c104580c042050030251030a6010400d40003150320b0f041350030718241c01c0c4600074000f26a80c00005100b031041c0392801c8900440c50384124000c45015040c0034440c01c00f0200a4400540155040d40040201001c02907480d0000c0001d08001c62041c0f1911411111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 934616124 1250 934614874 934614937
    0x1061e140d08430b0a0603080d020d1d07050907030e03030a0b040e0a05061005040c12020901090f0e0402090a0501060c03180f0b190c030c021212 64
    0x150340100c51a040c0d101c0000c48030016112250286500c0d21000c1e001e181080c40904856203544411280000302c840b05049150003550ba0540210481036403600c4050400c0c049541034480549072150501220549096580040c000450488004101100c55101014158180b100c1041c3c4070b45c801003040019042502c0c0481d03201150341804c1020303409407070005071244001400600703556a01c100b0042c055517030740d00c114040312181007105d00700b00303051900a503101003c0c1c400328a4603210a20000d480c1c54240961098144a99902d2941c2d90b4401d0917a03020b0340013024881e052001041000c9215030700c20410000134003445c1d00e03688142c203081c0180708480b0006402d07141c08604200040c071516030003109106026a140c9060040c0042e17915009400f410180c000e24020082038800085001c6400c01406c001860301c1c3c044400440d00340d005032250346081c80c000b800f2641880500c030140c5026041d0700360402c8400b0980d0304124282d01c90309010b030f0000c05503a800c001203908603500c10003c4803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 934617374 1250 934616124 934616159
    0x120a0b060909040b090708060c090a09020405060418060b120a050a0c1b02011404090e0f070302100507080c0106181a0306040b0414030c0c04110a2001061e 68
    0x840c1903181c0034a4602003801c0c0140100060b024030f45420200300e412008001c0400245440c005513803440c01c1071140300c0441d0344144801846404240c001003010100c07031007100c0c100c8200400360ba04d4a46407603138245e1014100c12203010700599400700040c1089003070004003100b58030035080040c18a40b40f80d150003200d00c060003044a0070b291501e242c04840d0480058600300244140784243c1c0802c40c40100c400500d10442d651980d1400700700090002e00342c2e001554940c0c1c4080a0f24002803070100c3c4a0369580c110b00c0040d5101010803001d00ac0c09001c2c00080108600800b010740c40c000d000d075815402e5402e241d203d180120414442000000d00a10411b03524041c0b402c3c080c0352000306000020307a1802c0c0544090100319800020030704000c1c81044006000060a05581d03c0748020190652586103041d801c078010381c281079070f4400c14000e11003107500391400f40c1c0300da1494100301e00301c808840005810b2852550368401004c50150300604400b03071003014070700f40c81000a040c00030001c0c56041d01c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 934618624 1250 934617374 934617379
    0xb060c070e25090509010b030618090f03120f01080a03122a120b06280302040509010803120708190c021006030606031106040501020607030b0d12080703200a0c0203010207020402120a0b 81
    0x18000d111840d501c07402c5500d20030052807803030a2b80362104e840c400d0030408594900289488000b40001102c0d0340c035510030384100c0444044220980c0d0300c00f0665140d081100300200010300004600c100114540d000e241100b03158101c00c403010b03d101c1e584a045075891840340e00400e260501c102d801d411280101400100b054500f03504002000c2d200401c9c2c000c0150060390929041440d0201075032181d8107880090000406162041d6500c8041d0703a02d035842217040040780381801000501860040c0807a03401100b401e2841011012005024002028060085411809000e6010642a48a01402c0c016501406001404519518013401c405031000c080342c3c0180307402d100c100000da801280440e4402e108d4100402c1c8a505c0310001400e0b404000c8004000d4800d0354400d64078144c0c80a100b42c0328280503101000a0706011b8201a42c1e0301400c01c031010014000c1000350181403050384a640300500c098000760414030030b513000030107176007001c0380307012190b03444004000c0450b03003170300a016074000b06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 934619874 1250 934618624 934618627
    0x1a0402030c030f101a072a0e070224040311010515030f010c080103021e0a06050c06060301090206091908030315090a4104080d0b060c070e25090509010b 67
    0x1d094904900c041444c5d07803440124004160481032201a800301d07418403460350045486004508842251700c900740c080c0c0700c800c44041000482c024000034051503c901d2000107810f8045441c41d800c030030f8001c0103104804005a82c030504007a540d0074000c0c80e010b04403000c0c0d0001460f541d00b0616103484e1040400442c1c07a0f06002c1c1480e40a9008000541541d8041d10000c10703120004500c0c02d14001c05802d210b41110680e280010b03a954050041c0c440320450605840b0319444210405090303c109032030113980030b4001c020360121440c1a00300310040700c25800d161160266102052400d60700204c03610302c100c0004500002603407500d205145d600c904100703420001908040c2c3d000c0d03524520740d0076020703000c40c5548202500385025490500d070f00c071000100520525080c50440f6081d00803044803041c090400e1003054091500c2c0c1d06840081c055240100704c140d181c42049402440090415035a440e008140400d10310706454043c0c456000c103403a1042914030f86001d011281e08143d0040000d200d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 934621124 1250 934619874 934619879
    0x5030327040c261e0c0403120203180603040b0a0b13061701060b041211060f0318071a070b1012030c0c09020a050a0c0201033b0a0309091a0402030c030f10 68
    0x2046013186000944100c0c00768030507610700c180c6500e01d2056030000b4012605050501048540c004010980c8000158400407000d040300c0621280b40002c2d100103003104843e41c00180309414640c0410038010008000d24442e13803402c0e280310100d5119410989220284d140362886084003401054000c0c1440b440c4246050310b4002e01c881080c0005000400c1854070061040c451394503a0190384400f0521810300b541c1e402c2449044080701984060a5042d004212000850000310303515280b40380a03049403146465600d55880b8400c1d4802000120a90030b405d8011401c0ca010740741d50441c05110f91103221410109081100a80030654050300c2d81e98010811510740c2a441815544440303070605105580350304c14070050f4054104005060325540018940c05e40d41548006001a12040c0c0121200341805998480e51030340503100018002c100301e071104018208603a8004405003c0113512034001400c0c00d4000740507684140c902c1200e01d5404014051907002410180b40c12586c1041d0442040d031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 934622374 1250 934621124 934621141
    0x1b0302030616020a06020307020f01150602070302010c0501091205180406050607121101021903140c03060607050a0f080408160515090f030a060915020405030327040c26 74
    0x44000b4415950098080c681480c4030303008010b108025a0701240554032442e04080095a034024002c0ac074040f5800d0002040b5510404003c10f01030350b001d5400340c0100d45c150780065628074843c03142100c1541d6101200004140070310305142081c44103584250303541c40c440c100503e181c00850100342c4121728040007000180c0d18681240c3c2c0c55a4080030721283c082420300306460300d1840c0c41e101403180d400000c0e40c41303481c228a4517000e8070040989003000f01300c41541c1380c0c0204a07411554404c006904202154141ca03008e400340c0364861140040710b40d6010301c0c2d41e6090310b4403070a1038101d0700f40101007001d11440400b8003c480390b1010b80703a001c0a20b0743c0b40c0400145c5250800c0c2451941480009440b05561103011003503180c01e40c00340444151200c1803a24800410300c003101078454529400200e10000882e000f201c0446600500039801c0424030241d5008046034000c0070f000d050315a20741264176450b83d01803145850380c140c5424090000b41520b0404500111274103059542441e0200507280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 934623624 1250 934622374 934622383
    0xc090115020d031a10020c0103060906150e12030a03150909110402090d0b1003141b012f0703140c061207050408151f0e0f040201090f09091b030203 65
    0x3498030380841c0312051100319603101300709a40101d4110804a144440031758000810b10380d40305081e41d00704201a0f4420092044850301e000e0b944800c03036640080d00c04c07140700309140d05000070010070710018080440401441c6a0100c49035002003a218203500c1000304002111100401c0b82074024800c940c0f443c0e4039103444582c804d0394548580d50114603100380ba11030642031070055a0003a582e900c0742c24841001c05d2525110b02c000c0350b240004280043c2142d401061400306c2a4031b541801100d021140c00540307044000314041c07121480310711460781c104611510b0780a0026141800f41c2021400c60410134102d040109800320349038844030640e03071141c075510b080758160003480d0f91224003600d5014048540d0f104035400f0112511810610000c040f0030348081c50300840500304034100c0e01100c4424000c14001900c07801081d003603018001a004a40d90781c5459020f48145024462140c13074210348445e0b464150040d544031960760002d030382008107502d0794042482d001340c14415418950760000799907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 934624874 1250 934623624 934623643
    0x21030c1c050f0915041706090705010c0b07140d020a0c0308062d1503070f03061e06030b0301060f06020709060b0c030304121103030a0e1504032f07080c09011502 71
    0x842d50748054541d9461160152005465206042c115007250406d6140d07403174000350b4414209005640c0001141d41c013a080c603c58656000d40b00103030a94504900760b403054100491038503a07983c10884107a03141c015100030301e00c14070242c4130203c10302000e040003800d001d0000c00260050040a941c031085010f040480483c0312465204003541100040100d001d2042c40304800c4642d079004000d02400d1a0884d50707002c03040b00c0d140d500304207040d6035023040c80c814500d00d440140c1c040c0780d03010107005040c440d8105e100084405000451007039614039400355800b516034026401a0040d20003481100f6460013903400034405102e080c1d041445a40074180c0341d22020340018000c6075655100c41d00c081c001c90005102c8901001900d483e4980802c40601901d1610030054a0b800381c0f202039a0403450040c0d416000d180c043c1c2d5228104806444200c2d00c6ca6804a89640c801c0c13000c0c6204c01041c42304111b4200078080e000b01400f09415804140300b800300040e040342107180340582e80c284c1070075400590150f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 934626124 1250 934624874 934624879
    0x40e0f0f1b0316020307050109060b0315011503020a0e0a0906150201061406090d0602030c18190e100b192025031b0305160e040221030c1c050f09 64
    0x10400c030fa0400603459403250810040c6103500302690b90b0284100e5a1002a0104050381034807001c0b6804881140791500c02d0284288055642215410b42417003a400360451000504209016081120004003030031900d61088401a441c0d200c24401c00020390100d401c901c80c0d0340000d02880f401c141d443d100943c95140c210303014070b01c0414000d021395030715040d98104903000001150349003000a2b004049500c4802040d07281c0d0140385400c2c059040032801c0c60900821031843c140c01601300100c0200d074020107407100364a044e01440124058504d078005101030000d4242e441809001400042d0a00b044881806800e072048080010f000c0404100b0803801c1c070380c0c4402e2a1050f0322115000c0e000401035040908080000d000e40c1a9022007c800141501d0249088a80f40e91606440001c1103845028403040c000100c00441c00508100004000c1c20362003190100502000290103031540d004002505009e0780180303581d20392604241125503d41d1801d2801c070345800c2c102191906ca902c2403880e50350 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 934627374 1250 934626124 934626151
    0x7291f0612091a071107060c030c020906040209040c0203070519080403060b0607060905060a0605190302011103190801031a010b04050105030910021305041503170f040e0f0f1b03 78
    0x2001c200c1e880c83c12000160300980202d04034100044001c2954018000ca801203114410000c03490718003948510f159903501d0750300e00145040303590030701440a90180c1440d07041074090052400e00d84c0c6500a508096900b68010360701c400250070101d01d48842201c90481000511540d8400b0500714000c50341070302d801c2840402c8000165004c12160701c82c0e0710015141c24a00400c4804201d0007003000c0b40103064045040c00003688034020404013025421740100042c03254401000154056000809580381600070b90b4245118881410b00b0f103041c0000c10713800200400700510130400340207005000300721501c5003c8030a6052042104640c0308038000d09040c4540840003d02a040810080060040c00c15040d521881000d01910b064200c5001d994401c504100100c0c41c0c01d0b500c0d00320300c070449400150f0300300c0900420301425010380c8150011142d05500300300c0450001c0120b4042400b82c1d030b9641c42d0801501d490303508110200c00160080203c100e5104802000d02a034030203407a0040201c0003000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 934628624 1250 934627374 934627391
    0x50909010e091213050d06021b0d050d0e120309031c021603030902031e010c0e042007140105070c20010206071413080c01020f031e07291f0612 63
    0x2041022131039000d194003000e055040001c000551300070300300401d0004080d2500000300070703842da02d480c0700c1840f0b58001042403140802403125078002c0080d4084010594951300c41e0840c444455a00450707440d1190b5000003481101130803524a1032010030340c007807804c5042c00c0409401e0002d01e1a018406010180c07644080d0007559002d01c005054100e0840c11003110000140c16940601a105560000310300581c842000e241414040c07490050300507210001541c1e41c1c181900d4050308080c20a9400ca084603a5180d11507000b440303918050007c64680e81001000c519013801c2c018658030440001d840d10441841150340c000602580198076402c2c401d950b6440c07100344140034040c003240010705200c0c0c40380001c1c0440e00403c441e01d0704d9100781e083c1ca91200201e405103a032403103070102c0610300901c0b410b80c100000ca400c5014041311841914900e0a1a17603100c0d040710b400810024500c00c08414509216680a85081c6480b40d04141d603101c025180c50254040c00b0385031440c510001c0581c450580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 934629874 1250 934628624 934628647
    0x2a0605120612060a1a030a0b0c03070c050a06052202090403030917070b01170115210204050a1e050105060f1c090c031b051f0c050706050909010e0912 66
    0x806400400b00d60031100b180c5004083c1001501071a0801124035000c3c0c00c2c0c0b03110b5400c022501194154005a00710425141c0c0510b44c80c09600c0140081c04102c2c2c40c0000000260b4107100039030825005220203d001e00307103901040c9140f4824503203400e400c0c1500040d400180c8030242c1c0303150f2041c1c050400045000700780c144181c140c8034440200c05818000141d407000c21802102c1941070b1209010b032419001e0711305130080c0c225000c0c00c3c00469503000480040060303c64600901c92101c911040504a041099020405031041600e40d9400f0688840f182000380329290b00074150480300e2032090169524060220701c86102e104130071210000d0015240c4000c026004884008013842c000c10080400c850800000c1c80405001c115042020080c40948958401c00d10394190b03440200b80c030304400001041c2c0c21608445a40e6a814042c400c8000c0000c03502c140044401040d00d41c0b41c650b42c800c5c10008000142605070085141c100369a01130080d0b00e00001f03030301003098505a1070716a5441690380e2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 934631124 1250 934629874 934629889
    0x60a05070f0c0609240b0f0a0e0c0d060b0a0806030705012c1c0203060906040c0b0901020f0106230a180b0a0905070507031704050604080d020d02072a06051206 70
    0x130b015100c1d802c0500280b03409a107402445c118800c1c915410043c0b41c044004018800701c8120400d076200242803c2400b444d18103207140303904001400c034186d10300341d01c180e542025101c2d180c2c02081940404501802002e41210302d040c0c1c402c0d8120080d00399281448006048200034030280c407081044600802c81c0480c101d22074850400e030051070141c48003003400030120781c850b001e00100d0080c040c0401290b41d4a000007603030703402513612002488072141018011500382d0050070710141144104482420645400e214401c0906081d0f07400c125401138170162a02c040f00440301140c080c8115140400400b9440c01040701d0545004001099812104002a4090b41590841d9809a20301018400d8071a0090014640503100e51502201c0090020355030f282c0d8001103c0203451908003e000400140c0074000500581e840c6080040c2400100c549403012604500003c8414080c1d00901d04401d41000100f945801204101007046034103000703008141d8052509080071580c1e0400114090707942e001d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 934632374 1250 934631124 934631141
    0x82d0a0507052511061603120b1e09070215221a07090f061b05010204080a0f0b090102041503090602041206020d050907061709010e060702070602060a05070f0c06 71
    0x810071a2020a2910107180c01e5540b620100c130303228044901c682450804c48103540c00c00c0d120040a100e4034407652400c0d201c1c00c411200030400c036541c8201c051219910000e45a0103600c80542403aaa103010304140040d412001d408a401d541c00606140c005200703034103070917500002e003940381c59401800f5070400305500b00010700100900400324884c40785c03500744060584207482c241d0f512803016641d0b0091600305500341c0100c200180585902d5489440c010800c4220300784160300041c0760036503c00700f460030300d00381c0c0d10100d40c03801c01451410180700d01e141c80c250304104100c0007140b80500e0710103640d0000d0000c106000526440d000014184042c43d03040c0ca0043c038501d030382c5458100325031614030001e41c02092030980c814035100105032200740c001031030400d58107503440b202d0380c0011298a1681444006290440a43d215a85806501c1003800607a010704482e8000300000c0c3c0c10700f00c010b4100710009000691651900741045003081c0d0100304201e090702d4505240c040300280f0304254000e02000c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 934633624 1250 934632374 934632397
    0x6140f07080a091413150f0603020a0e030105061818120421020f011b05010c08310206180409080a09061b06050c19082d0a050705 57
    0xc15628180900328004010403103103079850799203091316144d0400340884040c413001c0c1c00c8807207071449242e400a1544050b541d9403500c0401d46c00c0c980d41d0060350503154150b4005000182c0c020400401c85604090b405005c544100c009200610300040814080702080042e81011825071000c5a803004d42c428141d001c0c4d40c000001d0300c03003107414007682c40910b600c20711031014010013001310400e0040d0100010316850f940105038000f0184664011a01480c01c64003001021542211030300010b4400d1107840c10004164030340c15201d250669004038a4036900314501d42108003007403000700f0041c2001c3c01c0180340d0381c1180c109498089050a8002c125610148507804c113140480d50b0f0b0500c83c1182c05040c1c808400d5846010841c0c031400e00700d9500c4a88941c2480f0001d0501e014800508150070555000300355606440c00c01c2003910400810510110710700740850307040d42c140002241000c1013074560040d02004080c10840004055107840703802040b0a4210703942d40d001c50f960f41d106204131605035a95 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 934634874 1250 934633624 934633627
    0x1005010b070b0c1c15080114012606041b0e04050c01080a0e0f0601051021020901020c0901090e0105060904030e0904050c03070605120610091502100f09050606120706140f 75
    0x1404a4030040c040401c0190300f203090b80c840000d1b200414000c800c1040c510001c20034550346440e04012000b100d01408030542294000c2d4011845010840305104a0040585044581005400c80c10002941c1c000661901100382040042080010321101c02c0030280b070030807440d64900e071080d0000c10501d03012501c41c0c0a41124011203010004003e0b041e40c90884404000b404054025680345a22000e01c080580040704192414221030b4081c0005401c1030040c1c8000721207540009458202c245c201c1c0d03001d40d41e1000e681c51266401d03c14942d01800580d00d00340c0606103901d02918212135420140d00c0b801242c0000f03020004180805000603001500f02d50f0580c1c0c880e00c020b84983c1209840c00034403144140002d0342e52906008082c003040d0b00307495080ea03c074103020b0b21809900140000c5400e52085040305400b5581611a4144000000c1781c0011840080e150150500314041e1400b1b00c994a80d540c40b0080c83c202140c030404a0f015810310701a9641198004100c50240b1410725002070030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 934636124 1250 934634874 934634917
    0x30411060d0f020a030b030f3318010c050a2c0405090d1b02010915021c1d010807080a090c030506042603040b010303050f090d06020a021005010b070b0c 67
    0x240e074001d01300701203280c0c034144126290f000502d5554070000800c00035039401507040c45a0b50000c080c440d180510318500c850703d0710b0001c091800801c441a9200040c0c104001d441408251080c402d0441100051810b1031420a6a03180108580900140130450000500890300c0c045400081a040000c01074004c0c003907460141d42240c2c0390503103649450045140c14154000711088403160364a140e9050f180c0c443d81034205810b603150b5030204840325056104a00c8a940351002c03a1500c41c1c08021607503903018502c011222008191a03100f20542c0c140000b070700c01d000d1042c3c0c1000ba0a0341c0700400c0391b800180502c480c00c200c40c41c2440c1e940b014041d0b001c4d801c00d000c01d0210320b200c05180c6404401101c10500391000c0214598401101c01405060b03c84006100281c1700d400105451000f6404007810610b04d800003c00039251500d00304d5034680d0026804450030b40500c421822010413080070403807985001d41841d0f082c820100c0050410b003e81001405028021040d034604042032410f115030480b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 934637374 1250 934636124 934636151
    0xa05070e092514090c0a0525050303160318060b0312041d13050309091026011a03120a02070f0306020a090b07030f110f0a031d0411030411060d 63
    0x615006548500c005845848020b00300410005d0045c10080c1840d86002403200040310382d80c0040e130080302c800040360780e12110b6112602404042c540540c0166540342070080391707500820710343c050700014107041c001500c0e00399154010104510350004408141141124002414030307003468005041980086404a5200f101c5803601e01984004440018552151808180c00c8884040014100c3e40100a40700d402d003800d003101c6070040e2400025503900c035154006da00d90541d10581c80c24448440702c50a040e048001d008003240c403403002510f102920901d4000c00d40b140c100040750910131b0400a00e80c0580ca01c2004000010302c600701089402a49a203484806503201c0d0540900247e5203800204400f1050012140020781c5511803680c1505025025580184c115070800310074001c1001301c0014010910181507081e120703039900c642480c605451b164000c00700c2c0b0a0180140d1920644000c01c60100301142e070015007049900d5141000040060454030030303410540410f50a002041d032001d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 934638624 1250 934637374 934637443
    0x80a020c0313050a06030506130908040506030a09032c0103050903310801050106091502070801050a0905070b07020d081b03130306290f0102010f060f170a05070e09 72
    0x88108807a0100b890365114401c40660f482501e08c503510043c036181c140c812030200c1c0e0000d06007602c201401c600b400c0e5038200040e029042142d800700c5858a41c148042050b9200111004001c00c018400c1075141e05500352120201c45491050b042c1a51800440c24071501041514140c907008605d49000d40c6160412140e00013882c0d01d000864040d10501041e07400c0c060003100c0c10f94246070303a143c0034203141001c08000e001203860b030310065000c0d20b14085042c1e542802590b114074000705000c501300d44a860018034040b000e510800072400c0512030840166601d080e003005441c3c0100303940e0344690880704008980d00ca2090f150f80340b4840000d8011018010101c00c00840780079440400400458583c100e1181c07000c1e02032100d14564050b00382c40c01e841e00c40e61400c0c0341103041c1700000d0071904610325003003150030b990412000c3c0212900700704015070010003180080501c1c1e60180c40429559503800b070b035555881c007444120701144030001d0560807040040040180b424060b68a040d02c03042d8411008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 934639874 1250 934638624 934638629
    0x601060f0909060b1c0915061403011e230412030c02010507120c0207230f010f050421060f060602010b01020f0604020d1e150f06080a03080a020c0313 66
    0x1007016070000240d03455692041d04220b680f0460074920307141c0320101444004200d03505900701180c1e00c01c01a4003103035203c041d0003031030b002e04040015142e041200c04103030107590071000c61090381000000d40c0d01384140094016003042e141c101080140a0424038101c035684421b154100c1c01d051000c00040c07010001e40502062186e441c100100c02c940a012403d80320111890804120b107204074540f90740b900d60004a0825091045c0c039006e64032041c00468032860781e4505091b101e40701e40609047c1c5071003641081c03842005d003000d007550743d40800047c1c0345020b80e1050290a13600701c9480030f80c850ac111501c1e00300d10b90246040141185c031595220040183c0e0003000010742c644180d0060a5000145014031408078100901c80d9a45550030448032804100c01115030020802440c0c1d8140c40060720404102d02c82c1d50b00c1d848040380014000122806458001c8401d810030b4801c0005503408100154025050311345500a683e8194000c006882010014010f503c000641c409480c101240c5c40d405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 934641124 1250 934639874 934639877
    0xf0a0305060d050c0108040309170a060507020a0b041e29011e1e0f0605040e0a090b0103060513080a1805090c03060d14070f090f09111009080601060f 66
    0x2007611100c0900140c1e10489000809070350107048036403201d40c091140341d64014441c0c07608103081912065099100380070900c0b030315800d1780810380c00e00030007945000b0180e029981c1e01c000e0204011503280c0e00c0c000d2001900c042e20031020360a00b07840241c1d46040d4041c41603006500341044504181e00380c4250295500c40d130b02c01400010002c42c52000d04500000300b040780c0c0c2c41c55009103050009240d00074099090740307100d882446100050301c02c5910441c0006002c1500c90b5500c0303030701d044540020403038000c00742c280031490a1507107000205c0544015054235048400040c1560782e0040384500350700712a030058502e00021a05410166210380c101c0820480c00d51032900c4980d44100f804107600b01a984280070000c10b0000ce032040c02c0c42000f55850a000300d81e52a0700c04601d402d06410070307215400c0784000d0403044074180705540260044e80050b00c1100e43c1008948070076250f031108110711814042c450548100140038143c460881f00d005080061700341c5d03910b03581d1020060160640d0410600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 934642374 1250 934641124 934641131
    0x7080f12060906090c090406030b04030207030b010b0c030f0a021510050f010e0f010f02100c030c0e032b0e03030c01090506070219080a03020c1c030f1a04050406060b0f0a03 76
    0x1c101d810a02d1100d4028030001c3c198102907241d1004803100c94100e070000390340095a6a0300000480da54040c2507018a0080d0041c1a03001d041d420941407070071050700118460b92003002042907000d000803c5070a04611680d40c242c5407112000105d0604c00a0300110060090b258203126684090703007003850848078200da141031070840e40b40055922106082507103601c0002003c5101c01c0b54052010b40309128900d106584d501401216000c085a115080c5180001d03903c082c05840290884681c1c85408811002882e280001f000030340b600502c130100046003224407107070b0b0080c0c680c09409459244400202542d403540064090103008140060301640c8ca44544408503003210300214840184a007010020807000c141a1a00e1800e540003007140c00416608000b403200700311040c8410681c00c07210031f405c0e20a4000c540c0e0005c0c103442c0b91080424010b4503141c00e407401903440000810070500d00361004211a9101e0404400800d89a0710440302e02c170002079005800091140141f01ca000f0585041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 934643624 1250 934642374 934642381
    0x703200d06060510141801090e0f07020d080c19050910020a0215090918150115090522110c0303011d09060c0f0d091b08070b03091f0207080f12 63
    0x440d00007526030303261821450100086d00c0441c1c000c180d06150400181001002569100c641c01605c4200f05d0315080c031040b0500501507015070500c03400000541030b1601e02550b0815a020302030a00c034541303e04801070000010860002d0240c000d40ba00300030010403803543e103411441c019450b00c044e81400c9106100b25074104d5013086059041c0c0e240323100064003c600039680c40384540e65940d001e40c01c4040500c00c4050101400300707003440c000d002e0040306040f000e509000000150607400d21f40c00c074611500c900051200d16011036040000c0041e01d008004c00c0c42c90b20a01401c000c0c1c1300d6060500082c1c040000041808030030883e00711840608958400741596440c25440d4480b18260360f50003030200c04005002d0310400035005800d02e40c0f03a02c0303070006603a80c0c00d41e5205c91042000c1e144001a1483d4201048480410701481000b0030510341240d1030b620f40b902d145625031508841c600e0724800040a6058070001700e0741580e0030320343d112001c02e69070240090018016003090f00720400c442c1015001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 934644874 1250 934643624 934643627
    0x12a02010f090f150213030809030607030e0607030908070506040b160c0803040303110d0e06180a11060c0708060c13050f0f06030613050c030901060f06020703200d06060510 76
    0x4200c00150800b410810f066115074492452100305140b110001d0b4080c405481401c0742c041c81c0200a43c410f1110950303900b040340c01d01d410140001c1406060519180400052000100c5d03103a503c01081d103400a04003c2510700350345180a03240c0090440d1164804000c01c01c070b44103070301e80d0103848809244400e10105007401c50701030840e194024101c82e030600100717001070f010b40c002014400211880d103040103010b0b0104801c40305501d801000d6503114409008140c00f405000f03050313000e006c501a103c01c005c1c40d00c45e039044a60041029005100c0020407a114400a10000c4c01800c125001d0f902c040c00e02da5080d02d4250401d000401190402060004d10362401ca0300da4400742c00054080880c81e6450000c0215640000740100d400c0f101000502d000110301d8455188644036100a154403410003108090860b11142c00c0410581000704041c001e03142c002604c0b500f140d502070030320340d02005110b80791341c1c41c1c480507054150010201c002440801c4400c0c2c1203542a1603003035840f0400100d08100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 934646124 1250 934644874 934644881
    0x10906111e03010b120709080a060906050a1815020c0f0c0f0a061b0201270f05060c15040206091e03010e03090105040b07020406050d29010509060111012a02010f 71
    0x245109202081028480303e0544010560b48001b041c14082d0309566070300307056400c1240642044840a035a0900030040001c141301c0c89801ca103400f841041102011361190200c4076030b075080504542c003031000c940e0242d00c503a01102d10109504054400c2c440d0110700aa56950710104800e105200c0c42e4900451350034080046170448202d5942d401540a41c0f0914040c1084100703000c1c0d04010704400100744144030407044450a0800e101c8400e145032801c4118401c004443d00000d00c1500208502207107054001208903a4203048040140c0719115407000503000d20442d0310702c6801c140c8401094501d41c4513040c00b10720790708003038000740700c0c0c04008080c43e52a4443c00e84054041402480240040790004020b00384552005c0c0c400036199480b08001068a4036a00701190000461030300b580581c130500301088022550039001c25069418200040c03100d6a0050450741009071030441460160002d42040d50546d00030501d0540440c0d4010501803682050030300700c0007540c2043c05d0031011840511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 934647374 1250 934646124 934646129
    0xc07060f0c0b040201090b031006080c0702060405131e0e06060901031e030c06020c061614090607060b0a030b1008121209070e0108031305010813020f03010906111e0301 74
    0x945403200300311140d540c1d03002004042e105030b04106c18044049a49582080103501503096402c8841130146488001888090010704c0d91506a0043c004900161510710075107080c0c54085400c034890982c407034141c0c2d0040403400d08a01c02d80b1007a96500d145100107a0003410841c003140107039a41d0b03a442c0070030301c452840300784801481f1254507400c40b07804031010000e101d800c51017031400807000315950300e600f8280d030040c0c40783c50550380041040c8412040c001d90811040c950b1804c02c1081c2000c0e000c009800390082145450107203100060702030070001075a0001020780c2000380307048490354907070410030702e0a1021034020005500e230900209180c2400617104082180e0030384150700e4407001030f10310005007001825070000b6229851010034400391440c2d50304d003c0d044030001191602041e038000c44810400d640b000b03045c880c1c4402800b00300048203100340b4000303805440c003400f0120b2000c0424018412040080e00151404605001e4007415000800802e281454070140c072400f15070151416100a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 934648624 1250 934647374 934647377
    0x501080c070c150309020604031407120305030703050714070b071404030b150303121302040c0809100b06090a03060912020102160605220b0907091b0e03030403170c07060f 75
    0x341c0c001c103e0220302009005900003149070200b8a013401e0380c045841d64000360002c85402c20b102c841d00d0000c0c8400c002440040192504060100c00c07651070142c40c138400a0316540c00c15480d0710001e000180500c40c0404003200c501541e641c4c491071420003100c840c20a40344980000e400410366803a41c0c1c071540c1505c007500e80004844140340c0700e40d005021018042d90080f5010300051000f03029249450507464466051060260920305092040000716040541032406215552040c00320107580050903091b1b8030710950002849102a0000600c603018441c0450b078003a62414012041289503000140080d201c0c1c5a0200320040021080e4281d01907002008c9803450f11703030f500700e01050b80c603045031340c112080500241120109500c0892212034544007a21002025030604c1615141080480020f124005040140805c2c100104640110bc0a00c8000704400245000c107907660610844008507400000c0d20f00c04a03403150940c3c01c6421440d0485c5080c06003001c00143c20f405a070043d01070318480d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 934649874 1250 934648624 934648643
    0xa050603010c1d04060302040204060207080c010801030c0e090f0610060207051e0d1406010306021902010618090519030c050706030b300d1206051210200f040501080c07 74
    0x500321034003c00115011a154001e03281c0d00c2c000050b0322075100030b00c06007000754040c20405040c0307042e1618020304250705078108000400100040341404034140242ca0100507181400d4407102030451034030481b5580c0040a000344424450311482026410b01120004d8090fa503c2a40d0340b01048090303441c01c0c80c1c824507104030003070300030b201e252003005115018890007486071081440d5080919140302608101e40b4203600003503001440406201c800d600300058402841120300f810146200700c001040031400c03142d2140d000e0810401c4c180300071001d51902403907171207840000e81802440c96580d5041031f1200d0007074040108040e0310a0162141c940c1c1c01400100c61740c80c81e88405804c01d01c2d440310300d40742c02c2e54900c680d00ca4120103124141203040c8603583c00b048540443c0182d41100c5095004501c900c07041c2c2c51a404070600810700801d0031110500001d0600e90042c6200004d0740b269040c0c58844500255803580451031802a101340c81085c1e0701c4020980d150b1071240c08602c41d00001621a100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 934651124 1250 934649874 934649897
    0x50109051215040c0f0f050f04090c03380a140f340c1b050d29180c0d11040519090c05090603030f070f020102190b0a050603010c 57
    0xc04421960018070034060070404a40d40e048030301c1c0440598000c24808050260304011f00d1500850b141c02101048904100003c8680e59074402501c042c03200030007161400c1c1c4070040d110980c1d00c4c03d0703010022400b80001050f089000a055441e81100e005403c5450b00214000001c040c4407202d00c207400e500c000c0c1d8101c2e1503040702c11030b1600700280400c0c2d1070200c00c8610440401c1101c0c0e40e14603000740d515510408200c920b03002480401260b004614841b08101c10001a550804900c2c0c0346500144000f2007040d190440601c0c2c4103a80954400300c0d09100c080c8801d1001c00f042d46c01c1c40d90094002e5420b514004810011046501175000c0c2c0840c0118601a0300f600d0654011034200c91135110208102402041c00d07020b0301c0760618142c480c0c00403041c1c101b00909068180b070354024411030180d032500400035440c1c640c500a00c2005841d030f4004804150131a4000c210ba6920070154031420b419034040c602c1c000c55a0002160038486850401c2c02040240c2814026558949000c0d120050041e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 934652374 1250 934651124 934651153
    0x80105130f0b09100f1d0c01090303050c1009050609010b1f050a0e030d0c0303050901140103080714010524030f1e010f140702161a032502070501090512 67
    0x1d4480d02c0c042c001d0081415540c0c0c031520509240102800300402c5e0980d020006c2043c0d02035600144415801000c1400042d03a8080d400324140d0f039040c10600d840b941e00c001070500e01110100044000c5291401070b200340b02c0000740030361080780104000d0002800d142e090103074042c44480b006159012059607078081c14040d20103040f41d81d621349440404581ca04000a1420078034802030130104038090150700074150b250190b141e02492110083c0719034108500c00905041052001030401000820590100031a08103801c0c2c10a18280090045040c4401480c400ba40c40800d02080c0400810407034038a41030105008540600c3d00b006000042c1c0b20306d15482035018181c0003d54155620550031150710000e01ca030f50310310034114619003018548050080d01d03156401c02103040710000300008100c90070030b50301d0000888041c114026226203d10405c80c030f003008103804154508200c0c200914800781d00291100031030f40242d0768088070640d204240300ca00c10700c100ca1400542c00039110080e400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 934653624 1250 934652374 934652393
    0x20f01030509010e0105100f0b030c0f0715060e190c020c040c0309140307030906094e0201030605010e031b06090a0314120c0a02130608030d0501080105130f 69
    0x2001d5400444c1c1c2994002c0030900311442140d80316840e40841106000140050303803004040d1450b620f00e43c0c9541403540801c1e0395801000e104c100070410000d500307000c001c40c0d480e11f81e64080c02e0010910a4649540404a14400854140c0c0e550191440f10403602510340c091003030700030b20940180c12803084d04000e0101074181c400c580c00906490701503650004440300d407010490039000010f1616000305140003804105c0c0d40d480002001400d401c1480103d00850315811828003240c02c0d10310f200202c20151400700c06451080c01240c82d14442d0001e61b0201c5281080164400d1707030200b00320741d100c0c07006641c0c20741e4058002d0b406900c0403031245c243c0800c00045420b484401480542009002400655150030301c0c0c00c100d13941d42d000d4850704000081088000074011543d68004d00b0403035501281c0c1d5840c58804406485a001a004200038240c5035204c0c9003d4490242030ba9664101804418060903003849410415031138003001440c510808084001c0e05540301e854220810f0b5181c4071003c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 934654874 1250 934653624 934653631
    0xc0a170a0804033207020a0e0403080c0a020c120a0b010e0c2a010e0f070602070b0304111302040b0901121a0607030e0402070c081905030a03110903010e070e0a09020f010305 76
    0x1000c0041541c14803890800050114010b04130400d03690300960b1060041d107198607809841080c51072014000000d405c0002035500041403003c103038490405441c200d1404803e084140e030810407011182458900200380d00c1d187c24000c2690460384e9a9694082c800c5040440f09403122440601484041c041081000861902d0010f40c400e007100c607514602c1d0854040c0004050664440c2d107240301200030134070281c00201000c2c0050301c05103150014600301484014401050740004819034102982c440744d8008a902520304215110390700e40c4200240c07a407000102c0ba01107442c88400300708030748260240c05035080d81403000f104201d070742d00140019074201d28402c43c14403c08005115030364990b407002d0004140203285100342c65281c41e142c1800d22a02a000403c40e1450120090100c0d0f000030480d4000302141c50001080003c0c401c10322458058044119495401c00840a15440703001981c9400c1e03401e443c4400089444081d1030384e04460614400030342201040000104660113903000950 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 934656124 1250 934654874 934654907
    0x1406211606030509210a0503041a0708270c04051e090604020a090b100f02030c07141009120206070c182705070b03040204110c0a170a080403 62
    0x24102403010300c0c851100c140e4018400203582c1d14200040300100f00505504404840005034544181c0d00c034140390ba01c207400c14202809000401b0038200b01c080014503030798055500c0c9140e1103042018000b01043c1069801e4814484504060000c0645202c640d588403520640100780310184141800302400d801001140054803d0045000004209209520a89014019010502d040c1c410044d00e03840a403c0030410720300d04120380c2420307150030a000244070644e007441c0d0409000108100d20358410032074a034034540550000010f580e9402ea5070018403d108581600310060b028408031a11240c0c0e11034007510b640e96030b4200c405410100010b00056010740c600e02000c03911600361a1101e65034a0703114040079503078640414058041c030400c003617012300c4890700c0d1103286a41e100c4940d1910540140a9401e1000001c00c0456446901c00c0c18040e040c61100703921440c0f603880c0a5159503000c00180d6400340611030381e44c11886650208e030b481c240152100701c699101d82d04c048801d04107056000b01d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 934657374 1250 934656124 934656133
    0x40303020408030a0c021f05030f1b070c030b1e07050a020102300f1302040b06071a0702070501031401090203060a03060204090207020f0a060212070804150e0301140621 74
    0x2e540c6078140000e00c40416940c030354140400c81032060020303140c1400340380d804100d5190441c42034240e02034112038100454180c2c000c0c1c0e03511024641c188822181038161450b00d4001001420022640040401c42c1d014000703480f255a140c2c4100b80856030169503250210300a80c0004410300c1c0980c002c0c02e100c03403e0744001424282040803406055040b03805401e55010307d002401d42243d02e034480c40307901c4607500d407003000c05043c0440c01d40122154824007c3c8500d071280d501c6070482e100c1d4070590380803075000310f03611a00c00046501c5584001d001e82d448001805034000208440d4042d02401c0350341440840d00c0590f50386030010040094201030b180380c0e8013038003500d4008003007400c60000c1d10280000d15401641c030f0000f0f1040001000e14900124010300c61032104110141e00400d810204150101e009941d070301551a20300990b10441c0c0004107250080c5400d41e0440c0e42c004c40401003020190000c10019254803081c103c021001c450301640a20768000305003601d4918000740301400c0c141d00c21074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 934658624 1250 934657374 934657379
    0x6122f091302060a0801172122150f030902030a030e0105070c091e09050601030b190e031b010e4804110309070504090f080d0504050106080d12050403030204 69
    0x82c0c110380c4190342200003d503040c00180400700c41d0040b425101d461f458014032507500c001104440e558910000395044071008603111102d0906009400002403600c10490b61070740c2c079080c0c200e80c0040e0f140000d0000440185100d220315019100741d160841e001002030140b8095a9421120a01410700070350400c02c0a10084c0d0008001c218020080d00d41311030041420900c440012080c514020641c030701e2242480312200104102203021819039400c250061910354a07900c0000d0000c08040004081c54900419880300d4030b404406046e0800d03c0001c0d451840c03a440d403607103082c2c40221003e8021500a41c001140c20130b03000303034490b041799001c000c030554951141c0c40000794412526008400c90700524078045992508e40301702a4620200700c2070a06508101c0e08450f41d502c0a4094180125510f403404014411840245003603241c1c49001d281c9d0310310801d6051000340c0401e0381c0445040d801c02e1400b10f61052b010a6652a64107140da0304c0e0151245010300d0409444090b0040e400d02d5800c0001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 934659874 1250 934658624 934658629
    0xd0b0109120506061216030b06060405060f071b051f0e030106031103060601020304150f0e040603030e01080a020906070b0a06120c03030f020313030210110106122f091302 75
    0x1c0e440600540141129150460a00c1011210340100a10a421581040200e14090036400c004e07690810360034022652000041a4644500d820182c1d0124022400040c2901c06030006c00603a842030031508a0703c5492a56541c100566009a903481111903031100541c0c40984d101d030618400c0380c600b000c0300707030980000720b07085030110781003030715034600b00744a03000f00d800c3c10000d068012100b84015440d09241c0304220154180c0340e4075203400c0060030021100c6551207440500041d8a004000300001503032460041d00238090106203601040c80107000030200146442911103100c00600380c1440c080301540c9205a1200041506a03034983d15080810041d40030a28940e81c83e100e240000501810341c10701070003004040032140210352080160040005107210132204403507040e5000c50122044071400c2e1140c4e07221400c403004941c64001d000035071303490072100481000d00070640780138152130400c82000d101c9061003800815100c2c8040c0070130f090900b60706180d03000b00c504900c06052000c9900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 934661124 1250 934659874 934659899
    0xf0204020c0c03070506031012030203220602010f0c02061306090f05030307120b010f0521070f0311030606070b105103020a030609050405030a03050603060c0d0b0109 73
    0x344680c4076807266804580078142000134402418044074424191b182c4115884c3c08413840340980f0141580d007a041c42c0405000b0003e41e0001c100f1059008100701d0342d24220304140245215200056017001104e8052409500c10540f060800340c0c050314040c0e032068401d02804130640801c40b49c02d80e4800341c420100d1040d070581c4d214103128102941d07580c2800741000700005041c6240c0c1082d1454040c000c601c60380c002800200d8000c9130300f01240c907580d02e8140700c449940d02520b40505a1640410020407580c03218040c010a412510208134407000071981c40e003240011281070360400801c100303241c00f0440400710254410b00ba002e0f21179010761221650021941100405140051481c0141d401c40d08801340b04e8181099116111001d98002c0882c403a020a44407203060516a0000e15000c0c40e503c6900240064100c00500740b10a041a1030300d1552a03000e55401070002e45080042038043c03502048440c051000c2030459401c15103e001010000c1803010b041c2c03414007062000004150300ca041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 934662374 1250 934661124 934661137
    0x90a02041a030607090b070204051b0703080612010e15060a150e09060f01051c02301005060f160c09021201080d0f050304110a030b090c0307050105040b070f020402 72
    0x300901c00a031941018146404406031032003062011140701070041381c4013001520006601103e0100d09a01d82030102640085480d161942c0702c14000b50748011705411403111805a2416500207184200c09800d00307080b038000301c4032882d540d0006072000303400c20f0706241501e811500040050b00c03c140d40e02940d0513104c41215021000c14403078010b0399614a0711040346540444103891004040c511100000c10724440c0c440035a404d030304100110b8000d4142d60b0b065403585608170903071212008001c0071441d20782d00d841c2e84140300f80c09924001600e000a0a02c1881101d43c042c1c0311a0911042c0d80a64096802000518100e003105416903004500ca84c1d031400000d00c0188030060b92141e0300a540501404142c114500503072010005541c22544100c0c685600c41251401540300e8a682c5480c0444e000000a07090b0700650801001c4144414103007000d000340310810454404004c4182810b03200c00c058440c0a01041c01408100032116009000741030061140e082d5101c001115030000b012a003280 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 934663624 1250 934662374 934662401
    0x8060f0904051609060f0608070903020307120605060d0c03030f1806050a0e0a18020c0c03340819030314270109020604120f05030c060a181a090a0204 66
    0x10000200500014843d03080606196041400024244040c0d4401d540041c070644040140c0e940000351286d01c030f000800d01450f8001c09807024260b0300c45100310b034088a07410a80d14140741a0120707083c1e2410010a5403480d9118481481e0545076440c1924040e418840030070620107107580b0307071a0f6102d44441c101e01504264407030070788070319407800000c01d41034005130150b0013061603030400d1000e008051909111030564000140ea00c02c02024110300380380102e8041074040c0f04e40780da14610070464501c110031211400300080d19000e00d2040b44540c41c803284c40384203c01d420038518103003d48090f00803100030a00904000c0f69191f41c0c3e65050109100c120f0344403825400c96840302041401c0501c454081501c020000d200d8106103800054140c4603c0c81001903140e2444109403c200e021268000c9054010050b292100b0f009041c4544580b0101c40c040280d078946a110b205103180586d6400f40d041e00310902d50350311502c0031241540d41001130111302145c401c03490780030016a01ca00a400c07101401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 934664874 1250 934663624 934663633
    0x121009050a14011406100c051002030109320c1210080d091a090a0503060c09090c0304050c0d0303150828021f030207020d05031201061e08060f090405 66
    0x440c1044550550121032441c5241d0400780b04d07640d10705020f81040c1d00302c841104c1c0d914111751102030039a202c06840c0c10041c5580500000c60f201e01c0c45681c01345048805e001028071402407804042c400c800b905801c00301c2046201000216544045440180d0104001b81014601000c8499000b01d00d0012107261001c9910541c09208030007050002e203c004c0a03608000e0b44180c2440c10700c041010701b19040d18404040420820746550f6421485401848050203403181d5041043d01c80301554071502c4258002c0c4540004254901d041c1c008481c03240c2c0d0010017614904110350200110868805029010540c442c124241c2c068504c0f60703010010941746004120000700e049e0941e4107404190044500201c00ca0b600c0000358450b61160b040828105c2d44d40298402c0c4164242c0c001d0040b48806500010180031807801c01070004003c061f4a2080b450454a0b607984200c1102e072000f0342c444008061900040380c41e05240282a441d0b088031006003025200700300180803605900c1c04840c0be83e1789900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 934666124 1250 934664874 934664893
    0x609020c0a060b03030c15060a03120207080d080c07060506150c0d181202011115040c03051621050c06070b040c0b0a05070b07030b0315012d0512100905 67
    0x144540b00300000184e000e1420013070145941500c0f4400032098000424400000072800e40d0395030298000356500001306082c0403a00800259646054080e40c0b8007072180007040c6400303034015065240711709030707080e101481c00402d941d0b00c00c080c1c1800307010141c020f1200050751081c183d50b14094a4202003140c020411140400c0380101484010404140c201d0070111007480a031103010300d102e04054083c01e003034040c4054080d4a614001d115a18548103440800c140010046619940d030100da000d0000c031005c92a00d034200c0f40020003a071045540c000094105182c0c407a40d444040c4500e64014000d85103000303040c901280081d440400f00320b464000f041e08000400c07119851f2503025103045c4003010b003060301d00040605144100364001e03114034901c4001545541c4207400c0701c8200d50007d001d0f20855580c540d01c424800a0a0141d504420b0614005034410b905481c081c400c215500c1c50350703064240c5400c0c240803c2128550001c50725006d0041a02e003813010500420200300c2c07058008040604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 934667374 1250 934666124 934666133
    0x10506040f050f010501030e1c05090108070f0c03180f03060b180702060a050417070f0605070507020d0f05121204051e1c050d06080303010e01120b190609020c0a 71
    0x1071208100e04a1545402e0602c8100070310b103111281901c1c000e003400500c0192642c0d81d01c0c60810300c1d0000c09803c001d083c1d1a002142c1c0c2c4000130f4401000207032621101522100000e840354107001c86104d00080c400c141d1040400d100f1100b00b19401e55282c10450040e0b01c401d003540300186160401e480791911681c1c0d04001e403c1035800d40304035004201001d0303130908008100a45420340640700305007254846000c2400c0c0071074203480d58131400340f0011203039946020385000014500b210906449452522000941c458050021900d005600074500e41c4900d43c1650f6102206030004004e480600c078045420420040c1e5400420006015000c94401ca151034580700b450300640c80c3c1c040f518448080142c214500000803044003860302402c07010b03401054808200c5490090901041045003480800503410001200840c1610301c03c110f0b43d41180e80318682d05512440819004048103040c1c8005017401600c00292040c111108401080c0f05550707000880a076048a010480b071a00700c000141c0411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 934668624 1250 934667374 934667381
    0xc080f10090222122a0b030412110c1302031819152007151b020615030a1e0203070b031f1a09030a08190801080a0507050d050309100201050604 63
    0xc0000d4200c00304c4261035545c0d031743c0621400d0718840420301c1c004201d201c0181c00b42c40700340b40a403000c540c100e600c0b803610b070600c03041b2400c04a0b86800441da0302001c60a10f200c02180c002c583d003801800440140c190020b00d040203500c01046842d05807280000d20210180078002c40000e0301c4d20404001015080b800c00541000720a40c8842400345080340e03420b5071b044000603d104140306003030103e46a88285c108440e20030450742c185d102c024580220780d45031000c0120458125070465007152101e948400b0003d42ca40400c00845500d94843d0064200040340f01f100c4545240d5903d0008202c0f581070b9012034a0520544c0242002c0c4201108000c1c140701ca0b200c843e041600c0784030488011520707220101c0328110003841c4154214400240508443c3c40400150810503480702d03040f035650031281032a4802c400b00c1210f040c00038040300c0000820410000d5109522500710740907080032842d100812a03041080101111140028403500c50f241e0745010104076100e6a40c0c0000c507041c6000010041107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 934669874 1250 934668624 934668629
    0x603080405091f0504020d0f090303050912070f1b030c030b04110607030f270e06040e12030a18050f0601051f0c020607140f0f010f0c080f10090222 65
    0xc1000c1d020500107283c0740c412104040303400965005035601d1214000c2e4021b040400d024015840c106a120010140e05500103849208035009459410492024004817486882d40103403400340b1008500002c58001034101c1442c503107074005150042c1d070340d694403003106030030b0703070080d00c4400d4800204400d203c40d01050301c0074036904540035480d1a009603000b41120001c8030490702080b549103031004010041d44419034062040110071800540c1c0c45608a20468003111034a0056017881c82040d0f00c0c190000d1140f04035085256000d0542d9950141d440050001041c01103c444003100303020041030b01440354010054809001d04131660504080c05410800c6444000d282943c42d20002c0a141c0e10044bc04c41c010fa0458100d81d881e2994142055081c9100348218024020000f210402d03410004000052107039400091180320303c0280e8041c21901600c6054010609000009440316a02a60181d100740c03450100b6005030749640820f8100d0300600c18141e45001e045c440307000b50424100b001c400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 934671124 1250 934669874 934669891
    0x809180717060a030201020d031505040f02091003141306110c0124050102070306020d2711180a0209010c0516080c04050417070c150503040303150f27060308040509 72
    0x10811301d0742d40001c0d0340f800c01e200c450b02055076a1445104c0d04c542010850020440208140020007004408070000d611803000c0c103104e0342c006418404e000c3d010b40603480b108807403d44081030640d65461140680241c0d0f20048070440e03601c000450302c101048000d8240265044000101602d1040200a0000b424070300c98009031403543c420443c2e683e0014050050780e600100158662494808040151601c3d0744a402140105001c80b024a19441448903642d8002d00041c90401020018090800840740c7c0000108407800300082c00e8010a800506d0f81c0300040c5031100400c4110b46a00d424100c44034410f511030008400100306924007088800380c2d071701c000ca404014504040c0ea40c8880d4481041c0d07824500403010805200340020508844010020584002c0045904440041003903100f2542140030914280108030744c5071034061140140c030b51010610f5111414048007402c541c2c00d02c03d841c64480280c48102301000c1090056900039481070f0038054603581008108060303c20000d10303003034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 934672374 1250 934671124 934671139
    0xa0c06051312052d120a0501030c15020c150a02150f060f0d050111040521061902040b1c0506011d1306030501141807030f080918071706 60
    0x10040742c44401041c025441600701103507142c40301024408401202250050380c0c08600c51411082c10140e0f0050100f202e00d8800b1603459a5100c6081040384c0082c01302400d911002c0d0b83c1400100026013400d07141000d03030b00440d0000241d801c00103c800c41d040820b40c000070404120585032076010010f08840d180008210b41c1c4515122405841c0c2000007448035202d0342040e020300500c0c0c0c0301d4030a144078040d0014002d20040c0515030740095a0381c0640300301800b4010360700b02501030300100180070250200784030280c9402e0300e40320303211003440c410b04003d80701243d804c100014120320b102000b0111000784111b8040701c11b082e500c602c0d044560003000b05060010001c4141e0180c1c1e01d48001202800c801c4170705003218000c03c2c503642c2c000c0040703800c0240701c1d42c0780050344003000e90071200301c51040300864009140414034851440d20781d4070600c0000c2c00b00c21a45503140004e5500405001452005400e030095001c42e0841c01e50442c0e425aa600041510040c901c41441261901c45501032401d48000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 934673624 1250 934672374 934672411
    0x10b04180b19020c0a0f170325020c100c05010c050c0703030c050a0605070804110105040812070534120c05060306240c100624140a0c0605 61
    0xd00e6007403004020700d40740030003032921031a40300e160b5040e00c2992051000710b40b1008040c1c500404108010002038480404044034500c52102c4902124460314502c0210507000280c3e0480100b0228104102000c0d802044440078060f2604480040210140e55800c6286405030500900b103640550ba942c0410000300303c26018100700180e000b0880794145041c00d00d0320002d080c103e080c00b40296004240c1070030202402940341c5c0c00522940500d001b0185408841c00c07841c0191081c5c410303031168034002c0c0c006600e007545001c1d03144050050741d130060081d83c030a0100180c624600704000700d9191800f500380c41120344818030300c80a40000d8042d0704401900c0b1000d03500e5a42d0802224895944201000000a01a0b40301c00d040503900d1446600d0f02d0542d085c51108201440c0c21138082d0300307454441c103944103080280e40c3c090300c0c003254540400e20140100c2c01000c58103107035840e0869001d00100070030300c0c28446410001012090381958803400c40c1101440d1200503180041c2984107008407100c8030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 934674874 1250 934673624 934673633
    0x2122506020a021212040e24011b1e06021201060e0307090504021807050d0c1e0f091d070f03020316200109080c0706020f0d050f04080609010b0418 65
    0xd000140781c048507114404e03240c403100035103001241601c81e030303040001080c005840345165040380d001d11380710075060344c808440021007100e01005020003800104031000280301246644013a80b0b48c580540d0540e029040301c407044000840340d002d82196099400100030701080c48000009002d00ba8503d44244402c420000081d40c03111107018141046546101240031942d4048842114203c0450303203030018582610003400c281c204030035080c81642041d119260300b600c14292a0941d00c07030620010202654020304582511013080c0d9101800141c0c0c102040a00301100b945010240041c0a00302030b1a010718000c01c130444540c403400516005000384501a071219100240003840342c0f8000003019845041130700d040c51982c01c0d0001e203501c0c0170180d03070510903140b0041002100900840700c17826034828040369180301d40b111810941d0448402001d050b44104c000b080d040c8101510b06041ca070712840240d0030040c09448840c03c50f90758550100207402c02d0b0058000302d041807003100d1841140341d103e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 934676124 1250 934674874 934674883
    0x201110f0a1506170c1c050601030807390603021207080411040603060506040605030c09150a1d060a090506060406030e0f011107051005070e06070501090212250602 72
    0xc00404a1109882c806004100356004500502d02400c1064144005004140d12045820001800740141014804200c0e092111114070300764030030001c1030030b0780c030703607284c140c4290041c1c0411124411a803182000740102c2402c40100d5159902c40917010703015501f0705001c0040c05038000e1042c14014000300d60710300c81c00800e46070703c40e0305410700325103658603454202e042100c1c4490342a48141341c00c03400700a010b01940202c1c8152819282040300350f845208043d544c0038009a6182e12034403100010f00340c42c590301094181805d01800d4602c1260312a04891800c101045140c43ca900c032410400c5040e14289040d036005104c46481008907041c20710208040f849503000d080145a240c0059001c3e040003000215210300d5000001c00c4031440d01d111889007a48030005c191401c0c0718105891903503052034400c1c1e501580e4103441d004022801038051016a4010401c299115581c9210440168070b4013095031000d40314280c044d02e01c3e15200d250501c0d04a542403074481c2d407026444400c1c00150380014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 934677374 1250 934676124 934676143
    0x3010f050102120702270c09010225030f0609080f0304110a060912050703050111130e1005041116050f0f0615092206020414010513030b19090507030201110f 69
    0x30b4401a1584400701940c45003140660751141c17201c0001300300b0101447c81405480b4895003603013038407417000300c0c4100d800400c06034443c15407920822580800008030074018220381613120748004501095940c803000c132250000242c001c0180d40020400080040e02946061805400c441101030241048001007106000d4050014601e60340c0050400f4840100b00c0350b001140d119000340031800505880340895003080b10004544142a40041031100c2c500301d40d248242c0221070680321482c504020000680342c00451a0540d240400c03a0642421001c0b00b46078a99000c5da00500030b1002c500c6400340740c410014071800058010505008490305104005000c140d0300f00ea00e0b03445916405d0070072256030800b44420152480f4400c200c010004540c0107801281d0b0714100030745c5844043c1c00103460a00c240350070a691003d42500070301c00103074011485500721100740100f07480042100504012254515802e482c16440114104110b6074480c54002c8443e80540107424040e0070854001d5031031f00e80d035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 934678624 1250 934677374 934677379
    0x1260a080c0c060409060f1208270603070804030801170c2b0b06090a14040f0c12080403020916050a08150a091409010e07051905041103010f050102120702 68
    0x400c1c40c0100d204000c4140204402040541c0e034941ea00c510034014405841111100c10b400200090840401900046207c0d00589290724003081c0d01c58150030a56000c1580d0345168043c00070400903120500074610400746a00d0304c10003424907081c068002001644908440080d5151500111402003280c000e840000d54122240019002034001c008540c5412048104045540c00080c042070502c00c0d402180255185079041d113448000b04180d800c443c080117950300b00c20021400080c044a240c02416000380c810038102a00c61103803800040140c0390948040038046001d100354030f000d00325180c01494004440204c5c01300c42c0e01c0541305000d110000f02c03d100c10400041c641017052140c110038214010041c25510386c07240c12140080003420729038100395020f0800220015414804d089080d0300340402031940a240c84100040140d498070141d15060f040140000c02e83c48902403860f411081818a41d01c0f0340c14102d00082241d660b0b480385d130440d07001c40054214000703000200c501c5640c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 934679874 1250 934678624 934678627
    0x10e0c061b030c070e131703060d06050109060f14030601051507171b150619050301020304080a1403071706180903190504080706030c02120a0801260a08 67
    0x40d5440541018841800007126000c0040c86025603800402c0b003206070341220110070303500c1d2107010301070142c201c030b068004200300310040302c031140c10004034055940400d005100701901045552240181c0c1c07002c1e030001801a490702d805100000601030224094580c01e040c41c1c959010403800655a84018800e440c003480d4052604c1c190710031880211503500d9044000600100c1911300701e8201944810b401c148000d1079012490603200c808030b4410305400e901040003d59031108001c200070710604100011107510001d40c00205601d0a0014510807401a0011750316210120030103015990007810381c02542d1800c0013004000340e0005a0200c005002e650300c0b040590b15080820301c2400c2c9816054440da1000007001114000000140040f2003460a0700010f28181c03074013512035000d980121b00305134001c0c010070310100e4400d603c44e00c0d60300414412500303034604904c2643c0031540b02003031440000d4656401800792400c42580c00003000c83e12030b024804103e0a4107240d0712480144002003c0410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 934681124 1250 934679874 934679887
    0x71412060613120f03120207050705040b180405070302040e28020d05010f2a0c0b0619091506052721011a0405040c03260f0a020708010e0c06 62
    0x141c03006118003500c0c04101c3d8110302c0c40075003055044601c140808400045402c1c1030365107682054004e9800480d800301c01032080e80d04160070030001c0d012500301c0940009000070b152400c03072547d0707024a01650003100685810350460043c0f00503584003882c0c42409a0103072010b101440c290721701e030341e24a40182524800b00c017580d01c00501044880d81c0c01078055820101144030710003484d44451740d2001d026003040b42114501d0741c1c0302e0418900e0455000031070300f0b2103807010114103d904556800080100030b03405084440407003a2910a1036080102c00d156a80c0f80903a0403092000440041d00c0c050520a0500303012450760350400c000d00124000c200c4802c9803900103508c034078420070303890354002c448041c503130b040580b00c0350003000e280e103000968040c003a00444042c202071181e280180e130042c40c8107813041d043d0348030302c5018030301c402070070000034100000800d2400c0d00c0b00c060000300300592021652191004030003440c003591500201101d0b490101002c9070044001003281d075800f410388555031140b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 934682374 1250 934681124 934681147
    0x20307060c110706030209282c070503180607020a06050c07080c0d0e0d08031f05030607180509070e1005091c053901020a0602040305032205100302030a0e0d080714120606 75
    0x80005444008270084041400391403500310019601c5a1030810030b150312400004880c5640700c00c29180200583c00000901c004944a80c01099000e01c480903000e00e022515500c00107140d0283c1c002e8031030303504050000c0c403600b0f600c00f403100103021045900c2d10309a00d181e11080d00c244400f900750609003641641074078040a1100c2c030f6200600b401001d4071320624052030b001c3c1000d5a00c0707484180c02c81d0200c0740454146071140c0d210380150110f03035a0040b120f580c48280030300c00070000e02d21000e0003001e03c4201129621450043c41481e02d00b0b103900d81800301450081e2402040c6141c5c1e40b140c0868011949064031584032001c561200c10340d038605541001d10040c0e0800d8036194010f46003600000b400310034044004003e002e4a010b180500e0704400d10908503060341e43c4075003c0c0c13a50140540d070380f03040c18900c660065500000103501c0011800034807045c40b0f1426003010541c1d0040303441d40c010000d815801804200401d1102e410140ca44159407100c40c9901100500e402d1156030045030420000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 934683624 1250 934682374 934682429
    0xb0a05060f12030c070b1920010903030902180403140a0c08030901021e071e1106181518120a0b040303020d15030201020307060c11070603020928 64
    0xc002811a0084400b0501d0581e26544042c8002c0c0c0544110f890000d00e00b030004048807801420070605040341d5080010456004103401e08501a00d05180403505110b035081c42220901482510001603049e031900c14840c0c09005218480703103101006040201082d00b004400103050021020f403540c8844081094543d10b00c8480090010301c400320421801c1401540200078000b025000d2441500703685101d20300c18490303400014480da89480ea40d01e19400c0c0d8002d41c0c40420305c0ba080302041075a0400111f105500314503104650350305812403419403828a0007104c806050006006407800f2540b07415000052000c1d030703407036025404200b000380300c107802440005500c5900c207404c011182024100103000e50824143d081000340703081d441c11003840c10b00710b4813421207138103030080d50038206a9107034500140000851241880a00d40428080c410705021040180803107071001600c5003880010310884051040c0415031006039221850f885080c006034802c122035505441c40820011503070102043c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 934684874 1250 934683624 934683649
    0x31d03061f0b0a020a14060403050409020309120a0314070801060c0b0c0f120406050601090e0f0612011b0206011406090d0303020f07060603030809010515010c1a0c030601140301030b0a0506 83
    0x8060b000300d003410310160701003401c6031424010b0492510541c803401403561124004c0c0d40c01408a02d0030441040520f01d40d80285900031110401d54070a40a041340c030b00348591110103140002503581c0c24104d58906541c036525040001031900fc0d0f020340c10260302400d400e5030810046c20801400000a14552542c421202050700c44010103480b1482000c202104200079501200d41c0c604180005015501c03030300d150f60850b01c22955070b501540303c4140c6030004241c09400542c00c02da00081c030301d808401c02d0191000e42ca501a840c01a040d0f52501d0085c14a00182c0000040c10358405030f0745030580e69042a559034400032501407503510312031b14050340240300c0c502c00e0080c02603000c12640c051000c81e600a0b400c980c0a91201c035110750703460410900700c4404482c42c45c8901103c03200d11600354415aa5400c2c0503214006c12241144440d42400583c0c0341110390038100c0000104000302c135640410b8a504608200700000e045504554a060103100700509030044a130352035000806580daa000840d20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 934686124 1250 934684874 934684889
    0x2101e0218040c0e030d03050f0606160c03080301090f0e0a021c0b040b01061b0210030c23030109062106090f0f11010f0905031c171003031d03061f 65
    0x4002c145202c00f410722203031a402039211b4000d8500c6149450301a00a01d032041e05402c3c2030124a503203160802007641c00c5410b001c280348081440580001d01c14885003009940506400c944075807400420700d00790307444000000c03522410014a012001e034009201d48959504680703284880f0048030070040900403d05c0c0141c061070a200502c03091090000300241a41d42e00d540b00042a802c82e0011815406180c0c8000c1d040320020101052840c440c1c2e005218070303c5280750040000c0000d4104071148080f105801301074000020040081440c5403103840c0040050b4202c0d0340b411400d400c00e20031103148060000d001d568407000b2101c10000c0780d007600c03034945034002d076112145000380c20000500c04580e400c4034041540d900605c02c250b4011503000c0102d03180203006100c40c40c40b00c480c0014003c148560700003408001a049044141000300c1c451141c0342042c514040503107941401803149213008a641c0c42d094082d030f1034420944003c03500541c00705440c1c15140c3e550044901c90f4105141c140d00866 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 934687374 1250 934686124 934686131
    0x705060c1c05090103051b090f0621090f0f031b030d02181008010b04060c050c030102120f0c071e05150109020a08010e060a030b040507051c020102101e021804 70
    0x1e00d982207005803843c0b40080e40c040200d07581c2e002418218804802c0740c50b142c1807007440507208519260300c9a2040d200040d040d03d050000d0300600e400c400c1c008185599201d0000c00c10461008010401401100488401010f40302c9811401a03164441c0da0b14003415940713400c583e8140184104125006144400811903454001c84205180d00c40341c9030480340b007420b240d03000350300041c4038245080c182c031052580c26240a141a030159200c200b00c1000701d5041c01600306440c1c0070b0740c00384050a03403d100c0c80c441081901d400e4209071380b85180140201c1e006442130005402144081c2070041d0b200d00b8034510350360400c0c000d05240b45894101d80c43e5440813a0114004152400c00f6006403802c030741c158a0304030702a601c800803442c40600c103c42c51500204510010004282c036818078603002030060096950071a21040483ca5405070140d9030f110300d000b50740c1c100c1c045517410040c045443d010781c20300300035010040302000c4d90310200b83e00395018141c0200da104c4103003041d148243c04c90400140101b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 934688624 1250 934687374 934687423
    0x90715030c1d130c0c020604120308180304030f020d0c0b3c07080f0a021c0806150f221a0703090b070809060705060f0105120705060c 59
    0x4001e4030300d40782000e0010b608040542c40140302100c0e00c00030828010710402c81070784081c41840061490a030744c642005190203280000d40c90707d000038800703858008007050340d490050030b02034020341003d820344072803c0c005100094108400b2094406403030384120341009a50f114000188168030f400e0014000c903080180001c1c0507401c800c01042e0b000d600041c4d0142c000f05d50a042100340c03085601002040310340d5000b01c049484464001c01d036941c803c01da0b040c2400d44604010950340c0012044c1d8000d170707008000f084404c0c000203030b1000e4204e08501c0c101c2d02616102d03000c118140c1144180c0a442c2074080781c920454020201070320050506805a50034030b000d40501250200640d01c142003002c121001000c42804121b01180e85103601901d030242c3d454a84446c19149502c000c2c02981c50510902550800d07a4612000f40002c9010f48000c2990b8105034843d0581c01d003069018500c01d40b4000c1d6400d014407004245c800450744100c5031a43c0781c2140c4140c0a08003185490034aa0102c00720303440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 934689874 1250 934688624 934688627
    0x40f05040b09030a05040b1b072c09030d0504061803180608010806160203121302120d021213080f0312070801180f0e0607090e090705090f090715 64
    0x20a1140d80500100e598940301c0c040255100d12403081c412001a20070081480050714034801840c80c400095000120100d880d0344150174031035190010b00011070f68449409440590212641c07943c412122256064205040e100c0d40e20710402c01e2502500307840f00c001406112182e8041d4400000040310b09071001c4140c94010b207403011464200041103114000403801070b1103200003506135600d550090039541c49241c81442c2c005941e95500d011132004004510040404805807402003841c8040888210041c2c41007192641c241c00e500c0312a40d0114003071361513484d4001481c50010f40c0490449959041c451407140031a49950040700e0071340305201d2081c140b41d100200802400000003170031070341c40e101c1450882c0d4103c0d00380320b403144808002c0e000812a024a5000c0c0022400c4464005011150030000c0340c14040102d8428004c903500c0302c020004000c84954040e400891a0041c0545038100f43c0080d00100c40030b4081544944210f000640b0340204201c1701c006081480e4103034084e03540280c070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 934691124 1250 934689874 934689881
    0xa1b0305040c0f120b01090e06040b10050301090c150c020906150f0304081c0204060807050307170109020310050f060d050c0f16020f01080412030522111005130e0411040f 75
    0x101100c82c5c17519180009044800341c4a00000c2c0800b18005c1c020a8071240c0b40d4180c00c41d0068400704c1801c81e103070030008043d60240f0648518911954030304250600d07200041149400040181050000c0c586070000145c2d501950310381d1111007100e90b8000700003114031450041c000c09220000c07040000060000b4044200c0c080c01d1030b00c06103240204075098032980741c0180c0c0280e10511700461100c80c0404d085038081c0001c1d652245d018500907403030040c3c500f0590034880d400c1e8040300d405503002091191403656039071541c000e07200a440030348a00901c0c201040041c03240c0e580d1b0011255448002c40c44188a1008648000445035107158072100c2c0f10203100422108003008900c81e400c50140d4015a50041000602c03554221740c81031400302e401c44056010b00300090101b001d0842201000c4406d19400750300500700350244030040c0c0300342c00040501c690034025013090303c20b0040900c0340201c802c5000c0d00441c1502c6416510414645940c030744081c0000818180a074414101080588030000903131 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 934692374 1250 934691124 934691159
    0xf032f030103020913051005071101020a0c03020c0406061209110603070305070e092a190503160201020903250b07080d111c2705030703080a1b0305040c0f 68
    0x441c00702e06602c0e415945c0f0900303a00200014110703000f00250290069103a0b000a601160701e042909440d4186a070142c00c86c0d01444c400e20229159500036000d1550405c040d901d28041034604019041c100f080280c0041800255108845e480d1602242000321542016408001c040c1c065903c9007064071001d009032008a86d00000164500c60301113181c074142800d58041c4940038101c80c465081d44146091805400da682e4807200801c21030590350a0881e80c8490400903580d840d00d1312418812008010100508030850441e801130100d426103650220300820715042d030000781070b40810240a282c0803904a580160074052020440e0803d1180340b40081078016203249041101010307500040c0c0d0b05005400d41c0420900e1404010360354501c142c2d0103910800c0001d060400304044c1c9501c0d040213826030240484842c1c0001c1008400c2540203801c19422031170140c0c1c1440030b4803c0340c01800070090550000020503440700b020600380109000508050000540380481803a11003088407040720040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 934693624 1250 934692374 934692379
    0xb0901050709050904020112201b0a0b0c1608271801210b090d09060305011a070317010b1e030c040512030408030a020d08090303070f032f03010302 65
    0x40c00203441911400584080c0e030402080c920250301d880d0011580340b610f50300c10070301083d82c1d0a200b00386800d400e800074a850340c1e00b124450f950441c40046d52004041090b80c07890660140d00700307100141c0c4010a8503030010307410f140c0710f4640d4040f8020084030940030001a0142c40300103420300f51804405515080c0c00d50302140701540c008160184000400b18440d403101c0d0b224604010702c015110312000d4400b00b4040fa0320180c0064050f00ca43c25002401d031000b12160340304022880c0d0705034001500400400031403c081002c1e42c0b42104010745a103d02d09182024580020340d2400c0600486100031070320f4031000851155a1203006188045d400f8001d0110503108010341d582554401c803040701d101e91000340005007040d20f40380a2002e01002c00410b001180400d00c00496800001c00180501c40080ea00800c0c10298000000e401c0e0b10001d003041c0072607041001080b20b880d8020b40030140a04451800046c2c0d0358511b01080c404000e140352850003084058000d07480343c00d1010155051764004c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 934694874 1250 934693624 934693631
    0x50c0d0c0c11031609050604021e040f05180c03040c12121218170918060915010807080604180506220c030f030e04051f0605180f0303070f0b0901 64
    0x210b004040d61110312414905000503000f000380708050362500056000100a0070241c03c0080518032041901194501041c032039030042000c000c0103a41c0c0c11210b00401051f20140101c144032079480c200c1c560020580e159441d0b001000c5000c0000d00040c0000424215010201e0f00d000c0b07250184040ea0784558900002d4510340340640c00701840c1c4201c10b07640c2000c10f00080811415074070f250003400000000507214005028104094a494001d0942c040d03c0415034041460850200310030180003804485040301c02512100c041c2c1d03041000160000d0690400000b40d44d20200050040c01c035460450840b003035000016010840005092406154101d48104040030074072840c0294008880018029540f01c5c0c000300042625a10f0101c1c3d45402480d2103861551503401007402c0d0344c4142c468144000e00b40710b00c41102000401e4410152030203280041c60041d00b6500c6280313228140c0d600360311550409a05c110b007643e08000f10707800c1561000280304480300d141042d822482080300e40c3e4405500b03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 934696124 1250 934694874 934694903
    0x5180604180f0e1e101506020106081507080406060503010c0237030c050f0714041a0622091109031203010308120705130803040f0509010315050c0d0c0c 67
    0x10f000d41e091010b6408000c0c4401e60580000ca00313209003140610142c3e000d080020605031045000d1001d20b0459a14070710191807030540028211a1075900c0014190010701071100711b00c00240b08180c0110681c07500301141e03150707803c040006004a900140d410742c60100080d0f611070b000705007881000c21140300314100700344400e044101085500b070003103003011011102000081c012a00e0f0101c0c1ea000340111244500d07507003445460088140c01800100d0b4a20314404624541805491f10504940e95505140204100070582c64000d410420f82c0d4003071142c0031204136401901e42c3e00000d00d12007400344030f03001c0340c0020814030b580080142400b034080c0010fa80540c03243d2104880c120380d03101030410300d400c003107031442030a003440a0100010400200180550f0441e4140244054581c03000a1555036151402400700240d440e4481c9000b4900300d001040480c1c4440d94000000d100303100c1c0403940c0c1da20100c08210510039540c100710410729284ca0f4000107980400e405042500c00c007070407042c1e8903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 934697374 1250 934696124 934696151
    0x181b081509040c030b0c0d0507020c130218130e0a140105060a060203180a080a050601060912021c081303050705010206060607050d0c020604050604090203061c0209070518060418 78
    0x400c202d4014003120580700c410030006401c040300300e50080182d242c150604040c4070f00e9030159641a45c10b080141d115004c8448640780004076140446d00070241189000000d90404180c40740e8041d07403500ca202058041507010303a19401c0300402c1000d000c21b4070240e03419840d0101c9981c500c58a808029860000050b85c00d0810000e140c080e00d00b0754000b50b040c0100300d4841101402c0003644030390800701c0002c00043c03080040240d01041440740c0041c2c0015810b00740001c2c1001c065071b101c0390380c94642c3c0304400f01603145c080b40d80c0c12501903000003180010690904a00d14400d051095404001c039681c000280840403c0d214140c076001d90948842d51070310781c20410316001d248030152144d0000c1d20100034440c02a080541e40c44c2c80a01a1410302d5650740010303d003a00603500c51302c1407d400000b000a245000c82503c801c40300140c90b04c04410b21181c004c1505180e0041014051143c0007a9103880c01e10542c210300340e0b01000610484e03940d62900d18000d500705904800918040c00c2521068024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 934698624 1250 934697374 934697389
    0x106080a0c0b04060c0f1b1409090c060901140c1204060207060201051902160b090c040e190b0a1e0b09070c02131d0102030a0b10080709181b0815 64
    0x4c0b15a580e031031a92038055100d40381e03403000c180011900c41a40c0c0e01c08400d082c20548642c002880c4015003d41c0002501083c0408404003d140c1d0b113460b0008604010380b2341c0e822081c1ca4000c0428a81044071082c0b00003940c03005d1280f40841182c0c2d200d180c4a0f0a455090715000308140c0700d4942c01c0e030f20119139942c0d040c0c1c26500d090340c040c0361200c1e001400f031003001b003541d016043c400764082541041030400c4e101c90316400303c10384203241540c02c1a1000c0a86051600405142e1082000103200c01410708900c400609d008c02401440700c2d04e4500460350070780d41d40d0448080e580ca0007500e640755000c0001b0785030091030b00340074080c060f00e4110300113034080e0300a401c001c4040b60081e01d00c500035110080c25030020700f148248084130b40d03400189035013485000d101035842003500010001e0018042000c0200100310200e1071010003440f20108100140c1c4107030b001c412140300c503050100e40980c0c141181c002c4d110032001d142c2e4081c030020b1043e2085905c00c0c0c807103014902e141103640102d0340090a01058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 934699874 1250 934698624 934698629
    0x20909091e03120103110f100908010606080f1303231b0c0f040f1d010905120f071707020306090d09091107021c05060112060b091e0c0c0106080a0c0b04 67
    0x1460b180700400203d8442d800c05280c80702d005050000b1f43d1140c07000140358078210300c1c030800044c15544040c031514000344105405851181040031a07842d041c1410712040781d008001c500c1242b170405107401011b01075044451125481c80c2c0c0c94607402e0300c042c0700030343d1074000016622201c03101c0502c00111002c04149510780c000d01902c06091416810280300184c500400300d02ca000359640c22410600203030300510410011070f43c2c00410110365070300304107207061454034103004007080801074055a401d0340402c4465940e800301400025011415101c60746014030360f40039415002d1175040204002d0b0114003103154586948941030103a44500003c02255100c2608042c02e100410041004d4544441c00c00040c3c0300c6202c044140c003540b0340e22076040007000c0c0e21504058104c00410820050a401070a48600c07050740d00c0c45280c6403842c90351401080d01070442030003500c03e01c0415102e00038503088500c00e4084400a0103c26940e240d100e60710444150141d620702018100440c0141583c02101c08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 934701124 1250 934699874 934699897
    0x120d150e06010210051504110408010507080105180901181202070e0c1c1107050d020c09040b0c0904090804062106060503010b0f042102011b080a0f0201020909091e03 73
    0x480d034a02084400910024020b10b002d5580a001041c003a07072030340108c00ea0302e0340750f40d040e0751903034504150703182519005084070051101c40c00040c80f668941120b00c0f02030801e5280b00140b5034940e907003514010107484030141c41c40560b03180c8038014030800142581c0c0c040c915508460f9910758640b0030041c051801d440c5190000b40400889054940f088030203500c0080200307000035044500c081252003030703003c0c0c10708407987c0d04280d0403554555014041e408007200281e50b014100e140c580e42d01c150341c02008081c0e4049510204001d1040d489a81c07225414940c01a010303aa00c0d61601800340000741e0f40c60000c400310001190012111010303014080c01c0354095103501d41182d00b04081144a07401030005000008404d1200290000c00f1828000c2002c1e080088107c015840340001400194101008280c0c0c44039800d804000566000c21070710b05000d1858520412105503070120701a12400c5643c6170b2096000d001e11403411404100400f00d0707410105a03083e41d2a551555a49a004d005074842 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 934702374 1250 934701124 934701133
    0x80114040902010216080f1606020c040e01180809030f0307080a270b281205100801090c170712110d080d0e010b030f0a02060c120d150e060102 63
    0x8020381015008a00d0071403050055401000b2443c011040c00081035000f071206900510038110030440034040000849082010401c4260814801a40e607103c9580c41d2402a5541c101040c0a040d00b9030104240ca11041c8400c41610a01c0c2495020740d0840e9207401e120380a81c00c01c0010100c0000b04030303120607900404081c00e1080b1402e0585a20301004800229400e05000c024a11100c0503641f00c09010440f413001e484420b8050500030150030380d0041d00b03074604541c9075033103c2d41d0000d150b290384050b0300c040400c05a03034000025600c960560b0050303406600340701026081009440c0c1c20000d40d8810445088035001c07200d103c640c0d40280388110440c0b0a56400d0301ca022528900c2c032102882d01c09045046403008030341d01e4440c0c0307900c4151109042075275050710800107802030060b04d1000004a009014921480c0000d030345490054074028410200051094254003041c050050140801c801603034462100c000b14038060a641c03245040c0880580c08080f03440c81d1103415140c0150010390060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 934703624 1250 934702374 934702409
    0x15010b0a2d0f0318061503080d0609050106051c0c022d01150f0e06040902120a1101091a0306030f0304060507170f0a0e040e06010807090e0102092d1c0506070801 71
    0x100620903e0001102c4059114011002c02c2421004249c422002440040c989140071030442c00c560b01a086207081110800541c03615000a40740b1010b0703d10414000189040e0480c0c080c2d181c516224030341e03c0701c91200071000f44a9070714030f060841e040c14402c0c0203000601d2034858800e1420201d018440c0c0c40010041c050101041d0342880603070080c8050300c0000c1180300780e000035450f00400090001c2c8e5921003108e4000f0054110042d000c407660a08002040c0c4c0e013001c1d4159042c07031180010341412500803001a104d42d030300704a10f22b41e080d414130036070707584a4948500601d02d500100055401ea041080340c23244c0d041008085608071100090290305080101c44205c0e0a640340e002d09030741c403e0b01e5106030718584d502031010b41d000306407100061000c0e614116001c400d54400050854481e4030500140e04d140c1c40d40e4031358400002c42126060012140d81002da140a90451082d9400820888038501080050509080f12a000f00d084400c5a601e25030104e89501d001d002e030120310110304002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 934704874 1250 934703624 934703633
    0x5040b0307030f05010f031a0c0405041107080a08060306100602100902010507020a0f05040c0e1e0a0803040909020f120c130209030307060b010f0215010b0a2d0f0318 73
    0x2658200001d80740102d8604401c0041e03034141c0d0802e8004000c02d1010f10001c004214090000c1c0c551101017580100840c40c00c809403000328042c905c0780c1409243c076059154030900708601200d01041d07222041030340f51440d036030000b4a00b01d411183d4a00a115520219070040041103994007290202c5c1e005101c40ba1040d0a000081c2c441034100303d05100c81440b2200040e42c0b50040c01d40680841084403070090311b041d04100985c1c16100d4031805008050030240019200d030740e42c00000010710307010980340c10300c2800071030308017404d0b580080542c0c0130100c1d02280b00e201542101355018000c40c3c08050360940320003040040340c40b00c0382009640d44505001c4240e424203941d510600f1556100050604200c28003090450340105803c842c5942c0c0c1d148103404540c1c1080041d02c0141c003910041902c42c00d03000e090380101c04107008004280001240c2c818015104801680005d035032808140e82060b2a0030344140c070510322403018004151880d0311660098405d10034582030004984403a1813403031403620f8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 934706124 1250 934704874 934704877
    0x80304030e061c05040302071e0527010326031e09010f1a18070801120204020409060602030d05162313030b090f070605030411181602120403020105040b 67
    0x60040d00040140103c0ca0401c46004403028036081c1c1800215280c035240c034009081409035080f01002c0c0f01010741c6101c0c000b60f50308c240810740b401034526a001640f08115032500c02d4408801c0c1030000c1e1042c00100801c03805081c13000c00d11391480806001d94000400030303590350000310f81c036840d0352216086229200017810940c6070000303103610001590140c40034030f10381500c403c0d2040c40400c44100003801114107041764444005c4985c810f44901d1410128402420040c040c450504a81100300d510402d41d070300d96040f10020500c512040083c503030744882c040d46039000404144059071610700060500d41e00720081c0125954a695207901220780310465404811105098280100e400d105c130415401075006040055801040d0040e85c61500101c40f520f03140d9065149075080c0c02a410070480c05400200b5260065441444d09035100c807400c001c43d41007249144006400004001802040071241c02c041904140941c00e66070359085200c4940302900c620300c0000c3c00988100010000ba40c0c0b03550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 934707374 1250 934706124 934706147
    0x1606021b103b0d0e09220201140d05040f030e0108090712150606020a050d050903030702042f090a08150403051312120801062c0a03020618011b08030403 67
    0x352404207060102c00545001c0c3d911490034040340c41d64441d00d82138904407040070b038000b01d02d10740d80e400c130b00c3c501c80d41203038500c4840c0e4002c5c140403108000e10501c00e000015115240a0400104410b10b072608140c59070243c00502078000c074440201220080d41711301f41316481440303a6001840058075203604800d26240c0b0010980b015103035491681031101c454081c0d00d00030141c65008040d001a907040c06802d00c0e44490002060280800008409850210546100b0b640413a00000c50083e070b4804051070b01800300460007001e0030320b50640c0e141e01d00e52010301400303007007661100c000944848080c5d948140103080241480540c0c800240040d00c80c0000703000368080100340c0303214503944008100006105046c11544854000c5aa50b211503001c0800d0703004040074075150180f0902d0420519000b4690000701c060303801820103103082501c1e0300301700030011540600184e0355420014144891051484035260010f00c20000c04225200b03030341030300c13030b001a0004451403540c4c84503601600d4281408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 934708624 1250 934707374 934707461
    0x230d050a0b0a0e09030f040e090d02070f05090a0618090b180a110319240203010b07110f06070b06120609120717030a0c170910021606021b10 62
    0x8011a11242c2c444c00080d000400c223442600a01c2d0502c41040da0911a0652040d42194003080040080c444040790700b00442c3c40a94001e4059103c0480c2d403005820560410350700301000e00d040300306641c9035074861064075007d20754a048a8a8150025240c01c05034901c404131980900341000229083e400c018101d44030080454002c068691140d41651603d0107007038030728103440400c029245d641c90800348001401d801c2c00314078542c14140700c03030494026802c000d00101d000f522801d80a0300e5080072500c00c040f004041d661a64070030300d8404074140c01203901c0740c01001e4255020390b0f800000101d0a00031000e04000d40010b003092580034071071342c0140109a03189400f40034000900101000218010221442c01095201030b90340c0203440c07280c080c09084030b0000341e1010050084004030700542500c004900160361402820700c003565050001c0b0001e4040c1e0301c0003c101e18180148206e52000d0b240f2302c0295946011280c04000840701c60604105010000008140c00429210310700c02d00314001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 934709874 1250 934708624 934708627
    0x406090605030604150303020703050c0607170d110d06090f090c0501110102160b0a0c08092d0f010e100203101809150606090f0b0a080601230d050a0b0a0e0903 70
    0x5d60010028107085a00503405600100b4050080c8007088c0800c4900b41d5094540c0c40c5400079a50301c0d25682e492383c02403a50440004504445459250b81103074595050002c002501e131074190b10200f0091840780f003600d281c507107085031003240c00310540542c0c614903410041003a40180f0342001036030415500d06103500155420400060f0904030060304052080c0101d0031003003030341760489010703044401450700c00c000c1c0080da404010010000044290641c1851343d03a00c07907128036030107420321541c0c0c1c0c0b609000017034003c8001294106074154417176102841580c0c210f406038016900c102c4200d110a82c7c7d0001d008240d01000d2140114211902d040c95072107071000640980e00da200c2074158242c8400320340d409621a401000020352006941c4040d28280c00000f21040c903018180c0101c0c842c40c074000050180c1c000005400e0703801510400d01c20458903410940f55052004900c0040e40101a008242407074280850b690401d44c0c0f280c0c20b881c001c044d002e94442e906060003c502400c1c000d1200b80540700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 934711124 1250 934709874 934709891
    0x7270b0d15080a0303020703110c030c1302070b010315200a300b0f01030e030d091103030a02030307020607110a060b0f1203040e1b160804050a080d0210020406090605030604 76
    0x1403c204000340c441c0240c0e001a1641c07824900101185c1c41610b0505095000e0485240960340c0802c03003582d0203100316015040f2107102c1010f600a03004c0c00314060070304440a000007081c00a04041441ca00d12204410800307411880503d21241d000301001e6051240180300058006005040c086e075102e8460341034854403508210001c8020800380c1030444010380b1103c0b0b0010341e0502000e480020034017400d00340b0074024a003a01d1540c0c7d01480c05004002c94039a10840180300b483e106a404452000e000d407640c4800c07048001e90f69074001e80e5101c00600c05d640000302c002d0310541e00680c0d01c01e43d5802501d90010191903c1d80900254016145d0003074264a020582d03945000481180c1c544844c0a19140c9140c207016140e140001041c8001e13012a641c48000c0c030786240c1044904d20f1f40c1c1c840071b00303001b240b160500d44010300981d00080c0e00412520404924101c0001d9408461070841c1e00300c0b1200613030308443c4800d07030003248500004200c2581c03043c018180900040d6a200b4800b40c2300107034040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 934712230 1106 934711124 934711139
    0x519030209101b02100c1e03050301051003060b16110d0c030b07030f02033303030414010e0619020d030e030a05030601110607270b0d15 60
    0x260070f486a9041c0d141051050042e070050100d003003500f9880c0c00a4031400200100791022805055141c614003c810035607018184d0580c1c0c1d141c1542d18200030321400701c0c80c42c5100020301d40c5605022035181001c001070404000ba9445e0b90320043c215040c0354464a4501d1503860082c8240380203400171410000e9020101c1c0d9000b01c3c3e1000d03654a03400c0841c0280b00114500351150300001c14001c920714914280801001c0c4c0300e22110703c034048142d0b102c1d0010000c1c01c0158058106001c200304109680884600303811045c18022140f906050000c2c070150311000210100d1041c0040700300e80300343d04015101180403a41010041801c04144603640c80c040d00034580101303c000000991542d10803002d2070003803803d04040329000c0c2080c50020f40018151818500300c0300741c11802100c10340e0344200d600308a0340f10000f442e151880190000c80034181120040701c10100d80e010004809 = true := by decide +kernel

theorem cover : BRFrame.Cov 934532374 934712230 := by
  have h0 := BRFrame.cov_init 934532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 934532374 ≤ n) (h2 : n < 934712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
