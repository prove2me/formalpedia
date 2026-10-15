-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4222
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:14.585931+00:00
-- url     : https://prove2.me/submissions/5a6ead03-0977-4f50-b316-1b3febc4bf01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 759172661 ≤ n < 759352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 759173911 1250 759172661 759172691
    0x702040207052d0d0c02010e0d0b0a0f063203100e060c0306100c06020c150901060b0c030f0c0a060603050a1406060310020714060420061e160803130501 67
    0x561003e40d400000d2075080c88120b401c80c1c40751544030050f0b05111020480c2ca1440d2504014150114081e01c00e800150030850661821110422551100980307080c0080c0805124154828a2446061020305642c06400b500c40c0c450314044003c503074507100740040b0000c03003586504081400d9004000b0f03030382a035482e00003440e1103100072074000c0e43c444020480c081d8401d00070031001d40503900030f082c01401d26614034001e030700e400210551307440000100c004000c0700ca0024040e180c042d0000001940c00c0c18031010703c03941c3c1d901400402c281c2101011903071030440c0d0b00400180990641210007070000b6652801e04a0300c07260102000e4440ea5004c00300355950110004080e402800041c00800b015460f0280800082d0814101120080c954142012160a0401034540a0740c00745035440305920400c0140b40040307444041d60b50043c8010b07c82c0c0510040d00d141508583c54440c3c290540c0e4140c00d01580400c50480d81c0000c0040502100744000c00100c0300309001180d00c0b40f0000c020401c01c0b65212 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 759175161 1250 759173911 759173983
    0x70305060a05090402090a0f0e0c130603050718020c0a06090b100506040909140f0313090507050406120905060a0e01060f05132003070513121104050903070204020705 73
    0x10640007590740f0042401402c2052025034032600c4403c00280d100801c00b4002d0582d119440e5500e61540082e103500611701d0408408a17101007050810030026165556481d2181104d105410780d10709100040e0018500e80d4040354041040300e01a261480c1c41450000024000440296076440c42c40300025030050f050040340c0203a4034014000d90400d0302d4444580040d050f00b0b40202d6414000300e685840d200000c00c01c5c500028440c002071a2900604684100c20324980d500c8201c10a0528042c0b01107a0f0300202118103680d1030f07203046410714594880e001c0103071001c008001c0441c8135460410850207002c1e400b1102d1400d800c2c000344421075407140c0c25100c4080900805901c44100c94240c000c40c429548007079410700c0c8004ca48841403082042524803a0800c5030700c1004103100103000740441d08918019000390120700c81c00c0080c04919140c1501100c2201a00349c01107035a480401d2043e10300f04291140c0c940e00070402e554455680c0380640c1ca500031390641010302e9402c00240041991841c0d90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 759176411 1250 759175161 759175169
    0x13090507120521120a0506180f0109050c03010f06050714032212050714030c0a09020a0801091a042a09030c0e072a140105090607140d0509160608070305060a 69
    0x4d00c0115031206106030340202400361000d944203140c0b028a485122602d80f8803442580c0344070203000c0710361600900c90300343c5000a00769991400b04200522102c400c003102d00003900c04030300d48030384c60f40120f24120099140c1c480ca840c070039200c08215040f0046045150044e10b20002c0c000c0c480309943d920740344640340c00440004160343c1108005000c1c1450142c0721b51a07038a4003e08881100d000c1309d02040380c00b1090f0704480001600010340c28212900480c402d8010400c0010401082d001050b140c100084507002d040c0c41079440d651a0311a6054050622881c081d40c0c80f01010518130031500036006c22581e100440c4c0c584500b64000481c0e03008600c40b94400c0c2110f88503a0b03d200880d00c0384030000030250444030540502c4002e49000300e1a444507114002c1d0304030000190034206282024601040100a0000c110f400992000c0d408015030566503400001c55001c0b55075110480c0300d0741000b02d80e050364180403100b03c000061042d031104206000c0c40c001d8030200019116802030080c1841540a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 759177661 1250 759176411 759176437
    0x602010e0d1b0b070c031103070308070c050f0f03130e09120706230a0f0515010f030b030d03060e01060306051806181005010906050913090507120521 66
    0x48518100c60103540c0001c04400854207111291405680b9104005815038844c40060b401082d14070800d5041140c20b410060030f40e000b5400d0601994000300b0b0200c00400c040b0822a81407161020003408000048084928a081e1a4200e00702702040d9034940091566031200c1420340c500043e14680d40075084d008602d000007405a42e076010102c1d52003940440b008442e4517964103034030a281c0c044107a601600300c817030b010411410b05140c5101400e98a02e881c0181c0928500810f220b48031022880301505c00f0340a0800502000702c7c45000e0b00101100d86586803d0302441940c844042c2d410387c09101a0307800040042c0c07903645c95520482c01c840c0d1b540034441c4c100625008074440f084c001d10307000d07900c02c40052200d0030b0018450045584174006651004610400707110a01c600d6811151181c080c281c20304e000c81c2004100000117280c1a90003412010441d501c042d0308040c0701c020303c01a400303051180055200005a454031550f02e0070340450f840c00e00014941095144404603040310b8406280d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 759178911 1250 759177661 759177673
    0x30a0605330904020a17030d0b03010b03060105010e06160503091f14030c0c030a0e04060603140402040506030307020312030f1b07110418050303040209010501081b03070e06071b0602010e 82
    0x7000d00000e41009007050382c0c80850900002100c149030034040e00103000420185071111100e0000c202624904440e862080e410a01c3c4880c607601e000680b181180c030300b4640b80ca40001150013044d400d12540110100c1fa1483c400f4140c24040d000005003440030040d2814450099250000c103032207400080b0f25000100d00300b0030380d45020400350103503030090f4840c0c001e189441c64114540b49194003280118012076039201d00110316141a10801000f02850304040c031803d410024031050502009000034851595a00440d00985040003616141c2c2c1d030180460f40d0001001219100304e030021103292050003107d83c00280c02d55009514028805141602e6506045050b031350306a090034504260380d0440c1c0d032011440c00c1c5c04000285d030900e040c00780f8091952400c1c10300501019600c140c12007410b00c0800014031001031406000d400d0f03241000101c49071292a220412507016042c03040e0320350300c0000410382000784100782700b415503041180b8402c0598595509800d03400e03501070009009241d0052 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 759180161 1250 759178911 759179011
    0x20405120f21040e01080609010e1c21020f030103050d1b060218150d05090a050703030c151b020c0409150b030a0210350c07020f030a0605 61
    0x1429107840c0c8502c1c00c00a00c1c03c2c15100e209100029200340d002e03010960103607040c0440d4040a02c10040c40d241150094509402d904079041c03000709402140d0010001e0442403c620034101000b01414825008015544d4141c41400c030341c0e41d41c20a000a0385c031030003200b1707000c1c800c10f00a882c280c60203905140201c10f400e91035107681000303412000003580700d40190446800d103179239111040300d078020380c81d030030191916810400e1030100c81004005201641c0100d0044010400010f50311080ba035044c50a403d10342e100c0d1511217038481c08003104000c0681070030850b42401400c580c003042d5002e09030f400c80e03504a4400c405c0000751a203414001d0442d0010703a10440e41100c182c1c02c202c54004002e401c0300d0908901e640460017002001c2407860000d112950142401000317043c13207241705841700088401c00070f56206011a41c0d18007034001440110009441c0003107407a60901c20404480080039030704914003905240c8041c100440d401c10704442c03011010300c0d1844000b041600d071104011500350600304c00e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 759181411 1250 759180161 759180193
    0x703080f0a020c010e01020307180b040e09120307020304050429270907051503010305071520060f130f121b140618100c031806020405120f 61
    0x4003802203116680c00f0421114012024000c0e0092003000c60001650b03403500f41c00080060700c0b803a920003450342c08500204400ba454400703a409a0f0304504024202e0703203402c0d100070325010b400c0000082844010003001043c0303401001400885400b5035061142d1400e070014445043c000d101c5902c00e0000c010781940d61390130f0404922041c041c1d842c480340b00c3d4200c41221040030707502c110790000307907a401500144100c0c142004909114413401211508650441d0380d080d413940b01c0341c000c07501400482c0b98030041c0184295909029200001c1c1c81803000580c0000706a01c0d42803ca558820b41c1d2408408038941d000c0c01041d00e6041c1c1d400c00c0510f0054180740d41da0311082e0848026000410043d02c4543d0300b030000400965403410310130191441680500541c070350504600070b00b1049814034814242c8181c0d0f90224444075060848000041d4074429200141c0061085400d03148200c0a00420b11b020012a40d0041042d903c04469240300c0d0801e08500c2a91880740040d03c00c2c0b250468032100d41c0b4421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 759182661 1250 759181411 759181441
    0xe040c050307050724090b011d0112060911090903120714042c01080d090812180d15021c0204060504030b13080708040e070206040201090b0a0201060f29070308 70
    0x402140c0500085002408a400360340d03100c04243c03047d0041c0d0004202000e100b4908040c0f000c0c8e1805809240e40c507140c11585030f1103121602805c0c054440307100e0020400b0300010140305040c020b05000c814140314800350794076005860400507020403440070071540303409042c0850500c0d916030507091a0504100c03140d0101e006141c030800c224000301b60f02c01050507500c07230f01c2c9020707095050082c002d89103610310091a1890725070101c051500315000020102d2054421644683c50004440080c08036a4010941c5a030302c2202c06001c0340400400c42001c0010b0703400400305000384169026580440003080740c101e203d2441942c010502c100000c10002d0030504080e68400f164960080b0384d20065161040c4962080d28101c8c1c180100140c10f00c906a00005181d41091407840100060701c3c3c990b0001e0040c400501a10460401c04070305119214405d400200141c611242c00c0c4020315a21054103030303410220307030841c25100b0403604410f8008200070107803001c09425598001d0b81d519000310201e0700072 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 759183911 1250 759182661 759182693
    0x1504060b0307050c0f010e0f1531140709060b121f08160501120b0310050a02090310090b01230114071a0117010903050d020f07120e040c0503070507 65
    0x200802000205d103a0003032003000c08420306c110140c000c1140381185141451218031b09a5060b00583c02403000e43d14201c1307902c080705101c2d450305d00141d525100420840c0c2c1d6850750021f2491a0300d01448001030300108005088916440091081a4a4547d880800e0084141901c0580c444500050801101000034040303880e444514002c50354850003a030703007024420900d090240b04124030800807540d0101040880380411203040008040310b0703001a0302e55040308082026582c40310003149246026604580b82e04500404031095031000e0700d00400682aa070380e091352200c05400001801d90151400e1900c4d0559034114075606001010056450744a41d441d00c1c801d4500502070040010340c0d0741004440d4010541314145035600d80208030300c031024888101c14490b410f040b000030000350030105a81201610150140c4c0310203e1030f940704204d006800b4041c0c500f848058000f81110f8101c20004140c100c01d032001e022655140205450301c0c48151108000928108910004070724100f01b070b402d4907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 759185161 1250 759183911 759183913
    0xb03040209040f0807060504211e140705010906060501030209030316080403240b030106050312071b030803150102010507080105060702012706110601080d14040308030a051504060b0307050c 83
    0x5129588403807481303801800003125103d0347c1d603040c401800061202c9502602c0c480d03010781750303001d08440700a0188907420314242400c101c3c24410a01c0c14010200c85140c40f80c0c41540584422003410824060580d40100352611407a000c0041402d5100b4000c840191380094005c500d04214880404003e001c03418068031480c81c280001700010303034015082210318944001d000000b02e46c041110044440990b442c51081e8903200c0e04024035180494020069880400002c5d12018a070802c1c40040c21030204040c0d038014900300c044100040075019600071081403031201440e0701b0300e070300580c02c07220159040c002058032130780104418a0890010900c41c0c4c41850b05a0b500d072880b290101402202000c800c07803614840505110407680710200307a903006075007402462254034014440342c4602011700c0301c20800001c2c803000d0f0000396803942150000e5520600c056601d2901215500041109a45070a8000d2107050a415145058060401580c03400c4491601d1603d41d0781c4161803079802481846a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 759186411 1250 759185161 759185183
    0x1e060207020d080301090c110709022a0706080a0911060706150303020d0f050711060f0f0c0303040b130c0b03100806040f170a080106030b0a0522060f0b0304020904 72
    0x140ca800c2c0b264124a80b01d01041c60f100c0d4113191442064401c0707041c0c1102041190700003003115180c0004d2003022501440700c016640c0300314502c0e014140d2a42c40b946403038070800069000e0f0301880001c0840c1190090385e40c62015071162500c2d0070543e0380da000b020780385228a144501c072903c1c3c00c00c010b161491083c1d00000308030707039150401040d41d0410360080e800342e00030443c042c0000f070b040740311040520b1491605a2411000e13a0b142c01c4008003000b09031707000740c00c04248983d0206011040300c4c0003252807901e4a8460049480c102d5413540210383c11210350602c0300202d0380d2941e1040b20030070940d078002c41a00c15141021281011030b00700038010150520f0036940003801c039006103d240c0c040d90148030f05803130742c4c90356003840a02d40b00e0309205501584404c0181c180103550145010341520340514010a805802a0000f281c0c4845900500d91014224003441203100c5400c07400404024101c105102103642d4440407850004540314012444400708000340040c6040440c00d84e00a100d070350700e800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 759187661 1250 759186411 759186413
    0x1306030b0f010905010b070803040b04050304030203070b1305010f0f0305150a06020f0d020c0d03080603011e150501050a0e060d060f032a061205040311120a090905041e060207 77
    0x80d8104040c1d403610940e005081c0180b080841e5801894094441d584603e8541a90780d6126801381c0302c0100080c0a802c002c0d0003103010401d0510455004580040403504002d444402c0500c6503401200344a481c3c2c441c0d05000225035015000c1901248260340f1400140c4c48840d03c103901038240101001c8080c0c80403260301f56603907074084002d00035002c60340c010702d1914000360706245489605980c0d4000e5511001c0200c08559900800d0490158546090350058680d8400703c0c0c05084c08002010704686180d60400e909070155100c5601804140c581c851744d645c0d90701c01501c00b44960509200003400783c0c0c84445081c00d14100800581040d000c001825542d01d40e180000d4820766007089402c0c3e108408140d070007211081210100310088013000d84c80e1440e000001c1c083d1a1100e03040c90085813100300003000e05000700495400c3c02c064002b907407103002c0902d05000d084c0e8850520500420510398020460400b14410039104591056079010411488100d0741004c071150807003120140c3c2c080280c03270 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 759188911 1250 759187661 759187673
    0xd091509060f0e0a0b0a020309031e0a231e10051521010609200414150903010614040e03390304031a0604090b0a02090f031c020f0a0c05130603 63
    0x14010006c2da001d507468040c040c0400d4101728124101030210303108680034008051022650103040343e400100003d240b58410342e5030706040000c0300e0750349290040c0c8166501c19081c441d41880d40c00c6542e000e4543e800b51405219003141c405039800a00ca52600d101d180c128145032841c40100c00d035030b07220700c82c4243c191002c0d0350948003a6005603a8558032095079424080240c0e034403d1400302d603084031a08050070039140798001c49503405818420100d200420101032905802c45107100e5029000740b00d41070300d0704114120405140051402070303241c81700c0040100c0000c02078401d01c0c6e040d1138081c14101e8145c8040040300401c0b0070120303940200100c0941c0070030f0f42000107100540c80380d2101000030072130403150401607600800c010302075414120b141000078002003120358480705064005072100e0310800070903111000e00c40d000e5014414013007003d40003c28044503141200541d0308496040305d82140c4a901c8641407100203084e4a0001030501903403506040d512503503a405207000401d07503a43c0d2918 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 759190161 1250 759188911 759188917
    0xb0f1306020d02040f230f1f1707020a030c11030312194d040611100e0d0f031b03020720150d0605030d091509060f0e0a0b 54
    0x402c50b810740c0000e040094005040901c4014403070306205042010360545900842c2001c000d54a2089905c02d4005085680382800c00340303d20060301321030380121030418015200c64101d038101e0b1140c1ca201ca0000302202d20000b80e410b03505605648103035000580b81c0d180304c80143d0b0701c0c10706a4580400d00411101c40000c1000c01d101d926018500380061801c1c589900440386a0708030036030b40401110094011140c40c5c1c402c11581020300503848100021040034440010124a0450300d2620001d00010503541c041c0d80c003d41060f84405584110181400d900100c46200b0110b40c5d02d078002c2c001d411007081c069400d007000c004440c180800c400c00c3c045c072081e403000700c40548840820b81c086481014403850300240940103003c05060404401c80200180890001074145241e82200090580c010191b60f006078000f000e000d012038901da05000f0000d08540518003c0300d03021088458903c80a0384180c10354000c40b0316a444102c08050b1621003190300c20803c800760781e0084643c0a0008101d0000d41c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 759191411 1250 759190161 759190177
    0xd0609060e06040b01060f091403101a040b2403040309030b010b0408100e190c081902240703030c0e180a18080d050924010609120b0f130602 62
    0x1800035480d003450540c4d0701d204180c0002c400c10410510382c600342500012000140c076220031040890b1890240000e05d010381030301c0d242000c40e0602980c0d2041c100090034480f03c24104880a00c59004403401b4080584000080c43e0300d1181070808502c1c04109060007140c125010346440701400c3c0c2c8a8540f03001c00182030b030100884090026040000e0841030050804824000b00c09111b2a0000f070011590b5a40f58030040c41207071148020481001442010240140600c0094448401c208951b00103030303004501c002d90140b01c0b1151440300f01c005801040b00d100000c2c048550a00f812074a017240100044e5060a061000640c1c2e064010b6513414206113076551107800394011494003244010585103150120200c0d003400c01400c4001860000550311810314103040058150b5400c8012803a0007035580c0361903d0b00a0a00b500d03c81048011440b42c10303500662581c0c075030155030300c0c40440700101480018128101c2400414080710310b9191003074001c0344c42026840a260180c071600d0490f402101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 759192661 1250 759191411 759191413
    0x70c0c090608150f092e0e010c02010608070e010605160b0a0c030c0c0308160504050913030215060609191d0103060b0102060403050a0e010504090603050c0109090e0c0d0609060e 78
    0x9142443c096106001a81c043c1d440480f044071418100d904903030b00d0b0f0f20b010103504546d45060180002d005041150040e150745500140030481d00385042070b0007445070400703000040d42042e10101c0d0f50706c00020a9011601d5141010509030708e0403030100c60a42092600e0824403c615890001140c06003a1282c00b60500d0b4a0000781c04c05540d801400329116100b03030398107110700c1340403010119401414403030b1302c031000042041c1c25200080d002c580511850700b0107079200501c1b01c20b000c5c0d07021003900e10410151298080381e00c803035400844241500801c40700168081030400c2441c8142c01d00135000703c2d0f801340041c07030f000f0b03660384070812403401040c40c07c000c3d41e402100301c00410078010107000d4220281000e0018080318200f9840003401c6118890f80c0c1e40034000402e41d2003400b0b9104604440084c101d0b040d0800000b61a460000e4550241128050004144031404030301c14010f445140142e0b410040203082c00384d489828440c410b03039001402d48007541c0d01c1c40d280c004100d9034040c14401841d000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 759193911 1250 759192661 759192673
    0xd0b0a0806071119150b100801090f1515020715030e240c031806070306030303050601020c030304090f090c090207030f021902040519140108071409070c0c090608 71
    0x24000030080b110090802d080c9911030a2451304a04180c2145420741d45c021300d01c82141c1040100c5035000d4801912999040107101c0100e400c000d6104003124182c84a4100c10300c0104030410038207058561146c5041d0104500366820004114020103102c40050603005480c5a03650320110701c900242400c000d480840d0b00d80d10280e050040c14402040c0480040809444282c1c2d0301d02e81103062a401001000560b000001240c807d140171241c0d8504900c00c0c40403108103141000300140584000c0c8001c070f02280c00c040c0410078940c008180c5000341507028005608003482d1100c000007070f01600b0803620b0ba059884500310b001ca940601c0e42000341c55024405a030700c2d050361600070303ca441c00c0b202c5030341103400202c6032109889902c00702c00c0045404031000f250603210003102c042d01100311808a075040d4544908100100400360781c15040b0f40c45003050303a0300e03903644040180d01c0903085c10769564890b030241c00185440340240c9440f10091301494111542c140c640009074103c8905030008905503000b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 759195161 1250 759193911 759193921
    0x80c01080601020f100b010e04091101030b03030d05160f020f0c041a04050a091214090904080906130603061a031b041e180219080603120d0e100c12020d0b0a0806 71
    0x8c0160b01d91a480162402c002400b215210811510820580d050401d501e0f600164059601002922800551400300b00401d06007034240903602030a91000d071010544488481c0c44240c00440c0002e4103061080c00303440386091202c100401407010307050b2003621207a41030304442c0c0c5403214400c1c1b0340b280f100b214000031451030a0820f5041d840b02083c1e0401040107060031490603c24141c02d44140d0700301540d558240351610300d4080001e000b4800c03542d81000c004204003020744506916035084500c0b90705c0401172103480d80ca440e030000c40c6881440715108010400b080c0c0900345040d665800c0c0c0d800e2034541d8107203515084002d10071005800d4400d05120180030500c401c13585a1404814034291010840c641707403051102100402e03a1039140d806100544000070f44607101030004201089001070100d0780c4142c0105044000c04040346038210a119218000742005a54407800c002c08680761506408800a1300301040030b5803101c3c940100c2d058440d503440403035440b800900c50181c45140b010b4441c83c500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 759196411 1250 759195161 759195167
    0xf07051608130905060a091808070f020a0509070f050912150f01080a020120010609020c0a0506010503010b1c11030d0e010f03110405010f03090804030803070f0504080c01080601020f100b01 83
    0xc039000b01e83d000e80341a05214075039031212803120840702c8030000031860001484030081c64800b40c07034002e440e4200008031030b400c002465403541c0030746108995940d1007075220414050b554030101c2d560300101d4511021040320501a00c040c00c07021b4002402400050014580d542c20030803011a84250702000905120f0485020b086590160000b14000d00070445290002400701410194081c01a2800c8a14000703501082d0031032405808440c8055507150328146004c0e56a80c103206081c0d4190003000004202c0e840e043c0141900180018203440702041e50500000c681e142100d000c480c50ba160b6500644e007902d007401080c000080c280c950101401d04003002400800f410100d980805203481802d50551061034192000d8a07002c0c03070852041c0e0040f00050b4020140340b80050420100403030000200044c450065205410554880c0d4444a00c517006880c03c0c01940104200e6410000c820116544a22081a40590144111410f188810101d5070401d010324201e00909901d8421103841560 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 759197661 1250 759196411 759196447
    0x6090c08060901410d050f121e0a021504030306030314090d06270503030702010621060207030e1c02010806061305122b0e15030f07051608 61
    0x895407207905403610740d008046a1072407400105032192440141c0c03000d13506000f111405621031002e00000300d110014140181c0d5401462020380152240300ca99190229605040d40d0041e00544001c100f80b0880ea511884150004480c001c11441f800b05803001c0710f8114000240038500a40b40081d0449c1503040003041101341c2c505081070000b04000e2050795444910708004810b4110000242d4035200c115120340d4003203011203060802c40e51000600922401000030f40c0036800e80e8000f00075959880d8001900c903141740c17986914420303c0070804ac0c04542550010145940319181c11300894000740c1c00100210f202c003a80340310100b000c80d24541196007250710250420000c48149080483c68100c0d01400800c41c0185030140c0c01800d4400701300c80007080780c1031120412280c5080044d20310021822010500f4038030310000ba41000c0022501c1c2821410b00c0d5442680c220340c6803440d43d07641480b047c40741c009004102001f400700300c41d103030194440c40b0340841d15100e6031046075101c1420820f02c0b1145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 759198911 1250 759197661 759197669
    0x1a211f090203010b0d0e07051512060102010501080d0c030e060f030a0608030f0a1b0b090f07050a0308070f11090903040512070509130302030403120c14060c1c06090c08060901 77
    0x2610401c0148207214002c2d080d03500400c0c5e000c5020a000060030012800c0c40b80710743c00240c1100b9090301e020a407810030000340005015016032100d455641d200124240c3c0c00a100c1c20819070414440391030710701d1061068482060103414040c000b4100030000c40c3c190f074041d0b00807004000010081c0400240d01e8011440208180e10007581040341e00a41c12402d4800c0f410a481400700c0d0140705103800c00c140d0302a04c3c005800c20420304881ca040e140300e54540e803140302c1000301c0d40180c5002081c01d1900800031006c0c5c036081206141010040d80d90030841d028800000d030344c14000113910f006a0b42c0d6a402e03e500c03030400a0040c54407940381c00d003840340c2004405c1a01c0d0940e04810300a1003507448050b4180e901c180d5405103098004460300b81a8214030403500301911541410a9201a0381c1d0400014041e041c801d02039022105600d50344d0940714032003a50f41d003198040402400c0072055410301c0d8104009a0f003100058400d942d40402812180e8110f40d120100c0c072542c0c1000700d1840c11403a114010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 759200161 1250 759198911 759198929
    0x50901030c1809021b01140601110a150f0e0a0507080706030e06060402072102061b031006110c0d060b01030b0d0b0f070e03190501151a211f 62
    0x70000c0502e500144255405008815940440d0980d00107a00d810070380c040c040044020028403100301c003440c1e44c26500f00c8166000c505e4038440c0707120341c141c005001a0025007240e0346140c0b003044034000c040a0000910724910a6889000e40b941c2d00c507060058800301841800141035040ca40180c49040900d81e6020100f40740c0342041d8406021800304c1c5080c0d105e1001c68005a50700d8080c98100340e05036000b407807a44003030f03064104002140d40006515001d0002031a030750080010102c030800d042d2100721003104410200c0141004035600a240304052801c3c2d0805845041e4903042c04214040c00e005016502d032500e079000400c5a50301481850000c8605440d142c80d1103c0c03a85038116014005040b0080084860000a00302d0b0311403c3d80710a03003840201034031201d9032030021000f43d03c14894009c0e40e46502c1c003000240110745d943c114138101c07028039405860320900e2400311451030f0002d40d4805d010b8451000e000880c01c000070b221a10440d410355180d000d083c818400401007000075000b280c0c0c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 759201411 1250 759200161 759200177
    0x30905100b01090f0e0703110315010818010e1c0516120e060f0901021005070905121e06070201060609121b0906090f0f090b0408030c09060703050901030c 68
    0x82000450402088155014003094019400c40100c408204a6000c40141c0e03140200210b0300c4c00c03040d00102c0c0201c50598003482a26104031982800344000e6840d040c10620800000407254024042c03150303c2810a00e981081100d118025401e540c3c1050a00e22640c2101c02420200844d9030211050351031985011030601c1c00380a8145100452241c000e0010800a000c1ea440140300342d1742115581d40152034143c81300b422482e90300b61508801940c90140c02900b00f0701090000700d105851080c55240d49560038245008140700c0c4080340300154611902a41c81240000300f01d4030002d071020300c1c008006084030310305540000e0071180039403c00c0b02001105c8008100300415040032103201034003c4245442e15100401c00080300d0142e5108808490501c41c000940d110705500c0a040440007c01c1132080f01c040d00b420030210307070300c0110007401040d882c008a80402d1482c8043d50380441501c1504d072402c0f0204c80054015000340e0070490024500080c032280c03a50703040c00743d140c1d84002c0c0c0c104200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 759202661 1250 759201411 759201413
    0x15030b01030e060408032202220b0d020609010536090c07120e210615040b090403110a0b2a18060a0c022106061f2d0903030206070309 59
    0x500c000ba00300c810b9105180302d040000240c4820a090b03a6500803ca1750389c451401e03140e00c0c905c0114014001103a898402c1381081400e05003103c5a059600410341c0d46404420070043d9056003008292001404140c40b034011511407a484400d181410020020000031140b0b00300000700000400803158504203000305400122a100c41c18010400c6080c807801200101d40421120b5450802d110200741041c4108020000b000c50844d00640414400c49200048402444140c440c0a055190000382110000b40402e210314002124a950380040d1015158642c40302101c001d0141c03002072041c22032080021030560030175001110042d401061505242d28845401007034502400000c0c050703840001c51021080c8980d0b0500c0455a009010510a0050007034800c901d007000000c001c05442580007191291814150310007090040e58802c401982008100f20f808141c030201700114038140301b8950343e41c1c480d0b4200314451444c003951070103107140c91420000e280c541c02400b808103151510140038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 759203911 1250 759202661 759202673
    0xb01030825030e0d1a040b0f01090b01020304140402120703060e07110613150f0e10060b03130c090c0302191409010503090c06040b071511070f020a15030b01030e0604 73
    0x3110b0f404084580c10780c00b0742ea42c14541210a412040e002a40042c02c041104000b2140711150044000070800320450b13885400210480d401d010b2030038003587c81403208204840900d4100c1251080180c405800c00d8030010041c84080410f0700e0640210391074441c00d108403032500140603401001850400d0003103202c0410340313071039601c0540000081c4e07131801c50280510588841c4200d02d024255006c01080c101001c00500900c004942410303140281902d0000013245801502c0c2a28007400700c4520b1611095003600c52248148800c89500ca4110000158640148152000007084c0e440c090394541c0301401540070180c0200840381404a8002c03584000364041c400d40380c4884003070078907550340d0f01e0f6261007601c1c0003031380361050343d00c01c40c002400314a60550401400c01d8078466007070003092606484104055880441070005211014015400440c40704250090490f001411030140292210a545124500c6290940c086512243c0103101e5507454498191080305480152103031b420705d9910f41c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 759205161 1250 759203911 759203927
    0x330330030c030e030423030303220f06051e0f07020d050918040c1d07080a110705010c0917010203160e01141306030627050c070b0103082503 62
    0x28105599040c000214074000e03030010b5151011441140d071079035900c100d044010400e8040f1101034608a40c100d55140c1400020b40c1d000b203000000140100071103980b82600e0202280040d83d020309480c48110100d90284526030050110500da9040c41d070f6030000714088500c0107051800c0c020150b4080004c07443e40800d549403c0c141c01d1130328a0342c40c440000025041c0d10b04078609028000c03044107200c20410201c80403030448030401c0440c940d41241a44028081404840501c0400c80b400001859000f26030300502c1100d40c004030003400c1600035214a0b00b11201c142e40351011030300001d814000300d2242207242c03003070021000003545146001d1064480341d030311000a807400d1000900001066a00aa10b807603136026101500e9525404844003180003c40684a00400320385005004600c0580e0080000307601d1156041c512201090440c0c83c60003003070002d0086182000a010a0700003408680d4194000c60068608685480070344010125114400d89642c01c68941008100300294101010b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 759206411 1250 759205161 759205253
    0xb0a1205061b07020a12020111030301080606060319020a020a1e0f080d091e0b0f1611010615020a050f0a0312050a2a08283303 56
    0x2182c0866081c0555821031800b0703042000b544440b6070328010650a82c1c55440c850828001da0342d8809e200703050064543c4a100a01071480d40f900504002055805d01c0402076410032108081c10b0002e40d150a0706008036040b07642c2c60001a00703c249400140111b5450711158820404507100c0850500d91b80d0445005d10404024815940460071000416681d481107001d59080b9143c0000c4600203998101240d4000b9003c55100d2107c001203130030b02020715040f600c18411002500c2c5a010004006e1358645031050200d40c0303e6496030ba000c28292280c5c0032070400d045064008102c3e10b100c902c1c01d80c0c1000054035400d1480e521114894012981c81040c0c1d516211141d50001040e4440243e0980a41030380030090351405241c0d003905050f40505a0001c503807030317540d40c2ca0f511a6220050100b198108007001550300004880203041140d0040d8005210542444007513111048218617040b800c0310118001010191018420014002145035400d6207000c8241c40803c90800b00700b49180426503100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 759207661 1250 759206411 759206431
    0x405090d08040218091f0203012d030c0b07021509010e060c160b180f0105190c0b0903040e0c0412060b030a0209190c110606090405150405010b0a120506 67
    0x100b425520350703801800f10030406074550855480c0a0401e140e90307003001c030308481507000240350075a40260302d8800c1c0c0c1e0598041000041d0961048410780221300c05e04030b0380c101004c90702100040000e442d80d50403001080a07840303032600d81c000d0b40100b2001900850403141d004e04208056549030b80c0c001040b000031101201c1413600d80c522488194903026549030049224041c3c03070701c0441c0822050025180c0d51011a0492103044184400c3c042001280890b184c0840e000380f19011b150940840708480360aa80c0c54080000121911380000017501502c0d4040d55400008041c030440b825a0900c5601c82d5880c1c103c5d81c602840e01041089043d8001c3c005401c06a1320f00d10074115a0b0144075017503c1d2070f002030106035941480e202c100100448402814003080c03520201800250040040034101c685020241c50f00c0d0391000c0034412150402030080320300e0300600e0003d1886500200d0814044c2c0e01079000052402405414402405040e0304507403e4400b03130b103480c0000a0350000340c0380c0c1d204203252 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 759208911 1250 759207661 759207677
    0xc1008060a2c07021614090106080619030f03030605030f190618110405070201060501090b090103140a051b0c0d0f050c010204060e09010b070b0c07031209200405090d 73
    0x61154120710300c42c0001c464500d070485061080d450390028210b103414520300740490015680300358411206642900c0d107900403110000411095018400c45580078202801c20700080907000c045d1040c2031240d810860364040d02900202c10700d503040c8142d1001e05015030061651404a201883e9030b8104034030301c100380c4100c00700b0b000c00b044000d40110080354503030b0f00034800031381f068500100403e040104403801207280100041103d1700c14050312044a0042e160002d030241040e49003003e503030195003054145038a0b5a0110024550008243e2107102406c00c001610b0620700108003c0502c1085100000d500c180400f200c00b28003c104107020100701d0500240a49040000355414054044880815407010900240d52900048a030a131040d00321030780f2a040e80c0343c0309138030883d010b8502c0285c121707012400058080000708004124450203070611100c011040048081594010642103034221916050000030304644445554404c0044074103200500d404815560340d559100700f10004c02c1680 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 759210161 1250 759208911 759208949
    0x10b0316020703060e031c0c140f0f1629071b02030d12050a06080a03050a02070509100501121e0b06040801020a020102131a0409110d0c020c1008060a 66
    0x2008110015039010f8005c0c0540110080400c1d1a80c101c5080100030704980950f07042e030207420b413140c0c170b400301110380340d20310941c40c0c15211000b241c101c014042e642d000308000d003450141c980b0307018001118034081030015800c8a4a0400b18264a100c10548404000b0b1003101502c0c1444052650140061602d14148801c0748000d4040e601d0a480c040c1d01401f4500b41c4040c0d859110804a040f0141045c1c2070000f61102c200e044211402485940c801c3d801c01400d03000003d104c2c5d00144110001032044034081602c450004101e188152160034280b901c0050400041d40c03c20b07550134036102076000810141d1010b082134100410341e00d222041e1a03a030f40850300d80030381d144070658015040d4000219141c1d220310a0280c000e5010b00c06943c3ca2070280507002445030040441e02804600051004d400c091030101c1c5078010340707441845808002c1d0b00b4080c1d80c01c110481e02ca821140d12080e40101010807901c0c0503c89038100c2d9000200401503003900b0001036032585402c0800b195060401c2c01645014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 759211411 1250 759210161 759210163
    0xb03040213090f172215080415050c0717071502030603070306050907051207081f110a0f0e190e0403140429040311130b0a03060f0f0203010b031602 65
    0x31090040c0155145050071011100c5040540303041703098004420803070160404c0300c0307017480040e101306014440d980a000782400c5c89248441d401500c00d22110b140f4040051031101070f11012100e0000c82940403c0000c1400a0200d508540760710411400385800010713101d00c0866644d5400484010790000040380203a101041614010750b04141b04001c035060081082d03803511424032440c3e208411500031840c1096010881504580200f0020a1010300309005440d003008024012150165904c1080003c0c41c5003100903c81c0d401c541c0d803100c40901c0100c03409020341000b881c00500559500111241d1150107158200560b070b68054420b406a51318a0202e81c01c0c40300300d40984a4240203d030000360034078080c40f02961f03800e40500030b41c800325101d0100f132011300130341c40302410040c01581d1103403a84c103014a80400154018001045030f01c0d003000898802080380d0b00440d0075a680342c0c1c0b039014080c00c034031500b160002c20f5002907103103501d0300d0308120300c03800b0241c802001c0480c501c48044140340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759212661 1250 759211411 759211433
    0x9080318120a0308010306052d0a06150f03060b030105030a0b04020d0c0f140303030606030106111c050c0106080f0c010f030b10030203070e03150c0714030d0905070b0304021309 78
    0x10a100403582c080c00e003031800030440e120130b120807292507050401082287c560030b4440c0004a00c101e20302010000d110701003103000311000d0244007000d070b99141c3c00309400b010b030841c240c40241d1035220280e803179008100081c00c580c65503105140343ca406000500041c0c1e004138075003101d60b0300a800c0309000d4540e0300019540d20310303c040042030364810150000d5003100e001c200c0d40c04c5440d0702080f84034500b01c80d0281a1680300485034581c0c800b0003000103004003801144003034401070010b0111240c0703404544800c00311070b9110006801048010a44511150003406a240a0140d0401801030f03c51600300080d556988069054140502c0b2120880f46078441ea01040e032122009010780d80e41681991702074002d41c0f0503a0742c00c000621000107032820b818006a110503030680e00b402c3d078084c0d1390398544541941d0005c210880d01c86c911110315581207102040a000c6c4d04c440120001403c1e6140d02d005c0c0e10784951584010f01e02c81e028020040503039101d07800001696020700700450300501c18544010404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 759213911 1250 759212661 759212689
    0x21c020f040911040230040f0b04050c030d02101a03030409051b12190b091803070b0f07020606010f020606040b12010f0c090b090a0b071a09030a03060609080318 71
    0x14408240031342da5140c0240b643e803035415181b004061440b485029441c00742000c50b4041c00d1408072880d220002030441e2400d550050061068509102d01c840000c0d0070813140b40b80c1c44005030300046a0727a4141209100b007051000220380740d040205040c1020039105c3c09a0f00c502c2168940c0c13040055111002c0c10b205545034025580340d95510801d4003403070800c1d10702c1a140940e5600050f89620320b000c03000d01c990f070050000102142c0c8155108072811000b2412103082c0701c01030005001c00320000c0c0303d000000c2d0080844030b4500c0c249250485000b407800e203000b0407050410170001d8001c2442070300414080d17000242550041601c60380d840c04200c03917103800307014120190318108040c0d0300940b20790710881c40300540717966082000e60b481c0c00d0b400840c010710b00200d80c0400328020820000320004010045588104402c8050303010140d82904600d104650303400c115003000440240c07455041c400c00c4c0c0a0144c034140249502d0904604540d28040d103403001c00540002e81910700c40d076503041c44001d60340d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 759215161 1250 759213911 759213919
    0x2030403180608091207031b1e080702311109090114010e0402090102030a1b0b040302060106030507051305060d061a0711180408180a12021c020f040911 67
    0x181e41d42d02c0002e0006000f159035458030300070001048041400e09007181c0c115501543c8038081181500e40c91080100d102c60200c0313a09000c44007562085101002507080c260107031b091592145654010701c0f09890490b08030414604411004080184090100e043c04d5500030400040e500b18151040d030051240b000d4481d0300190000000451404072100403200040a03654401d400f41c010080c8416405000c509078056001402240c070124810341d00c004d414104205d41c24803e01c01900d038030103810000c1e81d00350016002a030041c03084030381500070950031181910f4900c1c540b1114406045c41e0007154044d41e40f0401d400200100c0c8020190011005000b24148008d880d220181d800c010070760102c1000c0741d014041707603442c40300d900e0065400410441400221011075549036034141d055800000349224502540c0c003452100d88500c0d50080c050901080c0c500030b43c0c02d85004009140d01c0c00c0e0100503882201c0c142c460016103a500310080d8000d002e4901142030b500713514203010072801000b011600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 759216411 1250 759215161 759215207
    0xc0706021e04090b090921070812040201021b060403030509060913201306031d0f0705040501050603090a1e061e05010618050d0309090f050105030706090806060402030403 75
    0x8920070800007403040b603c035403e041140c1511901403144500003126007020729002108510090490f0714040180401c2d01d02825283c200c1076502d0700900c0d00011225100d0b143d10380c0421046503010840340940c8481c40e210484c2e04855980015121320450000034100070b4007140c03440d0f942d20b0301d1007501c00102c1d004024562002410380020020800e0b15100002e14002c1007e003840d141500044407520a121907040d105142011403d0707010700034000c0c181603403001164180200c401d050003401020488500585000c514120401082d40c40c1a00a00e1140c503080050040c0c40f40001150b0041a500c155580f144d1100c0404208083d42805400b80180d42402200444810201d80c0e1030003641150340c1c20841640c841204032480c0440400060342203007011028001881c29900740c10196202e4901040c105440e100320030b056a6805042040054440c07005201b24a01030180c00b010b000c0c00e00d020307041ca40c581a5400c1d543c150103480d00340501d60000124080c10700c280000aa8201890480e4035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 759217661 1250 759216411 759216457
    0x605090109060c030209010203070b060307030203060a050702100e0c010c020a182c060c030c0424020c100219050c04020307050d0c0309030c03120623040f140c070602 73
    0xc0604010340089070b01c80d02c1c200e80010058024400c0d1904400706a00550a102c540d54510548003400303440d42e036252041c09000001a40c3c04c000052003044450008102800c101038080e20b002921800201030500305500c4070406400041d012007580024600304030507054038004100194000d410095106440318141c00e0284060340010000185400803040d443c085030842511401c40e00040040a81004001c01d000c0e040071702c09560003840840341c031458203580d0348986010f49218100c0c607001e650740440c2c1d1600c840e0144040d0604010944034271201007400e100013901d58501003012942032a103078a41e2000d210b810088481080b601070b000715600d0034404005421074104415a203c40c60070005082601c900c2402203a90305039060b00c94400d4001240c1c3c045d10415440000c1c0e00c4680d94a0b4030005410280c860041c80c0d201e10030f2184a40c03980103100703020907660000110300256040940391a01150321001080e0311184424030591124010f00c0c101020b0320601120b5484d80c600720358075007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 759218911 1250 759217661 759217663
    0x30e01110408060f04020a06050705150109062d05011103070204020d2c0d1b020a151719021e030106090e01051c081e03010801060e010501020610051507060509 70
    0x181d803481001c42c1d14940e11040c0c0e00d1413948048400a41020a82908000300341c0a4005800392512804c00c0c1c484013030f21410200c944c03103001d900c2488400c0e01c07405d00b00325211040c8480d445d100c0180f81a8000351045440f0800d009456200d10750401002c6542e01d8000c2e40c060080c0c5902c0c4d54000c106542e0784a504c00c0c944003500101000e040e00315610f80649034003c41c00d0008080f0030303d000001e031004000c610f0040c0c1e0301c414107502c4201c21131540304040700182d40700c80001c40989400c003020241c2810b058401806103101e01c2e500c200f95009074080c0034590400f419943c512250707025015076a40064542905d0802c40c1c3c40441720300100100003c0f0b01150441c4081041d2085840303200c003070b40c2c1d0b5181041144040c5020a144c04590340550342c001c150040010b04202d14032105820000342000007005680e40309a12861040e50b69203820b100e145000c01c90203004040c03d10003001c41e8106030000c40840c10086c807070a84940200d01405032170100c800252124950000310802c6180340ca0403001e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 759220161 1250 759218911 759218917
    0xe0a090603120306060903260403020319052401030f02030f030c030a0f170a0518030703050706230708100506030414071e053d020f2407030e0111 64
    0x42d0010a0400e400072520034411413034401100d030401105040001c0711303960740c0000410607000542e5000d0810002c80580ca0820900c0d1004501041d010300c0c0407060304000307042c1002c601d04541d103040c441b001c580520074464401419031390445040e84014040340300082c540561001d1198103408082001f072520b0002001078018051191107440080c0702c235100c2204e005000c001040030710b0708200c01007480300c101e687c0465404003807005a00703400013500014501c2c580005104030001100083c200c4100140c500403007481c5280b00107440c28005c0f40c8a0019210407000305200c3c100028100001d9000420b0002200140000741045690b810141040a0144000b4111000c5031080d1280002d44041000702840e00001100031401094140320800c41000048400501a411409108403001000d0311540b14580d03000c0041502c0c18039041c0340a418609411004000c54000d9000d20608000f202e278940c1d01400140c040b080c5a40d5204420340082030042e404050541c40c1030f02d5101e604c02d001c001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 759221411 1250 759220161 759220193
    0x4020f1818040506010e1b0a0507231b24030a020d1409011d030313050a150203040c1211040506040e160f0e01030c17030d0e0309100e030d0e0a090603 66
    0x6410700a40d0342c104154409103a401f051200d641c02002a000d55501c02c0001c0c180180c403403e41e0800ba5820580c0c2201901c1c1c024a0020107038019095013070404015503030000c50b0500558482145103014500303004103401054481038801030000002d07001c25000c0d4100c80e14001c4007041005000300081000e22450000c4501108940c80e01c0080b00000c10b1800d0042006540303040194915560291000c4403141180f100b22594030401031002c0004e1548a01c4034038402c2c0c0c0311001a02c0e440c150030004c0c03041c0c0305030340410010032070100c907080400c41004685d000b0070800d4a0101e595182c5c240410024a00035021035100e000c0c1010f041085161001e410045840121480c40c9543c0c4a40e80000c2440d0b007840006d0a004070000704120100307907807401a85a444c54010340b400c11189100e44001e5450781000c07403089400008500d81d5503c0c0403892074100c4240ca1802c03660201c02c1102180d903401c602c0c14004244400c04a00794100d85d034032900300c806040e00d0744003030040ca0f50304e1424898100480e60 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 759222661 1250 759221411 759221429
    0x106031208060f031f140f04110619080c070b15010e0415030f0303020f0a02010f0f0908090d080415050301090c05070308150d0c0b09030c04020f181804050601 70
    0x2011612074a82114003c14030b100c010042c08515000401140700a103400360006912600c40400c00c504840750780303200303110328800e1510804a02c2c7c14900408200c1202c42c03a203110303d00500030080e14280c42500b402100155091502241c0c82d0b150000c0543e0041460060070318004804100c90001d510581000c55902030701c80054a00c0f0340402c00c419990f504221002c00c8140340302c100080740b50a910310343d126009040041c94500e820b1500d59059001011040250703440d403103048a0060544154098100018030800410065541c0c100c2030380701e05070401d845140000c410009005901c400c403001028111000103004000032005840703500f0922501800c00c0c60080700d90400c900807812603068540c160754185040e071350290382881c21a1200f1521790007950010000c030011b110b180342e5001030f25540f071140c0c1c0c45200384810907240205002f00580124010320402e26202c04880c03d4400e4500c0481c2d8143c0d007c0e0350040802d41da20000c052045410752081c080c0428030201140d524183c410044c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 759223911 1250 759222661 759222677
    0xc030a1d220605040b010f0e0402090d12110c060403020409031707170f06010203091c0f0b090c040905100c0203091e0a0602030307080a09020f130b0f0d0f0602091201060312 76
    0x400048405e540d104502241150b1441c02c0c00c180304d162a409903030070080005040000501c08105510f1030390030201c4d00c200310381002c8944190050740e0340f03040f80300e09402040200301410125034540228400240240c4d140e0740520308040c003560100c1140005041290094501400c00800070f255150380108104070b07080106c2c1c411094000700034070528040e002545048049028801d000460340d041c00f070071000c0504244009481e04000d1220f0300d020710b401000904041c501d803401c20142e401b02c3c500c602d1a04e031441000480c045000080c40f1960080090030364584070040e400c0d403081d8192258880400340c9107140340c11714141d01c100080c0c000d55000c090562244000ea82d281b0007594802e0100340400006441503800e500a0340d66944082c11412600e8504d80214290300410406910466120043c540260402c0c1c0011325408408440229000c14251100054000203030005011035400103200c901ca034441c151848a041400c400030020103650341015507086080c00080c00005010f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 759225161 1250 759223911 759223919
    0x5100c0527090106050915040806040c060f0c0311010e1e1203011a030402040e030a080a05100501080c1b070303050c0106060c050c042004060c020a0503030c030a1d2206 74
    0x4042680040d450180c071144a0340d081031000d40e020380106007060390195a4810302c491600c0c41c0d00103840100a201d00412b120b0500b07141c010400c035100d801c0b150030828110440e50110764420790000c000d48c0c25090109500490341c51050152210340c0e0508010b104400340c800411005191001102d0340800580d02c0803008005c840d221032200388503a0a5104090340b9551842c0400b4004540191000b030000505400642405055401075004c500100d2441c5007040a200300500900f60b0084040031500c54107410400003034a460781c09040c1c1c0107a030784085070602c0141418207901240c100403504030341e02103503607160092003503212880300c10480d424510005071490003208640512a0310030045d183c000d10101c2804018490000141c01c04103075070082e86c0e1101942d1004202902059844000c00c0130303180140700c0400c5c0d890740824040d41c0200028105400d0200135a01c03004003e141003103a0411001581c400182140341a0307501003420744200d210304524030701003400c54402c90400c0c0103260f51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 759226411 1250 759225161 759225217
    0xb1e040507080f07050c0c10120e0118030e0301110408070906140f100e041104092a0f0c06020f030901051311190f030308090f0706020a0b0405100c05 66
    0xb0603200181048419404680103034014400703000484140c03411504494020380001d140203c440b80c00d50701092409914008041150103a42c9800c1e003080000d1114030040341101c2000c84407524041e0800c407800884249903903080d0001c013038000c3c416403000d4441d9228414161110310500c5040c00c41031501000044001c40f50030400c81030a401451320b2840001802485068040c00e04004100002d0001d0078810f6500d9100340050011050701c959295428079400804480c5880706003650507202101c00484100810001800980a46030001d40c407842104242c40c01006203c008103050300200b1000c483e85e10381c1001d98410004c080083c051a1030b614100042020540b10142c59100d0649000c51306040022101d4088400e002190344616501c04143e000390f161a00100c000030801000d010440604000d4405076480c00d00161800314074144020b50f81e81a00000142003211280004052085c2405250900107a29800340b0914003005401041640704420040e03148104075089482181 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 759227661 1250 759226411 759226427
    0xa050d081906290c15190b06040923150406140f06250f110d020a060e0a17100c140d05180a0605161805060c190818060309031b010b1e040507 62
    0x50042e10231490903007030000e02c01c060310800e0320240b80080491308640300d40c0f0400c0c0c1010701c07a1020032400510f02102c1802c0209880c05640408240301c0b0901c0503440581d900304c9005114842140c81c190f071411000300d001481420b2a01001c3c40d401046001030034000b5900101d40346500c25074000303143c4240f0204000c1285000d4001030f4020fa1221004d00c1011b00403c800700401d40c0040948405075500d241e420050101a000c800407038000b110ba42143c802640251854166a41440c8500030a5130140101500580c002c03041d190382c40700081900d81409451084c0005071031000d4031050380150900720058039040d1512031000084481c3c842c0b48a2081006100248802980c85082c42ca00010805e9075040000e9200403070240c0740c28509004041606205c80c1e40c4911603003510751a1000111042d01010050140211000c100300320314030101000303c0d0584403c3c0d000040707140e0808064580141004600550480d406c1602652a0a00b00700505a2008221003c1c00955a012000c407040c0c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 759228911 1250 759227661 759227681
    0xe01050d02030a021c050c12030a0806031e1005010b1e21010e0708072a051e0601090501150c0312060905011412010204080a03110a050d081906290c1519 67
    0x60010f006004ae41d44c03140780724036003101c0b00408803840340d0f440038030b203084460103032540c10718682c0480c00003c2200510700806004115401041d41003002c0c0710300c0000c82d00008100c84400150004e00341c0702c41850b5802100d01d800081050556640c0c45240423151080c0130346240700819045000076004610440d640305041c1c070700b8001e000e0124000b0104071846050844102c40c180a200c4041c02409044d0381c25810044190004065035490100050102c4406070440d61207612240030050202e600034034200e031480e60520b80703100300610040e4000003c201540003880703840c5c188400007440391041c0754181c0110504588a48010307400038515403c1340b02d1403103441c480f60401010341000c01e0059a000614120400540d00d04c1101c44d92040c0c24402030329a40740100d6035900902c0390101140c12070f08800c0d80201c008001417410400024540080d144140e50490040080b00300d5441402055035000d0b9440302c210f489101c2c0010a681456100700c41e201c1f20304500450420112800303020b026034003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 759230161 1250 759228911 759228913
    0x603020306100b041406251406060904120201090c06050901021213150215070c1718060306010e0402030112031e0c06050402040b030f061b040e01050d02030a021c050c12 74
    0x1502d809104c1701500745524440e0f6003c001800b02c50b5180e04178111460500364599a010318054842c51709003504507c42c04c1040b480e0f071068080140c2504d960443e070381c205800caa17401c030038003107012012409469444c600811004510b140040c4168014010f0325100b07109800361002003100c40c0d0354812900400405081d0081042d10420403030170030800d000803481c142d20583e02200680b25419042d9001606d0304400210010404414081d461202212166056610614200074160380c4105110b401c2061881805c1c000003291060b030003000b41d400005005072082d9140d40e0341c0c1030800001038240b02c1c203502185180325904803266035200c80d1440b00b001d6840e041c0349600e10b516404000c103c0200f0880c0c10940d0b034040d41200d03541c1006480c152014400081070780346030100c1203044a40e85550b0200700303414140b10600444107444400e0781912802e40d0400c04800d114000030380b50013041e42d0003a4000540a046401c0c00d00d101104131003080c0a042254000d8046000b4407101c110b10f40215034203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 759231411 1250 759230161 759230167
    0x70b07091a040905100e16020c0402090112050919050309030d0201061203050f1b0102030403120e19020d08040609140303030411210f16080616120e030d0603020306100b 74
    0x500c0340f160300030741c0c01680020007191400e848000400d203080e01a00c03c0034050070058001518203030704008103400100c0030f4805509080e074000018100304001124525019140c4000500400d0100262043c1e4003441500c80e881c000a400c06a49a0f0f1000102c03e000e40118111020001d00500401e0220b4801c0700390458600040e890483c4c4c0ca400c0301c1a03240d00404208464000da42c44c00d29148000c1d12114001030783c90400d442c020701000c0110418450040c01c101010030080408503141d00d00030280d20403c1810440f41c400100302c80c489e208020000b64000c6400f1440940c4100030405889050080c581400d04060400d40c2da07000c1250001c03c05490390807a22468280441c0d201c100022582c0f1080c19040350726900e90034440030201c5a0065480922007801401600840c0310041c4030480c090440c40c01c010700904082090071031000140144c40406004001c4280d00251f00b50200a0940e610741c250209030f5000b9000307511044c1e20070710171040460a42c0940400719402c4501d100e4049207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 759232661 1250 759231411 759231419
    0xa0207060810031b2909130207060207050706020d0c11040e1c0f0905090606070803040206042d0b090904120e190512030708090f15070b07091a04 64
    0x415000040c800d6000b040781503000070000318144802c01c800741a500a04010600300555011244d0407080d03045070801c4000391140ca040000d00c00c80b000c018050351a422100813061304a00640319100005010500c0010844140840030502000b511031075403d40d80c681044040c1103540c0150450081c02e480f83e0601921000d180c151f1190070002303078100c240da0075040b4100003512100642c245400c0030910020a0502c6654030403d1080589000c4a900d60b4900b092000b0900030b000380321008052080010100342503542e078505940081000c0b1211b40b52500140100041800400c19040c001c100c4490000c546130b4000c0d82501d240720805004041140c7e5a91600092110303034800100503c9076841c0c8101c400c0c1c03505106610054120340310400b090f440c1030b05220084104460151990700103000a0000800903000ca50403200100c0c2c4111003a0580360004042c182c10461403028071800080000c1089810041c882c41001592540403038030355502e00c003041c090b80300c5000301100602080144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 759233911 1250 759232661 759232667
    0x130605040531030903080a180803040b030f060a17070801050a020a0c0b0601030222030510050121050c0901060f0201050702070501020a080f0f030c220501090b0904090213090201030b060a020706 85
    0xb25001e00a1500000d030555980b130780d40e03441d84000c000c14002980100c3c003405840503012400001c2509000651400f4070b0a04800818040034011189000c41d050116410b50f8481034044058140c800224000c41415040a9a50324241c49001c0f041e5090100240c030540c0035200396510091140c88156054440340c0e0703808010480203096506143e0300b440892159901c3c0c040b540081105592143c0300305042d410298075107071300303810b80400f024280030050081c4116580c80d410360400000400d2502e102620340181809144c0b0b1aaa030004005030001500685c0304640c40e2240c2d0898000300f10f241c5400c103040380c030340308540103082c05a800088001c2c00210360800525007070703002c5004a81004404002c8202c180c0c001d54603500c07031600105804006401e040300c085102c510a903401c202c5146000c0010744001103c0c4a014032110010840c034030b0544458011014035680200000d21600041c69800c004001442c0180d002915103084800541002000c6441d4640c0c2900140a5145004022 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 759235161 1250 759233911 759234001
    0xb1207140f0a032a02070803040f1a0c1b1e0f011b060501080307020102070806010806070c050a02092d0c070210200307030f18030201030c050403021306050405 70
    0xb4070416984a0f030104c0f0508203030780542c2401214520b5105068a01580289016050b401004d0f807038000b04000c00181c1e0088000c4022a414100081040c0d007418400003428018000a8226801500c0801c60302c409280403281d05800122070707002000d40c00005c22600d4000c40702c45143c01c19038070445a800d075030080300c4001c4107039580f10544010843c01d980b0001542e100ba803050300c60340d06c0820300204642c0c041c811640540400c0d0000d05003589001f04a9550341c0024054109000c0c0c2810300b030050040c103120400829402420f41410750400180250b403030541202d60003c1e00d0108151607040c03040810304240520380025240303007400c042d502003100720780300c01081105000080c3d110b81510242025003460300304040000d16121801030034090a1031207411842401c120010007405030850f140d40c42c0006032034081c039002589200c00d42c0c0a50300c43c0704075000a98003080d24003202c00c2c46091a00001c0a41d441600c01340403d845a520000340100c800000e403404d11280b540c801d6800c1c0040200b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 759236411 1250 759235161 759235177
    0x120c080105151303330509010c020d0c0f210c02040e010603020618061b0a0b0a0903082e0305010603050c010806010503011802190e09250806120102040b1207140f 71
    0x1100c0681112400a20860961000c040105c65215000c01c85032040a00c40c1d1010382541e40040c22041201400081452030070b18802090300304580c101d842484014204444541103610406900032036031100038021840e1950101d20a5051080811000c079041c0500811254090076640c2043d007090741c0d01540341840040300c1d40120052146034088000089299101c845000245c14041100e04150074120b00041441c1c481c14200401800002c0e4041c00a5611190307a41020103420105001c000540d0107644109052802e00706001c0103100040d4458400c0301c1c0b05500b02c07013070168254015501c140013229094003082060004001000d0b14000c0d06aa221010313900524080c0d200c900d846034076110980b480c0000300c81820799055414500030f11038101000c1075240c45a40100003c0301103200741c01442034108090343d00030a0041d100c24000100d1804078100075510346859260020803904240080c800c0b0514110100e45240d02034580c8404000861410b00e29080c807040080700303940d204482c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 759237661 1250 759236411 759236453
    0x1e030a0804050c220b0d0206040e090a20011205061012060506040306050a140c03160915230f0f03151f020114100302010807120c080105151303 63
    0xa01c98540d9a03200c02c86092984504d10445031481484180171104160b1509008090400c18480036907100c8050b1021680400f400301c409a03a02c081d1141040194003000300f07080140c629030300130a40c5640c0c081403503c0c0280c0c1d408142654007044c40c401d07214151500c541003030009003010320380c6110b0700c440e00c042c24807070b0fa002c100140d8420100f0079581c0f00f58070507034202c6d81d0f50040c0807059a0b40e005a102d01000c41c03808034498240b040708807095102c05044c1e20080a404c2000720322842c01030310050020710000c8800c3d5540748410101911100c000302c18562107100c540c141b4011581280d056030700104c001c484150900d030101c18044801d901c041c6c407104400300310b010004415502c00300d202c2d1030890607004600d8a4891010f01900f96564520050306507600c680402918a00c1c034114001100e409183c00e0440c0d888058059130045060402038061a0900004600094010714031904942c02034840c20b008604220704002d1901a10402c642c0070040300c081000440d10110b03820a1001c0c510b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 759238911 1250 759237661 759237673
    0x907110f0d020102090a06030203060a0b030612030403050a1202120403020411191e050a0e0402070c08120a021605130b0105040518040c050909032b060608091e030a080405 75
    0x30846441c1440c400000c00050303400149010b080c4c11b05241000081145003810341c11403d02d03600144000400d8043d8000c810790202c006940d59a800f001c1000800207501529611a10b03824903d0302e88040d000251845890500300b40300d100d20004030a03207a5000380480c40d050034115800c03c40505002c140740044800305100d02508500c0020044280c41d01d5900e440c501080f000000c100c003201c80c03804400c02d02900303000032400c641c1c006201101c1140110b40040c0c0c1e41140e850b10721a1224070740c000030715a1290640a0b075068220030004c1050303902c035400f250300280c02e6200b801c041c00d0703003401556048010369000c041c1d00784031070300715214011050400c14105500d60300403403d07041000d00e4001d0001c0c000000d10061080001451001d441c041d6041d001500d02600810f5680c41041c120300b81c0d186d1000390760444200e030b04600103002580b04006019135540c0d45001000c40c441551440d0003030150009001249000e00b9241142a0f4144013860405100982c00d0348d06450003001038401d80178403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 759240161 1250 759238911 759238933
    0x6160f050c04180215031909020307090603200405150613080610140405060616060b06030f06010809010e0c010f09030506010b120a0903080a0f021201180f020405090711 74
    0x80c002c48007554611480b0007803050081c01041700c520041c88941986010400920046288144005002030308155010502002c03510101e8504503d640c460040c003032403e2004030400440c11111801803101d204003224a041c640100b0048a44c01d07698240c09589410200005040400180003801074598810302050360313640c91181856011240410500f00281090200c034801c0c81d82c15000030f0060710108540d29044021402c180b082e040c1d80e08142c007140e099201045441d400c4410107500150005480b81422070168003c84400d50740d0034003080b00351000a0354400b0510408048854a00007040740745001c1c001034a9014074101c4800801110810100201350100302c00c40c02005883c1840b96500014550940d2480c1c000c3c02d0640401d091401c5c1d080401d034403050464201302000300c0010320761007110a0700000d2040206041d5981000d200000e900c8211441c03015840000303400c00d00910041005440807807046014555110500f40042452a032042c48821018000981129040c41d21 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 759241411 1250 759240161 759240169
    0x130608030730080a18080a0810120f2901050405061309120201060e01060203120a091208040303050c0c07031514040b0702070b0c10050402040f06090b04060506160f050c 74
    0xb41d0040c0344042824441844403c0b052803040028042a803151490442c101d0b503105000c9204500300c00c001c01c0210b90208082c00c194402400c01000038450300081c40301d183c98081980b03060360b0002c3d00c4000b603044400d481d00100d803c0714101d408040c41c0300c0302d20341e08080c2000000c01020b082680c100224006064040c00d05202c1d42c41054000e0801029a07505158024255080ca0700002c2601c01ea0340c00412040e0740000c01d89191a110300c0b071070301c02d50761403580c114003c2c41017482c040c06101c0004082066542c01440c840e02444c02030b90144140d5030b41c205011480c1c440d00c1c411124a40c001c81042003c0340f140890325168030034140b40410500260100116804020b0300d059a000301c8840600440a40402c455401800b0341340081d81407040d000c418944a43d4a03028a806d0743c0d0725540094115900c0c1d41c44030800b9174900c03204004c101d480d000340034001c0505140e40350181d45485404200d5180c0002600e00043d0000341080d058503079565811014080048100c070343d4858034070000d25540d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 759242661 1250 759241411 759241493
    0x209070e330a110d0e060a080a230a2a050c1608030c0d08040c1203110d02100b030c090c070303091e0519030e010f0c06050903091306080307 62
    0x28403952100c81e034030303c22442c06081030314101c01c90007405400c555048043d102c0f80b043d55030070740043c05c1445e881d0741d0b103c4002d80909200b04540c24081483c040940201103400031050042c80f14090800800f4810003001001c0038442c40b80310050003051140c0002e842c4214001d24156403500241e51446003540058011041e060700505840c0d00041a241c8903c0c408001242d80c018007403030300080c9828251550268045603000e0703901004009000542814000c0309031607007410449040364540c0c001c0100003501c0e8144185880701b201c0c104503a20700c5074900080c1034541140014000141c0340c81c1c01050400581c09444201c041c1a12010341c2c80c0031a1500462500145080c503a644e4480501d00c2d005040c1213a01c404504580344019004021a92018038106ea4100030f0070311080c85100d0720700580e10340b50040002855035051008010901354040007070800160252565801080600ca256084c1d401600902c15180e000b0f22500010500c0940715401030a02c1c11080051100d1a2019030792400e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 759243911 1250 759242661 759242677
    0x131d0303040807050f0703021309050102090907030c02071a030f0714040803030106090e2a1c06080f0a111e09040b060f060703050f090103270209070e33 67
    0x1680102d215400d0200c05e101da41c41090840000e48062030030360340000c001039412068a0600d079038031041c1904020b025411234101d010003c101008a1414040090140000415040c01805039440000e02c0d014940c030781c99010324100b081d0f64116943d03900c03405044071004010000701320b08242d0b250004000310b4001c1c0701070b000c0c2a015680d80d605040002c3c003003010541c40200c403003400c401004a681014488401c401040c464203203000000307001c054150b40a11a43c502c07014030780d03800f001c01c41c60f1107500404c22038810400b5100040000c14801d0340b42c0000c0b0b10b01070b220910509110109192640342030b040500b00d403000e09884114140400c0610380215030440d4410f5910081c420340c4e181041400c5030b10402169a41d2a08d540e69500405e980129044000c6288011868030000d0f0300075040f9913240034840800b20100c08418921040ca00c107a01400c0e0301420399800403441c2c941c840c82060030740b240060708058026858440100d04540012103000d003c2e50284036a803142ca11900081c02d0701 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 759245161 1250 759243911 759243923
    0x20a15050a090f0804030c0b0c250b12010305150c031602150403020c1509060702220207080703170f0c13080d09080106121205071a0a0e010b040b131d030304 69
    0x5036003940342240f440d0310310b034008d1181100280b080030013400d00050060546000003094421144484813031000641d41c1e50800c0c00e618130f01241c29001d80c8480544103040b43d00a03812900f00401c0204103600f550000d035008001e00a0410010f088804040c94841c005800b510440742903614039401e0b182c001200b550100c0040c0c001c0c440c0e0100d240303015101001c4d44007600303041900e4060450002032652040c00d4000b8004d1503040d1001803e00c83c00340e01300c42c440d1a669020f42d0740300800e24218030359038805401200450090751520070008820300d00d061140c03040b10345266a68940c89042c2c08660001b003083c2881c5c000b200b0300450300c56000e014500c854482510b89201d01c80c10050076500b0b40e126a000b140c40441c220001030041f403c80e260602981d4a64141030fa50b964060414a040f40300112040d0b45a502c038406121981509620900700c1006d5600204040d00d140070401043c3c40216a401354450010724040c1625040d071f0b03000c5900c07103015030f0181d8078111001e00c2103419901b08844c2611131b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 759246411 1250 759245161 759245167
    0x120210020d1a10020619111b12030c041a07020a141201050417030423060403080115090312090905090a170a09090f0b03011a030d020a15050a090f08 65
    0x3401c010024800b01860848142102d10341c240402540c41800514a0b03601d0080011040d00d0340c04542d00c49020141d41d01c440c0d580d03030704840680b04030a21103280c1103c440e01c100940d25003007035548000d0740d00030752184d801c681c13804e07203030055110070214140042d01c42174504101c450300581d5810305110041c46100700040512002008010030b10408000c03103480d5906041c1000001a0354035284400d2900400c1c10315169115801c001d8034840e044e0480b1508202c1c1181004051500019010b219520a9541700c00981c0c88a100e921441030103c1321030b02081d4055010b1001840c050b840d044081d4251401d0081036a40b80c0b803a10680d502a1165491604429000070510081410903030801241c0d00d6050301d040d50003600205845414807441141c190794140c5103100c44690b400c08211044010004d00030b54040500c48010110890580f40c403170712035400d1401d04c003800401c1d8644691b40180140307440c5526510000302030070b8010035140340f144d0303969500c03000558070802c1c24403aa0301801c1142e403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 759247661 1250 759246411 759246431
    0xc0303030e03070f060c050c060406141014010305041410050612010b01080106050d06033009120f051e03031609051507060b04291804120210020d 64
    0x444580420703001d20340d00b08000c00c001054050104404c284d40c817440005106c051501e0866403030051800b0082103004202c14001405482c1c3c10020ba905c6c940d0718034070180e403500e140342c540302c030282e10503a41c203134040101004c403640c000c1d03122070ba10030b000741d010500e081d00e141022410040d0100305044440d40c6d50003403100741d00b00600111841c601c0346000304a06840440041d040d0801441444200100069554040c0c40160403c0004640c0900102e0350071740e8100881d910f44000d1400440f180d2b00c3d038050450a82e102e50000302c2242e05640d0204411102c684541005040340d039410f4603103100389450364800481941e01b07503403440d41943c09991603040100440ba0040b44c00c200100410500d50024025955110700f5244041c20b4454041c0d40d0351582e2506c6000f038054401c0701e0364414901013904481c03810018141000e48900141a900c0c01105420000303e1406c480d1044148408800001c0024208860001c80340d1054011104108100d00f010401c1c0d0303010046c12203041c0d48651000c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 759248911 1250 759247661 759247667
    0xf0a0f06080f0c06031b0c0f19030e090f060105090a1703120c03010b0328240915060c020d0c060e040b1014030717040506010305151302010c06180c0303 67
    0x102a6000c104c0d4414514100100900119609200849407040d00020000400c20b0100031018005200304240d41420721886140003002c1640c50050780400e1100106241c0c5140c0600c2481c4101b4103907443e500b903a215003004485039001301c00f6a0703800c04a03840c00411001c0c07201e40e4070582006000c00440d601c000075200201480344c040c044128000042c00113014401f040415654007200c0744a5004802134811311036400d01c0300c101c0100816914003500c40c140f90950a158904006003a04220a070a503507100c820122008a0b4043c101140303896424001140726a4907403c0441c001460359041205d1a01c0d21190600c0c16880350340031410841c1450031900b014040c18640076070071240270b00c0d9020007810103000054450200c0440000000003d0300c06406080d01681c1464108124481c0b0b02d09890030325510391081c00156124480c0e80d45000065a40407c0700b84030341004141010a40c80c10b40c019070b04d041a08204039074190300c50350300707086a1003800c1d54008228040c2d04410042891400c0107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 759250161 1250 759248911 759248923
    0x9030323070506160504030b0a05070c12020604051b090402060c030f040e0a0b1020010609020f0912211c090f02121605150d05040503040303030b09010303080f0a0f06080f 75
    0x240045c07102c00d00081000c5030441050301e0340828000404174256036824401c0ba0040c0301e0380c6000300500709680351884859400212640300d503110340c040b40d01c0c000b8083c440607003803441800b203681c0c031120050000c0c0c01420040702130000ca00c0210100c0c0e050090008580c02e07603420030307081f00100c02000c074100001f4007500e0017002500c690564201c122113050a000605100800d410095048440c91402c1c8941009501c4100140511841107448406011842c0c840c1e50100e02c1305d0780b00d207003550f5403604006000300e80c0c000d40907079010b11801c942a0903560308840e81c20005200005011803100068060305501a501405202c1d01045404d1a031500c10407207045d100400d00400f5502055070703140300360100043c2d40140c9404507008080d031031201135a25100e120720240840c2c041d04010030312013007184c0000900156803182d1014402d900100042c40b40500d000d02c0042d002488190101e6100303c07000210503000b0500c0140882d840e2846c50420f8155646580010901d074040e04a007138840400707001c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 759251411 1250 759250161 759250201
    0x90d080714070e040c0b0a180906091104050a0e0a0605033307080c0f0c030406051c021204060f0e1f0b040218090601021006030809090f0709030323070506 68
    0x503e2440d007031680ba0a60014480d0249155940c4000750000b50340d40124030f4030211070511906007281c2a10382040c00094040c5107d00881c15042c130707030240c2e20404450203950507100d0141020300164542004141c0d040c0015042d10b10403580d840c40803841d91400e110258490068001424003d030a01113500b51100101510310301c0d0a04403000c1c4020325501602442d081b4000c000e05a403036051b00c004100c0d0901c1003042034295840700080c0002c00b07a0f00240034050700b00c01120401c20302c108003600e580c02c0c2d00ca070b000340d00c280c0e501070070000300041c2041d0710890001221560000e001100850340901e4486d0150307048859000040c0d18050114403802503a414440940b010f50401d1411120440304400c1851028411401040060266407007040f043c01000c0e2070000500210b030345c9081c0040c080e80a0f04600e4001e20207000080c901d6032021403500d0082c5600d40e40d03c0d08441c81c0d0703203003203c412001d040c44050f00208041d044248030a400c001d00a903d005501900417418108844c100090070002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 759252661 1250 759251411 759251429
    0x605091b060909060907030228031d0307020d0c081f0c0903170a180b2503051207050d0c0215100f0b09030c120a0605060103110f090d08071407 63
    0x140c10791601c0f0801a950003400603944041903450b0b001e0154064000c1da580d4000e441042081d1904040074800224462001510200b0084d81c40c9000710420282c1901c03865001e5200704461401070801c40040103072180101a0105c0d19600d4a0740c060030706e0035013070f010307900c004004001002400d11803158280d001c000b41000ba012902d075550b0a0700456500700d117806803040c0420003800a80c0545205203140ca0520740c40901d4949500b416000c82e0001013400c00000c0e41540c020351054515841c4103a80d40c0c05440701d5042003c00b641d01e2840c00030040c4008100a014040081102c41ca40074103030721511150090035a0343ca0340326043d007000c2e00c001c25122500c400d000701004072901c10305955003545c005000d22980c80d005500800c0c03506880b4444030360886c0b0700e01002c141c40b807404500d10408911800051003c6d483d803400440548001d244001290300041188901900c00000205500880900050000d08580e114020036811910f001d4070030700036103241144200e000740980070203012000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 759253911 1250 759252661 759252667
    0x5040e010b03060906043c090503030118020f0301170a0602032e420801091b0f05070203070e0f010609060215060f010c020d03031e02041805070c0605091b06 69
    0x621f01d56802008070340f601021060b4041d03074201c0250503d07044021030110050114951078a00150b803540240314030b04402c14100c224810120040c0201d440b40c01784401c405045d82d08100c14030042c12000c0c0b00e0100340d8420a0050701c00660207001840c440d4001e403041141d14500c600040c0b01c0f42451040c25010748205030002e10000c8660b03c400d1a00b904c07000301c2c0103915803888006074800c010319010807a02000c0800741c090040c1d40070750141c1c1a114a54001d0084c00c40099035540702000112484020446010083d102d05124001074045580000c0482d442c5039555a502c05980350305803021406a051a80140006500301ca1001d0082c038491005004e0f9003c481c590011001c40500010b109008018290090b68406c07010180c010b0780082c08030746600b0b11882c01a00800d107411103030440c14030300402070f00405400d02c07e60381290204641040c0c600c1d60f2500582c00cd10004021900784020740c004100410510301c00c062203043c04000a144100641404601c0c071442d8401c0b4500c00c1c00d0070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 759255161 1250 759253911 759253931
    0x3010c05120f060d1a2d01060f03061e080d08040305161113150f08150711150109150b120406020c0a1109010503011116020105040e010b0306090604 65
    0x10185180d0004611001946a0b155400000e44c01580d042c0003402441100c3c910501800c2c1c8241d0090091000c00180042190320154610380003c052001c040108121070041000302e000c0c8401941d000c5851800241150f00c0b5843d00640040015201e400100c58540c14010840d00f0440d0700240304243c02c040c01a807600c0e54004109206450340d02a007458030398401c0f020003510ba29411003528000704580d29001c10001420700030205c2151440c2491480c040028407050340c800040c1c1a16144070140c2003003040400c0301c24440d500580b03080100180b01c201c401d08032405000c110820310341c035042081c9551408210a09a0f10400f460f6809615002410005a003401d1300b150403079801c07848103002c1a42c0b00e0401c00300900a14505141501480d9589000c01280b003100003070090048440c201142d80310002c2c1400c80b0243d113000605880100080d80b00307683d528081180562051600c203292035102e51124000d548203a20174207010b4000b00901034149400700c0166413201040c1c8041000c0300135 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 759256411 1250 759255161 759255187
    0x190e060c0702010c02040609020c070509090d270312140a0f0c020307030b09070905090102030c0912030903162c1b04050d0506041e05070323160503010c05 68
    0x102030600340d41039000249200440e401098046142500200100401035640c0381e0000030b03600031001c001c20390041c0c2001007014a0001d01060049182c10300402c0102c000c020160386020516500f054002018110003030340c8440c000048d4059445480602d07224070b03944a000e004100c407900b40c04100d00080c0520280941e0000c10389031003445500e040c0c2500c24013800440d00306a019000a05003070070044c200f280c400070000782c05007102c03071003141048660788114140d0700700d0100303603030020382c0700010464000645803403005d0001c0b01903180c09481ca01104400001e1070300700414220700e40c488451034208601e41c8417850322103500c07800d40300030071a8000c0700703110b4580d034240244081288000317144e40e1a0044118801e0300c020b48405812069140c0b55030510030344e6820110340c111100c038501c90600c80c131210500080d980c8564060010401c00c0d043d541c9800d80c022039030321030404c070b040c0200c7da1032085002040f030724240c0610f02c400c48444504000515003500c00c00d03401c060601c44100451520642 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 759257661 1250 759256411 759256423
    0xf0b0a0c0c03080717091c21051b18011d090109050a02040315020c0607090b090d03141b0c151909150810150e19080d020303190e 57
    0x16062820310403030b0b0b907400f400b0785c0c20011502d040407a005060042000402c40018840300070001c1307000c0e8141c50a400c0b002190554001600100c026009004140c00880141c20064204a420f81500303031515488042c034219030042001c6609290214135000c81c81c1d60441410300800e03040406441c4a0243c2401040c42c819041c411140d00c59030760710000e021003290781d05640140d80d2054a83d00e81840c071008003000f0790802100c503481d0b8051320b000304001d0380c080c006410841c0c2500c1c41c594101604403007004030b003034094031080e0180003c04802541100b84440201118111224494a0080c5401313415180c41080c2842c580513134003245003d4810542c8100307882c9103080791010700e03044240c04c06040b903080d2402da20089808080c41150b620b01074000106503c2a0b050555003a0100d0b6182c000d0901c1030f450100100104204060304070a50512151004500c0030040300041815034416403545030109103140c90340103130000f10900440458003041054501810542400214413105149803519 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 759258911 1250 759257661 759257663
    0x4060c0305150d060b1018080304061d04111b0c030c0102070e0636060a03030e04150503100609050c0903070b0a170a020a0e0a150e0a030f0f0b0a0c0c 66
    0x110400f81c000100b016541128940b64000b5024488100502c10090a04e080e1500c954030290021100403c90000000c01d94085410958031110744c403020680001002e5400390240360403580355588404003460305e034000c0039410b0f0507107580d000306e111040181e4200105402c65030b10030380001e02a500580e038002001c0c41981c151950322801d944917a40010142c682d5210714150001601c50421300c2521a00652580105107503101011036640404004105086001c0140450342e0642c1d0702d005030405500052456441a501000045e00e607400a0305e02480d055035802c2c00ea0702c4603410302000307599005032500000030a210301d0400141000182c0c440904d070140180084000c105103001034803841c0003131f0381c80114500180b000d060280246002c1c2d800081c128020600c00101006541407102846044800082d80b141488060407421601c0520000311541d001c0103030b40f008004911140180c2001d580b0954a210a0704400e1400c20142e02005114041d914070f08001611a00e0700000c020030302d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 759260161 1250 759258911 759258919
    0x201090b0c010612060b0108010608010501020a0b13051614060405031009031202040305070614031506030c090310060603110a0e0409030302040e1608160221070b0f04060c030515 78
    0x1c0c031481c200e49070042c003241e4450800704444034038120520086500400303800d8002e982c1c40099030b81760207060b11180801e1107600e00503403019003148080380c0280000c03a0403041a548400307602c5016101d052501040b100340030075000e59171808100c003595100c62010b40080c15a25a82402d140400184d104c0e1a000d01107288651140300000c00c2510400b40395101c4d0700360540c1152075035140d00740310f03958441d580240701c0407490324050b5440001c410400c3d00d20510300406621406491003040c04002d402c082d1094194450130302c6400480c1e9424088815022020100012500c4c1307040305c010181e0f040c0a01080d03072150200b0030840515880302a0302941042910b01003605045858200c000380301d1940400600d02405c801e00c000c210b400c500038034110300c880d51403858a49407250340c000d0050f4411118000340c0e000c51080c040b840d0113003004140c00c013040091a403c0c20740355180c60708091022140ac0512041030001c1004100d03803481000d1051119280070000c1e032070898049072204013010521445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 759261411 1250 759260161 759260167
    0x150f040218061603032703031a18090610080337052a0a352206051c0e030414040609051308220f0510020a0201090b 51
    0x88614080d00405440c2000307415140e075490440242c183e400344000044001a082900c0c01418a168000080501c3c440c54440300907555242e500340d00801111240c01910700d80c40300024074079650010305030220003807641e4008241c50190f0226041402c001c042072404d204043c414805100000282da0b28428080c0b140b034110b0858100301c0c040007001181088003030001030b81c0201e546500c035024015004200950f856003406501883c601820f0700401e0403016401581c4800103c3c05140510034294040e00c0030403000d181c0e80700c51151241e64982280900d01002410824000d00306c12200500e8130b00303d01c120350040c2010790040c074512401e00320020955016140c2c21a000069201015a0030701701e0440f90381c0c0d56a0704240f0400800210050720840c135080703000800800d00d01800c1e20643e1030100d0928510203683d135a0301a81c104403051001c482601d40700d54120100c40032181e010300104054690a1480e00c41049410714040385002d0441d0000040c4030010b0741c00c112034000744c601004180351 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 759262661 1250 759261411 759261427
    0x20c01020a02550c03150501080c10031107060603030809060c040b0d0b0915040f020c03030c071a100314010c020d110c04050c041e0311010822140105150f0402 70
    0x82e001e240310700e16492103803404200b041003101c0030000004170380c0300e1241c0591900a40d007030b08044840922a18100d0b41068001c0082890b02c0011001c0e80e065900f40003510883d1040380543c9501300304000c80d2500c0c0c0d1841d042c42890b8000c4640d580c8000400d008001510704090340b41031600030381c4105000c0039404101c0c00880c540a400180c01850050310b042c0c210b18046001c034003045a4415050f000e2860300700c1c031a480c0c101c01e0084600340c62205d4021461b640310542c860001c0c1d80682800c7d41d481d605500440c003040440e130040f50017800d600190001c3d69046007804800fa4000308100c0601d0b07031524169003166038012800315203a807642d04154840c0326001c44014205148501c02e075600600c0c0c40c0c1000a110884005001a521120010140840b4140c259110720920f0702020305800010707045444250b01c114042540404512a222002c1c5110a4056244103840c9406c0320814018a00c0042002e400d128559110324540e400c03000c030140c0203010450b03107070140420500890300011205 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 759263911 1250 759262661 759262783
    0x70306050c07120215160c150e0f010207050d030c320d050103060609061a07080d060e06040e0133052701060e01050306040b0112020c01020a02 63
    0x140000f5080f40902030a103204076402900c80407081200350b40b00c41c0000200c1c54181119070a070540540300c0c0c4410800807116100c01d03182410914032441444d40b03074880700141c040180155a45524401c001580740e141c43e00d0320500302411418100105031400420710710310307a8040461500c110742c2c4003030801b10320325240d40300480c1c03003c80030300790403400c1c00251101b9855225403001d81260b00440d400c000b40c036102e840c000305030364940c804c07401c5041002d003e40700c500342440000c01e20b1900c100c007410329000d44007840000f6124607a0002c0d4075030201000300040e5040038000d4001025480e0001c000788030710607002c043c0a2145038580520690f8407811182d0740009000810302a000081c22241f052429541030904000c0b400000701c1880c1085000240c0c480c040c0200c6036403c041612032038216a04c1030240030060089072521030400102c2850030600100c02e200a14010b0441f60003d6554090418003070300c0c00e031081d0100700e62688040071030580012180032203030704200c607180e20f10400d0380c100b402d0b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 759265161 1250 759263911 759263917
    0x40519021f03092a050303120705130302040606030603110406180c020c040912021002040e010501050c0a0b0c130501020703150b0324070e04090515060105070b0a090b18070306050c 79
    0x43ca2000060144c244404a007008103220620b50344602c0c10342a03c400034540c0302d00480d6200000b1006810100d00c555026002a03c00302c2130008203141d049507250002800e5869551264002c81d84e2518107000780400e98000b25405241914280700076441c00c04051940c500c3c04032441002d654070680441218401d001c421286200104107011401840c242043d0b0700315004030050243c41070440714075801c0742c94000e4600311010382d1012092a03180c44015941c80c2d010507500d034541e018008408002410846226000d440c014007084e440348521020554040b5664002c0e07810756015402c1007000030f145044210140000300c1d804602860080b010902e408000c4d65928850103402e4003202384403880c2c01487d445103489036165400d802d1044280000c031901d0110207460313500319209488114648a090680107801890011710700b084070b4407085000d03041510a0950389490701240c02c148050805600e030004003480b400c814080c5d00c0000daa950b00a2480001c20171503d503000280c5804200090b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 759266411 1250 759265161 759265163
    0xa03060b130501330206011503021b0d021227040219030902041506020d141b0c0301060504150e040312050a05040218010501020307060515030312040519021f0309 71
    0x1003444a543c440344107100e410b1640c0509100c1d184c071212a2040303420130500b41440c01105030080c1c4503590030013010241303044918400b6428142c00304819495170004501c1d42c0d000c210400c0103000d00c00a1220001d04108032050100b01c1884280103c88600301501600f545050380c55200ea07880c0e11292010030081e026032840641020402e8001b0f204c40c60f0940c00558034640308840400c40c0007807400300120003807814082c0e480180d0005172110b445c98020b401829070882070160345410041c1c100c0c00d02c0310340415105104819000030501003118202400361002400301110140400c41150a04104031748651141d005d105418034049000c1c1405032104007072710080080700344494500311403450701500c1e0640b0124024030044412060f5030408014003410380c1c04c1640030310310303040c11501d840b405844094802c1c0360f0322081899400d20b41d58100003e1400c851f001074405d01a00d09802d20300d003001203425040c03050300701107034645c0c0060707440d2a508000059180c03208050b1041d0710100302c1c010403150b04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 759267661 1250 759266411 759266449
    0xe010e0a080703150609050f0a05071e021e0601050904020d0f060614030c030a021c020f09090f070614041206021b0303090c0105120a2f09040f02090a03060b 69
    0x3000700500140e5a104c44908101e03403001c0c0102ca6817090400c04450701150301400030440384020a54406860300a5a04502e140c42d02107031001010543c9a8965170031080b40b40135070b1000b01d00010800c0070820034824007420b030f8060308056152002107001c90000030402803049200c4560389042100361a03c0d405501d8001d40200005611100007003407204140c00d0152007407041924000c1640f40c0018000280d550141807e084a283e106c607400348504000000c903030020306440385410301e0f100c0d900340794814400e0707070002c090041000d010281480c0040e08010100190b0352010704101c010341c0c0843d401c0700e0040d500c0e91103c0c0441d05110000740100c00c8985181910380314034494000001028500401200003640d4040404a0041d6050300c03c50b2081c090740080040001c4d0784000039800700032500e2440700c01910120032042c82c3c03500105070400d1001c1100c2c0c08101c03207440d41414410309208036900d6a003140303840d541c800022151091844000d0a00d5181c83d840301440e11503000304820a03030035003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 759268911 1250 759267661 759267673
    0x10e0102120d0c0e03031c0216081801170411221e050721051503120301090b0d050a11030102090a091407030b0603010e0705070c1418070e010e0a08 65
    0x100019003c2c1c003020741d20000240e043c0c040c10b2900d19021080b0740c880003c01600306120041114081c01035040180c003000c43c004107046c2c40021070031150080090000e1940d1074208070025000141140700294284101d10f0404002c000010b80341e6800d45000007421134143c030315444485104540c52241c000500b0a00d810b01d455942c9441860f0702c1d41d402d1103004502030106a07100c4100702d6034154058000d444400411000c08054819503004503008022240c0c07092024500c100403d1a00070a500090382c0c1d514004010000052036218480c1c44000072160150380194030386515903512205000600000050081d41040d07079000d504446002c140a0145046690f44503c908010124a003e42d201c041d00d02000602140c840d00c80c0e5007405400404060569081080c10041c401004203d81c0600c00100b0002001c01c014890140040c2034424011002000703c2d0148805000500c08130036401d00301c2002d101c038164028200c07210641d0207107400d481e00816038000078203010483c1e0110341e81d40161 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 759270161 1250 759268911 759268927
    0x318160806160513030807050a05060117010b1f0e030a1403070c0806090a0f0302070e0406091a0c040618120605060306090f0c060304020d2312090d02010e010212 71
    0x71581e54071030507030001c080e00700070440c480c191154403074024a8003042e903203da01440040c010001a0104030b000b135080300d251803055600c040c034292081c3c01c00394100c1d080e03101000303103803e00f40900c450070700003919603001030b1801c19040165081e40c001c40d030041c84100081c0d0702042c1c03010009070800030381003030750f00c28200251307460540c03241d2000d10191919850940042401c2000150241c0605001001042200c1c1d40c0c0d03c030071700d0b0888440c10480031030003400e60008640060181c02401503008400005041100d0f14001000d82d92003035009103101d40081c1041940d41d410002d84e800c8030410308001054070a00b0801c0740d0f0307044082d0448160312815460100600211b40d119070310bd41d000790b00300c480549400180b1075458046086540c00c0d9070040c03550780803d080a1002e50382252001e81541981020782c1d841850251540c040d4100c0007aa01da072440412000300321109801e0040c00c03050b40b40c481c3e214042151807002a0020b414464881ca259000740d10030041c1040b00618111155160f0341d83c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 759271411 1250 759270161 759270163
    0x10e130c08070207080604080901051c0f1a180a0c020705180711060c07110a0512010507090909020a05060315060304050109030e060a050a0c0510021c1803020303181608 74
    0x20395100c401841064000b084171403000803010702a90f00414401e00307000f0600011921030303012403004c160000241c50b03801040102c60050300240e541d80032010074481c5489082140040922021602c5410810018107039001d4076030185400a403a00c80201304bd9013101010382c0792400c56403017143c2281c011a6843c500c0c070000820319000314941d039100c00d00290039030005981d5060583c6d85042c1107030100580c1c0001030b0f6064910494110184c03100080584c0c1d0390008120726100c0c01c0c030340c40c503944490402c440345502c120100e024195040c0100540205a000f040c109601c3d0f0040900403180003010034101c2c01c0442d6030070900d40004109030350724a49440c1990280003880411000f241244800c02c406142c10340c1581d242c0641c44d5207203400d200601070111441c0820709016180b6000702e44502c502003401780000d140c4600c1c2030320110302844104010324200c55501122031480701c3d500300d14000095021040b02e0304400c05401400b0980345601c0120308000c104d03904d02040c03501c285000100340750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 759272661 1250 759271411 759271427
    0x30402040c09051c201e0102011803020307140d020a02040e0c0d14010608060f07030917040b090a1509060503150a030b010e060904050c2e0801051003020c070302010e130c 75
    0x100c034a100f000303000300300000903084001107030086900c846c1c0c8850b455048410802202c00102051001050412140300d184510800101c002c3d001030b003001070f440c020311940c02c0c41880300710b5801c8001c0115060129000351141c00c8050001e20480d01e80e001d84400302410002429a40001052080c0219092030400b200d0722504986030074039402d00c5c40000b00c0e4403011914612440c0268007000c0e41d80ea440808800034403100070102c0c0c416030074074100c000405036440608064443c40c00ea45686160070010484030020940c0f0480140861844c051072050b1303c64400000ca6546080054503500d40c01001c2a2a18850480a402c4040a5000400d200004502c0d41c122502840290090307100e10040c050540340889003d804c50b0320241e605880303801c01c080c0c00134016607084450990803020314045a44e15102041410006081d20b005200b1480c0035403807581c08100c581030840c5498001000d06803181e2061101a042c03152071003d00142c0d4480000e0a451074000c4801000400e21490303018045103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 759273911 1250 759272661 759272663
    0x3030a210c0512090705010509220e061f0308180a080123070509030c01210e1b030303010e060418060903091a090102030d020a030603121e080c030402040c09051c 71
    0x4607080c089070074642c005c2101da0a58038181d40d4146031503007031420300c0140455901c10309aa10200c00400795000100d00c2842c941c0c05154015200606051340055040c10074001e5100520345103400400000c0c031508103c62540076410084003140d030403000050362045059212a40365400d06280d03129541a0060194000385005114070440d228a02d0850b168080c6802040c1c03d0351003051801e0041d0301695912a6003444600c113000702604a111142c1a01d5019042d008913074010308240c90000a8040540392100c402e4008504540c2f42c405001168080504140c2c060f550307903c400f0039001c5020304580c40c0207800c01d00070301c41c2c0e081d245170003007002c00244914900c1020400c0b041455540d144202d03800c06105900950615100d1544580254071402814003455610940000000d420a54800c041041615606035001500218035007060080040008000d103c50801102c514014142c82d000b58044e240040d0308448103a040d1002c0406030011940070b4a07c40484140110f040c094040341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 759275161 1250 759273911 759273937
    0x5130e07091e0b0301022a0c030613060e0a020a030b16031b050d0e010518010f06030b0411030a05010f150503060405330c0702120a0203030a210c05 65
    0x5507600d40342502101e40a07507141070b203000740c00e0030111014055003280d04012030080006207010510021401d10200c0c4421010f40400079945441c00c42d0000e011a031449041030740070b00100c0c174007562042c00054a070003000b403c1d16580c900f001c01d141c00401c01440a2603002d0b01c6a005207480b4200b0591440040350f42a21407002e162140304903610900810400c00c0c801000c02c0500d00c4085420344007908001070326608a0b94441d03c140c0900024091140150b0041c0c42e09040d40380440c21840c251140b59103c90391041c281030040000602d1410100e900541003a95080c081c0142e100103030805d0075404018142c0d600b0a00746444060f05a44140c103807901360000401d0b043e503100140341d1209001c480c081d1041d00310805400800448909100c990282c0f80500d0a50500301c2c0c40400403500c094814129114000c6408070441c28140c039034914401100004110800d0b66600281d901d220311204102042180b080718114000c101d0914460143c0440c010300854450410040c41600826010051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 759276411 1250 759275161 759275173
    0x40c0302100c03090b0d020f0f04150323060102010b0306150316180509030d0219030f1a011d181611070303031802040f0506190501020606041505130e 66
    0x18260007088080c41c45685525030130b5559191103541200c641104006200a503020400c550342e41c180c80d0010100315982110460301d9504111980c8242d101101146080c03501e03103901c00d44007250380d40c00c255814240d10480d442079995000100d01404090310080c0d0036101e04000d010307245110540052a8030400d0b002c030780105254030441d0142107464480c0d0b81d8110035105010003242010f070012070f4405040700c07c1302e240240b4103100c5412648400040803006004c582c001d1541039050050321100003c6080038400301c401081c2a04500c50000e0f045410701c00c0281d105040f5000c1d07140328260214000702514a086807055071200714980844100141c03045805030764103050b010302500045c100e03004008100c641c0c110340d001c0e40101a141c039a00862070000d0070030340050343e850055100902d6240000315030b41c04c1480900c42da0020b0f642e4031039402d03010740c02d003400640d900081255024004032404115401010076010010019401c4142c00a06585103c52980100e401c00704840d9800e00407625 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 759277661 1250 759276411 759276439
    0x319020304060c0e0d2a0b041d010b27040f140f100812070f080a02100605030303091908070203030f0714120a0f140c0709051515030c12040c0302 64
    0xa94111441d07001000b071041104d6480c0c0c41040a244460b0a80050a40900c01e5449401100c05504239a01c9115400481140100c400301105000742c01021101c9419040510451035510949007c65040c00e20fa008103100c030006982e150051803144280c4582000712080c43d07602007004000c100e980079540f0195002040001c641c4018410444a0341e0019014a5030401d178500303015486110152994448d440c100300108021a0040100031540d4004010540c181000320741a100c1952105110740c0050003001141c00001c50301c45901e500307c2140000800c0941360100c1c1601484c900690144800b003085140c814058005010241c05094406e800d000030b44031460342e0f41302c00e40c000352200c0000d000e4507548500032560f03402e011500342022540701d00001b00040c410341202000148c164004081040501d1541c07186079041501001c000701c0c0c00d0140c50200d0f000020300c4107420280d1030700100058240c4026006d803030440c0410450155241014206a14030150308c0c0030992041014180d403031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 759278911 1250 759277661 759277669
    0x6030f050606030115080901020d14071e020d14070b041112010902100f030b0d0503190e0f0d080c06040c090f0207020d03081e0a1506020a03140319020304060c0e 71
    0x20b0b0480d082040016010400b04170700b1284594041d0640c0400e41d0244000c3d000c110050044900d01c0c00c2d02d0b001c644252401e18801400300d03018440c1140418034800d5580d800c3ca42c04207070703ea00302003903041885983e2400110202030384078628014101150fa40280410405041c162580482045403020b4910008a280320300300e54104a00a51150003031100714142c50084000d00b040174128100012000c2400700860103907204080c003183c20780c20014003843d494806520840b81045c80e807520800510741e0101041d00b0140400d030342071041003d50324460403c000a81164410320250b016100141800d1500007025200c030b005d4075911904020714001145414406e8440340d43e0000d0084d09695013544095440c164060004440c8d800c0010416003c0c0000c5041c160050000b081d0005021100322900c00b8241896004039003150403419985020943c0300032203c10b024408030f07031240c1d00d45070780c549441c40480040000e02e6442c00402048103006081c1d201c1402c440050b11200c9152008000308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 759280161 1250 759278911 759278917
    0xa1d1e160e0a0f090503030a050117030703093c03031202070809010e041805030702041a03060c031f08030a11120d090c0305011b090609060906081f06030f050606 71
    0xc807241240c034000030341401c2d0319800040502d0108640020700d041692540c07030640e4421907090b548646c40c0e100420120060030b2409448119034800f031418400340b80d400130200c071070911030035200f80d482d4600d803165402002e13812104c4114103a65007800e00174410070300e42541c07164401078021810510b00c1441e014038500031500e0b2b4650044509240440200042d2000428412101d40050790740c211010184501708120013814014801180c84200910410003903444000f070710642144255084c12054800084240d00210034460040c0c403a65103a54507042c031a241050386486182141c0b00060703444000c001001c49201c0c40e680d05214569000d040d0381e50f4114a10b90f140e044004100306c0c10245815445580b402d0b00c1407002c030388020354a0f25418295116210100800d040620250a0a42d00041385400600c03203800d100107068a04040940160030034410b18060210620020708201198800c4c030b550916500c1110307841c140c139801c0040040800320841ea80c000c0c589008070f4000e1500c00e041d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 759281411 1250 759280161 759280169
    0x40203010303141e0a0c021e09011203030207020301110309060f091b01090b03012c220326070201140c0a140f0f070215120a1d1e16 58
    0x41d541c910f904540049465500202006581440320640d4070364841552004007901c0c52030703581d02c90b0a05074a0041080414461107400a40786039000400c03610346504600e1811610307c0c0000000000903414254047e1040b600d00a615519005998141d111004043c43c0030364210130403070b0032595a049102e540c0c0c100035a48250140d200110714021603d80d448401d003921810301d080d40b049982c864021046d500280c0014000f4101000e2500c2036500c0d0b0810640982c10820b140c04240c03c0200003182903000e4100b0f02e002011603400c0e00030034140180f0a9032003c0e110318020190700000c01c0d0002c0713408002982e0040055007800a49440704003c4d4584038010b05d82c0300c48040c0743c958000000e40d1100c03101035110009103024000712401450500c00303414000c841c580359540d1141140b040101d821140d40303031060845014003450110550101c0f00030b501c14040000090a080002d03100319200050100c3c030080e0740305022514001d810004021103240500c001250010f501d00300d1080c1024040e40a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 759282661 1250 759281411 759281417
    0x50712020a170f0c07090903020f06010e040605040206070b040b07203a050c15150909010b3a020d110402090d0303020915030c04052b03020615040203010303 69
    0x540c0d441c21542001003048500f205182c5140210000c109420100c20303071302400c00a5501c03c0003000303068051140f0404000031a01415540d0304040401181c81e0015001600140c0d40c1e5000400b103458403011294031303d800070311031461441c061411001d94002203030b00344006141242901052001c1d49007000b0100c1c030940c00b0345100981a041c1c0d52003004980080c0c41c0240d42c040592030001c0e000c007a00040b038191030361000c2c3d171002c440300e507130380b50a070b51814080f0001c2030b00c400c0280e4501003022800c0060003c540e000c02d95107513001058090300301075000561003055040061005070038045905600c0038090815984800980c0d0a505035144921002e9001055001e030030001400c2c9003129612900d000f0300050030107524802082e01c5045460701200425400a100305061504040c860443c01d0441030300d40c0380d442c11140312000f40c0203034400d060091000010706125207103d00320581c000004050700301e980c0300c07031820025901c0b00c0c10380e5086101040045801d0141c00c050003201e0507203826803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 759283911 1250 759282661 759282683
    0x40503030a080c04030f050307030201060e0c04090c2109061a01020c01080a090b070809150115050d02040e0f01060906020a020108060108060d050f060712060e01120819050712020a 79
    0x420142c030000001800d207140b00340108000301c000b5848818071030015005900450700c8040525010382100e0700c0c0c0d0080a080b001c003104011b403024192013107405076144030101107800190302b2420744981d0031614043e10120010040c043c10903071258041c03100c15004120502c03800e10a0410708a0f51810069201d005800258024600394080d4401d40c3d00003544140c00600030105031203040413800155001c00c0050603010034040c1d541c0003001004220720807500c0c640d82039407400001103031171101c01840509021011840440314401c0358192070007841c2d00c0c1042502443c5c5128800c1a40c1402d008240c0450702c4203902181280c40020301c0c042099060311040010b4071640010340c4d503014000d0005a05c44d80c0744400c0c0d030001c7d03c1440668008420000205030504041e003010b449040c489100e501030760300d0400104040800c845c8094115003400a4600780c540d85414002c03441e200d00c08282c200e068010002d070b81419400001080340c140038001840703a2687c2440100c0c1c85c0e08509401501c1f6076541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 759285161 1250 759283911 759283927
    0x2010c0215010f060503040c0e010b03040b0601081504050a0e16030525090f09060219021c050d050604150f06120212160e040f140c0408071a070206030c0a09050604050303 75
    0x1728001c0d80c0103402008152880d40c0c1d60121090201000d8001d50f40044000c030a100070400d00e02e41c0c10390044030034201441d549c07500415002920800d00c8030540b0464840b808070300402c54981c402c0310400c1484c001e4800040300c2104d40d4030700700ca10317200440343e6110b039442d00041d80b03c03031b8000b034800300070a54244006285050380d0b6402a10b8000d00040c040341d41d488524000519520003800a05000745403e060003d141c0c10190a110050300303a600054030001040891651000858090040e141e81c00682915940046401001c5c00d603420904400242c00c049810840d2600e801d003100c03c1503035498810080221000705a0003001c01c205025500d01e8086840c149545d80d009600c3d0740c151038a103c8504010002905441003c007081c0380c070580d0f44205143da184072006580c0d01101c451009440d0518002c04a07070b0b2840d01f8410b402e605d034408450400c129011400321844940c0003048144c0f82d0800400400c050780c005c203e10400b1135601a0002440d0070213905903022103800401841c203010071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 759286411 1250 759285161 759285167
    0x50310180f170d0b0f0301021602120c030a0320010b0a090e0a0605150a170d180f030c0509090109200103060909030503011d4302010c0215010f06 64
    0x6901000c071040021003103005180d1100b8400740c80c454240304004150005400c0a20540e0400c03010201d019034010418900c030b40c84050785450401c0e074140c0c0c140c0c0c82d54000d01d94250a0041c02c0d01415894000c4000c41000c0c580d010001407104c0d580c101c6050008c0c4c1500b05202c2c226141d50703d000390800111501003210100c02c0d404014034040d1b4600382c07600400c1c0c595840c1c0032200d0848042d69003c650320100c9002e0700b01107000704084c11899116a8403894103c00039660b0707400d08446042001054900c1d03c0320300314030002405c010109180384815682d22490b102686050318016180591060340c0050180d0105000b10902146c020644075481ca40010411000d81100c9180d681450703220700001030241401e1041d8a919406640c603a512541803006c0011140029521240c006140317406001c581091440c00d0800b42c0c003914200184e4080900c3d160274034042d440d0b6940ea070b00342c814810b512103580640080d0245841030f42643c00d9500c0303500740130000200a00416034441e013212014445240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 759287661 1250 759286411 759286433
    0x40b0f07020c12030d0c03020c0d0305100b16050d020a030f0503070f050903010204080307060b0132091f080f011505040b0d0209030303010b0a0e0d0f06050a020d06030302030405031018 81
    0xb4942c3c00e992400e8610b034100d005a4110b450400000390b40001e8021800c0024441c0c504035212628040c0708604002480700d9061480c0e001d0f0203010440011051502c4810511000d0030702d600c94151002e80f00c400034069243d01e2039000070380100e1500030344c2091051054044911a4809444034003440708000710803070309a00210500c0d0741540d402c02010401321070801c050040d0354071a08000c1161021140010801000003080d40c0c1c0d404a150b50350380328401002d4a10282071011884151941200800640b080071102c2d03480c021004014204041a68401f07151481200c9842e0380307284507640c031075005a800c00c00b090f00c0d030002141448184218001600202108146c80d81c015041c10b0900001070704550007a480b10222348000148060351030b4002140030681807045980c007213100605e4440350702e6020b880c1c100a00b0389a50b800041c10800c61541542c00d074031102d60302003000c00e88a141c007941c2c1703034001e014480c440d10412070340d00b814003030b60301500c004841104c450903010710749503451102c40c1d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 759288911 1250 759287661 759287689
    0x804060b010e0d0813080c03070b03131e030806010806011b1a10090c0e01080a15031b08010e21070c0801020f040312032903030c1203040b0f07020c 65
    0x20039a01244080e0b03582e41c1d81600012401241040c0c0d0b98517642d4881e004891496115140641042417030503010307a800b01d10305048074400a50369039a5030b20519029080240342000800c8084030791040030050714100b45408100748070f52035041c1d043c0ca0b02c03001510540c0084500600088002280c1584503401c04d22288803030384208075000c825241000010300c142801c44a0302610f60180408105143c4a03000304803a450041c00c000b0020152140002d05040b00200b003042d00946811110102074480b0710307841c0c011a0005482e1100581b0200180b0100c0c2d0148a403516560800c410b021907600b000c02c04640c0c00c1080a040b003544804c0c0704d002d171440d400100e015140002c0032900000c6001c000e000400051151001503075030346040d464494090583c0d4107502d002c25182041300001420156040554600703401c1c1002c040300f9800c3d000924500c20071340740f02c086020300410180d1500c40c40b0013841c011446180c101c10290b8842c1d00c0030017444402c40b5404010f81c403580c400001400d0000f2100d81c60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 759290161 1250 759288911 759288917
    0x90f032107062009090c1c1814100606110d0318060612120c171c022a0f0709020a030204170604051b010507110414010303030f060609060804060b01 65
    0xe900b082c592003e40c0001c01d403e00d021a00008445042c0e2400303502a0381d0000340100c85506040b0000148003410003d812246030107aa1040c503481d0403411000864100b55102e01c1d10b00c0f14001d80741c47d1302d48850f0034100d00c41c2510f060400201d2024025a40c54103034100c10002000d0b080221542140604801c01910038800a440f000c1d001207078480c010b90000d042e0310104070808a03003030300c0d169426880207412041006200205040005c0446010703100a90303010341030b247c0701c010b02010760001001d844103a1101e14800268815007150341a010881621620200307881e40c05018600c1d0344440c825601d0042e15044030b9001e001129a42c0d001d010640d03400d00c0d00506007500d0b03000c8001480358944540d41a80d0200c004c200c1003200410074058802c045040c0340d0b0079409a42c0c0082c1041c02107020041200304240b0342070100d521150700c22003101d01c082c4c0403001503594038100a001000246c0710080741a04201001c203845025510b41d1040b0340301680c44c120560f07565203c4a00401c80c180c065410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 759291411 1250 759290161 759290171
    0x203092b0c080106081e06040b07020f011508010c090806190623030606010201020918060d0c171002030609040816020307060e0415080a0f03050909010902090f03210706 74
    0x42100703608541c01420000b000012924100b400e0301e0300d42000881c0700f00000500e0020f4030031855000c121540c000e41c1c05012940d060b2100401a803e0100c2000140c4180d840c015001d5503807582580150100d8002c04000c02c4074401c91030302250420014040c02e903a030782c8000003095181007000556014040701160000d0b00585a850b0303400344113000d00844030034881c0d440030f504451600b0b101c41a003000c1c090008514125451010800d80e0344405c0840380d0164600000a03403039150298400d5443d030b1311014145a9603102c0804010000a005400b40188900b1402c49603060807442100c1c06401e000700304090720303a1665260300140c1d000054070400b6000d200026001078904011507005011251101d08607441d42c1c0c802c0c84101d601030001021820120f0720304100260020986c003505070f401402c0c9892150751801d0a4170a032107079811f0141c1001c1400000180300c680e80c1d014000c5d10000711103024101071060b00301a43e070220008000c0c010f0b58905080100318080000a1014502c20080860 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 759292661 1250 759291411 759291413
    0x3111917010b150c06180c04020d0f060e07080c030f130302013b0705090103021908150a0c0201020a0807030c0207050d08090f03120a0f030e0307120f0203092b 70
    0x31030450b400d00b280d0f0782c2d0f1501250f48107120f941032104507444098040c02110600c1100b64059803404490f41c0c3d103024941c002100500305189402103882d52044130300c00d108040c0c2d50f005040c0300d00d50031180c58001416150100300342c00704034801c030703401111400a0081551a044921342c144400310904034155075992400c1c0504401d002000840640c030329041402d80c0703200d0089d16115401c0e8410088030307500551418000d90782c403041c1c0541529010340301d0340e4108011624440c0c03c200c84d0f0b00300b0403c0d4841d40703600100c81401542c026124240180382440000000035090f0b00341d0241d002e1000219162000080d640c5210b03a00582887c282441200d640030764071804500300540200b025070380303000000b8400515040c20806440a40b90580c01040381e610044c1c1203080c036000700646102044a02c0c01980045486500050903001c04202980d03610f00d01351a24a0192401b0f0180700049250407409000f41c90000c0184c8503c1440904000e03509040d4034200f403079040816881900507144d048030740c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 759293911 1250 759292661 759292669
    0x1709070519050907090e0112051020030a02030a1112070804030210060905040c0b1c240602060a0b0f21031210081207111c1203020403111917010b 64
    0x80c0100199220005c0b82402c218074a0503d8005800c4030300d0f00040010f90300300041e80042e90512402500000103455214105c001c500c1d43c0080003440c5a0044c040148000d0308415802035000f050101801c01c40c907181c08080c0c44141c0501102c030ba00c2803038407900003060103008481c0700d0390040c4a031058808110102d0040d40c121020f58100500c0b00740d42d102000100700c0700440d40340c060084551103034101408503101450381c00e02240c0044116858400301d40c260354410114103100c02c0c0c0031490501858903141e00039a2040700700c42c000d4850341480e80d1805a810099866001c0d10f501a02c8101403109004490f12840703100e01c40940188403c0103600c201c480f04801c0d0302d0040c05107102149002c1c1c90849158a80210417542d004000e401b08507220020750050f03403100ca04c520aa031643c03010041410b074844900c0c010300024040d00c0000400c04409540f40d07005000352445200b0f100c0c0100c0c00101032041400e809095102d003110b024006101500c443c0d80c081c40190300a400100f41e250502c3c000c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 759295161 1250 759293911 759293929
    0x6051815060316090f0b031603090c060302070b060a05060d0e0304050409030c02090703110301030609060e0a0c05040e070810091e0c09110901022a1807170907051905 73
    0xf6284141c0b00381d0b41d01080340c0d02c500b0010051a0b0403405080041c1000742e254081c0c13001618000002e2421404140c6044c044d03084542c180b07401407004400a51f4500000d8081c0d40044d000b02c0c1c8019288000030018502030b2640d1094503006440b050070900d050300500001c0060114410891100f4000011207580301c0c0100e0010300d1081e6034411aa40b424414005030007000b038001001d141c00c090008800a0604080d681129000078005c180558075003070800003000c0003a8070300a40e0241c081c00c0014400031661080c00c9450607030f4100a4400449003441d1200c0d610f0080c0c0940d50401002040c10591542041001a001e0703201002d8411051540501c25018018202e43e980d84442c0108403800040c4907a001c0200060190303441e15152500007900d4500c0510650145020074411011038070102030162074507200541490400350700c10450b0510070004a811000140580c000c0b01f03402c00c240c00115000c5c240c500020700f119410041005005145664441903408075071000146640e41d000758 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 759296411 1250 759295161 759295171
    0x16060f09061104050f0a1d1b0a08011401051303170909041515030f20040c111c0c0f02060f16060c1806120603020a0803030118060518150603 62
    0x302d940d59490300c1d050008000316400c1c414800c0e600c0c510700b0031050360b0b40032007080303440d1881281c984680e817403641c0c1b0403110380690280c460070301002c10035410f10b43e008031000c1d050f12044906140182c980800440b13a81c8260902c00700075452000e420800200c040c1c413403041107500f40c0141030178a0f070301070041881918100c6003550051030000d514641c420852241083c40250100035900907401c5803142d00001c002844020003000101c0821444001d103199807034211440208240490500c003140207114409022168001e40101c003086072058030310032140c0c0c102854903210051090070f20303120110341d00f01d10716081e80c01590070004113429200304001456211002111810f423941141802800c913104111b07601e0034040090200310810207a001c010080324024030f0440000801a807441e0054652540020b401440a01c00403418070000300255050f505c1c0f040050b108280d00340031860540d00707a4441d0790340001150951120210080352419482030800318008103103004480419019070003250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 759297661 1250 759296411 759296441
    0x20f06120103060506150909270703050114070e01050f070203010c0c060e280606150c0b090303040804060807021603060606030c080609060d05070306091203050a0216060f0906 77
    0x4010300800c0458440e403070b0410400e07a44c02120508070341124120b40b2840c110588a481c8c0000010003d8041060f010250030b5600e030382c88541c0b0307002c221080c0c1d42c41c2c060200b11205c0d42401100c13008030102443c514400e00c250382e9011506031441c001564258040f91110801600401405026840900034402001607507914100b06030703d02c0c00c2c4042151112040d141127508107910302900d0300110009880b4083c6812414589100a49001c000500441e44004c0d4010f5101c0c0c01800216001840200c1c0c1d18091100b4100641c0e0722120143c40744000c40d00105010310510051108510030002598803070700380d004584c50b4181823100b11090409030350040383c40365240e01d4240000380d803500030084040c030581040c580e40c4c05d01d00002181e99100900c03460080c200300720008103000d01008450021a0010401c000e20040c5d828240742c15a42c9403c5940402d0802c0d0200e80784030280e108070b8000303024405820011090546d03541c000b8107115401018403035101c00c00c00c1c01003059803052074010600c001e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 759298911 1250 759297661 759297697
    0x15040917042d050603040503040f0b0d0b01030912140c01181208090d050f0405030f0f1908070f0305120403050306100507120f0e0a0f09050a0b0303041202010201020f040e06032b0c020f06 82
    0xd0ce04c0c100391b992030103456042501341303041900040d1018820b80d0010419040440815003a41110301c0345024034100a0803030742c00c0c80b10810010103200c1482e0091405184d079400802c81078401030360480e03401e0f074800342d190340900044035001d84128007074200f07280b031201043d18007a42e900003c1d1603c24078030080b070700a401030040d408000e20100081000072416004140900481e922452a24010040301604181c5040301d58420144144100c1d1040c207440492000b00b801c1908001b4240c0e00101c0b140da000709508083c5030301140c01340301501c50403680100740030384c1075600c80400c80710b401d0380304440700a0001a611482c165540c9190020282490f5040004803d184c2044c100c140c40e805800c0707002240c5421003c1d21180ca001c41142c040d90304000c2d0180da007940300c2c40100d0082c0309030310148811540108001c0751000948012500800e8104d003103c001c1050b81c044d1400312948000491407006ca0090f040c40b1280c02243c01c40305ca80e00042c2070303003c80351521020900c103900c90300820410b22454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 759300161 1250 759298911 759298927
    0x2030304030c1d0702010e0d030f1116110a18090f020a1206060f03020f10091a0406030c1e1d0306070e030d030603050615040917042d050603040503040f0b 68
    0x55804a58401c410b1710007405543c4640028948682100f00c08008154403040440e04c80b40890308130419480050400c550348528800a010055005160441d158000101c41040524160000340c0650f0507203941403980c0c0e003001d16140014150808100c800d14021031242001d82c0e42c0c564114014400c16540004000c918500801212142d800c10070f020315401a0900246e11520302040c1075020940b48824842d04800c4142c8030f1603030607448503070450500510305828451070805002201e14946044c0401e0a03070500c00c6c2c030007060300e0590881e05c0000d003151240091194603c40700c811701e4840200088281c0401090821030100c4031701001c104503e00703041c100e060801a21030881a00c0c50308000440c00c668905458000207080790903000b038120b102d00b025035920f03800386150340c0c1d01942d01090a00d990120010640051280031000c1904440000740303418101c940d44400c542040d14146501d09000400c1040c1e0400340082c2d9040c4001c2c0804074034600d45103400d1000d81803211140d501c3e0340d80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 759301411 1250 759300161 759300209
    0x90a0b040e0f030415050412030c120507030e0918010e070f170706031e0f0507090515030105060309240f0c1c0c05160c051e150702030304030c 63
    0x1d00103070400c0a5011103001500100080241e0b800d4030081a034400b0174811000003100d039800b070358124000b07034075440344514100350b0441c0201110501c9600035900107600704209607054040d0782c10280104900e01e8040b801440c0201e11310703038440003044401c18440e8221001500310341103014041e855902120041c0186481304059600070f040840c12601750500344016140c94581078441c0105050f12502040038094000c0303441c9429001c031441c1000110300b1486110b010300410b030f0744000402c0b101c04000c1b980d414065034400000300b0407840d2500d540d01e020140310160380014980607035401882001074000704080030200d41344440c0001c07170a26040c52040300300040740250a10f40501c1040064616442184a00c081c0c8484540800140301c540c0e040c05540502c01c13510111a00307030b01c00b155030003089001c0008009842c0c0a41c1d600340a4038018007540703000c4519a00059100101104003101c40c2d0400b401885070354800f40960741000c0d40c80c1d4131400c814110360840343d462241c494802c021151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 759302661 1250 759301411 759301421
    0x1e190e0a0807030201050f0313080c16050901080d080c070c08030d111c0903230d0b0f031f0209060a030b01120603120507020301090b090d02252102090a0b04 69
    0x41c590003030440c01d455580080c2ca0340c4541e0840082c01d070004400248034044030401c0d109426000f07a00240d551f401c8103040c9484400d81503c24160a4030000040743c1410011000c505031030786000140b012070160203065401080080c4003298120b020858a80000c4c100503030440101203440045840d0100441e44009442c00145421035008083c4091404420300390f0b440c08001c1071140000807a1000f609085843c20b141500d288501c05040c13511441110b0b082009240003d00581c0c10411500400308011030040300d6000da591550018048850010142c0f1800c051804459001450100744001151403600720540360350100740c1e9440b2440265800400b0304540f000d20082c20411035045903114500f420112820030100700c800304064003191000d522030404036030800608502c40c980070f00c04d40ea80368052a1410014025045500808183c074940903c082481100040909050450f038921804209100d04800c12040310701d8030150300c8113401075004000100c000f05070040341d18240000d0312 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 759303911 1250 759302661 759302669
    0x6091a0304021804082809050d080a051b011404030813021302030c070507080c1801030b0601030930030510080c0f03010b0a0b12010f0b1e190e0a 64
    0x1810030420080143d8541e00b04095403100192100c0094035182002d100030701680100034006e0901841d00960025184224410089543d452505807a114401e0251501040d00010403609042c800d035103034207006501a200b54501d0440d804114803042c0d624500b59104c01800101c0400c04070140401e1690040680d030b4001295101e4001405181d07012540d58100c001da0504819808008110401d106c0c80071601c0254001c400c407041d0f1501d0b01c68003a10b8104001e0994465001c1500545094103022070960417130f604005049940d03030b521070040d400381000c9503040380ca0030701c052030040032150481200d00300ca0752059880c5552003001035000d8100c442c003904c0c604010382018010814650700250303060915000f60f030540748031302807100403a0141c8482f0405540c400c054800c0410750740b8004004d0640280505035450240e40d0340d04003084080d420780101c1d0181c0b00c082000b011107940c9a051514010841d20b80c1e40d1401c4e50900020a040e2444400800002c0000012480b0341c904646010058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 759305161 1250 759303911 759303959
    0xd030906031127010302090d0501050f1302010504060f050d05070819020c0d1206090e060708060118061b051b0f030606011b0501020904060312030c1701060302180a0609 74
    0x1c02041c00c0c200d00c0003503051061401841020f0307031103403070b44a038040d6086d944026252002c6901103180a6000e09400c45004e41ca1002c2c2e400000c0e00042c4410b00e22103800d806031240303840c26051080c215501884401210140403040040302d0f0042024482e66104080b1a40c1d0203400b4100702c0e85443ca44980101031000c59070044c00302035101840030841607486203c6042880800000c8200321001d46032903404003501d185065104440d4080118206115125640d90255540c1d12000155040341144021045075110040107109450013040038401d03140d0402c1c03e070600441a1350300d5034900080240c00010409060004c6502801d012261051411084000d0305c12490000002040d0030001d960700b080c0703c141510b101050040a50441d54005000342c8140212600d0b410801a030840c01d03142800060315005030b03504118030440f0b079071084d050780c01e005d2202070346801000c5010f50041009002c09810007801c80083d590780d403010b00014416500c0f1326410703910741b4003a200c2e803610000390f04d025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 759306411 1250 759305161 759305167
    0xb1b1c03020c0606030d121a0d0506010f1a04060f0302070c24020109080d02030402150d0603021c150e10060e09060903030f01120c030203030a090f05010203090d061a0d0309060311 79
    0x2009030040d90f203100c4140b1f40b140000d402c03003040c1c0000580c5241c1c441034940118070303030500b141844004510342c2d041e40c124407254081c1703a558485a11205000c001d55070780c03085c002e000071b10100c0e208d2424031702c11030300924001d801c01700036032217000b808407165016200e141024140c0403140c00c2044444445460140005c0008441c3d5072a00c00c45072145a8040b07400560005c0020b04640e070301e001002c14a20700c0c076121620740100c0c0241c03500800c61360200303034030440ca11481c2500c00502580c44960050348603000c108540f41d0310780008040d00d582c00414469015000d404c403440c02c3c051090f070001346811034942e43c0d18200a0111400d20001a069448a8000300304001e4801f82d001c1d0b12070704640780c06111a01840340e03401d100b0404922504000c0d41800005036985845900c803c4610644010706440440c0310364690069941e4407a4041450708854043d00500108149610604207410780441c40c141d001c4e0140700003403a8012070302c07040f03000c900101010f000d029850320921510901030481075103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 759307661 1250 759306411 759306433
    0x5030f07170f0706021f0920040b06210c04080d0f0203070605010801020705070501031a04110409060618090c050706020307021c0203040e0a05010b1b1c03020c060603 73
    0x2803145080c0c000c145140618441c0d00100340010004140007803200400c0d14403944d240c0000035190b4403404041c01c039100d00e021026001d02643e20404c14036541c4003c51103403008103c081d40e180e5034a80001c0d10750040d55100100120744078403008049848800b0348440c0c080710480b400004412010f04503109418007404144141900080c502441007001d05100b0901848520100d2840c8140740307000702001d0600e400042c0d0b00c1415005015064420780035124550b855000460491713469205480c0076004501d24001213092940c8610580c0ca6001d164600c0e0503107905542081ea6000e50020000800303039404140d85030743e00c3d0401d034094000484180310342e42d6200401407031740c05414000b41c038a660020110300e07114020002150722128006940c2c41d44440e011029440b07030407038401c16032480143d4001500e250003500c105030582d4030180c0b0550038611140b652511132098901c107000b084c461007408c040303c48044500308400060340d95015a407002c0fa002800e05084001d00414025030208074560 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 759308911 1250 759307661 759307663
    0xe031609060e0f180f010f0b010f080702101503080304050c0a15021b060d06030b18280201050f0f040f0e090a0305030703090c12031407030c03050a0507080c0c040605030f 75
    0x750000b00c103114010100e40550607035820401443d85c1c01d0141d40ca00780d02160032999503004040491400d0700e841d00e200008010030343e07040004075003500041c2c00066982071924080c3d841904640041c910011406440b640e80d00c4c1c4642c010759090342e10f640040c06820040c5099207400700074142e40ca0304840e01e00c110002c040c1d03465111070300100306500b803601042c1403078070368200791000c0c40030a803c248003080d40c9040c00825480c00307446458003980008001b140040300054000072820301d444003a560072080b50180d940203a03c51004a040101c20010144030041a001403c100041058510781c0c0b1032070409401c3c5a0516a803203800c101c036180701041544070021401c0c1d50120740506185d6529980e1200445c01030104d410300030720304c4c0d445000105800310b610300e50310002440f98841c7d001d03552003400c03203450a0143c0c04000340010165942c06001910074070103026130010700d0600390b0030510103644107075451700005803c02c015070240c1c0705120b0a1030240070310002050281e01038807840c00f42400c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 759310161 1250 759308911 759308941
    0xf0611031c0e0a0f060c0207080c0f0a150504050102010605100e040e01061703070c050d050a14010b04020313060b0603010b2d0316020c031204090c0e031609060e 71
    0x41c074041c0000c03803140780400607082a080c02030b5140594041020902d400d4051054482c1c0964a8624022241400d9400022078106856002000701201151101081840076011207400d40100d181c400010300302c04121026104105681c0f01c03240c8840c14a40024211a080d51002d0b12850312040e02188003900a546450400c2d0b007540d0104240345060b11542c0900050340c0700040b159000e940c07501c0c0c0e552020029001c500d100e116440c094594501c1000707503100034440040c09680105072a00300090407000001d0b40052136000101d000345541c00010200d0f0001c039880c140e0501aa42c0c60b1080022a11400c2c1c0d902d68101e03015411365040041d90759560080744035010381214030b410103410401c0c100d00c040e40f440f518401041e41e2441c06400551540e500078140c140980700e002c001c184d5514021407035000d0b242198000b107092600d001c55810103080b0f54000f49042c04007a40d82c690032a1014858121008030000303480701810b150151001c01c650503944142d89240c6950300344940c0c04243d1100d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 759311411 1250 759310161 759310177
    0x6061809040318080709051006090b0703020a020319061506090501050c1609090210050702010f0516050a030801080709180201030b13050901090c050f090a11090a08070f061103 77
    0xd2a00d855641d450309079a9070348440250a4620302c0a000000e000740006134544c1a150006024071050702d07035841104e044803480c09240045041e1400030b0104240b02800740c90304034043d1040381c0143d000c50b000b0904100080e01e5074001d82d403000d1400010302c241801080d458601201078800210720707100004042441d103010322810401c00250303541c031485040102103100c40035004d044040566542d003d17030060080540880c003c03050521000342942c0540250780f10103406855001e00454512011070309503020508621010070f1001c480c202140d0100a02400e00f8400d40703c041036541030205803072400000d540b04654250525240700d80c0d0340300031070452080650a08001c00c3c2c0c05120303c0001c28905690070078911040c81e210401001010541011307200a010342000e201c0c1540740c2042c419025149045035801c1803403207002c100c0c2c1c403031554003500441c87c0840a09040c110700000207400742c004c5510000c86c940c0114070a021a803440c4400400400950900c038036110409000b00e500c6c0d01503042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 759312661 1250 759311411 759311419
    0x21c020c031b04090501110301031a10210519020306011a07080a02010b12071d0f040b0907050411030103020f090103051c210515120a1412070c0e060618 67
    0x5820b15442d2140e41250b4801944a0003e10809a8030341d1110303050b070400d01c001d84d00301c05a40c90032100c0408030b103070140c020391812154802840c01e24034840500c0c101d00c1084181030030803e4100c000308030f09009204450841a180c00b4102c0d07214010140f4003801a04407038541c11031100206907010b40340e003c440f00c0079846000c0a07154510004140c0c0140b1030f418001c0d400202080c50803440c1040400c0007003d40305000445d0034402040d0383d204c0c03081c19040700d4007511b07070a116000c1004501101c281ca0ba02036801c004030b503c2a0345810218090700e02140240c820020040014411031415210700703000301d4400d0b600c0100c40d600d0350302d441c0e5403000f49402c1c50035201444c0c42c88020303040c82051a0400600c621300c40207112070b007030b00005004003001c0728241c006441c2c4808110722813800031544140c00081d000140b441c040346032a03010440c450b81c541002c50340303d080900021104c0c440d01030800c0300c1c000d0210000c100e00e000e00070080300d040100918415041040a4500900401d4060140c07940542d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 759313911 1250 759312661 759312703
    0x40608190507021501211401060f0b0904060503030f07080a09080607051b0a03120f020d0e0f060a0b060711180c031f29040312021c020c03 61
    0x4808081103404488005450a04000c1042149034001500081322034406100c6046680d81c0c0c400102060440108440e0049110031031002041c40180412110420a0000200c3c2c6965a00982c500040340e07001c1402680c0120300c020f658a000c1c81000c0c010b010950285103032614034040c200c010711603050000c0c00703082d0104007000300d14810311256000c0d041e61011180310781030407900588950000d40090381001111200c070108001c1c0404d81c80010341d4981c40d502414200340351020081c00744114401045642032248074158076860040a0b1422407180142000d07000c40b00034242001c0b802040c0c031043c179080010703450180d1244011160078030342100c422414001031b00b001403150036080c03001094000405090115501800c0c004501800100301d10109906100c01040c40201300341c4a445e410071903e100358000f0042d0b07602201d41c203420f0a0b100c01c0c80c00e5102d0f581e851480000105031001640491540c032441d41c02c002d05128140280c0c001060301c0580180000c0d6191030072599440900009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 759315161 1250 759313911 759313921
    0x41208041407080a0b0114090606030a0e0109060e011404030804020402090d0b2e08030304080c120406030b04180206070201200a0605190507080f1e070e04150b040608 73
    0x807401101d560307028402d4500b401d80d20441c00340d0350300c0211802d4901a02d0080001604400c1a00b00300e4129070103825141984d4852080280942005000811503034603030341807281c00c042c284103031400b061143c0000100e50302003170107941c216480326030707400080b601080038800481d070004006640983e0403900565a400b450000c100c801c0b00c54180200072484190900004e024038001c050b860a49041910b4940e07032040d407100100c100280702d03411300c5800810105001c14595402008100c42c0c1108490f910209915285a15030240e800080000d43d99080400701b03180501078101c408c0f031040501c042400003600080c1c50391180000003414080445134001c0310707100300804201d00e8585002540c0c61003c05081490142c0001c1720b050f0088a289483d40a040da101e1180754010746c05c0c1c0e0b499219035502c401c10986110005044402c008480300c110301c00e1100172043c8030740700d03940355956081d20100e20b6003071205440600206103a00f0024900903c51b10340b4a0050b070f0100e0741c2501c3c004003140c07a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 759316411 1250 759315161 759315173
    0x13080c030d050112050d0203270a05121b030102180d05070902040b040302010806030f0d0c0302071509080c0f010503060f0a08010c030e0d180605210106020c03010e0604120804 77
    0x507011106081070305000c00060300d02c8400308a0030303d4500a00985040e2030490600b261a48150404036580400c000301400700c02c585494500140395010f00601c0c045034030380e80016410b8007408407045490344042502d0482c3d05d04d640c0d01140c807040035002541028061000020140313000f003080c9029000c16011803040c084100808001007a42c1e0004550310740d12008020700d41c0d40103000503804100e1800100b80c150600044007020904410302500c004d00a8041c01c80d900041160150300b140300302000499110410418000507101545481e824985850081e904200302002c03503030703c02d10300f4035001485031360050104c0707a00c00000c80d00340140c003001c080060304c90a01c0e9003224881c1c0d0311748400000582d8065100c020200e800f24207c038100b41105030101e85a0281c1c00d001003100b0300c00a800c0011f54010000303003600d07a01070041701407114420010595440c109a1000006922aa441c81040e0600303226680c1c102c072191025144a00d030030b8540381441c5d440e400c81c003000c00071100001014011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 759317661 1250 759316411 759316417
    0xc0302090a090209190f050906060408250e090a0305031305031617040305070308090103140f0709080d020309090714030106120b0a15080603101515050313080c03 71
    0x3800400800381c407521180460000c0d0041c001650240c002c070108000100e420000309000c58001c0050301d8845400d220500049440c0035144a40200c414070000c00c07602c0c010300150300e80c11005c07480d0090f03151842c0f10381a50903c00750310100b04080d2210a00c00d80d181c011030055081e81d01820103507642e031038018020b80c0460b86001d019003a0700011818188134008601e15901890140c40040000004026094414410340c031001300903901c020700800c0040d0303445018000794881414005401000030001e0012880c00f02d90300c45860543d00e080140080c0c21103c0040600719120041c0414010302c3e001a40d40d201d02d041c0b181c4143c04640010300f209221704030340741d207101500c68200d03144d5940b0100035010704285004850140d050004140e17150600008000443e14441c1200d00c2ca041481410b945000300a4145509809128030b51042c103080382c0140140c03036401100c9017403840d141500b030310000c205401000003000420402d200e9001000e0090407041c1c0d402920460fa140c6034280309a01d144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 759318911 1250 759317661 759317677
    0x90d020111070801020c0105060609010f030e0a02040207060504051203070507021c0203030c100605010c080304200901260d0e063006040b19060513080708011d060f04060c0302 77
    0x4842d02c840441c002406401a02c5905980c50091150740c84510420806003c1e9840c01c81c000307045a1000819a80700b1b404c6564200c1c0c2540907074034010700075008078050342d01ca4807082d905251144103000800404001806078000b21a980e2403c43c24615801801d41c41882c0002c0d20403940b01888080c007603030f0b503203007403030016401070482c1d5603102c0307024103d034440e170486411f524040d1030030744000b580d94003450728100140d90002c0554910381c0ca03562500000c001d101c845098142c64505004180c0e180d8541250203004024540a01e075000e83c000301a41704190304100390b0903003100f08420011038104031012015501229182d486025902e004c2041c0540c2d220402400c1202d40160003404688107141406410250f40c1031000d01346400902c144c020b10f00c081403502280020080048922a50292031060019104010032039518800503141540d584c02c80f6501d655215030f10509020442c10f031010300f03003011024000f00e15228440c540c0b00d20008002902940d00e076004844024807aa04a81c014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 759320161 1250 759318911 759318913
    0x3c0c11180c09040216061508030405030703031101020d0f150936050102030a060e0f09060109020901050409092015040e0727030209071d120c181b040506090d020111 72
    0x202d0050911b40c000c0c5c001090705001c01170041c036003c80c80c00700102c100d409445014000f401c0322491660b0865110344400040c0e60b20f554248410400029140100d00035145004408a030943d90350782e107010295072651150100e1454100e02c40b00340000c040c03280c00308107020710324500c4944d0070020360300700d800d180c1e00001d00030f5100104120402300c0aa00002c02d0b1118811056040d5440c81c5075520038490989006810340d005000401540c1c42c0d6800070803001e103041c501541042d0381c545549061300c07103007402250140c08214118503403525444d10b01902c0700003100c420b103210b003440000d035103140301f2030040d2800300c00b16100180c4c406000d503034080caa000410614000303101541d100c801013180f080c00101d103c2c14a48012900540c030818499005128100c44044285004400c0002203016464a50380c507001d0544c240f1540c2e40c400b0001e0300d58002d500c05031000d0f464800b9118010340d070403003840241e50005000c10300003500c824084d90744444003070b40c80414000043c001a101d806680b0302c05480303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 759321411 1250 759320161 759320197
    0x2210c01060e0c07051e0a06110d0207060e060c04050d0f0f02090f1e070f12061d070210020a1209301b033c0c11180c090402 55
    0x505914a001000000c0c000c1d015601d6007805074001c0140c28800081046c91540110785000c045011a841098400d240c0c034481450281c0c113803e50310680c2c00070101500c2c640d60f10032903150303401c01c00e1081d01d030f021101d4100130340380c42d080c030000030b103400d905000c0a056600d00c0c00d80c1600300002d00308607404141c2c0050010b007a6241c8a040b4581020003190306501ea90005403c801c1c1040000c440b45019503030b6600c41d401c00c045c4c0547e048400d012042c411200050300c03098001404882248044c0307034000d208400c60104e18100c10064600009000d900c80011310410105200603484040300104d025070300303808a80160b40342801e010781d94801e017143c2c00030314501c905408410ba102000c0c0b50514520740f105010005c20720078809640e80c4c648130160115502d4a80c80e0b00a04010700c2c0c40c0310036017403090b0300404c0c488400c141c2207014024140d40340214185480860900c4000c01644280d20f1084440000d10000b80186c5824007101401c04e04040300c000c034025045070341b250150740c044e2015000c00b2034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 759322661 1250 759321411 759321421
    0x16020102070f08030411010914060d0f0203130b0903030103030915030e070603060f0f0b0a200708030d0e0f100b0a1e030615210204140703050a0501050102210c01060e 73
    0x40c540c2d00944040706e6280c0b00860455995006540714000c9540410342c00510441c040c1c184021980518505071131a550b45441c90710580e6244080d5005149641c60203840420920717105a815801502c0c00c04035500c00d10040001943c4240040162624004101c5845500710800e80142c015034000c0c0780b141c0074424001c140a80e141d03201800b21800207560307001c0710f6540c8000d008a41c46e54001d01a0b915010400b240030f440c010b0b148503100b128847d21034a1081584800c4e02d0900e0711030341205843c6d8100150307411a100041c00b54840c4201c603240a0032004072030200caa5030b2030624442090480e034840604c2c00c5282d0b150260180100100c04000000c2d1100300e890040324200e0b80401c5071210300e44580c080481829644610031348903c04004c080414079407060902c20043c04a00301e034420340322a4542c0c0312600c1c030f0f483c282c0100d056071804102824688940c60941d401604030034115844030809100511140b4101c903c00107039a0761903030b070350042036011502400e01901310b1140d510b000c0051103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 759323911 1250 759322661 759322673
    0x90b030f060102100b091605040b0706050103021504080a0f05030c010c02030403050d050f03070c11060c1c031506030e031210030302060705090918010902030d02010b01030b0904020916020102070f 86
    0x2031041400340d094a804c840b010407480122000e002041c1d8000f0701d80800603d225070303407240f801003100b01420038505103542c2c1c65400141c2e600885003221400d440d60010400c500b804c800c221045054082c15904160409909594481c00407001030024030350098401d09125041c4200d03080109440b0013801902d40c4900301a41d07d91103444215051b2098a401d0605507110b0810340d03010801e540c8da0146151943e0804883d443c0082d0300070350b051410718079900b000769200f81c001d0003011000b4015000301c440203400c03030561307103003900d4110b00b410b003002e000c40002c0c91400148010b8a010b8140042d0302000200c4140c41e6011761000903a0b0580102c2c203000303007a5603001d444d0b000c134ae00c0380e400c039041a69505c00403101030040180483c3c100c087c01f4081540416045500c09041d0b00b900300018500105800007440d011200c981440581d550346030014a40d40e042c000c4c50040c82042d241101241800d5001c145004070042c000b07941c141c03820b072200c1c22403032003034046494884d040500c141c2c014002e81044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 759325161 1250 759323911 759323941
    0x27090703091b0e010b030a0f09030c031701060806040e1501080a05120f0a030c110d05190c08180a080307120e010e220b0a08030301080c0306090601090c090b03 70
    0x2a82c800e2030414010000c0c0780c006021200f51503000c55200301c503903c0d00c403211400d40c1000e800e00004c56291715545482c80d10502c505644540030385d459a68001003418041c020a10503020542c84d20000300c0144403041d0414a40d64212005903000100c0b0b40c41060500d003404a4522200720440c2103000016010720005004007605008009551340068103103480030b52480340903803481010388240004d43c1d0f190b0096202c3d8120301945d09004d019110041120360034802840303310008640c001c56103011140030781c500356403910003505107280301c295a515140700e24000c1c10100c8500aa010601310303c09d482d28a0010000c120440803262107040624200c020f90001410850009503c0101402d866110b44140034040b58094070380c044417891007503041c104101e04c0341c441503000d82f00c1c00c40100350380700d00c540b541c000e003910000755440e0750610608074100702c030740c0c1c41e442e00ca41e1284061110340400440d42c0c0d411140100c000086281d4041c00540e0819131550060035261000f2040203e42e006000300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 759326411 1250 759325161 759325163
    0xc150c0912070306110a0e0f060f030f1f03020a05090903041205011b1707140906040602070806010e010b1b2103090705060a0c2d03120c080c2709070309 67
    0x280617040e000003c1e09050b000f101c4005001440340c0e0440c8007607040100b4403012404c00602220325010149151f030045510513504002c08542100030000c003003403032492000e03820543d0400000c80b60b01c0c58001a120070b40d68090b60303121351500b4010480c020020800c440081040810324240c1c0d41c0309052460080c010000c5c0b020030b0ba42100d03c0b00308014410140a03000001056042600d0b45410404480c3c484040340d403a24590000c00415070300703503605000b070001058143e00501c26103040c10081414010180c0c0001e0141002400501480891a040e0355902c4100c48031810f0001c909200a440d0a0b041c80c50080540413041060750500c20050003144561400d800b03e031035140e82c400c00e03c2198801c42031b1400020b40c600808100082c41484102609c9141000d15941c42d029102da00c0d10640c403c00e0300300d0200d107180401144510342401290045080da00309140385141c02c400d02c485034411440b2822902040419492100c5854400350014800142001d9154a05072030007500401c407481c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 759327661 1250 759326411 759326423
    0x30309170109120507030e041b1e02030702010516080f042303061f080708010905070609080304090504060917030a1a0a0e07020a0b160e060c150c09120703 68
    0x1440c0c004051050084030326807503111260484405070741d10304640f1900a00d108408221a42020350940c2da80d5010b900780042c1102c501040d40d40c1d0030309016000f03600984a060a0032004140030480c1c80d0040191040d0036028200743c0c1d500d501000c1070145103030b61210000c205010218a0b4610310618101800a459110000d011720101210000c1040603403500e5003039065000c080021000100ca501a040c90781d01d00c10302c407010503100c901e205e041102640050280740e546403610f000703004082068000420260070650511401d1541c10341c2c807481b032030184141c0c40e91a40041001c101c40d55003c050856080b414525410300074200103e090b510070b0700c102d001c60341030030500c100075091615a030100302002052400c6003407030190301a0a404c40103005c441503008410300324020400d89562035204082c008650201420a803030007034203070141128402d0187d4802c0c01201b003104070010720440c81c2501108840015030701c1a4000c14a4841c07001e4a9412402480c0744030781d01c600016180c000c1d00e00c225 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 759328911 1250 759327661 759327689
    0xe0d0c140d050a0f170a0e0c060d020a09060906050a030c0923091012060b01090e181204080a15020d062405130b0703140403030809070503031e03061306030309 70
    0x100480305120300c05c9010b00d0403007141021440024590b404080d9a086880c1500ca1503000312000078143e8202064030103845070009000360b003080c0e011541d0b502402d8107050040c503a80c10700800500600400120130141603407020400325881c014401c42c00200428014404000240e0303010034a04409082060f0181d50340001041003034160340d0074030003a258801d804000610700b0341c940340081c0003200d441a0601918a8012480c020500490b62041c58031074480d85501071040c00c62484d102d038840c1034402800c400c1c0014480c10a01143d09001070b074100300c0c40300b04001c0c42004000240305081071002024038090700000c808079000624002400251400d4180d17170a9400700752010b02c910411150144003a01060000701016405044080c0c000d103400140518250398024a40d84140c00031703404a036900e010050102e1003004218041c01e810b4001c0c608110071807549560784046a5042c040585c000700c0010007684a61406000307061810703c09204465803800c020303100541c2802807c2c1100048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 759330161 1250 759328911 759328937
    0x210b040b040f0c03050a0c170d0507110d140d020c1e030705030607120f050105030c0111070509010e0405061303080112030c020d03030e0f0c0a05042a030b01030c030e0d0c140d050a 79
    0x120036105a08d9040046c0c008003080400482d003941c000700e022140c450110144074100c0d1950f600560742d1a10071001f86440f080c120900746d01c0d03c594180c4160440d440381c1c1d114038854503a11100c28014042581009841c3c0d065800281448107a0304102c0c2c152140200308007d0036403022500340d40445007101041500c00e47c4c14203034141c0c1c20034040d4a405038489440b518640d4810000c843e41100c01a0640303440644400024400c5030003030748200800541103080c001801014054240c0010304031940d0810217201d83d401500074070341446040220b10800d80c250040c11f01072007421403019401415008070900c149030203002003d95482a000030320484a0000403508000340014a10000501c0340111a25200c01c010103007508800030402c1c0c1c20240041c001a0000f200480c9400c5003d132408141800064001811112803486031130425041100c46000c411340459030944107003007464038800c2d01d038036030030040b101d540301c2c03000f41c0b14520506c1000b445007541b0001a100e0503104e951503150b22020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 759331411 1250 759330161 759330179
    0xd0b041407120b0f1009080a030e01030f0b150c0a05010207050a21051e070f05300f0c0a05030301090c0905040c05120603011805010204210b040b040f0c03050a0c 71
    0x10f50300e203810080e41c1e58066180d240120011155031420702e07001c040d140e215030340306003000c5000e00c04902103000f00340e64010030360301400340e01d010601c01d0700b0800c6110030703820008a88181c0801d038003c1c00b88001458107071205045c4001e0340a540c100c402555105103034600540d680d19030600a07122003c091091101440503820b81d0328002d14580e54650500d0b405061150114031000641802c154042100c2c1e00010100301029660b14010030103880710315104124074000301601100c0200324030341c410181c60603511003410303228045a40b400300ca131110748049182d4903095070680050301078400170000140d0304825801103601620700380c0d0341c500c0c500c0ea1902480282d954401000700480c009005410001418851040d4013007002000030496240d107445124080e0100602998641d40000e81884240004151400c0c20029504014502082501d031001c0860b0050801800384007400041010700000b0a55807194540241d2180121030752490b000340d070703035804880c22203020010710f80000703100407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 759332661 1250 759331411 759331421
    0x6040b01020303131101090e04080c100c210f0207050601060e01020102211308040609080625082509051008070807050c03040f060203250206040b0d0b04140712 70
    0x8150454520ba40341c0f9642c0e41740d592100d0302e207213042280440f00000d51804c0b0b40b0907203000c0c6008600703c5d99626082d110b82c904020b40d81800c0080242000b42c20f00c4069030000494154521194030743e07103441490b14104002e0203292245d64042400071804c94107010000c680c40f41290001d8607040300c40c09450005a09078040c01c13189407103954000c47e401c1109500101030035800a41c3c11208000d11101d40d848a107160426046000002c19550b01448402c8003002040e8100c08041a4120f161810211910841400000c41c0c5e0400541001040c0c0140908880c11203007403110840101601e0f2903100203001164a204892003100b19001e121030b00307400380d40e00b507000f40c1d140ea03601803050391030346400d0b246c5070700000b105600c0d88000c000010352224024044c001070212035010715a02e044a00f0344110f541c81c10f00700600c2180007200303a01f00594594040750100c2e00c068206503280c0a400722120020909181c0305900641401c0c0c0002e0340b2070406004a1068030161210305442d2140060302d4200c1d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 759333911 1250 759332661 759332671
    0x31a010f1b1101020712020904061d0105090c0a06140307050906040b0a020c090f13030e1503010f080606010906021b18090c09100608010902030408090d030f0314060d140c150306040b01020303 84
    0x508c0110104020030555008005c0a044000d80302c4000382d191908c2d039003155411583c01149070025100104039140c108204802803140d858000204003406a03071907924070010781620305000300051020b03199195841a1070042c00b0391810b06454000450340a5118141902e4543c81000240d00244006410070320480c060110303050682d50f03c030b0250707909944c4e82e10281d200640c00903400c0c8160a1000c0404000c60181100046416046240c00407451800754041d144e5414002544404d1224550029071502d17628241001440302400f42e01c0402c0c01480040c15200e00041a981004442440000c262829450079600c00c00685d0700c1100750424001107005c0c0c03a0000c0c0c0303032074010042031340190083c580150041c1c1406190161303c00c0010040400e0076811008200da0705400a2010707054411400b1206114401d0501441d00400003406102c00440040902c40c1c4c44507940300540c4204000010800054221072080c951388071001996002250924403540c108096680705502c080306480c014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 759335161 1250 759333911 759333919
    0xc091e0905010b030c180a05061602040605010c05030d1509050a1a0a212a080f01060e06090a060801020c07050a080d0503011710020409020712031a010f1b110102071202 74
    0x1880040ca40060386c942d22070440d88200c0312080411146e90700070040c44600c00b040010f46d141e0101c0d2040c4400c0d200c55070310482c1800641d9044c0c0021500220458000007907464001481141450b13a960b440c00407508148402480d0208020f0010450351164084003c07251030103c50750f801e00d0402022500d0340c000c80080806d09143c20000400f90b0403071152240c03140d0800200d20203164080d861107400309030103000c2d4400c01a410404000140841d044100440d402445a0343c240011100d25040290049024551803400559251001c0e030040d0b002c0c0c04600000e5580700d401001d480d64503111409098071a068010300064100030002d51f500b5041d0b280d4680500316883c08070400d400e0050f21071060000c3c041c2c4100410b1482440c030003400941940d01d0016140c4109007001c5d0107007505031a1a2092515003a01e440c4920810004550031030400d00c0c00c1210448503071000c0341c0c5d450031850785460a0303613040040b500b00100000c07031610018003079080760342c054bd86682001c03441d0203103c0c001c3c1d04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 759336411 1250 759335161 759335167
    0xf030109050609040c141c0b160305090601120f0614090d0507120309050307120305040c090207051b13110306190b190306051306030c090e100c091e0905010b030c 71
    0x1298031081c40d50022490020300c41c0d541187c04403103c44910050410840300200d2001c100f205d4491580384110070310100340b600b00024909000e0f0a640d5840c10701400103540724800201003000800c142040100781c1c4500700b842807041081d03c101c0d1800c026100480c0318003601e40b1200d24540f140d13007500c036034513008450104000d0b50010107034000c0c03203440b20999040c0410044a00403404102e501000120b01d07690010b05403a02d030504c284a500c481d082a02003034010404d1a02242001031252045908548013160003a03440000501140280b02c070940c98a0034030000e00141d402640c051442414103503050414040d507038003542c00b020841d0107100c0f03002c0300c01c0c840e0100b4000c115141d28500c66140c140000c0184d212030004502500310300003403650a0b1100c03028070402c44000001070090504504c00d00c0b282c20001c1398035449060380b4441c08040350b80d5003e0340c00014030641d6a0001451100704c112410703101e0a01c1d80754804400c0c012958218105000040d00c0c64100007100e1040c1190240141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 759337661 1250 759336411 759336419
    0x10e0a02040c23030f0717071d040606050405280314160e04061103060f040902031501030b0901151206090309091505011107061b03030e030f030109050609040c 70
    0xc02400400844020418030b50004103180c0b00480e08103644402d00b043e0b003522490201d07038000005000a11840c1081070655030a01005000d00a5076044074040c00d21640f007640644403503030003010700e0040d294081e0500a0003e90541c2100081c010b440c2d003600d80d04084041c01c003d0204404c060b0400f180c041c0c80d901c038100041400804604200b1401c40140c0e085030f4540e560f01c5509128580140301e101120f02e00307202c10040c19109807488090401000c0f030075441c1040000e14843d08440b0708078000c54480701c420b0219035040c410001540c100b065003039140d5840c2d0400176000d40b0211445a6198644070055003c441440603e208503280c1c941220505021941c0703080103008550000c805200043c00082007000d4079008903100c4c00c09815084a95904d00b000041401c4800044c00d0459001002e0034050a64402340500b000309002010300d120300601c2c0360440041c030494810032101e00000c1440030b0f941c040c803801181295041401031040f0f803500420000c5030a02a50020300c5000625401c00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 759338911 1250 759337661 759337669
    0x702090f0c16120f0801061d01090504050c1c05040c050d080702030a1101090e0108031e07200a060e09040212010605030a0501020417070f12230a0b09010e0a02 70
    0x3640180c205100505001800041c5041581c140300203c428441c15008090403507032201800003500b9043c6000119945001005003076014411411085044102242d403000e90203440d03030a0040402600801c020300d0000581400c1d50011401254004007106096000c11401c4c0a040d02554201c0b1a1019242c40e0808120030b0480b030070320440f031241060040c42d016a50a0160300300311400b50003070081d03100401000410b0b400c42900b212804000c41c5005101000d00001903d032640030615040c2c0f4212040c101201c100c1c02000c81c014402095418a540c025181d03500d45c10310f07414240c4115512035190f1006552141103034160940103c0030f9030004000d45407480d018007081180200025005480d003000c2814039150042c1238030b8680d00010100b003913090800f40241e02a030004054a0b941d420005a40321005d41d07031007800312007080540310600f80481840500559001c10f0780c00d000000c512040d450711015010000d441622001001680c41a810f008140030000500054031162180790b00304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 759340161 1250 759338911 759338941
    0x60216061b03110d02062508060f0a0b131401090b0a140c0d021e0f030d1e0e100e01180813031b210803010303030f0f110c1002070209 59
    0x41e0b003002203080003e045a40709001035030301c0000e6940545941e103030a80d91103681c081c03403084901c2200f01e114540c8000c203034800086500503400711070481c0080c07000f80001e24aa461904425401030002075022610741000003841c0454942e04a461b0116201d100190765030310151042c000040740c1001910806441103071441c100c0c1c01c0440003541440d02d6250790306d140c425035500c07140c09644079101074030b55091a41c00380c0302100c1031100108102d840d802c0b05d00d5200d01520a100c0d611548410040d4105000500d0a00b80f611540100300301c50b4801c0203032140d840c0b240f9202600032074603120080f410705c5018040d01c200908112100400e81d510340d501c03a111a800400c03009c8517010303558004130004844091040901c0b0411250803181800c0c000c000701c00d02c1440c0c0a14849060580169000620b00425a8116505400c0002c1c480020000d260080e2400e10000298580f80641800e01d2600311005010000c90000454082c0502012050700b24468228080c0d4004003c40000b05252400540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 759341411 1250 759340161 759340163
    0x8061f0b0414030a050105190f09030c0212010b090f07120b091303050f072a06080c0c010921020d02010e1b03150f010e0f071e020708030c0601060216061b 68
    0xf110004136440d240ea80c00c66400f540d24240341886032080e01030500182c025041684601e200c20131052600e950302070300081c1820300007800346c082a07010402140080d030101c0300816000d801d0291601d00020100c1c00740c0411680540440c0b0705a818125031601c5100c1c034110420060802c11864591010707480c1c01020300c1c4c1049040242c10421507000d61103d20142000c184590942405002048110b803204903590f0084a400e1500c10001c00c14298443c50f0703e034000003d040020ba4078519211042c3c0540329184000e49142282110300034403030708a030004443c400c00e6030b0170390742440c580000480c00da0355240070390038459208000410305074003101922400700740000d0481c1e011508070307485948040001c0b1040441504a00b00401c0109002c40c0f80f10780c000740c0c08413081601c5c075005501426a2041d4071046a0425510312400c000e24004c114600c00303401a5400c99480d0a0089806940c540c801d0140314014000c0801c0c65543c0300d00c156451059a915072107556603c075090300940c2d060fa6600f08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 759342661 1250 759341411 759341413
    0x30f150906130e070f1d0f04030e0d0203010903020d081e180c0a08010902040501060c080d0f06051c02030d020a0b071101020f040b090108060a182408061f0b041403 72
    0xa50600c03c0642004643c0c002c00252024010701c6180c0400c0c013040310b2400c004540744100000401540d0500d00c0d403207590042d03050405a09010708a00032030b185241e4004029059031070405004107054001481288a000c156240180c6548003034090040400c1d0740c82513804000030302c01084d980069203a80d103050181740021540703030078101000528985020741c0000510395544415006509150046030301400c040e041c000000e462683d15a846480740c0030020502950341c07104500100050b800c0381c2c0051000811404820a0a101c1d1060760398038044100e12a112382e03071030490190b00105504500680141d07110340303542d8900c2002e0300e40050301311030484c0b0f40d5400c206280f106905580134101a00d280401c564880d14808005003d000e4042c0c11030f803203101014001c00c003c4015503440d050b450303c0b085011508005002c01c51a8103028100ca0860440041e03a02045500e0000390551048407510400c00640c40084c00e8104a115103000b0000d810794200020700000302c40d41da841c50590f01c050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 759343911 1250 759342661 759342671
    0x303030b06091017250c140303010f09050a060b2a0703030503090c010c0519080d06090b27040b0408070b040c080f0c03070e13050d05030f15090613 65
    0x3a0550003402800b1000c500813240100324013240d0740400b6888250f00900c0c40071500c003050b81540d811840000c4000304800800c200e0100405414152110381d140c00441c0c1e12941c51f801e0f041440030482c001c0b000041e28200000d400152140100400ca031000400145001d40c04001c100f10011500b82400003055200458403099004000c0c580042d406591129120b05003003002038103040e43c2c541642d04102421528901040d800301d24010b580e404131040c207800ca041c0b40f901d440d490240c115840e01c07035071810300001500c0c40e0070b4211030351806c4100d032074030600a02c10300b0210401c0d0324501c484110060200c001000a0542c00159070094090038150f81042ca5540d1013552442080b0b404980038042c18008000d1160100810507409015001602c003038903c00000c0380d034811151180c0342c031240c3d070640410003000078850a001910f8001060310b4a1504038003003c0c285510a40d60080d48410460000b0f0052030015800700102400500d42c0c0003507180c00381003000654818000188041d611303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 759345161 1250 759343911 759343927
    0x1c050c070f060b01110d0f030c020c0603090f06010803040303051c0b040c020d02070609081005060d05250504050c03070c0215040e0402030d020609070b07080f0406080f16090303030b06 81
    0x6060701144520a08011440451500c001007403000601005d02407030f4440c82c100c03180e00f038001c110382050001c07034500062800c02e0150124a0b29440791506a003000c400000e100c1b800360f0206100740d407045190102d404503641c8102040c2e1302c0c495848094001901404140c641c520001d50306e005a50908001044c3c4641c0040000c1c1210455034049015030300603e840b8018039014404400100424103003134013094500030040e6102e45441c207140440c1561140000c005d80e44010740d4910090f080011280880c140e4144454504040e0001041d482d1802100050b40d20b42802610f10400d51400c51a045841c0c14100343d070076142050080303034030014450044200a038181c0c003510080c4a020014089410310740141824441803c00f000215048281040300216000810f1030448460105050341c81e21203080c4041c4a01440844280d142400600020515130000c405030182040803c00480d0342c54140c01c410f0400030315680c410110301100800c2003c81d000341e020440101e006020140b502c1341c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 759346411 1250 759345161 759345173
    0x90d0507110604030c240801080c010e120a03091d01151b0213020904060801270f0203010f020c01050a0b03060a0209131121010f0506030705070507060908010e031c050c07 75
    0x869041440109409030440381102a01c68400b1b0301400c80d41031000f025414002d203161100c8642c0003040c103000284a00310f00d151035402240003201000816540504411310b0010802d0340c0522410300e4098844d4100c411042902c000207040b241c45091043c0ea80c0004071058030028002c00d0b407a070410f0381c554070000240e201c0100080700070441500c0140e5a0b01100204070031207520360043c41103a0314002d400340c41014540d00040c0703541464103540a00320310500d081c0e079540c0341942d0000d4165083c2001c1d0803080004e500035124040002000f40850341e03e0300b0894045803040440543c0c190701c840e010500044031a4010210210060010107840016840300002d0341c11440d0080b40c2d20100180100040075900c0400d40401c0000302c5101e03065241070300406c0321820750b00613288101400030100e0700050280084454042d80034040d24102540c6840c007070b142d00d91b1407040078001c1d401c01c0e03c584006440441100d0b440d1401c1d0b14071445126026090304020000184021048082000180c000c035071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 759347661 1250 759346411 759346433
    0x20d0c0312060b04082503060b0a09020c0a030e0306070c06050a0b0604030807051204030c05040b040e0a231f0e0718051f030f020d02040b04091a090d050711060403 72
    0x9980341e00aa41d5480d02c40221b02e01240310400c40c0c140880880d6146030005907105020407a9000640461441d401e40c0010b048142d483d07004030f0701c4038400507507240f041c000482c1c4082494000d80300c074000342d201e4800341a03c950044551780c00003100901c01c140000d980d60700140e04107040001c0098805143c4001c14995071107030f0020790f03e0030400304030b644c01c1100410040c0050010048542e0602d0300d0356491050400c81805114821515000105c005440747d90104610640d10b9086030708101060400c6d8400d1201019180c1c9c0210541c22665081140000d1004084a0ba09196a00d02d81050340c100014118159134501c240038252000603280c00442c0700102c1c80701c4036180003c0034248440314140a0308803040480e850041c1ca0401c001040a0b6145101c0040e01524600900e039160700c0003e00410f40c410459a0043c81c3ca503081041c40005101c5180b50b1200908107040c0c0d07100c0c40c035038569420480e410100040e004102540c0060f0b240c03600341080da003010785101e041c11341701c6e5074806c8881 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 759348911 1250 759347661 759347669
    0xc0a0803030103062a030506042a031a03030403020415080609030c0106092d0f020a0e1815060f0f0f09031006050a06030e0c06030403080403020d0807020d0c031206 72
    0x984007100620038481ca5102d4002c45095120041320160b04d5020031840300d241c0d04030940149a510000100280c941350003c1d24248402c4c500410402242d0118144201c0c5400260380000d24103800e03180901d102e0b180f003205549004008605142c607590802014100d001c60340954090480300c00144060100303c0140500d200002840d1070b018510142030843c0c145520a041040c02c0c400c108010600c120b181c920341503031021180452425144c040c40141505404c0c03501d4407840001d60814683e07020b00c02104802040f0340a1503650300380b003d1030044134400c8e070380800b4100c002d00520072030341f030000c0061440c40c181310000360074100100081c1103507402c0103c00500c3c441000036030038014a014003d070ba03031514145c44104455814400803030005262400f4140c103140e0f80b00301004000b0303010000c1e080d80c0040140201d5892400345801000380d00251021009440b5440380200c0d0700b07010b2080d042c0f18052650090a042d40070781da04030f6061404510036018402d15400603d20940c0324046e0502030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 759350161 1250 759348911 759348913
    0xa02130212070f0f032a020318040b030606010302030414070e0f13110603070504030204020403060c03060b030f130c210b100b0d020d0212040b04050d0906021009050c0a08 75
    0x4214410301442034410042c1000108480300214000194201800845001c070901e00005c82041c040140c10300260f200c0820044c101004400341c140702c0e400002860702c101c0c01d40785402c501c0000014801518105402c451b4950007410002c2c0302035200364099680180151a050380164540995070305201040d04114078501c1035008209000141c00d140c11380141503000c04940c0d600f50b507222460300501008582d031003103000001240003188240151005503030002c004541e03a6581c2e10b4a040105500405100801e0611400140e071002e1001580d1282c5c03445849000c4543e22154500e090300d010542c120303558002d0250221b0412030001c5000d404014002210180d0311450600906401c40181020180041a0010311200e5410001c8d0f4001c016000009038803058020b94900c0a03010341a035030014614210100011f224080c03585a01aa003d502561825411501d0450300000c4c640211304c0541d0100320700f808080d02c250b002000320b034018020750f60110510070002e5080c8a4a912405d00c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 759351411 1250 759350161 759350167
    0xc1709070302090105010f0c1106041505040906080307080f030a1d010506010806030d0f111507122003040201080a09320a03080601112b08070306031509050a021302 72
    0x11810814500fa01500007403c02e00d250700a9143c0040c070311840c3c001700030302003240345840101d00c0e01d0745401e680250400c0070958404281c504001012a0824071602520030304181c00016074a401004954070980c00c030782010310740851000305134000d900207406d1074030f0564ac907030080d41c4240e004002a54101615400401c003400c0c6040010042d0f840035066034441d0300120b07000341080342c02080029000c800d500b091480341b8800319030300d8244412030006259030402c050410074050340c06400a903040d1040501000044a108050714900002c500d2820f0201000c2010902544c000c080c21a40072816480201c0c050318035580e4111104035121880070303800001c801b42c4520003070f0807020401c0c00f451071004103203640340380d1401403855a021f045903040c42654541303d0303c000c2c800e200c04204c4019040c030048164074440e50500e1454041c040c03580001d5011408500703454403d0080d00110707600440c008070718030385250b41d01c0300030b240c000001c44191040b2005100141c0340d2030684144d1005031080162 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 759352517 1106 759351411 759351413
    0x60c05011803020a05070b030408030712240501110a0c1403030d14010f0b03242b06060e09150601110f010e100b010c060c17090703 58
    0xe520340141c49050507000103580720101e201e001220340d00c598451040200d030101341e4000b401c4800130008112064401d003001300c041d92102000052078400180c034410088110a4100c0c0300c0d0400102c01c0045682107580c146c3d0f00c1400102078858540d00d80d03601c1542524502030705d068a44030281038252502d041050303aa1070b660340101001003115000c103020b07004809100d4050074052880c07012414040e17043c00c2d28001c41030700503900f503440b03200031081c3e0031212481c070880d803c0b41e402d0000711021054880d0b5400d144008a2010201d1401d505064081e982e88bd040264598a08000d00c00c01160014691440340500024a06503468038030040355107014021003242c05203d810607280d4404010752000e4010303124541213820100c411294001a290101a41404292060031000201e0b600350400b0241c1c2c40c40c0d141000c004d000d850081120002c058940c0070742c50b4002d0000740 = true := by decide +kernel

theorem cover : BRFrame.Cov 759172661 759352517 := by
  have h0 := BRFrame.cov_init 759172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 759172661 ≤ n) (h2 : n < 759352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
