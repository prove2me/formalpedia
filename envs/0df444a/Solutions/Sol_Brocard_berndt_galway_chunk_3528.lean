-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3528
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:55:00.810566+00:00
-- url     : https://prove2.me/submissions/4e60cc9c-f57c-4f0b-a558-719704ab1022

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 634352517 ≤ n < 634532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 634353767 1250 634352517 634352539
    0x1603150306020d060f1401050415050c0d0206011d15150705010c18090c0c2009011715101203120203090115080c0307053c0a090e0309041109 62
    0x400c0358000c3c0c050303510348001c0c09403551307481c040d0100100ea4909001d00288e020f0204000d028051845060100b0341c6003086424903c0740c8080350716184220550340c3c0164803010041098007207a00c510350b00071001c1d0010442034501443c0c1d1a0705420300f0302006000f407191002d01e94502e548078085c2c40c1440d6002e4020300900101a43c02070504030a2188056040404440020303013071103502c40c8100e0351509458140e0144981c1d00c56850340700d41e00a102c031038a041d860000f115540e51040c0580640f407180c0b101510300d240b00013500c0c60109980c1c140b00d0001424401e00041d0b0a02e0305100e003c54a076003204120035866450100c8500805544041d111070001c418080b131844103410500e00415090601b80034280d4840c0429650500c4032140354154100c51414400c40c2000402c5d4414030005859218042c0d18184030b1465034200c22624103544030300e80101d4502890080d41120040442c3c04050001010b100400d41e201c2c480ca0003c680310340c2e5240006440550311100303842c129280149031010003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 634355017 1250 634353767 634353787
    0x8090d051906060509070c031202040b0d0e010621120210024306020318060709030302060606042709020a060306080c06030c040510050d05180c09160315030602 70
    0x10718015011240b46040c00070101d113504060b4030044c414441540c544204100136107080c0d6007403500510310305200c2d4007044080f80014078a00241140f400b0350000140c00440403400a00b101c900f5049109855090042949006e46134103400420035007140480f084000100c0041c0d1401810f207403c0b000305400815403030944a0021909881c000300e40c4a05420780f134485540f50b6401c0314040c2190710070072101080001098655001e507610803864448134800c2e1050490403443c09200b203d007000040c2a00809108140d4180107164010320300383c074440c0c2810308001d0040d0040c1410001503900501210100c0c03007190090704186ca40c02d801400c910882ca4445d10000c0140c1307807500466040c2d200f6000300000a040c8541201d00c11040003110700d00301404d040400c14017000003c000810454140400780303605417240319440c0030b207881d03003a0300da01060415010b42c0ae05000002e45442034607202d0410030500f0446070100c0605441e031400041d41900318500005611640d04090405440030034030621b8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 634356267 1250 634355017 634355053
    0x903070308031911031b071a100e2403160807150903020609042f07030932060f030406060e130f0b042301090b0702071208090d05 57
    0x11012040c2c9424541c01483c106002d5819183c0c1d280c0b1012020000120022040022052092000400640b4104481d260b840d0741c14220460010141d620030180301c4e203224480d4051008002031829a6414504080b501c84c0d02e90104111039000c8100c0082c40240c0d070b4042c003130b00d40c0d540d00420702c0c603481d9031310780100310b076241060701420f58a2070941c1e0340344042d03074000c0030094216940100840d29202d12030040c400980090703e001c01c0c900c00c0341030f01240b10b4980b548040c1c962803c5100c48079204c03202d0341002009411590b01050745207001c071800200742d00040995811503010360892101050400010070303400d10503090041c0d01c1050102c1172104000c941d82140003101c0d82044400c0d8182c0320000410620711240c40010201030002e40450b0000e038410703110b01c2e4000d00501d081c0c1d0300591030f4028041140da0503117801440b65500e11101e01044100d24204d0340000b0380b0710040562a0074525150518440030308068010000804c118000d980c1d030341650a07010ba400016510342120000310448 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 634357517 1250 634356267 634356271
    0x12060403170a0b0f2e02011a0f0918120a0801050916080115181215152303480d0f120203120a05070212030c090307030803 54
    0x2520241c0000c50400c0000e8012500c080d0802021003c01d0300f00541002546aa00501210b03041980b1200c4030034840100001d2031303d0b03c2c4030b0300081902d11703071004074403038420140c20024810403002d890b06c4140e0b1150480340b0707881224000d900d0305030f11500180c0c901e0301c0c81e038440140b044100010b4150401c2d034000d1655040b140180d40c401c40549075440a24442d0080c03100c0c840018151800410005443c0303040e0b055203c00c5400d00075110640314821003901d00c26a00501c81c07000b80441102e0400c13000000070224107029290400c011078074604203601d020038034402c2c0004203c18071005095610320000c0c1111341a8001c04403154030005500f4020140a0080d024044480421460b03142d04000d0800b094800a030714801e0300c0091101003044422159010b007918440050840e01c4009420f4a89200680308680c000311307218815008213115480004003004452801c0c01c00348100700782c0024402c00088035185600307450740e80b900588041405a1407041e40c0c50703c140000003042c4520030740254 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 634358767 1250 634357517 634357547
    0xc03080a0c2102031c32090c0312091825080c192007080106050109050d03030513120806121c12060b0d0506030120040506030612060403 60
    0x1e6402c8040314903451081c40c824110001d40c00400540a5454401080005002501030b0000321008400140c405c00c0c41d000000c00c03281c038400f46643d40c2c100c2c013405e0003a0b480f03c0d1101c01099801d00329808030740c071040c5d2415648074400c00407030300d090260b0307400d580d1651030000358400341c8c1c503071400d8810f041c114000e944900813240000512403940305e1059070701c94494942456000d1600541d411410100795400c1d545100b0488180300c403405081189402c0c201c94620013005040640c10400c40c9821500154003903410b10038403103000c0201d902c942580da0203040e09030400054a40d01c05100301840780091100916607150b0842190034942c0000f440c9015480541e02885089036020106996400744002148000c1c020b080d0704004030720425442c0043c3c844201c01059069a407001800c1d10b030401d0b0b10000501e034840041115500b402d00c9032401c04a500004211140c00f140411100c2d071145003d0b41d4003400700040010f01548500280d4202103120030308541042c5000e040040c0b803028030200076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 634360017 1250 634358767 634358783
    0x9270e030d11030103260c03120106020d0c020102061b07050d020304140405060303091e03010e01140a050115120b1804030908030306060d0e0106090e3003070c0c03080a0c 75
    0xa0b4500c0060740c040d641030b01c0e13010140d100a801c0f1503107801c8042c07910581c0c21900d0807041000c0c0d8294001400584840381401c061a40306506105c80a8105016400346004202400c206100540c2e40081c1d0307960032111400c1000c421a0f010b030000b0206100389140070f480340c4502500000e2880d4004010001c40c1c0a52607100d40c003042c0202004103507002982c019901d03a200344040a02483c0c510580c0b680d0048008a44100a0b110800f19007516a500814540c80e5510340c5c0c880322558001d1009644040c25800c00c120075810000c141c50399a55044e00d0200704100c542d000d055240156000444140c4001d00c40300d40742e010000800500281100c048000803c0071400080f203c030000305990181100915580c280b81d40031002800510040290f042950340783c0800280c0c030821441001c00d00000c10000c0c04542c4544112402c0c000c05080300e6003404121340c00c080c0c6044a4020039a50049110710308490b5201440c18841d08006043d04041c1c03034450000713a20040c1d960407140b03250383c2030705c41c12503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 634361267 1250 634360017 634360031
    0x6030b0108070c030305150405010b04080c06070308010e040503070c180b040c080114150309010504030f0c02010207050105030c0d050c25020f010503040804170309011d0109270e030d 80
    0x44078003040503540c250200c2d000c68060340000380203411481c1e0202d80140c04c10b408280003400a010340f0000e9000d08100c61000805200401c400e1000c140000415034a50b80350810a50380100982e03030510405d40559169000b0500304201401141d0ba01504114846445a1901003c104000052428450b45032801c031505003682441c1c003480c4888a842d03118162079a180ca444241c404605060035603006442c018012408040d4401860042c291240001418a03161030060840910302c03e0000520682e9004040180e900080c480c1c01e4070400c1c641592280c96030401445a401070014034480181040304020045581c0310252a0203181044c16040c0c481d40700364410a0100d12440180d00440f0b20902c00703006c0e500500081d5001403040003d179180c640d45825408000d0b5200c40b049010383c0000070b00419541e840030510b031880f503078207850941d40c03210a4000f0380030240c01c1c441c8030b03820800c06101400440b91761450044d0203128400500030a031010041d0760702c0c1e9000e0403030910001e00e4510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 634362517 1250 634361267 634361269
    0x117041b081f02090d050a060c031103190f0b030a03020a050607170f1b04090203100504230603011d06010807140a09020717070807050c06031314070503150106030b 72
    0xd5190240403011032014030700ca22810b844020b540248892a001251003041000040c1c040089147d0307107001d01d00008040d01c06030b1005040d501d4201c040d8001d2101031003441b9481a108440a103244404271002481c12541210303038015000e1222425418007865003520241900840d00d040400c7c80703003055952580c1c41000c1507034581c0d03814094945601160000404052400340445e40140395040014a0307454038211a0a0300d500540212030304503004014442188480d50b60813029000c1107c0610100715542c030784506410050240d040c4510301200420090b45083d81b24507540369103804442c883c03241c9900001d40d2a0800c0c0310b68555842287d80004424107600032321854040020a401000392030804528080e4014940607508901c5184140421a00e07203002004035601c140841070f2600e0040c00c0450510f45d00f240500d000780010010056160b0f91031541c00d03480d9500000441c80700e000440c4403880d040042d00404e4151207143c09a890030b0f41040c014504031045a0350912154003c0f030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 634363767 1250 634362517 634362523
    0x10f061e08011503110a0b031e06010f0c060506040905011a180403091a04081f0b01031e021606053121020c0a063204050f0117041b08 59
    0xc1d6484080f508840042c000a42a03c45585424034000c124060041d211544102190310a580245001407000c1108540429000000340d00030000d013081c00c00a82d5029010300310000c2100f000702481d6407480080c090351740310b078802601e447c2c02c400200310943c0300f00403645801d80d04003869481589884d00a8018228500515114a6142e51004000c52a003031142c2404041e41c8448c0f03d50b48414040490210002c01005c4070700350002c10006803034112241c46074121422482c01d2410141040c0891540340017460410340055900340006a44100410b8031242420b0700c5040217004500306418000000e40791000600b155503403006038403a4110030f500b085818010010024002c0c2c102c105c1104408000e0591102c4500b407600540c1c031441c030800c0010303040b00c1c0746230401c1c40494901083c038003101081400d8501c60101c0c3d48a00402d40303642c00000100e44c0103510619214071200d444910542c0d22984207980c141c08048465140e40c00c0ca80f80400002c03413005402d0b46400443c3c04001543d01c000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 634365017 1250 634363767 634363781
    0xc300311010f061d0702030c010906050f0606070c1e0807081b180604020f070b0403080415020414040b030a05030313020906040b100806030c03070603140604020307051209010f061e0801 81
    0xc0134201c0002080d00c480201e100205008103500050000031910134080c0100d600d0b440c41031078000b6441ca04444010444140034040f58022030060100d000056904550007043e15442c44c0740c100d03035042607210109000026006a0b02a000f9003100280650bc0024000711051081c3e022030485a00b500c24001403c0c0c40b001441105000c001c04142c43d41807590085c650043d104c0d0070039152100a03100c080c200401560214002840c1a0811041c0008a10030b00585802d03440c1c194903203454a00883d10b52102139030264410b80c2d591000d03e0a0360340400120002035070040542e5181c0c40c01082c0704c00761440c1024168001c45400c000606c4500d028842d0102c91303000140b0b29000d00301d080c038007101d8681009101c50f4262280800e5415035a6040104e080103102c20b41e404525081c190043c0d658002c03024140a02950050090015141d048016184554901810400c02c0d50b200340c0b0040c0500480701040d030750503261450104004420303904504440b05101250441d155503950020b00302c1d035407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 634366267 1250 634365017 634365029
    0x230415051918180b1504091202010b060405150904020c0607050d0c03020f0706231603060e0c19051306090510080114060a0201060504140105010801080303040c300311010f06 76
    0x43c0c0104030001800b61110f040d040203d9a80280c05106400d02040840c0c401c020250740540c1003244038400300764240205090303000150340c1d042c245481c010100b9022415860240d19182002c50001090744960b41500e08440301e4408484a6082454010f405a803081010560035804c0207401942c1c98007a0003103441c55040c4203003561509d035031511084000e10000680140c000b4039003c1009040b855821807031701408040c804180c00084030007018080715000d070f101880101e0300e40100170248074440300b41c400b031500c0e040c803050340003128050441d00c0d44074510041411000090780451880d44c803800c488180c1c1c1e01034550b03424001c1400030540f0707040c000344500400031407144038200c40313030400001130103540d0020700001c80d00c1900e03400090b050711800d2400c440c0c010105001001030750707802312009004080e9000a180765050a80307843c1220681030140d4a110700c240001c8084805910710b02030705900182d01690340e4070215280c014012a0980c4064244d5800e00c1d84100e0580304a1040030200d0f10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 634367517 1250 634366267 634366301
    0x120203070b070b0a0905010e0d03020301052b03080403090e04050607080c1615090512091c0302060c181c0605330402071b0e01230415051918 62
    0x4d01d82031048081c00400c141112603540b210300520403c0c0003040404402d40c419180540c407581800b05205143c502d01890922048000c3c407050005140c440400f85e1454140c42d19000c01c0d661418142c81d413180c41c1e84801103107a9004100810700c0b2000c01c589004440c540e0f0356410380c1e255681c1007a070500030320703c88001c0242c0e00000100001d203514042039280076442000700340390303007541ca40038200350510080c0e1420b0100002c070120f09140038202c0c10408018203d280c044071195480081d92034000504020b0140310000f07107100c1c1c03240344038901065190700802d1814682401c48400c02a070000020880c0d02c1806c0001080404a8484d4031032800f410964040c220441811440785c229002c072018142c110360300304614004180004c0c0b90709003230703420701d08400c407c946007a00802841c04142d004c3c0d105020200e03003004100b00e000c000310f9000c0b40100c40115aa801c1859030b000503003069480aa881a1601502600c2610055421046443c0c0440d0041803a0190f00d5000076154100000b0310140703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 634368767 1250 634367517 634367521
    0x3040e010503191e170408100609140c0d021c0f0e0708150c0d060b07050d140306040e1c030b120a02220915020319091509020f0406120203070b070b 65
    0x128501c04c0e84010718010601c4080001800c98120745941c0550000c988980082d403000c410300e803c0780212001405643c074200f14055240050200909005d403800c40301140005444c040400e8a030155000600000f100346010100006500010544007103440145800c0c024004c40130517021850504907503282002e444030302c0d04442880103030742000f0701943c030380e550501a1003041e10452160074081d01e41d14118079a1a052070a00914000c4203880b08410015040343c0e1010f281803600980340c004400340c50204224003094900c82c00e01c1e094051843d01c15440a00f542c1015506800c254800001960300c3c100805450350002c0d140d01d00c1d10400381d04929007041c0360f40b000544000b2520a119502c030002074040b180d82da04951103009101c4074003901e401006216a14011030a0b4692002a03944201f01b48406503a40301d201c950700c03000325540180e480c2c04e0007095445803803910500c6034005004000150302e881b44094124403140013a07000344103054010920904603000c581c4202d400801410840d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 634370017 1250 634368767 634368803
    0x4080901030e0703231612030f021915110306060a08060a080708070e1503100c030b0607050d140a0c120c02030604150c0f0903080a090803040e01050319 67
    0x40c05030060ba0b07024511403210008003080100007503011550840320110540c00b55802254948070b000e021180395503880307450402808103000f00e00c03940c0303c1e0303d824200300302d0542c80c138140c0c10b000085c04400980700c45440c2c42c00c00c104000d50903049840c0540c03030801982490314900061404101c0c0c907990049000c1202c00c0d000d034000e40b0710642c4408024080720500d0380f5190b1407820403020380d004e40140e07480200203004900b030404501d42e03c20a04440c2408004107400002c0d95988212009640395544019011050f4071a4000d220075210140100c1c1d034502052070200d50710075180c1c51a2000032820b440c126045940c07281140c0d00046a540d640c800103441d40c03144200c80501040032421b0200c030720307681401a00c050050790302c00c1f8020825196465003007440c00b0191450301d032100b4100920b203004074246940001802058903001101141c580900210a50f402601c540048800d840301180c00241110000e10700b9068980540035180b0b19008084001e03294402000c000700a45c055150076008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 634371267 1250 634370017 634370021
    0x1406030c16170306040b0d05061303091a0d1a150a031b0302030403030509070602031e07020316030c05010306030c0918080c0a0b0f010b091e03031207030506090408090103 75
    0x140e0308401e500780824551540c0d8402d420b1103282d0340118182e0340441005014038291040642a290a45141c428070100d5521152680740007485000514480d1402400b494400c91001c00900311002c00c0001603070644050760401e8228004e801d40003401c2c02c1c0105000200700c1466507040102824070300441c00051402c0c204c40c3c1043c02c1103070405a403a1003480040d110083c6207000d0b807070180c80050340d03420241002400d442c4000d04d06c02959104031010403090381d0001c1103584201e0a42e98a240003080784980340c50604c100340000e03600d841642c00c007404144000c030102040b43d100303404021398156070b04015000d8541c0c4c1d02c0301505035803650504000a140e650489251000e21084401c41c02d05241e4030404103421020b11456640e0140c4042420030040c07007001d9400110720030020210b503140084c03402d100e102d013030100f5015004030309220442a4004109880d00b440003000c2d6600d585205030916481602100c405000030b040502082c0c0500b0641c02c1c0ca401950080c03070842c5000503050040d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 634372517 1250 634371267 634371277
    0x3070b090102030703210501030305030105100c020f0f120304080d11161205030912062a07061d011a280e270a02090907240507060509161406030c 64
    0x340f58411b01040da49414851081c06e01840c425102d540d10b03541000144003101e03001c0c868410038000083e400201595801c1d000020480c81180c034503841402041c0420062940c441800040d880301150100d20b100d000714000c9400e00c801d80e41c00a148194000742503076010003035070b00500d11020300803c0c0803c146000440340440e000d50100c0c1d1404d9100310120f5070803144260020055008a01800b840781e5111000700c803880c05462001e502c521fa8139912076214480c807407000b003401d550340345e0752840f01015030140007460003550000c1021080c8000d02140310003504061900c01c035404c80c1842000091003824044c20082c02400100c490305010491041000c060030702121a6003121511072802e64445910045c079441e04060030420145106010038000c2c003030580851030300007035402d106110070701003e610250170029004840400b1401c0030f580038030130030704003401c02418001000300003100011075038041003443d5600c4450507510480710926100340318900e6446042000403d95074080840a05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 634373767 1250 634372517 634372547
    0xc0801210309050613030b06040204050f0409030207030512180114030f0601090503010c03020c07060e03060a02030402040f02070318240c140d080f010905100512250503070b090102030703 82
    0x214026222070020b6138030380240701e400d00c240a151409104121030300d1190350b04048203840541c145424000007910380a403407070140c2d00a6a40300d64403400d052003000000b00458201060350100010307050b0240d2140c0c070225005241450840389002207520807180a0000404510103504645490040319000031010b01054108512018080341c1990300b0710502142c0b1071075840c0140d8403035442119904185460f4007000500100b007906200b00e0300c02284559010107001c80069a80d95a03200180060007208441c1906074800b1402c001019000f450000140424035804281140c0c0ca1040c181c00e00c00014240305040040340030354058600484200c114188a2141e41c1200401d4800e22843c2541d5090071000140000c024000005061012603025100180c0e05015914101c0c43d0303034034010000c3c40744a029200565079111007450506c04d007007020011300b1520280400e60207448107603c525004607442030180090002d000c40204046030802e00040e00a141403a05540b401c1c4c50150038040c6003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 634375017 1250 634373767 634373777
    0x30b0406080313300f0c03060f0203010e33010210020d1d011119030f090302100e070f0e060a0f1203090b030411090a09080309100c08012103 62
    0x3040212040c0003030184194002c44000b0a03034a003445486808190401d00703000107804031150136405201c3c10702e034440a40c101d0703035100310010300e4681480135582691015100c21303c2c291041460321410f030002c504803403032507110b01040d881c0e02e003200398202e2900110ba03c1c0c2101d00b020b000d01d01241243e02c0e0101d000c050040e98107401807408100280c1e0b01c007100041c401c076642d00e161908400c0d8004d4280c008102c98008000905100060380d11912440642d141c03c807050081450285200ba00041c4203045040c100340700010b55445c000c0d5903040600929401603040c4807850400003400503034034088900e80d802d21001a1300d0f010368a0308030744000e0700e013a4001d0001900450720040700d24031100104080740f00500841c0c3d507400c0007010074440d84c00c1074101d40700410502c008a11300c07042c0102c0c121403c59291002d42c4408100c94000e01889e8802031840034080108640c600307001c211031000a02c501000d000740c4c07004134000c03a0340190034080e1f00143c01c3e0713507845014101000302c4200b07a0035205e4245 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 634376267 1250 634375017 634375019
    0x601050702030102162a06121e090201030b0d020a1206090b0403020601030b0604020a0807030510051504050909070305031e0702041107170a02030a05070816030504031103150601030b0406 82
    0x2ca42a680203078480045405404640d03010809101b001c01c0740c0385d00c00408200d0701c446a460280c0c090880d481a0020000c50380f0311142900d50580c80300b207400003074409541c1c0d11036121000c007010701a21001640803e20380300c1d030101c0a0a0000da006c21495000341010352103420160325503e0200785d00c1042d030b60583d03104c58501c00580100c24040c080e034080d4000305810f40c55403601c580c2d0080f004146502481c014490700010980110300150001201d041c01316056a5030005644e80301c4566014907404050002c0144040344800018010340d00242c071071582e50354403100420b03583e004522000b01181d0003000f0005008441d48072814096100c3c44a240ca84500e540000f0107a0300003400310765080c140007445a0401c483c4501049101614030704641c00c0c82040c00c0069204d010387c01d071090034440002899010880c480080303400242d030079042010310006c281402400394020b4003040340c240440b865681c41e68034000944c004101203449203000c0c01e039641c41c01103000e807601143c495001910360030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 634377517 1250 634376267 634376269
    0xf080403080309190b0a09051f0605010305090c09071b02060301060f020f010b1c0302030d0e0106031e0203060703021c0501090c020d2610120303092d02090601050702 73
    0x100019406030392500d40b60300b03102c820103090030500404030318040041c1d040385000810788811141e0103100b60718000b40010380d600b0a9400e007404068540b0802407120307141b00d0b84045035030000040d14001e03078040140d6030310f040d0074681d14240180d07450351059402d0006104140304030714080e4031024500e45d40c003088485e9404103031a50000e03001900400d03185100d0f1084a41d04001c0000007503100002400000080c5022609140400854030345180030300c1500828507000700120b03602c000d000e0307108001003100c83c03014500800c00781c041210010703d402205012010709480e01c5010316002000344c00c650320751a0041e0002d40c41880c0c0c09070010702d00c50350041c04000c0d502c07076503000348800b1401003204e002080d07009003002c400d5903810003406095280c207462030401c0f0007203d854001c1e8101d95400e0361600f1903404051400b9038001100d044030304041c0e80406a242d00480c240a115050000d441465a4040300140d050b17842030140000c61210075101600e8800021600100103050843c07424550f60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 634378767 1250 634377517 634377533
    0xb01081311030a0611310308030c160c03020907080c09041e09030c020405060a060203030115091724010501020c010f1b030305060f041808070341040b12040f 69
    0x80009400c64001142c1c140301c3c0c0c0c610b0710008215007a4080e101040990405904c108180745000280000c44c0c04400169041c403802c1c106c07145001c030707158510684008cc0c640000b0106550200700d0181c5294404240f02d60f02941010b0b0050002d41055030600c03410030144001004599038207004001d031440103882d00e0800c0e1040004940c02540c901461a03024014441900d07070103005035000d40c640d1107007001103a40c080103030303030540300c4600b000202840104811180b90055400c503205403c41c8a052481001c40000c01c1d5514010810b03d44420b210024181e060210091103050301681040001d000d0030342c410600d804070202c00d403e01100302051800b28007040c901c1503c0c101c001c207035a40c0c207000c2c1914100d00d640b0001c00c07080b0303020321000034a20011002007200510040281e10301054403000c02d03018403010910205090000c0d0010b10359510720821a41c010741301e00720184400d141380d1a1a007017940450701540d10314500540307450540b218005004070014429201000d400c004217002545038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 634380017 1250 634378767 634378781
    0x9091605090901092f090906040e01060e04050606012609120d150b0403020d0b0a0906180201080630160803090928110702041e0b01081311030a06 64
    0x10743c07000540052000783c0c1420340350200b8010002c5030005c100d600c0c044140c0c2c0341100c03034042098a0700d51b801d0b120303880420041c182c005032400e071550804078082180b0420811192045015508440481c5c958000543d500300e140c40c2c5084200c641219803150448171900b542e40c00c40780181c11a000c5d20b0082030740c1d0403607820203801220480c0c1c03500401a074040d1000050b4000d0401000c29074036041c6035030b0000700d041e00c4001c0014003c41b0100700140a40001d544400e01003034000d881400b07001448d400040c0704c00c0c03c00d10708a020814880c0815030f00d0078590002d880985100036290104c008000e951503540d0101440c1c1c895600c01e520901c880d8040800404000f0031080b00150380b9200340f44204070209600600c40d09003c001200c3c1c982280c0440034884446000a2000140d85800c100720700105d0702c51810080c0d042428407601f0322202e4000300e4181d03821450500208503901d40e250045482c03071821f80c1d006c07915042484c8918003003a82e8011003001924001c1c1100d071a022259140b500750303640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 634381267 1250 634380017 634380029
    0x60903030c09060201020c060f090f0319120e1e0a05010905031e030708010605090109080105270a03050909060d0b0c0c070e090d11030d0603050102180609091605090901 74
    0xc1d0784a00707241c01d801081100240c00ea40c002541440e0b000d11500e80d0f80c02000702400099040c4902080c69518103005022a0b40034100580356109001c0b5041510803180349034400000f080070380714080c40e0203070344034510000305000082c01c0020049140191103030040f81001925000c3d9541c4800018824411050a81d00c1038001e580c6400d405804c0171520702600848241b4440f00700104102d80d60320240a0b41540c8450804a4803000c1100c01221815410307013045540b03628040512404002c4010b94026080f005d00482c04185058104940ca400c00171200501181060140f0655840c0411100d584020301034a0941500c0e810b0301c5050b10401c080e1400e1600300b0002801c18002d210074030107400602489400c01d1060b04014030440d0340c5000c60380d107902c00c104c0803d003c2400a041031040340c0d000f45022105001154a07810810b00070340c48151030004080c0305c0c084030341d141d04052003580c120070303030003480845255128458000e50070000b06048007001801c014501103562503400e00c0d03020f810b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 634382517 1250 634381267 634381271
    0x17010608151003080c10020a030f0b01020d0c02040b060c0316110d02060a031d0f0115050a060804081804020a090518010b1903150803070201020601090b0603150d06090303 75
    0x40382200480c24186812940c0c2040c9000104010442d0158030365541100d6000d00b446070380342d02c4000b0344d50402e1083c541c050360300790000400f1482e0550640140d2204055041704200e14007181005982d00d0f210160401c0201c2d10030108003015160552102c0c1c15134130054100303450300c181c8801d0b00341184d00c50119400e01d041810300d50010f0220480f880401c80030147c03405103103401650006107490145900410415848841400da041800c511010b0a007103c50111001451200b911a001c0c045d480c51201170a0142c4000041c1481c0c14540802114400d88541d0780350f03207840e10303911240d41c003c0800403040d6486410000460319507100400101070340d907541c09003080c00c01e03041150401c0c8083c224007020b5071040060155001910441d4642c071315040c011359054406083c1900a0700d020309040c403201e2401000011086404002090814801d070300799406aa02c038880103007140d030f00300040d5411500900001d445101c0080c03800301c3c04070005103000b035420042c0e070b50f0350305a5070741708002c0b000a5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 634383767 1250 634382517 634382519
    0x1030c0f0807061b05011803020c040e060f0115021203130b0106051804020c1203160246150902090109110304060510030c030b10050103020f070b0709170106 69
    0x94080c0441000d44150030141841501c1c10400070084205003010705410500010610700b04003096014400b4500c41001d02c0c1200d405a040103074407617100c0360482c1c2c0141c0c200001aa95820042240c0384214040340440a861b420541d28441c20400541d00206501c070b46014041b268030b10074040c41c8500c00035400c40404480300c1c41d040c18420810781c001014090188421000540002e040c91820041a074006071507030001d51140d4a0107140c00401d8125100000c1801000000b0301c0c0d0502c410b00254089456600001201010f07440d00c1c140c40307035401c080c0801c0280da9901848051030000251b02418400032409854045c0d00350720482c1108040d66660591108508209020381c0c0180250b800c10480b02d84103098a05240c40020300042c64140c1e030790300007003000d6800041900590b400c00c401981c40c42e141d03d850481d24005840c150000b2004820000e0a981f0a00072a1140c0d096a84058100350680d91106003004014140704140700f194000495245ca46800003038650301801d002062217 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 634385017 1250 634383767 634383779
    0x31e05070b030601090f060234170f0a23010b100f0210050c0706050a020d0203040b07230a031505040e0706030617060f0705070f112d1e04020301030c 66
    0x481c0c4d0340000d880b40042c0c4000c1021f69004117210400a850601d2004d03290b51600440c80030011410064040140c84600410010345178024000e00c800290125003102894910725030390750180540c020914100811007540205000000400d0800510300100f10205003000081001c0b0030032400c0710019151082a55145da81041410b8040545400c01c101c01e040240030240c8510070f4070809043c458031040466021140c42d0704030303003a100445400315182d09282c81c0c0034005440030703500000025046420703040029070301c41901d07543c1c400d440c0c1c80500d402c0076180e06901a003594000f038074003c9621040007410381c03154018038150061100103004210b04140000c0c089400603044108d011b100f1680d10300b03402000003551504000040700e48507069507501c4040700c45200d0303a4070083c09100881001400c20500040e10508204100d80e88111038900d4004600350850743c1c8103c41a0010341c0c07140c1c044504001c98070000849160300d00d0441266030001283c00d0b6403007a401140c500f01410800c0040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 634386267 1250 634385017 634385027
    0xb040302060a0c0e06070c0e1e07020708100f0b0d050d1805130b2719050405100506010c0b090304050a050109030506010302150c0d03140703090c031e05070b030601 72
    0x2002014a000b0030046142c40700003005403449200f16401350b800019036a09000255100600900035924080d40f1850410707403009c800310844540202c8003c0070804101d8490022807440c00351403c02000f000c001d4071610501e00513054040084480c1592021900401e403684a1000c1565000b0750050429140300740380102004034400710381400c801c1c8158207110170ba03074500c1301c43c103100b00d240b4010440b82c01c0c01e00002d40703459114000d0400420003981c0d003926046400c5401c0c0c4a00d103000c000501b810302d041ca45909440301240c0003055a005050320042d40a4640d02158100f20189000c00302c090386541c0f0000322403001e541c070f80d54541c40171130704205502e030020104000e803600381f03410313101c085c0b841e62411380e19541800024411400a040f855040788144107441d04d00549408030741d001c18007120080e0080460090380c131207410381100003c00b003c1c081d000740c1031403503400b403d4104241c1c550380326484030002212890041581450802c0c001c50f4007000b9240c0604400e0780d40136aa4100380c07001420b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 634387517 1250 634386267 634386271
    0x50d030b09060301090f060c0e0603160e0913060c0306210b010605070c1a0717030906061203070803060f042c07031a0403030b09071809020f041a0409090b04030206 72
    0x3c4a42c2c104035940d000903034203000740d45100da4041030205401d102041e06841c00070440848942040002c070420070000030003030a459050845441e0055104407003070600000c42d404643c007109115032030203010000303003881d804002d004010740341c0003900c99158041d040c80d4501027540300a9540082c1c20382c2c428002000d114500404080c01c12600e04003403903a40d0b00070050584204078540340c1002d0b922190401d00412503c03d5540240b80b520307582c10381002d8181d01e80003a02d601a01d4450381c0300241d49820103d8600702c101440340c008600f00f0143d5034481e13080fa800201429040309040c6500070b11512540108480c1684182d46140021041103940120900d401141d0780c82c0c0e07020010410103e80ca00d8000500c80c0228880c0d079403181c0c0d43c0e0909901030402021190341095a0001b040001d41e480109049403180c1c0310b5040400c3c50b554190941070340600c2d240d0080700d500400c42008100d4a1609a941c51100c465a5505003607507103a2420440c0d01c0c80c40709a03000d180c100108000c060307040c81015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 634388767 1250 634387517 634387519
    0x105011e0b07110d032d0807080603120f040b0310060f021209100e0306010f050f0102120306100c051005070806180601230309010e0f07060e090a0603050d030b0906 72
    0x2908000341034882039800d600500e401e074055503501c030000c01070504c102d06c54040041c00200200740035520601e44c0000c0d0200c1000d65000400d00004a4041407090b017046010304070007402020703002040785002c1e0075584031480e84500c200741000300040248004002e50310030590202c620710014a4143c01070a100c444070300c0300003150011105040102c03101e0f026502d403100c00b9581030b0301140024000755000780d403c81881c2c2e4580b1a0100000d40310464080d8001074900c00d9500180c008400c03001642da8a40200440303095000500c006500f6003400c0116404192051800e9400f900351521403a003480c1c50074810303119441c0c480c0f00704560310f074001040540100c0280c40c800407442c2002c0d11a207100700701170f006c80e0410200c0314041d0065020008059a810300002403540d07207080000c0380074000d046010320b807807481c0180c410805000b0000700d0101c0850380c10b0b40b14101030501a0303040140892008041c844002e541303101c0031010820400c8141d07101c98041d00c000601345940300800294220092402e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 634390017 1250 634388767 634388789
    0x1210513060b090c0f0d091506080f070e0103110a1203170c090f0d060221160504081b031f0b0901081b040509340f0b1611030105011e 59
    0x4040130f01108030803580002e04501c0d0254807680c001d0910000f410714448068040c0c00c40520050403614182d1149045420403c110780c07803d50041400c98551b11a0720a01000407007400040002c0b4901c08200c0c40c5800c0f0090900100c0c1e074551640146429061701c0580000d0500026030540141e5015156000440300706058100868103000440d04610035942c02e029034036883c107020030059035406942c20400c1410b90303c034204c070051586808405048540300c1140f152900320a10359030084045a0598140c00064440b4100c125040050054842d18003a0144201c8000c8103100d5100c2ea01031000d1158008042502c8070101c0800001c0304040e0042d242c140c100490901c4500d02d100c00d0207401810559020400350f40f2040350908028008034041c03555158048841500b81c01c4003400c0705008005500d030300080b0b0f00c8003001c400e1f0320218000c1d0045148104010282400411528036141e0f00c520050b000ba0100d0700040790a68001381d21403260b100c0c25507000042e0031080180440500301044503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 634391267 1250 634390017 634390021
    0x60c08010f120c0302060d0209031506030d0c050309130608100b01050d0c0c02090906190207500c09060d03030506060f030103120816090501210513060b09 68
    0x901d4051401d440764125090741d802452007000514000100115002440c5903280c0150b924401c01a500001a8503c02d000d003042d500d03080d15505140c18041c0c4e9002d0001c0c41940e01410050320b4540b8902e900f0744161001b884401d000d030796200c1404085226000c40480e03082e1078040240d113440140a902c0b0700701030400d101845140d91100c10f80b00c524009250105d440005100c0507141102e07030203006900030180c0c008124488100103209405014404030b000d01040300410003000304d0050304002400b48814034030040085000aa8801914082190907030500000c02083c070544068014400c800c81e600c4115503001d00010b01031715092100507282c504580c6004c4c00056040400580c00a0074150b41d480480e0042e1246429125a080015803080d81d83d40c603414503c6d103c01a2030f801a000400d4500041c0f0407509600032003480c0d5541d504d03400c1e4030508040c01501c000404030304c0c0340c0c1c4c03a103030003461000c2004441c01a01c0c05032000360404441011a070400e03006556201480d94003c02d03118003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 634392517 1250 634391267 634391279
    0xa12140405250503010e0c010801331b0b16050a020c090c09100201020304210e010807022d0d02060702190222020d0c0813062c0a060c0801 61
    0x110794108500d1114180311120b52040700c1d6580007080d4000d1074066180031785940c04104000b0b500c5040e1203007600c03000303510ba03079440242414082d481c406080c5a861405203140b002000c08926401c040c0b5400e00b1288001c0001c10b150a001d1403410079100c09850106201003000c00401008092640d490304038541549418080e517a07000e0b280c1e82c41e0180090f0800100b0005000042d184011001402c1e13001a000b501c000038041d4000351010ba03944210440c00340d0f0805009403001d100c2441e251219003423006880015680901c0090840080d4054418030642c0092100848004148080745045100702c44038405481c01020340081070956100c9010310001540000d028244542c4000003a06001514408035210400c1056452811911610807203038143e1150041c1c00c04602440041101e4403003240c04031030403441629040d05e2002070080d800040340860f001116901c214039210f0402d000300c0442c4007400d002107400c0518035009034640b4002c029460040d5021000356207400c40255040032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 634393767 1250 634392517 634392523
    0xe100303050c071a09040b0603100e09120703050c071d0103020607020a092d09030903020607081e09130912030902040902060706021b0c0604091e05040c05010e090114040b12030a12140405 82
    0x1005680303002c002400004d4a030001003014103011a94440d0090310ed0316207103009440c641211031130312806d0003041030108009004185503040f001c2600032218250b4030391340901284d688074010698001c0500c84012820141074011142049070340c41c0c02410712070002001018090040b07001d0715000e404d0206181c04280e001c006a020b50b43c04466643ea5540285005103051203150700c086108460900c62001c0d88101902828200b40d080d074201c0314981007000c50740101ca01c1080f006049040c0e018100b01d1440c480d80c8599819403010344001a1005c190700007408941014600301c6615800184915400f011508080d440700781742c43c004d002d0700919800150190096001e1a503055580380d4255510030814584070382c1c0c0c4035801e82c00700414182420702c0c940819680c051b443c0403c10425003200c0c103041c40010141200c01b01c480d6031405030741c042c04100c041c118801180d07074403140d8010541ca002c8014401001070315030645601e0183c0c803c00351f544080c0d41c4400480c024242c80c0500f080046030000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 634395017 1250 634393767 634393769
    0x90b04150302013c11060915060301090f0c170f1903030209040515091807030602181c0506060108060d0b101e0f0e100303050c071a09040b060310 64
    0x900b03080c84581c01c0000d800501e68003000c0f80040070302206000c0c5204d180010107070a03810155607030f507414003109035030f085903541002d03101d1020b00e074484c4011850010900f01e00980041c002800496121895151180f0502e040482503d80402d02c1c030080040d00f548120641c80340302c0340b0001e48030b440f18240c1c078103455007002282e01c06110908402c0008141c40395044401024009004202c242000a900034014140703201c918007816541010414107140f003100442440f503e00020010f0b181140d0314100a03411090000940030ba181550311000d6450060b02c00c045001001407620440041c10414a000006070995060018001c1032204d42e440c3d8000318824950460075903a25030f200d00d8442c000e0a0481e6000240c01c140c00c104c00014641c001d508070013221444d00546110545640c02d4410300039041d5205110144036100400010307014201030281aa0385a00761303004166100d41d140c401034007004000d1850000040c1d01d45080c5003c3c861a518240e0030b50f5030764210310302255181c0e058409 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 634396267 1250 634395017 634395019
    0x9070c020604030b0414010b010e150d0f0c020d0306060e09061e06040b0c0f01050c04030b0a11030112120305010b0412080903010c0c200619111501090b04150302 71
    0x2002415419910307460100c4000f554444440640c61409081c01c1107021454000002c2a5003010981d540743d6205111034056400d00074080c030340360300025184e03001d00c0c0e00c0712610302c556980311140030580701c449100c0c0000d40c0c00950058a03001a1421004044811a40081041c40180d01d28199a5100c644031240d00c220b041d0390758114221103098641c0e000030b0100040e60701010015001c589101c0e0032000c0d02c80740004404070f0b5000000d610a0500780c60080743d80c1034154809100400115011511198020b20390720f50001e54800c00f0385088240341d2090300110981c41000080808028282e05c02c40e01030705042c9006c12803541002520700d02841188141c00101001d281001d00384002e64045504030f10b2f00900810202549213409010603061110070345000310000e8001c00c01d1450084c1c0f00c0a6100300400d080d02e441814600c883c0d0000c04480003804008640c1d018601203c0100809100b5812100704030701c03550b150507804001d0316501e5080501880c20188040b0000340940b1021040c0c941c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 634397517 1250 634396267 634396277
    0x8072c0d05010f0501080c0f030609120a2006060112051302061b0a06060305010c0206011a03040c080604060519020c100f020f0d09060b04020c15181510080703020907 73
    0x48241441ca0140c4104074002d404180f9140000030035840015070402c0d80403062383d2101104203140708241c1c1352082183e002e8001d410401119025a195500400b010b081d9400d1a0883e4149003441241c908890200d8001560001c414080150f0700300320507501900c0480c500b880301d40780c0100680c1da807400c6400b0080c0149804101c00707083e0780040c84601c60481200c001c540c00a049030402d01d01400c040e20080d0380c154178040d100079000d480400d8182c141d44140c1c1ca064020601140342004c0f5500040095446c050b407103001094880d018815203025074000c00000c2154141408841c4040c030320314030052501c0c0e1041001c6402c80300c0102d209013006101000000f0790300c04101111000c0e10600c2ca95500c02c50000a0b45000400c0d5a0302240d42940264400c2102e81c01c1203080c07104910840800200c07030741c4503802e518890300d00c0d10b900700e500500d1044040c0080d108091040c0c5401090041139582003181010840741000c124207107001070040c2c8005003d80d601e983c001c5041007001421000c100a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 634398767 1250 634397517 634397539
    0x2010b0a26010609180c08070308250206120907060f0905012604050d020d02030405151c0c0201020a180b0f0d02090d06060303031a031c020a1208072c 66
    0x240702980800010603440c00140a2091913440e00c2e8003250225108480c8003204410100c0d20440006001d01925400365600345818503030784400400c24140007030f410314411a200132600684441015011a0600a01120807810102c4605041c2006074000c0c500300b007a82102c00c1015684250701c44200d840a00749000c0c0c000011200301c0d040b100084003d025201c140c420310003001000940c110f000c2320160300380c0340803110620342281c403031141c0d100d0300368403040d44850002c00c509010024070028451004d03011003000e0b800c0c407100c01c0d2003109441c200542d50200ea00b00640e80c1210001c040300d0541c02045e4401d40c18829100040d010703142a88401c0e6501142c5000b224640d64111004d40740300426010011170070740b600747c000e4801d13402308500103405e100b0004014100f80c80e580300c1181c0018081d048480c644202e40e500140780c0640841148690444003022900942803020140d000380e0743c0240e213240c80300000e4196040d40103081400c3c0c0040d9680b5943c00c0d1180a0300e040b0600c01c4a071401c80b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 634400017 1250 634398767 634398839
    0x40b0c010e070b0c1b0a181b180506030408031302031f0204060f0e010905090a110f0304030305070807080f0c0f0c011a0402131a040b0f0403020102010b0a 68
    0x103000030a001400c1e8460420b011800240050103002c00c0c90030700c8101c0d15140110790f841074888078504201900019003500c1407048140e04055044135a4140000081c1d41080103940200401e00d03079002c60114400072944042e03122030016280140c00d040c1d800d5465400c00765a03407d05884020700d51500c84070001500d000f1580c1c1801f201c44401040a101031094242d100300000a41c0144034810104003000f0203640032030b01442342100c59040c140c4607080d02074a0301c42800320401c0c00130011070b0900d03504c1c0f6402080100342c1025003003a003c0150300c0b988910b041e01e0003404465003e440c0409019400040065896100d8aa030b640802c080701e00701810f803900800307600240101103c855102c500800c90058800d41544500c10bc030100340c1000b00301c900f0304000d020132841083c42d01e2074006541c100510107810070208040080070142d42192030207035511030900141e00020007e92441c01c00107810801d540e824081c14507180f5089541200282c039142a0401d05840c00c0c4101c14403500c0180c0302906 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 634401267 1250 634400017 634400021
    0x809040207170a18050906010e01030e10060303051e04030b0114180708091204060507060b0a0b04030b0a0f020310060309140d0f08090610061d15030723040b0c01 71
    0x215044142d103640c58081e681c1000c0c10500440300001000c2c040000b00107628680b403259240582d07011f840d10782c98008442c00440240050a41070003480c840d0240103250101c81d8800c202c0258042da94007a2266030706421008144004641c01000700350500091005c03d2008500c1e40c1118001340151882c0301e2004e000c07801d4180b0444417254680e40400030460400d4201c1c410740d106004620543d0000804070740304035081e00450046000141040c014500000c0381e075803141340c00081c000e0145404a41e20f5415982c0c41e44a500120340d949101403e01404c5074480c020042c01c2c010140c0d0560651820b0318001005268922500040513200c02000050059036410f1092800201044c0d841d200f011100240c0b024456101040004401c1c1d80001c00140011880323600808050000c241003910340b210445040b25031701c500d0680c2c0314089503400150f41da0302400c10026004600b40c561a4a4034030030103001124003a03841d4002d02c002080058407504c07040115011f407401c80c40140d0f2210740e00196180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 634402517 1250 634401267 634401293
    0x3190309060603030e181603150e0a0c1814040b180907080d08040b010608091207050c1002031305040216060e0102070605070f082d15010f0203070809040207 69
    0x4005403a00b08040189544603c0d2110341c04000d80d0f00084001003442c8035480d0744000c9881240340300c402d0711601900c51082e003041c074080d02c4200209800f6902c810708030546040076950107081590740c03040c00401750303041040101d0581900c5c3c1a12035085c83d001224403a070b54a10f250a05c20f66991031300075840e540308050305180a010100a078800d240404200791b44020314020b410107440364440c4c0804541c4150f5015100341d6100040c000182d103801c0080d0b46d01d801c090701c2c0c003546000e000d581000654001002d0f00790103001d0001003100c14a06001c0c00160401c00e181602150010045500201c8421072040d0032600305940069032501c85c0605044a40c030202001001c05041c408000100c2c0015006803c00e00d005100401c810344682205075945003e60b07450101095185000904603000040040741100b05101074051401408105081c1c401c011542680c180110340760700910b5503400800d00007000d90740d00007145042003c0c0c403061203034002c45100603c03550b00011050108090400285 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 634403767 1250 634402517 634402523
    0x50910061404150e012c0405010e16062007030b040507031109041a1503030c0601050907030207020a06030c030209060a0f02060903032404140f0403080a05040206180f09012c0903190309 81
    0x1b44d07142c200b52074514064500c00c406c62419103c0da4180007034030000a5004411503200c0d03207413200120394605000f0001c64410907012138902035040000040f8568070108e40c400c9101c2c8014008460540c501204c059644441c01c5005040b44e104000000306046028480003580c0075509015954401c82481d401910b101410340600011514042101002403507906036841220102d1266031100c1040b0100d004814010794000e1141c4c03000c01510b400f903800342d100030585250240c03405629001017070135580700104c442d002410720000668600d90500143c0d810008010240d45075040c030043e44c82060700700c0c10f20280306450030300e4000000e6480c1e612540b90802007182440b01454080b2400320007480440d030507004030b580600041c142031f00c02d20a4500c0395600610803800c000001004aa000341740c2514960405c0c1d40c444108420781c2c4020b00306000785074000176502060030865174260001407241080000a90b150113001c042d04e400b000b501c14440074415400482c49034904118050f108404001d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 634405017 1250 634403767 634403849
    0x90c0c0b060d1e061b0f1b0b04143919090507090605070b16030b040e0606031b0904021513090b040c0507030909050910061404150e01 59
    0x54080042100e15a800c140e0140c40100200d40c2c0817040213079142180045140003c8140819480007409144032080c0c0c01c904c182400740140460340c0f000f0b6507541c140c1c0c0540d03072910828560040f40108015098440d9006454211001c003990103440607400084140f100d8031a15454403881d9450b108c1000701c40085504c14201c103e642c0d1000d20004041c2a00d1032000601404004603000f8000c20407560700316481010102c1076903440301c00050340100041d00804168035501c0e222010340d102d0090000040302540540f540d42000e104162410500b018015020186030406002569584e8409a03000d03405854855048410403441a030521a1149a1651440c610001705910003558410844d4210a840070444000640d030700b59100e0240d0138009001401a02051103040d065030089500f01c0740b684e0440e98001c0c6035071300103004c1c7d0386141c002d00050360045a01085606d8a4000c0036183c030742c41c054140c4039604280500d889428140240d0200d03e4642020f0528800c910881025a031507000071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 634406267 1250 634405017 634405043
    0x91a0603070c1b0519060504180f0c0f0206060f09060904020312130614030f060103150b0a02031c15060c080d11030405060a02030903040918020301090c080601090c0c0b060d 76
    0xc040f105072594018140914401e490344064141803551396401d8455540b00ca0b4241440c022148282c60780003036071800c150b521001c00d54160b04103405040b00641c8107488900031a003054000918001d80104840c2c4940c0740f1207100c0c0c52940741c20034010341101042e501e01070a44c0c0c0e18000719250400c0e1505070b8449402c00a0b030748008046201c8600191585e0307503129070200d801d03042c0c045094001501d418007041c51050100c2c0c080d6010b9400b00200c042010842c0581558401280300e054000c01d500342e000d070304001003500300140610a005a20041030304108403082c500264520401d2960003410b050181c841c081c801031046600595000c0c0300d61840a1101d103003408030003402c45d0001e071800c480034482d11011451003000750003524800d803205002507040514000c0000084c03d0702d007000e03c4506a42141c0310f000360f2004e002d4140c41034000c081591200c6d260615041c64150140d002c0c14515241c8501800c0e0b1a9010244404580e049140903150f41c5070303a80003900207203501c50001c2070b442403400b13 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 634407517 1250 634406267 634406303
    0x7050c09042316090902180a0204210f0305033103080f040b06060f0717131719061404050606040e0f07051908010207050a060501091a0603070c 63
    0xd9400c1041c140c1005440c007030402103040d19070314003280aa03000c0580c210082441070b111340c2d40c03011551031700080410812201100c942c040d01e100030f6440307100d05074000400703000390307040d059210a250001c0c204651490703469464034250b802080c00b000b02080400400300f0a024680b2503000d60036402c0c03810022040c0f074080d0760200c00d422506c5040340403a030003c00040c0c07103e0166804910903a003201c1005030070b980c1e00701000000d6000010312410382900b802481c0c00300d01d9800b2902e030314800880702c4076598152100e400c40f41030040e500c40421940981c181c00b00003000468a0342c55803002895172062652035192000244c10440d0f40207504c4180601044188040001c42c1800b40100340c6040010a69140041d500c4850b00c1c0200d408a901c00300d03041003a8107241240940140c00d0744055108551201d119900ba6840281c0554195020504ca42c0034404640f091034010b01e0114010440e0b001d140e0303021006601b00c031090038072412002c00001c41040c0100500e212040e84040b440d10b038180aa0303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 634408767 1250 634407517 634407533
    0xa0b0a030501022b0b0d080c0f16080f03070302070b03130503071515060e0d11030a05071e050108160513030303020c011a151305060703020102070b060a060903030507050c0904 77
    0x200041041c4e4100b1240c0c0c402c240903034420304075007442c00b901501114510342c4a0000647c4644030418451144010180896001f44020800100d00c0a5038042044c41c1c1f0220354944405401703901090f8100f0403407a80001d0700014120210b81c544c0c081c4039201d941300f02d0102e030000c0882401505070300001335034800308440074895025803803039003200308100300c0580002101e1050398000c000104a113183d00740c2551922140600d00d0520030030603500840d8600f40480d08089a1510888030b036440380c0c2c1c0c01d00207800c0040914482e10381540c03012201c0d624005c0020024140a0200303401200e02c0320080001d02e1281003220201c19100c21598079a40c0d991078024001e5016001d0901135510f0202c0035480c120a007412001001700c02000703600b031560103400560041e800040f080031182c14500001070030b03481707071800780c1a4107019800060b00c0e03d442d402d094403c61401440c4030300c00c880e82001030010035000130646040d00e401d403410340d4031800d45207020381c42d000c2184a200d0344201c0c04010402008210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 634410017 1250 634408767 634408807
    0x3110f18090105010f140f120106033801260f0f010b0402120606030a0e071215060513090305220f3809041a030c030a0b0a0b0a03050102 60
    0x14000b0003c90780c2e5010703840b074520070f140210640144410120311a41c5812a07a6100118008111444c40ca48244400303003155226402118041510b0790703221400a402e490225840202005c0c0d2075100940c008c00030820601401000300c01d02c40709621070343e0b03c44070940d00650309614608440e5854205035205503101520060140e03c0e60030700c00c0c4410784d8202030090380c0501500c10003070526034a95008200640c1c00040444c84941d0b5200320000b9003000400c98040240b61001d2400e4011a0a00f8840e02755000e01c078580a41504142c42088191100b0300d848440d01e0360070700300050004142c54115894415036041e00c0c03d4800c02010004071000020301d5104441c40d1090b100c001d9607950071081c090080c20180702e0708486180c51501000c0501120100c0aa4040020546881c950500107012901c8410000d1705c0140d02c0041c46103a8101023000048500e0300b00c004001a003c10b607500b0100400040c03040c0a01510381750f10281030b80b03402440802555002c0000c0d91181110506942106a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 634411267 1250 634410017 634410031
    0x90b070b240315100b07150225030e040b04020306030d081009060e010603061703190c060c0e100212031909080301080102031009021804051512060115170103110f18 72
    0x14200009001c034180340c200c44403a544070060410f040ca030803880c11f00a411503c1502d00125000001940000d0781c00360100d2010303c07a0322043c030b40c0714905e81803008850703620070018003443c410020310106960000d80364260700050326190700f40382d5a010801c1c400d0b2400e503105000460074840e011508a29002655041e5041950100040ba80d038000c0130462700c030f50115002c40c5d0b410800c0104808110985120440001820310041821300b6580d984210340e00f0a84640001d0038044822000d4640031003000f810303c80c90b1000f081da400b031000524000b4400940000f150810819800824100e140c00002e440b41d0010001c03510b80d17a549003010301035881140e001d2581d410300140400c0310711280c425240c840000d02026518054a8400d010080a010700b15001d981c0c40d40c40111410b645014402010041000c00346c10194503010551b1025100d0b43d80c020113018580d6035540444000c14041170440e9005081003604440e140041144580c1400d809500702c080515000f03015816202c000d40a021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 634412517 1250 634411267 634411291
    0xb06070303270b0f061504080a03110102190810030b010e10050312030f0403032c060a0203131b0b03070309050f070f0605180d12090b070b240315 64
    0x2401142d40042c402c00118000c2c2030000f2540425541081841840d07030109001e840d424202c0780320104509550807551005c032480e4001c040d14400c042c0d06c92219000303c00800000d509000000810301c419042e03010654081082d07000008001e03030b0615000100a580004241003656180c001020007918107c9080006140c21280003a00e810002684000b07544c80f009400d003903841d2110700c000484400ba00650030540c03981c0c41e09a00c0d0074801060151607151100301145050540d4000d824040010442c802251040c4200b0064421200c42051710551068000420200e404c8001030101d030107402c011099440801040207064041c0d06c95844240142c007200c1e44003000514140e5101003601400e61003a4810300100040d03401280070740207601c1c0300380c1c0d101e000e8585103011401202c54900c056a05298025440e004950084001c1024150304208070346040b0964640004040024003440d81290519201a0380e1041050505401a074018141c6010031901e1840a841d00030a441c2e0044074a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 634413767 1250 634412517 634412561
    0xf050624030d0507050c031b0109060908070504110f07031d03031c0c0e0303120114100c170403081305150c1b061b0d0806060406050d0f0b06070303 65
    0x42800e85410940000340100080d6054542c101c07200c0d002050103c40c184200c0607065043d54090141c6684c5001d403c44079021a0106d200040a420640d480181801170021090101c2c00c1c010039071000340c49017030b0350110313411040a4220840d0b1107111104040c2190201c1c03c0c1080607031084120340122298520b80300615901400c1540368445c400c10307071604104040601415050b0368114a00040da0703400c2807010605a0f601003400d591001f10000a02c0b9242d03401401005022014540000c0c0252031294655200c50340c068042c00903050090103080b80c0c4121220300c0c4201500710b4010310350104c4025199035804c41d214100401e02e002d11841500c4000000c00c121003d481518145800100100801c2801c040b103d441b2191107000039800c00800c0007030952800003e00c1c13500c1c0c501914030040c0015158940000c05d01200903055034840d807810441084182e501030b09840002501100c00100e03400b00303440080c01044210f1410f0303042800442c0d450180354041d4456030390382e101c40c44000000303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 634415017 1250 634413767 634413811
    0x11100b1912060911040204090209040608011e02130f090b010806091b0d1409030d0606020307030c0809040e0106082406030303040b0403050d02030130120c06090f0506 73
    0x1564080c0039250019411a9006020440e40e40043c08194055107524000c644240c02203002d90340941c101c04210790300000d60000b09d081c5031081100401040700200024840d00d549441020b040354903242041c1d802280303801c0b0b4901001d05481c01401d0050220f000300e0342e5002c0e941c1c00341c0061501d1601003111400000c0c481c0c00c140c1071442c0304404a6008082c00f400785005407045070002040c0d408082c0d52003c443c0341d15043c0c40880c03401001510011501c40070741a452005940301a0050021504207008a80c0040d4211444043c0c0b10351000d82c1c25142e01c800c0010600401c01034283c1c2c1c00d1582440000214a5000710350b211040e00054011444000c84034194440300500f40e131a507805500410018010840b5400b1040d0054420b2a10503d00840e404202c8266002078020102c3c41400b22601e40704070190440860510360704030b101040806194441a050228100c4800309010200c0c031410300b008030030b40c000c0780740d00d87c440750300440c5a09504040d80e5130300c000c07203500714802c0561341c0010340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 634416267 1250 634415017 634415059
    0xd050a09090606082728050307060e0d17060d050a050a1401060501050f1b031c0b0a0e100e060604031502040905090a0c260a15271211100b 61
    0x507007103004009110440c0603980e2078440400703200c0094000d440130711b0317144002032007840109000c0d802514041240801c80d4205d6040000301390030f000c10b005041084200401020545035849072003110101d0304001d483c00d0085c00d000802c403005219000d001c111904003c0701203085100c13000fa8000070040151590015a00f40c030035503080c450525401d000c10310303a801803a402513050380c0c00e040c140d904050141958500f10400400100a4661191268100d6003001d65812001b04801c10781003800742060b44100492100074001c10300b043c1070007000140e2a8503224100c030700642d4003103014a910620030304900000d42040c050041d580b41890b0102e40c0c0941300041080d21030303030400d00c0c0c1e42405140c04000300c15099060b9000c51003d400c0c3c00c1e6400b19170000e110395090580509030a0200d0580004071a0403500c4c5c901e20034950700e094140006042c0300a0f003c0d05102548902d248521900000d411358618280480728041031141c182000903080403600000c1000c641a6101c4140b40085d9000d148 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 634417517 1250 634416267 634416331
    0x31e06041503060504051213081006060c15061205010209031b011706040f09060c0905060310090504050c0603040c031103030708030c0d1e020a091202030d050a0909060608 75
    0x7005200420701403020071196400a1380143c418000c441811890f886500140e4000d02980701d15102c1c4c0c01030410001c00140000c40400341c060504002150501002810180c41c2240140c40c20705605c142c0340204540c1e078400d50144c890030046251040903803603c03d004c0d501c0700750014042e0240101848103606002c0a00050100584450300100e0002444002d0761070000c00190344143c40740600e5015403014818184003038002c0317a022800300c07628040640b402c501507000c0ea0103007904008102055a18000b224295400207201103200e07103484c280b40e8548803030780f1000e0398042d8002082c0001c020194160200302c0780b01c0d0701103100c4081c005041544034000c05202500d50f080420000d600d50750180c0040c012048030406c0024005680310300b028071400c40c07020003809950700059000c0e0f0290071130007490007000c4400e00711440c0030181d40442d4441000441640a120010503141100c50060050b82c0c05040707400b5040220030391b9410000e021f00c50907103100d1030100d502c2400a800c40c0000300860 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 634418767 1250 634417517 634417541
    0x403020a020112090807080d0e0a08160c05120309090708070509090c0d05010603050a0f06050307050f1c03090e07020a03020c13060b0c0303040201020d020619020d090602031e0604 79
    0x10460841a0700151a0001010b94401c40581d1310400d0b030000500c803401074030101d40114050ba4440050040c030404079a880340c002000d40e4003d14001000840b070400b1240780000c03958500c0d081d4141443c0c041c2950000344c10180d48030341c00060520500200001034101c90b1007c41e00d51150b0f44a02c8800d480d15882901d480d40050b00400150301e080c10030565007900705641ca44c61910380507104800d80c04035070081c1c000034002521182884006195805002c0000c1c81c540c60421140b40b408001079601c45c0d452098500400b14406d034080940c2c0c800c0524145180d568002e18000361917840d0091140c01540980d0035090280404520958400129402031a5241c3c00030081c4202100800c01c0d400680550880900d44880d000700760800d1080240c41c200710366000940d10703402d0a10019040c151200d030f00c40d08662001003040b8a402e443c6642140501c284000103130754007028184d55000e0070303580d217001d48580e00000a101443d011b030a15628520b082011a0203c4d442e1340c81000162000d4200e50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 634420017 1250 634418767 634418773
    0xc0605120a090f0b0f090f030906040312111213061e080a0e030720012609120a0c060509060709090e16030819030209060403120e041a0f0306040302 65
    0x690148103a034000310195000f0501034496040550b5042140a002c6480003070550020003071000d500c0c020820a00d002c48084051802c010b800c00c080781c090b010b103100c00741c0000884000d2804150060361090031004410301a41c0f80e805000501000e241e0018100c0910031b2411040014054464441d1100b052454003864810b0009210100d80030781010744503004a43d512400c1c40300d002000c00c000c0240074468074509001084c4001211550b201202e00e841c18401d0700c0269410642c0e2000610301c4804c16030384000c91130349510705c0c66850803009100036900e0040000d2407180c5c45410800c0b90031041d109030002c0c0300942d5200340c0c0c0350300d40c00c0a4541d1008141c00040502402115400000f0706552500854190740b5041e0400f15406015070300a4941c1500064006d00403441c0f01081f0312000c2060030207520380601a80800c074a40b00d588005807111001c5145626200d00c10400d1003d070200051003409001c0401208952148110324090305c01d441c2d080f2503500340c0c240031903158842da03015005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 634421267 1250 634420017 634420021
    0x106020a12180e04020109090f1a0405060901050d1b0b04080f0c030d0e1201050103111e2229031506030d051e03012402061302060a03060f09090c060512 67
    0x7504000c0d03c1e02601c200d060121030b00300402d0603001c0f4030880320807980600011a035a0f6245d02020700324028000c600c1e006e64106800c1021076200c0e8519203045943c01d403000c440400b800d050140b0403041e08112841d207541d810000245001114028000707a0750341c2800d440f20075404134041969114402e10b01601130f040315000900c071502500e01d40c20003c0010f018403500c0250b01c40b1007400c44200341c02c00c8503040706401e1810100d0500341602d5011202e6081c10317540d00b26452002401c0549460100c00c80c5107102d00c04807403000c500b070b0404181d4009a42504000e0303007040c00340810140070904024000d20852b0505506441003000e0a4001e00c0041c014100726a0b00340c10448240e03110b045502030100b0441064403403121400c005500919131008048010b5042844e4110300b42100c4010504543c400c00a0060380300c0c40081841c04035904580b0241d503a08100d5058015111607880b015103114400000507520f4101e0304008501032046e0005016107032203080a40e0f00340a92918040e1f81c051401c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 634422517 1250 634421267 634421279
    0x8010b2703160801020304110a080a06020d0b0301021305030c03031c0b0103090c0f090b09090d0809190506040218011230120c0e15031b030106020a1218 67
    0x400c0120050054140c900300c0208020701d00d1242c0c5603a11416260703500200b00300c00c3c0042d010101440300b108480484400f460040003c1c2d858503540d2010b030920340c0c00039400805107100c3d4080302c100c0d4030190082d510f0f00d00e8513018846400480c0b203614003c1c000c3d070f08001c8491501200b19950003000c0e0103822204400e20107680010400030704207034140f41d50b42c1d41078804124482c0031f4200a101d07d221004555081915001c04d960015200d60b001c5c1003a2424080c1100c0f001c540d20010203410b1810a0040d59140501880c110031900600850071420041000307111020807030038402c81c02502c20015207800045002c4250000344140201034a0b81031030000007074050b00307003070b00080011040c0000c0ca01041040304124514862030f140419000c1c0041c0100800c05c1c001c0140564450604034100c100300d5001c11918011120b4109004a00000081a03955080a9414002c40c454002c0b0345941e103c3e48080d5441d5282c0314103a407501c14007031249005c144184880c1281282c035943e034013000c074030b015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 634423767 1250 634422517 634422577
    0x50610080603101521020604060513090507050d05060f0f0114070602030a0207151407110106030c122d0308070333061d06211608010b 59
    0x10740703029814007901a15800360b0165008030002c4203c2c800e0000d19003032503d41d0748503812241e05102c005041003682c402c0d02595078001a901114114180207035130300941c1402c600404225000f0280b460310704007c0c0030b50b455020b00505080d1410350420001c80d2940d00c1042503030150194041c1d03201d444108040036a503c96602e451800c081c0201c181d042c4184c0d95218000e0340c00c100d4400d0f4940e40c0c0880e41506200c0d10070084500c102a0400405c00c050030600c140c3ca14074001070140f011300040c16240c401b40b44003584440f0066401082e8640c5150b251070301c90b07865041c200408d580e445083c00b4041c030240200c00031180009a094034140110103980e4083d1401d04008101400303069075000d006da00240e85099203402c0c0c04416000c00941a040190100c4c2c80d09242c10050401c01201c0b251042c08188034541c054032a000c45905480e4043e11071707100c100700c0b404135a15000d103440740c0c00c0c0050040c01020700040c0303040a44442d18160380f1450404014041d0501080e03100c4260740c250441d090180c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 634425017 1250 634423767 634423771
    0xf12031f0611070512060a182112092a050604080102030a1d0a06090206090d2609031f1107031205130b060907030e15011505070305040b0a020a0b0f04020108010905061008 75
    0x100305814038003034054032150303074000303601249282c09030300c01e040c030003049a001d502b10351400c40359070041003102010b445160200c424042d1844c0601900c2c05580029aa404403980050030020911a9a991202174681c043d410035a5601d5019080844e003204481040c0f00055443c64510006e207c0d800c1c0c6901d41d84050408007600340c0e0858020000c030b003a1501c402066101450060300b400111550540e5480c60440e04204449071890091200009558001c589945203100444445401144038410900248a441c20407803031841d0010302c0508140d0000d81800c81d008911030200003e580703405201e4481610540e00818010300107001455911f04180c0403604501c4e00e103000034003e8400341003103181c0603c143d2051202107034940100f109040c0300785420200310851070040c1c1007800658000e0118082e03030040c0c0d85004000715006582500c02c01c684001e461700810050464148603407201d031500016102039000829007000401ca00f4044c0c01114004e1074054841e5036000c00403641103c09400c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 634426267 1250 634425017 634425041
    0x5010501020102091518040504061a010305090a14120a020703050d05130608180d020f07080d1b1104090f031e050306060903070305010507080906090f12031f0611070512060a 76
    0x86d070103411030181c6032845514840c5120320341c00240d000d1842428858244003c451504160609081003049a40800c2c501c0d55964015910903105100c8103480f030424002e201c20784408180402c141900680c00600242183c5c0a481962124072904900300c07514840c011082c0c84041c03100c0c07400c201d1140306004240d400703501140a030451070600600103080650b5807111000690054000305d03480c80092000038020b015140040c00301c001360300d0003d0103c07541d9451410306a03901505000502000c13607811a412100100704201040c10b07031030141400e40302040107400182c01d00c0c44030906442c54039104803804400e44c03101c0e811950b520003007008036400f504140750540034103000080000c41c24061940104495140e0210700c0c43c11110035880c00030000d00188503a8440d091403483c1c500c0208418454021111b0125541c1d47c91000c00d003420412100c208a82c90310303c030030001d4460752000c0f481c40100104815214810f03034550401c407148180c1d101000b840d40090021807099209075015410a00c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 634427517 1250 634426267 634426297
    0xb04051e041109040f020304050a0b0601110616030f0b2202040b040f033305060a0302130608101a090403210c020d0813030c02120f10050105010201020915 68
    0x190400c081025102410120301e0b4009011a5400052034140038052008101100c210700394500b07600d8407070f900d601841000d4012485080483c1e0264414044080200e10040850700c0a013400e0a480744803900c55110003000900d0524200300e5818280a0000850b400400e1041c003040010b98840f078044039194012450340e82000006071140c0e504004d4002490f819401c074880703d00d50b083c44009144118001d00d154190784001c140141d000d02d001c600d40c0d03234440000090650f500350200d80c0352015038102a40c420703000f030141243c0d4441c82d00210b00740e0f1091029500b40c00580c480c0801510a81000240502c480101401d41030405032110f0764414001e103810003000e0360b80c4109052058501c0e041c0f264650307c80e20407910f00c0c0e8041102103c8815946003030111894840542c00045441d0000282080b00f6007240c8015980d40c7d90306400c00c042a001954440c5884451065607050040c0c1c40d80c5840782824000100c030760040c425034841010290032070004101c0703050740c80b1141d8854151401454 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 634428767 1250 634427517 634427569
    0x81513030e1311070c08030406020604030e030129100e030a150f060315050c090904020d02030c1e04050c07020105030f09010905152a250501020a0903020112060b0405 73
    0x1da207401040f90040980640a6440c000ca0602503000c09040d0000100c075881080308000366640000d146078071075003500e004901c1044440019014000c2d07882405030034184988101e104490a0075455147c103c1200ca0141c00521100140c842104458100ea490b410444507140807414030000521136068280000414203020900c0d581200c40a40064422100245420500c0c2c0c0d11032084940004420100c0b9007400d42e06070020b00c0d0140b004000a024019032050001151010040200c00c01d0000700050010780b001e450b102c20500350001d01a02c00c4d814440815165883d92084401a42e0181c0d2000d10355034810000803502d0720082c0c5641119980c4004500214006108031420b074400808078050300d042c000e03030342e800d804440003011030301c0349c203002c9644d01006440c8115074541005406070800d0314290312036828072401c049130281c1070f540002181c00b4072035844030a4500ba24400d80b190442d019541c0d8030181100c031940100904290b0410041c000c1c0d240070441c6242ca80c45000ba410301c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 634430017 1250 634428767 634428799
    0x908070b1008070605090a03030c0807061406030c0103060b0a0807090e0a09060605090610120f0e1e03160f080403021206010509280c05120103080301081513030e 71
    0x4480c129007040802401403814800502e042c030029000f4100351400909111120b0002030301071616220007000d00c680c68100301304101100c419035005075000101000001c0200010700300f4800104c0356603100307003c1c042009c03d166000e44242c03c03c1d41c01c44825030717040c034490860aa410b902c010f040d14040c0f1202140024045c6058162a41310310703c104030200d4205180e01e0504141ca030300b0b402042c442c030b401c13070100003081c2c460b48480d100c0c8210f5403500350150700755000c0700d400412040c015040040d090004040d003043e80090b1003072142c542c4514207185c850650882503113074010307820741420407101d904190000c90702e0f40120020003401740d042149410340c0c0ea8009803a500364621500241e800480c010407040c508000070720350118420001c00d50101c4164080f01400300d007040d860494941c7d03020002c1d0120320a000351a001c0022510401d0f0651b1641044825900f00344640c003810711031010b002c0703011612404c5140c040c408202510301840d629903000c2c0c5441d0301840c2d140f9004440340d1082414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 634431267 1250 634430017 634430033
    0x1061a2a0304060309031d100c1b03030c0215090d060528050a0606090b0d200a02070f060912020f030c03010510170f120318070f17010507020709090807 67
    0x140003d88000414000d249005403207482070000e20f1004c40d01c3c1f800e9103001038541ca843c0f0000c00b1060300d480c04901689141c1300d00c0c400e03105c41c0400180134190101008140c1c2010f031925607140203c0b401442011995200b8039648601c50043c0d070400c01c24800d08000a400b5040550030800300103144c0ba280000040300c02c0b890004440c3e018005454405201c84008244560009440e6170315003040e6082c141001b443c490b04c2010f0142101d0781d80c1340f60b4401d6007400030750000380780c100541c501640c80b0baa400e4000c7d0740c1d40050203207140284950f5400100c56000311314120840d0014260320205525075020400c11084400d5295018003924203050040e0b9000e10070301d44980407c51441d0942401c0128081e003401c00d242214910b5880400b03c000c0858002400b00e04e54903480d4029030f40c9907940c3d0503d96038090131020745d032071900c218070001c12805040652031080c1c07008403e400c40511058407101d400c0e16000e50340b060141e00030110034005440a50020202580960001c0b45041c095654501d9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 634432517 1250 634431267 634431269
    0x405040504200904050309010c1a0703021c0b0d02040c021504140706030911040e030705060405030d05061c03050a0302070506010b19020a1709120118020301061a2a0304 74
    0x100c101c2c414001c0014020150240301d546070050702d035100d8620b0940d40e1169680324200d5800d040c0b2540e0340d0040304002c46004070441442c0c00305040074050511200240280d0403840c414504050803940b154841220362150009550700200101c078482c0064080c0b00c01821214420300860050421022002c0098140300303018074800c41040c1c034a03401040c1a6800d040f4141c021008050911807488007007001100210007a50044a00090640700041001e1a501c03424000420a020f07080030402800004000740c088015000018000c0daa14034082000b09070020368145e8294841c518000040fa00c510041d1406600034100180351220f40d45440f850518244c2c040ca90450380040c1a01120b0442010b06555100600052110103001e9843c00c080c91141c2d10520075801005c01c1c0785146654503130f01c0c0c450552201c0000c02c00d030818101211104101c000c130690180d03003010030001e10101000c0d903040440c0e040c2202e90382810400d0742040d89240e034542c10190300500000c0010482d880c1840244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 634433767 1250 634432517 634432523
    0x30302040503010e0d020c0a0509160e0319020306060d05060a0f060906140f0f15180d0525180216082a070e04081b0d05040611030a05090607080405040504 68
    0x4c4540000f03801d00031f1a040d41074810b24042e540b90102084507440e048a2560000c0c150404c040d80d100214104036900c6409003038150781441001e4001701d0607400841d511540600980646030317280d55402c14049202c1d0745020042490f40240000341c00b14105a2181e6840414174030040303000c40d660001501035031195005022413119241e510000f0340342029608034000b6040e43da400c4290307d513000023418609a0a1611809140010003078000c2d41d6040c0307203d1a11000808000b4005498148682e4030000d00b5a00b103d02d45d8a482049a40c221003081c030400c030359854000144408655001d800030390800144100a140e5004c4210002207850000c1d10000c0760001344881c01903052507400c5d1111141d4107081030607410819041c03014401402000f9407080c3c0008034240e5585080800d0b40599824260b04141c50250402000c40c256001c00108101c42d050307a101f80700f0b07607420340100b0345a1240518030b0011410400104d8224100803000d4800e041c001d2001500702076440c030120f010b8510840f021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 634435017 1250 634433767 634433773
    0x306030b01081e01050606040308030c04031709120109020603160905041d061b0a08040f0c030c051005160212070f06030f0e0a0312180f0501092609040504030302040503010e 76
    0x1540d01080348504003c1c40808980082c00316003001000f040481c41280005800001e0000006003000c2c0c0240c100c030f00555214110842030f207240424881580c02681d0311911408200d0f02c101040d00050040c0200140c00408451654681c44040d42c1249514140343d800d01481c00400500c03a80c4520841586115004c01004a60004000141088001030804001003038034410348030309032400e00903a4425074aa042010751622075040042901c0304450008210340c4003000007000700032861b1480000c41d441900c500f0003210f410541504c440c010081500441c01d01101c2200241c0f40541008030891030b001305a03034045803541c1100c0f8140009411010100c1c1d00d590081c1c1040803203102c4d41e5041c501c103101402001c4420b66000700b080b5050b0301014070f419194060890201181490b400d00035a03c9801c403558140e03540350103406403280780c400342d4125001400c2003591003290041800b80c1855000760614105078041000000c0c800540140c042540c2031102141640303091040c50584c000b58401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 634436267 1250 634435017 634435033
    0x605060c030405010f05070f0818030f0114151332040309060f0806010f030609060e0414010506030607030f02160302032703030d0e030f0403230312040f030306030b0108 74
    0x3504410482c1098000c00c0b00800501f400701e9919800000032070303400300c00c0e9039a03403001040744076554052042140d410f0148030b1030140c483e48150305c40c80e000c029952030308007513903a8103059030791100800749101d030015a080c5401d92038030495403110450030010441c1c030024680b04a80b041d1540da0710700034400312420708004e000c2403540064011009006900c0c040f040e105240c80028208100641b44c0c0741481003d0070300461040c001d422100162002000800c00b0980d104c21070000c403401034900380c07031560030744030210041d41040c001d10707201ea44080c00409043d2034182c0101c2c014150399038041440c135400d00a10604405603420707002007902030341c021b603111440404400c42001d40101e0880b8a1600a80b0b0303020b0303523103001c030503544840403034500080e60a2510550303605520402d074240301d000c43d00150100810000c2c85500266490076030134124000741c032040c16581c030700c00d0088042081c090b0b18009000507880c410000c00c00340c480d19000c03402e140d0ba6541c80c08040d0082c6c100003000e4122002d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 634437517 1250 634436267 634436269
    0x13121a041208060904081912020309030913020421141f0507020a0c05010e0102010905030a110d02010605011403091603030206061206190905030f13170a170d0605060c030405 76
    0xc03080e040b203000c03511001d2031704207036403044003034031446503040a41c5062084018aa60103200d5120141400003000d654070716050b0341e01070300c81d441048441e118810400c0d035114414210f10a445c00c3c0c03182005100c02c1c81d500121341c11031810a200040714080b103615402d4646010130b100120b51006a0083c0e80c0300018035050040940320024200001c551250040c40041100880d240d01104d00030308046501c0501c0000403030150a9400014000f4800000d008240d980d000041041000c4c020064507080c0000c011304900fa20b003203218080c00508100d03004c1000400352002036400c240414202c0b42504c10440c050540d003110ba50007600960890b90800c9075900301b49084461404a81e006000c480c034120030b540c21500c200c100403050341a900e51454040050820807500351480c8115501c1d01c0c0c0a9030b410b076680d090b8050240f09901d800c41f081203c0700301000104034905650104454112548285002c0416001700d03600960103a201c43e80041c0300e4480c50000c00080844401840d42c03581098 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 634438767 1250 634437517 634437527
    0xf0c010c0513061b020f0301110c0a030806060307020606100507060f0501030606080c180a020c0a050f1005190f0209060720010507080a0c0309030210050304030f0513121a0412 77
    0x640003000b13100c414010919040040a50b40211a50485130038103988034010100c0d004001c50410300340c02807000503180c040c1e05800109013145a00c02d42e10424070b07079549001d004140c041038800001580c0070401107006c03450216010380300b003200e41c0380c16401d05026860741c0041e2001c00c410242016a1200148148102e034001c80000d000000700800030040d03a840460340b03040b0800d5529184141d0100420b40410311a01200d040c5940700e4100c545400c0c80d42030440e00c503c2101d41403040340c4990205060191000c2c002d491040c1c0107c3e84c41440c62101403074010250400400740b503051a03007007180c1078072591070402900c0c00a0041d840030800c1840d048551284030440742e1100d040c0070701403204d00009000f04040301c00075110740c500750180194510342512081701a401c02980200c00c90404045c41d603001000e50720990203550340d030000034424482540c1500c105075070104400d07294a02441002c4511000c071800d58451031080c50920242407070030600d908169000c441400ba005000340301c0e0307544a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 634440017 1250 634438767 634438769
    0x3010c0f1e020a080414040f0c0f0806060d0c210504110904020d123c1407060c1106060103060602060a11120c04291e07120203091c080406050f0c010c0513 68
    0x315008001449c1c140c00c0140590201240090030070072004009080780e1591000d640d81c0c0c1103580c030103101c880710390341d00070700002403625a44464020403800210081d0326406240e00032500810010009000082440603486d03005000340d0b001f403403510314080080d9146d05007030341151060b6038060030140700d0301d4503031541c0808661409185869084001c081c02c0d10460895040aa1b41440303117050000112609980c050381001901d60b91074036a9004107507800105190b01140283e044d580d21349e880c01f006404958185c061200180d014000003504000c09500c4103040c3c80c0d00f081c0260800303842c0e0315551000081214821030701c00000c0350800811a40f12401c1402040c0e040840f0101c884c00d1803d50811f00aa4000c2c1d1002291916001007074002d50703040358070090b08507070414000c04081c2d2010303643e580b200450703501412590281102500041584815499000700341c41d1600d494210b08440b075411240030486644010454440101780c240f080d01c0d107a8505450702904d031180418013400e40e00803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 634441267 1250 634440017 634440041
    0x501020f03040e0402210d11030712110109062301080613030507170307110613030212090316030b010306060b0702030c01030c091d0603010c0f1e020a08041404 70
    0x1092085480141000c4269002d40e104910411074a135524000503401c202071103100d4240c4541400751010064010901490104041e25034002e644080c007660303660703803085102c0509015603c0500f074407640d04c00c07040040e0075551140040f03000515a160102142c42c64500580504002c100c00442d2400c02c4d40b80d103006143c090058002450b01d130300d94086545e08880018104a000100b1400300102c00310001c0b00c4001c07801d61581c60b45068000503000810100c042c100c41c3c4071701c80000707020180440e0707014030380b41e031550103407070403055001c8002c0003a0040355403940d160150304614411846400480c5d0000c5004022080131b03549142003a40840e105600400340c6a0300402280000d41c81c0043c0d6507203d60800c5c40c002072602035407241140e0808a0340c2180011900440f41c0c101307400440c043c40c6026190440080000c0c0350b107002e040c0e503040d5a41c4103050100c0c901e50700310400d140d4481e268849200b0140141d480b25101a40d075081641e00503042002d03104c90304400c06641d410284108000848 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 634442517 1250 634441267 634441273
    0x150604080109060b0907020d0c0206040b1b3c10090b0a0506030604112404080d090e04170c070305060f0405010b0109230307090e03030f0a06032006131e050102 70
    0x1b00a4802510390b1032151028048c00803a9082c036045403070701402c40b0010503d4180380c03511500383c8503503c0740d95502d003452600c0a206030091400c4010000e5a0110352103804812076010810342004206841015041c1c5007143c080e011600d1919081d81c040d4542c482e206218080a0f0b00d40300e03210004132040604014040d42c026001c200c009075220300e141120003000c0b24442d0311800f95001804c445000c040601359036040100b80042c8600d80020561051180b60b214500c0454403201c1d1400c41030002c450281200051170b0400c0039410860009022156903c3c0c1699234003610b83e05c6a6103011801c8e0f03101155031641e03800300300c10f0003820702c580064440c0910b0850000352911044404402c0180040c16041d03d108031a5082a07074104090703002000b000f54284494440340d030040707860744c01c1111117000c0081c40200041d029503c40c2316010640c1d41c804d030700860101031003403021000004017001680210781001a01d011540c004d209400a006510303288e08504201071202c0c0c8000d00341c0d4030840c1994 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 634443767 1250 634442517 634442521
    0x80709150b03100308180a030b06120312010506092d040b030613021c050f030403030e2403100512060118090c0920030906070f0905030c09150604080109060b09 70
    0xb5884102e001100d411000f05c0d92188013504000030403d600b4a00168003401c00c090000030043c00541c0648a14003ca8202281c2c1804240c0c082e00da00c545804401815140d10041c0490f1070003a02411140c0b0014046004080500c0c0318503020328419140007101011a2221071114035040c01a43c969460a80c090b001c0303402e1540400c00707854481c7c0e000901c81c0c00d400c05e0980119030b43ca2000070f24075400400b100d901c0c0824108150302c1c0c0d441400260001100041c0105150408180c454401c180d4043c030040d404070355105a2140740c001800540c0c00e04440900040e00d0ba64614102d1028640e00c1c0107003115500d07104001c0204140c08249000c2d4600304114403020440124034013045544042010030165000b5071400001012f00f16200c090a502100b805506100010b03000d120310407580307841107a50303603240040d20700e100d9511030694590300645001480f030406240c1030b03401070980365001c00282c50a070700140c00c4d07400c0381c2c1152a403a9511040101480345a0084100d40101a580800e0b18 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 634445017 1250 634443767 634443781
    0x1090516050a051c1122020c01150303080406090c09240e0c0f09040b210f1f0c030603080c0d141602060315090a1406030d0f0f020304080709150b03 65
    0x113825060015040c612451903011954072000c100d20682800b032400daa00200e042c2078143c5c003c0d0080070140900717620741250b0088030485104400300b070301d0301919180c0b00f5948503034581c0d000d0000c0e004100c682174565400021046030781e00401002c500f03107480803912040c00054401942406038054043d404c01102801b4000411200b00c426007466000c255654a220304081006070480c090800c3e0030001d0b0000d41000d0818910b0030043c4442c102e07040d500c0303102491046503654400c3c801c03c485072141c9620108492100f950041c40020483d080200794155662107190540d0004d100ba00c0312500041c500085c203d0b4090b800c000c01c03811500f41d40307080c2030940c0c0100416000300c41c0020f01036900000820608201090600145140107104030010b18141140b01d01030324000d40f0403081d150442c004074140b46408604071f2003600e80760741d50131b0311400b007000d0465651016082c0e500c1903010801c00495000e605004043c05005400c90100d00c80701840440300c0015043d9125522400040c0180710b07907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 634446267 1250 634445017 634445059
    0x607090b0a030915060816080606012619150b0708070519120f030c0c0b060d0219060f090b040b0d0608031306020c040605091801090516050a05 63
    0xa803400030120940300e030721411095000301020480902000181c61040c070120030144c100000780c0e6544429503a9070495413401290070503a071f020710866a00004000303010f95100c1c20b04240040300c0890100c0700141c3c0107400190124080c0d842160b509103034054050b00102501a80189040e40c0840700201450030103000d00318020380400526200c40013446005112003048000c9111440500344160f00c0b0451074000c00b07001c02d48400001040c4c0517000c00140701d0192150811002c034981356200021529035540c0b02c0c0302001400154441c000444110168442613101250049440080800340d400e08002810340312040800c8c3c010044250400c0c00000986810340e4203e844441000b03440d049600303075070300140c01c60342c100c00030a20004c100c1c108140f0390f01030304d0011580c1030303000e480c0340b04102420700040c1c400600032035400c4a4020041554140e2410503501424810000019904041d6030380500b0000f1041800072240140c035070030701c0140b50403103803030004140032074100d88040b0310826a095 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634447517 1250 634446267 634446269
    0x507230f0f041814190f0507050913050601060804021c031e0309021806010f05030a06171c0912030e03030903070602060403171611011e1413030804020919140402030d02060709 77
    0x40900c0f403148a1b0801108026540c06080000c0c00039201d46030440304080c2c0507071035080c15125486014000079485004440c103901130b9401519880a08006000c00c21001050040c210704102d403408040400040d942d4030602e00c00d035242d50101c0c002006004111060300280301c03025a58103a07005101c903982c1c001c04400403801c1c4a0414a80741e9454114800c0104159070108900040b4440c0080c404140030600c25134a000c3d015804d5100800200c0449890369240a50361003141d500c0000c0011074001d140080510400400b240c1c600114500420b05001560b445200076900c0b190074002015044024a8600311108494041c18500681c400b0910900c100702c0b00140b01d504000e08410007829001641c02d2207807144903120358146a0800703c02041038940d200c07500024000403900c0c1c15a41a00400210b405640e8a000b54940c2c4c3c007040b0491001500a80104407454103a5018100034002c07545c1071118040c03554480c0c039050040c0b40c1401c440e41525011034115030704010580b500100820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 634448767 1250 634447517 634447523
    0xf0702150c03160c1d04060e0f030a11100609021b010510210b100f14131d06010f05010305060f0a0b0c07030515040507230f0f04181419 60
    0xd940302c0d44c100400d44402d1500302600450410900b11007552a4400c1e460081d84901001c000743c4160b400c1e029180c0c481c0c190400c40030740007003007400c4010380304d0810040c0014096065803e0022583c40c1c110403500c1d50341c07101c82c0007600800c0075451190420118005034403414001c0c4600d20300701c44880c14081c128010303654203240400c12502e4001c548500320301c056130b10a010050390b0400d0394a08403070315510300c25008040c0c0100c40201c0c8100280d0520008135a0180440011100b44c10700300e00503000e6940e52406103421481c0c00940e0b40800c110040c024801001402011814040010300b500e400600850043c4100e00d48a90983c07211003645040340d010a10b84e1791100840f040d42403c091070740e80041c1c054420110800034403162039502900a51060b01200c01c0fa40e52160110901d00078100049d020007114030100800c0c2c204600420005000244240c03001c03100180040c0c12200d601da102014030b00800c3d00001081601c511882031105000000c044030301560300c0e5913901c0c2142e901c2c02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 634450017 1250 634448767 634448797
    0x10c0b010324020c1e0a0203030415051e03010306140f04300206011e150c0510110904050903040803041202060405100f0210050114061e0f0702150c03 66
    0x11840e1010b21401150408241c1d142c1599241d00c0c001c1a1940c2d4816103c150400e002106401c8226050005a0304030b01540500503505141c41e00441d001212251140c0c2c00500c0020458000d4039064603a4440e0680b00c6284110384039415402c00400b1910021407101c1e1443e05107080c01089885083c41039841235101c45100020702107000b05c6210308038010111040d041c00c2039000000d468020032106c0c1030f1041e0041400c100000e1030064030015400e8401c011043d40c0c0408070030b483c548250101d860040c02501150500c4500c2800e5030101c5510b20082c2800da2004030305102c213460075000f04c0d500301e10000e004500382414507403001c0e10792207030703200d0030f44221522a00c003411511460240c50040c90000d2070200c5c080030510b009400300c09075640721001070140810114540b483c82c8a02816144544181801c8500100500440354020000500c05124410700307140314003904130080008a02c140002070701c1d00880e07c140410152011405401d0035001d02c80d50b00c80312000001d03281d40141d86071030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 634451267 1250 634450017 634450043
    0x20a030f03180f140d0305070f2603071b0b010513090b07030506030f0105150105090d120509010207080f030921060f1608040f0803090709020304051b010c0b0103 71
    0x2a90200300928040040b00c685040000f20040034043d094102c40600c2d5948030b20800090030081d19002c007020040c0402c4080c0885000316006081c01d4419a20500c40e9404189001140c0c0300344210034500c501c482800041040304a5612040c01c01a46084c0005000100141da84000c000b00301406801d0280c400d41c4118185440650031130351074a9008140703c40f15080c0311100030040d000864040e0b000f8401c045060031075540501c1018819072170441501c03007002c0a5401101c21b5806010321f2513000f0013202a480100d07680407a8803449140f180ca403541e1740e80b0701c400060308109082e4000040c40d0410b4940340c0070000080100c0d40b224008540d40c1a04482d40700118004902d0001b5855440c4a00c0c410003a5282c890200b56004116403140344414194000701210b040400311401000c0203514030308100001c0241001c1c64010341100190f9803141c1d19620b06000b00d0300111829075607075100c0c45901003100201141408a54400e103041100310b00305440c2c07203141003818480105a042c241c42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 634452517 1250 634451267 634451273
    0x9051006120b070f02071d07080f0c030402061813090b0a0606080c0c070b04080604110a03020f010c050c04110913060b180f040501030614010503010e120304020a0b0301060207090e0109020a030f 85
    0x225039030203001f14078101500401d40061042e080b030800c42d44580411100c0f008611900c1082d81607500c2030031011034841c5075a55590a0081c950270007844111240103100300300d80282d841c9220f4111440205070001440080303410041c240000141454002d14a00b1009012840e844110f45500504038180e5070783d5215102c080501d424001c3d0700c21201c1714400700340480d2609010404c58041c41c0180c01074208541c1c010204900c140c01e13840300951000400d5020343c1c0d10350060b200402002e0081d030944100170796040c0403030b06840c3e42d178400341901000000c3c2e544291a089801c42c1c140740c00107204101c03003070038580117000511903a810001410010744612030316545201c0c0683c0c078401d002d0b005101c1c550b035a14008002d08496039409250705c0c680d03400400e15090522178a04644514802007561490801809141754009030050740c10401c201070104281c2030b10001980205402e03401011b12500d07201508040303480c0b240000a03241d0501c05144056039903180c2580c150782d000b0306090400c200c10b203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 634453767 1250 634452517 634452523
    0x703171e060a091104560d090203100c0c0b10030618021e0f04020702030a060e03130e0f0105060c16170c0103090f0f021309051006120b070f02 63
    0x36101014a50408015680402c001d60107001103606243c1c00d982d52219030118482401c0030500c034002c411209400b140c10700140e03011100c0421141d0078070900c9121b103030200341605602581d0040039003a12010840c0440c20200403124041002080800c85000950001485081c6850019040ca40c1c0e40300170800301e40420b00300c980115404481008003e900c0102c0c1016641140f8050b4410007521503e103003170f004000d020794180c8200a0541000e4201305d01000020b4100342c500740e07098800c5220880005115119105507182100000d40d00c900c044100c1c0c40800c6810f0700b0400004100d002030011075110945542c2c10b40710201c030501d4640c03540c50317246441c01c440c84070700010f880c04070107001030700044161203800002c0040080d1610626900010750554002c042d0060190071070119240200301c003008a15420b902c01000f44a1003100072624100b50b413044002510a43c110907140703c61007001e0310940d0018441d2510b0303910814401c1d118a580040e008200c407050100d50601800c801c2d10034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 634455017 1250 634453767 634453769
    0x130f0e01120819021b04021903020f040306051e0603070602030a05030403030f1a03010c1d1c0c060806030105010f060c060f0e030c0a12050c1b2101020703171e060a 72
    0x2d030f008030070f80030315240203566017030a503542c600190880d400d20340340b81040e0086850f1000e1416002051119126040b00298408042165040014000803000514078044c00707001d140808a4540a4100034915500400000d0302e03140c4281d01c1002d00300714254001c4169400c1d81a6410300f00e4480c2e0780d90400b60041c28180841c130003070514001c00041c000c00e442881c040b040d603042c0c0007044494040079090356503070581550246031981d031000000301c2c1c1c40c0410810500b84400304065403007040c0303a03036140545a116000300300465842c40410041e802c0074460940180510400c21a0381440d00030081c1c40036050701c5000d4110b44d2200220902c840b03154004201c014900c108403580c411400c43c1c0280c55081026048611003400419540034600c82d0003031343c40301001140a450410046a1001d004261080c81641c000d50003805c44c204210101144003200b0000348000f582d0b0b01300610b80105100000710390952200c40c104107004214540041c0002003002c1204440c0654440c100054205002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 634456267 1250 634455017 634455037
    0x90109031106040308120703110903070b07050709052505040302010807030207111e040b0d03140c3c2d0f0102070c06020d02121c0902030111130f0e011208 68
    0x70005207000440d004802c46c51042107030356800c2000041005800c0068440d6001d129856448000c0501132002c0d41002040414491004c44040964035842c1c0300580b001240c0310005641912041307000f41d80754001205101c141440c2a924050443c0e0003c0c1c51b00c4c4002d8150020940e0101e489400c0081c60341c1c208a4501009200c1d20080805030700c0101e0003044469000d014500b00f03101c03e500780c1811800e0058966040e10782c00d448041c4d005c402da10325001a01c042e022481100c0b511580300800c0500f00f011120841704204516100b1241104d00703204407031120341c4642c07000c0e100b01550340000300a40708112180c2d0f00500c00180b002202d51402c001242010b100e035100141e03000400c031600d02d020f0211030041e0203030381c0200300ea21016a110150008481004e030030411005243d18040384900356914049040080c51401503004207003150f9410a009012640000e01c0100c600d200f03400c0c0e140100719407032191070804d00f0311a500d2a20300c0e042c4106c0401d10011005c5e2803c01c1580802e468501d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 634457517 1250 634456267 634456283
    0xd020319091101030b0609030706110a060c02100e0f101d01021210060c03081603180b010320060403080f0405060d02120c0702030604120e0a1413020901090311060403 73
    0x1103418102180e05482910b240401d2404110881e1070804806032440e5030002005010058500704081e941d0a0301d01b14031084900605601400140380380c840d19503d15070303a500803c00c8a01544061084a140001103012a4032100c0f200d4002680000c007540080c0444101203548581c2034200c40911120740c0d0017480550009c0307030030068150f00c10192841032141c001d45c1c0e801d00e69511825a1062100500540050394240c0056100710010014228440c52032900081582c2c000346501219500c001080383d208403104010403d00425000b50341040c074a24000113602034941000503014820b5101c014690800441c03041c41c0840c070309081d1802408054210b565500b903a0711464025032102031420807621140700071030607201d450002e90b0724003035020340280b0850b110364450030340a1004080600c01c00c0409802c1c540c9940360808540001c1c01d0030000803200043e801c04000043c003c10007620b05451041c0700c5c0b5052680d000d0b11000171207402071040260828160089083c92080d0b400103840f000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 634458767 1250 634457517 634457531
    0x7110d1404180b03070504181415040506060102010c11030405210a0305130f031112070b0a0309020418030c03140903030415180b09010302220305060402130c050d020319 74
    0x1050b0300030300342c0070400324141c42105445008100440380013920121100400401000000703c4100d00d01c0c1270809942e0895007070005c00111401e0001d402c40f005c44c1d068200c0000d0101c1960240105840301000d17041c0b080d01c03a10303a103d034296a4000c500c10903100e06140700d07504a108650f5481c110481026405699a46844d070030b000d0929800821041c40249110350005564842040c1100a4a82c0140401c0300740301e101c001c102d0443c01c0ca0001803010b0003001000503180c00c4010003000034024946000c40e5401141c010001200e088850800c1c1814200e10110006a40708104000039949402d01c0e4016024250603216107000d022401034152000240104000401c081800306034041561a40210f403034040007142d407000c071840b404040c0302d424851842d80b503000790050304c0802c1c000d1458110341c443c0c2d814540701d132491551003030301c09801101c240070641c144a03c1d49180715107150014042400a0000200b007449060b100c1c1d81020f0b40400402e009400c0e00d5101181d881c8000800c1c0401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 634460017 1250 634458767 634458809
    0x306030b0f0718080318310b04020415050a020a05070e010f090b0f0f0f04050103110f0910060c0f0501020c06010e01080a02030709110405060c07050907110d1404 71
    0x4100c241c42d0500440c60075003107241800101c0c003189040d02e108402450501c550025441d00c041340704501d10b40e00007071820300c40803525009080b1a030040c003544500300c0c0d44d0313a250f00c80000301d40d54851024029401044140b2043c003440c5201d100e00c200030b20344240d0b10b80c0c0301c0000b01c0c100030302550300610b2801501400981c1ea40d0207542141038403d40c4011403480e641e01c0c014030040340e0020349460b401c408048905465403401007040103aa400260182c058404034600150481e80241c02c111071005090521200d00c1c00c0c0201000030845054400e0780321401d2414921007031050902c50b0000300025441290101712020004a900b158808020741d2141505590a0780300c0c03009010b01c0075038080e94000060200e90016480c455683c01070f002d840742d1401c1c1a1b4207000b4041450505200324410000082d2035220b0800410500302040041c2c0300a606100401011b02c1000d0403220400010034205c0150b650003003220b2850580508005840c002d000862500f640990f500510b090302c0311f00300d00012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 634461267 1250 634460017 634460041
    0x150f0b09060c1e0c10020606100207050d03031d150c0d180f02030105060a0510030203091e03180906060d1e151d100e040c0902030103032d020606100306030b 69
    0x2290b0540c0d4262440042a02e0170702620250b03400d1180300507444170300450481d08044003004402407591042d10b42c0b40361200c01058040102020403030000381d44003030411070754110280d04400008a04050b00c1c100407400a800440c21010341002e80c1c10ba4006405135914507141e10a4101180710846980c008844d800c000c0f507201201c0c10168000d50901001404d94600904441c1c02c0d910700400c0d04985c200c801404500a41004040da2041c3c426030751030f0300f1500361400e1800d02452058004540d01c401c46014a1581c1005401c41d502501080090044031394070f030025101000b40c00d010018104071b1405c0740c2851803883c1820420707494a0510804c8880c1070300c0102e02c003510035114418400260741c0360030a002010032240c403a01d030304400d40140704010b56040c0e200d40286c00b800602e5a1140c96102e100201e80c003e0780101e0106020aa41341c110140024090110300b030344400301c85540c01e00303002c0692a540300422541c440ca140c442045e440a010340d0200c000745420516415051a00254a8203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 634462517 1250 634461267 634461313
    0x1d0a1b0b25020d0c0512072402070f081609020a05040e060117090601080c030312060108060a0902030109060e0c07050703060c1103030a05061206010602071422050406150f0b09060c 79
    0x40181d10a5440c40030000d1b0000700a4100e4101d07124502e520401c3c400c0300d08400c03480901030021402120b000080e1030071102805009000d541c0042c010790114a45151401c607041d5012020882c014419400321980020540f0111404810f44080503903551004270743c0020740c50700d895005500b501c18440e80d81400100181a1802c48003100d650864600c00c1541d00e002d01d9400601c9034a040000803460751080161680108020701010310058807243c0501c1a40c20907001946056554041002041c03403100080350054000f441703040c50903d0507120142c640505010242a0030340301e4214214a600c24044200034940200c1a29182d040025641c40944010b0b18400c0c803c01c1104640c4424140210311103040792201c0d00100b5041c1c0c5080c0c0282495160b400900303500c5800c481c48084110b00c01041140a0260410005514030340752610304d040303d40003001c02100740c0304200c0c14041d08001010b070405803443c91100d540c5443c0684005206449071010407146805a0200e4013054030080203003003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 634463767 1250 634462517 634462519
    0x15050901032d0c090603061a07030309080c0102070b0c091806190906090c05030c1219020a0e012d05070816120801080309100e01031d0a1b0b25020d0c05 67
    0x411813076031743e400480039a2028020348030791140041c640b9211000400060031030710700c281408a44900c51361100f580076005401c282a06035000a4940e04104c0c24240311584800800103a85c10804400003160f40741c000d00c1c010b00c10700c14840c0d02154055440d504900300c4802e20791102018980c4445d0030708040d100c10301c282e0700518146001c2e02c20741c600640980b881402c2e0342d40300908064050480d1041c000001d0b014040c07002d02c0003c03242c16603007180000e024030031154849100300381108000400a460483c0a22180c140c02c403900d500d04000220300101d00040c82c0360081d00d40c045401c05951522030b50b48002c0c038881e10082a075040000350005141c5000080d101c450040e80e1300c82004e030b1244078141d40c840d80301e2a8103c51030300050041448525180040c9400585445041c42c1070b40000d9020030707954269823090307104200700000d0490409040e02c8040004620301d180c540c0b00c0c00035000300703007890f0042012005520b20a441e1584101d840c80e40003403010441d00a0b604143c0540c1c80180030715 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 634465017 1250 634463767 634463777
    0x120f060a0204061b0809060d020318060f070f090e07090608150a0b18041a030c04090c0303080601050c07120210020d0207050f120303091615050901032d0c 68
    0x10300c14510510aa4080302d4007520355200c124400390801c9101d1411480031180050240b01c8180c003a11400007400164403030714401a5242448040859418020041e400c0690b001d0002c006040c64200c21558000740c07142000c254140784841c0954214a0940120440d1035001c8104417142c1e034010750120484402d40c441c0c043d0350701c03400d40008141964440d5642c204800b4003080020000d210b0060101a11020002107128105000503041e07950400e1441c0c040d51103081088064034041c0210b24090804550402c08240969104400360320f070f9200c042d00340300d807000008c0c2d0f00d0f03402417003214500b40640080c0c03030f0354603110340f0311800c0502d50702c00590003601d500d450b40003110300014040d00f001e030840c0c00030080345241c81c003000b083c0c11508020b1a0042010442011600d0041000d940600018809880340c0d8400e04000c41c981d6000d076000c010008000c900c0858090380043c03c9840c01c150a180c00315103a5298001e0354050759041c40241080d075059414001124907951041c1a0280b040d960 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 634466267 1250 634465017 634465021
    0x602030f0a050c0423010302090d0b01030b0a0902130b0414011716230f0307180e031204030c1e030c12360b040e0405070b070b0a0515120f06 62
    0x100d8030700b074001c034090505900b480c140100c4100c4152509005c2c00f110515000d0302d810988000b0608030451124125402000240140100500140e80f00e03404500b400f4104001da40d2600003c00e284149214151040d90710041c1c0410f52721181c0012103807049601040c091035030349504540880301681599062030160008031210310148031007070790031100801d2200d102c407000d0061240b600d11940c5040b039405000c440320000192010700010009140704009501c050306071141140035034000300c4403110b2580040020b5800441d0200309160001d4051600144580042c6000d0b260105083c1001e50001c110311503a40c101640a5000d000140c0300d405140c8a1842035070064039a1000902a1a01c20802501060036107511a045100341c21007001c0d1040280e507a00040c115681c441d0700004e003101420b074108818007004000102c018600480680d1800c1a80d403164080081c1c0030b490f5921280c1c903040854102065601c045040c110010700c0a0707071110320120910340d98081c00103030210f64014200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 634467517 1250 634466267 634466281
    0x207081308030c0c0906060a1d030105090c01020f01110301060c030e1c03030f0b280e1609080312070c11090903091017070c03051303050106090b100c1205070602030f0a05 75
    0x880340035004c00b034051400d2000440050726022409c00c00381e80e43c4440c540300d0761030341c1c0d400340101d80c054543c0001130140c0c2603081c0b000a04102d0201c010185507814000c092010352900d2040304d0448000c0e01d0a80600000b40c501111513605029500781c0c085140d60000301e60a42304202008000d2090b10204a201000c0c086c440035a400006c0c995441114107008581507141d40d24038105040000f1840b040081e1149641403100800341ca41484051158074605159500101c181c1c000d0140800254201100c1c421204100c01000b0402e40c104120f002c03007001002800c2e01d0b01c03240d110006040caa11480d08030f180a549410141650380b20b510307c00d400c41d140901072003021038600080c1c1c000120701c0d0b0319604151403020300d00c0f50171001c1080400400801d0512a407403240554410000130842c145402e40401c142d03200320300c046108010510040d440a034000781d41c117040580c000c0440c0320700440300b04280c845001c2d401c00a48410300000802c03d00c03001d42c54540c0d100e2254410100702130b85030f0034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 634468767 1250 634467517 634467529
    0x260a03050a1b120f11070b0c0c0303040306050105030c190b130b0a030906060b07030804110d020a0602030307020d050a08061210020d200c060f130c06110d021903030207081308030c0c 80
    0x5c111480076130049034091101e000004002c2c0100d668802c201e804103045230021074034683c000c0e4015642c0503503540040c4100e140c2405414202c020481d00124559101d001c0481c80c2045407103903105000001460b02135812480607060020724035022000c2e29540a00805000b41100300750480d2641c0c80d1260100b1818050030036107580b42e8165840a1140c2c4d03641da90340c00503c4c0c45240c841e0b801800c1d0070503200144d503a6600c44000d01a282d01840d06ca0512240180c036100c0e00c0e080007010b2200074000710301102da0020000d43c2c094001c49140313805114145540d4140040d020015900900006425006445a801c01484912f000d1140f041050b104408001c080c01140500106138001c00c0210392038143c0303048081e400c40360041412040c10344e599600d804006103980a0408102508503145800b002070050310b004c00581d0000e40480c0c00c1585090901b928503110080a065004c1010400c1c4103005d000e55880c4549410016041a151120076540c3d400c803a05001c00385c841e40d00544d074641010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 634470017 1250 634468767 634468787
    0x1e2706043e0316180f1107080f04030501050c0a03050c2502040e060a06030c08070e13150504060b04140601080a0e011d07170c09011505071506260a03050a1b120f 71
    0x4108071b04007c0550703100c0b022940880800304840105200120200d0400e205141c01340011444d6290703a4442114064151040141200310700e205c1440700d4400015414034041003445401c1600784164000c0c40040c0040403000e80805480c407805041104d0071201ea4404000e490203001c0c0040b10302d588020003580c1d08401e00800480010050104240035142c910050981d48138220540007590388a06c5041242c60864090340d100d600c80f5800710560a140c030640c00705540b0082c1c5e100082c0b0380070002a1096030058508144079503103a400030003446080d40928184142c00b048000089420810303141d4034405402010f40341450710301030700581540024140c00204000e445a800c50307185c13007403405054910640110911000704508400550030041b40e800160802701c00081c01030601451125101401d1117040302005403d0350801c0c583c0e1300013010340d039080e818907000b42d4603461703030f074003211002e101815400704203805808031020000b10b541005107018856861081002201c80d044a00002e2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 634471267 1250 634470017 634470041
    0xb3603040603050603030c0303040609171204031d151e04080c011803050105070810050307030f080d06030b0106261e2706043e0316180f 60
    0x8200820032031a80650041640714100405807420098a0240349095500403201201d48941e0b4901c008204284080c1a42180c2009642e031030030110008a4011a2200a80050144086e89021207558400d071303070a2684044000d002c00b040301400801c3c41c203081c0c21060000a40245084040400d0340c1003500341c40441d00450020f00d6504601001907030002126120005148070320f503400700106800340140d0b409141079a0f50f450700d62610404501040d0500c0e00725038420b030001441000444da620f0344040946030407803400c0c3da0307500324120a0001460b09500041c4482214000094469003181448110741d800c0d180b07200c0c1402079079905903045003088a408403001040114000c40415000302654400c5002100c442401102490702e103442c828004030b6031040c1c4c0308008010030829801010062442e6202c01e80206000031600f07412400d608049000d02070121014022756960100310440016446544c020085900c0d100001200c841c5501000c0740c139802c0015590b0084000d03c200c1d064940 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 634472517 1250 634471267 634471273
    0x31207150c021c09230f0f0a14040f05070c03091a040306020d0605030f010b040b03010225210804020906011e030e07090f050f0705041208090d0b36 65
    0xa085101001e50380201211141000800784c00828621345018198585021815004181c42c0c10481040220894554180c1c0144001e18000354192500303944082038909548040741c01822440105000342031a464585085081806106403160444204684d0a0096503202e00c81d030344641e06800c0107641c4814159040704100070030030100309030741e01600301d4141c03240000c24102e0380c81c00000e103041c444090300c4100c5c0e591940c64802c2803410740704001180601350029405e046e29805e8640c100030840b00340c09a100720319044601003040c00d001009490354100344248100350f40341c0008040c44130850341280500468004a0095800380310f0030030f03010401c0c030074202c415403101100303e02600914a03804020320907003c000c01e051006010300ca990711020440000c007460502c1800c00001310280c003403800d1007070400044c0801030140c04040d08841c0c00001041d521200100440c100307080e1140701400e0b0b4100c42e41400341d000c440112910f08922001003070990600781c811842400020007402c40181e078 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 634473767 1250 634472517 634472533
    0x14070e04080d0e0601080601051e0d1101090e070504030c1d06011b05060f040308060901031e020a030807050c120c010815010504030506070306060305010902121b09031207150c02 78
    0x5680000100704980b030003100410031400d56960745181c60030030b800c4000983c00031001070000d810310303691144030001355a01201c907413489040800d4a440d80707070704082c00c46202c2182040850340a4107038039006000b40d00501000f8500640010001c0c2c005000441c0c1c201c01f0030400250070700120003200d0070755a1002e1100b1140d2110801074651680b8043d0a9050300504120100865005c0c0f0216201d041c05102e00502031800d40b8005000100080490b03109040040047c000314070700d405036000b050031200d480d80c43c02106000290045540b94801040041d0000d10007042040c08580b01c8400d85065a0707064440003c0000701307856070703e1030002600042c40703940000c50351039880051402162040c184030745025100d80b82c4500b0101c080701d03070402080e103035070f001c11006500d48101d038014400c0c00000c44c109900f12400301402e00c406071520004942c40a805100e18000a049074200301001b4111211f80600c203030b000265810201007541d00310340784141c0c40c0041c0d40134001c8109051996020f80815 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 634475017 1250 634473767 634473773
    0x90c030e0c12190b0f011d040f05031e0c1c2a140d090605042607050a140315060a05061b0d030605030f010606080c0705030d020f0714070e04 62
    0x4a030302e210001c5030324400d07440024054450102401c44050140341401c0c03413894401051010344006900c010300d107841070600c886080a9442005411a500600c03111960300582001403450240840c038241d80309551080315403840e04a8024030035040800c040e180100720031101e070000c505c4215a02004189200c4400304040d000e0b54007a031460024002140c003a07055615020400c4010b82e0795128036501c40360032281d400b0b8010070360000800b142d2600525150a12074205015000c802c072404504002c022450846001840b125026207005800d1a20450b910842c0c00d000310001c0040d103019018003140c00c100c80105101c01e501c00c81018141c40b40301071412043c0302d40350384022600000301114004ea14084901445502d41c98040e955010855500340810036003840d880ca40002c03ca43e1400c00100445030300300e840240d01020100c42942c40d95190b0030031a0540c411a40c82003802031000552411380c000140c080c180760760180c0c1c9504102008070140b83c0d5940c40d1030207030364004a20a0009000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 634476267 1250 634475017 634475029
    0x108010f1e0f090605010b091e131d060406061a0c0c0603220807030e03010c08040b0709170d08070203070323390c18060612070306090c030e0c 63
    0xb19119404000404481a40b100e4007100c0b8203030030907071b007581c40080c2003003280c81c001e84150038202c1117022a49a1840710000611661021140540c1c142c3e203d0707459592500c80b001c0904d81009100056888625151404c800140414000d0400440760071a407249400004000d680a130b05115005104460307c5200f0010b150b0001440c00c00d054814203c44c03000d140300105680c4080d48111041078171070b645894064403101c8424a12402603150027000300c8000c2d40444015005074001e100050b0796203a000381203070403440507001650201e00001c20b4080da040c0001d680d541404269a402c0c2c02030321441800ca80720320070b000b0f000e00040c50340070303250740b40251400300ca45081c1810f00c0418a022502d0b0490103050306021410014500032405007903880003c0603241d050452040301803c41881c40c000005c05000e41c5541207015014050002519070b142c0324121000b100e10481d181c4020301e010350008001c2d154034040d00717642600708180815801e01078082c030079507024610301500c07890b00680b041c090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 634477517 1250 634476267 634476281
    0x13140109021806160605070309080702040e01020f27010503060d060b131b0815030d0e030a0b1006020d0503270c060a03021305090106080c0a020705090f0108010f1e 72
    0x61104010b401c41612640e4070700003000c10040500c414440300c400b60034401c08560303004210806141c20103800d1000100500b04442c05654111800034191108105c40d0380207004080e01412900c00006d03000614000700000c800661462402d00c0140c0c08220004460078041643c8c1c0940000d091149500051481e4100309410b03000a84104540650703491102c081c1c40e00ba6282100a00c4040c08031000c550348959002e501c8483c15203583c03e104290800310341c0c0c900e0b100c0700c41c0d1304010845481200d0b60750305110301150142c024401804030705007603215a090b100c031403094030094440c4184014000b4042c2d01500e100b2142420391114050040517200100103070a0100015401424003070b82e41036455101402c14100c09540040e01c2d0060b60800c1025080282c11180c0304400c00300041000c50b82c03050406e80e110f0983c4001580302d4840315400d03440c214854114030343c440454010007800014032207802d81210072100081c00b60b50100300c04001255005005502502c0081520007070ba00340340d8011803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 634478767 1250 634477517 634477537
    0x2220b070b18031c11040b04031101020a1106090301060b0708121b04060c03050c0a03081605040b09060f0403060203070206061302030403080619030b010b031b0309030706050a0609020a0e1314010902 87
    0x1142405e10070004032015405030300044000f0307001080c1401444010302005503400d1080c00107085000c86511400d0b4100386030710313845225034400201c40881da10290003120080565821160306c440480c601703034206030801c03c1460b481021410024409071142019900000c4003000d81c9071a0030304014017194071007032450301038040c800208400c41c10300104028441c2864065603400c142414025807034041c40c0360b0901440204881400b003440840307183e1040310b03110541101c200c0d60301c941c46600d09141740220740c4054400d07131010040100301e41c0c0106d1424402c201c111010007240482c201a40124002600c0180c0010607441c00035205e0b062200481035809075031289081e03d50341e03035a0b8480c00ba0209030844035001030044248031480c010b010354010080140e104081c11494020a242c1c0d590007016409003003a922480070070007024040c0d00178005444604d000355036481c1c0041c005094440005003490040031a440b9008042c9c0e0030341b080c3c141400c914080c500c1075920309007914020b9040000070b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 634480017 1250 634478767 634478771
    0x13090b010302121801060816090b0118091a040603120804060f0e0a050f0d021011070f050a11062505010209030109052b08070302220b070b18031c 64
    0x100114150118850312074402429640c00000e035804803242540c6d4182e0101d505c99000008509a1084001c40b00080d1080c5140000d02030450a0040303030380f05101c0c00d0440b82e240c0c0324070000c1340300c0d5115000741050b0380103404100000641102030008032640f0b0312008d4440804179143c200c0161007141c4194209005a03030110741c2e8845181914100c9810151000c6281d001a840404015062104800709108800278040ca0503208001030345505907076100e4003045980c1c1c206440b0303852840c010384000e5500094010000107103071500703036528243c0c030354191607040244000c52418504039046483d240c04100d00551601d0003e18204003502d51584106d440795001e00809000e92001d204011001c0e008100514080211501405910660290340d42c1c1420a0f900c28003159908024100d810602c1480c0040e0b641c80c001040703e184801c00d0003040e91031090010f0024510100b2800340402c20300800d4010540d407250002821903424060360104942c2060000d004032801d403180e110402a448000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 634481267 1250 634480017 634480027
    0x160204090c0b030907030203120a1b05210a08060406080c0d03110109062405031903050705063d0614041502011505090411100504052e0513090b010302 66
    0x107400c0039604203c6810040394405202041545810460f824000510781c27a40c601d4081024402050b6029030b5064041c20358402c10b403802080010407001140142e10292844011507000300c004176540811203071400100750b080494401c2c5018444c410454015070010700243d0000424032295a0306d210095081c03104002450300490001e0140a03407041c03090300c0000d00e0492076003140002c4440e11000340300c19101440d003800a51400210301c404c521114044208000c807a18085402d4440c000e0028041e00401050001d4101d031b201c0b000c261584200c5200c075502e03000c103448840301449885405c6055180c10000c00c651805600e104210b0503507a1a400d1815465452000a119a1241c103c2c0180c0d520440e4820309040034980c440a0101101e603405142031a4580e203c030700c10b442140c030784110360b403000c000c000ad400340b02110024600909541207001074000c0035146901c0507034880010705496490030b454079118030212030b030301c4001101c030a02403030401004500034407150118078145039003084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 634482517 1250 634481267 634481279
    0x40e24060a2103020d14030408030408071e0b0603030a1d0409050601030308060f0f0f0907180e09150705160206090607080912010506010c0308060319050f010b06160204090c 76
    0x207a4407803000c0c2c4420500c514001c20b01e402480c040440d6003201c00c00540040b4541035407504000c0b2500207070001d152031346a407102e00300f03250f052180b40c900600074208034071300800b8503d803406031000c0c80e40200045100c0746e843e9024107480e4480c940e15034001900303421008402c406d8456824070011405480001d106815583e00c51409000781c00580115100400300805403600c00003d0401d1201541c5112482c000200810b80072070302d130964144565110400558481d225120100404885901d011005070f9070b040c3c4030100d05019a03c418071030040300a82880c01664003580c500850040d502c9620307202512000058079109580e049034004d000300403512184d5100d201500d50503000e5840ca650321405407080000d15172400070848021f074140313030802c0040e80e004045400c41c80e40501b40042160b44000c0042e042c919400c083d11501d01100404106000d00000c2e40d8905209007002000090341a00030400940100d0741c0b00d0b0300c5c0010f0601d0400042c01d09811141146119220841185840300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 634483767 1250 634482517 634482539
    0x1110705011b05060c1210060507030e18010f05011106060a0509091606030204080c040b03101e0906021201080c15180d11031603020d020d151a040e24060a 68
    0x140305c1c081c0102000c030311403404c03c0c40b6901151b0081452400500400c0c03a041c0301410b41c2c0903401010b001d2001185001e0415111144034442040703c0390494502503842d01c0314011000c1c0907001d414002003091b890400c200a0000310385024880003421404080d2414003088040180180f00346154001d0072403402030000c446021002074042d985001d6161070030070703031912315018001c0c3c4094032680c20050080450385001c220150352003400100032036003c42d08001c00e542c03280700008180a0504e0110b10344103010716580a8052103800000c00384890b6a01c900555641d80030300c05456104040882000a005400340104450411034082c032484400682c00200100021801070310074003201034410019190a010410742c0ca8540e074014524a030554022038800140708600034007460407c01e54000b4046810500c861807007245009124400800120f0145942d030244100c0c0a43e09101c40550444004900aa009030450724501c00c044c1d0f00e0503c015440f00090440358001d0700d00400400d11405c2d030303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 634485017 1250 634483767 634483771
    0xb070f0f031707020d140a030b130501090e060405060a23070e191a09010509151309090b0a1d16030b01090b0102030703030c030f1409060601110705011b0506 69
    0x1d49031406101140e8100c0c1e40ca1010060410045405c8103607100c0c14560440b51000400a0440381c0039280e00e40d41000f903006241610b003495002d0310306190080c402056420682c103940b0b4250040c4111881503402740da80e4031046d103004000b07400c01000207079088191b034024911096440240004100804000a44002c040c4c0b070140c0050914840e041c9107042041c00c10482c1d0302c0025034100e96500d01051000c5100c660280b070f59054000040c4048903a100e8000ea40381842d006200f06a80d040d1091301e03541c076030320000061000a0007100d00190003c5244150403540e034206058618075038810319842c006003548421800707040c04100d49004104001c1048080705001c0703401c161301c030604505011174880300580c40880402e00f0f02c104880a07980c04000d46075155410308021a601c0c4039440258090003e4880c4076580d1481c1c01340c480c2810a032040c0b801d00440310242601c01940f0360100440d0785078004a02c101559021850811055100d01c000361801f0050340001840074076290390ba42e0410b501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 634486267 1250 634485017 634485023
    0xd062903011512020a120c020d09031707050105131101030b1509040f020a2d1e120213060e101d150304050c0a12020306280c11070b130b070f0f 63
    0x12000c4221b19121203200d20001000703140000d05805900000091501640d4007004003144100d8242c0c684041d040c205807415154020028011490b02701c1c450042d1084600003910303e80814001500154005d03c54004041c00161403e641b81e0500d80c800201d0b5071040308544d170480d84e500041080c0a5181c8044c000717032071160355030801001314820041c002c0b2180c544641d03584001000540070640e04000314280346108400300d000c82090f043d0040e504020001c0000e4012400083d606015401ea402180203039051511000c1086030400d083c449a42820f400e0440400c150800c06034283c800710418195000004140e00c55259500282d00b02e1900140e500710b40070f80c005000b4807094a0006124009460822000442d00c8065000207070307282006040007000344e8107114818101e0308030481241c802c1070071780c0045c071040b041424004c10a4000e071216002030300404502190301d041070340840700c0b2401e401007814815800e04201d0890790784000401c44a03203010015000c0000c2c00c03100c50000d5540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 634487517 1250 634486267 634486277
    0xc032404050405011e0203010509071103040306150509010b0c0a140102071a0a0c0c0b0c0a14070b040b09030403021807230a0e010c12030c140d062903011512020a 71
    0x480040001001d4031703210803540805006000510003516076600c4641d00c90b46a2501004c000c04601580d4158811500081c0c01070b800c101032200b00900200056045400542d440380050f070361403040030444c0c080c0d0141d070aa26009101b400001c01d044103121304401414000051030900346e60380c2c81e010303000010608443d01c0001c0082041204443c0711380d0302600441d00344285401400d40e00c20070041001040707440b0324000800d030400c00c6486051300c4061041c220790040c0d82c030685428480340d001e100303e40490340c145a01c400160070307031400320a42d000c403540074111035160a08019a03005103c0c006084c10100907001910208200b02c101030700140b09400380c002540d4801c13a11000707103680d40c000341c60ba050000d281c0c004800205100c203080c050780c0141c0360001d01d0a00d0440c1c12189601540300a107000c3e1300200d00b200d00c41d03000340e20540895504000c0a1000040d000c2240804004d0082c0141200018001000b0070756046c584500340074120b1801104500083c4444000c03178001c0e00e80040018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 634488767 1250 634487517 634487531
    0x1002030c1005090115080703030503090a02090a020c0105150607080d02090613030c051009261e0105100305060712090507230f0a091806060905100603050c03240405040501 75
    0x10f503081c481c00f0a40940c0c010001d02250a0808183d81c1700340902c070003400c120001001905090043c40007110745a80182118064107207442c0d403901a41050350001d40039403a01001c81e0703500c4841c1c0c1d88000c0700c2401501081c1001010348450882b500310b4140b01030101d80070805501160780380b0000789003c141e00e42d80c14400c1401c5003003100401d8895005103006800b04148208000d4001012400b15080240c0158030381d14190440b020b039020609041c0950f02c070f81f8403c903013108031042030500d114444030020441079a80c1c0503420403090152001500d95001071340450071240c8503014500f6808100c440110307080b00e040d940c16240c06655400302c18647d40c20010b03003103c1190b003d007010002c1811610702c07060340c40c0d840002e4130242c0184500350030039940340c503000002c01190494043c0c41750441d10030894143d0314980c0f41c1c0901305c12548601e03003560340000401c040d4000c0c0302d854080e0419001d510b045550b5004031146030206221582200c40107408440455600c034040c061042e80700e9030002c40d0700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 634490017 1250 634488767 634488781
    0x206010e0903160f030e0a0b03150121050402030f0a0b01090c020105240307170f0d0c03080a05100909050d0e15030f06190801061509030b04021002030c1005 69
    0x41038094800000c50b00304002e0300e804100074582d0310341d81c20b41101002c03855201e00e140503a8240e05190010b81c00410252000801d0042e03c00034600c20114540d18101001c4440c004484250402e903013941c0c00000c001c03484505511030750103198014405001c4400c08030310800598078040507810100c40f10000240180154849401035070421a2540003e000da0f0800c0b00840ca00d80e4010381c4446920841e108401c23409a0341041070348014001c50641201080c100b456080e125a00b06400e09498410308507500a0188136201d003c00480d019595211151a1030380d0030030103850040d1200009512002000c0b4039211580b1940c20964411001000e418012040143c0010200210544920a4503901e82d01c145681b4040300c1d4400301c90501c2c1105640c4840009000c00f01400b08821080c0d984103001c100340748158484810364281401248641004100403200b6010038040280011405004240113052021001c284411540152810300300c50036000c84c5408000105100c060361550280410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 634491267 1250 634490017 634490039
    0x10021306080c0a0c050102270f1503011e031707020307050316060e0a080d020a0b0124050c150a1e02130501050c070b04030606030209060d050c0105091c03020601 71
    0xa14050401025a2819201840280c000c154019044c0070400040d00d017080300c294101c41c8204650000d40754800d22221441d4100003001102500601080505240078500400403000341c1d4844581c452450b800d04445030003524042040ea0080100e6600c040002044220410203a0001c0ca04154892040c0d004041c0f03460141c0c1e008502079007000403490701106d84120790605403284c5060540a4818810104034606aa64014000c6004100080700b4065010409080b442d0007203180070550303600c680c070f41e54040d020426020127130000122060740481c0510040c099130700d2814165003050140e200c4e082c040c000100d480c0c2103016518180e0600650a20404c1c1201000c00c5c0c00440c10017100901c0d2b0408900c86003c1c2d58148a4085035090110604200080240010654854489a0b030340b60000140c582400100c1c81140d107a0f0000700036040c000100810190860000d10700140000e00544082e4045840c1642165040000701c0e1154404010000302c1031203075000b402d1543c5040c2c01da5071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 634492517 1250 634491267 634491269
    0x5040308150a05030606010e2403010e070503070203070b071b050303100b16060b0a0b07110f0d0309090f0f0504080a030b01080103171303150b15040b0313080c100213 73
    0x8442e040240301440342d80c40015aa0f070b84a002801c083e6000608040024130412480300c075004d10100c42103421a203a540c100c0651b04a0300788042000d0f407912000e80580b41c50008842c0100181d100744034042c08207a020722459042216403d01c1c01c0ea071078000c070b0b80c01c220880314101030340c0ca40d1001003840a004202c501c0003004015843d221410800c1c0e004050030000080700000c5c1c034643e129000301150b540c60070440401030031511a003d665286c1441e040300d00c101400907040c0302e03080144600c00d0390305200300700100d4250f040d521840480d0502080c0002002c04541c0054640d5840a440007010043c0c803419005a000b0300d0020b494020647d40141600c65000040d810040200700410001b40d000031100710150a54000319201c0803421030503071904580d984003500002c4900d81c005035901491b4031201c1d6007403042d51004000301c00002e032141c0c3c80c821441030411070701c2c04000007240342400044034144140b01d0401d0624109001c0001e914000ba0109040343c061f900003103c180410201da0004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 634493767 1250 634492517 634492519
    0x31b0f0e012a051c0905040614060307231b0d05040305070e04150501060c020139051212070e03011a040c090806010605070212070503060112050f010504030815 70
    0x70b0006044000d803549426a0100c14504003101d1001420801c182802007485502c10322040a04038032a00c0001811510607101d1a07020f2450301c8008180703103000d049411382e0081c016050318650744031280e040341e81c51180c04500c8081c0030300d02c000100075200d0b48028625156855980b541c8280c01281c000d040420300c0d00504107104042004100050010842c401201d802c100400c05a980d1400c0c000704150544140b44901441c00f000894000d8000c103031072280d14000c3e648e0415005154240780c554000c030065503503643d030322408c128805043c40800d05085a21400565082035000c503101c041d1500300142e0400e5002056041089042d40071a4241310140120000c1c0400081030024001c081c0807101924041c0d074580d412031500d103003d0034030340340100b0101046a03a25a51800001e01c0c1da04010700403031149081d1210140c101d0704c001104005d5800c001c001d80038503441c3c02000000d1400c051821141030080c0414822103000030b1040c00e10a178041e03200d0010790f151102e151190000c4d20020a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 634495017 1250 634493767 634493777
    0x10c1107051c03051c0f050906090c0d08040803030a0c02061321030902090103080408010b03010e060121141b0915090c04050607060c02210a0f031b0f0e01 68
    0x20400d0342d5408100845082041030012010011410110f4043c45100d0000c0b81180ba2101800002c01107540b040580e01d080410801c229201c000c841615050290b440006c40c1c1d2040c500d0368040c0c81d0040c0c0050a240c410f07080e4a2401365100d14060554100701d519803072950313640c662120000d80500c00a0391200851a00700c141d41d800ba03a98198546032008502c032007664008010020a001e41d21111310280c00801074031113580e5906c2c0065940d8440d019654081d424a00d12052a040500540c0c10301702400014146c50380c03c2441c1d00000f04440c2213008040c02600c3e00c201c0104907901034801c0e00c1c0d182c0c000905480d4400e12104840580c5050f4ad050290000b030040085ea648050017988d191001100c2103c040d803030f070741c4c0001100d00454000540c0b0410025a5104000507580030390b180c0c801c95001e40b4184120f208409901c41c40380040140300703040410002c40803c6c030030307500032600546504000403000508051048801c003680c0b82d03880400c2140249600080d004178120b41c800d5424600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 634496267 1250 634495017 634495019
    0x6080609090d051b150108100207020f040b01020102210906010f260127060612020a0b0901031506080414070b0f0c070909030504031707020906010f020f0609010c1107 73
    0x2001d5aa8007925451408220020031100d04600803944542c0950100a088031507403c40e10b91400e035070f60760a20541c1c3c003a20503c42c44590b846018002d451200c0d40045c9401481c00ea50014000507280951480f0b0440d54200a0700c0e03030a2201108180c00410311040e50115850000400381ca0240180c1181c41d0345040b55004000c0c10707521100860b1001000880c1900100800400e54050464812200320301480458200c40001c6000c0d20a5900760040341c0902030541e0b2aa004400704e840308034041c0d0040d14951080c45041c03400d00c001d0940c00010b00d00000c15500d060101c0380b291840b6008600060600c10510041c03005020a9807900d0251070040c240041c81d08500c10580d105011801c00d8080c0301080d400d14000043c0071300001051750f210306004811961500610760742c0325010858130407401404031510b030060442a10026640900000c8141d00c03800010f4801306002e03c1d103c2c007107216103541d10182813001c0c8203040c040c20a040022031495003030b16001c1c250410001c40340d402079012500c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 634497517 1250 634496267 634496281
    0xf040c14062b051614070302060105100c0605010b040602010b101e02010603050d05041508090a02063603010f050c030703110f0304080d0f15050f0111150106080609 72
    0x402c07200d0080d1029540d003a260030406012404001c644a4141007618200401504500c04040e6603810301055840030071005d090402101c41d4003400c40c0c0034005900802c01804a03003480c00d010390b541c0c035040c03d100b4a180c07041d542d0481520303426040032030400000300b01080000e0302400b59011514084491600d024503200004090640e10f04d0b0ba150014200010860064000e5100b9409190880e00383c84017256298005425070384507203d03440000b2038611707a6131800e5108051142c00380000c1400703050900c0468080103800d8002c0070783e94904440c01c961060030310b481210301070503042a01100300103443c0400b0416007100c1e8804880d0125070b08102c10811381009040803294410064100012207501140d1001483d02a512025005d0b140c00001d00c006e000c883c80c050410b15500c0c250030b100004032004482c003034800c50616003049411021081c01710b860039011003406008185401561a17102c8880300d0f1511600c880d0340201d024001d070040c45500d034807848140d17104070141d450704842d0034041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 634498767 1250 634497517 634497529
    0x919031e030b13180c091406090114100504091b09050406080715030e0a150f1802120c10031e060521070e340c02090a0605090f040c14 59
    0x8840c10783e40940d241c40c090790140044030294040381d00004049401c4e6101c0c01c0c140c0042416200410594501200040c018613040b10218141c480015200ea4030b21600303801e001260800311440c10510005200100f4140d07034900c19002a81202000e107a90460a01009003510041e90060f83c015810718605100b41e150004698048600a80d8603060b8544280d40071001801498030300c00060007512410f0302402041921450345403a015010001c1d0842c01c6a0103040310301c0745060400268602d94490050b1030b110b00c01c600c0080000c02500c1c03c82c0d01500c00103403844081c0c130484000c6a07030340c40e10384054440440a910f0101800c078041001d9420f000004c1c4100da1082c0311041c6421060000c2e082c4030728188030103002800460360399041824148880c460080c400b004c00e80c8250803481d007014200200e4004100c01180540341c07000c60700499024040714060041807a41d2580c1c86e1080054141c50317526035140f01710010b07102c55001d400c003442c01e4800304840b07174080c564204600b0640c540994883e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 634500017 1250 634498767 634498789
    0x110106080706050d020f0c030a08060f0109150309050f030c010f0c0903080f09040501060e1e1005071e060b0901060819090f021201020306010e0303041802030919031e030b 75
    0x900f459900c2d076030850007200c0648208080070702c41190100d508068458000003404c0b106d251601c07800002c2d5218002c0c080c18080b9064442c1c00202d02d842d040108890116120803888680d1401140c0f00500d03441c0c0610b0041000b03c0340ca003e03880003a41540d80c2200703101c0c560500110701400c2c09011480d010007000c6440351701015241c188000f81081051244804845501d28042c206010355a5a81e42c05001613440807a4203000310122190f10070716914098904849150040003000440b2460070215103d4111420884086181c090001e02c14849054810001881800c011889140740c03c107001e5460410307803040d4244004d550503c0080e00c207002102e6205401c1e0740c0009840070070743c24158518120000c01070741040701441c966002da001900258480d50081e260003529084443c1030566a20842c41380c0c14000038440b480321012092034000310740010302e180861700c101c1c541c50103041c20b030804498101c0120345072110040d003600d41ca4280c0032001c02d4605003008010300d0000898088680 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 634501267 1250 634500017 634500029
    0x10110a1b060e1509010810240801050d0f08030901020405030a15060605180f04140a050a060b0406080c0a021f09030201110403050c0f0316030b0402122a0604030f0803071101060807 79
    0x9440014102d951040724040c020040d100300c0c400d59180c1d230203800007002040b294902c0082c66003400440c1c0d40c24804650100c2540c8072084802c5d001041d01da00016401c042d02981282d5020840000d1580d0204004881540a81009a001540b000441d0202c0d1865403140d02400010300403032072a52801c0c0444000084195505444100b1480c0041c00509462081011180560082c0030035124541d20540c400c07003000404100003a183d4985200078012032080c0c1d40003c808900003840310302e10703070081e24103200c03140100d9103000401407290060980000c01303407100329540c5898205045c1d0901940c4110380400e00002d244c542907850f400d4445200b203000e107000300e88940030046a610200003081546000154400b021038070f900d81981c40030701c10344040e4410441c9009140c2c2c64100407940c41c582c0103c11b500f004040d25003520402c1c4c80c01d04079020030351212092000102040011108002d840c0c4601d1400f07680740382c1104060003034403180034054001e0385010002e20000754000740789400d90740 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 634502517 1250 634501267 634501277
    0x10060e1c02011e12320a150806040c08030301142404121203090c061d040501060c030806030102030f040212210408061f06140408100b011d10110a1b060e150901 70
    0x1b540c2e811030300143c400900e40c00720280c0d8003400014245030103d144c0303004500c00c018003610349660b041241e50720301081c020700d001e60f8503100710001039241200084c81e9041c0c0c0a11201e8610180a00148858210380c2c8000fa8109101c00b9107000c019504a50720304d01c0c410f40c1420040111710f0b4507074402202c0180a4003090100d103c0305000c0d450b668414002e10450020424821503071520002042c40c070031014201d000c2028000400c40614060080d0ba00c0b039403900f0383c003141543d16a0200700c0360182a07244010300c1e0048110b0b160540012010854254100240141e5628a0005900e01c1c1100091003040081811608612821000c4148a040340c0d403921b00310341c6901e021296032040f4480c0d94402a800d102e000d21002d00405a030700808042c11090320f030422840f105404081d004003a800b042035101717005510aa40c8903000f0084411007445a4040b200401419980c210b22409008000c0c5850050039004010b0107902080c503c0c04d858042d0f8200c40758a10010a043d401e004110308103040c40703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 634503767 1250 634502517 634502521
    0x120a110f180c0d0c1407110604030c0b040e01080c090606220326070f121b15050c0a0c021c170310060e1c02011e1232 52
    0x264800300c1919091200641c8100d182c00c020660304441d90001d401d0038040e80c00c0c0020340584d60b00070910401401d07207100c10b0900d050526a10040e0040180340c4480d8403901c1803002102080486000c030000d85460300344903507070b18140b50860510081c1640060515880041490f100781c94910702c46400c003d0a813100354440c015031804040d0000e10002c2d501016142c2c1c07900100348202c440090302ca02c0402485407400c0c10001c03038003c1c510b21518401038a18a42c0c1d5103101d001945034814402a1403ca19005540312002d00e00e842e00c0343e105a0083d204122003c1110f041d03e01079128880e00100320745903143c5081c88401c0082c0c814608200080c2c414940e108650180e070403068484018150701154141801003e01a0781c0c400340c00c151554280c4000f03117203001c203a0b44d014600960548000820300311200c45184c40e00003560000c803500324104484c4403010205407100d02c041040381c0d56661210048a00c00060075001c48441030004501e440c030f502e88490007442a816a100c0400d1a90790301c441c0c40d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 634505017 1250 634503767 634503769
    0x501050310111b150610020d1d04060909050706020601050a23040c0909050c030105090c0d0f020c0d030b090c0a0c0f15050f0a06032315100302120a110f 67
    0x7501480b22080320300034801140c2031480303002160016500895443c0c0104680b9085c05114126440c04407100c0507902045000318118041c0c0c0d00587c410a2030403140001001c0107020070300381c0707103e544201c0b81c1c80e4983c0030310400c011003400b07014081c1c802d41c401000d0561400d00051b12480c0359124501d070b481498010340c8241c040361540e04040b840f000e0400c0c0200c100c2d00c03200900d45541407041080d0503140601203145030b0036400850341203901c000c0980c0c80d281c4504460842690000034001080340d40d4004031003a01c051400a001c4000303040b00584a8100304070f001509444180d02d200c2d100e060782408200101030000182d407906007040c5040000000c070391420f94590105040c02034040d81119080039030f4800300790001071150264032114081034542da040301c02075510902004103140c20300c0c0c04102100030250b1449664039554030441e011400100d1103160195400d0307800281c445a000018025420300d403155107e1a00c2c0c00e0300824011210380c0340c03d4121032234640b210788581148550103c039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 634506267 1250 634505017 634505051
    0x1a0c0f2116020604120510093804030f12020405060f0322050304060e01020d1d15190e0126130819030b1c0b09070b030c0c010f0501050310 61
    0x4050380c0605081d40d2285c071100c0034402506060000c4450703100d4060201d190001034018040030035442a103030801d10145807a0622880140000c188580381d40003022070725070b080701c54014000c074081d4442c0e9000e1100d09074000c00c0c20a080e10203103042070040004000e1a29800d044803021070200c0c0e40161661901136180c880b160126442125582d030b598464814464044001c00480e0401d48440c40d40011490069031219481d1680001240c40d400c44061049000095905c80110003000c48101c0441c2034000b0010ba00b042034080d800e048002c03e41007080da0401590510303d4000d08221403904a1304610b04014086926541c0904024401081c01500c0007002d000440d0f5000a01a0b1a110784140c5e02c176003054030a121000090421103c2001410f104410364801c09104440d42034a0406898810b45c4610140c0070850740c1c4210000058660b40307000203036005000c036140c40d43e80e403c2d45000d40d5080d0f91514013014152494400100100d80d4006000c0403403403501d400200d04081e8074400030b01e03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 634507517 1250 634506267 634506307
    0x30807020d09031b050a150219030c0219050402130503010606090e01140118030308150108010b04050405090a1e051203150409030210150e0f160809071a0c0f21 70
    0x1410100c03040020500050000940c1c7c40e500d41c540c2260019070344994164803d6111841c040c000c5282404001c0141c10000b01c40d070350380307618001c01e10711403036817803010400701e0b480520301120080f801d010500c101c2c5002e02400740140203600c0c4c442c45150800800d4003041e00107218101300000e444514078016401303103840c0b0280040001c0ca60b01c14550300c0c14003401009007102d1742c00226001d003e035030b0465030084500d6410b9030300c40d40e00c6c5410310f410101440000d003009000134200d489030006000001d090340c1141ea103410400d20134041005c0041c50401e262012404040c000f0f608107104004210300340300e9061284c80f104031800b00f413030111403c0c03d90401700c51624910303040341001e0016446105048000b012640c019201401640c2d601c3d64400d282e0000340c2d110b0444070703c0490312701c1009210b85071803500070040d1801ea80201d0313650b406401a0030304080200c0580345001c1441d188401080c0186030310300c1c445030040c00c82c1d0b4507440300308850b0b25401c01d440400008040f40286910903c044e20745 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 634508767 1250 634507517 634507519
    0xe0f191407030914010c050d02090d020901082404050606010309020f0a0906060e010201020c0712140109050601051c03090b22170f03390a0b04030807020d09031b05 72
    0x4105410501c1c00200a404110720944106035820407101c24a08144212800100350780d0301c040c205040030001d80d02179400f2030141644201e02000707210250350390f09030003802000100c00900e50703942854a6403800c500e0921105440011034000c00003c00c0c1d021400740da00c00024a4000b4030702c80c9601c00984c020a01e02041500503948620206413050240d2042e8103070b4207140c072041c00c2150756200490903071040001c4044a82c010640c20800300c002c509880030103900c50094007007807410401c202c03400c4920240c07054440740e10210041107117041140803001444148003940250f0340c104d0324060124001d074400c6041c2c841c2c0005044002c020000600403042190341c14401103176a50311075420755409c8001100c00c5601a25000041000c00001122028218000801c20105401d0031240012558012881d4a00c02078040343c40c82a0092200000711482440003c40314101820b00801b107940041000d0f055610010701072110340d801207852412a54491020f541100304e50b484200803602541c022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 634510017 1250 634508767 634508801
    0x1a18040c050f0406230f121005070917010f1409150a380307081504020409170d05401205030403080a05060d11010309051f060e0f19 58
    0x719510a14032080b110f26030904582d2a40c0c1c0124046c10000000044004a2040d07403218051603011803058100b264010b1035418003420039940c4250f408105401181a5011650340304509401c040b40b51082400080c104c0c01f0858080c5800380500da684c1b039500940b800c0d403504690001e442030a00350817900c0641ca02e01520796250900501c03008281121804a030300406c0031940c81301a604001a4100483d0121002071000c180d60501000034080d0151081e41c001c1d1720344111002083e104802c40703030700a200d240d00641d21442005401c003110005032441d01210041e20012204100e015210f00c036203401d9480b0048607901e00f5034035a000340c50b000320083c65101c0c0644c407800d0103078200d0080c1d40705a009464039000c0e6507401542c00c0413110100d031604e42c0310550b100104041100303004000c2d000d100604001039070f2555a1219883d2070052000c1c102c0e26003008002a00086a82c065103009008140d03503402941400091090700300740060800c00d04020039128801200d440f9080307070511100c0e031416 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 634511267 1250 634510017 634510049
    0x507150204080a1502120402010c030507020d030f0305151003021812010608120415050c0f062401080f0c03060303040e010605181c03080702030c011a18040c050f0406 73
    0x107940355510504141c0c1c503c1c0f044c400c14480e48510b03008442141c41c640d481c2c1111075031180e00641e04c0710603545c01170b02044811f00c8414016140d00c1c3c1d00035661402a11451941200e0140c010203031007000b4011003201600969809113901c80500059070454181005038560200841e1b0754111110009401c1d84201c01d01d0400b81c0f188010352003641525518401d40e4800307081603906541d43d22440c41a01442000c000700c207501a0700c154050700300c4100d01c4081e80e1200e4509006a0b10300481035900c2c1071560140c54565107690038807050400030030b03402e0078042d016142450400780d0003800140300d0340305040c00000140c0d441c1e070280221000381645000c49040381d40c50f000001d000b90044030152454000743d03075500c800792501d5484600f4611285040c403d00038019501101e0482014062070254441440200c4502e0020301885440002031015a0308500700c85040190102d0400109044500c0341014080440c00a103041c07410780e02d0513a0038060000402d030104004021b1580001001e00c2c0503d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 634512517 1250 634511267 634511279
    0x6030e0f01090b0103050606090c03070c0201140703110c0415150e06040303080703060905090d0f0201020c1905101e0b030709050711011a0d0f05120307020a150612030507150204 78
    0x307205060717070701610441b81e80c1ea40d5481449110388e42503a641011080034000a00211300c00d18040b1701040c07043c5491030080b14640c00030300711504003039800c8001c80c007120202440814200708103443c501040740d00b441044c91030b01004600502901401d100e20388000c1c1c0341e00d6207500030360401d6103498000d02160303550f42e0303a4207004003141020b031030f0640007a003080c00c00100c41c20540902e600803207403680540441c003030328031040d1104603607084000e09554090007014030710350b001c0c8451b24140d5a044207000c0350100754500103081004d0b2541c030b003212500d09820701045045031040031503d8035801000240c68910440041d00d040d0099100d0101b56090000f040022540410454524203925009014528190341c02c081641c02d013041e0036400c605100106030100da4006140c80041d0f0289042d00e100c10306110b0740a005600440d014400359000805034406c21403083c170958828242c040c41008502c0c09c0503603224511869a102900b044408200300f824400c2c10a10040100c1ca0380c0c004641c1c0765500c1b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 634513767 1250 634512517 634512533
    0x3030403030f0207140a0620030409021b030c060c0d0e10020403021c0803072d0c1407060819020c070920040e0604020703110336010906030e0f0109 65
    0x100c5502c0041c011240005566290340310b0150701160010700486803141820412514502e686405c4518094101d020125005080c0001c0002e03000780c3d640980d0300c078102c00082850955810108025910401c2a482d0342032000c00c40039040903004440c1540d81c0c1c007143c66100600103021901c0460b0242c010a42103010b9640d0042c03080303134802e560a9240b02c907650f26001070318450f040c001c2c010540c10800030345081d124503074009584e540c6004000340361325507103110072a07140d00d028501b001c0b44048450506001a003110b1501b406248802851400d05020009005410142c260503084002d49460315081c0241d03015070740704400c1f85080702c0f94159030764128805006d505149e951015030b17a0052900400c0760004903002c2d203800c1124400e0b503031a20380c184402940006016403c00c000341145050f03451040c4002c05180410b104451010039214028400a020f848040602e501c51a004c0c11000d9812003450310441c0c400f82000240581c0c0004070ba4180548051071138025480c24800c0000c04c01c0503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 634515017 1250 634513767 634513787
    0xa0e0f0601060206150603040b0f131a0f0c0309032a061e0a0c050319060e100302030c18070e03070b0a03060f090605150913140402030d03022a07050303040303 70
    0x1311860081122102d41030001b603110540c0c020303040c0041c480015050b071030015401a0424004280205000002c0c1c8500d00100343c90010010519100c03000c2c050444a11038990703400075143c003500e0b031131401d150f105942d0700c1c803c003190b1f490648080f401007010b45c1841c202000116406105885542c40c001c4071221840484500001100803d10003249841105104504a119a0b5240c10b880d60321a40340071a001104010805003003521850007069074491081a18010b14000c00450145410f43c41003500301501a1625030003482000203034001041118501c40c3c02109038104035080302c0000f00403030b0400515800140720a000000d010700c0d81c3c2da26601c040700721141001c8010085031600710200c01c0e40e0035440f0b103e50143e95080f0420b10010344030018541480c0050074101586580d0000c0d83c1035400f901500195001c00004010030341c01d0500c8441c40c0c1c04003614003149041e2107a00c401003107125003444200e0100b194a140e06501d001001a4006031400030201c03a00c0319520701e4010204294 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 634516267 1250 634515017 634515031
    0x2030a0c020610030f0602040b0c030a03060e0609010315110301080c040b03010c02030406050f12040f02030d0c0803190209040f06061407020102030d0b0f120102041a070b0a0e0f0601060206 83
    0x90491103114040c80440c086008244541060305818916241c1200300c510254054172125803c020020b10b00d8500402030103110800b4004d15144c070041c2502600312241c07540440d03194002c0e0001c100c2107550f10ba181c541540d61009000124a4090748542e0040504450320b4980d8a0000000300e4500000545545022411501842103980c42c0d411f25080e1440e0360b90700c501590003480140700700360051025000845005000c3c90608a03000c5800850480a031800d41700500c202c00e110701542020b01c0510002142402c22000914881e901d4106510000f801401c0600c602c07500c1d1408200150112044280d00410030b002e54281c0c0d01402005200c180308000114240d408081940755440041c0c0340d03413075016000345088c2000390740400c0c060840b50740000c0d0321421f0001c0c948442d44c2c44030810031034140040c00051721135050012000250b400741c0038100708148140002000206c00f0f401090344400c107040702003001040141810f18203d044240b010301c0b40a0320700081106640000c940b03115803c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 634517517 1250 634516267 634516271
    0x100513060b0301032414010e07030c020d0e03010f1a1f080f07090b1201150903020f06070309051e0405010509091b0312120a060807050109060309061407020102030a 72
    0x8841500300d510622032040d0764441480100042940411030480014280d04849101c80c0b03c581400b00310f810005540030b610110300c0040c000240c40b003441940c803102a0030304211030102d0150103960b400d1040f84e2101003005c0802c0c07242041c0c60a4200a6500e00b285805000c400103010b103401c28120004c0c412401400c0e4110a181b02c8031041065480560580d1541a05500e42c0600980310302d00c028036041c103001c04403000182180b1140010318001c02c40440c2100702c0d50509004180c01014110140c0c100882d1140a002594684105101e03001c8119201035030b4202c1c0303140580da8013030301c1e17800301e94009035507030340e0701080c0b2003801c2078408040044031f08200a0b84c03100c080019458041e528900c4d80c0d40711a0054520b11034000f9441e0000500400310742c2c0315840d0724401c42440d840601c805d0010201131041c003050380903500510b006020382d88041c0442c10f0824000030002c1140340704160825450f400268280032140c1d01030108400a0840f520491a0086020303000c4d510654810b10098 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 634518767 1250 634517517 634517539
    0x4140d020109060b190b031f0b03061206071b15020a050c060609010b04170f0f21030105012106090f061e05030d050c0f03070c03031704031e050d051005 67
    0x450280030b02e034051081150160350785d0342000303041466a0401014a04080c1d0148000141d003001e02c08000020001e501c01140e80345030100510424016228418503564012010301036215000307a22142005207148106402ca011401d0004103000f0400b115800d00d0b00c0040c0382c03115140d02100601e0400564012501d45031110b800384000701109108890701040140010f010003a00c028001c440407100b58202c0c1ca6141681031654107080c0e61041e001c109900c001c80070000e40c1400c0b40464a0301040c0922942998540400078100150004100941c01e09401042d5050a0141c0c40316000e0700c503e40c1c0410a0780b03160780c0740310000e08240c0110700500e0075011201082c00c02c5082d211b800d441d00035001d4101220150710a45c0c258100300001c00c0c06008041c1c0c00300e0352040400150500601486840c01c07000c0ca1810050240c4072540c0101600310484004c01000c03a03007201a510400f240900101041d000010044401e070084416515407542000c051117180c0b0039403019202669021107000c6c0700c00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 634520017 1250 634518767 634518769
    0x504030f1b140a0902070302010e0601090e0c1f03050720010f0b030102160b06031207110a0602151b040b2106010203071e03031512030e06071a04140d020109060b 71
    0x20b030042e0342c0c0c2c1c2e44120b540b94180725003070300e0f600030300f954910a00000c120110040c0b02c450401509030400c4d01820740e2415580000d0b40204028001d45000f03482d84003048107030b1001c4048000501e03d1160070b058030383c008a013103544600c406201c1c920107410808401c500380a8043d0280c603991280c1c190a074282101c40c240c0e850103100316243c18525480c0203c580720103a50b0382000c0c2d10f0081c03840768140565003070044e400309000024821107102d04100700c0705d080300034208081700c01d103500442c0440d4048141100c4000d058030b20035800000508049800102e16154045144a241c210129444000c26150303a144c1c4111515000c00003400d21034441d03695540012179030380c092001e0162650134081c042e4080150f10f040421050350007864049031200c5c8000024240c51140e0b403098002d00980d405882c1811342c054075480001a08680261600307605844440307007a902800481c268410007c013082c01c2080c2d40c0c80140301501c41c0740c00d44240c0d00c0c0000d006402001c402d001a1039840c28818001d0305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 634521267 1250 634520017 634520039
    0x60315060f010309080d020403030215010b0301050904063207020d0f09030b061203040b07030f0e0d12110106120302070503012a0905060f09010e180a0902010504030f1b 74
    0x1240901502850150403101c0044020b840010804c4e5810a41002080c80c4244240010030103940a500180b2000a01d243d030075140380c1c8160301401000f00c1c2800103210540d509400c00c2e82040d0049000310f403095804141030041807101c8110b482e4650300e4240c0f200a46961680e8503c01ca2842c0c0a03240d50320740380c1503f540e042d02a141908001203990006000081030050b801c0e40040c0090001c5c2d2600f0900c00215141d98095005a41030314004520362040661104004900001e14a0003c0d080384c0c0450110b02c0c0900d403110028001c101140a81c054a48614402284141ca0b44020b0080300d6a0740150300c03040408030701c00c0d40103000c0d8410200300ca080502071002c18280c42a034550080266036480005c0c50304d140f01680401038035003400034540da070300409030000b00004c00f0626030340c0040ca8005429550701c01202030151a1049035401d2040c621011180e201709030340d10105946a151004aa20380f00300d03080100060351814201007407029518402540180c0055800300190b112030400d10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 634522517 1250 634521267 634521271
    0x23100305011413061a0403121805010e0409150203010513110919080307050d1b030801050603151c0b0907150e0604030b0a1b0509010203092412060315 66
    0x707591010340c03441d00c0b82c5040c840101d5803000640c00c07000411644901c50540d0204e1922169484441c02150070f00506c0300c960801c815440da039060000c6565001840024102024420315052011003c4400e84645880d04000c003240d6003c07225140c02800307024180002c0d0002e000b21800b4040e00020300c0b240032541d10410000c1c0c256000034600748440c42c810060740c0300c4030b01030900000380715510001d42c032002080905111880352000e8503940108641c010031548100c8460343d001d4002284c03510207e0380248469044d190705490159882e55040c054141103890140030b0340d04515021590302d038500c861038208a15612404d081d03d060b44521036415501c07005401031200264540c080309202c035006040740e840d004c2019000a061581c0c82d121001e4081c0c0495400c40160745408580d180c100c0c000340d544410b40c0c0c2c5070501500740400f000000f9034900444d00302c00c2c09030348000400c03110101d00d001203014150301000e0ba070b0358800340c1520040203d0b4090302c00798001d12a0f8064020a046c140c14168 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 634523767 1250 634522517 634522529
    0x30907060212120c0706020909090109060507140a23040e0405060a05090607030e19050d020601060203270d0203010513060b040605060d090c0312180b0c03031303092310030501 77
    0x1031003980300e22401404e04c1d849248100c485680c2040024010345030502810700ca01e81c42d000000d40000a0701b4402e090302c80042c000c00030031900401100241c50f542003629081e0355286440d0f400700000c948141e07080c1d064015000026a4041030010b8441103144500d885180304400780d840710b466100180701901c0c0d00b541c0d100d001d90890b00c0000d1400744654021001051008110b4503c107010a0103013000c0c13044150152190b40015166250b840d804011250040a1034802149071a00d40c19070410724140d042c03681c030340107000c280e0380c0300c8180d0312000203901e00c9400400802131420680c1a40340c2520000c20211585828415001c0c0c40b403070030784545000c6030700c00b815151821f10406031000c0100030841c070850701140e452101001091560320900c6000c1d02c15281d546e20300c880442201a02419030b40303c80200750007045600c80d002c0340070003666040701d079075901080c2c4115185029180d8011a4100184940c07184850030307850344810541240702c2001b555030411741803034040114140d600c24001d030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 634525017 1250 634523767 634523797
    0x1614040b07080309120d0b0f01080609012102090708011a19080403171006180305070b1b01050c030a0e0a020306060f0a0e0901020901200c0420030907060212 69
    0x20000c107a110b8001c0d0b511003d00020f40350b607020708074040c0303101d500718602c1041e14560303800e4402d1950030402c070406222102401c007000d171480d0002c00150340403c140141429812440d1042445034402e07031100040d143c0c0202006494903017544000c080341c10034403c51619901c45440d26840045e09021222189031a0b140c0140f03110074201c054135080c602800803401c004003001507808030801c04010390b00480030301e00d500000610741000140400000c8800c542040b0550b04200005800041d40030100c1d40c90304035283c0c0301c08505200c142d40c00d41c10480c2c0c5d02d10b54240000c0050350081c0d0720041d4810161440100241e0480c0003800f5590800d0202c000c0d090b9000c0804070b441352400c0f5440805801c0b00415041003213807180035100d07a0503000d8450030044da4000c80c0b0b2a100d9038000d90740d45e600b11401d00c803c000c810020b107450b41c2c1d0303800c00e80d0000b40503c0d40d0310305426155401c000882203407003060704500d07603c4c20641c40f01c56480c00984120b10050050039408041481c3c046d00700c4d0070a60807a03642d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 634526267 1250 634525017 634525027
    0xf060708040e060607060f060806010603020c100e010e0a11030610060f030509010b03030406200c060406050a021006120c1e03021c050a140d0c08071103151614040b 72
    0xc0426003540036100e40e50191003030184000280d02c6c0d0080f008100d00d11003011805070714040ea0719290080c10b8110341c0505005000303294017044001035040c00c440240401003002034407914031500425203401008841c1c003503082c42d42c042c448a080c1c205142c0c8026411901f0a6a54000b10036000200b8083c04000032134203403003c08041d100303410554001c801c1000020315181e40b100000c3c41e5034441c0d80700340c000c1558010f49411141c50401e40300c02d082500d902030b282506c405000902d9030310807809042c040c400c0104407602164030802020b508100907200070084261200d40ca4071b21091400340444114070012004204461203494480c1560405000f840e00c55007144d082140085200c40340d130440000c0300b0824404034000700b042c81d0009025980c2c82074617880d1808518203118401807601c044c0202d41e103520001a6020044600443c0c002c0c1154500c078400000190400c03000d450061001003c801c04d100c110310300e40032903400e01e0000c2e8944801d01042c81900b9412401180300704010001c05001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 634527517 1250 634526267 634526279
    0x3060f0d050c0604140f0402191b0f0c030209070c020306060111030705030a09030c06030608060105130e060c0a02010b04060503031614010f0207063e040506180f06070804 75
    0xc039a8a11620650644151884038000310700b580d0000e9000b19020024520002c01c5424105049440190150b40940c50303c600c545620107025081c240c0d02e400c212240da140e001100d08040c482c810940d101c090310134100e0311030506a9075007400c1c0c003041c0d104c1d2640001180e10b49001e000008810303540035019102d1703550741500555140c40d04d450b164a2a0004011180c00140144018403446001d919245200c0c3d0560a02074842c1d9200d070890401d140c0b401381d0900c00010001091030440d00211040806406107803000310181c502203201140c0c1d1b21880050060b0400c0d0180035244608480e8020062000c11104000a59206109003170309500200084241d00406a100404072030240d40241d40c100026491642101c0180300b483c000345034003090307001c104031503400741010208850701c05481a48000070b20004002c0e000002c040c3d00c500d480d04000300c4040c07a009840041070002d20344d1b619510754003001302107101d0f90b64400e40302d91400d06e4074030b68600d0032506880c000380d08162801d0401d4102030f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 634528767 1250 634527517 634527529
    0x30f060507030b040504151121151002060a180b040609030810030201050913060e0114090a0c021b040e1510060302072d08071a06010203090618040209090103120908010203060f 77
    0x1514043c200245205240b05520b10a55850880d01c600b49e940382034110036000b2a05100303020b2085007035065010b41540c0c0012900c0d080b818420b80041c010f210321441500714a0281d20040a550604041000b4050301d50301c02030b9943e0007929982c485542d2090482002211804000e0208100340003240c0142840002581e40400b540d80020350340d0345a94480d080c0401c264070407040052240244400b41c1080407200383c120005140c148900d81f1040c001075203a2140d000344400d01172103480992521f580b65080300c8000c0004c98141d03400d40d00e04070055240e29030308030303036628aa8904520004005210b03100b158481c1d60002c01126003400005850210040040c002003030201c0010120804954000c00402c29140700746400356031446040540b04248900405e85410b64005020301c0d54140c83c2c007002c8a00c1c1c0603a4400e40c00340c40b003c2d440001d0085c0035400d440b54012188000100800100500082031040701d40c0385c20b196640e07a292001d090780700c1100c50300e0300b00c09200c1000078982004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 634530017 1250 634528767 634528781
    0x10050915090d0b04050a03030e060403170907031502040f0b0f0418140a02091f0807212415091401111501090c020a0c1707030f060507030b04050415 65
    0x40200d80c15102c40c1d11140880042030f24140c1c4c5030b4101c05035080c10160148100702c2c031801840046d010918154802502c1101d9258402c540c5040030000606602400c0c071100c40610351001c0b18050b100e00b50080200203400134040c0030b00d211b8034403002246440d40c04040d122104040201c080c90302d400e0a004071228001c07990185842c9486800c0b03850b4605616019034401e6a40000040e100c144213420040b00d4045903000c840c1d500c9a280c80c0104281d480003619900580608005c405819044e0340d02c050150880340c440c00c59864065034802c0050004010685008440c864103045900c0d2155006201840304d0004086450404100b048005041211000450505000d94516110420f0302d04141405c000b1022450043d001484600040e200700c0b19050038a100401c00400c8650320002080410302411104013211080c40c5600368042201da40035590002c0d8580c1d4101081c80e008000c0c000664001d0082400c00b044500503040a20410f4802c1d80c0000000b00203030959001e00c4018045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 634531267 1250 634530017 634530019
    0x308060310110d02130b0319060506070c0611190f0b090607020303070c1103100b0a0b0f090d0c03140601030b16050a0c0c0b13081203042a03120203091005091509 71
    0x8505c800109048044080e51007061900e00c980300c40216050004100d840c03030381000e4450041030020002240d1703603080001c103803011414010009a1500e0f4040d203040e03501c1006041c609010160304041003404190700c4040381c031451002c5026100c420170141c030f42404031a054010317032041c0700080c040b83c8140c0c08000740358000d40350200b0dc840c00001090410300400f440c21540c64030b5100d00c005904001c00c18000810302c015000d0308002080c06031480e244500c160306403203951070201c01000d005046424070000c0d44d1080303a0414070520300e0703080c5403103050074030040d509800f51500041c07950100c41d08151a440c0039582da00d251021650041e40d0464103107005580c0341ea140000030840c801c50600901c100c4100510070400d43c0d02c0e2904091038450080041c0c80c04900500500c40091031801106088102d440c1e145580381c907260111108442050707101901020f421240500020b40100040041d6401500c1c40c800300c031a00b6a05a88074826041801d41250720300f0310b8280c03903104100103841002c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 634532374 1107 634531267 634531297
    0x1051c050601110303061e03120c0d0207140a031218081f0606050906030c0702031501090510080d12061716120b0403080910090308060310110d02 64
    0x1c0c0ca8480700d0300c111007c05200c1c103903001e01c1260607a4030301015982d100c0c0c1c031f000d12082da101c800e40700710302c0503018214010400c1031000c0344121141c007025148125203071441d40c0741600b89100303c8000003040000b0604c000b0340850b80a04030014004800149070021507140402045651110070400692070500300700700c4641c210090395400e110440780a51242d490b49100c8005110b0041c00a515010b0540c03a8800c90001c400d841d4103a51010030304000380c0e5940c03841078017420f1050007198003550000c45c0d5200f42612551003500740a001140115080307036148010710881810b500090020f8024140068000c0184903405000381060220044084003e440304111030502800150400c018080000e014500400196074400c0b00003804020940003414010544242902c50782d100c0e00844849a03684101c0c0d0140a6081440003000c6140c207101c10300340c0d80203604c6503990880c015 = true := by decide +kernel

theorem cover : BRFrame.Cov 634352517 634532374 := by
  have h0 := BRFrame.cov_init 634352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 634352517 ≤ n) (h2 : n < 634532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
