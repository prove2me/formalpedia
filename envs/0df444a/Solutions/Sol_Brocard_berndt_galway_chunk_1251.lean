-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1251
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:59:31.725648+00:00
-- url     : https://prove2.me/submissions/b15be2ab-dab9-4722-a261-e174d7b50348

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 224820143 ≤ n < 225000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 224821393 1250 224820143 224820173
    0x20c0a061b031512062a09051201020a0e1207030507060c20030d18080708060108060f07050a050f070501050a0f060605030f070e0312030a020d0e030a1e0c020d 70
    0x3003400e150054806030050818001510111407113078411000e50745508000c0c00b040c80007042c00e49540c09801221060b40c0850900002403a102c4000c0c1920348400e00040312850604200d05920500014447d541d0080d442000701004960b00d0501032078041c0c2c880d052503150313800205140f00305880011480e400203110111030f4003850700c600c0302c0031001190400b100700c060303c447e5140d08286031680d409805120048a01028610440d101d81e803204242443c059654201d801542c2c0702e4070042184d06000c12081e54000d4090100c045c96050035080035055008040482d0140003001c255000d9240303a1000751500103420000900080c102107004400410407005180710241c10900d0204109015104481c080c0f1f02c9490200d8a965541d03c08490742c64030041d40d50390600071424a981c02d0140c21001c2e50160580080042ea112552440101110142c0e1a0341002c1d4006001802c05950031480f2500c1010210703801a6820303141a1080300c2d40c2c400000001d44c054200300742c01c5c050200d05a010016 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 224822643 1250 224821393 224821397
    0x30902030f061e060f0117070306030f0b0924010302010c020103111210060f0203040311060c0a080904051003030c0212030f13090f02041212020106051519090f09020c0a061b 76
    0x954440c0800d121702c482e40818a14049074090030513080307501401c112594845100d01d8002821900c81d40c81c51201c0445003800d413018081c51007800a100014071029042c051921242e4101c00304041c8110021001444064144502c0404060a40e400380c0c0007902c1d80e0000d001c0781555501c0c5e4000364580400305803220a44110214400300d0481c0c003d18851201c0c2c1540d40055081c1440c582c3c40c10507901c030325031103190080340030f00158903401410850b00c40307030f6441980a1a100c091000c24041110401000c090051480180400209810070b241404446d01568a40d291003000f2014924502c52100e04c201d64440000e0480321110f810b9440358180c9410000c24004116081860760681c020340c095009110302091401000515282d45641c0060140c000030030710599820010b4003d40c40000190401e81000a00b9410700300c81d195006c46068240c00c181c0c40c02800c0504500950182d805010000c0d41e0018044080700702c10801c6c80701940e030002003130000c00e00400c408045000500e400d100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 224823893 1250 224822643 224822701
    0x902150a18030b04050d081b1b01020c0717010903090e071112070b0f0f0c0c0c1306031b03050c010c020315010602010212010603020724020702043e040303030902030f06 74
    0x112203071151f924580207200c03001c1c00c01070025140f1800c01e071603884036202442c0100384480c20040e80e90b003800a0000c0c01014005807071101d290003245030f01a4130003500e1880992400010100203508000c2d040b00340c4640c5104510b080c0c0e0344000a540241840181090f0341c0b00380118210079884880042905512031002907400d0b49411400318124401038a40c1c05120220074000741d4941128000f40109048003c2241c080840c0034000c2880d0301c200a81c20032005807500c0b018001c1c426401c50800d4983c00d03400c0000c82e060301d15100e1761b0300c600c03c1440182c10014113140b400107554082040b00c2c0341200c1034004584650351024040e0003544854200301c1a85900e000000c0d015001c1d10036540116080140e41110300303114840400010000c4001004256090260030007507192840744074004c1030b0601c2d00741041c030b4040c400c0c2c0b41c02420000c1e985105a01280d00c24404404940c00c0c1c804a0382d240c10086124045440000d08000440301c1c00100c600c41e603410880b01c0403030407010072101d0500064030a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 224825143 1250 224823893 224823913
    0x6020f010501120308060604180f14091509010f0203091c02070806070f110a050114060a05012109050307030c06060b0a170601020705041505030d030902150a18030b0405 74
    0x1801d941d02449101c20309506210500b012071700034502d460b40000000d09051400d500c031080d4080e14010307180f07803242603903481507441c410074241d03c2400d0ba411441d003e0340c442da180000540d5581c102004c80c200340700c40c203039021482d1200250482414480c070081c05645900d04504d085540d004030840800011198440110005002141c08000d465100c00500001d54031a9402d0b154010b840a5100c104044041c811100050a010710030031503105e280003040e245001c05042d56811006440c9070721a460b4900d00700040d0b0303003181001a485407004101d01d2244a461782c6200140181c60000e8054000040e4000405504c08584036440348209001c00c507183d101d0301802c4aa0041410b0301c0003003254841c50301c0e08546203050700c543c040c10501c100c841050715000401c00351484c01c5c3e0050f400c01d9554205000900d002e10842020022610382004070114039000901103c0000c0603050b4100f00005208130014424032480040c0d40080701c140e45001d130350f132801e1030620b0360413141912580140e24101d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 224826393 1250 224825143 224825173
    0x606041107021008090309042d0203090d0c050705090711121602010c06090c15120c0906050706020f03161d0901230424090b180a02070212070602 64
    0x1d100c410b6009040710319045100201aa01c040700900415100d2106220003c503039500c40c0a204402c2035142a000b4006440b11482c288450114a044101031300500400c800094001004d0b07008210610f800581c2c00140d081032801d108581d080340d50016858820000c2e0789404c08841c1ca44403c1c0d48088401500744908016200d0140c001c0c0300c20501034544c0540c0140d0311644044104600400d80002d82402c1a915810205055402494030825a1104282c619049166500d4500c1142020307c03184003544c000418200e541c0c0603034000c0c01401b0468606006096040e41c11040800c0d9450f59242890f420019103021000c1300d03d400252030303104806807098038411880b00c905002d4071656150342805c2d1340e070000940f840c8124210840f00c020600c50356507203000b6042440046810017200d803d49500703181499819411286815003009018890303500d5580007100036000d1000c2162030390b1a18414480030784160032001e54842c071601091141000c01148080450b0503075003c90724035240490324 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 224827643 1250 224826393 224826397
    0x190303020c15071e090b0912071502010f0e07260706021608031206040e0c1503040210050304120e120f010c03060f180903022d06011a030601030b0a1706060411 70
    0x44d00006113102e008009006050001d821220740050808150702c00c80282d60745050035682c40450f9658010246212464080c400e80361910300514003401000c00b00309106030341c2d400324403c8507141040880c0c000c440c6110b00741c00520101031101658042a5200c00080d84c0d101c0460042d0880c1241030b0000038180c0b000400ca4029000c019048069646c4400c1080024250040c1c60442c0d030040d21b00c548801c0d41c0300c0e4035028210032541045512810030f0300511400c00007241e034510038400d08006100109009006015400001d85802c00c0d103000060301040e001020f100d01900c25109280c01d06006c4038040d00508003890035690208180d540d6900d0f0704400000604c00c0c11181c07258510200e090a1550300003400c414000e004a0b0b44e841c0201d603485d400f00400c5061503810441c0b40241041e0348200380142030051030f04540600c1c2004400a000d4a18800540760a0605a90310f030a6040c07612a540844010321404200c1050300707801c0514551038070011590300c0e01c0747e85400d9602c20071070200c6003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 224828893 1250 224827643 224827697
    0x1a0c06042f130c110102070f0b0601030612060b030a020a0303021005060a05010e01030b03010b0a03050601030303060515120702070b0a030e070f06020303040210230d0b01030c02190303020c1507 85
    0x1010007010801540b8100c0107000c0c0070046001c0003141402103103846000d00007084000d10860743c484001c403103070610504503200607096504060070b01c14104890807034442500c038819001b0b14001668144000000d00c0c200108000035004985100000141600803d0380c404001d00030b00c0901481d602c00d0100011000d4502805000c07402c0c0308448100d6500c20b9005040c0d8110180c0000b803100e42c040c0001380003070400d9100301c59503070000f0014020943e242c0200b600134001039840701100c048200da000414080c41d0b02c400c0c00300c051040000ea0051003084048018481c0f003405a54908040d60010080c00358400a20042c4c40349210020b20080b148100700f040781c1c207507405142107032660340c01c2110300100382c2042810400c203001e281111541c421090841410f16484803a0b41d04031100551041e42c404244150515281988041c1859000700b030140004008a034540d81200e0140390a400074003d20b06100424829501c2e10040700140164540c004e0900d07803540c81280400070120980e84c0f00c4a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 224830143 1250 224828893 224828899
    0x1110060501050d110c0307050a02030706020303011202040b0607060507030b1908030f0a020f0d03050403090e100905090102131202090610021207170a091707030b011a0c06042f 77
    0x51201c2c00c121544804101500111001c5c940325080101c3c0e0b145800260040e0390ba42c118044140852504000c00001020140042c40c1990b16005061440c052481c81c040e002d540c4901480c041c0d55562030845119a600c10010001420541030040080c2030160100d4040d40d440100d0b2180540121203610403144800011407401c02d00407100d6500e80c001025060540c4a0700380c0e600c41d0001c09100718001140b031076a00007802d1819040060403100140c3c024034090f858001408081e95080c40144180d030b032804000f089a85804440358024490313906415001e81c0e95000110701c0c0d40090398000c014500803101c4800030b844035030401c60a030a1040d11040940c0c810701d143c049205400b4054071415002c0c0702441075020388868049403981c041e00d80c2100003600c0c00703400c2c000c00c0e4510400040c070980420003420035509542d41c81c510034070b06009041001c0104148440f6560504084840c5062180183d0b07200341854a40084c1d111103844200d0024000d225911184103032502c400c0d000e480d801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 224831393 1250 224830143 224830147
    0x108010b04060b030c180603040b070219020105070f020f0a03060906051b1e090a090209030f0f1f0605041b0206060f280e1f09050106092102040507111006050105 71
    0x842803694861080300304d042c43d007010400c0c4941d031f400d805176219a01401032004c4c40d02e07210340300a00f048000011040d29003c4001d4240c00b60364000d0655440d682d011311924000111800003e10034840d6115046e44100381c410003004000e455081141303914490341040c4100d0703c40c03a00300107009100d0198031203014018402145003240310300c3c2c04550500c2c1201e04500d013100d240301050030743c40300e5004501c2880c0c00080340101ca08080105071108000c940103002c000302034041d00c42e126280140e035601c1c0502d0302c25082010400c658444001030000810422481c8a0b07000100340301001001c040001d4022000003036141c0c28203500368029607000508a4080c130500c0341141542c01042d130003800d440c00c145040070070100729401c1c2c20341c0203581e0000c02a414070b00d003604409401c500c54204040c12400c000c010040300d6008014101601d04101e0400d1802400058a4000c05041c440107540700382400b0070b0280280c0c01401e14640001504280c5180342c150105000a803481032040500007001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 224832643 1250 224831393 224831401
    0x10f061a120402150d0507112b0525121403010b0f07030c14061603060f2706141309020d08030603160312090e0f04170415080108010b04060b03 63
    0x4a413190059032244142c04906001040c9810411a0300894101012481d000404a4001300401c82c1c2c40c03400400d00840701104120800c0e031107405441000f1070060013404113000700308000c00070110890b030302c55112030a50420142046050140340311215004124500c8141007400e540004590580d101400d1151401481c21980f038116840100c09408201c5142c1c0d400d00050714031042e624042c020034009251604204081c400604d0351850080c05052400400300441c500d00d20600045501240300203841042d812010200c0c40800c100030000c030347c0b42150210b11607a15401c0c890380c0b01c078190740c030b09410440100c000c8115a0380602c0607600c8480b16502c170740040c1110f8001d540c00000075068410003070b141d035255a10555150003c4a000c21000030b4010b5455000c9480c400404107040c681d007144c00c0a604500e00b4407000b400c0900000159650b407201d04124100300c60040c4018001e5140090b107807400108002000c0c0a201429403c0c400101190b10b13007070041e2002e172426007681c42d1540e21 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 224833893 1250 224832643 224832649
    0x307050127080712030f0e1501060c15110c1e070609030203100b150a03020d0509011b050906040308160302010e010c05040b030a06030506011e0f140103020a030e010f061a120402 78
    0x2d07013507034440070142c0341c1c100d00c55819681e02842601d6000c0c1c40090000c03600c184079401000805030070079410010031542d1000450342d014100c2840801141c1d0006809002c440c100c035051040c040144041d124952f8007494460900070b414055940170019200026140c0b20119001c18180c4400307541540540521528807180345e00c441c03812100204409010880300800c0701c4180c208040543c007180d40800e13803a0045d0098001c00d540400054000c110302c0041901c418200d60002c880041044008600484c541c1c0300c44003210099900141d0550300c600e9100724010100e541c9040807001075003000e07501c900078503050040521800c2245c548508060030f080013074400c1d810040c031010328a031300c584000001c50301c00c1c002d40f8060100030180e5007000d00b030002c0303480806041d0b901c032101194058038104005005440c039582c1b4403000b441e01581c0c914582c1000c03000351008181030511940b915011104900310f560041c1d00301c038103c018000c0000c52003088210325008040c058000c103d04040007800500d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 224835143 1250 224833893 224833913
    0x10609090c09271404240e060a061706011410202505011202090d0215031f0b040b0a0203070f300f050c01090503070501270807 56
    0x1c40c15180a4010543d207010b00c2c0f2400c0e452615002015508000d54541800c1e40d00605405101c1c080364841142016130300e000002c081d50850680d0050414112586e44400740c10060f05050641d0031a0352034202015410000e1065110f113a10581e083ca00a070f09462022804038101c1e10340c2507403003100c10200310600c1001502c04071001c003002104128241d588a44a0041d44a40019130080c030a0020308600c90b40c2000d0300030780c000700419054108020981c1d02c628041d000300d80010000da25500d03044003140c0b0f8050121402503200740240c0100440302c510002841c0f00c0c3c0b1900454407010b210682c00040d5480b024010f001e00510200014014416604001d14141c80302d44100c925022098640948081c00c485084038074241d02d20101080c60390f9a98200d1481380c0e0301c0109603102100c54009004c007030050301000103202e40032942c3e00083c842940300000d01c0d0b4000054942d54469490554000c1041c600c040814078103d407060304000302c42c09111600c250344160424034140c0c5946501d0141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 224836393 1250 224835143 224835161
    0x40506130213080c0a080c0f040f0513020108060f010917030c1912030e0a02090405100c030e0105070c020109090525030920060708030c04081606080f01060909 70
    0x312501441640c00400d45100414003000018084040c450500204904001065900c6446628245014881e00c980810f81c80301ba0700c0c007100c290070492a94004100603041e000e2a105203c0d00d800100028400b110708010f01c454402d0b07941c1c10199495004100090310209113250024161510a0240c2d035490140d0380c2c0310032010b104a9041500c08941c140c5001007040da040302032800d50001c041008150500048030200904042c4040706208407010b0b0f0b501c4c040d1102078030401c2c0c418046030520070280700b82441c0b02100f4a080c0906422601e002e4060710511000c0c64a561a12000a040324401d00a105520768142d4440b4040751078091460058100601200c0302c0d007003866603035000c96001414030840651291030105110000c0d08212030980100029402030701548144101107541e040c0440e00c0c0c043d03100706040d80341e484159084200c3e001c7c68100601c00e10900d200c801040704c4402000d02143c0c00ca5864100c150f4410f848014034410170303c01d00d00421900c0409220f00b40700d0382c0141c508 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 224837643 1250 224836393 224836399
    0x309010902030f16051f030b0406170a140106080a0311012405130510060f030b031b0a080309010f0302090102150412030c1809091a0a1a01110c040506 66
    0x394160640020341005440c5048030b100c0d41c01010b40c0079010a0341c040140040004075840604115103204040c0c00601c110181e908256036044660a40d55540e88004003a01c0d00c103015400890f60161047c5d42d4855503d400e9030b8080501d500046143e10500400d130540d258040070b084c803084259030a84003d0b4041001034041d5403030701c804c081010340c102c01c0100103001160154001911b0101800440110300c5801d407440c80c01c040c01c100d0b500010a80c0141222104d14107844000c940c21000c4000b00801c54106074180074450110b0b103001840d1840340000c260440d55002e4041e40c5a103101e90701c0c0f299070312803030101d4032134985800280c0c007075030180400207810f0040c1c41d640400e00d420356010440032a002c441c4181d500d44445400e5a062080406a043c2c03404c010f4030440310180c56241c42d450030310648101c039403103a00d0b00c41006a08031941030191209008500142024507440b0302030b01240240000c0da07034155030344000a41c8141d140140c6040311030043c001313186000051001400c0010100c0390 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 224838893 1250 224837643 224837651
    0xd080a1101050901021c150501080705070c0b070c0b041a1b012a0201090309170c0907050c0607030605060304020405060f15040305010b0d0206040e070c06020703020303161b020402030901 82
    0x21940c9000e02440b449000d0706400140d8a10a00745030399404024002e688044500e410030050aa075550306800f001d6807c00d00f4a10f00a94820408a41c01c1c442e40c0401041c1c04a800000281c00c0540805003410300c0c400c0c80c41c2010f032074580d081407415008034800d401008000d61060308052803000010280c0300d0f103440c88102100c440945d80b0b404d4440412080a18a40e5160884040d4448000c01a206604c40c40203000c0c0a04a840c014000100f6000d00001aa600d402d41c20b9142002c1051070700030740001d003030104140340414014006820003014003540b4011040000d803414402c0c450720040c1d400007442d841c00c540f6103400f4800200340040401fa080360610611624642d29090070700030701202003d03255580d5082d460481d0956918181043c050303004452030400580d1620103540581f921100440300079a1600340c2240e25070f4154001900ca1440040d00c5000d044d408801103109031520300c8800d12400028400701c4401d010b8400418140301e4400d43d010041c5410740085411071034a40000c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 224840143 1250 224838893 224838917
    0x7092a0e0603130215090d0221060903030403170f190e1b0a090c0e190f0609061e0203220302120106170a02030c01270306060906080c0d080a 62
    0xa500703500640f456903e2004540c0000210b01d000624103c500b000115000e003040f8038000415507440c00c151000303101d02e0041e4617101224141c2e9614030500303406801110014108520a10703120761080d5030039000116216440b5401d900841c00c018010b1440700107007a1607607603d0120a103150203040400c407106498240341c0408804c00c01c01500148a988403603000b02024500300081842d2590002108074104800200c1e0507802126a0380c001c1d00c2910b05d42902c4004014080d070105c0e081c2c00c6990301c24500c58000c11003da010384090140d69481d2242a01515a580d403440007403e00c010940041e44100a00d80060010000c406e8400700c0405124840949990000c1c0d2003650f071941410f056035445004005101c902c002d100d4007407030014040c00e2050f20b0764002c00d440f07121038480d03d1b043c40340e580c40100c01d2071880403a9080c9030701c00b48440501075441c0e14042002d04070900c260b21402c1d04004000c21410b20100300801c007004010941350100109035034031042500084085130a019480d0528 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 224841393 1250 224840143 224840149
    0x1201090b07110c0d020f1504030c030602030f18060c0a11072306031521010207050a02010e0a050306041502040510031b09150e04020f070506010807092a0e 68
    0x140d0080c181c0382c03610300b40c1c50361450190b4607000d442101248110040245000940c035103d60082001400f50344000001840e220034080c14491988001c05400440c140003080c0003455015500a8403c1105011075484214070312500312161401f50741c060f084513010440070101700c4020102d5008604120101039420300e0428242180d50740402c66600164220f4441811a90a1413407070b0f40084958a080d418100c10101c3d8940c40c501009008480c012500540d0a280e1064004515032070700003559681e03064030344983c40e500c1c0f6171012404100c042c048902c15160400d130940607220003030000c00b1155210f40360b0700011862410304169066080101058940710f220080007400e880d40c402281042c0041e81c050000c11805907460b00700140c440c4180141950100c0b111400c40319480c01146242d1104000341c0284a803070340300081410001103a0040000c04181a030481b0701c0001a07a00f00d035078500382a41691401540014014003454141c521283e034440505900d00542c03070280c994110100c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 224842643 1250 224841393 224841413
    0x70902071e030219020a09090f020907050406091406190c050d080c0d02070c0e040c030c050a230301060b0318060f0403050405010813050a0b0609090a02010203031306110f1c020414120109 82
    0x1040e907109d003402442e00158102400c8654004000b413921616252a05030020600140ca0181c003045c0c0301ca00319080040d545402c1610219450200a4000a1f100d4400500038500d0400100c80c10701444481100c21030080c00c0407840303030340b040702c1d141e15010b54100f111000303500c1031078121410880c14201082c0445c2508509200e50b2069207103c40c5141941040225000c0c1030b07103c140300b40d801d0942400111400d460f84e00345000c1141e000100b108400c80000e024250070340100c81c2c100030100401114080441000f1100030108091f84c6840d100c24217401e034010002c49000e004510104005c02c4554450588a03030702c42d003078081c01541d10100c0c2d0fa0306410f101d0620801d940040c0c0103001d01c82e40d0329100c030555400c00043c0000b050380000e50360001c1d4490000400c4002c07926407404aa2040c030009070001403c52250484290366842e503010381d0f6155402855070050f07001350000320508803503150700c00c44040c2c49040c8154841c8000080421030701305040140e0310019522121040001707010700030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 224843893 1250 224842643 224842661
    0x3120d11040e0f090c060d02030406180305130e010f05060a1101020d051605161103030913060801110414040f18060c12020708090405060f03070902071e030219020a09 73
    0x501c000da00d0401c10f10000110302c0291105600307400400d0f0300b400c5917403210222600d0300e6220201503282c0d51030781402d000400e04400390141e140007007454001059030041c000c0c1008506000c580640548900c0c2d03d02d04001e090098010740c035240001030142e441c10f000540b030051503501d010b198903682449213509a03045031500340c941e43d4540050100402c441c201d00c40180b401c41c600142010640040300c25548034650001d0030762501980c160f2640d0302d06000310b40e4260400ba0000000c400d141001c2c900602581c4294400b5520704511508050104012641100c0180c815044030f0141d50342008002c2a64280030007955030341d0032204864500201d101c100084c0136000001d0340300301421000e0040c0d162024240041841080000c000861010554442d4601600e0000e61550f402c000720f090391207101c00d41641407103400380019050001d9002400601e02c00e9680c1d400812100010100b19220346500a000d600007141d00c6084005100c1b18480040c00140a200169550b007008070407035060301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 224845143 1250 224843893 224843909
    0x60d06150308030901060b030408030f2a070605010b0a020d05090112050a0c080c0306060403060e0f0303100f12020a03031206170c0f060412081c020d02041d0603120d1104 75
    0x103c01c200c0200f90a218142c000d0840c1d100d218a503107403641d11000305100040400096140341e1011a81c4800c60091029054015841808034442d42201c280d040d07821690045840038140f0001280c21205501031f507042004a8005042655016006550581000d54002d0400402120385403495a0a00400340070f400c4011000685082d0000000e01c010001810009071903005c000380842c680301c140442c0d007225002000081c200052410490806500030f103a00740314800813041c01406032020307000000f1100c2c005d00c501c4e00c840d90340c40005081040100080d5124211f9441000882c0c001d45030010050084500065065210b1400d50a960704060b890100d82d0302c11500c00c285820100340c0c48010b0b1908540c03242c281403034000400e13017280080000820b917a0012800c0403080001002d004801d5241e80019902c2c0d280c0201e0f00d0000303420030312861a0048a840e42050600e5581c0c00c003c1c090400500501440700b0005a4a01181c0c040b408032040140d86a980001200700480030303002400c031903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 224846393 1250 224845143 224845147
    0x80c1312030806010804170c03040302040504061401080c010804060e0a061a011d10030b060d0603051609021c02031b0706050a110c030702010804020d0519120e030303060d06150308 79
    0x360034010200c01005200906100040040c0004100441c282104000c0c158480071f54520b40058003d095005960000f504142072506120400c2501d811440311200a0824220107070f0781c1d642407560f1034102e5038240c0e0204602001040109905400c525402614032003101c04118965541c04122689402900011442c900c0f0b19005503038011010641c2c280c491500420100809000610001a020814007031580d01c1880e0800b94035807806544444500010030403549940c4d0400c40e0326040000c000b00c945014410020414250b24400c1c0c4140713007404800a0078041c0401d100c00c00a60000c1e103800880108240c00414081880c002801c985100d5200400c5a05202000900b6a65140f400240c811400c0c0700501d00340788000b0940d4030b5981c091030440640d8940d8008903002a00ca044043c0030380c000e040d4881b1800084100240383c091141c1100c02c5140070100b0101c80c03420300480c649074550010004a28503150048417034618600a25000035990f8110110281c5c2d5180741e80704403840140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 224847643 1250 224846393 224846429
    0x21939090f0c021902030111041203080112080a0809070f06031509090201020a081c060e0f0c250212030301080601090f09021c05010e0106090905072301080c13 70
    0x20900400009503080318007441511882040039403075407003080303004004c000d410303100c1029540d094204182c54803002074515a11500c03401c0c1314003a0302800805a012400030400060000c04812a90fa0310540042186052001e1401c044860940103440050381780f04000000c141c030381e043c1d0180030040c00b0640b40045c542910301c060b00c03040e942d1680300a12640c603203034150740983d0300483d2a2550b10f502c1750f01c0d29a07420315846a42414060b44461a50360f503e0814040785031148188001e000d64291241000706a450750a045260b10640c00000303810f40000380a205521040b018450b01e80b40f00170004e01004a040404a1541d00b003644448900da00000040107000d07054811031111710281c8206014880240d00462a0664401c00c3c02460b885118a44000e004c8294008050148010000e001307895490440001910703611000f92194042c40400080011440e07240001609141c40004001001e14005503082030009008201d00041004044803601030f00e02084080d161784e550139003035004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 224848893 1250 224847643 224847659
    0x30b0403020c10171303140a050408010204030f021305061011030705032a0601230105071416080304050901050d030908010c08240f040c0512040b04060c021939 70
    0x30140c4840500000c6142900c0440c0e40545180c4047c0410800745949860b8400200c80302c2c80317698000011940f011401000700084e041528408a000301d4044e00c5036210752180303908640d4140e8041b940800701c0701c4840c06050040c2495428841c1c0d45e8103070b9080160300d840c3d4900b164010301d50380010f601c1000c258400303041400300760512100200000c0c005581889105039194821520303800c007911b4074200015240e031040701100c8105620144030420112810f540a40d03c81c4c0c0c031219161050040d80300421004070001c26202152170041038201c003640b80805014409a0404090b420081446004110704400f4000e04040440701d2383c47d000179150801c543c400300c0070310401c0e00443d03100c4039003c01b800d0390302c1300d40406800c0c1c8202d400240e920301e850400e807418804c0d419011755024007070042106000b05081018460750141d0f4050100e05091002262241c0660304844500352036800e0080100d180504c40040414203c021328034100e444c403100030080d02c1841c0d048141084203850600a0b90 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 224850143 1250 224848893 224848937
    0xb010602070b0f030f1012060e01110a0e130207021804020f0105120402100306150306140103050108070b03130602040803031603050c1e0904020403050f0708030a09030b0403020c10 79
    0x412070001050808504088112043c070000c0d000792405c078a6400411008a5030b0085a002032240f0140c0340d154200320310b070800c00f0300310419500c02c4c3c035440c14408800303566245048500b440310740e03a1000040c040040400a40c034401128028140c0d500703001850068440c1c2c908e9000c0d10710a44042c044510f81403040181c11000003420030f04200c810700c100c41d01040308550340382c0c00c203504071540415541e0601d4110000c2602303a10a20204003c00307038000c0b00030b4055002005070b030310b02203242070080182401903080e504284a40f00e016032040c1c00070841c02640030040c44d0000005050090600201c2c2c407984140d070400d8000800c1a0000414000702c10040807180c1401807480c14140003c0c80c0c4030220300b00a003c0e007d10340750303802500f0030314000c6240c10400b25444050000d00071908c032a16030600307513982c07074031284075090905ca40c280105400000000b40c486500144e0b44051103141035640e000503020024000328154410043d400c441550760150310310403103081ea40d8140728210429407480c440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 224851393 1250 224850143 224850149
    0x20d0c270b040b1605030307030603050c151603090b040303030501090e0f0d03090606030501050c04060207090e101a040603060e01110c1b03150403080f0c1804050606160b01060207 79
    0x104421890400024800c1c030140d40803208240e030b4050321140c0e414418a03058403d420300402d140000400c2240107a0158005070030f8074026810bc5181c20190000d000198000d0782d1000a140801d02c021404d0304449080c0094442c441d2812060207a500e40d81d04410f6003040e08110007007500c0d603005110303114140c03140c49000d4000030010030b07000102500c2c0c940c80745202844402050307107130384507803050261a403c160010b43d031000081200d803504c15500c2e0140c0d00503000e124014003d003e00042c204589000e610640f86010003d094401d0312a40d82100400042030b0f100140441034010b0b00c050b94407841500d000711f0080c1310104065803009a014210b0700c0800d00241130301f0083c051420701e03010001d500783d0036120105560242012050009203000318501c0c200c1a071a14640c100310425900c080e00c107001710f1a040b100c16284d140c1d403c5882e224024526204040c0607420b0f032540d000d00d8290002a00000e01900705407034900c480000d035040b40f041190981d003441c0e0541c010002d81d941044600c1c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 224852643 1250 224851393 224851457
    0xb0c0310050616060e240f0723130f09020307030b03070311130906020a030501080c011404230d140607080f070c08040f260604030c080a050d140702060f010f061101020d0c 75
    0x1440c0302c0254600100103d0030001e040c0d80d0100703001604004066916000e0424440c5100c02c4d5503640078cd0034060761040740c1072000281049a0300226080c0015550700340ca5001d070a90341c128860070309004140c00c001480c03114507a200c0f640384010492034801004030104984d80404c1660404c440c0519190000c42414100720049010a0300420880150340c25292407440405902000c40c240c4a507c601035028154841c2214203020108030000404040740708440301540e54a170341e20102174954410454217601ca1210202c00521910f1240850305000d0f4410b01c0d4850030962a211710b41c5844245410409481c2020010200b000d0380d50389405aa03282442c006090358606581c0041007c81c1c0c031180144848408034035444e15601803c00e542100816080400a100d20b1050441484600703540b802c000d8003840b030120f074011284211380380c10b852046940c580380c139190010885148026030200c2807555407d00c52000040003502407080040c035143d44107181c04509000061341b10340702d4400042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 224853893 1250 224852643 224852657
    0x31b0e010b09130e16030308060a030305070b100f0f05090a0203010b041a070b0a0b10020a121206030b0903070b220209040303090b0c0310050616060e240f07 69
    0x108119004807080d6050603250300d10f80d410b0b20f21003103016111102a41140c0d028418200710f11071444900d100032640261f490040e0f644403181803125186481c01b014001400070030040000c00c0e030075482c0c55001140286410f5000d6600c90121405111507000720f0759403a40e46400b0402860140100350f08540300040c11844c0d0b5141004c240c100b0720803482800c20407a100010107044440074016510103540014070808a890704840d900c00070100300e0111446214450803650185100148145100d130b400204c624014000c0007054900010030680002560303200d0b480030001545840c0243e0041d030340c040046850b0141c6107001e4a03404002820751a0481609544000c1e03814000800c02d904d50f0181c072262565100c0f0b040c01c03405032401840213400f03480b94070180220002844019449024480b180307030505512901000045c0c440d06c1075864a600d4030000c0040400e0721548040140e12242c0102c03141c1d20b4911600c6407400d44009020b441e100952810000d203401d100c8c4d07405078050b8031460400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 224855143 1250 224853893 224853899
    0x102030a0e031306200312180115030b0c04170a0c0e0705030f070905092404151802070b04030f020105010b040b07031404051804170301030c0b090409060204031b0e01 73
    0x1200c44a1640b08840c1008000c0d41031407045ca102c1c1c401402d0f18464913050302da99031860b9040300400c003410ba80030511703010414801e945c40d840c1846003c450401c0b8021811106195440b50030716a800a016184540002c0000260102c0c41146083c0190100006880c800d4454141082c0000c000d901c203034118000a820441401d07800310450341c0c0030304599910002520b0b0070104480131036036600900c0d0018110b9084c003422030403918441c44001c40050036180c0010075881840300703032402c0d03c02148003010400e40500258440c48000c9a0312155030390700604020840d200c0300720803102a102600481e405081822841e5428000c0c02d02408010141038602890b11020300030520904001800308900626030300c0320f181100d4201c500a0200030402c0c071075a07012114040c0b00b11402ea50032100707094500303441c2200b1400712055134100c2e5040344851201524090341004254080c1044940c02a590020305001503101e00c00f034006980112a91040c4000c66040740094064030f03006050b04c40e496030010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 224856393 1250 224855143 224855167
    0xd121a01050a0507150e06090f030a021929150a1a090406170f01140402010912060207020402070b0604050a0b1f0c0b151e0306010b071506080102030a0e03 68
    0x100c41c00b8a05180480c0d86031010305002110100c02011010001d0406800d00d0380b0390000143c1d00d0048100c0c2c02515640b210410782255284600502103000d43c000c046000669418907a0304500341e8003600d42c0f01d40c1c6c1c298510b08540f0507240d0b90a0000440c2c280300030712440480703015103209424003c0c1c503603400c0c60342001240d104a11a4801800d20803400013401c0340745e42c03a44e42041000b03020303101c1c18003d07118105a0751074943c03080b4070714a109586408585164441d03e40c00942c01107406844841c4000e0030a8001410b4001401c0c00350751140d000c0082c1d4005031910b2000300045e44c0100e0807210340b42018000c010580b08003610180b5100c1c2403011008203a902c1e0008517540190902044018140c806026076440f84050000382941e1912070400c50280a518080035200d40102c030092203145940c401c0460380640a000c040d0141d0011005000341844030000300002c40c01402c6440c8200c01100e8520290303989034101c000940d4000c0706000c04d0040602422551f001044069414000c0000b82 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 224857643 1250 224856393 224856397
    0x20601050a0b0c210306040e0601050d080705070b0a05091206070e04020a0917010b1002030a08040b0606040302040c031a0a0b070204180b010311010f030c0219060e0d121a0105 77
    0x40c2440a0358005810200307a0f000b00400000000c0801d01c942115074001491003594100b1138005000c0e50034103000404000001c212541a214014048160710150b0340302c1d1001a084004200c035a4403c1c00004200ca00e410380c00ba0506000d00d1355006d5448151034140701401210103160b803582d9102c2814020001e4100702085e950f03090035200161240c4d0324400403510310f11564081c0c1252401d442c1454003001c410340112035441c405840806d000c1c40407010807652881003401d0030300042e9580010078001459a04c80b20780001b0002c02d0320f0700f09a203a80024081725813101500c00429aa001d1014040004859002810f50120340c161202c0d440c10101d02094480d07801d00030320941c1d440e0382014060070742d0900245c0c05c507000410503400d0f41c0c60303207056040c00c0b241c12107075804500c02031a054a041d2103401041d9201220b82d02400035440061100c0112140980302181c036603855850030b4007404010801600380720141d0b42c61410a0a01e80e0340b100480300c940e400d1409030051030140700c0c002d98014003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 224858893 1250 224857643 224857649
    0xe01020c010f030b04020f1312050a1b05091e01050a080312090102070b010308070c05040b0a0608040212030c16080307020f011b0503040b09090a060f1a0f03070305070f020601050a 79
    0x2425403002c5001402240100100300e1081d500034804168040380080c038001801c0400d00080e40041000d444a445810003903032803000400585c041c0240000242c10400855000380c0c0798440490300070b894000213110030400301c0700e89151055504000900340001c011050050200b680d02a5041e802c0c41140c517142e1280044140515202c40d001c0b6459403c2507045030f02603604108811001d5031240b800d035046511034032094450605040b408601ca141502c80c1c91500d110060076940041c4ca804415503049400410599000c4030400c0840d0803404280b00070102d200043c405011a80200400e03401c1607410303900b0026840d8018050340c070060b181c414120303d01d52424241546141c0b101c0c00f42e60400708101500a00900002c9800980340742c03e240074045903001100c03510855541c9000003c101c400610440d140d41c0000d5100300400c11842c0c0c203030f4005446030013207685001030307489500c45c09610580b00303900020b6071601000351031a8854402d40f8214824405440203515040004004d88c2640c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 224860143 1250 224858893 224858897
    0x4090212091606050f0c07051003020405101701170a21030e0703080403081e0408150606120609060105070c0f06090503060403080a020a050d0507210c02120c01021605100c0e01020c01 80
    0x86c280d485400204441001441c00406070000d0800b6a80d00602a4100344500350165914402c1844418081d5180100200740070841200c2a80b8184032600180c0c41c0c80450000741c041c128169003c50303060482c4001400761030f0410071801480400003170450f28104840b44084d00002418800102c03560111800c0700d4000010303030740702c1c0000340710701002c0ea46103080d002c4031001c00900040c00e8480031540e444c0a0042007542a940c0e40d8030390600c030303040c405d14240c42980405d440014096103088414150450f406241042c01c025583c5e81d40701d0071400d1078100041c2402d45000400160754040340810140c00141d0140610341840d0380c02502500c005810341112540200c1c810384403030302c1001980d075107005a00051002d4100010040c0c10812400040c1e0b102503a0b2408686580215009007100740c03035140d000b440c43e00e404c3d401c008000d4120380c4008030255002c0000441401011803040c542d07030302a00240598203079041e405407c480d903c042d00700034031a00c0000c90009a8000c20500e40a06080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 224861393 1250 224860143 224860147
    0x3170304031403010602070609050f01121109040204030f020321120402060d060620070b07020913050105100e1e010e04050114010602031e040e0c0f04090212091606050f 74
    0x340790648090026140c0d440541e07402000009013a0790006030030040728002d807240c083c225105c100340300d440c02080341d00c2c7d03000c40d103074049a411214045d848008080201d503105030800d40b1910000d426030b84154400c0d1040c00c3d5070302805007580390034001c90610b9003041008103060340c41c146180146016201c000380d100001c10300000d007992219001c51b0000c80200d103042200c035440700300c05401d801d2004146010102288541d13103902100103441010380d40c4026509060120715400c00c034a0f4100207203154441c0c80c1002c00040028000d0040b80e00030b000403980520390714249410400c02610080c8a00b840c0c0301040381c11002141002481415503042e0000c0c030026641e14149140507116403200c1081094044000240850b40800549007203088410003140c5030644910214590143d40102c118950304a40840c410000f41002443c00151860030a400c00c0d6403146c0c440200e030803019038081501760748403c0104c011001d1140f880c0303000f05022402c0500782858402001f81c000c0310718405c0c80b6000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 224862643 1250 224861393 224861401
    0x203090a03120b1521190c0c2012070801140a09020603070f030e0a060b03120403120825031515080f070e030601080a03080106021203060112020f0d05190204031703 72
    0xc1403000316031800e00781000174450070700c40401e8100800328160030f51003a24007035503080700e288a00d440b0710703170300b0f40111a803060310a040c81910704200b80390001603400f080e883c41c605580c0c00244622001040f07468000610303034001c100002c440144c002c0c480d600451520031010b0041c0d0703508050720340004092801121011007040158014103292080740039a01c40c1c20a000c00b000140c1d00110b40e0300030264155800720b00b803044101e08502a90000611f007032102111109480c0c443d80b00154401400181d01044188030801041500800810b20700081c0c2c80b101c0b840000310714500c4500041c4440c2e200d450501a00c0c03413008000c1e06019149032503c0c284803011580303891185400101c9494010281d41e85035a44500c266607841c0e000d80c049021840c0d8000019000d800452604001c6070010b60b881c0c40c1d0b580f40c80044590740481303020021260307803d000c0300343c0d4005010090400d0400d040d04c00034aa08009200e02c0522800d1038502141a004000910000d10000511145900e60201140e00c9443e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 224863893 1250 224862643 224862667
    0x30b010314040c03021e06120702030f0a030605040617150403030b04020d05060415031a0403020a080c0a051c0203070f0204060e0f0711060402010e061b010203090a03120b15 76
    0x41c400c00c21036181401c2c402840740c1a0030030000c03688200e600005851880c443c0d4040089141000d075400b00f014000d141c0740f85c1c0c2840c08030764001003a00c1030764507240f0f02d02c201f110560040c0c1d00101c00a6542c002c144414180381c0b003414040d00324040700014108041e80a50307520054005640c01d07103a1100040703007c02d030090300224480c560040c004d544030301c01c4002c801c00400f011034010380300d40c0c100307840740492000c050000000e5980080301000c3c00c160150005841100c0030f44210118880e00e00c0c408082014600503126240011018042c840341508240f490159100c118048040a0b01840c00003a500007081b11515640714201a4958101e8000280182219403001d100d50341118100010b10760044065885040980c560b00d01e001e480c0813190766902ca00f03c0e002404210b031203141003c98a0300c440585003000020820754400503820140360b0981e0029034940c652503000e50020010960065030102c24600c400f60f080280f03035610400200000c104030700c07000e480c4c003001580d201000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 224865143 1250 224863893 224863901
    0x10806090c1804110d0b0901080d0c1401060303031a0316260714130212060405091c050a030c02030c060106110a0501090c1404050609040206090f0d06020408070f0312030b0103 77
    0x6200920820213110340c40d0311040294061501e004145241038100c80c010320781076828a068070f0000e80140039401e00c00d04141c0e400a040e0400380c032201d02c042081401003509015410156210740c1d40821204d000c2490300c0b4902108040d158425040024040d68510000d4522821958040001d40c00004400060101c03c4100c0441100600a54402013000854810b00341803200c0f06075824482e514010030103900302d00030684145032441c81540410b201c0d10746a040140c000c407044007607078180c40b2000410506020700346e4200020400219181c1281da80510544650f105e032400a146001008400140c940c0c0c01401502c0501580b030b480440040c0b000c01c0612409507201008100f5a4502c0c00c040e0244400c0c2c0c403c54540c41081d90604445080c180665805088007600b880b0450701c1e1542009034a0300844174061700602c91b0410082e05230f0761240144a21801004010f070ba490030101d01c98100020782e003114030090980781c0e0800000d200e000084411407414a4000754a084000040340a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 224866393 1250 224865143 224865187
    0xc02010e0c04050c04090e0d0e0303160b040303180f031220130b0d060311040b0d030e030f0316060c0e031c052a0609120d0207050106170a060605010806090c 69
    0x1b149850080c041c1202c000a0805550304030f41c88016507001c5142c20150b0f039114041601d60b8150b04484100001100d802140e5080f521074100842c3e031400c12140c0c0004250f00010a554080e41c0807844400d06810904860807100c0d0805d081c0140c003000282e091040520b80c4464001c94170006032400c41521140d8040081d004140843e40d17074680c030708a000060103681c04140d40c00195180c4042c06807800e07105842428002900c0403103201d08644003a9001b244c1a070700076816004944203503101c01c40600007080c2345100c880d80c4008072900c40c05c00c18102c92020019000741f159411840c0e48594000540b18030103641f411489140003100e8030221203900440c4a000f651800341c0d5640000800f00080c1c0800403080541124071543d01c1c40595545d800781c100034062503005c208019a504001d0f40c0050000b0742c0074100102d407640d50fa0417a9050031248210603581600b01040c1d6a0070050540119401000d00746030100d01782c14010001180240701418080e200c1400007000050036800310380320200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 224867643 1250 224866393 224866409
    0x40315020f0c07080c030307230a06050c0a0806040e1509030405090712050a0b01091202010302040807060302030f0901050403020309060729100e09120702010909060803040302040c02010e0c04050c04 87
    0x360180b40741c0c041d6a9030b4440c01486001c4c000d4800750401d030300300001980c0925420002c40d4084208001c5112010122500512000e001c0d024804000c26007602880d4001c000e000c02d1a42d0f14802818010300e030820281101d0301c910f051130707402c07c045070b400111041c84901c111051001601d40c3d00c01d492640c0308941c0031030f8000d01d250301005405500b0480301c401c5a8814482030007107554950ba603900310b44544c4403660109024180a1040c041e00c3d02050341100c0c4181001450aa158841a890012543d020000180c0c00008108030143e54583d107a8005491200030f00260a1994000e5140d000f20b5418034010031000c40c0040901c0080540480e2244204410fa00384648200130303605000d00880350002c40440600340021604140b00c1114400c01400b0042c090307644c40074101d00c1aa41c0481c209a0401c07207800800310340031100e171282c00000c1c28207500840e035442c5140b0612080d940090700b02b500390b9243c003402c960303100c2c00811041050b4804580c00a040e40c0c9411400c43c1031300443d000b10f02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 224868893 1250 224867643 224867647
    0xf020415080c1611040c0c0201201014041112030706051b07060e06130302060c0f120108030915040605031609120303200a020a0303020307050d09031d0f0303040315020f 74
    0x818410001c03082c0404684c01c3c1e80601102c01c8080054403043c203201002400030f402119000003020544244a03004007800090b18800507a100a10050b030796100306d00d20340c112101040c001042042d0050710005c400542f06130004000c441402034882c0a0b2200c0604070f00c2e00e5000040b60000000f29500c0040d01220206032034455508040c1d00070201e24840e03034690300c100d00128504804680c81d810728550b056009003029aa10399aa40352a04100050201c5120a10000c000c010321010a54064510b903002907888030f202404204d840c6a48000d03141c481d1a00300000d002c034039400b0781169405807036040781c0c03000c07400140c808894415065110400891911440300f0070164950400c200c090100001c800e071012020b6502501481451070160160380300c0e0b0480c0c40080c0c001d802940d444041030903d2800c0c840902e450300140c07241001b04070002802d903411700240300d004203803008003200300b501c000c03240c90f50031808640d4a00c95400054002444945404101c410303a4048a8040c000120280c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 224870143 1250 224868893 224868937
    0x5040302060c010b1203040f0501031d12070339050c0a0b090906060405010203190c02061201090e0c0f0112021b16060c0503070609111906030f020415080c 68
    0x18000d001507292140704c1d01d44580b09012088001050f47c007685c50910300c583e441c515100042d40100b01c1405511540082c0e0184200c8407881804903c0b02e00c9080c1c200710350740d04800d207001400103040410341800c01b0506140c554100803094031101d018a041c1c24003802808060501a18105a040e0115031002021102040f40b03030382e040c0500407512086c1d80d407600ca07072514402c0200078012406403a0069006000b10a1840707400026050140241d06001c052001d441e004140c1560040803c0b20011001100422103d10240701d1105a091240080d014620503640000c07031201d042c001190412400054140190042e07034125480002496050080c0000601c400303511040042090b21060348003500010709603000340610940701c2d5202014601d09203960740c2d443c00804038520140c82e1010310b030f2604140fa807651282c01036020400302181c00d40718074180c1e000b0f0558103035502d921881c60061100f0028142160540210030510741086a0a0743d81d00c2038070b00c00341c0211143c50b0020140340c01c600c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 224871393 1250 224870143 224870167
    0x80c010f020c0f010212070c020a0905070509130c0c080c0f100c0f08040308040b070c050316060510050d080309031e0a1209021809010b040c030522031e0504030206 72
    0xd0080050740700568043c1183c202d0982d00700c2c0071700d038411601c002c0b1950000310050310a504004885200500030241c03035895000c00070403100100c900101180300029485190300d8a2041c54014004810080c413000c80d00e550010101900c103603000300480d4000c035206034541d03424000080819000b104403081018200d22100203004140b00200106001011804a440c8101001e600c501d8241e210102c858940d0344d100c50001100400740001c11490340c20680011b00140024400054529043e1805002c01d0401c0d6040b1100900003103103d4400100801a507212404403510b45038002c410980c9136540c000540b421071082c1c2e501c004111106c506040c2e40f4008a801900b10b8168039a01c0320200524080d8a8085905408000c1d500c100000c460310101108003502c190f000c040d19002140f030403034200116041d11480d0040c580440c0d120000c00515030300310b44003035900c03220083c00401d45080030384014100c1c104560410504030044d010b12001300e030140c402ca90042d50f0151502c3c0c0d03140c4560b240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 224872643 1250 224871393 224871397
    0x41103190e072c10050607080a0311040914060f100809070506070c180b0a030204090201032009090f0708130f0821130b19180b1e130807080c010f02 65
    0x403203401004240482c8613081c0684051003a2000030b000581703041c581c0e80f200410741d003290380120101a103801920004d000040c001d0b20050031004004291968041c025042d8003d00401403401100e44140400841d514105005c0b8400d03848e04107031885031150001c01e424186240c01c500e0b04000c00003000c1d0204a1100d800000b11142c440c1e00203080003058400c1c1082d5804044c4996102d0703d410024030141c58680d000ca212944141800a00d002c03559081a2200c1542c041c1c45884d8080420f101e506400c200040c2c60340600502ca03501c1103458200e0340600300031005064403c90f400f0070000442041241400301c40f00d90340107010b040c0c6034560366030b800500c400c0d103180043c211145030000c81e000d088521981296140d01420307001680d9100c83e101c030003440340000700d08045a120b040d10a82580ea52090700105409140c9071200ca02d444511111762104001e5011013030705030b03003003040000300440e0700c2c0c1d00c440c5078011002566140310f4144000300c0c1c040c2091006c003a51230500800000c04040d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 224873893 1250 224872643 224872709
    0x30d020f07120506040b1e040302070501090f1a070302030f0f03010311030f0a0303020d0204090e01050f10080a0201031121070f05040e160507050607030b041103190e07 74
    0x4101d0710090340703442e800c80b040303501c0480050003640064045000540c41c207800980c041026803c1c400822401d450044800ca8244c4040c0d0142c1c10a030024005540d200300ca61014058640b1581c664914108080100b00381d0b00f46142003041c40864201d0804d4401d104807031003682440a4070f619062a0b0300b1080c6241e00c00e10007150865803000f45c0d43c40a05001c9035000709039205a001d01314503c0281c405402a60200012200c040d030700300000702d00142a4401e1f64441030354038000040a1900d401c504034202c85c0500b0202041c03017100400c01107a074000a46004c0198286000304034440545034090baa80110791a0014128440d601c00c03004000504100d84038180c55969080c085801400503619481540a280c500107805000100c0b1080071000ca050000181d1510528003260394443d1130616105540910001e92220070302d40c15842c2c54055407542900079100b06246041c206c04015070400d40782c0218001030348601070314030110000d0282e10001c01c1e400f480c1e00132905041c440825006110720f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 224875143 1250 224873893 224873923
    0x315060e060a080c0d0219030c031203090c090b06090a03050f070b0f040e0c07230715050a0c06140108030903061006081b07080a030209030d02121602040902030d02 72
    0x10004040d40b40411400d0221091400a08a614050f4050140d00e0b141804c1c01d90304060740c080400004440c07000d08030000d50243d040c81071000d0035403a040520340d0185603000205800d2070781a0000c00c00344c51028044620300d040008940c000302d00441e0050056020069102e081d1200c000103000012525180341e044040c00d842c13840d034845100710030f00d0081c041034211100d003d11061148000303203030324a6000541c82246909181a503550f40c0440c030049064000b2801e10700700007900421041080c0b41c0038016004036110521489a03000f0300da0301908001c002041454000c0720140f0040b0344c040003204a801007411011345e10f82200355a41e0744080b001d140a4421070001400c2c0c01001850101694410f03a034107480c586841407036000e00d0a0209803904024010020a00020018801800f80e515103403000b607155108401014203102c2811f016400350b41180300c0d03480004040c807040391140da101c00000b50500d502d5002050082c0034041c0000c1d054800c42d58818030f019000244490f95054031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 224876393 1250 224875143 224875169
    0x409080408060f0c0405120102040308030c07020307080601050102030a08071e0f0e12030703030c050d090c061106040507170c06040308090a05120a0305160605040311160b03130507031506 82
    0x4500c03c540703c9004a440e508003c400740400d001d01d10b80404e031031208004620015040544030740382c0802c40e500613100e401c00300000081e501e0460509124480090007104090000b42d80b4040010751207100b401415810450104d000842440c00741c07900f04c00b01d030f40344101024221031070b0074058881c170a03001e50300c00442c80030051b0101d1458540040d04031890400301540c28640300c2c3da0194042c143c8040c510080c884144811f02d000c000074820400032a001c0c0b00b54640f110f1404e10060042c6400b05404101e80d04507004000c08500c0000700352088401020f050344104180042650901502100d8141c1c0800009800818018124003606881a04440c400c4800d5910300402c86850301c20200c0c2e4600e03030000d01000020074022800392000f034059540d0503060036410b5403a181111401c4800b1070200e090004d00c80f296403410003402c40c1221481690400080c1020f161884602000b8001c1420141c3c520203401003013400d11a2100560b449160b0289851201078850050150ba02030018240b900c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 224877643 1250 224876393 224876401
    0x1709011d010207020a03021002010603080c0d080609090a110f1008010807060306050123070218070206060907020c150706020c07031208070f1b14011e0b0609010f0905040908040806 79
    0x1842100c00c0035a00178141c514103071450703080c4090790494800d1a011f5540c0c1e000d00202062850005028030200b80002d00180c3c0507109000d864454041c040b103016401c0784003007001216001482103051500444600d4005050000003400301006000503500120b0f02103100d0006034004042d14103907040c00007561061612007104500300c1c2c0161040e03d0004024030034010309501040569006680300e550b03910724007425500031420100d1070f41529014000e541c010410400c0d418040b0b941c001000b100d858802d4109018020b540f000c00000710b0703108182000c60007030750500c0d0300e00f100c20a0b5030080007551070f69154081192111101d220940b0071000204804034540c3c427940f5454440c00e0b142d111070f500c05028140840c1c1e110f85d10018940c1030030000e0f503803c010030045001d0621030b009910010a1500e4402c2e825600c940b0141c017401112030a00c05e9081c52136440d8030665185910a2034126081d2000350001c1f1540981c503400641c05c01c1c6130441035824442110018003c0d1210f1500f101d0b00354403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 224878893 1250 224877643 224877701
    0x5070b09030a0804080307050408070e0105190b04051e030a0b01150c05030a0c050307141605040603210c0b010e07090e0609040303020f0919090605060708031303170901 74
    0x102d9100001d0001d03d8807000540081d0406000d140c10241d145000d904054480c58200c0c81c1c01540d410400302c14100b40c1c010811490940203400e081040c0d02804c500b094071f0322406a01c1801503000f40ca03c2030750f0030105040c900540c900c08001001d0b00034215030404d1680d081150795883c0a0081c0404815503000040f07046003d11060307282164848011880d1a641e61012a101d02034218200c031076000c00c00800002c01c500325814428000d0f0a40500f0000c0d01c4101c82001c078590950180d401103023042c40400115140e50210591040f11416820081d00645802c4070188514040280729460100c00401c05405648005116013001c0e100d101c9181d0b29038001816480e000c4920b55402460703a000240001d100360044c2a203000c00f0600e507400d143c20303080065281940c10180000c404030904d42008469094064140100000e4403041d15101098860102c00d00c00140310b07411a0750240600c1040500c40c0c072800000100c2c2481d6040241460900c1c0e6018108010015080381c85521800d25062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 224880143 1250 224878893 224878897
    0x906280206090c0f1309030207061d030a0f020d080703020c010e0a081c030e1506040f050402090c090607080304060b09010501030b010c060e0c090c0a080f07080a020c0c060a05070b0903 81
    0xb61210001e20500784440100046104010351084d0848810044815405064016899401c0c0700f0340242803454200301c402400d040c1000400c0b5500e604c2256202520348021450101c510740181c54010000703114000700b0f610280c0103000910f80c0a0020740003052507030109121102980036030750416164442810004c2e03070001400307409415000340024582000709001180c2c550001c605000c03440115885009051510141d9a5101c146000042114a2916100b400d0540640d418100514245900451f2980303c008003104880100000c4070090380d9102d10075611003550044000c0d03664a00f510380000a4446482c807140140854070020030198040d001d00c2c3c10305070040e0f44203006400070740c642e5000b9007081e0700500064055000603401907141c4031b402520580f40c144480c7d555011900c40200001c0d401000c0740c0101000308240080705911044060b00140c1140c00036880e040c0300701e9880c1c2040f16064050750b0100000800c9100c003a00080904a1940602c0420001d41d940800b81503d038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 224881393 1250 224880143 224880151
    0x60c05070504110901030e0f030a1106100305060606030417180909070305210705010612020a1401120f1815110408100e0f03070b0109061202010c03050f0906280206 72
    0x1140f0180508071180d4420703031240030710640300c400f200c045240c0754804a042d5403040c4516030004a002c0c5040b00c401d60200701e019004603102800b41c1e10700e451526019100c10380600420710640001010809020141c10b00240381c2440d0031075a903460764006c03900040601c1540b0a02c8c000c1001000017240c51002041c01021130b034104001d0408603143c0e45126441000c0030455131140c00701030107003174003152003442410082c106071003a9403860503a600400c240300070540d200280d11311039082205144e90303010341c5a1250014400c0e0214000c852560218042c114142200401c002112602c5044c0036000c030502c0e00e1400c08035001c112000881c0c4412820f80b265010b02c80c0c0b141d0100041151141086d40901c0c0d40c82110415525812608880e82d804c55100240644070398200400501142041f8071540000705039240c000d0240501581c0064840c0c054100c01805024010a0700407030554840c00310f504580c40286200d5440d904907801101d000c0904800704026688003101d00c514900000b815402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 224882643 1250 224881393 224881421
    0x3071d09070e270106020606190b0a030207151509090804030206030606040503070b0a08060a06020606040e01020f04030c09050c072001030f020f070311060618180304060c05070504 79
    0x5107644518068403503030300381e4280580051219010000da0300c0981c000c0b08801c0da80c0d0329500c460354548400249083d00180c40d080c0304070401c00174a240c040e0381c0c4003d20f080780c4d01c1d4521580c503841001d806030028015400040c0c6204002e42c803c401e604510781c0a600a081030090168120380c44d908020115101d5140041c02a0001c02040c4003518281d400785070300040c02000719281076102c0d4042030410b04154440ca0300b080010509a81103604000f0880d40a50b003507036000011464040001e5440002070312850181e580c0304150b003209042901192920055020000d41d00c136500d182180280340e080c0f2a00c441c2601e0040401d080701404005c40d540903402001412a40c4030010f001c0b0540103100705402d040c561b0300c0c5041240b41c2d0503030014241c89104501c00c9600c400703060034042c2c00a8500090001c09801103010000a80d49028401105228a02a45c07100d070307680444001682c1070800b4000864840490002400356202c002e08003a50300c100c090341c42855540c4280b00688210100440c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 224883893 1250 224882643 224882659
    0x6051503040f0510020d0506090a0e0325060c080406060509040201050403140c1009080105090c030a14010204050a0b0403050d03110a03020c191209080102160201050a120603080c0c0913020405041a0a0203071d 91
    0x34002c01c10001c1141d41e400d034400e200403008493b51780ca4003102ea450101d40081020340f81000309101891060700c0060100340c1d0f4210b482d2a099000810034840c9000040001400340700030301040004000245441501a01600c02102c0041014010344054440c2170125800d290024040e00004038210302c1d20700000c0d0050140c0d480c15920001008880501798000d5903082c0000103081d500d01c40c41034000d00700c803100565298150b041c4a030810300d035903450406042c00c09c403250801480520031100300c03003614500162180c400e1100ca90a0880c02c1c40880c89003072940c1c1084060250811100d11041c02c0c0d034070b46100003590b510340282070740240e60602d40382d28080300036500994010b40c0245582003ca1418210100c0d5500400c02101c6064100303450040020070b010381c02c004200541140c0030b40450f150b01c40c6203050303d0b06200038843d00030300034000c84d21070300850700b0010b8110b801415804107031a40081441e060b958440290401c48504001030601a90229080640321703641c4449800a01030344 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 224885143 1250 224883893 224883907
    0x50405030c180f0705120a0f0b010804030e09060406080709050a06060206010b0405011206050409030e01081f03110109150f020115030203031215030f0c0406051503040f0510020d0506090a0e03 84
    0x401460f200421590a1000070040c010303032154034955075072062201020006d4280640ba0881c4100c4d043c5d0461181808841c60078040466003041d04440f0740c450444041c00c40d50ba0300300110b00034102c00e902103039685c4141c0801141c56036080d000144140c96096007000071564615080303a5600c001c0c85900b6080c8030800c418031240d44242c4001032100c00c44a00812000d0780d581c08030b02281d90020007940080c03401901d07a00340e507a000c3c02d9981c2041d09000b80607036200011041484400240c03000801c620202c002100c020f902400e03125004002540201880a010050145c101c94030302c44801c1c015480c2180010003041684002c1c026682c0280c000c60505a4108001c2c400c20ba028000070780b1010400300301c54540d40c00300140104407a410000d03050341d0003000d05000584030a90812840bc06000441d400700d6003400702641e50007500440500c03907080207424030314105030b03c4144810b840f45c000941c401170f0002c41e130403d50154400f5103c4e2001d50340d806141e501104ca90414501d000e400802c91a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 224886393 1250 224885143 224885161
    0x91b1202090a05090702060603010c0203041a0d0906021614070b09090603011509060806060406030807121b0b041203050402010801091119080601020d0e0310020a03140106050405030c18 81
    0x10704040300020306010304580e11000056918201107500c0310050744905c080006504003070007000c0e240a010b000071400c050800c0078a960309164210301e51540030003c98150f1401c0459003000c0c0e52290080000c559440703400b0f020310000724075408103440e24104110501c0c003103000010410101c07610b40e40001c0c2454498001c100c030801c000b40840f42e0664880c0c1c0e1442200e854140180010040a000026160302d0300da44103042000043c100fa01c030b01d1a2110810206864108581a05500c1107480d2609a01840142d0f0105102130030b03242e03010b004051010030008031420807400385000f801c2e4894600c2c00c001c0c040f01500e03021900280010b1841e4010025054142c124030b100c00d50a100e414142585600c0107080442c0840c41400002c0100d402c0c4109540c05004a58040d001c1c5c1c500001203004401c0030982d00c1000e02c0c4a119619030000c5d800c030046100340e20104425201360290606941e44160051003500030b806514800c0c01508042d20f0149000224070110f405240034820940c0c0c1c851240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 224887643 1250 224886393 224886397
    0x601110c03060c0c031e031005190603020f0c06012709020d0611090316090e03131a0c1b01020d050903060109020a05120703060e0a090b0f04080c010204030c091b1202 73
    0xc4d800c56120a1007001c03185682da0355001c51140c2481c0c03440d5141e180080883d034158085521444c018100c50740034980d4024104096010390300e003800c01690b5401008008802c45c42038540d009a1809040c00100e00d0071210284188080c3c0d1f24000242404400c408100c100c0309484c90007940304111044607000169507403c10707000300003001c26032400c051180c008642400c641801804030003000b0b032018482180701d4810303102101d031303d24000c0d070400b40c4450046030b80c030949004004c3c0300038031000c024488181e030004480021042c0c8054452070226040e80200300c0300c003d126680580100e588048481d44a00b007600c02c183c0c0020002c0c00544d1a06524000035031081070540104441040030349150342510181034050000c036a000035005203015100000783d20090541200b15003021000d2004c588048410394200c2c109107a40340305030f00ca619200145100300009041c1950000c100003017480740d4800321004640c01180d0900800c603910f14010703180044c6485090100e403140594200344401980 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 224888893 1250 224887643 224887657
    0x15021b03010e030f04051207080d030b03010b060c0a1109130605041b03050d0206130f020906031e0309030c190e070c060f0b0f010e0a06120f050903030601110c03060c 73
    0x100000d01e030784070050030b5821503000c11049540024006003c1046040c0201140010142c41c0c3c05000414144403905482d86220540c880c00c03d500c400f128241ca96080d4482c02018500404c065503844140007110f8988071140b40c01e450402010344a03551509200054610a492500b0300500300f403043e40c0c5500c010b00000d04243e0b007001201e1180407070fe00509000c40007850003100105031602e03140c0c074000d02d054801002c18081800549550000070a0000e0300b040180c0c0c1203070342038050360790305011a151506103260400b11b5004940e0700c44403080c1c040000c06000b07206801b912180800c0078203100b00301d170000101e100c0c203275207071001040019a0405d00c8e54101c0c241e40f0300030340c81140c01d40b186016242120440175409035101504c416510f03240302e00305807164083c200032900c98000000145c41715118441d0700140b040e61641c48652070483d40c0001d040000a00041000382060780c8002c0c0d9a0704111101030104000c12210503519500050141c0360540c010002c01503592103440807601d07034210076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 224890143 1250 224888893 224888899
    0x4020a0b1e03010f15030606050906070812100603062103030e190b0f0604050f0f0a0225031404080c010f0e0414040b1308030609060a030f050a0c15021b 67
    0x600c0790720300030541c5004500800d518520300c106070307080002d100410540000f100c400c0c1403911008010300c581010540e8507030315046a000c5d03140c06550909421512401c40c4030070038003072080d00304030703120000810703060988a055a0400041e0744580306d450120420310040c1c425403002c8005000003e10030b41080e4a40c0060b00d095442e80d0f016032107241048044075408a4003618040300b040b49400303c41003125488070701101c2c20300260a0254481d801c0d0f40d406001075049400e130000199038803680c6e4040300c00c1c0c008030012044605601480c00e40704448921412000244590440da60404080003600c0a4a0000001e80310035184100103465040d80c07410550305202a070262401d00b59181c0c443d50320030030150080210b29142500d003524400038020a00c4031034482e80484040403401d01810360340d008400380d404880c04e031121000940000c029500007480340c01070300254800c203c0081210403031280300d8414840c40a444e962a14040a82c500000700141d201c906081740c0c1c0031000340c100750000c40103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 224891393 1250 224890143 224890177
    0xc030b091009050f061f0203040b0403060902150a080a230901150501021f0b06040801090f0501050702010b0d02060d090c08030403110f0303160c050306040f11010804020a0b 76
    0x24001280c41500101e8a4010140032140d04018941042c01440c0d400049110f40161078a001000291203034190014404200d0406804941a900800c12540a0040000c007940c032139507249820780c0a01540c0c04202d000d2003500a0190000c03850700d0507145143d040b6212000d4550b66011120000c0406405801b16181d041d0019107101c3c40e84400075000d050190004100200b0240c00140480d000b82e1245046500c180d503664040b085521004d407055140c0c98000c40c0f1020b800b0000390090103690000d0031a54039100490741007002a001c2c1d600340d40e20440c000d011944d14a01c06900b02d40c1c070700700c0b07503508184208845001072a02500400724145010302c0081d400c440e50303c40c0b2014941640004d0600d920000d001d00901c11200b440a100010440d0400385446031307500829101d001e020035110004070741c050500d0030800c040c180c00300a805c000d01110001e16184c10b0a4010070155807041e03404281d03002285c00c0c21f51190744424846c540140c5040b001504e400b204000c613621140b42600341ca220 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 224892643 1250 224891393 224891411
    0x10e0c37030836031b01050c0f0609071706191404062004080c061e1815031618030f0f12021605040207020a0302032a0102010605010e040c03 62
    0x140502824000054900910b001802d41046181030070140310446603025442c1e9140141c2d603000a81450710b02d040e0460111480302d00740041c7c0d02130040708040342d0755000f4404250104000018080d1203610750b0822900d159980d4507200301400f000c0c10404006401510020780e036003407844e40d820611585490001401200280101c090310303001c0e1000c507501501c0e24481800b4140d51095020840803101d070080c85c16252001460740c80c00c607940e19230b014a80c0412440075005862850101a0b100000e0741d0f41d589203005150001440c14a02d02881060401c0c44181c0b01100b44095900c500303030812400c503600d080580185c03400c601d2030304441c20b2040f40c84da01100042c00340121400d103600c030342d030160308450701c901e0312007802c01080d107800c021548103040e05064501c0500070042111006d5070f00698604450001c81c00c04545500065014490b01c240c11180d100451148029aa494519898000950b1004900380ca840c2d01c909400142080d8402c8102d01e495031100451210606000685901c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 224893893 1250 224892643 224892653
    0x60f053405070905070e031c0c020303041d010906060509010305280609050609061005030a0f0618060906121407050a0e070f0305040308070810050909010e0c3703 71
    0x29840c0800c5034140c005800401100545000b4150000c0c254180089900c00c0c4101003680c51302644180b80310b00c502c0742420002c0768010120111601e80280a681e40c40f519070200907a49601e510550003040000400094070100500c200002ea50169441600c0d089000004501801340a0201c40300100f5507049040501140c0c01c1021284900001c0810054501005e8101303c84008108a020315030b143c040021550f104110307450b65130440c0c1081074803070f282c0014a10041c19060500e40d4018030300000810b84412103440103102c2c00015805102540d1180003000c151421880b8903c240c2c0c00b104801000904101c0000c01016076540407241354a6880c400280d40b2030803a8490084c541c41442400241540303d080405908250b04080c03007a4181981e00402c01140241034104219a0b100442c0780582038907100750003404010401c0b015400c0000300c2e00e000f41200140c102680c0b05046062219050800190f5a54054058800800d0200030704d40482c3c01000e60740070612400c21080400003070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 224895143 1250 224893893 224893987
    0x601120c03081803030a020a0203070909050c01050706020904050112050c011103160303020c030d0b130203010e041403090a080319021516020f06150a060305040b0c0a110f0f0601060f05 81
    0x10907264000c0503d001c2ca03004ac141031090581081ca240360800842c1c5000c01c0000501c050442028603156540e40c1007820312100074026181950703440383c100400010001080070381580e0860280b01502e1100c40c143c0015078183d41403544492454005000c034040440d800040700c102039020f8140980b9240509a581e42141c0c80350001c0004203650b88071070f400c01d040c004990003007240c55042c00c601c1e5506048a0101c61200100001c0c11030410340e0003442e0010302802030f03078000000a0090717003206444085840d2640c1108103214591900700c801c0c134003020310003e103c5c3e422002c0e40100320040d40340e00c2c4580c500074450380900d0055100b428a00102c40e40100004c51142045a40c00000d4010010412029400c01d50010007014108000e00003c25000300d001e0340c0055240054682c3c1300d40505080e58070685200d4400400d00503180c54440742600415640f1004082409450050b81c0b1810145d602c4000c2c81c000e034000071014040c1c00c000302da80004c5090100035009041c0c1041c20080070501c409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 224896393 1250 224895143 224895157
    0x1b0b0405030315030304030308130611030702061602030a091401021e060910050f060d020307150e190e041b0909030f08070516110f100503090601120c0308180303 71
    0x26480081000807801c2840f403280311034581140914a071034074507240205414005020101000703030120740c0e80100130640e80000c0040580c0d0038100d0b201d20b40303150007a4403060f00315851407181c164881c0000c0e0b0580301100301c54400c2001d0704c80902d440d040c0a15022100303000328040f415485001c0c90025180f030400b01088456000c84003d000c0b91405c0844203061081e441054000942064184100c1e991480c850650040e0213a404075800011070000910308100d40d84090451031080082e444082d90082c10070220074410b440307803985e00d01c034a59807a020260707234400c44001100755130115000880844e078102d00423070856920f40907181c40e10303032440490340725500840101c3c480f03501040c0226040a82a0f601c0074050414500b131152901b0603038920319942074010040c200780040495550b80d9150034100141000e400035940000c1003030054026803080d24900994803a00b80001169401d00c0ca0301c5401541c0a58106581841c0da50f070810039420101c05005491b081d4841300c241510200050004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 224897643 1250 224896393 224896403
    0x30906021204230d080106080907030212010c0806060310030b070e040501060503040b0a05071409060f030c2101080d051b0d031a09040f020105091314010306050a090b071b0b04 77
    0xc401c0d030a4914283e00a6070424406040d0080b144490655400450361811202c5038107203044035646018a0030304202c6c460f000290f000c05c4c2da001824000405501011540c00c8545540e1030035180c0310b00300112070000721203421840310040d5050000480d00104507170411002c0c18180c0a8a900000250503250240c11150001d4008420041401a00700345550410002c220410503814002c0300140034400c82042d14600070400640850142c030756a04441c4810b144590854403410f2000f0041139035800032050304020001450342d00d0422402000b543e04881000c2d00a2030700d040c0b000d50903249500500c10038204920003210740c2641007014012034130254169580080c0c080d202c030700d1001d0b0109000841500400c1c2503c10400022503c054250040340c0900703108d80c84411104c0003c4d034a0103148140034101d810310f100b40b1454048001c805058034450102030045544189001080740d05d1110040c04000551001c654140e000791010401803510300e66000c140d41c1142c41d943c2902c031040e20304840d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 224898893 1250 224897643 224897663
    0x3040605071a280b09010b0a12050903040f06050c030307140403020303030f0907060c051002450d02010e0d02130e15070503010e0714070212010c0e010302030c0406030906021204 78
    0x60055980a03c005078001c1d5402c20030040b140c41c0c0100c0d24100c01400b82e01081c10300043d0001285001d46510220206100340038400c0d40760815040d034803074105101d1f40359070340250b00780440c02501038402e0340c0850448200030741c11a0f030b0f680001c5520030442c036050300d00500304000100150f141400114031070190111100503500704103800721720b40807607035000000f000100d10401001540101e07a034a034a5040d00c9000da00e40e2032848803d41082c1c2002080031601d620145856080c250844006140d042107141142014401e01c0a202403400e220000030b00051440c5200d848616120b603c2c0c0d10303550700180c040c0c661b00901941403000c6481d0b512081500383d004e116940c1e0100e054000903a8004150302d400380c210751504140c0098a040940300301c00344a5075076101811003c0a00595000e547c00820000f041c600194044d03009000e42007202c000100076264030f03265035000703000701e0b8000c3c848214400e18041c500002100184088241102c01a400304038041c02da250304980e0ce405140224000e030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 224900143 1250 224898893 224898931
    0x5041a120105010612230f04060c080609061329040f0207030203071e080a0302030f0601020601051c051009240e030403060c11010e060619050303040605071a 69
    0x51040600c0c40c0c03000190381041d006200b4075921102c0f80000250031400840c0b00840d40b50021200e051001091400300007032002c01044c1c8040300c0c0c1c1c0501403800b402d0100500848400f0840d035150b8100d071031079000780255021800c0c81c203105040040c2c40d01108400150140c0c06150460b10700c0c8004a11008022445a11340e0f0516241c880e000481c100100300710b01c1c004881d54060346074001c80c100501460b600085e07504d014040540120006584400700035917400598901400940090ba0070000c80d150010005030389500005015050b50001044000c4026640403440350700d00c03030042c040381d5a004a075015a09240709000308801700e4440c640140c9031a2591403d000c8241e5142641c600b9141401034200a001010048505a0743c0144001c1030b40e50003c8005e071440c80c040400440103620f40ba10590246d40041000780c003c500c101e07106104062031120340302c0b05c04a42d018a039403540003000b0800c92107002c1d0000b003a00b24030406605088491085c0980c000d90812180ca07864036030300e13441036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 224901393 1250 224900143 224900149
    0x23045a09120f0f050304021e030a0b010605070309092c030906070f031b03051602150304111018140325030203011103150d14250503071d04060605041a 66
    0x25402400c0c0030328140d405e501d09034000891200800342c0821404580364803110040e1024030116a82540100d10803101b0359489130000c00381d81c00201d0644c0051000400440d0045003800b42040b107282410704500688a40c0ba0540f200c2650340390f09890300d100410000416855260250045038000c0c0d8510005201505000d084101c609600c034454588140b190320001b0303000400c1c0d5401601c180b1060030060090b1010813417800d000100f40400c42004000c00080015101c02e1401d960300c1514415440c048070074050b03c540954411041a00b03c0d06c201c2800040c00e1200081c0041c48014100e54004112181c5503d5101303042104241c101c02070350003803055090900402c00340c2e074000fa400f68558600b89007006d0f04038007512a081d02c00c88448200e0000c1c80243d0490382400f44204065503c40c072800000001401804200b0b800c1802d40c003400001c9034580415a007048544808804200d0294012050210000104111851a40e4880c04a0607890714840c802152011590b214140c0041c0c0d810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 224902643 1250 224901393 224901407
    0x5030703031e0801060206070e04061a070212010c05180d0b04050d090501080402011b03120612030e0904230307050102030c0d05090f0723045a09120f 66
    0x40b500c14010f43d00300400c00568000303103144c0d01c42224034014030142c940500080c0581460380c0b14608102e070380c820f402c00502840b001487c0e00351003110581401541c000350300d4241c403000d00305500031450610444264025040310300b080c03044010001d42c2c0b91121555903c014a90a8806503143c2c0e128800c500c03c081d400002e010050102420141c0d010714242e80020000b6040c05949103084003c13191520400d4015003682c5107460324000140b040644907400d0340e00d0790300d4540d015400a40c00c40090740b00b40c101070118601a5401a040c64000507140000002010350056506c65500c010410240465428030146d03000e0800700045aa40b072180048450035550090882e22085c1c0002000e411a6400061a00c0403201c260049901c40040020400f40c811065000300d034100341407c1042d0f5242c0841c412174400c4024403070002c2441c21400301c1584242d0840c810003c0d1410720740504480c0110350318100c400d103d0702c4143c04100715140d030703540f4524219440008004030780c0340b5410081c0681c120300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 224903893 1250 224902643 224902697
    0x3f030a120504020a0306021b010603031809090b0f070504080d2606030706140f0d020309160b042105030705010507020c18150315010e01090f02070203030d0b04060503070303 76
    0x14455402d0980000b180c44a02e0b10006010f10b60001c0c44a80c0030041c4105030200d8806000200b0810741d0341c1c10f026010b850000340c00405030300103d1020800320080d100c1d2514464008041e0309140c0e03918241c82450030400b40107001800300070f000005181000708243c0712030444603031b590307138003e58600078920143d0880c10f0710765000310304402045182e840c005908800c0710f400b46043e5405030b805180d90240c0784100708829004110010794090306034017a4004500a440c24401c45011080c2500e1045800b07400d805078031541e01c01003100b0400c0e800c544680b000301c1d03440859a000c00c03040c140d4641e450350b403005001b01d55507511402086541178042c0a03c1c19184010b03110b06090760200c290034004400010300000000d041c2d190001665281040040c25909d421400c541c41540c640e64148100d90003481080a224104030b6042e00c40714080c000ea03070f41903501030001c6090001090b100130240c95000c100d1038200d5a15000092143e908101c4100214066114032010320b407003100c03036269040a80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 224905143 1250 224903893 224903927
    0xa020a0b07061503080702011d060c010e060105030a0c03170405041e0b04020a05070b150d0c170a08030601050702010309021f03050c07261c0f0c09053f030a 69
    0x454200080b031101021a841c0e6031f42440d1051400c02da580b00240380c1d5441c2c11120350008004070b084031030454154400d217446c0c1e0710001150a5a07030780b50109540e5000d9032400400c1c0f465101c00c01c0001420401c1e520141d0400d00b001103040c01d0f1078501240c201d03160004140ca0305505d40958510128507442582c8200710b055400b5480c002c00d580018001d0300c20030394014080303074400b0001500c82e080710000c0c000d040c0008010000e500c80c0c50038101240c80c100c1c041d003e032220840845800d84c91002850a080660201029046a60300c9005541d142c20410040c0d05042e100c40c00d060041e990b0020f459407100142241800b2004076a10041c11546e00800411404904010100c00708070141108092000542400c8800c1441c0000d450a180200400c1c4003049488210b03aa40882140d00312120407604450108000c0186900445008500b031044c95005101480103ca5600d4410a40b404a9014040c050080c0f5140260803081e0610410584111742021500d00511580301c117030551002d940c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 224906393 1250 224905143 224905181
    0xc0915041503020a0b0d0207021215010e040f110f100f0e011d06160b13021f08010608090a140a060b120309062a100501060311030105040e0a020a0b0706 67
    0x1603010032041099030140c03e810000c0811480340070146c5804441e03803140e0140c00c41c2d07030301c1d10103441007a580c3c0700a17001340c410f19281c2ca002140110868400c240715a412050110b030f00c628645805240c0c210112202d9042400c002c00c048035034a40d0120185007000550300e058000ca011076000700180681d90001d41000303039403181c0c045803080c0c0719484000003034200c0d01d290761140c080c0419070000c5504400280070039400070800c212441c072000d281030a44c2c0203680e515003102c0002c640e0030200c1d90100f2039101080c0c400c00103001140c0b10300c2c80581d0040d0303118203c80d40340754103868545081d1041c02248807941d2109261003700051405241c10318a010380308a507450010765800307501e82c024058068000d0070085444d10750420400d00c503a10881032201c8420720b09401d59000c075100c0051071800c00903241420000038165100e0721034112041c252192160031a400c0004000180021410200051149111800241c0d4038103400d08004c02803500d1143d92607002c0e140100503985c1e0020380702d44103005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 224907643 1250 224906393 224906399
    0x1d15010f03030e0909010209130e070b07120f090b0706020409060f1a0a091a031806060a03111f0807021c08190609020d0903120902010e060c0c09150415 67
    0x2c9241e0f00360211410a09640d036880114024014481a5035014410f00102070800c0c06a92050181003054000d50341d03c0358070303071500c1c55961051400061440c00142c4000c0c0049100fa1b1128800644601c2d140345240d9507004040c4950304201d80070345225500203030402a005040c0b20741d0004089007070748025400e18110384840d448100159004806d100062042c00d480d100d14880701c05881c04405440460460010680450300100ca01d01c5188050b10f0008002107070002e01d252007504001c080d0440380b41941e9486c2e0301d0061f540f0705540c1000e9034986410300118132500f0300000103901c0e42e0f0405c45103001c41000303107003001d40c45942210080a03115480100c0e071004029500c0200c00c00888039000692013044000c00e020351210740514404a03410014100542180100320b000e0b9880c0303100304212560140407201c203d003000b40800d441c00d90300109810000007800e500d80e031b074000f0380b11007051560125182c0102112205180021003403007640e140340c80d2080300901980d0008060071182 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 224908893 1250 224907643 224907647
    0xc09040506101e030b1017070801030818040905030a02010506131e1d01050408130803030108070905071e0e01031b2007080a0804031707030c02010e041d15010f0303 72
    0x416240003400d85000000300706802c4c003e0700400c540c1100500058101e0141107030050070000c45071142000ba41000c0c0106030303040d00c00c6181d54186ca4009072002c1c9400d92651600800640302c44189030000d85828001011541c1440500015440c070b4002060034500b040030010091210f81141d01103602d41000c140c0c0c0249917695014004281000007c0c101c442d607404841a4503544107480386d035600f888108010003484a002c2c0519114000840c41d2403130b00d076202d540d182d00003400340c0c204a034041c08080080880c240c00c2260844000c0c1400a2a040004611034409501e8129500402d841d4500b908065926100b4000c0850303000c0000c002c1c145001360001c0000d205040380e86d1082000e00d001e0390180a051254000401d0a40100d4500628034513061000303030450711043d10045d80c90010101b030341000c00d040314510b0780d0580e1544801051a4019200f105400fa81a50401d0b600c030380304c240031a601003400c4507188081d002030a00c00c000c141c0003420a0701c160454207c0714003c480c10000a6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 224910143 1250 224908893 224908907
    0x1b080406030903050d0c020705090a0207020904061a03030415140a0813050f07090b0a14180408040509191d1f0e0d09060207080d1b02010c0204050c0904050610 70
    0x12503510340031807894118141200e0741e025011081598034a01000341080c181c001401c078080b1001919100011354601e050902203029510000c1d401070007a50002d000a5042c1d48150070102504026040180307038207001c245950010380002ea400c0440c03203041049642c00844004c0b5401c42510b609140c0000058010414213000d080c3c41089101c1101d00020484107202d4000e41a00c00c80403a52030507541cae8030544c06001ca0400c1580a8181e451006c251902081d150080c403000182969505411520031105001d10003403059400500c2880081807130b030b45100f13040e406501850751104405160f84040c004480c0d60081e05041074001390003001d8144008200018801d00e02101c000c50114600b42c440b01500c403115180392240240c0107016801500000154240c41d036540c219010161a0303c1c400e507940704000e8454021864040c50900c020490f40c0d240f42c42d2031300c1850100c4440100398042070580340144c495964949000c1389204a608181c494250300c050201d81c091180329249001400c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 224911393 1250 224910143 224910149
    0x30c0603050601030b1903020a0503070e221b030201030509150106030209060409110406080c13091d010c0504080f0c0d020904020a1d01090c020d020d0f12050a05071b0804 75
    0x10685900000b00141c1c020b84c80b00b07251450203402c2180968106002440903001400b08030b11820486a01040034280010400240c0d1141080b40805d600c50607403a07401c4200ba2003085104c40403502c282e10000b542c81022986280c2060044221181540300140689070014091308030b42d40103440840f0300f0b00303402d29500d04451442c01c0050382e921400d40401d02600c15a0060514a820103601201c2440c0450090040310345560740c0380440e881d401e40142c020300c240040056403102d03c043c18084030740320b64002101d803440744041d010321500c1c4074180b03804d56000e00d0292002c42c4021804108070716041c13005075084002140030b4103059444100054411307185c407201074003c1600c00005411034883c3d0f40050090249444400d401c801e224110f80c4403441d090240d2100c0505090090500c28000503140d00b00039110b402804c02e120070394608945040b8540c0f040340801031420504940400c5511905008101840000c1000e141120300a00405450010003e40c05408503645c070228019000ba10300b6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 224912643 1250 224911393 224911397
    0x5090c01021c05090628080906060f04020c0f010911010504060c0f0203010b030f010e01230402100207050607080415080c1b07230306010e0601120f1503080c100204030c06 75
    0x540340c1000c1e0031603c500501502e9034015400280d484802220801300c09800c5c011800000d61440c4a0201100d000c0300603a0f0326840c03607100d0404030351a441c092222500c0c0c004064001420400c070320541034980401680d0341c0380540d55415500003403004000301c00c030809400382400c6141603c2c01d41c00130142c480240000e4050340001c84075008650f000c1d0810308162100404030340080005003255030007020f150001c0d9002e07602e04107113000c0b0502c00d110305208074000c0c0f05c3e00e421540d0722070b024000d0b15402c010440085002d904070104803a0b071068042d0074070500903203081d521503007010075a01c0400078413030301c0c0810300240c00300300181c240c8034800312481040108002d002480b03036107005034078100f1a41c0000c000d03e14450024a80d60b0350400d481c415420040b0215421070340da031032800a41101c05c2c0c4d00e403800941107680d042091f805075000300710b41140d100c0c0c0001c0c8144d10340740591280e49407a00b08403003040b0700061202e01a64100b2203c5100704030500210703e80ba03c1e550300e00e21810302030300c9147c1c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 224913893 1250 224912643 224912683
    0x211d01050903010905010c090e161704060f05130c0b030c09010f03060b030708060306070306080606100207030206040905040c06030e0a06050619030b060a0e0c030f1902180405090c0102 81
    0x7007280c4080d00041c805581c00002400401c51444000c0d10802c0342d8051312407032551140000d400c0a1007071600100c1040c050310b480c80503c1c2c0c4054000e50500000f4410b8601d107845545221050049104d40e502c034841c0f810b001c40c01c80c429898801c43c00103a41d4002c44d1101000d20901085001620890351062000d0900b080d000400310030a401030b00040d48050034005010017040095500a48090702c14941101620301d00e0351002001c0e41150302c10702402282d60700c85000030b001810000d158901c0c0e14901d0046458aa039641d0005a440e813180d08504100b64070303001031000300321048103154090030b4182020b2000010a0740259511000070402408860315280440e1072034841c01d4501d040801d060407503441e503648038240030303004500c2a9486030003a0401400001c440e0800070005000706110410145182c541c50300c000c1011a016100a0444000d0405071100d07001c0f40c8000c00701300d0320500e0b500c0160000101004100c81c402800d4541640000003500341c03d030303404181c4a504032a4003000070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 224915143 1250 224913893 224913907
    0xb090c13030b0a0c0e060304050a02040f060e04121704120807050f0c011409210306030304080307060504052b181203050903010b06070b07030906020d0603211d0105 72
    0x10109000641c00601031510103800d1010380d0100d41c1141c500c034842a20b504034140b00000620105110454000c1c100390007002a180c01842c140e04041349000c0c3c0c600300070504e661030781d000c04031200c0140c41c111502d110360317850405615001241c403d43c0700a4031800780700614007500c1d9038035103081c102e14082c01c01c880100041c01d0703240128251000084041b40c1c0030f80741c90b18410014002c0c0181321902041c0c2d58030800090f60140d001890307001c100040d1149001c0100800582c801a800c041c01341d6900d40403e10010403001d6081029191b02c81c022440481c45081070b0070000c0c1041034041f0020031008403500d200b03200d0a100d40084049079030701d10f488540c020302200440e03d807400a40261602c80180c4e91a0000d1503800805000314410480080003450301203410080740e407040c448010610f174141400a07154a00a43c09032034014051a0058502040a0280c000b03c0b91680c100b20b9a0f040007da0300c02d610a0702c401c0d07924800005041c4140800c1250341c00140c00f180c601c3c403050401200041311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 224916393 1250 224915143 224915167
    0x60103141615120507020a0627030c291501031a010e041e090302010f0c0e0d05010f021303060c030b060d0902010c080403060c11030a0912020d0b041110030b090c 71
    0x40e515012a01c08100d05d017041580251205040304c0150340170707410409800d5100e40122036003d0040400740300d9602020b4541c0c3c0980b0410000c0c0000d03590181c0d40c4c10000031030303054072202d038070544011381801c0c7c114a000c2c1400000040b41049560403d4601402000d003820340c040c0c40c014100090a20381b00e036401c41c90000c0c0c0a0311410101e1001800340280c030301940c017066048401c6091194000b8020708480c035086c1000c4411904208001814a525042142c01c000169250781d038083e03000418281d031070081040590b032000240401c4480d6928081050008520403144401c00701c0c6001d2000261110000d443c40c060303c3e621a03141c2d42d842c08920308581c0600084440544e10111407510f03180d890400e18000e0000d0b0780007801040141c400124101c00120440340814203d464801200d42400d03c1458801c08110741260070008010141d401b1407001458584038030b2003032881d440d03001d605809110015040351190018541440c1225180d80c1e140ca101c150301c40781c428207154440c1d0310390f141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 224917643 1250 224916393 224916407
    0x90503070f050102090a06020c090a0c0512010602070608090604150c05040329060a06020604060b010905130606122c19050610060f2f010c02060103141615 68
    0x242840c0c9601140c41c100b01e019009403800340d100301c1c0c684400a90303a103800e170384501070b0500c0c040d40700c0151400a501c16120368030840c1d45003841d24081c1c4c18414a0f07005191802e40a03045080503034401c68003008000d0b440b150413680804004003401d0b050030251788001c1c0c0c3c101c0980c5180017a580b40c040ca0044540f0607000d42e00215007028030518a00003200350319141c154111309000c0d4401d03004001520501300b481215040380c4049c0c3c01000541c4e01d5403650002030900102050412103580c40c0003845030f5420a000321204130f2050006440f501e01540a02980707480c0c000942c9090400e000011800810617201d40003124000d00b103101010903202450a112822144a400110003602d5405001000603403501c03c22005110b400041d440318030543c0c600140103801000100c0d0000e02481070f8010814605107403104070074490465051841d03503801e491482d10a500164000d0f0010024000a045480440f540040141a82c030100421040c0148010300a000c40f6084100d100200a481240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 224918893 1250 224917643 224917657
    0x6060503040620130302031009031d0418031106090606030703030503040501230f1e072f010e01051506090118030c0609150206010e060d0203030408060702010b010f020a0510090503 79
    0x40fa0380c1e460b03100200080c18a441c00182d00138451042149144d100500c03c8a42c65034258070749003d81d403100c00743c8004440386144600e030020b486040c0802c20429503401014154469203541580d2801c1c2a10907241c02d00080411900b41d0024060160316140070803000e050740d8161601c80e9403170340d540c1001070141202e070b4905520004000384c902002e00b4a950703010b010305400f040450340c5441b0507030001c9219881e881c1076205082c0030400300d0342d00c1c1d0240668403c80c6001c2a54141404850303e101c0c9001d4910042c040e0407a5111050400701c1c0d107080c420580c0c0301208401d011807410054020803c03d018581c0c4040c10300c50070103100764180d4216102d030401540d0003607020040c43c2e15510001d00d400038910030800c2c10110000e00c04982800030600c107040c0c40051f0214011a43c0b0401000090603c0300000e0360580000c000c00700ba080310512009101c0c0d4501d800200d2078071508000100742001b09000102150864003e010014802050301903070a040e40c000410f00b0300f003a00b0440c0c00e600c6020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 224920143 1250 224918893 224918951
    0xc1403040807050f070501080606030415090506010515030112030f0c050115030b0105091b0f13080106060809060108060a2003151e030307060c110d0c15060605030406 73
    0x80100801c1180520051602512680c2a92210611a820b542d680e11140c040c1c50701080c0d03400001a89402c000000d181d200740141030040400750302c000c1220846002c282e055840e904018014021401c203949040444102c0100703a0303245602d40405010b02000f1400b0003020040346401e01000b0b075200e8900042101c3d040b00007040078070305103c0588540d0356540300031145140ea143c000550b500d8200d03a80d51007054082e407041c2c0c03a69040c000d06142e651004c003801e403902c60148900140da0010741000c2000d40b034020000203c15080010180110380000c00c484c0b12980150010b010012010807542d4000440710004506c85410f428500a1401003030030074140f410f004400c2103610300c41620500312250050310815610120f0b585103101602c11030b01e01da601a07004109200008009074001154407809140c144003076820444403c1c2002d158218003030000350845261030030b00038a0460100c0d29800c005c01086150314158018041d400000c001078002542c03010300314914580b81072072003450000c01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 224921393 1250 224920143 224920147
    0x2130810050912180108060a18050105041803122007200411040b130e0103050703120801030309050f04060e0108071a03100e0a0f020301030305180f01080a0c14 70
    0x2100c101030003808111400d6015214200b011508004034070110740c00304a056045102199040c0015100038030060300d1190040080c0340c0001d5130b003086040007200407441040c00714042d454801000255911101850540d03031b4054036120000390408a01c0800c0c2d04490004641c16005c170309101030700d000d486000111220005000070400002c02d000140d1515618080b011001115007440111820440034048803034003044140044140e44000d80b007408444200110103d132140c2200d0030005080c0d00880f02d41d0702c151424010000071541c07074203071003180b403401594031341c0365403002407a580341c0744185401021040c4409029803116040400a0501d0466106007540e442e018181ea82c4210b106029800c030703a13054140072403200030f400c4a0050010b000760201c8641001c50031709500744054220908195551900074a82d00f01d800a14021030094451903140d00e0101204654060b0400442d0321a21280312510309030f030f8010400942081c01c186001503d00040401030b6000c0030040c4e1210154200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 224922643 1250 224921393 224921413
    0xc08010c03090308070908030307050906090a0306050108120c1c0e090708090c060f09060c07090c02011a18070509060d0608071a0f07020d020d0f0f060608030705060a021308 76
    0x541102c0000d42c0320340d4608500e6914801c0c01c40f0300800601503100c46410400c00700b582d42d0f01c038101504840d031008000074501840710000443e0341340e20741d10440d04c2513103800040003801300a000d00301c070451210707200364580b448035143c06840314098146410420003210b040380030503209110340425204080e01c4014642080130000d8626402102c044400b449406840d0b01c06082000503200310405010b11681008104000c00102d1b40050840f80751511940c00005a075108601070b40c500c0c02980d800005254450100c0706c0802203508240500610f0120000d500f264400c510140d444540b9241503600c80c500135000a43d9840307140d280810391703814014049840880030500004480e120940c180217074000011980403401024200480c40c04117020101c0075082c001d40815000d032008061408100f0607641d810500b150860b020743d6405044400b84041040a1062401034050500298200010790b514141e456600603c4611200c5d00821021621142d156019001d009844140e41420207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 224923893 1250 224922643 224922647
    0x4050115062d03270c140603040b0408070c0b1905040608060d03030b030a05060906090109050d08040218012303030c0d0315080601080622150e1213030203011a060301030b040c08010c 80
    0x44413070180c40c00030240d070703002803e04108556020201d401a01e03da04660300c3e51100e0100ca4001070050301d082c1c2c03003040340c030300001e103400c0211000e8840340890644800072141d240f1041c02080e134005003800001c20052243c0c94011840350b500040481d030250030044649407c40140c00303c40c3c005a010700c103000003a410800080b444034855624902118655134035001c0c0e180c00c1c0c8040c20805080340d0006440c01a2a03445a02103551140c000b81403041183e6000c10400c01c1d0700001d900c49040c22244881c1a0303040d080c8001c02d107600020072801141000040d00710703d0348444100300d051080c0740da5000c01807050040300c411500140000410f441e07166079901d002d10b41b51281141c2840500d82c4951020f40d401182c0041034514075003002d10203c9001c1210b68040003001d41d40001d42942c801c4000d00c03031a044081d002414946184210300801c0d6107103205260079552000542c800f58500040c080d01d09480d1802900d044a0b04103142040940f0b444c02c1503003243c44030303030000c1409500301032003000b0081d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 224925143 1250 224923893 224923961
    0x6040f0602060a050f0606070305120f07020d03150501050c0c060c0105100801060f0905070513030507151707031e0203040b042d030e01030b030604050115062d03 71
    0x6030140d0251500ca5a4940740b04045520440711004002c54140c00300718107060200141c605c051203818a03601c1c201001f0700039500380700110745440c0b48584a80800440650600800b24040c0b13060502307000d81001001040c00302403650041504104010416400107841008160f0740c401000e00145e03500d880040b2202d0180804644211040101c0d01000501007414450031045031004032851540c0380c10510780c40060034001c1c0481d000c000e0b00740005040c102400d0072a500a51044000b00003c6140460042e0001000d5107024140316802c5e40000f0300d8141d001d141c1383d110800345000102000d076403406030b0040034803200381e80c8901d2021007040104600307101010700403406811210302209542160540c200e04001d141076550f022041c0b540b00007030154480c01c42504050401007240560b4101207032410780200c03000c0c0d40d85d130b4407080e407016195600602e60000e07000c6480c0500d07a028620014110490754051700e002c0084d400103044500310f20950020010104c41341c101002c0b5500c1d590004101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 224926393 1250 224925143 224925149
    0x303010602010501080a0503030a0903121d060601090f031515080c150f0a031a03100f060905090304032d0501020a0f1b02060c15040c21080714070506040f 68
    0x950310b080f001285a035400500c010905900c40011851681c1d03811002005d80180182203041c8a40408096006981402820181010b80040e500c2c100c100d5000c1500e0050b015040314103004086030f040c05584140394a040660350044400c02e02403480102100040080c40340b1900070400d56180807610351008980c5030015031044400451851025020070824070030b5881d84e550041c0104002000c00d070003604090800b01c83c8400d00c44003118124042800d098403c000c50946a035143d0540700340b20303003a1003900054440c0c520b00300681e29092a080d941d03803085003c060211148c0680203c200400c40c22648104205845000c0c016011f41c90118040d4101d042c0d0400803a6068080e1007904d8402e5101152918a40c1e521081240e169001c0c0030713803903210304482c01e13581c09180e0508002207502da140c2e81c00346110b42c1c400003045150440000d0f6042a244030503600780c61900d103c601207241c5400362a02a900050366200c2044518482c6160141a6000642010000c2070002d2909605180c280c21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 224927643 1250 224926393 224926397
    0x1a0906010e2208190801060f0201111606060308041508010e07090e0c1306080601030c030b03030a1b0501150512010c080a0e0c0d050303010f09292403010914040201020607082703030106 81
    0x10b0023030850342c00e03820b0b1280c08000c1e10074034038280009000800001580300b50035000b0b03200000c00399100c1d2146030099100ea0071001d1350f032503c1c1c00c003150342a910481c020b0040800c150054400c1c01c1017103008081c2b02030b500c02c00c0070304000c03540400c46481644044a500003407422000c45420360b62400a0803940007100e2a0340424540061304611394003038003070095140c0000300554642068900292025042c111100340f40c05030514602300010800d2050421890100c5c1292027aa0320f042c080180100c0c0e1140c000c6626410408044403180d04581c030350790042510390303010a841154902c03503807800520290265111491402c0c5005100d4040015410703101c80f00c2100745442e49400e03a1800b6590f0308002c0b298004911450b444520780700143c142c180e07880c020400d01e9400c07003c0e041143c03071900d0b106143e131654000000400a000441c415080b400c44140d9a2100310324240d00042e407100c03002003651060150042c000344100341d612850890102002c01e105400c1d413080321042d50b40741c000f4024180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 224928893 1250 224927643 224927657
    0x3020d0e0904031e03020705100f060501140406080c19030b040506041a04050a150603060807050d0b15030f0316050d0207180c020a1a0906010e220819080106 69
    0x55400c201004a1065801d500d444500c1c5081080504c80c3d214040d1550742015400c1c40b80c0381c0003440902081e55805901b03100410a241c51200101c12074000d580f049060000d24100142071a40e10015581215440d0402c85040c0d43e03150078000352032165000d46c5145401400c4201890b80e050783c40100010303001d079000c0100340da44009110881d4058003020485208081070045a46099080f51368048032040b00410140d030383c00c903d680c8004454004c2e5001c030703403034590034080c102042001100070002200c00e48484038160702c54014000c0c01400c0d03540c120003448103c4ca416101044481c2702100d00f441240e80c0c4c0c0410048600e100c1c10141401ca400380204140701d26940d00c0040c0110070b440002c0301e6100c248002c030144a00800a201008080d405403901401c046200000754588032502d820f40c56000c6e28004641500f0710905822000703918031510184614034558481d010786261041c000029030010340d0801504a00901311034044684040b001410101d0f40000c00904850340381d15044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 224930143 1250 224928893 224928917
    0x20f0405071716050702090408090301050f01030b07030b130207050a02060409091407050616030c020a060804031b030915090509130201020f0a080a03051e09011b020c0d080901050f030403020d 84
    0x80c280e148410540040c4c418003c0070f003d480c1000f05203412511440120b8079142e03034440803a0035285c0c12202c5a4030307440c05000410901c0b0142e15050340c040200e06d820003050b50f0020008000c1e00007103801c03040c1d060f4046001002c00608110410095030001c040b151615940c140a10162000325011180724401c101d00b0903d0080c001103d505595000349400d041000705007101da0801501c90041d01080301070201000540c54000c1d4a4000e000ca42d582d501040c40c00d818003404000b041d00185c40c0c04100614010040703644018000d00761854403840d15149034440324210b8070411690032465000c3c150f8000d00072000c4c0d41c101c142510341e00c00e8094036010410001c0058031081508405000399004101c0012001d100e03501055014503a026645c854105607900440146000c031483d00780d0303039036592581c910849203489020035420070344010011a055000400d600c44e002d003c0c0203104000203c2c1c961030580c091419600c501c001c0986e8152203161604000b55a44000f0b03904030081b0380d45040c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 224931393 1250 224930143 224930161
    0x9010f0204050d170d1a0901120309060f111009020a0e0f060d032f011a032508030c071802120601120b12010504140721020f04050717 59
    0x1d00e085820050055880207000d0f21140c3d03081d942207848141042c420085214112500e00c41c10b8151507130f0710180c05003141d16105020325044103800894640001e5502c0e000002d502284e85401c1e900701d0301d03040c0d0303840f9182d81c010b95508000c400803101c1400345000045085049502510103c0d008694002c02c040c1d41d000041641032040d5086071b10040080001541810000d80d2040306038400e02e01040d080041c0c1031214407940c0a40c0c1070600140c5c00c0980c0d59003200c030074080c07003288046801c1410110301625002903500c80e1503a11100c1c100d00c2000147d03080e107800810070801031400a0030b90b41d945581c42c0210341c84038508c2c06460402c00c2604000c58034511948280c800134814814456416126400151048003080565a1400d91218080a0f16407038148001008680b5a400450241000d1405589041c2c886814145030b900c050030030480c2004071600c44074558402c81c04808442c4981c00802c42031080c20b80003a4206080100384040b070b660045508840a03548180101152140114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 224932643 1250 224931393 224931397
    0x61a0c010c09241403070c0b0c16020118030f030c0b0903030103440901030f0b03030702190302040c0815040e030a0509011107080a0203060a0902010816111509010f02 73
    0x40360f00c014000c9801c2c40207078590807180001c110060030600080c1c0c040400070500d581c011910038001030500034400c820404c0300501690401890311140e170800344588143c503030102c82ca031000f81c100090308104d80c0380144140413150180d600500d204081007101c1c203014040e08004d1000701c1e820450f4400080381c60340d011003a241038941c4850340e011585c900103c42c0ba075003002c1006000110880407072a00a0540c41910445002824405503440345c11007400503088851211406015605001018116580c00b0048421565040750219107903000d41c4d038000911080d0380c0009400a1a04c6003020550b604544564428800c0a042c1505210404240b00540d000c0d0125006d10343d10a114240000e070144010b880e40c4007061400b100556076101059182030b600390b20803c6140c00840e080340550400707008440c0d000d5a190001c0c01200c0c3d007580001c21500c8000c2c060403001d000f02041b41c070518070440100e04034241c0b444c11105048040c6000307020b21101601d01e4a450361911780183c10440701802 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 224933893 1250 224932643 224932649
    0x9090605010c0807050c04050a0606030e0c090103060c021906090c0501230d020f0d020703030b09090a0f03110d0e0a060309030e0402090d0c1508010e01080307030c0204061a0c010c09 80
    0x145542d5034040c0e903681c0d5403c0740c1140c00111203038024030f01c02d40200c0d03d4611a21344900088000400d440c1d1410a0180854040401d01681500034210401031074403411003c1c0d04490340180e000030600e05040c422400d00264042c806485031000040400380081e91b041003002901901c20b03420b07440e42e104010f4071800540800d40403802c8005480c402d4801a410103004070143c1c406015203450030340b01040d10b85512181d0003040f030301c1e4049a00003d00d90700d485a03401500040c3c501c5103079402c04016540d514130350400020400c0c000a046201003600c2620648040c40c1c24100300e48090101d4880139282548040710107001c0d0f60243c0380014014401c1c01402d072100d4160b1100201041030400713120296000000c030a80020994010400080c45400307000020f0908000080407401c41a100406c0c003031041c0c0c85200c24025801c0103001c1c058020080b070307002d90b42c9809c3c200019280340c80403e020300060791054980420910030350701140c06090041c114200400c0007005001c40000d01504d501c10707680 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 224935143 1250 224933893 224933897
    0xa0b2106040b04030e0d1401060e010f030f020a05040212190209010e010e0a0506030403200102070804120c0905131104020a020705091911180409030813140f010506010909060501 78
    0x200441c01140d41c545005411038000d1800d03900900d04440401d00d0240d08500c01c407100880380e02c0200061400b0720401003d0102d0000341082c1d9490b0010078100000d160101904000b0110550421940c0b40310b0340400800c2c020b8019500c44400c4031031030f407848100f141e45040f0b900d02054070240c20a568821100e07c004140c4076201142040001181d81c0f090500900307030051901c070303c00301da1541c0701000345105601ca40e80b806844c004040081c0c1e0702c828104824aa03981c010b01404000512070b505031030565641103030a0064076401c0c00e1000b100c4109520013070604e40703030005014046554952070206e41d070007805001c044040180a100c1280715910303039100143c0008100b404103140144405801c0850043d5519800080314420000c03905806800036240710000b800d10501d0107142500790441004a500700160940e0344c60213001d4540c010311450480030080c3c8610208444180c05003481c0c600304007160301340c00402e928207000b400240ca1042c045120503a000802c15590300810042d1a01a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 224936393 1250 224935143 224935153
    0x50301052a09060c1e0706080403022a040606020304060e090615070213020a0207060e09040b010e1806010e011e080714130c080105040e01020a080c0f120a0b21 70
    0x50305581c1a9401000e09168848420000d0701c0b91500304200641e071702c01c481000f124040c05010082440d208603030b4055030520401504200102e600803400400000e000c041403504110400c4811090403124810140c2c4a450301c1c4012506d076a0000142056079402d80351840818103680401008000454a9941c0075850a640c0703540200d42c0e07070280c40b04e0340c4044c20702000306c0c9281100030241d8128416120041c2c1c03002d00100f011981c0103034001c480003400ea4810b000c0b420143c82d00c20b180365050103426546042c60700850450303280e0300a8024079800400c2903403600e50b11801c82c0002101c081c4204024404c9554800194440c5000c0d264201c0f88254010241c0d41d280041c890515005031082c240d220802400303912441d03001c0d00400c1d86900d010340d6180784649c180030400049403001401d4000c107030f2041c0450510b03507030030148003a000000740d148181c07aa0012004200c0500c21459503040441104042c0080704506400c1154600340803a070800042e804c50348105a0b410110425088a5000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 224937643 1250 224936393 224936461
    0x601020f0a0f02220207020109060302030402130c050408120c0d020705090106080402040204050909030a080711120c010219020d030f18140c0303041205010515030307080a03060e070905030105 84
    0x58828024880348041d040460910015080c90403a4181c5130809031241e40000c4d49004544c0d0280c481006042e96080071411410301d42c000c100296410203d03064607039a59803003407181d103004400765402001d0f440100c4e44040803107901040e498100301c204041900c140f03907441480600102d18041912000780c10004260b00c0d0110807a5803403800350091b070b00541d0030040800d80da222507210b544900b401000440d51820b0002d0010510303200100f10744200001003860074046000840c40708843c2e0360410040303450704001294107009218000c00328005036142e011b80141150082103503017103d5020703281009002c0040504c201940c1c444512107280f07401d070840140019440700c46103029944a5011102d2000031003003c285107511030b030447c0d900e03130303410079030040c1042024001d041d40281c107644005003194246000c290b40f4012080c00424146010482c030307100d03500c80d50100c0010928080001c82a040110020300710003541d0054174080c2d400c2c080080c1c1c0c000815500341143c1e030b601d1840e44400e060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 224938893 1250 224937643 224937653
    0xc09072706052b141e040209010504020a210923060106210501030606050a0b0702090f04050f07060c03170f0a02130803071b05151c06080303100602060601020f0a 71
    0x7080020368580d5000302c0002107011075200b00818041d40c8504400103091560700c040020405d00c8a216000030124104001606c5d0078444a044840595015803541d6076514240d611840310700e0091482d4031851002d2410904580001c048240100301d000c96800d048001c042c03c151070501802c00300d0f40302000401c99a44903285070440358400c24a00c1076401004900c04054920a030310588240340c94010a00c0240741180281009003500c01070103140000c1940824035030b1200500d030140c03c0c420b8000107824021300303101c2060030114001c162040c05865070006003c0040443e000d07070001c1e40107800762194460a098035406101c000b4800031151791105007510195104003005003025604030f0002400c01e40400285c200309205260303410b4100000411030400c00702a030b22a6201e101c80c2ca40d2040b2400a05003103824a00380218002d19441c50028180082c041c0c41d8014805407000104000440e0269002e49060f81c594ce4251881e503140c4d0340049a440c45600c1814615411407091341c00068 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 224940143 1250 224938893 224938927
    0x60903110a031b150c031b02010b0f040b011103030f041205073518040b030607050403060f1821020706090e040c0806010f080d02011503060506030c0907270605 70
    0x340314808130401d91404410501c00d1307401d0282c8080100751074206c4903004001c2c03d0000c5000e42c5440c4020442d005500002801ea40307031132450316000320340c0d0300d80442459214aa12100780080c18040700d642c1c3c14081542c15200108035408d450100c0911064642c5c0c034400d60850310710130b4110082505821048110700b03c0d404250380c01c40311014408161682070301081029005500710f220800c40404058003d000640390030704030503486500420100000150004240d03070589070000000682e161001410703c00600b00c81c0c03016500481451b180304100320701e41100c50302929400d0503801102e44203070710699403100140107001c040380c0b1022080c08114414601d460b44507000300030001c05140c2d54443c1070705004003030300884213503100d180701444440c000b0012610400c009100030003c1c0c8420b440c1c0600b180c81d00380001040c02e03442d0000306129903000c1003040204800180110503a00381064003900d503404d4040c20346005000c280340c000b081a400703918407003140e00e152103151030b000f1101106d000e40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 224941393 1250 224940143 224940197
    0xe0604180216020a27050f0c0a020c060d02040311040c020c0607050307021206011a040e042013051e16050c0f0d09091406010918060e04060903110a03 66
    0x260607107400b404003695400c40494018202041c000d41400c2c0381070000c20108850201002d5142d0034030040c41140d0385100503803a4000d840c0508107888020303a44041741003103100e09080d544844c009c01d4002c1d4044007640100100d0b88500114a250480102032000750b921104c44000582c10400044d00710341040d00003841014800c4003680c2c90312000e54000342c600080d4080520055000900500072803c030341c0d0740480a02000010203060034503104098209a400500082407202e81c0d511040c4111102c00000c805020000c041da4020008200c005009110448503001e0028030008050032a01f0f07aa9a082c3c0903000d65909071402d0030000609490030340c01024081c2203407240c15243e080c00281400328050500c0c16039a140360003032030071449400b9980304420581e41203101c00f05001c2941e800a200d00704640054a01100403207007400c02e80002d02d06607006000c8044400104410445c2640c8110307101c6109813901e0300c10340c520748025a031350462800010302240c43d443e41d042c05200c2e508500951 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 224942643 1250 224941393 224941417
    0x20f04150902040803030703051e0103030f0504180510150503060f0a0302090702030909070306060c030f02010b040e0309120309011b0606050d030507031d060d0b120a030804030e06041802 82
    0xe269441e201d030400c03644182c2c407100281d0000320a1105070f41e0716016103500100100200802c4940401a000760076106100084c24002c00d606091000ca0081c000d450040c40c840d089011040c03071044c6618050401250325441c40080001c000c41c0e0031100001d100d0802d0403942d503907425503862100788042c46240d044040d6110480c020004016568165501e2140ea034650245403280c203003000b030040040000c4c04100905051100c28404268411266091103030545000454400840800d030700420580e0040c0c2d030454188017802c642c41400000400d461002a520118080d1860b00c0d100d481e4001c01c81c01d1400a890620100b124641c00364503820414020480000e6103580e030740018101e0503610004401081010510805154114026541009046c0403000d801e20000c00003400764806c001e00515100d980b04408081c1f40c07600d100010b044500c4008540c2654041c1c00c3c0940b6030401201c0850000f041c40800064605148095400310384025590300c200e041400c4982010350809991194 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 224943893 1250 224942643 224942681
    0x120903011103160905100c08130f0f06080108010606051909120308010806070c020f04090f05060406020c060c07080a110c0d060506030f032a24150d020f04 68
    0x120700420719004602a0b402180b24031403081070400c000c2d0200d00603a020074840e41c0500d900c0101d042e009131201e2606984902c50750317a900b804003004080b107003a64115901103040c152010403241011740250007510801d0f1a0504240e82e1498050700342d403800c0c0030710800103d0920500640b4000351140044900c018103204040b0b5480310100b01c08d03441f002e84150000340c3d80b0001045004000d02038070f0340194041c40c2c00c000215194001c54492155090018045c6584892480a0009d41201090080d030302ca81035855500340350030848081d40002d0010130b441c4c0203613408211103070383c903600322014540d005a4480c14602c52410680c0d0f500d5081c031844920f40a45a0030081550301c00f5103010050f8421040050541452014540307020007070328bd900000c0d4010000c10749000c00b01c8070407080ca810a402c000c814100004041c0d070610300744203120003c0d9a05410101211481008201d02c90700072246550b01801c514010800d40100b0350801a41001403400c1d8040d00741007071307000b100220601155000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 224945143 1250 224943893 224943911
    0x12121e020d090501030b090c03090c0603040b040501180308060904080d091a0901150515040305060f0708150d03080901060b22050a050a0b180a031b080304060212090301 74
    0x5112140005200181c015105a9601541000d40781c005484203203010041c0380c1c100404100680005440d502800358040002482b000307041001d03600c10344008d01035903240e007000d10f8680913250046e18220b85d254241010006100001c2412035030340c80d003642e1413039090f403034000034003d0504003c0c0050f0341040d03040010039942d2104d80107406d003251241c02011701c0201007a288111503000504104a1641020b200c00502c01c110050003040da68100d07041201d03079a041d84091030f68415503000030000d0240b1070030080d50303115502245100355025124084982d840c145908505903480f13510541c050011000b601c0031910801d4031a900000e0300000050300c940b5a03501c0d080507003045000d400d0030700302c00b000c1d0004c0d400418800c90041000b510704d480041d040070300141110a450080c1e03500b210300802d1284180380c0e1902a056990740250000310545d441e400c202d041d0004080c6040e074000c81c41c078000107007080c0000850b0200d400c00d41c06888070541c4007140701c0b40c40c4d0200007070590540d02c4940c00c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 224946393 1250 224945143 224945177
    0x9031b030f080910020102042706030b01060c05070501021c03020a1106010b1b0613150204030f08040311100e0d110301050a06290a1209050a03050901020f0105011212 73
    0x701d000a4000c0c0308403030b1641c102c0c0c4200310040c88201c0d001d80c11640144001c008070b41d940c0c3c074603050002e0301c15404007200c0c8090b4042c00c001c0c1035075440509466203a1f070000a90a030444d1100307044034098002d4404c020b44480040e0303076902135400b07005104861505032144540c401d90140a40411526240707200240f005461442d051003a00306e04101c0e4000a08008651352400d480c10002201030040d10103854400300f41c100044503e003026180380100c0742d0310844400c1e1a03040740e02a55101542840292079824a880f10b0340140c041214401c629441c0e00c045440c0107528036610464a40c1c800c0340d6440d190702488400d501e0381c2c900f1101b856903070b524088135940a00070300744031341711440c0c0000da140e20b0065541c0290382650710100000008403024080c032410310044420154442c100041c5400e5503000340801003901c88405402402481125001c15a01800401000c0003d0742102d0240783c916005500301c560038030410200340074514581c0001050300f104201486080d05001078100789059030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 224947643 1250 224946393 224946413
    0x92b0302031b0c030316080f07031805030303130818030a0b1006090f1415130504060b0903061302010315060c020112111e16030203071e0309031b03 65
    0x2200960030100705840e214240303001508010181d64002c2041202d42000700c1c2c0c0381d104d03075600031958607200400c14050150300421102500002c4818503520391b00d50030020007900c1a0041380001242d105800142440c5c00001d403070282c90600a014040000c56036040c5c5664804c10241c42842148907107400541d03024000030840c98005e00250200c0c0c90118401e0400c850a42c0061040c010b21480a0040080d8004030720b00f130f90607441002080000302400680d510101020001c100d000c00110856012006880c03401102c1055509002c100c1e04e4011070f251f180540fa01841d0940e004400182000c11808082400c85006040001c0d04150890085496000303a03001000418603010b170000855034411407140140202000030082104608100c0c8458031030303101c0004c20344080581d06600c1d1340002080b514a8052003a0b101c0c0080603914029480ea044050191820006091215040ca034801340c840105949503540349502c9055070b0f03038042c01281000b22107941300c1d80c60002100280c18220 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 224948893 1250 224947643 224947729
    0x11e09120b060405060a2103090510261b0f121305190f02010c020111101a15030103080f090604060903050f0f0705010c02030a1e02012309 61
    0x20300500c0d251100510080e0740024200341d016001c2d00346c0410a0484003041d024580000001c0403210b00a64101141d001c3c10b030303030841a03004007601c5502a0040d0010310b501c4003403040c0550300b949100c1d5000d100358840c47c00c5482e01040c152401d100310b85000d81c0b0000f06a10f400d105011414015101e170a540403031411583c3d07a9843c54090200401c0c0041005a05080a442c031009031400c45c0c1f980e070702d1036408000c3c4070083c14880210007290031607001c1e4010503100c041078011200c106070740c00d0309035000d016591441103682e07481020700301d00390401c4210b01156040807403800c2e15607469aa140c4134541d2200120851100c424064109280c0d41c581c002e000400c21740d40c0303020300103013141031183c14241e030b4031014541c50384404440301c036004000c0745660446009003400003d10b00300d4004203013800d80c0400014400041c045400000c0118010b0210015000781e852014080e903440541d0b0740d100b2844245040706606002c100c04070302c1c05c65032100c0070305148402e429140c1d00a4440c004443e038148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 224950143 1250 224948893 224948903
    0x20c010e15011a0405040b011b03092603030705030907270506061c0506010201090c030b07080f1e070c080c0105040213060f05060c010204081e010515011e0912 70
    0x850100000346100e4401400350800e0302400d083c0107500310b40d001c080d1081e48280342c012034031089203100aa000d2101c052018610a22084156100c1c1c0780080c4030741d0050045260700040300b1001050054019911700015462000440c5540c076801c4040d142600300602100c0b20703105021340440c07013440314080c51950f500e06524441860714032011403015104001d001c1c0303000c3c19051060700d00c90309044c1000c80010481103800034090f120540100d02402e06030708090018001c540000040204601340c481c81902180d0321400284c88400c0c041114400030790b122111141c158151070302e0540f01001c419005000c1e41413590004046640b80e41698001d81c0b0901c007240d40d502d04020642c1080f50320283e150381c540408010321820b02076880700300c50450049078000c00001c280010101401d40c11a80603020400403540483c440c02104605401c070042c0c00e68295090078081441ea000c04281c207249c0310303816120710054200c401d81100c410660204010100f0034580800a8841440200c201c0046e0141d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 224951393 1250 224950143 224950153
    0x123060f06120709061d040e0106121a0703021201090b0303090d060c030b06131e0e01180b0402131203090b0c0d030e0c09061c08030c09010206150105030a020d020c010e 74
    0x30003c0a070007076000ea0300910a01c04a2002c1075100140b0040044554004070b800054100d07506205a00420403900030384038074010341d00c2d4202841145103003440680494016000170340c0d0781000480507400b40460086a1070752a500603c8030700501e41000485d00c0300502260b0802c1d41600020b46d0320a08240d0589011b5551b003040c40a699050007004040e100a0350302c6803508403801c0411507400111310442000c1e0814601044c5403058009401005241c000d14144807942c440c0421000342170440702c43c03a0254513101c03000d20603060174001d491102e6000c001c0d6201d018500495243e1600c051a01142001a01e01d408aa0958054090440010954002e0900d5454018080c04882d0000141c0e00d0640c01440740d515540d6030441c200c0d504c010b056950300d00078560307002c0e040030815030124003d020100101c00c020410280318043c00d64840245e0890301540c8400c07034174040c207035141506240003a004200203910840c45400400c004100d1080c018504907584065134212501400000002d8100e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 224952643 1250 224951393 224951401
    0x708160303050603011a010f05090d060c020606010f09030c05090a0b090702062a0901050a0c0606060507020109051c06150e090a030314070203071104230f07020123060f0612 76
    0x5d11030b070019141c0b141c11600c0d241b411030001801c2e0b0683d5070b5400c0200000041c03110328039240c400030301c552543c3c440c8040c030041001041c043e4864404648460000da50710400c03030055845120582d003125005010300078440e090030305100c403900005084005a03034a601011045484402e501d500c924200d902a204905000700031080d011103c402c816144481a192020000d0800d82111041403090803c151364114030302d800c3c0c0c0c82c0121448017410b85d40c07900b00c0008209401100800c030b028400d9a500c402c486d1034030100540201c00d141540c08001d0811411400209203a2115124210050351711124542e00c400d180210041240da642d465041680c00c5400c250709400380d0100518010440540c0d450028002036980c01540700c041d0448286801c019450303100c1d940001c08811003150404070403100b88184114070b801c16502d00c001030310b40d9000035140901c1841022001100181e070342c0519060344100703690800300030704002d512119000c100b0b4501e0740c4140003020f43d100d043d680382c407403403074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 224953893 1250 224952643 224952649
    0x20d14090a1e0209270d020102130506040806040605040809100909050f0106081b070b0c090112110403020111010f020c0d08060102010b0f094c140607081603030506 72
    0x290b05003500a003200c49030085401692001c00040e803140c2d150800d80b1103141c0407603180c01001400503003003915019071b0004c06851641900104022900d1301d000c9402d01c0d41c1c03041400303060311a07807049042580015011400003241d6402a50300503004980039170518003158001200f10036450310b40780115010002c104224449402400d030b100440320311806a6600d4440040c041000003080d440994041000b640c046c0d060310400d0b20070654001c0c0307038003501d8034000c0e841d400194003c000b01c40c040369218519010144440c0240a081d03804809641c0c1000c0c65a4010b407003220a8a40320032840d500c0d1310181d0103845e450b01c00b9001c44101c0c10700900a13001c0030680988401030140549045906008080c1d0b12074440b055240720280080d1000ea920390340d426214001c0206034195254200080300b141d00c19031190800d101140b602428040a220f20981c04a103101000c070b00c140f800b0041704000070034107490260003900f5035601819a15282034070301e41d50302807000c08000c0c0c11004207a5807014040141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 224955143 1250 224953893 224953913
    0x207080129040b030307030804080c01090b011d1501031a030f0c0a0803030c030403050a0309020307060e031e0703120c080d021206030a11120c09090a1209120204020d14090a 76
    0x190082d41d00b00040460000800c0d1640324600010302032222480c0450100b0104d48204d441261a010082280403a186080e0014000c04c0c46560810000000020b082c1502310034068003c000c03a24107940c241403030400640c00382242d0701c1d07055a10321401001402c40e890900c60f450851440b2405880801c00e18020171008020b25044000e05038010b00403c0703840c1c045201100c0e0007a4041c203200e5102d10907003a04038007a002524000303406001d19100068200e40003519424000030840070b0b40e14142c80f801460309030503d04000241140d00020341000032840300b015452a0310618074103442c4c603483d035403101c0c4283d03805582c2c25200c0d50707400a060716000c01403800b0070b500400b0840103418000c0040c0c880d1041c0e00102507045110f0804625640b48450b003c100307485500b2070181c15645180b6003110000d0725072980d003000f038682d141e41401d01d404441c03003100f2140503250180100380c8607280301d8003403000a411940640c5070490b503c000d0128403070920001c1d81c1c40352802500404050100e440e10390401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 224956393 1250 224955143 224955221
    0x11706030337141602040209030a0b010905090c010905060901020f070b0a021c05030a15051003090204150308030a110f04120c0605040b16020301020d150e01060c0c0b0a02070801 78
    0x480808400c3c0640441c0a04a55075502201d1410720701041e14000034009100754100103034144109104801004465880f4034104c449007107003082280e0f81c0344c2e420794940907101442800545040000d0041e1700c1c080c4040c1c042900184100c034641856140301a10b081080d402c81803407101e000c00c0f05a86994100410070358800d00d84550743c50b080071900d016006000240840740300c171340c46034012003141440d5042c0c14010b210052a400010000150240c010460400e06a00aa04082c85a038905007141644001c030303540703c1040c603e5039480c100c40340c000b44109130030305103000c1040280f2400c51075494064009010004107a15911000b8074107030000c10703016030103001841000d0000b04a2900c40f1415201842e85200c506290b844982c0700103402441004000030800d80790204034030340c80050440070b000352901d45503070000350b9807240d00030b41d1081024100204903038000d8106002800d041d0020704040c103081d0040b9014682c81c1c200303090135903c00d0000c0d40ba1200008419150061034807510420f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 224957643 1250 224956393 224956397
    0x1506032d150903020a240b0a03031407030306030c0f05010807080c030705090a08071202091e06040216020a0312020c0103020c0307020111030706050c030f01050f011706030337 77
    0x21400c0580e6070391004182003900349a005598049003002c2c18000e000c1907201703c5c0e1140261000150f80710700718500003605448040c6030f529220018115003842e41103113040d241c164075000d40704c0d01482e803824083e50000704120201904c0350400000140f0014187d00a00100d184560010f41440001044100010a0b04003002a040b00380b04c481c840420480340c00c0780c440d281007a40d443c000c401240d03145005da07102d101a840386200010302c82030a03003480c0c0e012a01c21102c80d002070b220303402c500c50112081200740240b00700c0b90000c100d840c0b4155006250201d030402d406119400e0715000226400d80300d41c016240c0301070764203000d0100c0e5814405440d038400b0900b011418002c8600125a913809034070802418002e00c54100c590b03032813081003a1039105500103c14031240ca0205c442801c40d801c1034a501096942e448004642403500c034003441c26900042c1e54200c810042c0d142c00b4164180040c01094043c00100646250511884a4108030880d001c82001d941180340700d07040031102c424580541 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 224958893 1250 224957643 224957723
    0x5060105041113060f0306080f0106060905030303041104090f060216031112071203020c060103050f0d030209130c0e131d0307020604150921020901050109080316150603 74
    0xc00343c032101079100300740c80b038910301181d0352403030b1503015002045131350048615849a02d90020906105401480580c1d0266842d40c8010382e03210141650380c082514010716a4035007840c220740c80c0c00c2652040030494060900b0500b1a81161101c0c4108c0e80858590080910314400c0b0702c2c145034000c1d1158244000f81c20051070800491526072185005403000208444140b03032000b80e44902c280c055134440d8980740242c40030382d41e480c58901c1d40d036070b404e480f10f0101780614041f50060034040d03c20384107003000241904202c1c01105030500010f00c8142e01602c240325074942800c21a45808880040520600c480080c00f449107801e5040c1c5003d0b40a0100c80c680d100f0004880162244001d9900304c0d1001106101840180c0100744c4404e480360308090349105e4403503100b10340e101302411924a014002e1358210b0450741c8800044403801c1550151403004e5004104590003540022801800300c0e0082e0000c0ca180c01d4010b00390701c16240e150b8420785003610140c50190520001060340c007c0d901c4c0e0100040c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 224960143 1250 224958893 224958907
    0xa0308060306130803040f0209010e04120512010506130b030c0c07090c050a081b1c0507020a05070b0702040902130506031005060f150d1410080a0b31050601050411 72
    0x14419030f403003a10041c01000013001103820030071100034801429034004c240810968542c0304500d905141100c0c281d860f01c0c10460072007607c902172400c031014108069402c0c4806c0e820201031180f1030b8800c0f403160090740c02000b0002200340300c15000e140100b85003421075a0350108030710400e2907c81c19800041c007040c90700001f107a415800204458182d007160070041b01640d00d8000503601c1c2e00301c0f1110340c540b040700024103120403003440c1e0310900c6a08403918100880d0700e400008990384c07805082c00511517481003c3c2030100d540d8881c0500841440100081880100c1c0e81c0881c2d01c40c0d4440520603402a195800e01174079180c00d200400e41d800c0180010002464403400245c034010360141c90501901540d4001504520f070f102c1203a003a202142414056a107426a00c207400600480e0f010140900140c40415440408503030f07894880d41040d0b802c03c842e00d030715044a0405a40c02c40742c00b80c603c0300c2206006443d000304009005070303001d0005400e072136140c00240015588000001409030600b00030803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 224961393 1250 224960143 224960161
    0x6120105010b0a08100b0c010504030f0e03070302130e010f06030201090e0f0a0f060323070f0305032a0d0206010e070302070f0311011d01061701060803030f0702100203090a0308060306 81
    0x160709400d0140c903011034903445040c90a03459a41d0390704962546c4c41d0010f0400184001500301501861299640803051004003d0481d5924031007092a903254010400420151030200c0b83c00380e03d451650030009240d0103c81285d0b08403890f401200c18600e88a8601300295a004849040280100c07914110b4510742000b0100c100c44e0010b00c10016181c0e40d130000b500d45041a030000010303580c40044c1c154503800c00040350b442c3e00c564105500300b034400d884000c54a074a00e005044222503120380298109140c0038200fa14014050250084240b010091304480c00c00800285101c00100d40103007100754184044407054081c000c20b848141070042010800103070640c40c0101c6620740502d46403100c89440c541c407134058200301019070b40310303a85403010f0884868194000e0045801c2089004034000459040d182a203580b03106030036607904180001140b0344040302a440d4044d0740c900c1590000015000c0400032038000b40c80a90a65011212560400d9003003009241c00c25022801407030035260038015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 224962643 1250 224961393 224961397
    0x90615021c030204030b13060f0b060901050903010924050901020703120b0a1a090109082d030408010204030c08210a030902060f0408010903020615010807080402030a05120306120105010b 82
    0x1141160140040074036208910941c15603001d10303800b201c442031905100282c0c03032600a549006452043c0b915145d4404006284a010f810440160015080c4450300380151000d80180c03591540554a80a012001446200d12407100c000180c1c0d182c40591003602c42c070f1044800040c00d800450307204021410100c0e4015001c0c4030ba40c10083d00c04512413540101241d104035040d0301007203a4a1182c1d02c45000004880080c0441d9130081e80c0d4201c00a50314440140ea80d031111591403e5082d07118200c4400209a2180313042820500085904e000da888400e68226801684181c2d141d105a1405101e80d82052200d40d02e410b0048100c89011130b19100c2180b42c40c41004040424541c0c0e84050000315103d200950704060010400c460329255140d81c01806000310b010200c0c018000e000019040760601c252a4520410607594144680c0d03615806680d0303880c1c0513005a07810b1165070082c50000d8002c01c035035003020300305083c2151031341400c4003442180c2c25640b10a1245034107041c0140702c1041c236841 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 224963893 1250 224962643 224962663
    0x16060206010927050c0f0405060a03120203160b0105090f0702100c0c0203030c03030105091f0b0d0905010515010e060a170711030307030618090206160809180109061502 74
    0x201107400100000440308a0080f0a0485244201d21024080042402844800c050700c040740e44118070801c000468034104c035020361001d251a030500200d015011038000d1080240100d900d084c0844201c520380e0207400754100d03500c900404c014002c44c01c09050b05a01f007501d54091084a041400000c3c1d1180c0c0361100c2d04444076507504020030124418082544441e4019080d039548030480704500b516903009004080c001c01514000c640354440080c0e0b804041220a103142c01c406050194038485a4410388034210b1307103503c601c000c0340030a1003032290a018400b070b43d60319042d0b040c54800160204840e45003251054030b06001d10035207650403586105030381c0d0641014044640e29500e003983d902500300b000340c2c42071001000f0840c8254140d4404020364024213030b80e000c2e5902004c8082c05039101980001e40251090010241d40c2c0640d100102c0d155204089940c101150341e000b20340e0540c285460000303000a0000100841401841034001810ba00901481030405d103150296841070215 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 224965143 1250 224963893 224963909
    0x2030c0f0114041d060307120602030a060902040905040605010b03100e0402060d02030106022104030305070b07120218090f090d0503090a0c09020403110a0e0c070609060c030e1606020601 82
    0x103104425540e1244444108900741800780382e032190344480610700c8082030103504080b01105400400c240d4600020040102c076455500e0890069440c3e56030320103500040c0c211071071907886107404940380100c0d0000d0000750640d040006054582030409a096071010b074010040b4032810814007154050b54811182640d1001d600442c09882e18404200a0310403205042007840c80400045100c80d0701040301451180b07090815085c0f407461482000f1603104c3c510005000c1903082058a0000e0a141420380e0b00250f6400c156088010080c3c10f101640d100101412640781c0071180c01d00c061400b504040d408c0352402c1604101880c181149036581c0f00391b80c42c1d401c1400030100008804003010040a0309255010100590690742c9401c10406074205001c01c403031079681d01031100c0490a00545503000c440c036400c0c0891305501c2d00b41001d84164000c60080d10403e440d80b0042c40814990f00a9040c07003055941e0004005001008007420099410100e0032008100c2804018103a80007c415054507200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 224966393 1250 224965143 224965159
    0x504170a0e0607210207150f110106030503090a0902070f1e150507080105060c071404060b131406040b090103050a0b1c02130c0c0f050102091809150402030c 69
    0x490416a000c54040c0101ca522480004158040110702051100011102c3c00c20100315140d60700140c0c0c0312a014080c10881c00740140045002d18455501c000368242181031019860294808044c2034a680750015510740e03000140034181800e00f600ea00004080c25401141802070607600e07600f545481d440058030b9090309201041d1403a1120018111050380040c2c0c80e00031450070300f901c202508045520b1804142030b600000f0300e40c01d208080f200c5916551000e01001c9083c00030190007400503841468025603030300004035102c0c001d94028060b07101108070500f220751901038003542111102c0011070003118140030400550500400342d80b030b45c68090802161590320242044002e14100580310b602c4405c0402901a0004511101030810f000b070340c05140b02401d405161090300c4d02c2c40b0090000500c1d203800000420000c010071540c01d0300c07038000036290602603400207410f02818419001d50358400c100744540b0200400c03a8280942004c0d0802403d0310b85030300003a480d081465182d900803208 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 224967643 1250 224966393 224966407
    0xc02040207061d060601031b02030d1e0c02010b0306060102160603020304170a050c011a01020d05090a090203100f120803040206090307080304060512010503010e03040513060801050c0715050417 85
    0x6203030030034240d82d080b401ca119003160070000510750b070711402d07a9100c0c0800d1030003104698565112048c00f0924540c0d0f00218030b030913444c3e007505005000d0821030f0126401e50100041064110340665503900400b54004202200b140d42018200728001e0509415507004a0045816041070105c03181103030514180141c0b0b9071350310300f055103101140c116905040d5200040300200280c00001401c0007140e801d000f003101010507282080300003600300c8250b001d41e1015284050a910440c01006c5489001c1c0901c1c0400756a0030303110040c0d030400d0302d60b10b118121406d0240b00c9401e182a40100038041483c4038400c003030081d01c9040c00d0b40b10140004c0d00410000999040d00c1d01c00708501d000524610040341d075625960080101a60800c00f101500e007030801c000000e5501e4140510190040150302131482e1a140504020084144485011740036403070f0400000c4183c000e2040a2141000c01c4100e540c501d414a13201582810300100c00e0030f4185801e0610000c200c4000003001100341d03150b40e003580c80078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 224968893 1250 224967643 224967653
    0xf030204030210030504030225120807020303031305060c130e0702010212040c1707180209010c0605010803130806150f0109080106091b050c0309011d1008090c04020a0c02040207 78
    0x314641001c0d40010110030b0b48060168140d0280b40f146009a00b07a0710020720b42c3c2e066901328009441c10f0b0250039000d40c018132510100003ca001c40034494108249072525541c0840e0458000319230b940400c84959070f484003407200070700005900829011000c0d00c8c0162a48070309496000c0c4d801615010100100011240341c000d40c11100b40140300a1080c825150a10b40700ca0f000410340920141d002d0050011030301c070307100050444280c40a00d400d142030b400000700c90000030741161012a0400008145020100b5105d110300c134040c060070005541e461140180707640030003100d0352201883d0f60042c01001712054810140026014088400c018080740b8000100c420307200e95001100d46520f0120300290940e0765030b202a01000000711510440001c044090390781c1d00844032500c1d8a074004001c4000c403984610501c40d0120084103070100b031480c14034041122090561884c9003c170305100244050130604000c10f518020040302c055107007203c0c4010080855028400c0240141d030003081100400c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 224970143 1250 224968893 224968897
    0x9120d0503130f0515090c011812060207020a0605030420030a0b06030f01020d0603060605030106030b3c041407050f0108040501060515070303140606091e0306070207030203011a030d0f0302 83
    0x680c000702160a400c0d0700180c403070702149050f00d140c1c00031f10801c54a0b80d103550060b1000450f902d6440c0c0b1040d9900d141203a500310a81c4000000c440107507007000034030016980c0180500207400c054bd103d503102e24280c41c013060300580da0041041c80700b00b1051007160503540050b51818140d0f01c801b44000b2a140c02c0046481c00310ad0711400440e039400800e41508411302603101c4401c90340500c00903c02c20313075036005140c04ca4180307000c09024486004001409060880082c80da07602d01e02400300c1d00803400350b0300c00c25441c07181002c02912016040520050200c0d4001a0514080010141400c54642400154484003c046440c1800013040004080c407a083d400000100009030a034000c5500705614020113900c030400480110b8a885a1800e2044039114054400e0402905c81d07440c14800d90201700f8080303c162040c03081a108008290203d0310284180e0b4041e0300c6580050452606620405d402d40d0100400e503013128107181d0800c02181c0d0005403101c0000d12078141138166951000b0101c01074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 224971393 1250 224970143 224970173
    0x207060909062312011b14040f05090903040e0103060c0e04060b0a1b05010c11060a0e0c01030e030c1b2e1b0506040804061b0c0302010807091a09120d050313 69
    0x15480c08012510a0200780e54401c201c0e01b0303d41e40c90324184110926448540598024035103a0f052584090041e820440f180641092965040f01c3c01c0a0b51107405001c2c6200907001183d03003549980d41601c01c00c2d0003040c070380c901d100b0072038080c010281050010141d90103201d40410403c056140328580b802c010f480981d00c02c40d0042c1c02400507058044000d0455000c0054401003032143c080020b25160340f41c421407024200d40700140c40d41c0d603622801100988012104480c40b40001c00c0b005004090400c160b502c2945d00a41c450300380d6a000c010403880b05814100143d080000c00c0b4819554020005c4e20b00503244982400180614520040205e039061000014600e10800f800e01041c0300c06e20018000700c58880d982e244085a803801440003200c40d20200400594081405100660041101075405803440c505107840995810a051038141c0c14041c8070f007a43c20000d004a1a400c0c5002d41201010031240200003003203548030024036620004000b0100341d4180d071181010424003610400d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 224972643 1250 224971393 224971429
    0x141f0b040f080c061303030f052701030b03030f0301050d0c030c09090c0f0308090d1401060f032112050403030b0409050c09010e100e0a0e0d02070609090623 69
    0xc9507210072440310300c0901402001124880c01e5142c1d2180e18050301110103040300707200103011203032441c1c4d02580c440280344540014024144921582c40d007001424248040486a0340c049048140001600302c03030f02c0c2d51700e540c000d410800803000004940c20031281111401d8480740072540990401d0001c3c14a1a08001c00f2000511000552840380d9049001d10502429a5140b0565506c8002c2c0e109442e902c03000f48210070034003801c081440c01d0700529000b80e0103298010380b43d141742c501d0340b421110103801c5140c90850003201072082c05001d01141d642e0680c000c0703d07031a4100750250007421040750300340c540c518991180001010144240c122500d2201c1c0548203200c01c0060745001c6440303564001e111400741481200008224001481c0d03913000345e101c14040e074103850400c0c0500030424401818107801c00c0d22109078444002041098400d800e540d58040c2c00042e00f003800080c42e558252388400c04284c20030030203105031001c85940c0181a402030307190f400c80300c940101103600303403c612440b001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 224973893 1250 224972643 224972647
    0x4060b040507170105040b01093c06020708010b3303040b06090f1603090c1703032e060c0f3804050c1c0f030509090a141f0b 55
    0xa6854200b10043c0b0b40107114143c02d01560388480611003110180c1115500048540c0300c2004000847e02e803c03082031010b80942900500d01016401a4051040a0100720851074908111095051100c1c10140c02514002e0280f00ca200d0300140ca0303042d13a4000b10320628020034102c0002c2c41500344200202c440d80250903100d04d09810f04103400c1004070340c200e0060140b440020240f13440c1000a9100b40070520840400d1119800c00f200205107400048880e039682103030200c0c0b4091039405420190341c2c00e8004580d01d2078501206200311801c00c1c8002c00048200c030780c42010441415070711081d9165490300b4000c0c5045400d00b5440d240510034040c1c00002e0f00740513505810729001145d1510414805034403072110b5040301c0348400480484019119400040f60520b01d0300d003031000301d500164441d084070010306590b10381011121044500307c000c11070000308001d55040c44007103c4c2d0701801c0b44408004145429018603030b0100010050040c0968402c2070a208000c1d8858510103001c05c51080c0d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 224975143 1250 224973893 224973901
    0xb150a090f050106090918030e0307120b07030b092208220e0123061e0a2601080a060c030204081209030601170d05090f130506091b0a0804060b0405 65
    0x18000705028043c00001172040000481d004095014030403401b07441587d200e0f190b101301e40302294012641c950140e414003030004005011a410f1140c0740340e680c081c4030b03c02c0031130904402c05803c569488101600402290003003200400c1082034a0f0b581c0c0d60f0336603401d0701b189954a05141e4501c6806010101141d018103559200404808442e003a02e02d580740038041030742c842103814807a100d8a001035405440b03108400040781080d0000d0003050103920520034909040070154403007500080c800000180c00380b191440c02001180140c1e100240100558202e9410640c00c140c81c4d0380707072a0001e00003507200c045101740300f8402d90498000300149070a80c0d9040d0700f0a036021015900c003014081c800c1c459a400441c01c2400b220850101c540b80c4401864a000c18170001c0d5019005240c000d40c4c4443c18000b410940e480344280068502c20b10040091145059420003a001d0000740140701514240c2d1016120300395158210b0f10001c141d82010400c079501d52901c0d03405400d11100007500681007070140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 224976393 1250 224975143 224975171
    0x70b0414010e030c070504020d11070f050c0105040b03131416090b03010203090712050a081606050708040302030a0c050712050606100507020102070509130c0e0601031104030b150a09 80
    0x300d6184240e0800921800388204840c940d24001d400007005560808181004549000d03401070004803000c0d180412642c2c14940e0b40b010b0768109c24030a80c0c041840d44401e008014050054440d01030302424031504240c101b4000c005280401030491f0b00e0101c070700000d0414084c00c0f00c0c010701241100011958081c03000503100c2e00a8020344035910b04117080c0b10b800080c52406009481c4542190b070020000c1d9031408001164414004205076558000e11180c800880c0c04200108000608030343c030268450550714002088032402020306c1c1c10006604203010001c4d5011084568010700d0349070440780500d4900380281000306a5010030007001514000b001005004110240304807812a00042c41000d8500280c40e603204a84000740140c0008009110702e24100134010780000ca603812607a04c00e40e00343e880c040e1220003070700190f80524032001042269a45801070b01090034154504a0900d03155503a00204840040c0860840b0070140b21480f15944076103800e140102840101445140945460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 224977643 1250 224976393 224976413
    0x140d02010b10110a030807120606020a020a0e06090f1b070b0601020f030304080301180204081b030606010c0506040f0314070b04030e010c0809010f02011104090f060909050a0b0903070b04 82
    0xc90b0300400060420590300c80c040d1040000200e02038010b4407441c0c42d030350340855403400010600d0042c011510035044480790036100e03140103010f90350010043c1c110980100106d005a0780d0000c00d10400d51000c2211350b4030340d17498035a049450740140350020303140d01c040c1103524840182480741904002c5401401d101c000c05800d40540c5c02a001d03100040300700010a40c4900c4200c0b8054840c03c0100300401c46500c0720a0900416204044010306094480f60a1400e001c2808070141c2c0305400c10302e4004035450144205500110242811821181e0302e40d10540c81d004028400b4210000c2c0c030107111b0615008045540d0b442c0b10000e480c1e650b42c038041c6041c0c49a40d509440a8000403665800d640d5a0350082c00e03174041240d0000f04060600302844011900c41110111940842d501d039042e400000381d0440240c0054445000c02140003107440c0b90705400c0310a40d62088180700c2c10007400f034021410104400001d142c0203031403094203607554402503186200d960300041c0b810128038100010f00c540144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 224978893 1250 224977643 224977661
    0x70303051506030424110d0509010605031c03111e0408060702030703080a2c01020c010f09020f2701171923070812130e0c0f0304140d0201 61
    0x90641c1034121000e2005900040b20700a104001c9020700e40d90b0400302d070100180c2400c04070804038144042070444034040e001a8060900552140c0520044140030b0080202805055005285040441d0300c0c0301415000f031880c40c0e00b031507a68000d00e84400e89203000c454104030002d91281c000b00b003000000c01d03a94028801c2c0342090141201080760684040100ca0b5029095512401c498460b02284d000508000c44158034041c1c0f098500f81002c0d0005641c2800c40390203a00058079001914100da00351024060303901010b601c2e004840c0b00685e01e01d10b052001040c16126072180c400c45081d0140d08004505402c0380b01d0132884000a595240c26651200c014407550a6500c8501000c034400307440901c9a100a00d4448081001c1030000040080c0312019001241128070b101d5850080505024411600b00190000050720f02402100c14800c000101254603840c20285084040e410031070050325161a00e410002000c6000d20100803044424901d8880554016003110b6030064000c00640c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 224980143 1250 224978893 224978911
    0x10309030332090714040f0b040504050106060f090e0a0b0a09020d06030215030907030b0903160c03170a02030f07060609230105120705042703050702011e0c030c150207030305 77
    0x2c00040c0380e8440c04100241200c00c3d0010345c480e603210010801024101c65038110040030b0303440d20701c1446941c43d0301031785006a000380300014180c0d044c0340b001082c040c442d810860611000300720805c83c41104002c031540c003140b200400106540c02c20f00242107629142d001c0142240049480b800c0d200503607020f041100d200300c1b24110080745031500e0348414001120003640540041808002107542e4803c02e9031b00a42c40820341e4609183c2c000e132200060300c82441039580c903000c0c0c1010300800c00c884d480d00d000079608202d00e5042100e0550300941c0e034460b0038201e1b08185000720b84003042040360340180d03002d00391540080c051010942e504d554410340d1000d00c940c2442c1c00c18000107840c1001c03810b10300e920102d003000e01401c030306220600015115400e0600040000740300e46500f6241400645020140301e950340c155501e0a80c0001407001c01d002d080011480401c040f034901d60768000c01c085007141d606052004000b851403c00340401d2441544a60009000103160400c240d4236911861042140e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 224981393 1250 224980143 224980241
    0x60906060c03050901080714040815010806101502070902180f01030618051b1902011401060e2e021609111c0908072001020c09060103090303 62
    0x514040750040340708003002c0c0100d4000c0000b01c2581d44102c13401548000715082c560f100440d580355503026980035510184c40380e0806420328203040c0c0410345050040407010010842e5052140340307071855891600c606030790648002c0000016078020b000c00f1006009019086495002400301c010304ca10600c0c281c0c92095030030303030780c003800c60742c0244103041c2a03c64485828005049550525000b400c0181070064040103110347e41880148040080c026441014100b50304032000b10006429580e03019811282c100c881401441055406841a80b008000f210350482c2c86213800c07106260500c205042200c22a5080f034104400768000900000c8035550700b600354507a56650502d6001c0b111214800c0d200840b0420444034420001a20f20000c1c400e000307800901c03040c9a07522076465900c8440e045540b110110401d8080107502d1b003c53703010345801e0010b060000540000100401c0c0c0c02132030241819039401030007090503c240e02c201c031040d00c004004042003402c0c0c1c80c0c0701003040180107450450100703 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 224982643 1250 224981393 224981399
    0xe0a0308011706040302120901110d03020c060c0f09040207030c0515060a05120d0302071e0501091109070c02060d060f08151f0504380a06020d0818010b06040603060906 74
    0x803e03d00c51368140c0e0140120019224407150340341e11440a081c10400d0110542c00441018004109441c8441c0c500694a0314120241400c0080003842652080703014441c0001446210088501a0000b2075005903200f034245002e84000501c4103020302071f44614002000300d000303000c91590055204581c0305d41c205540700100074449401008920749034001d4042369070300d20302a4002c0c0005038030501c0040ba460100444014140b00540410760b400d0b9103c480d0301003400702e1144146140a02601c5a41c41d81c1b40440b8064028132071640c0003800b8900c0028050b00c0d01c1c80e103600c1100640390810b0014080d5595440e0360746d17203001100304000f81180007000315a40c1c00c01e00c1b6000441c50207980040241a02d8a01000300805404029040c0315403020b404001300c8100040c0c0c0e0031034880441200c80200d40070818030000440c0c540002080d5845100014142c5401007602a803055545140c201c40700285220980034240c0c0d20205600100007040218140303070160020002e0781e144610410289035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 224983893 1250 224982643 224982689
    0xb031609140f04090201140c01050a0b040c08060f13140a0e01051b0703020109060f0f1d0a0b04050c0904031106060d0b040b09070f1211151902010e0a030801 69
    0x44001a50350040c645110b2182c14146904205545401411710700c2c0c20300045400c41e01c80741d0150078082c8441e55540200320840c0314a20803070b52445030590701040000701c50135014040b8240a00903504c24080310103040030641d80d826160203107a02080040c0610b1000c0360302d40901d000d040d14107042483c01d010710351003442d0703051185e107201c2e101840a1180e151401c5000032980c0d0f00c100400c0d01103540b284000004101980111044000300410014140c416060070000b11480300c142c2981008107030036141c01d02c10001840104e040e4210711401000c3d1a503180c2145818802402c803034005c0450740402050581014448074101194070a8889503542c2ea4100300ca040f0107030800401c400c00880c04500405c6501c213503503034800610800c513040e80da21707480360b01c0a8910700e40c0a42f000501441c0c5c10b01c1042110ba4680c041e0a8059a1100100e9409940c00916018062001c08100e60490500c4851031007500584030140981c81030320140d02c0613043c0204511b109004040040300b1a040142540d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 224985143 1250 224983893 224983919
    0x2070e13020a0501050d020d1a09060109060e040c0e040e07060809120403030f111b04060803040807050f0a03060501060c02041112061924080105030f03220b031609 72
    0x26a0090484400d1802c050040d02c064024407200d446c460703400d105c6494000d032240309903000744010b0354021105000c00403c00409400c000e1815041084402c820409030750407003107071001c0c0f400c211000704220081b50011501c42c4013410f1010340c002c0c2011400c3c4651000420b0181c2500d1055030351807010307614501041c1e0780e41d0791110000600102041b04001280c0f1468444203c2c01051030006410503d40220b0791400c0000400701013000d0310340a4a500a01d850310425008220790300c095400e0910704004281c0303800141c482c04e07006206810300800c01c1c0c5d6403005d142d405103900003030402c0b4a5071036240080061074000310490041c0d00e82907058400e012002d0655542121a100d1447c0554500d01403114503003d0420b28805401c09407030100703e1aa6010084514140c009914a9803202e440001014000181d101900941200b078000003100340200484e000b000c0d442400c552424840c020641020b820b07648a07807894113021083c4075003006160b1301d4400319101d907500c170300040740c031031044100740f07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 224986393 1250 224985143 224985181
    0x120307030509090601030b041a09090a0c2114010e0c0402181201060f1e0f03050a06021c0504050f010c0509060706050c09060a0206070f050f04030312110a02070e 71
    0x400c4040c0500080303440c1c43ea0009a102406140218031900301001080542e481c640b80d480100d1100d00c0d0103c1076081c0f00c00c0480d84100c44c9402032964425a49662114100300d005a0404151409030a03c1d20481d10f081104400d6000001c0c00e02548110b1025000f080c0c11100d41c4014024030400d4502071501d4001e071801007800e00010050b00c8050020488200031402681c880b82d500c03480c0004025048001c01001020b40e000001c00000302c10588007540002c3d03422051100040200c1030012540009514074601c0c0d1011005a640c0e00e11044481400000d0a080240c40d00f80f5040204109000c12030409040d04880240f0030506c0c580c4082d20540102c0c602583c00c01c0c028000440800d685800182e08010380901842ca0701a052000c102154807052010016a200e1001d0000059204140200055891814504042c1c0040840003c2e215030b120203010000d42d500012443d0b940c65001c0400c1c0500d016600303954500000d03010303484844501c00c00020074201c90014800c40880100c007061 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 224987643 1250 224986393 224986397
    0x1015030c082707150306151b11040c051207080f0a09020406051e030f070e04030e030c09010807060210020f0a05070c1e090c0509011e1403040b0612030703 68
    0x310781d200c51403a08250000c2420301c2e5609454418403554410520082026140c1c2d4a214520341040d038a018064850a0340b28512035005010451040b0b544800412003580078284e203c08200308a0400b25a481544039120380d0144c0b40007030900703000da0444014042c4543d541400f08840d074a0361401d88444004030344c8240c4480803c0300140e10528140d01061495100a000055164440d0081148880c0e0425000a00e140c1854165902c6c50100205440340c0030043c020b050803070400502c100c10a002034001000d100c90700d680c0a0b80c40d5001d0081003082d01e005401030006681d1284100d645006074070689015001d000c00c0c03403400b0710081c001c58290813000c803200c52a00c0001c1404a5044e8440c40007500c80d55a104e201040481902c40e158185801420b00c1b0749005040043e034108403000d0645000038454200034843d290b036040300c0840c185401600003101e040c1610717135041d5440d4944503c0c02c032a0f10360000c10001003068030011503000382015a1001d04450743c441a543e620312403120046c2c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 224988893 1250 224987643 224987657
    0x10902191b0b10030605010902030103020f030601150e0a031208060a1406070b100b0729061f02070b0d0f0b0a1d060a09020403030809010b04111b0a08031015030c 71
    0x404501c100036a1a00f100041c80f400030390301d541780c0300c1d0340480d0f1080c1c20040041b40c0003c010015407a002d100c010700b00500310058429075140c0000868441040c9504000f840f820021103039840e514043d0030301c000d6421030303208011a000d0190082800d0000c0726032a105284e100400b25040410303241c2c030751486501809041c6040c216403528200e03080d00611688419079604004182070356140d0286c44002d10808640712807034841c1c0380c4201b031103081d9480003040b4401c0c4020441142c1e00c05044841100d00c0c0c3d00c8006c0c000900e001c08a051802a41024096544c0081e81e92045441ca0b402440d200001071420031030003d03110100410048076200700340f881c0c0c90303114080c61648614401c1a4001d14020400c40d8042c1c0d80320f2074030003a60460303842603010136205020451000002c5c000c0d001c3d0741c001210f04120090510910300c100c0e014140c1c2d103601310b008125401d0030f114801c00c20344c507440790004001500c0c0d180980c11184002101d001e4060088101e4100d0400603001c6d000319002d460983d00c03516 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 224990143 1250 224988893 224988947
    0xc06110d050a110a02120705071203050a1d13020a030e0105181e060403120b030a0f03020c040506310906060303090602030c0703060c170108011a0105090307090b061201090219 77
    0x5002908074a0003688c4900400c0d00010300780000300304240c00c203840f0391269501da010030744000d44003030000e00810305140c00300140c000169a4004801c48001c0c044000141c540312141130403801094440b60607104c0b1340c070f05000e010001c00107044a00701d0021080c1101c03201200c04641c4130201c00026003030f800c154014000701e40001d005a01c000c480e201607600006411401200182c0740c5854808195000352030f040e040028075905000b200751450050b982800749080c00c2010030b2030b00800c030504c80d0624201008a1400941003820740e070301741d80c0b100d4042c441031a8034200000200801d200c214040f0701c11103000109240080180c4440031040c40250031420310f103171a03510140c000c07030280c5010400081150042c620032904a180a402401e000081440320085110341c40310640c00310506108060010040f142d400180c00c100703503040305102195140d400300100b44240111001001c0c441074600000c610054542e028000011641342581090305106105a6803500b00c21032449120881c0b284c0b031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 224991393 1250 224990143 224990173
    0xa050303070203191e030f030b120a0305030901020c060c0d05070f0914010509120604030201050c04030c1701020c031c06050d080d110c01090302010e0609060906070c06110d050a110a02 81
    0x64134490254040d200003008040811244c650813060480c0452942540031300001d0f810b11510100c040c0070390303007030400c240b1020810390360b55400e280c02001c0100000024064090a40503910180c203290102d402c3d5040c4080007403001d400c8840e103882c83d20300e803030002071949204881400d0881c0603620780704031040c205640160406a90903c613418004104070322100d98840c00c1d000d0205c0344403007001e4403650405240c000e0a40c1c00c05000140c02000501040c0003245042c02c0000c229000901d020341352180512804c3d019014035031200c1e00038000411800303000c001ca40b6416122079095041001601d407500308011191030002009010140140461030014806070320141e0a5088a071441c2e040030251500d090940da000d010880060b519036a10b5070316208204401500000c000014242905c6c0000c8e06a40d110b10042c03590b03042145c00e401c8001480115484112400954060503039280480c026010241c54240ca011103260718100140500c82c840d0380a507040000c40b6070151285010b60801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 224992643 1250 224991393 224991433
    0xf06050403050f01020a0c080f090907080a0605060a0f050d0e0303250c030f0e0a050405100806060d021804030c02130606120b03030a0f090e2a1305090406020c011a0a050303070203 79
    0x1c80c0355958270030017120700305030381c1e06aa42c2d1144010366130750007051420410721400c0d0340c640c0d80090700511052200081880d004900c80400003050301e441d940741caa8101c00d20000d450814030701c2585000010030311501e40d0340031440044180c0c4d4600018400381009204032145800c0b90000750000320040f80135820725219071511240d1540007411941c040391103100040444206580d90103a29451100800c6104000d00c24607920010442d4100039204454000c034506c0c109851546040300011800542050301455008003d56006404d24110b840e038481880b0042242d07000b01404100032441d003107a90943ca01400342c0c43c0301c018002d1410b110030950b060700e481d18a0402c84050003c0c2c20400316000c2c5250365107900c0b908100040c0b00030303c0800464915105006504412506c03001c1280411418002c000f45040712815907140741a5619810850000d0142c10449c510550800c407441001141c3c84980e03200d440412141c0710700d031507a00c100f0190b8a12801324029015001140ca031403c44e560301d13034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 224993893 1250 224992643 224992657
    0x3050304061b02010b130b060d0905030f190e0906100e04020904090503030103020f1e210609010509061e0c07020d0203030c06150409050c0904020a0f06050403050f01020a0c08 77
    0x101240c44002c0c000303070758102c40107a0038600040c4e54900c0080c18502d80704007099807030503a8403020041c2650381e038041a4030f03204000121801f00c0c3c80c0c1d11000c003004010000c5517051405c05071100d0711109801000c51801da40c15022000042e1000300326081d520700200103602501c0020984401031004960940d6544030100dc0d035035210b98280701c014000e890701c5c05000d080300e1203280615960360441c41009030b410391f0f0826143c05000ca807400d50f02c0303440160740b44107105034003104c526011180c0400c1d00d032180e0352842d818122501900090002e016015084140141030000c1618003d6407298807403420044c1e8040401040308602d40851880007a283c01000c21600161241020300702e55004603146520410500859a01040402c0b901d07140898202e5141103040f03d09200d141c0381510b42660361031034415141d00c50040e00000c101190f4030002100c1c0184000c280844a903640c440f009003050f04980700c21344030360040c04030f991100c8006201b11100342c011520b44209403090798840c107100d0341142e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 224995143 1250 224993893 224993903
    0x315061c0606050d0807060c02010b13020c070f1202030606040e0d031a0303030f070306060201110706021b10021c020406090e042402040305010e0715030b0607020904050f0708071203050304 83
    0xc2400701c0c4a1321600484401c03680980f00b441d03500c0c041e501d000e404940441c12640d0844e4504120014941c2d502c1d84d00e100e40859001d40507868070001e1006034200324982e07212410f10900f60100203901440208444d004500890580d202c80d9140800c0c0001c3e101091116101a0002039480303120a0083e44840581030014040020340c4140d04086807450388165000038400420004201d1141c0c1d040c082d003c05032200e88000d000c0c98950407410700440c000d1038001031080381c01046052400007422054240810580b00710340d05800305407000002503200454010f801480307003029800c200d00d103008641c2101e9181d80c501c4a024501102010520310190046940415003601c5100b48190a100c00300055501500144c0d940d01e946801402c603080fa0000b5882c64100c403404104144001501d080c08070450304002c580d410040d0005150352142e00c00081d44030b400701050000703015001592a5040c84960304641c00f950719076288940d51841c034440c820500c948860001d00103481007000e036801a10603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 224996393 1250 224995143 224995151
    0x6010f050919120501052e0b09040b0a0306020310170a0303020a020a050a03031d0d02070e06010212160b0c1813020706090b0a0c0e09130f080d05060315061c06 70
    0x4030500d0b0060043c502d002d41c4c881e0f44810070320002a1030345d4509103034118445206103002c1a070790307452112072000b480f90991054010800d43c4180d04c0710782000901500040c0080e40440e2289400e4000350002d4a40605c407020305600410552a103031403108404010b40000d1030429801d5034100c0182d4031510200301103004220050001600070401c1e40e12151003924007146003080603030101c0c6902900e070b0300741403198804284120aa9000700340101a1041c041004540d83d0b24100140c0c5000000082c3c802189000550041a14034171042403040358070607248400300c1e4849003108056800f4110300200c8028100314103c1031032501750402c2407500121070002d400c080d040c0c0c4502040b542c00c0c03a42074038425025010018120301034481d40c2848101070030174980d2070350b8080204200d014000d0140e103229100d82140c905221003c90004a425484011380307641b8a003030111540134000c2906e0036400703031140301082080c1206101605100e554082c1c807035981e4032542c1504210701120003e069500030f542d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 224997643 1250 224996393 224996399
    0x70203010b120f060705030705031618090b0909241015080f090303010f050105030a15080f01060e01030f02010309020d020a12030215012103051303150506010f050919 73
    0x7071512128036245400003c3c00c594100d070000d0742d0400100820707050030003508000300548190000c042e02e4000d00c030180074034452040c20409965988407008041071210b43c0000005000e4030f20b400c00c215074182070f900c80300191150302100340c0d5408072a02c1d151403040641400c901007001c070304a1645c03050207580c1d000811542e07083c1480c082a03041c0380300c20000d02d04408004c00c440c0b11080b6103402003190001545598036000c00c3c40040c0481c1e006042c100700d4000301180484070b20390082e8050303c900c11a820724155a40c038580d640c03a039078001c0102c01c650070442d00251000690300d01a04894000c08131103500c002d650700440007441040f004036802204003400780050307224120a0409002007110b210f48a8025040117440c040b11201071004034500c0c900180000d00001c1c51594407a0070714200040012014036003a6003071300680d40044116682c00740c1c00800c0c021710b92a40e261014040d10200003c0c0c0310701004481c40c0030f80d085000c0100380100002d9849090800d4030071800d00400c9502c15000352 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 224998893 1250 224997643 224997649
    0xc03070c060606030c0318020604050420130503070803210408120103030e040e0601080307020904080c0a0c17010b0f06091212070611031e061c0302010c0908120f070203010b 76
    0x1616089640000e1399a10a28900f82c0c140c4540340c4210701e1f000541a10000c16030010300f4611803801100c2c000c0e034803480219004140f402c0243d40859000c1c1c90f081e12100c51440624525005100d080d2003403007582400600040d01001b1282c50010808803054141c15135a820182142d025200310b4010008000015070644000140c43c043d52080d640c042c1e5001d84681003005845103459070b00380c950030120041001c0c810000031190800d13410741e84400c80e6515800e01c010940200b611540403400764012050402460303452820031390b005050707104040b00c0c045a281703003200e2020322030316040b174900f00b691002864002d028100310107009000d510100340100c6004d007003e95401002d1810b0300c0c041281020000d42e4002c0c42038036411200124290302d01880385c9039a641c0003805044000c21840007140264699203170300500604d5030000040b8a05803481c00034001d1100d00c02100014484050200321810017140030191082ca44400500f44820780321100135070b03840060120380c15980c1d921400c115031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 225000000 1107 224998893 224998901
    0x6020601090b0105090d0803010518061c230726030406030209040f020a020f070915050613080d17010605040e22021504080120030c03070c06 62
    0x401c00181d070750303214031007617a50011034420510040c8440c1c90300070b50407a40280d407007845041e0644e8441c12100001d48499a0082c40d1001095600c00300c401d4200d03009000744911850407018007445c001c50403034081143c55640040e00c0c01c01c603140070080303180d21071003000d525441030040020016440b4491806178074280740c1d000c100001103480350391003c0c0b103c810841c41190b0341d03505c1e1000a555140d8901100c9401d20804802141006c100d0041454051901240c1204182841c0070030006400c100002ba1002000901c00110107004114010b900c0c0055140e0b05c504200da4800c2d0208580140c03c1441448802c00c01000060704104d40d03103a001022070010001061100000d21101d0090b1001a6102008003180c00340800d40d03c00400032509400b008001500c00310241c040f00118040340c01e40c0240b8103100040101c4401c1c0011030740450725252030bd00304c0860341d58903000c907 = true := by decide +kernel

theorem cover : BRFrame.Cov 224820143 225000000 := by
  have h0 := BRFrame.cov_init 224820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 224820143 ≤ n) (h2 : n < 225000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
