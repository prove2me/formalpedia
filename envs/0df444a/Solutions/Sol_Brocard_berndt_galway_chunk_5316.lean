-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5316
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:28:19.376493+00:00
-- url     : https://prove2.me/submissions/1fae5a7a-1641-4bda-ae2d-c40f7e49054c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 955935251 ≤ n < 956115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 955936501 1250 955935251 955935259
    0x819020f0d05030301062006040b0c030417040b040f0512120319051503010c17070c020307230108010b07330e030c0d0c050a0f0c030c290c0606 63
    0x2a00c0051940e415841d041416800001c0d40d46030751756080d02402040320004070000e0158842e0881610120000320302d4400c0360132088440294450340b124442992001d4010b80d500d80f180c003410998460904018001008900d03007030340e40c41c1d03e414503903000c0f40443d41000340b02d0030f0415180485071b8030008244036894064041a90750341c039000511070000780416004c414480c100407c0103542c1402c0c05c000310107258164020310006d1078224084650942a0329080310144501d40455140381c03190071894040d6101134200e0701c4017030f103c0c02d0843c000c1809102c00b00c55500ca6030880101540c6c00f4403c1401403040c0248242480e610342d4500d0000340445016180d02c0d403442301800c0300c10080c01c2d042800e81c01c034200300b04038081c1c0c41d801c2162680c1c06110340036161f1184842d040c6036540b20301c400003003a50f0044045c0610000985d680e42a04c8140882071b24030302109100070001c40c0308510104001d06519030f2402c1c80301200c0308051141d0102024100a0560030701c00030502d42c40c003040107540400202e03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 955937751 1250 955936501 955936519
    0x31008120306152b050c0703120507030e010216260a12020f07030c020a0b1611151204020a060807050328060b130824090c0405040b040606081902 64
    0x2d00c1c039901401598000f2406901c203011400740c110581c40c204408a140210034005c2e40e84807000705000d84181c030740060028060f4802508480110390180790040c003a4500030451001c100380080c2039810446a00c41030011060504c010040410003d04008800c1c1c1c021a003002000035a40780c40b0b004000b42c02c0d0500c80703031265241c41902658111200d500d184405c45407200404d01b030081200b0307181141280a8122100c010603a030351040160b5200d8a1003000040c0900419502e0781c0a850000c0c1129400103421130002c008501c0d4030b406031144030088040604245041e004010155640e544007409024400060014296201040b00c0e40074145440080f0356502c0d02d640340100044c2c00700b09608042c540440451039030218030041901003091806220041d84400013140c0310b0583d000c0080d1814000001400515041c2c1c00e50f41e4840d0030f000035114403001880204044d681c0481e81141e00e2990710040004103c071324440c200c0508807144c010018450b8000071444940008075010748210581 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 955939001 1250 955937751 955937779
    0x3020309070e0a02311a09150307082d1306060810051f15030b0306040b091605100c05070306110c1902100c1104050408031008120306 59
    0xc0124000900200078101058544100288020341141540c10340440b142134894000100c900310801030450412511720706141780070059808009202d1442c411321509000d4145c1d559107100a50821030020392000ea0784e890711880060580e04010240103812408035071481240c2c00024030310308490088000b1101030303180e00c18201d0941c00c10b51030041a460400101103200380000c11050015040d40a0a10043e12210964040c0505602c0030640301003001c9020407071a42000c0f4030801101440c1000111000c002001c00c0c140f5001716415541c4400540c00e0040400e8204086c00b207045821075060703c090f0924000404812070b9204003010003070004404014010103010000045502ca4810000ba0f540c02604405c660031603080175009002e080002c070505100c400360010080d40c001d0100f01c00041c060001c3d00d030f044080c1004d40340009034074000480c9880d6803046601683c05442800d03186e140c5a02c0400c29030303809030402d0100c1d4115045040ca000000001d0369081402115596054426 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 955940251 1250 955939001 955939003
    0x323010f14030c030a140706091a09120d0305040c0b16060b032505180103030503070f110d020606151602120c0a06090501020715080402190f0f081908030703020309 72
    0x2c910a0f5505000c0e000344001002031000710085041802401d5501455403050241d03030401c00c42c442d680c00684e0441130700303c40b022098020041c2d020010082c1018200000302c2c01e01d001400c00e80200800da4460922052101004035400201030760f1941e6890003440c82150001d41249204c0100901c3d03e0748082119641c09101040d2041003d1700740c034501c090075141c9140090111310505004000d44aa100304819810b80c1490580b9050f444141c9582c40b490400c0f225083c0e460f901004000c00c81c0c807400c0030000c0c14441c0f0b24040c1c19a03801441d0604010301046001c1035030f2200d0b0ba80748135080040d02e01410191a2032411150100d0300086480c182e411717520f081c003603c2e16000e41e200e414004089441c641002510094802c20380c07c0381c0100c0d4403695283c1000d81031030aa14049489500054010710303001c49618500003403002e019079916030b6101c1c07000c2c40c1e462a80241c00004520801072000d40400c001c0707201c02d240c403210b01c01d0030304205440c0c03110356220180c41c1d201010380000c00502c54500c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 955941501 1250 955940251 955940263
    0x20d05011808120105010c0804030f08090909031201172d032b050f0f040f0803100503010f0c0813080f04170606040c090506180402030103030323010f1403 68
    0x1840d00303021985454a0550720036408000700c3c018404840c000821785510803215925020f9100c0340440c602815526007402c80d407401c0104030781c2c49800304010701040d01c814420138001c40950300115286d102c00e040703d480307010050b000704640813131140030032049034030024008452050b42108020b01203c1511204151440407820815520000501c00c3c03d041462940201e04002c00035249440000c01140106541003500d4031601c200d80c2c440450000c0c1740410f804c035082482404030880c0040350b55240000b9400c0bc66150203900d41440040046003420f002c2d141040c2d6080804100c8040c80c410003503c010300c041d0041c4001100804848108100c04086070200d01d240e504c11a02e030b990380c601c0410404a1624690510301448020804900740342c0286020182d854850b441c455041805001003500a0010425051116113020f1082e8071507200641c065800381c3d50104011402606400241c11030202510b0100349401c01001100c044034062005d40300709042113a550389503203001901c0c02e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 955942751 1250 955941501 955941521
    0xa021513090905030319180b07170403020c0316180b06070b16030e010b0102060f070221090102250b1b161415090d1704150306091107020d0501 63
    0x1d0710342800b040c00d1000001c044c40c0301d000c4225480710355820075440803080c1c1d17400401e50611908104004000a55000c0e42c076a40500c4074500301e1140c20f550110000a900b00391350513005a000034191003024102400380d840ca03101c41c90180c0d4400c529125910642c429500c40c2c403100e00e581d40f1030305400341d038401c01254155900000380041c141803c4a0081c07600d160034035040e0220b80780002c42c3c8c004505c107016203140c10005801038941c03966087da00441441000b0482002c501420303141c80c3d06415042c10790000d50b40031441c40c85c5c8807181c26002a00d8000c030403030710310102152042494045900320444c40107840300325805a0300c83e034034504429025041c9074900c6080703000300996410507910b08402803040346d0414880b11618410b84045c030045601900c0403200c1c1d43c90030842c107002800c0242009030390038450141c446c00000c0c111240c03480c580198004d1000c900206101d008480e078103020305009048455800c1000341220ba00140303091040c007000034080c5420cc0c02032014000d0a5204000302 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 955944001 1250 955942751 955942769
    0x3040f0305130e07090f080d18050612010816300804060e0a050901061202090f060c0303160306060806041a1c03170f1b0715090b090a021513 62
    0x25540f90b140e0b540e050300040b200c4000182003218000341c00c184003040071040f14a501c002d48000c0000200c216804100e10b10f011002031031034580007c1c1500c407500242110416a07110300100c0d41000d48690078002c52a40c004020300b2451020701802e100f00640d0407a0703501d000103040391841c8031000b40e8400c400c00e000280c410345001c50001849900001c54884140c0b003151110341168450342002141c20702805480c000880068540e40c0c0a115a03000f4139038900014551000c0540b20030005905501a11512580742c0020081c449242d600c941555000358981c24144840c9040c51002400858005d002910442e2a04c0c0480c0481309100046026414003401d4141d03060b201680640414945040c00c40000d015040e0b044800c07a50091028000c0d1900e8134040015150019011031483da441c21000c0c0c001c03002c01220000a94040141d41d03080344a00700842c0d07100c01801c0040c40e4020081074010940c005045000069443d42010150311011103070050b200c94000c804104040c441ea00302200f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 955945251 1250 955944001 955944037
    0x60e06101814180c0306090d1b023f1c05160339020f03030702210c1c0b06010203041503020a031806051b090603040f0305 54
    0x40100d0380521681607540160207101110320000e8254100d0707128a81020b0009101c0e0b0205025064180d103004012004000b1100010300f41d00000341004019221840d06a00242d00388480c95004260400c884400341e600c18031450f81d40e0003042110845e04101c0f01514500c40381c2c4c441c01d4140c1c2404140084010301c1900c0f0420605100070703525072060300d404ca030041e400801d0400c0e5520a80444290400a065208450000399019210746000400b81c280810b0042c00e5628032401d502200000f83d1800300e14000c00e1200360051041410f982c1c42d226002e81c00401075100540c41d001e41001948442d00c440c074090f04003c6000380d0401001c200c035903600c5003801ca03044520000c1003101d020b155014444a4209071203030030042e0380d648660701c43c0120712902e0044000002e40294041e00940206085c04507501c03403140c071075015850080c0c0007202c00076621b6003805804d8082210890701c102d1000c08043c5000701a1002070054080100002c000c0d2341000c0f4060b0400d031140040c2c3e00d414001d07007001d0720 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 955946501 1250 955945251 955945261
    0x30f06140a0507031b170603120d061e0506091306150201050f0709030b0c1c110c07080d30020c030d050702150a0b040b0a0b1804020711010c060e06 65
    0x10142000f640d000f40020308024824400c45009030420501c0341e074035102d40501070318413006007064500c0200160f501d402400c50000c3c407043c034000100424110350300001412030070a00f0f900e1680c8054a40c13180341c9940010140001d4480000f16a1801401c8030b101204600d480c2240010b022a03800414244030000d4000c40c5c11601500b060b03014203070a02c609503682d960788408076441e50117840090a4402c8407404506a41e003031000421801c2c0f032102a6180504908090106480e0030704842c92510f40c00040001d600c91023803007500d02a054100c05404540d00d015001841291400f00c800740c001410b11329001c0218140380361106c0100410019900d55004a100315141e0f00314400d185030340340c00e000025000e0f17440420342d000384020240d03141030305071598180c0c10024482d00241c2c6030010303620450489982d0f03c01100200501100c1d8102e40d40e0403403420007a000a840c5007080340950f00501c840000203000e412186c40701030b000e02c0c20341c0c9103100a05080d0003500201d1404215030007440140300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 955947751 1250 955946501 955946521
    0x7112506050d33050906030316060e010504030512090609070b0a2f16030210080405151030060903020a0f080403030905030a0507030611130f1a0c0304030f0614 70
    0x60300d10002c4042c8002895130361061003071000040311340b00da16400030482e0f0080c04004c0e1402c4500c035400342d100061103a414613255400c41d48181c2d010740100d5000b10714031070f401e50001401980f1825080203042c4c941462a081a9944410b004c2e019415002040c1440b299209624024103046144e01c1c00e41c4000001401a081010602c920b05050044044c0c600784d2141c03590f6050100c0e54040c0550b1070540c0301c010200d46501c00078004890340d0041032040ca40340500b07800d004c0c0c05140c00100406455143c10100a0348001c4003c294940d42d4069054410200c05a8201c0307058541101e40410207440314901241045080780004001c20840c691060074403030180054000e403071103505c0b820b849075180d00406581e10400240101a030780301c2441031000945e03030342001c030460302c08006c101c1c149841c0001d5401100c010f0741016415417115001004806001d06e210081c0d501182070091030050002034940c0c89101344e0001070040181a5030110412103542e102c0030074a055000513460758101f0071584 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 955949001 1250 955947751 955947821
    0x320070203011b050f1315110c030f06040b04031103040801020706050105220f0219120b0d0305070b0c070602070302060406060f050a030f1a07112506050d 68
    0x264020362030150030000e68440f0b0400d00303540c0701a41c0c0307641e03090030f01802c1c030190258052006180f00c0c541c040000110040f42030311030382c0449403e848200c800c809080515140032030008459120385e1040c10401c4e42c414000c585a50002d400c01c0b000302d8513640e130b4103081e0341d800f5650807a031009100001c0e0005505a041d4054a4030a204280621059a0f54030402000d10b001504c804d821030001c4482c000300302c94682c0a0502440e40380805030030a8961100640c0702604000f2000110700307000c0e410031000e0928441c407020300c0070488200c41d40010581307000304680504e201c010180582c0c000455803041c441e80a507000680d0284007955146003e10f0025280c034415142102c001e4108500482d0104010282c0403e03201c014280c0303011203285072115200d00c2c60716001075407421030790b09009105030301c180300d400c1c4140b019481c0c1c00c6040e840070050614188000e80a1025884030018403900b00300c11004038021030b04175280c410346410a111000006040040c020fa40001d00e40c840c0000712607491500d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 955950251 1250 955949001 955949003
    0x525050604120e010801090b032107060f11070b101a0c1908180a03020405101a120103030c050f0708062a070308041a070302030414031315032007 64
    0x41d981d480c840b48400e070f4540100c1c0c003486004c60b2420005100300348003648404800d040c010700701e07404807412004008000c402402c03210160900028440e05005c824010403500016880d410000f1000c001c800c02d246005096000f030003442c90f1030102f80ba41c0340c1440410094410a01001d0304001061521042c55001e601d00e09614024050000c007485528228481c007940c1155042e40f502c10000e00c2d15400c64040460f4a600c0500500c010001d40c6680c0b084501c070341078191034464681d00f8030b031241c480c0b1207280c03604000c40042007003480030030940c000781d85c0e044079803604000400a446141160074800260358110f06841020400a0340800000d0498025541e0784040209000c028246010200301c051600c581054108841c0b8002407181081c43d41c484e0161501c1410b80000054441030544283d4404000035000300c180400c0c805660a569181c041d224000c5240c0b204c032043d0a200d030311941c40780c0c0130300d100c101100200480c00781d00040130400d603200c6100c07103001c5a4490941580c2000344 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 955951501 1250 955950251 955950263
    0x18090307031e0915030e030c0d0828020a09091e060605040308071103030c0f0604020f0609031e281505280615020109030809010606050a0525050604 65
    0x1880b07012640100e81c0c0c0e0382d50034040e82d540c0841904050382101403c44031202001010740e216a40c60b0000700c21700151841c44002c5002d411184502c040040c942c000103071800c400100340d50646822118400034000303115043c100c1c0940c5903e40da45040e140c4c0c25040c0d1115400701d00345805030380390f0300380031010341c95890035040c041100350b0322150100c8140c021800014072104041007207502048900005c01c400d082e009007101d203400008580a401c100301c2403000120f990000091004601c0c0c892240401644160303485800e01c603610001940c1c4d0002404036103401221090f0418255a0030b022106510141802034414409048107080c922919002d043d00c4007400244440840c200c0e41c02b9890040e084055003c003541c4024202d00881e43c106034084230b2803582c40000150800508084112040781034000145800b02820040e0501500800079030b040d9251400034025590814140d61500c1f00c40c0c5012911500d024840c1c0b680400503a0100f15103580d9140050100240001c6452056200f45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 955952751 1250 955951501 955951517
    0x140114071808010509030906130506070b16050307050a121103090706083402031c0c030c02120412020f0315011509081c020129010207050d0203030d02091809030703 72
    0xd910b40f0700f200c1054580740d4140d0810055591030b440c1481c0542100c4e03a03003002c034420141c8d07224005030455011034021031722508000208001d1031501070b02c1c8943e640413818954590703e000e12000789184140c0d601300342807041d0000c180141c01c0c9164004403d000103014441c0c0d40341001805075a641d01035103c0d56000400d400001007000c10f40c0d0340c4005100e1a801c079807250301d001040f110070860b0202154242148020310489080d0740ca8101c4d00035200c048176000260080c0105401801e4800ea25072410a5500004485410302202012541181d00000f42e0f14170740f244910020390481c81d00e005080c0c0c5846041d00f803400c40418011018122055006119035100a100f002d445040c442e1246080c0740d0065040380640d800441464030490506100001d800305075401d0600804210740304480221904508440065130100714210103800100c4a0f503140c82c141d98006603507071092080782d402403600490243c074240c641a01d0b5030385580c100160420340380750080529030f80e40c02a680c19400541a0303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 955954001 1250 955952751 955952759
    0x180d02011b0318020609131103040b07080405060403030e01150f05040501050a080a024b01020a050606040c0513090b040f0501080a0b0903040504060e060901080705010c1401140718 79
    0xa40301d40403012450f11606001d0f1080c580820106400c201c28980d0000c0103c0800c2c7d41c0c6149a00c521000c02c001c40035016100c1c20141132a1405410003030281062110708400d01012078130005106078065454540030401070010a2081d026200030820041c2040348a580440c002d80c84501c9034081ea00b00b6a002c1116a907150b04210341c140c4503110311140b03a0800001e800160030400e900b041070300403e400c4d038004000c46c41003403429640c0525041c12041000d0311030b01e0100c40e03a00c08002d0109401d200414414031035071200e035182c800c0540b005102e0f1703944500d4020458050401d40d140d000e1005c14490001c0e59403543c40d000382c51845c000b03911a62030280c0800a02e4283e12505060315010b000520341c2c005281e441345441c8101030701000341d034841400001303001d82e624041c072000361020050f1070360581854000c0c00002841a0814034039034018400c2030000d03980c841c0b9045552500180c0c80138580c500c08070000d00400c0b107100049001a984010000b600d5081000304051020000b07861214582d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 955955251 1250 955954001 955954007
    0xe15010e1015050a0302120c07050f030c070905130c030c09060909110d060e120d05090606180c0d0c092c06040f020d021204020109080c0108010509180d02011b 70
    0xd40201c0031070408a880e4036658500c02c5004e0712410301ca906005280600040502d40026021910000c42a000160f44420040300b40702d000d1007401920029030409000c00c500a8581c10240580810142d0340c10010b0500702e00d064084482e140c002c40310314500b035202e040941c100442c600949000504140b80000d013440300340700d0105825046003040400c48120002c020450048617000d071412522030641d06142d180a1100100036000d80e5840e950b2080035842e02001c0d910000e10000007034000900300011500c0d040b03240302e403044105141d04a141d840d01d650f03600350701443c3e980a041c0c1e485c2c0030901410503040050303182911101d011540c401000107900c034403680618020300458840300f0001c101075003405c0c3c20604001c1c011500c05030400b0409007043c002c0742c211074540488030071000b05000555030081140c50140444201400001d032400002900d502d1040c491705003e1026140080c42280380450349144250700381c2c0039201c07080300c2424028060030b458401480134048100c03102c070300310f40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 955956501 1250 955955251 955955281
    0xc060114010906110a052e0504021305040201050f2208160b0f070204020c0d0306050a0608070804060617070510050a08010306020a0201060803030c04080607111b03010e15010e 77
    0x60140d4410440701c2c10f101c000c444042c508203202c9400d00c500805240042e100380072000400c400b15042d1440b0070101040540468211000800340c1d030700d08020311001d42c032859040402d442c042040400c503030f159480102c500303200ba184c902020703000c0841d0410700002a007000a008000f010f034282401901d032021143c07211450118446100e580318000c100650724a4040c0101d0300a103459503007480b40d00d402240991f07002e141914201d0b00149030029109402d80b1442c000f9000035034051200900b440f802034500301001d060b490a00240c9000078080001a811450280041007041c00070301508811082d40c0703000314007407a4442c4c008461030281b000d01ca40150703180d2001c80c0c1c0d64105140d1071512080020b40c40b0b030341002d046549640000c01c40450400040d4024851303050ba00c0d03611450841002d04205014000d81c0c00c10903021982e002c91140000d296500382c110030b4018044807807510021f40100081005180c40d809484440303210000b00c0803016040324498194500650b0380c424070506008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 955957751 1250 955956501 955956539
    0x405070b16030e0a12061d0706081b0d0c0e1e01020a02060f13061e0e0a030303051312030b01080a1b05070302100218040b042a1e03020c0601 62
    0x819400740300100344101c0402482403c06010003507101d0f11400724001a030300b65501916800e454401180d01c0794880c0000e06001c0d20842d0142001500f000700081c44540050003400c20b6003004824401b40e10441300c2100d000b4241034000b008801e101c0744c0d0162400d84440c00c014071034295500300c0071155182c04010708140d20141d01401e1180b16032f03820480c40340c02120044500d10424805100583d00c4159004090090380d00d55200d040d44180d00100c004d0301004064042005054200070030f5160141d908081d00d91500700452107581e001c144000c0c982c0306c1e0102406a036000400004807070781603401084070100030707030320042d00fa5155035009082e11244103000c010110050501c6c507003a03104a000d0510a031082c415900080e02c3e0800760410380e0405500007140a010040001c10380c6032511500000000030340d028031800d9503440880030050701c9410341d98218140c03883c000c070382030b403083c810a0130026030600346007219510b00310020020b4003c2108010740b403040c1000031a40d0445c542a0741c02c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 955959001 1250 955957751 955957777
    0x50105060d21110f161a040501030e0115090b011103030c070807030c050d0207180c0c1b0302130207121d014b0e0a052403010801050405070b 62
    0x3a01281d4032003040da40d40320401c401040203c0ca0440b110002c00d2184400004c0402d0003400b1140403101d816034542015400f500c030102020680c42c016544e04411f4808075002420001a0741801190031800340501e540100f0406001500c00f046002d901da12454103000300b03a90b107141007a82003500d0740da244404e90307404d80c0800040c070020001650020090121a2013442c242000407240d03175403140b40c07000310700c641d03000340e0850300040c8000010f8600c1242001e008007410701102c43c1121000d03110304071481000d0080141d08006144680172440c050004681c041e25003256025170041c500000d42001c0c1040307420500642c10103c09500c80d0144036411300c800d9030400b8071011004010348a050226903d8400b040041c262074041c0d4220201844050352006d0f1503000f02e000618102c0d84028842d0300a00c1840120742007508142c43d07410f00e440c103480b0141c0d0003a8004402d0a00c0b08a802c015501100c110540000042060f10f07040d00080d0095100d441100c4880d52526007a172610f01940c00e4401c82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 955960251 1250 955959001 955959023
    0x2090906100e0303030103050d181203121d10150506030109050a060e0702030d06060305090c13021b0a0b01050105040b120a11210903073504060804050105060d 70
    0x21403810365550181c1000600344840341191680200c0d09541090348241d540350007001c0c0e10850741c2c0d0070030609880002d482d0201040c403814103a02c9510010416406810030a400c12450010820755101c0401074604044074210381103a107540d95501c100d0940c48400c0c15040c81c030030a041080601040041e108000d00c16800e5a0800f01140000c03c0e00a000d61441030319000001b03a00e041400d206400b4465503400f49d03940b01c1e42d20310454240e074216400301c0205860801005a2114041030b80100d5110444100e4894009089102c02a009500e09528600400d200001c8408800182c0400c01e5216a0200e5061780c1d0710001541e0500943c070540d03881c010108014103d1402e14030440e5440841c4410015035004503020303000e4143c0100d401000d41404100440303400300341e54028180d103c0c01e45001140740070500c1c0c2d1452880400c0800700d410b80025022080f11810b06c3c9100b4240c6002461501c9440c2c541d5050010f1074414161016103103546800042002820044030000c1105e8120192002d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 955961501 1250 955960251 955960261
    0xf0904051525080103021c020f1e1504030201080a11040501140c0d03021c09171e030a090b33041e020301051c1a1003050d0819020909 59
    0x304064005001c4580b600035602c60002d201400b0864000720101d6649a018660640c0305002100b40400c1c0c00030174070070134401240c0042e80e40e2103008290f030341e082d9012941100e00806010115000c2648540e11120341d421081281404401070822203001f6030b5180850b40303401582c04215418070801c503540210800c018422540941e01c01800928405811443c0c441203107020390410059030b0003400000c3c0c0004005d039092101c1e613125034020b800300504210b008a00c0d51105402e81c44048402c62124000c5500100d518160303442d4090009022402d80e0b0364605049404010103000c0d40c11901004024046484600002c0d08040d0a021300207181e06090300d0041455150b541c00d004103548947c803003021501108515180b01d8400d004144c0c050f0300ca5040004022408049140f5040485401e80c0004007060f41400b810903101c503001108299911140000030080c181c981010b0600d02c0344441e4140318039480311a891069040f442c0a940d4801110f0a002c103134412403041c0ca5010381580c0100d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 955962751 1250 955961501 955961533
    0x1803020a020f060c030d1508030a09050d080f0c01020c190b070309081b07031124030a06050d050604050c01050a140d20070507060801050a0b031806150f090405 70
    0x62030008000d245500306019003144500d9031b40f03c4400c0c1d544098440440005003011084c0358000343c00f80c00042d500b84800c42c08020507075140c910500b84904980300e1a00e0512446200f104c580c0e4401c04145075856001002c0b05021f540501c909143c1c5100e40d205100445440c49220b4000c1d80d400030b21545141c40d8098110041c0010460540b1941d070204039140c0380078012503502d103000c0d1518015111291540c01e240d07142d1450044080d00401c0030b4440010361611551000c80c06901151945440e0784444c0c008100400442e0400c542024900704514140000010303141d1080703104108881c4250f003003400445903170082c07039078540120f034032080b20061001542001d032010008641d0001303411900c030404503a04a183c0c422040382e40c0c00000b0444144842070210314080c0c0040e0912030b0440d450000490301c010220711445806100c00300205501010030b01c640c040b111482000c407441070800c510740a9070006a11040e520a580110780b803c10b034103010301160305c1070f1740080140c0860003c0380c500b2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 955964001 1250 955962751 955962769
    0x10e01050307030b3d09050d0f06020a2a02010206062707080405070603020a170c07150f0b010e1305090a050a1a01050d02030d0e0f04020c0a03031803020a02 69
    0x81024992980340b01c00d90781c1c07561010401744078580729040c03420301c0c00d0810348084e068503100710702540342c24070302d03045805900141610111041600d505c451b0341040e08000800005154004106500009041d03074020f81c440c140940040c2003141c400000e0182604603403440c490b150009015030002c1c00003610034a07151030540e00003214208a050401c20030b41055886c504101e5000c40403404003820701c014084104510000340c03c0606045180060505000e0a403654600400300d85440c14030000300380c000204151010315034002006020701c842c0c255248083c0882c840485031003450301000150b59840380e501c1c8844d140024003244d00c069000c1d4100c6014180060100d000e5100308412400080c10401060000703d02174a480701c0d40e401c0a032000548010103900c868400c0020f80321901c0542d40201d1401d88100950030300302d10803518007011900e05028100c18503401480401c00b0910884081106041035200f1b0ba803c02408000301c2b400850300d40d25400160059000b0000080103050865071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 955965251 1250 955964001 955964011
    0x90b031b0301030b090115030c0b0a210608101415010302090613060212070503190207080109030302040503010f0e030406111e0d200d030b0a08030a090e0f06010e010503 74
    0x22224500300c0503a2540030791081e84103d43c0c4022200420065150038412060076904020004800a00c0c1da01d0b030403010110b5001d1007480010000d480c130300950103100808220f000040042d0b1500300f180280d00000c2456100700c640394013640d681301c8042c00c1188a04800d82200d80c592002640701d805d1802c3d6200400b07000c003418142d08000c480b850303075a07242c0504a16420b41d038068202d0b508201d070090811041c07130001e0108443c01c0c0091030020b403010003501c0150036404805540c0b40b018400407480c100d195170201d40b040d46048c62200034198140c005000341c0c2c4c0d0643c0240b2501c5030518806080b22101410f44403903400610051042e0b40c8280d024148a81c8002d00b10b5012240103139500310302100149a85656a01c00f56490782c1171034006411242900c2e149548103c2a0108402d0039100c003031000050080554403000c04540c2d9840c280400007030100001140e464100081020f0700000710b50081c0340702d081a80000956034802c105a1512512040c0c0d180d444981050b801940c0c0c036000501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 955966501 1250 955965251 955965271
    0x10c121802061c0c02010b010503150114030115020708070302010e100e150306040e12030a09051203042f13050406182f090112020607050d180504050403090b03 70
    0x420000541d0702c0d04003602108904503c0c070340540110b400074804607100410b1803429a41400b94120090707800c03d050343c0e0301a1300800d049441c0c0220000403a0f141840320241500c060001c000491040251281d81b80b014400d9000c80308101e03100c9000c01d0b03a55a0074800280018844885c104c4c0c1030420030481c58450a150410308001e03448280082c0030000038010701c00f01c1c3d078400f004000041c60a4000c8144590f15140a4a401044001c210302107100043c50550b500b600c5100711410080c0412010140700c403400d0070903440b42894a842091120030644881503425a0303910700034900500b0034033b040d9401000f1310228885401e00700c2100500002041612007030781e541134070350046614400c0c280b01d05200300c01d206404e08081e40a020f68802d860012a829100800e501c0600e03101e8081e40760540744a8445c04102c440c0c0d83c40068038a215072400109135005214024107400d41210300f03030350841c3c106811084281d0f02d4405000071207004480c007800181908600f0020714480c0801981c1205241c0c3c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 955967751 1250 955966501 955966541
    0x60402210109050a1a040b16090915090606051201030b0a0b060a020d09060e0d020928090506070c080d1a060c0c0a08010b0901090f0626010e010c12 65
    0xc004a00711040300744155034540203008840304001040c81810030440707040518080134206a2210081003c00800c0d0800e9042d0310a010412039005451000060008030012b02c0f0702d9609054012680880b842000c400c0c0d400e191000c44c3c542c1c002c40c20340e8022950013513030101581c81c58540700000900038001c607005940d01c0140c08a552a80001040d210440350001d2442450801009003680d80603800401040700c0359044801a580d9070b980c480c000c0c1e07012540304456403281c170307000c0c0302c000c2c18814200c0044040035105e800a600c107800c5240c803a4007070b105a50b80e81d501c894045e02c9400525030b0040050a0402c00c604030940d066100c81010f0411019076003540c9480c00c0825460341c00004110440d6101001c10009850029888000f40042000070710141c4901b030301040706900103002d1807040c0c90300c90801c4400300d02140d001d800100f200c65405020340030055030b408402e1201c880010704075401c00f002c500c4034601c14001e00c08101780c50f642d54201d0004020700d000c0145050780c46040e40410310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 955969001 1250 955967751 955967809
    0xd051003020a121a0106020d08220f0c060521070e0402030901020c070f290c0d0903030305060d03020601050f0111010c0f020f06010e0705160606031101020106050111060402 76
    0x492800150640a440c0f512409960400440400120040041d0384104030018014103502180c40901c4081074201080c0c162160100400141401d5038090078034410b03054040103100d1880d0004030158081c0f02e040d551582c43d40c1d0100c0ba079214061a1703000008071105001400d40385620132940c400700900e40b403100301c00c07a800001c1c00c6c0c1c0c2c819a900d481583d00420072003401c110500400c802445c0046012402a1901d503c4403c02032903031401050184414a801d810b00e003400044420064200d420743c1d1034000c0d840c4010706090494081038001a140c00b002039801d0804c05a03170300d50307190503030002d05042e0f10344001c00c034400300080103a034100a010420b403004010240207a11150090b612604029040d1100084c81c0c0b00300e510381001c8643c41480100070310f0011980a40d00702400f840e00d01d546400051014100b40129403009003030501c0c2800020502c41080074a000030f80c0f0903030090180c29912001160000e030340b6030b1b400040d80c104001103801440c00c0821090001c40080d08402e8036030607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 955970251 1250 955969001 955969009
    0x5030d05090c041104030b07050a050427141b09010c0203010e010903080906040b010915080303070207031104090b011401030902090c040603110f031f080a1110050f0d05100302 77
    0x58509010350340c00700100581503d850302a135448035004442440c01c09180d9151488403100c041c0425052180005003684880e10840403074014020707030305071a500e004040d400900c50b40c80d9914000d84003880d100c0c00c006400d0850003018054800409000702040b4140c4c0503d0403036110165040c1881741c400486c030010b031403e0050310460480399000258004450a0103010340600614400c00c0350011000c100015207100d0200341501d510030400560032080010103002146c503a0418144c920000c400c00c501035500140390700640b41314000c0c1540001c1040184001d5400f01d200050070b81401074014442590003101000450340145808512021980c000c100e0707000d0280c5400e0204800003a003030043d25010301600789141c032000f010500d4a911803032903003254000a0b000099080820b029039441400d0031039a44054280300d410b662a041c002e18000700300302d00c0c080d92103000300b10302100c0c6043c003030050040e101e030740301040b04551901c614002c0000c02042c0007007020000c41344105010025032a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 955971501 1250 955970251 955970261
    0x3050a0236040506010602010b0901030615032a090c2312040f0b060619050a3e06011202010c1407030609051e030d0207030e090718080303041e05030d 66
    0xaa01092550310b003400e0030075a060800580044065a0410110305500c2c0c0b02c100c49641100d801071000075000c10150040080e81d10070307502c0a45403420b10900e150781403400c1c0d560350100e21a2000032404440d912807d100540c0c20a0840300045103100d0680c4010300d50603c2c281e90744040300c0841500d0a80411918808a00191030503910b20480503c008204116010709a40010f01168810b0134540e54145440d45409640801010084041020300c40d41c0c1c0a01b58441421102e403440c1948249000500a0103443d10448914010402071044400d00404101d0506850380145da41c800254581c005440803004101304a80c0ea1002c00d80c0ca0182c40014820400914499000441d04500900384a03142580300040450301c451880c9010645880000031035400c010807000250315a005400c00392003001800e41c01030b801482c0c0b030341004800307544802212450914100358a07105034071100d05a55030f00040360014004405491100c3d84030b1381d18120041d8452192044074a0442c0d03102c06001039079 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 955972751 1250 955971501 955971589
    0x2031e070210020705010f081014060903010c230708040905180f100509030910080c09180906091203070c0822091b0507350a140403050a02 61
    0x4c0c100d62018000e569010940c0d040d072a0003442c042003281040082c1c2e0701c91500600c981070552404500f03003101a00c580c0c040d01c0c00b58000800820004002c2200902040002605a035922100545d40c0f8084000c10301983c4145070008030036800c0c107040500310300041c000a400e408100011400d1030100190070800e0210000003107001d89035942c02e1214910a9070310141054205400c00c3c0320f04040c50700d4004013440c0118040c03500e011680c58200e400003a603c201d400c425041940242d04555044040d07001a0082e00b450301190401e6071600750349600c1d42d600e07207000113061030100302180a40c0e210b0040560030394012090700d45041a4185074502c088181e01f900e00c1c050070384900030410b1040d42d104803010428a40c0399400c1c180908103000304644a82030004000208807004602e1118900302c461030b002c080341400b5203003806410703400540e541000911000082c047d8035109000d40300502039034200e903448001407070399200d1a030070000c64a0012024000c4d400c41c20401d202c40d44590750725401d0031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 955974001 1250 955972751 955972753
    0xb1006170121140d1d0f1003020903030c070302130501080d0c0614010837020d0f0204020406171e0708070e09130201110109021f031407030209010314010602031e07021002 75
    0x340844010241401c00034000c3d0089a4905c120100340540b04d502d4045401310040390310602c00c0b800603000360000d0141c004415003501c00401d02204041001880b40c0c1924000c40706a43c15002c5281c44401ba207000340900207403904a8005004c3c0d29002d1030314140d942d84035140100c0c03070b00508401a0040a001d0b4000f0015034080006140d0380e6001c252008841280c4100d040089481210880c15001e45481d000340550030740000401804404240860042d600410642d691545c1c0c51009041c001803141140009030200d0114002010300003c411400408080030540d65442d08029a001d4100034110801c1c45040c068505503981e0341c1010300c1c0301c0d064800850401d00c20364000102508810107115001e685010152000350b81e403075105109071140380381c10070202461914102c018007090110a00041c01800034000350942503000792541c42000e90f4104400803096150f00da107180d081c0318040c003582080014400c9030070148031607003d80381c0310a07070186030100303541c080717120315040078404801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 955975251 1250 955974001 955974013
    0x17011a031302180106080601022d070e010b0304030801080f070311030a0605091f060506030109090816062003130201030b19030c080105011a12040201030b04090b100617012114 77
    0xd684e4115081c6d903000b0001b0710003080040c5c54400c000388460040d200603c05c00c46000e01e1150700160400006020b4041104202090b50307480000142d1600151800c0b008141050004500c0c0080050100c0034891744a00030190985151644c01b101100c1e101c0c02901070007156000400b24035180900d50262280c04010100c40003003480c05090743e0881c440d5100c0003400c24100700420b94882003507034152545070000094a04c40c514007030400c8d100300e5000c01001c4903481443c00602002d64491152510694450910019100c0b06482c0b02d110071195003c41100c1d845143d00954441c0d03120340c0c2a40e0000d00303d140d0740c001c900c072071750807942c10381c0d00407249803448143c144111007003070080314018450341e41d506812a01d000b1000000f4000e850ae101c00c0820178000142c1568866000074004501c00b42c0100b00c039088a00300141c1080082b9010030405800c01c800140041c41441340c1208650746e4420074103681d0070b01803100340d00e2016400e40d2202e4558880950041403121901c100c030085c011000b016 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 955976501 1250 955975251 955975259
    0xe03130e0601030b1e030f150108010f02030402090708040203070506160507080d0c06020705010b0405130c050924030a14070602150c0f0a02010906060803070317011a0313021801 78
    0x155801004107424101401d00151040c05d4640c0480091088000007030228202c0070b500c00700341b50a0100441c0c4c012485242d01c558158000300303070580c3c142c1328a032009010804074070302c604042c0c0c071003a5070007500007888600080300c075407041f0749864109100405840d905559440000e0150b00841d140e05440c54220080804100701001070100520071880600032403030307120b0000342c450040301ca401303400182c00140314020802c007940f00c0e00680c0c000400c200014100210441751580b042d041c01c541003a04444049130510301103911501c50041c0c1e034051b144c6800320300d408184803040494881d405109420709040040c44070300d0344887c4040214001c1c4040c0b03160410081c94a03400240706044000f403030040c81400038481c03007292003000c0280202aa2a00c140b0000c90061101203406003542d0310745500421040f0b008030091140314041d650b200c0d00090401d010014240c020b01c20003012400103030310070202901344d01c091644010072954464030403003146c01040014000c84d0b1150708c88031807400140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 955977751 1250 955976501 955976519
    0x140301081e011808030c04030606060c061425050c250b07020303071e0c1e06110c0409030203130f06030f0e0a1707020402070510050717060d02040e0313 67
    0x2010280d01c002400052a00c207034400007a4030007080070301030300c0001002800000b56041110003c551040040000da42d44100081100803003403021074001c1d060452011003040d05c0c181050003036415807890508049018140000482291509001d008040c40b9661452100340b05005050040701310340c1c4c56007009403030200e0205010703420600c0006410700050000d82c4000041d9140c00e50b001c2d00040c185000d41039601c18903910f040c030090000c413081901060200140c1403180c9900b01066060302c0c0c09443e101c090300c944508012040c1c5640c8000400c0000346405c3c2c0112a0043c080d00650340382044140e0b144070003104a03007228000e0860700703001300708440e07251107807003010b0768012002c003d641e0501480948134058503802900b101101c04101c0900c0c07481c0070480706e05980c003e1086540701000c0c81c0064072402c03a007011146552070000000d004a01030003401d03010900d0600c440c00c1d00d58464041202c000241c10f01a42c11903901c10440c45035410800c0245607204265107482c030002e107048150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 955979001 1250 955977751 955977793
    0x40b03150a030804060e06070609060c020c0a2d05120703051002090112050a2405031603032001111b0601140a0605030a0e07061e02030301030c050d0314030108 70
    0x40341c05000e10380d00c2000812110f1042d5410340d011071504184000c0f0010000d21140a01c41e070150610745404e40c00341c1009030a6116080b00c1c1200d03000e4416034580802000350003034042c802c0400c08000300007480000c1700c049181d45040c8680091b00380d203003500c1e0070200c5c1c203000f005c42d4220610303401240c0074402d2180810100380c0140c0140790542c580112440003e0586040803503040d08079860f4004038400201c103401101d548501d610803151501e000c40f9007209009500c0c46075601a010740c41c00c2d41c0008072607100050a0341d4150320381d040114130311010b2000000c8840044400d80d5614601030302000700107001001d02001d0401400040c0d0201e0b50b110f420490180e02c458260301d01c004d5409503540310742014004890441c00c1c0280caa544884401000c0c06028031001214010160081026904079000910780c0e2407104079101d001070555416039681c07200f0302024116410320a070802c81481c1c80c04000100a00ca460008001c2d0710301048501ca60f0000c2e002055590030011051042d46620940 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 955980251 1250 955979001 955979041
    0x90b0711030f04060e0409170d1506020a0b04060603050d09080c031c110c090c0c0d080c1204051c090510021504060c050714010b090c030f0c0a0c08040b03 68
    0x14520b800400d182e100b80900c6984036040a02a42a2281c410796481c0da111096030750300801003d88511400b80220407540c041e010104400c1e00c0c1020b10320002c0707036400c281d601b070300d94a800419140308103881d9030304050802001104c090b52100408000a041170164500981060311030242517418515614142841068010300981c040e0f400220420030464090301095072500700b4410720164412500e041041086c0e00540103d000340510100c12318400050022058500c10b640d00040c4551080395030207c103403072501c80d2040074410441c102400b00c4116400510401c100c5a00300150342c03150b130b407a80803105070758041000d10004202d9420401c010156000092003e400100e0f0444455a0070f003074090005400c4c5a600c03008480f00a0190007201c50960704070927111261214042868044c2001c001464011121007022490601850003520f01a034000f24042d0550782d02c1c0c00403408180c010140082c2000074000e40c800c08200124000c3c00034101c21200c460f40c0e8685000f040c00c4980d03040302 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 955981501 1250 955980251 955980253
    0x708031201080a02031f11070f061808070813150908070602070f1a040305030f181806100513030501060321020d050f0d0e0a11030c0a0501110a06090b0711 68
    0x90703c00059401180003415080d1321320030410000003105180004080b12000003030705490004503641802000c5014804492043c00309201d12840f882d2501e458022072000180200810301c116400520214080e0103462541c1107c7d01246075036040742e010704604080e2910200b28440c20070b020510060208001604060000740304051829400d00c0500d900f0384500350b07464070030364401000780e0181c0007124003e603080800c07651030b0700c2d00f0440340040d039104010300841400d00507074084841c24210589070041e490000c64001d00c4da242270500c0800c840800550b01004020040d04403000f216825280c007550140000040301400d42c8be05840c400b02c10600c1742d0000380c80c05803885e0101d60002d00c0c1943c0212600d05140c59000d2558420941e000314184c4c8420207003898250100320000203041807480d400b0b11103c010305a400414944c440c03031850100c98000c3c042a00a20040d4000d40c0c01d16100c403c0b610448a0605c06038a8810407685a40d02c02c80e00d083c0d42400b8802e0a0b9030200e030701804400410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 955982751 1250 955981501 955981513
    0xa1a09010b09010324030b070318031407020a2114030304020303030624030117062a160b15120705010912150e060105240403030e0d05070803120108 65
    0x500d030065a018491290f03040613210b040c02c84040800e42181c02c035a251584c0d6034511a500e0b03151900b0385040c2118020f0001e0302d0000502601e2040860849900c1c1c0c040d210201e0359401940194403a5201d00810f0380c20840b4800002070011b0000c0340101100413010341564000030f07a181c00c40da031001c100c9050303501e503000303209000150381d0120803030b60082421101c0658142030442c03081d11140204445d0b500b1020084000500381c040c56002546000400007696050395640744480950008144501503001c3c58101300482c0003a81e50007031052120403034980c10b003030150b99910345d400e000442c0c0031140d40e805a0714140042c14002412227141c4542c501408000d41410300003818a005486070001211000d040d41052101481070700d004560140c4003070050748503031a410390780c40c01d0a10646005102c0d05102d510b480000f40b10320701050703400400c0f10b032505103591801c031010142c1901646e48200c0c0d40b818440020002c000b6600184807960155498004021001043e540140c0c80441650851 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 955984001 1250 955982751 955982759
    0x17011e050312090910080f0102190513031b050d0c0317032202060c1c021c0504090914100c030f0c020a0204151a190516030309030509090a1a0901 64
    0x3a00543e0784040065510b581681d80390300300c9a90343c0351103a103c80c50500a06950550060f010740040884c007014075081e00c0c09088201040350b2902c5503c0c021255055070b00020310024011210a403445261200480041d0b0348600026000707003000300c01110f0512208100b00104800300c1300c03120807500d110324400c0c1586403042e0740607241043c05007801d45100c130910b001c90031982c41300b065031040c100000c01c46011019170704903d28031a0403046082c000d8442c074800500503c0100703920142c0403000e5580e590900f45003001240242c42412401c403024000c0140030344050030100865048507609020216601c24103003000b80c100c459559014907054104020074100540006907002460303070540300010021071015514442c2c0034250058110404455005407040c8c0840b006020a000c0c031207031076a0781c0700c0500070035070b0740e0710522015152902c4000c0491000c0380c000c1d480078800d14000d007456807030500c60070002110440b003102c00e05a26559901521503259008402404400c025103c0b03400315418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 955985251 1250 955984001 955984033
    0x11100914060a05221701140a05090703110a08030307050a08060d1a040c17030c0c042003040512040e0a0c0f02121e1612090e0c070317011e0503 63
    0x100d11134400c801455000ca00501040f40c07050310b0042a140701e041d420300c80705e0828180030301614103420300e5010882c03020407074a4506200f0640100c04100080825030700d1540d8a4201e078109445040d403005054000051501d0148003c41c850003103940c1d00790f0368079110310020380780440180825020708041a94040000d20000548194030f44819002c01156654502292031000d01d800540c603482c50300c00c00c5180d000740080901403a176203202c16900301c0c8604000344800c944051801075800c2d44079050703404803043c50500840c1c1090103002515020202c03496800c3c16a44183d010ba52a503050740d04000e0440e01c54031aa8000340c0c1c40d07207402c030984550194004d60313401c40480b8144511000240345441d070040039402291100d0b00f481019269102c0400c00c2902d1101e030b03d001c0d14031b64500e0354840444c0e803041242005681501c10410000d8a030782d034080f821038008200c01c80c20f101d18100209025007035040043d00030510b2040315806035020040f0403c5418003540302e14060741c000346000201082c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 955986501 1250 955985251 955985257
    0x2101106040305160c0803031b16020906190806071e09060f110106090228093c0303020708010b0d0204020904141e0f04080d0911100914060a05 63
    0x140500c0d1480e04c40720391804005929201c110004e10742c030307001c07440040c80000100141d03110799004461035401000d801e105607941c0c4540128014822003070710460005140c4151080d4201201608100c03540d00000304042000440703410000c00750b4499820448880c2d40a10340403420b25582d00d5401688000c038001a1030072031a40112400c0c452208103882c80244903a500c2e0050483c802d001340602580c6400d8100254071490340c211011654042001c4a0280060246200c0440c0e41d61584031901c2c0c1944054080d4509400644861640f4502025401840c3d003540e180f540b88145081c02070b1035403038003901d000f485621900c103c4e410407a800055542d071070416101c01d80c0543c2c0150b515904000020700400c0c07216540c04034170480b00c0500c0380025201030480e10304e44401c0148000ca071540e901c0400b08241c125001043c6d01c008110401142c00c654018040d00b611914181c03102104850000e051400b48101c0c8400003859000304004960320355184200076441940c0c598038011910400800504c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 955987751 1250 955986501 955986503
    0x10050a0f020c10090905070f0918060e07080a0b120a0f080c0f07060908031201031b030203030d270b0f1009050411130b011b0201020f12070210110604 66
    0x291801004100034001e00c540488190b000344060400070031070802910140480c090007004a1505000808550249040803a1501c1c0ea444005c0d26507d00700d000005d400c90004841000ca40f10301c40050b015141c40c6606000e0f03042500c030407009182c400c01560441b041d2021891003084101031044090a010951154a41c0c00884885003800b00d4181075410344100760940c1c595114a1001d04ea000c00007240c81825a0440e55408280c030340c0e076034092546c0707000c0e40705203e00201c01c1000400c00506000340e01102d40d1410045000901d990b80c00007401c503001500603440765502c44000223040e8400c001010a08040c81e14155030b0382d00962070f04458100002c145005552180c0041b80401040120300001800f4140042c0803138500780c40d158600d904496021800342c004481c0d941448421402207070040c281c1a51b0342c541c14601190000c0c030705803500b0010b9042d80150380082e8209002072200c140010b0703025a482d81c0d100524414015141400e8010404010342d1100c00c0c0c1c4001e4010800507041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 955989001 1250 955987751 955987757
    0x20f0607050a0b0f01080d03090302060f130b040507050103061a0f031f080c040e010c120b0d1505091504080a0309060b0306070f020c2e030605090f1510050a 69
    0x10040c51819502d8900b403110082c004003910020440101148402a816200b0700700076034041c1d03480d060058050f00e8000c00000c002d40c004100040d03c100510320600d604c0081950b2070b02c02151703540c580350401c1c4000d40c0d054420303400080081c0510350b098040c01d0f0062030386082940e901100076914040c81d000700942c040380c1d2800040426081c0300340c4614000001348844030780d8040d0b9030314000c5580e0341c0100e02d0300034060340c28622103d000b60810311178403031000511b46669110b20007401d200002040f41d02900d03948074a41d200c0e0a008201140c8018403100c0d030849001401e0304108460740d160005035202040b1207180c960800000800c00001d0f11800361003404c000c1782103201441c1900c0640b071022000c80d014455001007060740c581c007420782a0701400355001c2c0c03100c0c8143d4000748200403030341c003114401201c1e0301481c1010b500d051501d00404080503140004041d601c503000210054402e50b0000100c242074418030240c01c80010440504a50441d59041e91142001e0b0145c82800b54030005018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 955990251 1250 955989001 955989007
    0x1b0c0510020d20070204230712020d11090a051005071502040b07050105070e011d1e04060b0703031104051c050a120215061804080c0a0503040f05010f0c020f06 70
    0x842c070b00d60800c9480344090381c0030400441c08400309540315005600140c2c49107081040d07000380e80744a58a58149025002400c40c2d00341e035003603025181c070340b042c1c0c4250100c15802c00c01e000b10700603284030f1400441c2c07005d51071390f590f043c02c002000b900516542000d0312a4000c0000155101d8002d0100e65001d030780315007689507034015402104024021a40606040940015414100081940524841c41250300c80c0030308140c0f11030045616201c0b04030980308642c4081080700d05071030301844141c0110000304140031643c0b440781c00f040c1a100d00b64090788110380c2c003292070301c2019014050b04513104141c030a9281000d107402c0005214000c800c8080c412032440a101d081403090901600c40c05a800c100e5200034080003110096950b018031001001306c51252000c245a868445805041c91706002e0a400080c1c07525112940550b10001e00164144a10118040000c1d03048c00984001c001c1007009101c454605000540320403150180c950402100b000b280d40160b40300408600184400d49000e61 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955991501 1250 955990251 955990267
    0x61707020709052d0f0a0908090a2c0702060103060e0c030d050301150908100c020f100f06080c030a1205040e09010e0f120a0804020109050904061b0c051002 69
    0x10402000c1e07007004120508002c1003085021108013900b0f4500e00701071a6a468410500d040b0280e4102920700d800140308843c042104414603820030191240190801031508031001c00143c0c592080d80d020013991003010010394a0340c00c42d401c0e86402814103907404211407818020003511a541400003c04140c0d8424040d54039120402000000c240007404444101100a10181058000b446010340c0d4614003545450708900c1003c00784100d452840c003c0640000204003c6d0190a4000900c421846803400d0b440b0f001c482002840c0f558100700f41c00107040a030b5000407100303075103241c1c004500700d5006104000c074030380303000a001c40840e4002c401070395031107040c56040700c0390b101780e034080d03a5050781000510150361010741c0480075004040702160784003c2c40145141d01d0b0000081c100c1004070080c042050049d0090700102d80c02481450092030140c0c40300d0001d1250141030380d0545000b9035600071800c482d0344151400e0440140c40c01c195898414654405680714103000c40904900c1e0041035803c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 955992751 1250 955991501 955991503
    0x6070f12050907150c0f08070521030a0c09030201022508030408101b05030c03061c03030f050106090f031106130e10060e06030c03071419120606170702 67
    0x100c0460304055051007641025508541d8810960041c40b01351007030799203a069043e020b001c0c42c030f84c400d40c00743c060490b8141a4a07004250b800000d002e468500803032000310f0021446c074403480b82c61800240181d0b26400e0401c10750040311184151507041c801208011f00150ba000101d0015107448400010640401d09501c051400100d901055662001117004501114081440e071400d0035040300c10040ba00d0502e010303c401c0101c146184000c10f90800115080e508120020f541c400c0028203070510501c41d10003080c403510b076025002e80c00a80c3d211680843c80390312b409a240100510302c2c040002d6405c1886c20b050240842c88024a1a01c100e491540141c036030800340e0701e00160341c0703040003c01c641d41c040c0b034280081c044458140e00e103008200402c4a0340a9003500711a160007808090541d81d13042035030b1140341d00c0603101e2410321003d4001307511204451700050944807200d0001429100c3c0f101d10282a80b90201d80100d083c6042c41d0041c400d80798001074000709441088204482c0342c44149040e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 955994001 1250 955992751 955992767
    0x1e28021f05070209100614070c050616052a01030f18081309020315011116090c0e1e0904140a0501021e19030f020f120718030506070f 59
    0x50011119418080d0811070704800988074080c0280c030401308030383c3c54100041040030b080c0103007000725156008501841d003986001e0201144201400e0341d000da107079800030300c1640241d00032100540000c2c40300d034200641070110080c01c170340d066910200d040b12071481c0030340340c2040304146040542d40c500384a0151361641040d402030740022102e50001d41141442c00705a4815125030701600d291140010341c101c014400c5070721900d40d690501c0c1c28101c0181c0115004a5240e80005051007444030503040043c001c0c540b8801020f801d1000646100c410340080e0003889840c0030103218108120560700035540c00c1c040003230005400c56042c00315a9861424021082841009201501c03404e45c0000c108a8154002c2024281d0320786440c035400c02e040260007062140441ea4030384490000145032400b40650031a03100441c84542c058180607100c0c19400840d0400c540070080c3c0c8d44e00d4001c0c402c030150017a10a400c2c030035458500555190454403066034600d0b0150108040120078180441503a20070045c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 955995251 1250 955994001 955994029
    0x605121902070602040b21091504062a08060420070f0b070507110604030201050703030e0c1509041812050904140a090203100225020a171e2802 63
    0x421901d03180c0740c0044104913044010360b5a4410107c1401207007080500d003240703100e103a010303009098401c141d451407485540003801c00c440d03191322098a980195011080c10394582c030b00082c070403030300703040258018401b99000d0640350086140c0b031303e90840341800940301d841020f00c1809165440e075a03450071008400040030003411280000040c0400164080000c02101380a22141881c10b2000360402c542d502c03031480000c4c0450402c00c80700740024040c2d003090400d100350205480140d9104008a001c1e5404510002180c100c0014403100710f03d000c0c82101801d110025889400604650328013801c0c0391a0f8001005001010444c2c0d0010f030f0b1941c0100d154100803210103841c50800c0030349000a00041801240b003805541505501c1c4c2225100303854024940c07140300059445108076200443d06400340680c2c00c4a1109404241140f00004021418900400900c00c000a404000f030500704512111922600401c1c6491a541b4502240180c24945103412201c41c01d4144006102c2d41c20100c6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 955996501 1250 955995251 955995263
    0x170907032a03030c0b09011a1009030b0711190206040611030904140a2d09050f012a0203090f220f020903011401030f17270109060512190207 62
    0x403040544c01846a00e4092080101d40d400d07031240c203601420703078113202ea4110080ba00810440308501e01990320200212041c05d069809940784d44a250278842c045443c0d030081001c49040b000741f101c081003034034400080900c1e4602046040d80c000789061065100e83c1c0100560812214a030502c10300c00c40f503020000a04c100180d80803d545034001c170740b0482e48614070707034580308160b0401032501d031201c2d2940140145000d0808000300c5064001c0000700d0050b51103210320748001844100c01d209a44144241111040303401000e1700310341f50401d0f26a010002150001d0001e00304a468004c040cd41042003101d5500012040014070000750040590365000d540c14809002c00303d1005038010144203e00f50001e1150744c00109014544171805e01c030003081b40c030b11083c036440411304541c40c00003d804007000c038919100395030b40348008031140140b004144d150808041c0f00f02e907801c542c0350300040480d8200715090075150010b4644401c00104400c0704612075a001c030b240006143d049600440d4405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 955997751 1250 955996501 955996583
    0x9230702030c03220b030403090306020f071b0311060c0a030e0f030102070b010302041a0d080f0c0313050112091109040c15050310090e030d0209010507020405040b0717090703 77
    0xc9841e91100c1800e244c200c142d100c003000c0801d0341c0302003401320b038441e64054580c01045480c6681d101c2c001c0d4042150700015000901814000405000e000442040e0014018035801c0c00c42c05c06401c00c3c00c2011000307110350820026a0200c3c2d80c0411025482a00b5080101441d8127040c04500d050b40d041c40a00d0f031551001a001081240c80e1900760b0507a4001c0d9801c1090f00041041c04010b038a003009266403008840c8202c20004007680d0092005001c0503500f1403c0100d41000c031459030300b082c800300c441d0a02001091185581c0880e058010f044080c0c0148030014464485038058180118814003a07128030000500f0311600f00f45150040c10b000802101407009424002c000da002503c40c491203004080001610315078a0154010410003a00a0b5103408a030000010081d403241c2c441506000041c071842001d65a81d1007214400d60107280e940306103281c1058001c1400140300e030355a11442c0c0c00010320001400004601d02500e6200307500304404950414043d130542c64010941036402c1c584 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 955999001 1250 955997751 955997767
    0x105071d1516050708061b130b040308031803030408190212190305090d082202040f141f150c080f0c0f070e0a0218030106060509030709230702030c03 66
    0x90810694501d00903c02d80b5101616507514545400c2e0555001140740344110f001c0400101d050028a40094034401140000e40d940c1141341d01034105a0080c0d821180100400091030410030103141c8000855018500d1450250f5a02d503582c0500801c038025041c41c0340003000c5880c000c02000c004401307014203150f150f0068001042c180580c4800a0000908240121740185400a6000c03044400358494002d25690040c580558540806141c0700b40b10f804001d000c0941c0303444c4500021100c100c5400710340401c48110010308054090403540c044403180048000f0a00c0f0264042c054511140701c5010b85280e8080494a502e01c0c4600a0440305000500040304008c00d030050011800e03a005440801020104050302d030b20140c4074400018443c3e20000d98040c48a03802441940c1068036400d50950758040840c0c2140c131690045004540009048401803030200000c0e001084102c0782406275114080c45041d11000f00300142808003545408168402c2c028000c0c3c42042600c0002c4940300c1d849 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 956000251 1250 955999001 955999027
    0xc080f09130e0d051306081909030c0309051210020913020309010c17010e06060310090e010f050c07051b040e0d050a030606050c06153706020105071d15 67
    0x1101e02c600003441403104920103180110151031a9500d000f0700b444e00c807843d0017400e544501000340320620301c4040c000d02000c00f6440e4402d00e01d4441c02941c440021320000e10300900741d10a05d40081c1e104035007a0000350800d042c00110140f8400d1414800f684615280011405007151a04c41240d954000300c100018024150720041034520140d6865400701d102e2040480001028082c064803e007d4500051081c1000b130000c5411030744002c140c071842a551500b040031070313010f41560b00070b50351130b8044c4080c50030301405140d4202c0081040036140c008503542c0d055407404240700813202000c8541d0744022541e220b41c044040c80038179400380e0b594031068030001886607000850391342c0444c2c0b400b1000701c0c40c03074404c07803d480201b00b61074014030306a1510803030724801030641124641d200e00083c00e0642000d07003a03032400440b09030a498200e0181c007800421b15182080c0e07048082113a14000030010001d50050382020088155025808c152040c6404103080f40c04003d000440c40c9070003d4241c0b00744038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 956001501 1250 956000251 956000261
    0x9090a02190f330504060e150a02010b09072105040c030f120206070216030311010618060f050315060603040503210406050907060806121f0b0901060804030c080f0913 73
    0x1c03860041c4030302a400c40d98803142c240c01c3c2ca91420004100b480203000c02da000349441030100400505c0f100942c840d40b40641220740c01030a139070b40180d44640101d0f11500380b8500040d0005c9050030006511010a0111491003500c2c1d1344001c18680c9134000f140c01e1066619041c4042c40c0c2245e68608180d4690078a24003035101ea01b031040051103070740000b07440184046203150004100001d0100210f14544044441e5081040140e91355540c981c000910300e1804450000b040e651000089030017031070040c04001461450740845e009820401072007440d00541140c1640c0030340100d4005131aa00c0350304000d451401201400540750b0903170f83301c005d10003a140e80b215205911850080c419035407070b40c281585811440c4038500c0801c00000210b15145045c480300c902c83e031440b5003103440c0061a1413944072410140c4442c159101e9848910110700e0034958000c60160000b4100200d16092641c1c0050046403203170400741041d14042250030034a50340500b1580c07220001002c0d5005158082c1010b00244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 956002751 1250 956001501 956001539
    0x4030f0302071a030105060904020d0e16050111070b030709030b0403080103060501090c0c03030e150f0f0106090b0d0f0207051509010608070501081302033909090a02190f 75
    0x121a0500019041003c150000e00c1c410011810f581075900c2c0000b40310941c0c001c400c1d581e5010740c003030040710000b0703145209000a0f1400400244000c400450b010030100c00c8e030360013490401c00c0100c1450a001c6000030217004860048400c5541e070b58030703000201c5a401050304000d0201e0f14540c2408103042d0b100d91994180c07030040c0401c01071a43d803201000101e8031944c11040c0414200c1c040c202c0444c0c081d6110050444019061300c5640405d2210100c04c184201d90b1701e14450800b50501100352003003003001d805480c540c1406803116003402075505c0c1900440612852b51510780480040031007a54043d5107503554000221140589041c00038080350000300c03110241586050000951013000141c403038216030068503400a00d8170b41000c10750310503283d14800c0c0d825101d160520050340a02070000746607280a80c440d5031080b104800380080b0384000ca03e0803481403064030107100207000c0214455a0269044806802c003c029458890f0680f9081d03021441010246100144520100c09c480d03c0c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 956004001 1250 956002751 956002753
    0x50c06010501050a020a060525030204141014030a0912030506030d030b06090f1801170609010504080327030a0905090f070c0f0c03150b1e010827010204030f0302 71
    0x15a80710700044030b86009207100a001a4018a440c202281c4141d00483e003081407889402e0710520408044500480601502d80c0025400542040242d42d1241d50015100301180c100d0040ba040318001130450b8111a660b034605240000880d0844520341c1c0070501c005d6201807055021000c4590140060008891260007800345100e50032107580300380b1541841300d0b80200310a0401a0300010b00407131124109a964102c2854401d0022400724280654001c10102c041d0403400020017070107a04081010b04407040350380c10241407100189085083e40e5004c01c54102102104804000c005401140010701c80c03024040002c400254a034410340e00e00036100d0560714408542c41b045486681044220344084c0014901c0324030400003807091000035a00c0b8044c10740e41b82da1a44940b2264180010200442d90003641c5d01801011410310001408040a400806a20810710040003a003000d40080c04070a80540103c2661090004000c0d909618207030b04008540311034980c60065004600c0b09429005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 956005251 1250 956004001 956004013
    0xf020c04090c0611070b03131707081c051306020a03290a080c0310020f07060c0c060e030307020c0f0321041a030106020a032604051f110301030b070507050706050c 72
    0x100804c009402411920700007102880d5981d942525100b9803a0a541125403034840000001039400040103004550300409031182e4404049001c10214030100c9131100045003820104920314401996600340340c1c1e04610090b94880d81203404400921905008001c41c0e9000d000310354101b070000300b5000d4004d20603550b2010f03854440ca0000c3d0748900550219a15600110a0800341007040d00075103441d01e201200a420000181d0700c2c40165400d8020103c000351481c0c00c01820704c6020300030441e8101c0c584014602e035081c9000000e45400c079068000b8007442c00d020314120992000c01507000900c506800154003800032441402c41c41d072051041c60884020807001501611180c001c4904841642d0000c00c2928800d550035900d424400e460318003948000900d03044032400b2941c5040c0f10742d1140000e048010402d00d01c4034820a08500300101c0c103468000c03210b07070f00507020088905403174002040441e40d9980703000072600ca120f0b02000a10714001c1000020380d860b00100540041c8041c4800e541c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 956006501 1250 956005251 956005277
    0x5010807030209030c0d0201140406020303160302040513050c0c0a080705071a0307031112010303050706110405130509030408121206031c0318021c15020306060304030f020c04090c06 80
    0x903030080c20307401945904000c1a11701d9614140078450103552060422911503881c4640e0300da41794002d40c0c800000f41c0c00000811040c1140ca901d00756a803d02070030f046050034103103000b003040306545c600350350f000654030408101600303c03407400e407038940721490226410502c05280124160b00080c104485a01c55214046403d4034141c09105440c60b85041c01d0342140e40d007030b5048001e840c0885040300c03900c0b81000032442e22100c1c002000c1c06940070f92210340e904e03040c6150042c01c88070a54490b064900050000f402250ba0702c01d85c146194000070001f06440d101c40452a0561280d544004064480d00703400c07400c800441005000118104080c20b105076035000c052584a00840301c0010705a0301035180388007118000c0e0300542c4c4840c0500303c50030001c0210f03070100312000ba5101c24061424500c02e8614100f00d076403072143c0c80c6804092000d42c00c6d410a02c002c92014000500003c007800646020102d05a100300100740c00f42100810078003805589040003216000680a0310740000c42d0140501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 956007751 1250 956006501 956006507
    0x910111c050f0613180308040515010608070311210613020313020d23100c021c0e0607151406010f0207140a12050102092707030f0204050301050a0605010807 69
    0x2610821074550ba803280d42e80c0e064108041c031428640107412480c0c1d500700041c03004807288140b203d0f1600c03948408405040c281051450300180701805800c01100d000144070450b841043d440c0c1000c0075040200c5e010110384000802809111442400c00c440c03031035207180781004640035501580303042c2e4080003141c0300d41d9480d4060348001c591100700080b1a40e10703000142030100740060080d000342250303c00300244032018141c2c0c40756240c0040780c0c0d40c40a0081034080c0c80b14454509403280b540014865840420451031081b0303510070822040c0b00100a00011545540f0100c038841544101415004000c4101da84005c1c0b8400744038450826401000451950294101e0118259160014442c084c0750a0000c0003a0030105001c0707402ca1103003080042c2c548240d204080701e5a1007200051b031a550182c0a2107010001a045940d0445e10b6182500c2d669030804400c5070824010716000c03510021b2a144d0002074400c503031020350158a0403082051040440d071005040c0c0c0e500340d9507010390341c450140403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 956009001 1250 956007751 956007761
    0x221130501110a1e140604030305090a0209240604060207090c140316050405030f011d031908070203090a090c0206070302040506090d110405070801030b06030a0c05090910111c 77
    0x1600039500c1030070f043c00841e501d028400c4890b1084480300e16540007665400d50f44250402c0710a070139510000521042580500030950b0002c1d41c0c000070111207155800090524001500c075241000766841c030403408500d9101c02da060003d001e0801d0343c0c1d9640d0b408000750350781c4c11442401c2d4004d1a01e91a52101440703440e40b12800b02c0000800340c290b0b25200c00c480c0054507144040c00501c82c040000181c00d0310240a1409602202000010001658000c40040c100e1045030341410340c00c10403450410a8005540d04009051403a010315140d0b0b40c1001a4514400c0d001c8243d841541c00b1000a6189216080a0038000082e17007500c10740c1d12101010f40c243d0145028099102c1c405000a07041d504001110458090040c2c0030714660200010102e012560142c41e0400010701500050080c000045d001581011096005001c2030074540c5034103000c5140c41c080c0307900c191740c00c80100c0c031540400c00103c280100c160303c0030410840241b9401150307502100b0a880d41c4910440b00c0c08090b8000c1c498 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 956010251 1250 956009001 956009027
    0x507090c0e10030905072d08061303210207050c0d0206090d0f020a090e120c0303061c060e160b040503060406051b07060f0f0b0d02100221130501 64
    0x7550032080c110410412145981ca4200d41050b82e03503005600810801c105c804010b01c1051902d420605103415280c01d0180070540380c0b261001184020420032000107000c41d40485002c10480084c01c031890704441c0f02c0d4003241e0750307110800c13074501d442001d44042d801001000d11074000c82d001c00c1c2ca039100f4407100c11a00316000e0341c0a00180b060146a040c086e00c5003c4161242c04401c09218144e400030382c8030132a0b03810503112240e458002d0107140721b08001c03004903030410f01401810000b1080e0000e9a0340300c0244250b0080401a10030203c0c2d6084140c403250281d80301038248041001940c480d03640e07003000303480c96280040c05c480015150103035030201c40588101801505141d0307200d84408020f4200a8075006080c0101e90912235400000b40c0540200d601c43c60b80820829103c818000070344007040700049000d4a8451f0b0031800c4c0d65840c0f4101c100c5581503511a040300300c0c80c20240e0901100280043e000f80b41c403a0001c1000240d100204001100c0200b8141030b503407100c00464209805c811 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 956011501 1250 956010251 956010257
    0x5060f090709030201080a1d0f3a0e06070b2509090c05040f0b0a030b0612040b090c0a09050108251e1a030f01080c030d0302030a06030f0f0507090c 65
    0x10b020b00155100310a11540001000c42c0171651107940a0310b02c0020715605078600326904008505030301180e0610080c451040d254004411003c1b08014110000403000314600d0b41c8003410544c038003400c2c003440a41d4540d100c02002d440d100d440c28180740e50081000c540f5045401c0d02a00364074070a4144081c000010300c074540d03036200c403c1d0604507180e005210140c442010b01506220004070800100c29500143c1040641c00b40c943c0058032025082e80d40900361240324410034001c601c102c0c1c64560b60300d64465041521004681c9500034001d041c0144250681d803c0100c402020444000c20f0304401d0485680000b181c01800407000900392041032040040c0319156149401c200c0d00d41c256144c2040c52085408510045540c0c01c007040703540c020892a4031801001004210040400c205d040d401068150090200f05000c00006500c540b40d840820b0145035020020075419030099015001841e8002c1c3c90000400311410074034890140318800311014883c442c4082401901030040b01e86c5c00010352 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 956012751 1250 956011501 956011517
    0x23010b090f092e0f0b070c0b07034802130e0715050c010c0908010f060b0a051b0a031106070e0f10020f01060b041d1506071a090105060f0907 62
    0x2500303000d4144001240e88900d0f0302aa6001c41c03252030b4000d1000007041c140400036541c81c000c3c41c01020700315855020311482d240910000700441d40011a8000185000e4135803610914201d509020640c0300040d075400c0201043d13007400c00202c4400e0039036040b6000300c504001848a551542058440142401c22590400d14003081811a5103440b254405110308010781044a411a90381c00c58600c01115400516029000c100560302881248a6450902c200340b041f2420192070144521807030110004200000600c007602b90348491040d0b5060400f070b0700f41c4070991000e00b4000d021080078200c4c0341c1d150141c1008108443d00440c100b110174900608240340700c00030542007107d0301140c5114041580a540d19816618800f031150f4000f4001c41320050751264103080ae5245000c00b0490904e001450b41c4007032000002d1000041c9100d02c0c8110b610641e2a0742d9880d2254802402d0070100300c010301510140f040b0080190805032244005036880ca03040c071708080411903d1b07082a82e00c040460044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 956014001 1250 956012751 956012791
    0x315020d0f060314161422090b0402090c09280f030b090d17040b0a1b21020a092c01032d081e0408072c160323010b090f09 54
    0x828030640c01140e0508500c7d03141d0202c4900d8000340c0d20440d0044805107a010100411440c0041960381c00004c10070a240c2081c201001103032510180010075a1003000d90038461003503040f0b00b48500e02515074103000d003058956038541000041030a84011145018030103039001c00901c22172074115154144083d415068403144c64a00c442500941003c0b2102e48501400c24003444900c03510310b82d245507549490078911040840e011010b000507529107614010004410110751020050b420380c0c61040311000e644c010701b0300c800d0404110000140031000c1c1c8200000c00c0c440c2d1812a100111281c00c00308244000441c088032501004040050800805000745405080701080344542005440e00743c4c1d00c0d164440e00803034034201c4a44c0c400340c140751203c5a214040031480c0040400c9484e00d40a0201d6070030b00361103181043c0c1014848104240d81e480c1488952048003e21546200b042e00c0711004c07958441c503048103075901071100f841c022410a203681f0403d060018103540700d024210300640c0d2a1703000f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 956015251 1250 956014001 956014009
    0x105040b0a151b0809100e030a02040b180403080a0b0a050603040807170d021824070305220302030118050303010506071b080606190315020d0f0603141614 68
    0x31550202d04001e05000521007030040000c10f003150602400300e05840c0d02c040c03000c020001d450f8034640000c001401000c001551030004503c50a42e504950200f0140c08036000302c0c060001c01e090a43d03107001703464103200516400000031802000000c1052220403c500c0c10301403505154800d2980103501040001e000c1540840030340b05603441008640d100407031009821085401c480b0750034000e1f550006000c16031f09012400480203110a0340d00313200e140c4a03003855500700088250b01840c4110001802420184143c0445240410005c03003151403200c01e2107041030100403800206d01039032034801070121070100c010301e91440c01c3c1e2020040d4556800c0000b400056041103d040760180d00c014102c480481245142c030000e0542040107241070b1070041d0400c8011101860b00d52141340110b0424404142480750610b03e51050050150f918100d0031198001416500300710113086160104c003004214901001ca0f00d0541c000c2c040399110703c0380d031803030038140c030303110300c1f6a0b00b46c00c01d02d03203800b0340600f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 956016501 1250 956015251 956015279
    0x30a050f0702120303100504050907060e010c06060e180312070f02010f090f0308010f0311060901050403200406060e010c110409080a0806040f05160305040203011b050309060105040b0a 81
    0x68640c400505100ca2903000c224541801c080012080d00080304000060f4454051403006050032103041c1700d81c0c14020000313501d80070780d4014203007000f124070641e0070340c1d90041c0c580380341140e8800800c010346559691091024841916414803950a0403032008002a00005580480e005105010065110044290b44c106140d03007001c0159500c1e14540b648403032040c032030b40480502801388100003c6880c50300800020b4140c0114411012102d010f0021881560f2641032019003955a29580c050f4400141c83c507010740e92008000b07000b10301e0b0000b080d120140c000028030700e05440500c0515180c10040c0c0d00c0000050342c450006005c0080800441d1411420002c86000038000090440654690318415840880d101c40072031940d6003440010704092203140c0c019a80280e0800c558100341103046c075070059801c03a0904060700c3d40023080035036400303511041e9055208810300d601040c80b003901030803540013168407003414003802c400042d082c101405107a2100c00d0050441c003d4505080d01040c2d810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 956017751 1250 956016501 956016517
    0x6040b06060a17060109152f030304031b06060602030c0c010e101b06050108071e051c06110301060c05070503150f10092c0a0b0a09060f02071209060809030a05 70
    0x714680000c1203100f040101c224011f65950b0100311160310508031000800c01080c84d000d119124031406d402290200540350801d606240c80c4440950308501030304e03141305120010700101e1900900003401c98000000b014030300105030644900281110040d034444264640e003c1d04005170305011107030b00d40310f00080110001e00e00d0784400041e10644036141261000d8100a01d80d82c00440c0521842c1c5000004940f41d1041c030000700045800e190120f440c17445100d5280c4012018089900c0c108400364100c00c014003540c5040a45a41c0e4490000340049079020061f141c078022400c0c0806c140c03c003c54654003441144440190f10307243c141c1c508081d818003c3c02ca480d0480d80000115600c402401001c51403100703901c2c1440c60202074000b4402c084a00341054410340d0000c0002c0c0001110a02c8a03076002c01c40200002e1640e000f41000320240511450f6170b04c5281c40000d50704204100d00c10078000042e00e40d540c50081d99210001515003000c15100c1180d1f42e402484029513881c40f6800400003a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 956019001 1250 956017751 956017757
    0xe09060f0a05040f0f060e07090f03030512070519030b15070507060f1e08010e010b0910030b0406120803041718040c090513141b0909130f0506040b06060a170601 71
    0x80314240172041c2240c18640024904803d0001802107403030b44030240030f02400101e404181c4c400c3ca1031703901030f00744d01c00c0e40c0d0f024001031b018a000a0569001d0020f8841c1000c40f41c102d1460803108010042c020305d400e02c84207214071180c42c4411000b821510907540303a10790140080c203001d420a2400d98030110180300d80c80401c101e2801e0b40201d0410038442ea018401c2903226240c840d41024115500d0100507000820940c00512601059544656406030b0500050600041920401000c034000d4410b940110880e0801716004504014090000b103101d140643c41d090b01028000f00c4810b4107215100507082e441030240204050741c5815030020340d07402410b0418100c203c4d40e1b20045004980203c0452800c00d5448050034900750500c1461540704800ca04407420503246035100c04400e019400010307001d42030400029803140300107012203600170303040440007811918626080c0d54404041b1401c40d20b010100700821042d04101081d01e4030450661145044001314010303694440e88020519410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 956020251 1250 956019001 956019011
    0x1b0c1502030a0615020a120305040302191716120503040b15030a1a0411030606030a29160210231b0a0e0103060f26030c07060e09060f0a05040f 63
    0x1031901310910b040c2089241c0d8000d415181c44508040210407a5030b0400c000f85400c03c020080041d6010849010728040310700341103038004042c1401d405508401484680d00b000009036000b003820003c110301d60041c4a059078031440e107407a15080b07c450009a4005000ca4541004a03400b00010040040580c80c042e0485900340f1007622140201d101ca4030145040120358014002032207500d00d01c1c1e2624680540c000c1002d400d00002184e559850b01c00701400c10582906c011070385400d0340c07240d000701c405020403c600904041d0003e201c0000380300d502d038001d4400d8942ea000b501105001c1c5d0b81c000b1010a600250005030340300540e504220082401c586516408031800c0704686030009456040d000d9992030740d41000b00c2c030003d001c40718550400540c25003e0801080030070700944985030a103c01540450400c0115028949180109030800c04d090041e02c00211b00e555200d881301d1600c0c03008407400109a162030041c40604220100c90540040200c1401c0c03241e801c01d50040c5074041402800065 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 956021501 1250 956020251 956020259
    0xf0304110a14130c120c02011d1f0e030a0c050c09010905060f040501030803060d02010c082101090e1c090f0e04030207150504031e02030609011b0c1502030a06 70
    0x1ca20a0380b0b400c01c491019200c07203220054200445811140100b680342008120351482c0040c00401340059400c485544422030f600c0524400c0d000841c030280300440035281c0b00d6044180c90780340d4070018040140a00302010102c50400c0900072001c072843c0034000b1714a00020f0340000c40e154801f402080d14640300d218080c815070340b01d9000540c028411281c0010300390401c0020440c1c04095603c40c144654106401400860500d60840360040c4084039000710490382440160790940c440c90001d00041030100e400d204540e008070500700f001015103018402c981e2590403980860701c0388000289a03134403651000c140d43c40320181d1031007111400e0a040c1c12080d0b50304c25010300201b03a50021140d00c40039105000030075404204d680040c001c5401e911003d50b5030b00d00700034075a000f00d1002070704031034421074200326060f00c03080c158000e01c1d009804d41d071880c40d180c03240501a180c9212021481280e01070042c12040c4180c00030b400d019480038a141c4080c03198035520300a50800b07800e201201d556000005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 956022751 1250 956021501 956021509
    0x608070203130e0403091e030611070201120e01230a14090c0d0c09060b0903010c08010e0c070303091e020a050f06180307050d0516051e0603070e040c02250b0f030411 73
    0x21f00307021580040b00304c190a6140520a0760315500c0380490440c030506c0f2500050b17804c40d008045079503c07804001121104e1030703040c50140074130700b801080c101b1580348160003420610044074400c0d061802c06000220980340c0340c5200b40e02c1100c2080c0150024036403070740c2d1442c0c9040c4010100d40110b403103004103915801440c044800715480800c081d500041c0c803c0d40340c1000e014401521500c0d0400000b1589004401c83c0c403500010300382c0c0c501a80015003070301058040c0e0b2254044940041c0a81ca03030581c1da11070004070b4841400140d101d10005540003a440c90b2483d480050b500d401f400050a211a0400c2001c0c07050f45c8081181e418025014085075603100c448014102da8000c03401458104040c1164222007092078000e82d008003a01e1500040320700c031101c0840c0740103000b5655290342e50f550010485d010180c10300b2655105090121140d0002d81c0051032030b62820040301590b6a4610300341902001521700e00c14001105018404140201d8141c2d003c3c56000d80502c0c61040c1002d0f10320005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 956024001 1250 956022751 956022779
    0x14060a0b0a0c241b050912030408030310050f0a210201090b0d0204032d1401020d060e010614070c09110d0c090911120f0a0e010f060608070203130e040309 68
    0xc07070403d541c038800303804110307050240001c2000c921038107561611204d0401080c610030108014018a01e9042c47c044294080044034000c02e00002641d407203007807000c0444c04440040c42600e100e5448204c80400c0ca1415190190480d4095a1244031542d0b411240302d090f880b000200743c0c144115540001840303820180102400203000d180103070344074150725288001040e2102c5840c1882070148652500c1021018080221030f003004cc50101298035100c0305000e440380540700080300c0d04246e00082e08140342080241a9000e64846000c00e4401c004440c0c5207005402002e000c0c0d40c0011001c00c20810a680700c01c1d2844001c030a001e00e8600300340700280030b6500865004001a02a0004100c079540c40c2c441c60b00e004050306982c0c1e03d015912507020000100283c80403410b403040700c02051451500b50302030351071051003a000f44100603e00c181d40c40146030328418400401c1c111400204020710100841d0090070702da83d0401001800c0409108c1000002003048040c880c1ca07803800700c3c42c0142420a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 956025251 1250 956024001 956024033
    0xf220c120b100c02271510110d032d09020109121127102301021f0b120106050f09040b0f04020402090603040506190c05040e0a06030f0b0a14060a0b0a0c 67
    0x8820000000005000b00c00040111010400c113114004442340100420602c07262200303482d010890203841140740d0296204100840c1c2c1c0400481400e0000b20001c2c0c00070f1140314000d0300c07044200c3d81c3c0c0d2a4126080c10348108001c0540d804102208030b1854a03d0350242c1c1520a41480c48a4035850a22061030300005c0d00c107101040710303c1d031082040211070700c0c00d00c1f4107000304a180b1002d6166600041d5440310701103040741c04416048000015000c1c03a50280c1e904042c0145201c13101742c41c0c0c403807a50081401307020b01c1d4041c1e00c4500754400142000441d6501903580301e120965242e440e103420100403074000d0012680503808024084c0165180805540514088c20140a03c0d04021204101601080310b03800c802904000d8100300300303070b044816a0308449500c00204c10039a15501303100d0080281d80c10082480d142101402c080c000c490040724451a61140e08200508440514a0182c20101c45055110204480910401802c107000d41034288141c10701c440b148600c0d82d1a050f16001c4146 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 956026501 1250 956025251 956025271
    0xa06110d05070507061a011b02190923090d080702070b030115020c011103091908070303020309190e0403050f0c060a05091b0f220c120b100c0227 64
    0x31318401808064071070b0721104a840404070f1030f40d640301c1c0c3c00681200540302012501101c40354000f403d40d100c3e0b078500a9000410030030340407000c0e21035821000034141e8009641444048071058600c5c18023507424640500b41c070800400e5441e100c04030840301404000c210600314000c8a0001804e031080b0742c05140a0001c0d00e007000b00704c0000d000001d103005c81e84d60003141041424041d6003c0024003004844a4035020350f940745c250108600c01840d204040d074800d211505c1102c60010900d5070201c05489401d038200c0d402580021640602c1c0014549401000482c008120210700003078051002050084100755589007811080c51545041c848100c03510850345444d1410485146401d204010038080c5948044a8441210000c80c042400411080d805100000500c0c55604d00c1402d12020403087c11405100312403015400030b08030b000350f0011400c000d0400300380c0002031900311003014426415a55082030010590200100e11030650a45906482c1c1c7c2090f41e201800400c161501c1102121 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 956027751 1250 956026501 956026507
    0x3112119061a0901140d051b03010b0d030503070f1b050604050d0302040311210708150109020a0e242a030309030d05040809220f020c0a06110d050705 66
    0x42010001d45511041c0c00d80300300c2d424000500c06a4421035640d041d240f0601000303110a064601250b80c109500f079010f41507224544030180320541600c0c1c0014041d0342030b0000d100da09642c40522001c0203e00c1c0008020590a02c00102602d2003106424291495441d1200e0a00c1442a011a1071140da08080c4c130590080d4041000348082001a1684401903142c2107103401e2030740c2c8a81840f0502c10310114829400c0000c5290040341c14009500300103858015112510754074400780307913194100c50025001004c1c6100000f40c4064030b10076514001e0551b2070340c03514404c0354410051080d000600c00b00440a100e20144000b002e020081e00300c1e90000803141e8511102489606078501c4885a1040250700c1002001900080401618a0100d46a078046070a4490b0704d4803c0850048002040e00085030000c2d820000324826814494080480b40c1002022842d5508000380d21804032108101d40c0282c00c00d0700020850350241d0b2612102c0d950300d508141604030648182c401c2a80d80c600055004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 956029001 1250 956027751 956027753
    0x405120a0308040312181b210809030709110712021203040204090f06051009111908190f02030f090703030e0f060712021c170612010f06090509010c080103112119 71
    0x1600d80d034015154416031804468007000424075800c8206200900b1a000440d81b8045622f08020744405880320031014003950481012425158008a03400d40300344170b510101035a0b0b2800810480074194001d40c08500c1e60342d070b903003d10000d0016001d084803004800e440b08000f00d4030502c96940075543c50220810322910308031030281520180c020190050000b00000c844072440420054414078942c100610742d41c0d55003483c50144881260309070503041c01c0540c048010003296000714031501450038420200c7e168004015a500140c1c0001000304840c0d0366140750b02d00c1e01c0d01440c0ba8070344000304050324043c07059030f40c03003081489110400b005d45e012000116880c8005d5907000a032074010315188031309469186184200e001d010b1300c414002d800c1801d01801d14103080d0000c003880403800c0001d21a0503a241c0d40a4010001110a203942c2d519003034200e681c4507c1642e4050489802c11b0380410221220320030010b49032126000c0008024021080c0c030340c2c0c0d15043c00342d2110081d2540c0327141031140007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 956030251 1250 956029001 956029043
    0xc0e0310020c010c050306030303070f1808070609090b10080a020c1e0f03250309080a0320030a050d050606090a080a0318051e010e0d080405120a030804031218 70
    0x381304260a10805108101041d00c000043c1c9511145e20b18103a00c00596941c026501054110001c0c103415401030404100380b90001149022117445a8803003020b99515206982155850029564007003c1c440684031450300c542c01c1c264106003c00401860000100382040c9801d611b103219040790906c48607000168001407150b144581502000346207407807010412041442c0003540d01031380f042c0c641c050100070315201e000c0a50181080c2803c1312030b032002e24107000d084002d59101142c81401b110400c2c08007244044142ea841e0251500e489050071040310215000d441c009041e03d400603c28451840140c0d40c400341c1500904841d40540643c80325800c00400411840100031a07a140016003004030351503201403a1234038040d48c0350354030b034045181c40101c4440510001680d0b021803825040c034180a171040080c8100c510840b03025100750381a110658a410035040d015011030039100000d000310b8000d8100042000c0039401c0020240e001807403020301100225800d5513050003580c8083e6003101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 956031501 1250 956030251 956030261
    0x2406030118020d0b0912040803120a0c020712020409050703210c21120204060e01020c040504031b0503040f14040f05010305060612011409150a0b010804060c0e0310020c01 75
    0x10000c071164040c072500890000409100024100700c0c0c900d0004088007410700c03c0c1004240c40c4282203a40d40d42c2d906000c0e80d00d802051410206200d05030110303c0b521094407400340e403100705802034406185024004060b50b080310106a030840e4031070040360b000074814420034000e948100c02c101d02c01e4845200350070700e0001000e00751050140f510008808140d02100c80032801c103107030313521690040c0d41e0307071044543d1401c50207600e01507400441d010139459044004d903401d20500b80d084503403030f0391071504200550318140d80240c089880c0c40d11070700480440c0140041464041c0040700e24055464104070b5100ba0729030300c4140c104403004201c45140c07a003405910081c103500481805194195201d290301e80c040588824800d6100035004a8074200a400003c1401d050310301c801c1c0d00b860410711854480300d041c603142c5080301744c801c001131070303540c0b83d02c81d102501406945e030003c5e03607542c2c0e55040010001880401c007480040b1050340c9c0030790380400441450210b00100561540400716401c0d094034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 956032751 1250 956031501 956031521
    0x7080409020c1501050d020d0305070210110f1b06030702150c0405040b1905010809070306091a1f050402090402070506101511280f03020f0d090503031204030224060301 74
    0x2111004002d140d403980c500080c102c7c1c0460f00d076803060040340740684051060607402508881c04015151744103410040b200e11489070901502c1c804c0c04000c050a8484540e040007611204058280c00c5071420140301035640300f12940115001c03a140518007140080044034403c0030210300040504c05070070603002c2c51010300020380c1ea81001c3c40d450389925036034689600a150400c080c0c1c0c1c0001d08010b4007040100b00840d000300701000640c540c0d0800d01100300200841000d4695244046490081c41c1150f00e03d03202460426a45440d00b40070030440030b0741c821007855a01540901c210000b040c000e0203114060072103001420b00961901601683d501035401510b014000d11200001d003955001c25540e048032078081b08002d00024210003003440102d00c0c0c1c0080c010907140e0841408064000031314002580c88c1e0400c8035011010f4420445c0c07009050b0180a8241d003003480060038480c0010007039a00548a401916001705c8821607042036101440a0010103203643c41c18441170303040a106060000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 956034001 1250 956032751 956032783
    0x1906180303080604092609090903040e04081c0501090213050105090a170319020a060e01050402010e0d05012406030b0402040b0f030a060e040b060315160f0507080409020c 75
    0x5240d91030142141000808050180340c6a2001400700005000c3d20040361549070301141d030030701186409610542020a8481c001c80381780c008a13070b04d41000819241203d41d20707900e10b101541d803507a5030241d40e0018000c59202000c07000c1d41031080b180c0381c042c0c58040c01942200684440c0c81007444501d2030110740c441414010100070460498645045210607030302c110306018110b1852002c007920398401c10400e8003046004039034540e0400d03030206442c061180101d60500a0f0110000d20030b00b00d44003640c000f070200340d40c03038400c004a003009292007003264055000011040009084071001801d0a4980c8900340c144140c140a241e03010f209501402100b03540450506007413001000c0f142c80341a0390071099050101c00190513261542040380030340f0103400c05c20303418242840d00c51120001512294840e008105415844d15408650b00d4480e85c5c042541d100c0500b80081c00f035455003800300918003004001c21010022486000040004000500c00165110305007009a410200c540d030007002c034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 956035251 1250 956034001 956034047
    0x2e060e0f07090605030c160204060e07080a0e07121a010e060a0605030c1e0c0114040c090915020d0617031806190509130504061508280c051906 63
    0x2200d1303441401e890f44030707811035103c0707507aa105644009511541d805e13000750307c9424590042054020400c006004805036100c01400341c0b200100e000c01d030b641c0e118120f203859111a10800c007016188840c100b10b03074003980d0041000309034003204c2606d90500360030028450f00e03020144403860500a10040042030140740c09401c60601c5061103543c1d1140d80c00781c9850235101c041401c01200d4402c00c586041c4805c0d802041034809d400803141604508540903510408080e034002000006030190f41c4005900c002146440c05103e00d91310020b410025036031120540c1c0c1c40c5c003c5807080c200481d48180c521080000c540300d1a04454800e0032131047c440e03c5028103800e1014142c1075035401401d40f10b00046040042d00c0341c0d00d00b008a41c10b60000c00760742d1140c80c107010a010600171a0b504c5104c4003100703030054000c82d68684c1c0c001c680d14840d11400c503c6041c808250403c0d00e0741090190f90109204103c1602400c0c0e5450004003505c1e0980070100746641ca51108000079038004a19001568040688040b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 956036501 1250 956035251 956035259
    0x1a060604081504020301150906030c0b0f0901140c030c0f01150305191e03170c031e06130903081807050a0b09120f030a1704052e060e0f0709 62
    0xb4481044a451071007542a031008141150760079041400c031080c0d480340301c0072199506d00440000d40114030040d02c020083c030074081a903503001d100315007814958007005850f019400004407403900344044c0340d010f081c0003400744008070b400600003400540b404000405140f480e0407020341c215151100700c4105181d0b90301041001400c00b003030111400c0d01e4884291781e210450308000100030805030741c1e040840780d1465940101078208002486045ca403031803251555545091071103c2d4442591032030f00e400c501c2209507030700e080c0b81c201003076000101510702e200c003403940141e41382540c03a0002d048001c1078070b14003082001c9600c8416010306550400040448901c0d02c4007142c004240380c02040300c501400542400c071074035144e081ea00865920310031200072445440f0b185480341c029100c03110004800490181d007c4403590075483c041e541200c050031080c85000c0101c5440c0b2101c5100110f20060081080d03c0c0c42014801c0200411089000b8241840e10310800002c8041c014200342c103006025070180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 956037751 1250 956036501 956036503
    0x7170301031106160b100315050606030a1a06071a0a020f0901030e01180309060e06040830070c1701052e0906140102010e210703030b0d1a06060408 65
    0xd5400200350b0b100e079524a07003001350980769030340c070074000e01706070a5030b0280700d1480e21200918007168020080c441d1a00d560a1402c4243c803020760707180e41e0201d003e001090a401c0c00ea40080c910b0171080e4a0324060070340500c007081b100d400005064a0708a0815160f110580c05044510703448081c0c0c040445c40d000f403907480d100c654014407a41604065a500210f40102401d5000003108a6014400740ba09070840c6001030a0314080d004074000a540c201f901d03056420f20b40c054906035015040030b800c4e80401c2c504060006048520600380b00d001d600c40c80c180328601300c001403c06600500a41c1c0751142404d0a82c0860700c03180801100c0340e803612080081280310180b200c140403d410034040a604010502e511420701244c0181005030b242801c0003820b150b108a0740041e02c2c0d02a00244040040145201e490f600341c10b00c1c10200e014200d0100c950010b43c50014524039105c0d0070001050142403003c284a007803105000c4405825640000c248000b810a0003580694111492440c040c184a80c103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 956039001 1250 956037751 956037773
    0x171c021504061a0301090f061508071502030f1b120a1b03030e030c28020d0b0615040303031e0213050603042d03081e0c0c0c0310020717030103 63
    0x648075950b64190841907054120300c030b000b0700f4070040091106c0005800e0540910420300400c5920900c2c00600c10801e00e41c60703004000b00c0718208003410003039203000d008903005941100100c00b18003040000310000040700307001d40961070f580801c080d0a1000c082c2d04610344018071940c50b1540509210905000da440b050135074442c501d14603103002407162443d041c3c0c0a880c054055901038000807a0f40c031380044001a210902031141040b04801d510194042200000110710107074203c0302d090300410109011101e01600060040c05207682c006c01445805401d4105404c12030002352a01a1441540b02c8107000c400d11040058045107401100c0151441c41981c5100d0305018010100c0080c090014107001524a0401c82d00d07000b1a05042400c9003030415144070085002c1580140815001991441501d900c0c4c10090764200310703500c541e01d41d00c0c4c1c41d4000004c20001881655030101c0700d82c6040c03224119500c05840090703181c0303080f032030a0001d1000d0070700b5030854600180b0040020803450504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 956040251 1250 956039001 956039003
    0x6150e09011824060909020f120a081602060f12100f18150e011d160c0f0203010e01020306040f0218010e061b0c13090b041209171c021504 61
    0x504009a0300e90b4143d0b074801c5025a052030900d6203802d02c0012440fa90390405011103100315808001511502e0400c1310005501e024524035520540b0f20b03070000f1700004000c104448840401209100181d40001c240354400030034103140e582c0224044c266088112103058202c04170400000303086040a0400a601c61140326000c1c0808148039079100901c01c5601c00b551105201d415021000c0e11104418440d100c01c0c0b046890120107485411a4121010403031030280c54071a90801390000c9600c01110b0403015400191210304650040400580d000d202d0030600b00301107000581c503454a20200022500403681241403c0d00400940040203034418440003c19001d0030207074075000c00703007004c14094050302061991a400035811350804290000d0512145081100c2e1000b010450450b400c0035034101000040c40c1e642010040342c00225101464554142c692504070041580d07090710380c0c02441c2c0c031900710003150040000c0e000c04050400d03c10000c4081030000707090102a858480c12030440c0200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 956041501 1250 956040251 956040263
    0xa110a1203110906030a0c270302040902060f0a08040b100e040618051b040b0a231906110d080118090302030f1206040b030d0e09090a06150e090118 65
    0x141c0d1105140c40302070b9242c0c19009402c2d1601c1b8581401641c0060400301d04083c041541c041104506034120507040c0c60b000d5100394040440303032950342800302a18000d80c049901250a002c0e0710b0300b000807100a481e0160140ea00c400007401e00d400c18500500c00641700104d1400186c034140008440d0810b00f41d005540301301c0000301d0104c603440791207405401c814020014060468080c20b1003a880c40d003015400f504680400004c0d416404110f042090791143c440350b91452031a0040407980c0d0528091034010240c004010000360200310154825181c00080c04684040450070000b8800c200b4244280c4060070002070550401071900c11141e04900001c5901e51104266401c061082c821342e01d502c403d1001e607684445000b11601c80115003124254061071800144801c140b42c0005d12205400503601c40240744141c400510445400040841c04644501300c462000541036226541d900300b00d82581d01d03e940d09004403d181114090060341080c0e0402645a0f00c200300e0000c0c250301164809 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 956042751 1250 956041501 956041511
    0x1e09020a0e040f062d1d070207270f1e06140d1115210603010507140f090a030b0c1207090608010e04030c050d021c18050103110f030c0a110a1203 64
    0x90001c15400c8903422594104004150484074900c6d601400c40c06103680342c00f0784501e543c0700c038840c2440e95402013185620300c01618010001c1402c0c2d62001a48074118031000c100340207030a94052105644850090259669480c200040007200314000f0f06070404640c0340300310181580350310110280b480343d2a403240082113405440704141c6c0048400814400b03582c0c2d040d0130780324807400507a030b6030031100d031402942440000f0740301324032816043e001c10703e041604500b4402e051801c2101c0b42c008011440e0000d03039106012020860079602184520145541aa031b1080290840300d04500080c107030305c00744011b4840034421550441200740c10744104400301b40f10381c2c0d01c44c02c0481d800c94001d0005070150099410b103511071903010514942ca0f19902e000980f46201c084411101c844006144240c60301041200344040c3d8420303080559001c00503000d10f400c203000701959140a91013514140105500000d04003101a04590724003c043d0442003d0309040b901611130400342030007104080105a079503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 956044001 1250 956042751 956042819
    0x160c3605060105120403030c0e0603091e010e010f0222120b1302090403090f0b071509050a080c0d03060b0c03031b040f060e1e0a1e09020a0e040f06 65
    0x90b070503200184c0030b103031030003649040501340a03004001c6418000c2c00951084000300c03450514030300712030154240c04010410800e2030a41e0f90001c403034210b00c601c243e549651080003410000d0044070b45c9403140a030016034405020684510101586c5048004542d0a60b410084c1c0281d40c3c120012490b00305150102c2e581e21900f20a46904040000039072000140041c401810740c4040e07000c3c1600c0ea0209194452a03d60784801c1d014040c80d0070040405040341c800340010025604125860340c40b0710704441041c0e0141e0359156454021520100d0309a0016141c4010940e150080301c0090410042407032a10010410075034076032100402171100708003512040800500d080303048600030031605440c0020395440340d100600d440c5e421081141b0800250079080ba00d03a00440102815107030050a410444e850404001c1c2c00e55002c0704c68900b0200d0240001406540070300040000300702c5075948044c0c0c034422800300011030b03583c541ca4298079031030244184500e2a040014030906006030902140103078036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 956045251 1250 956044001 956044007
    0x309061b0c080c0a0503010b0f01230f13050607080a030b0a09060603090605060a26120a050706180c0b0f0c030406030b09070e180903160c36050601 65
    0x1000000a14034048040006070a02c00864501c85400044030110301290751030701098242c807180f0450950040701c000d40010690700510303098100007544602c031400f111045500e9602074000e803010500741c5000064070360f18065418102c0c0003404049400c10704000b03d0f0703195488140a00c0c6115801e0550311410b005c8250348800e1135100815600200380400c0b42c8821004002c0d103036200d421500141081c0c0840c540e840c003070b203080c0e00f6142da80c9441100325020610b02c5c5038214122086c0d1520f4050760340c8207001880840000c00e0018510340721030395515075a00d03205040b196502880700060030588002d000041000c5000b070100c854a0694030380b18002c1d0b01c802d105600c14000e040d6500c1c440000d0005500d60103402610a1110407251500107907039060054039a550914070b03240d401000107040000c1a64a0300550341c1041711142140c0c10034460103265000140e5076002aa44030780040c004010dc070220080c1061404003c0744210100d110724524810b0b03511084040701222529030b8009081030744 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 956046501 1250 956045251 956045297
    0xc0f0d0e1e0304060f050909040204111903060e010801051009110c0313030b100621090b18120f0f0a020a0f0f051212040209180a05070f090504030906 66
    0x7807804000100d056081291a0350303620502ca1800450303460b0a45000c020b0140c000c0d02c82601d000b503c1050300e80c0d1254200001001c202103040ba07081300a0204400364151141c144404605580700051064108181d190007094168007988480e030600d400c010b80340c0f20a9002100300c40100300040b0f00480d01e150b030030801d4052003400c1c200301e10010680d18038080b0403003464030489000d11100c0030141c4600c030103d4010380060007500d01141601c00c880c0f80900030b9405c40040f00611602c001350940c0c81d580d85418410701130303543c0c664002000d40722018805050000242c000e584000e03107880c02d500c100c100c03685402229940d0b01d0081c00850074000c1c8078001c0c0921402154011000500c00c0c02604e400764418000300019905d40c0309038030100400408490840f040705101104030b822a9849a00f0015280002419410350b2001d4607440480c4c03a40c10420244000d10807000b520001c1c2c00c0c04034103030400c400c0f580715103030140c00c0c0024040840d42207820401900c2d001e03c0d00d14410102c40b618191040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 956047751 1250 956046501 956046523
    0x804080f0706050129070807030918020d0f05150d0507210507140d0b09160603023013051603080702030d090e010b131509030b0c0f0d0e 60
    0x9540081c0340020401160702036810f03101101c030b4086904000d401c095a022070584c082d42c108150800ca0200440e500f44050701c50300d88a0b00d40b0515507501d03100b0101c9158107100081c55950f401180c843c0811001d402901c20051103224108414582405103903900102001a180220304407880d01090100074030048000e000a41da00c43d04000d840281c3c1050380e0014141511580205000810140500e00e80041030717240c0107110a61140340e82e00c503000c0604010f04083ca0314032030b926404110151082115000708840d450050b02d0700c15201c43d02c42d070020035107482103594070303040e80d00d10468200780c0c036040d00003400160382c3d0f80841c0a40740140c41c0040c4004900491030009034000700b04035903a03008241d0303941300b0b0302070b0750042d58064810b440700741550186c86000c0302d41e03600612682d00f20700050100b0307415105610004a9035001700342080c004040d4000009813502400b4070901c80b004040c2074002c500c800701d15191658080310140d65008144a0078559521103140103840b11040014000c0d01e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 956049001 1250 956047751 956047777
    0xd03030e0f070f0b030103050c0402030702031306050901180e1305150c03012402070311010302091305090f0718050a06080d0305071b15051e0103050304290703080408 73
    0x1d20852114980d030b020103204195141140e5080811100c0224059904983d8004000c1c0450007000c800c01c80a500000d2108085101c02e110448000468810442c0140401d440d003d50700c0031001c0004003149803003c6c908080c3e8540d0720b0200140307500c4170080c903845110600c9056410900d40341c10342c1030039800c2c0c2c0001c440ca9104070500504004507401141284c6082e54000207100c11115540d031080f00c82100c0d80d0150f044400200041181c0303501d5421032084c14500107150018440000d05541c21006140161075910b000b0801e045404002c404403c00f2104002c000a5280040034180c014042125120070b07a15000454002c0700c180d040b0301e000d448400306550840c54807140017001801c00b11150000140c0520102c0031109082da11184440d401c100c1c141c4003c050903000001904014000490712941005482e22407018030520358060740c429009141e642d850035031b44948500c07440181c50701081d100700c1415100d04031001101d000e0355040c00d009055a40300c2c14218214003540340e04100e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 956050251 1250 956049001 956049013
    0xb0705210108010c09060e0f0406090e1c051e1309050901020903072c090c0603070c0b0a05060f040b03010905030a0e01020708070302060307080a0905010204090507030f0b06090d03030e 81
    0xc84201500d480c1660b030900000c020312a103200d011218075034a8464000407800c840c040300e18608060111b07054900c1d003c0c0020503180c0c0d80b0345000003281c000c00400302c4c2c240c2107074103040140680c2c426070889120041c648035081c4070440f490000d8120401e00d10618101001904681c1d20301c2c3c0e1015200200f500090801c40c0d8900300d240e6070b010703610040c80c0600c03074000e080010070310000d20b0002e15135407000c0c084102c0c580410380f24030b50004040607241850a104074008408942da07140001c51040080d987c840b008024546040c2002074800307401c814010b4245001c200598840503040250140300722008100440d850010030700400d080307440078149000000d100d4850607040140d101d500380c1c003a4225486136641c4c01e400fa8441c08503002c020b60203202017020460241c40741c907085800045801d03002071911000e0b500c1e10300f2030f8031503400070701f049840314100710180350148903288a401100205004513900080055168411400a40c1c428a4441c0e48441454803981c080310202c1070400448070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 956051501 1250 956050251 956050297
    0x14061e0301090f0308060901061d0105120114030d02120d1d0d03060f06020a23070b0a0305040b0702190b130206030a0203010302040b180a1d0312011809030801030b0705 74
    0xf00352400800341d021507102d4001ca8154144803006d14101e600a558a60501c22810805000340306410400c030f04000003441955000861450254001e00304088030182400c3c0c0136080c10b0600010a002100790b4101038114148401c00c80201e07089900211400662a800041810848501c2c0380c0c0030403040c8603180311100c220f5090f60026040d43c1415002c80029a51810102d80d14541e0384401450031050703c40340c80d1042401d0002294052a08040d50000c60322614114201c1d0060300428002035114400e00c03050040180b040e5400681794400340074000a1344884418110340c42d60018041c409a10019141c20724000341180d9842d8006e00f050b80e00c0c106200164043c2d0820b000591087d403510070b14a4407440c21a09132040e040d84034070b04141c1503071030742c00b40c500a040c0c080f641e2011614204c0c420004040a00080031101c0039a0b1f0500c01c90f504001440301040360003004c610400f8038103103100f8003107500114950f045a03030021300d0711001d0b928072008035000c1c020304c001010140000c0928503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 956052751 1250 956051501 956051513
    0x2b0f120f05091c02102d0b01120e0c12010b1c05070b03010513020307030207060f0906051501021e0c060c0f1b090f25020a0c0914061e030109 62
    0xa001c1d8040000300c940080100f8010040300030781da0710700f00260748400e00c01003800a4075048050390046a1003c0b140d44200600001601e503000300810306d1450750303400503000960704441945403007600c0e100d080042c1911200d4682d690240e074078083e81b080c00d204000b03403240c4100350010b040521014281c7c09201070824007050403a02915403c40c0e541c050300d800030640c8451101964100c1c5ca0040900e1010b0409a070b8a40081d800a800d4900f0160200039180c08207609000d814040402c0a20002e642c0001c0d0a041044940141c40c0000c0700103140743c0c41c442d076a0f00007030444646207425910740c19003441980c083d18040d0407203034542c0c000340041401c0040e02400318004150020400640d180c002039200030720101440c80b104990300241080201d10f64010072041d01d580400400c008001c0e1a501080c000707031107103100445400503070080745030100704005017001400500f41e680003400f00003c3c40c1d01c0c26001e210000c01c158018241c1c92160b02d5100510481e910305200054020005000d26040c02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 956054001 1250 956052751 956052761
    0x17090106170a1401020f030c070c03170c0d0906140c010b210f1c0509240c1509060403080403140414040615080402060a030b031203092b0f120f 63
    0x20f5a10401407542c50301090700600841e900003105520481c03440c4e4a811000099070800d9000395019a2030a00110003d1661440d02600c0d01d0301400b0300e41c540e401c4407186441c01e000c401c1d032030041000d800010452183c0000854200418040d034154031211402e101c1c85c018121b54440d1540aa405000c40c4484103002141c0b01c401e003400b02c02d5070158040c45851343e036558180c3c5a07081c00242440d510110a40c89940a4203038130000500ca10851420421960a02e110f000104070a8140018865175000f034208a5402650042c10564640e40b0f020440740303464440c0140084c0078042c0e400d0006003018810001c08041e03501541c0e1040c0c4032520340110040108080201d01c0c05145060000309241ca100891140da10045554942d00b036034550b402c0c00400d80200e40305a050688500d884151f69a00303002105a550446860607103900e0280001032a185c0860a40300c402c201085c2c20b1041002000d41c030102e10103007418000240102c0301c5040711000e01144960721402c2c60014699007481d6103401c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 956055251 1250 956054001 956054003
    0x1b13021206030f0a17070606180b040c2f0111070f031d1f020709020a0c050606040e0a14030909090c030706051801030b0d0b01030302070906080d17090106170a 70
    0x1100c400c0803114103c15030300c92102e80e0280115040455245045210030001d00200348074040106805039202c0c0700405044c03d0355041041c00352100c00e44d010a080c944200b10744101103142c140f68581e600b80340729003034818440c1105504c0c21a8850703007110310001d400200078448d6032241c0e00d07941d6030241095203103800b5488085001a03102d2500700f0011541c5002524000f000500e80e600d20b07031a98200a10040c1c680b0000801d40c0144407001030400301900c05050708468685a0b2403c1800341d01d0040d0074584010000751246141c940302549002d40040d29280450344144030026900ca4440024039501800c445107910240d540c080100303040c80400c1d010040e60045d0b08890b829510f034241964a8050781c00d58401da041e003101000040d40c841c0e040fa220351000a4200d510166064543e040407000c00d07082640903a00109041044e5031103486040300408440c40900f01070309206900a184101001c2000301c410b000c040482c400d0f904c294031410082c116500d811a04180801c003054458800c807030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 956056501 1250 956055251 956055253
    0x908010c0201110906030a06030b180c030303010602070302060d0213030f060e0d0e100e0405010b032401171f08010618020c0d1815030213050103020c1b1302120603 72
    0x4404611078014060b0b82c00341046180b0840c10140c4102c1400b5203604000c00b00001551100c00c0040172503010003d150090903451387e041c2000c54524100c41c0341c6078060580301c0c0244c1c0104010043e041d404240070b415aa4101c400c295101006000e84010b030290b10754820491a15420000800c650655130710041c505c101014844c00503ca0b80040d1600314111080011a40c040702c3c2401600d000d11004092070207505007110301c07440120129007140c009811046122000109100f03084075101d04d803565182154445a140d00c0c5260002021032424990460845080b4404240711621221802800107040010040780365a1094840c0c06010144180c4e14001085140340e07000d00340c02e00131180c2c107000c000c0060400041c0c20304102c9900407158030701150b84a04401c003081e0844e01c0d501b22000c201c0266405602c1d801030007207907482420340780e0160341418810005040a00000304d010b0b02005c1e28681801d00e6400d001d4041004040d4110120034450310010703007070104603031940c2d1103801174100750 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 956057751 1250 956056501 956056511
    0x507020f0607021e130906050103110603160806131b080a090c171608060411010302040806060405071806171b04090c020703020406080c1905012007030f03090801 71
    0x100500c01d0510800c800690041821011079062105040741d0034108a4040c3c80004a84c40034030449040703c0206e88215291601c810040090240001c600c4418200480b0154030b582044071009114001120780c4c901440b41d49400141141e0b03840380c4204a07420071071018807203042d803201c4428410000ca40340501091404010820240c01032144071401540500e80f0100f16003012070401d6041041003041d41c1d20f128041500303582d01d242c000207500504000c00207013510f080038a0241c0d10200c4068209041507c107100130002e10500054464114005a0740040d068032212022113640f0100005031441588074600010b0a65001881c606000b844e003098507869140c25140701318000d25841381c89240d220900003403003d18001c5c0d1044800074510700480d5401e0f5980e50201d4281d402991284c85250009101c0308036034100109003003c09020814249c01e4142007100181ca4800c40d11302d411407040c2c001040404004040044074041c54101640080300c3c4c1c554600140a46060b0140c590300354201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 956059001 1250 956057751 956057779
    0x70611030f2431051e040c1d070305070e0d06050603100501080709050109110a1d1e03010b030a200a08060f0919080703032711010306060c1a0403110d050702 69
    0x81d01c140341c02440304217040182c0410079162003102140141055641510a040c0090101c401000e605054140319410148510785100040c044800007487c0c542400301101020500783d60f0304041d000d4440d0701100004460b00e520010030300e041c03070280d0419000d0380350000109071800005418000c43e94a070609102680e2600c00c07040999248420143c100042844024112170081c0b1001c5907004880c1c5031071032603140500004005181c218500d04003081204180841ca050030f01a0b83c2a8500640003030600146560350321a0b5400310401402007482c0ca100b40100903516600100014601c0d442241c409080001c04a00742410030ba40d00b451500c20b0340c1401da01c19059200c810f0107943c00c90066402d000c1c0549054000c0d06e60741040c107001000840c48802c1c0646030091010320340707000d0782903500c10320352384800501214102d81001060281e8121b0102c000744c0714003e02e020403041e2101c28081601c5a07d0203488040b681c00b0083c000340500010066201c0c2c1c408090314a507030089504161864603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 956060251 1250 956059001 956059099
    0xa02030918091209031b03030706060e2e060503060411031e0f01032f030d030b011206050906062a0d021204050607121101020f070611030f24 62
    0x20b13220900b6019000791805106204011140218102c0c010382500d01e00130550390341c0b8003211015004030114076070318001d10010404510380300720b19007600a1b0200d02040c42c0751540e101d40070103102d840700300500000013419035200c58000c00900d034041d5200e5a220b052070310008c9442465a11481030210704100003c13404a00b070000b542c103d81e044079600c00d0200341601000d5a800c0c40c0281443e400722010240ba40d1780c2c0301041469410394017913070005200c103102000140001815550180b9543c20501300f131109680b102015500b100089416641c1d4840b05182d400e00700311541a603540715042043d2120050302c0200d01c541110ba0705d0350a48a0040080c1c0c1a440070703004a0007001d42183c8117202d6240010000c03501c1d00403c142e45c2c100184d18138419620036003668419030204411000201d00102080341502500c000d140c00c09003054118580082c60034000070009200001c07a003454071080d01c0c07411180c1100c0f00307502e50192401031605c5840000719265805201c0400c12b41c08200101c080c2080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 956061501 1250 956060251 956060257
    0x5070f2a1a1213020d140c030c0f01052506060807031a0f0103030507050f1209010e0411030f1308030a0e0f0106060816140301090c17010e0c0a020309180912 69
    0x1032030140010b02a202d801521103000d90701501213030001030345c0e24107034081401d050050541c0b4880c503000b42408040907040c54200000c48030020300411350340d0a144402da800a060b22848128011455240701e8035490942a500c40030078007030325040c40c0180100e010000458888256030203404d10f5101041c02c0641c0b03101e0305400f1100c41c0c0d14001c4520040c00043d2003240240100c902440884581e00b0080101c0d60800030716004400159100003000110fa5070800452003031042d01f110100600c0d4560845c0c1011031200415071001d190b210030002d0381040040c0f955501540c0c202c0b01c0d09440386000017211004042825405085100d4555602c504040500800e019600d0a0303441403007a803203103800f44101c03170300007800300b0248649610700440c1904150050340c001c0030410070120304441790b803101a0a04001d40c008030b40d4420508014400c02142092040d00600e4500e0529914060507208074254001d0b0b1004640c8217500d000e03450741d41e034404251503004418403810b072241e406e01032940e804248 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 956062751 1250 956061501 956061517
    0x903171207111e03130603060f270b010917030403021e1008100302041107060e030c0d2010050a1a1c0501150605070309060801050105070f2a1a 63
    0x54858a4445a83c0c0450b405059020408100312401c104010b84005244403094010701d000940d10302042104d151840071740d8004001286031215212074509220300100c1170b03c50200c6115031104032a2603140d02c00c0110000034410780701041d080c80540001d0710b443e40d010b484181d101d500e00a41845101c019603161180240e001080810707520742c1c2031001e94801000600482202e2298070000001d83c0344d9025035040382c00101000c990310041d615001c0d044400190600709150301c103000000e0300110015000314a04540d0900f034038004688400d0b10440c0c0d4130400311a0f81402410100440303e43d070354001c18020410700c1000d007d4206680780300907000b8280351940750311841d04040300034204035002c007a20045025600100b6011400c1e08040c508103c25801840092000202d01050681c0705082c80064451854008825454080000d14501a201018080202d8441010100402290f12040c801c00d54500070f560b200b414198100b8122007031007440340c00841c12140340402d40320318013120000c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 956064001 1250 956062751 956062753
    0x30d0e010f141902010f0c0e09040b04061b030b0a060509032a040203040f05070f03020d021012060b0403051501030c17010603081801021c120c090317120711 69
    0x380218010403211458039800c2c0900d9650304100c02000d000da08805000d01c011180c0000c210780d2441c0c3c80e040c2c2142e0100c20b0391400c01c1a191703000c1d59280d40e900d00154011303800501d2983c2d02d4841e800e00310020890162807181400c1d84441d03008200340c15801081900c60100c4035a0009507070307503406446c581306e94400035916412000b13820700f034900710351580c5100d1450300740403c20350b055900115040f80d1040d0790580d40003040c540260100a020405140130340b01440b44004030b64a56804586805000e00c4003c0c803542d1181d5124400034030070882e50f0f4111040040c24044503946105a04c0b05a1260200740d4407401555801c00c0c40704224940d840c1240d0f0f00100e41020355140c42401e0b2107454140707801c20895521114004045100303100030f065014001c250b070045a80300d61001914000c001d00691800808011aa20189401c20300030300b2009035125020840303884002c4211603404d96600020811020b00000d80405400203025214a83c4d8511420305151540300050b81c000106590030052 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 956065251 1250 956064001 956064017
    0x30e0d02060114040c1202030109090b180d0f0c0507181103060901090915020a0332150f0d080c25030f0f080c0c1c020a2d0305060105030d0e01 63
    0x100e04045d840180e02c00698035258a1080200381d140061707034801e038820144552585107150900084a50b0242c0010b110801ca00a0f040d0720003074152030790300a0320054240b040f03c07030403903100c280268400f03000943d101d03056510094a80d81c490042d104243c0d1900106450710004c00c252609140440e03000d01d10040c800c647c240c6c6060903000240c10240360403504c501403140d514404801c3c40c00a049803003640c0c0c81c046180c03804a4a4428151b0940045148280d00d501080c000c400c5007200b2a03400c91101c81314401801756501c0410908803103158019080700b2201080401d02500402070200940c000040d80c0d0500c1d00b034140c2d81294440c9c90110503c004140306d0410000c2c100c0e0400d1500e092040e220114000c1d84c0d5260100240c22402c6003103416006010b0002c11440d00416400407104040300070030080c540341d00030481c2c0600501071858285146070422407180e00084a03400c00000d8440d40c1040b25480b0301d4010303116202071041e42e000f4440c094500308090301451720304450660603511004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 956066501 1250 956065251 956065289
    0x8090a051b01050f120105100e0f0f04110a03020c0d020706050a210203130c0801060b0f0c190f060b01020304150518100e09011a03070c14030307030e0d020601 70
    0x360000d0325101d80e5050040030011001c440400c500500360401441c1030480c5958580802d101480900d41c1c8601e042040c04001803600e40da90031b6541880346001da401004428254011900a0105400082034140042061907503990300d0740090405481700c1c0195103540c880702e0700036030703590b4198081c41012803028000c2c40000d1b8490500e610881e0031203412043c4009100c01080c08a903c240d62599804210700000b0341070010070380150005040003c02080f1a91034211a2030640c000c0c40820007024800180051598004205541d000e00024602c1c0e03400302c400d480c0103851840700080c115046030801c61441c00641c004015903003190403d40810310440c0035a4012119940b003455070320044100b01c000f501040d12100b5130703407842c01f0003519034440e421001000c214417072105a2020501c8219001d680c921100101d05494100c062803c1000c81c0c46428074002c0c0c0d0300300030701d00000103600c03000c800c103e001541a004251a040210240c50030f0340e2103044202c3e00c84200340104031001100005100c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 956067751 1250 956066501 956066533
    0xb071106090d15140f01030311150a0b0d050102031815060907050702011b03020d110106080c0603060a0306021c060509131707020310020301090606050c100513140d08090a05 76
    0x3c1d0000f4003400000a01e15400fa0701004d807050142e03921211030110b00014400c06400c02d4010000204400081c0304810000d03203d20140312000742148001922107601d00f14903110130032214880d43d4071000a540303900d000c00340000150f4121610801920441541007140300682050754001c210140509034580e0300c425041d942984140000c0781001841d010320b4080b8208103042c0700d1603e21030f50280c0741e240140c0720000c1403001c0d42e0b018040144d24001d0204114000040d2411040f03000747e60290316951503c00207220400c0a6101500340c0b400000d40015406000d5542c1102e0169028100526a292001c0c021040e904850412046062414090220300700c0044828001c011085903407078022680c1c042800c003504212600c95968001c0010300180c00a4002c0c00080c20003450702e141400d000800c040d1f503c0b626000b03a01d5a40c0d1790b5102051032165900c4d0046142d40e0030a0300780c510300502d13461082d690101a48403000042850012410300140468050140383e040350042040749480d039034030303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 956069001 1250 956067751 956067773
    0x10090b0708040806040f030201050a1a090403090e010b0703020105010f05090a050415230105032a0609043308071406071e0b061503150301060f0b071106090d 69
    0x70707600024103010000d00c0c404108603c0c0d22a5102e41e42c41d400c259018580030f82500d43c050142d0107030900301210200d10089180e9880c0c061001168805000c2d1a40d00b003e40d08850585c0014050412600002c03c10501010007055801c0c8280c0c02007010781e0f03a501e00400c440c6550300440e5400031b000c82c0400d0303c40f040354120f10f4020b40500f22040000032903510391421902080420403981c841444c0510206c10188011801041c0c246c0140c02000c22020303118492400b450301d0b030100c4030041d10300e2001c1c644440d429a2004040038000b000008944001d02d010041030070400e490360700500341040d074070341c003029220802c49000c0d00081901900b07010350f90440c94103001c50103400c13480504c01080892068540048002600140c0000290084c10204a4482d004103014010b1903107044419100481204803076000c090328610210000c1c0d40000280500304990007000941030040f00440d812451100030300310603204501e05281e000e65542403085502480e00307500d92101000f620800410450a01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 956070251 1250 956069001 956069003
    0x1e07120f060e07090509010807030b070513030b2e08030a0f05071a09060a14072a03020102270319240b010e0f030714030307080309010903030b10090b07 67
    0x1000c6000d42d1242034003044110708841e0030001400f00b00d4100a0380c2002050503025101c41c0c8080c1440a0442c1c542c02c0e00110064800401c000002484941820480318428040e592041101e0b0141c208030f2040800341d00c6c0048661034020f008a000c00031200003010a804445d2800301640c144084080265042c451285403002481820809c003c0007822051003211101c440365004501414020303130180c9000002006208118a05070703c03030b410851500b041551110140c03070305000c00520380c0107507403100342c1420b810000541c4e4150180704058043d0054533031440200d074952034801c03412901c4200480c546d01c0042d01a000350482106041d42218095540ca0281c00d446406002c2064541103903282601e1032a0000d5a460000141e90390041c240064248202e03100680002c1c0040000d80341c184a20460a41604030400c10120346c5090094811b0b6903005010141c803440e000d802c0b42c0c064215000100d000030b02c0c0c1040120b05281680003142d42c45079035515050240c6c14a02c42804551142c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 956071501 1250 956070251 956070281
    0x260117010f050a0c0906180513020403060c09050f0316140a0b0c0f0c040501080c0409210908160303050f091809010209010e060429040503070e1e0712 66
    0x1040034441c1100b802070a00400c0421400a102890660002d0442c102c45e00220100084078542070005c1e003203846088107588003160141035420302199030b8402071140b644001c14040c10980c8031080241c020420400f20ba03003d44864007980d2000040503211041c207040040032030b012007800d0000700c0d2200000c10072280060b1107009102d4441810381070320b421444c41c020403680442d0024043d100d0a1009035141c18003903a0031720055040010064450510720040c5003e195181a4082400010300ea540201a01c8010340f0108600d000001041308409005145040c03059404031020003000040704000c50340c2582d581403d000f4001d031040f580360301c00c44205074054004410700e45840c50420405000d03d030610001a5507400860014004400900a140c4200e17428002040f00340201030544915103c07903030981c4910114010641a24012074100c0e40c0c05100314800494140c600b0a1120300908134100d003803c0641c1c1c204020080601c00f207030007100140c0c10003000c103a8180c031070b042600004072581e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 956072751 1250 956071501 956071511
    0x13031b020a0e070e0904080a0c02131107020117090307021e1302030f090706090501031805030313030810031a041401150f0f0f0b0c0a0c0b0a26011701 66
    0x5000224440c02070781041c0b80740a191814003807080d420282d01d00d01c104080e1242c80e4540350540390f00403603000c0c08d0101004d01c06140004000c540c2c2e209000049031101440800100102e10040d046a8002c000102c2c0072449e04000f036803824483c1c019040c800c0c44000b009518001d1158240103071410300e0110030b0149018114000d5650340d9845044030445406980140c030b0340781c0014005031192020346400442e401c030403800c4c840c0d01e500c03480100542e070302800d0114401c0d000d0f0a28000001e0280b0015006010200500882c01304240b01000c1e0746000c0c2e51a10b406485200c445003807804148401481d2202c800d6143c02800700d42c1d00143c0e84640103014240418a00c040000d09440400007000e001f104820411f20188480c202c658001e8000c40d404c124420342000740702c42801807075004039a0040d02c00700d0f041070407202c00c00c651401154071030045c4002ca680d4190345003442d08521010300c08100790f00e40000c100084886a29030000000385d1103141c0d07920300480e00c12150500541c0e298255292 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 956074001 1250 956072751 956072753
    0xc0d06150305060c09102f0a02041107030e09190b060d1b090801020703020c0609151c0b040203060306130206090409080706050a110703030c03090b0a090506060102030313031b 77
    0xe03c1114450300c1c948401c550380300401c00402c040c08030014020400c0c1701c6041190441400f050b0384840440000648000420160408052401c051a0307002135100e8201004400c00720444c5020b4400c440c880d40720309030036004000c200040c0c11f0048441000350002c3c0241c0000c5000203400003070b02504050642e1741b40c0392600c030611059030140c05109500c42403180319048907030390102c40d04000b0f00504000b1820031a4a590082d120401038842901c03a0340c01103440f240701e80c4d55036280144041d800c40040d503590300344224441c07007824801c0350000240c90080c002a0f581814001c072842400014050241d40d40c418005001340041c68200f03070f8201c1c00600514260792503603c50100301d01e000d0300301d40303480307a4140c58440c00356440288807408060138084c48116946d0003c0c180c1e20b402ccc0d8036050120351041e685804400030070081d00c2c050150240d410500c4001e10003641b0003c8524012020749002c0e03610280160707540c1c441900c600038031402a0b40d130200803a205460311020010402031402c00e01c03140d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 956075251 1250 956074001 956074003
    0xf011a060a0507110d06061211030d09050d05030f190206090102130501030c1101020412140703030c14100f020319140a150510030b030d0e0d0201050d0e120a110c0d06150305 76
    0x107a007180b841050908048c405026420303200300d40d030002c00c40090041003002132000b000c6003454481c1502604104800f1810460280b05689030114028512034440c09454034224020807503c00000150003581e0224101c2281030003200c95280c080064460b525152000440040007654606020441c2840140388070443c280010001130541400c96901c0500340d08040c02c140d00c40403a4012181c1c011035041002941005206441c550010101c4050030319880e001e9003094515170600640740d1521120121131042c913406503000d00c0340e4114001d00814a50010003c4603420f0001030007072900b0344001400e005441d08a12a50b00710721590b40e140e5903407000401c8039610100805070100c0e40310706140da280d04042028114144c080e01d087c0f094400c19601144071016800d82c00f0341041030000c0e10004414498025402c0300461108840141548030402441d540081842000003500d100c81c01c031403590002290041d403200141711001c80161940c4900040c144041002481a00a0000030100340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 956076501 1250 956075251 956075261
    0xc241506020c0f04051e04050a0515150409200607080d0c1b08040519051906080709080714030a02130515060301180c09080f011a060a0507110d06 64
    0x2120740041c00e120312410100400c0c3c00a443d442809030b4904401c0101c3c5e150880078030301030940741d185441c0d42601d850a00340d081c10300701000540740d44151070300c0d05191455501c2840c4244145100603003549101000c0009a03080400080d10036407024084d400d2915042d604002c564a00600803450300c003255032285400e4009850501d80a5660050b60020f143c10580d1512951041001d9241030890781d0f07a4808035004500415010b582ca06e1105140000b00f0800c0001034100200030080c0600d80401c1c1c0354401e0a64001c0100007400c8001007003110340152a42d43c180c442080c00b401072030381400c440e0003008115281c0c1c2903152044540100140e101c3c14014595052249070100b2946400b40400c0810100712000c2401035100b0001000715054032400d8001e901203940001c40c5501214008499412031504000b41a024400541c04280015480038041e841c01d54040d90170400c050080040171300501100601081d0204103502c0000c500300100c81015a0081061170b10b81c10944441c41111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 956077751 1250 956076501 956076509
    0x1802281206050f0106230d0f05010e07180602070512210c0106150c11030a051902120f0303010308211e092d0102070203011103040b070c2415 62
    0x2540e10424400070522001c0e8040c05417280d405c04d070825902c115002c004080740c403104824440c8002c120207104a2058104072202c1d4021001070080d56142c1c07440aa410b075040d43c074200803c0031003180300000004072640208407411038003d0010f140c0380c1030a1040b40070441080014a000d691008104540740700d130080c884140605405840358000c8501c00d00312000c541020000601403081c04c45c0c8280c3c0215080c1c1c0440e442894461031400b4070303000c030b0b14040b10b500004126000e1400c000c0e85002c03803270032a9645c7c18000c80e001074580308442d00392070303c4050b003100c42c81c0503800030001880461100c03401840b9413082d11801c03111002113003000300e11030a400d80d0784400b05087e29062214444210186582022880c4007520203454203403540304821080c000350305c802e81c52100f04400c8a01c401c1d07054410190b00034000f4420182e18a0400d01c0550041341c0807210b20040d031002c03441c1180f1403044030461a6000d055031002e802c1d546c10010410061002e041e071160f8483c040d609444c605014014010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 956079001 1250 956077751 956077763
    0xb0a0509032506030504211101050a27081602060d060602030915090a1503060806040f05070e0f040b0a0b19080d050a09050603100e0c03070318022812 66
    0x8202d03010422000c03040c007a8080b004040c1800e00340702c0400e0807402c41c02c01d004405248444040e081340e0003568a084001c0c008401075182c42c00b00b0801c2c0b15940c0240d0300c0fa600440082018024103071420111400289029004039014090300d284240c4c1d2581d48145079000a01090904804240c80d0741a143c041d0000c0006800102e112000ba0402812070b911307080c505a00b15090040032004a0301058852080d4558401c0200c50013010302d01a0340030788060103507082075403a140741c2404c04c2800840f0a48007292548160000000c0c0b05400d14941c60144c03044441045036a00c4070340b41c03e060f100c8040c154107060355540c07048002c0d41d603030188100075514260f4042c244140c6031103149424466011282824014204407218845502c07504100913501c04445450b2030380c503020707414034000c04a40c01003602a8402e40a201080c0c0d51600513520911050348d01b480702d80244a840003944075400002501b02e4910955445910108412000000321842c500c01c05d0f03d42c0c9405a0030a429507072400d9541d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 956080251 1250 956079001 956079043
    0x18020f01200a12030e21040f090911010509010804140102040b0301030b070e03120a050c0c090c04031401020a050d020c010b04020d150506070528050d090503060a05060603010b0a050903 81
    0x2c1100540003080200f010b4181001a1044100442d4888200510710a14203841082820030600000203840c09014484840d00403e5180c413030f0040103100b420802c4e605980c1c0500c0011103903105108640c4d100c181079407800500d481e03560303d1500701704018040841e07075500bc0c0030104070414079101440c001c40c021002c00c0c40c00d04103a4805030008100c090220b009810501050304410107100850380050303124039150f6a1194298180d500b060002c0300840e030302144480038807000805040c068401e0324010740c1804244100c10007464200e10494801c140450814007004074040641c0e030107040e083c007011001040c40c41080c0d002604036880b15803000d031042e0780c500f4642d0101d003c0381754202c0a400292180340c608003103500c1d26640c445521181c0c00009464205086104030b0350354400400c00e92000c21100b00c1601c0706800752214100d802103d00a00c00c410001d6508440c1d4040d16008100251006146908081001201d940020380c00b50034018104007041c49074408001e02c103c0702802c0c82c99660 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 956081501 1250 956080251 956080253
    0x30c152208030d0c1d090106110f010504030c0209070e010e1e0301050118060905092d060103030507060506030c1e0307030c08070510110d030b010e12060a0506030118020f01200a 78
    0x11103001d2121354602c0c01942c425411989850b80035946041d90882e00306900f0300070320b82c10000c0c5410310400d64ae410f99401c0000740010950041d41c55400240300b1550543c503036076081012a4018050204140010140b40350b400150405150700c0503085031001485586d608920042400e40b002a8840308221450b41e1145020502a00c1080f0240c41d09075410301850070941400390b580c20410168042c440c5000c0c000b410180303450456031050204d4039064a0302c640e034030300b005270964220500c1524090309105c0001d000345008104005111030088c080303400180994400100d030040c507611181c151103483c00100200382401c950030024142c100090001d18240420300100c032814402c180f05024040524090b45080410002d00320301c141d00c0c0c0040c0410302900125513000056202641003601020800c40550000c19000d01c82d2244001c148540d482c0c0c2d41c03d150807103182c0203600d4140c00341800d68100501e4845101400c1d58014540006114650030201128160041020781c40e50b01c8440d94174 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 956082751 1250 956081501 956081507
    0x105070f051504110d0b010b13080a030201050f0117192301020915070308011a0405060c0d02070f080a0303050901020d060f03031d090f13140c030c152208030d0c 71
    0x4007464095903081105c0b012a40c890340b100030b043c00b48040ba0500403412030306d943d9600384840001d001260883d140034600b420040d00034802076400d4101c6160500002c650210050b440c5200252028028003642ca80060a14000b0354140c0b030440385450b0800c40e90f682c510600c1c0b0f4814200001c0b4000595840b992420480020360302c00440288600601c00100031980001195044a101c3e008a40503110746000560092143e9003040c1d900407808508104010300020303d551518105e0b400310345030075840c1c1d040741410550358810300301694007592448001902c01c0d0006500714001c0000542058070f40e00128007501c0280d000001811003203c0704000741544102c1c0d00e540081600c0070300c0000c0074540d002c16a9010000c8c602454000c0800100701a40303012095015000d400080900207030310078211040d155143d0100701d070311a109680a02c0fa49103000140d581400c13900c09891841e04000543c00041e207140e00d103401d042404040d60000b103c64050000b8080c400c4455000601401460005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 956084001 1250 956082751 956082773
    0xf080d020120070201211515020604080d09051504120f0e0d060c0e120c180c09090603030d06060f0f050a09030b1f03050c0f18060105070f051504 64
    0x300314a44240c40e4100925500c2d001c90340e810382c0a10380400415014041002c03812900411000c120b0310307081d010a580c180b00c0c040d4030280d40f26801610710140c0d8416007203a6444d000e58000d02201402c02100041c0c034040e5010310306a034451000d8821140d48510050341c103a0701154141d130440c1c024413401e031800740d02c2031101341544103032b0428034220f40400c004900d1050101030000c002c140e44403241031125001d810540200e80740244145090045840320b6a16800c0e04210640100c1900c44e035a100500c0042d00c15100d10342e060a4107003007c541c0c0c2c0420119070400352815070075000c10000501070060902032a07010380003546460711100700c202d10017050f050194240c002040400c1c03011140c1c0c9030f808420030080340d170008241a26520740d50300403101490003003e80803480c030044000004000f000300c1c494184102c00c81d264100b003c00c08041c041c0c8000c4042080510300301100004d41e040d0301400260004902848260b070500a0960b5801e10303010524a4020303507200180100410080c0785001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 956085251 1250 956084001 956084021
    0x601180507090f06080c0c01020304051c0c030503040b15030f21040503100b040e0d031a040b03030d0e010f1d07080714010c0f0606030b100909030f03150f080d0201 72
    0x140ca2603e030002020301a0518001c101c10403030f102c030200b00301650403015a140601504021581ca003002d2a0956030b80301140781c260700c10014244a040202e001c1c0b4422000140c240d02e8030303031841e0303140c0e6a2050b28000082450141e4509103044070102d40f010084407000c5400c81000b800c00da0030488407445e120185001c43c80c4d102804004c180074036103001c40d00d5050003242c01c4002c01c0c100294400107002d03200105850381d140c0b2807400203c00e032541c5a04903406502a809030790322088000401e00007074490426120350554410020508038046a41c4507480d42c1d0309403000041e240780d44403004e209903046c250105d0300419000c0c291070056401445071000a0a60300c000705100340c81c000055070007010003902c3d20b0500120003107101c18084000c000b14600c5a00841c20010f0607200c0c50700c1903200030140c0302c02d40d1100fa0003101160b031400c18491200c0c1c194040c1c41e05a02c44441e038800310083c1c4074007580301074003200c2060002208048510300c00054105440904641041c2c040020300319841524 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 956086501 1250 956085251 956085257
    0x7170c07261b010509010e0613030614100e100308040905010518040b062b080a0810030c050402031e04050d0f030209240f1317010509070603020c0f0601180507 70
    0x1c0c04402d46107410701c0b401000341007030070081e03200c15440c2e00580d1a1521003480c2c0b600b0080000d5030814010595a814027540d10400c010802c000d01001721021050302144d034030f03402c3c50700c0941c2404100c08101700154010a449603100f01c0a40302d07518605190015401041c1082d103410050085240121804100c00307488411107080d0320f8a80c44510700340300c001e8803881c000d002c190f180041c03c010b0749410801c10030308500b07980d014201078540a004d43d8050b040b203100003001c40b0041602d40d142c401e81c10040340d0300308000882d035604103402c000083d80064242150440b07407810340c181c04403104c200144030b580514040c2c010001d103d00003500000c0451420410036104100c05496956400068102245c000e604022480b000344840300b010710036419404004a404114450118030030031101082e10f1508000710f5002181040b0f2500b607030020b40f60300c007154026900500c1041c0c4240c2c081c00f030044ca03000444108080d406516400d1080a0308141c0e1285040210400401c029002c2c21350011f9a0746 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 956087751 1250 956086501 956086513
    0x7030c0822142e0306031e120206010b04150306080a030c0605070c08121b0c0a020f010807051e09060a030f0506030303190b032a0306070905030307170c0726 69
    0x42c0345400043d921031109806083c1c00ca2400c01161003503000c01d02643c2c1c0721101c01200005080c134056a800c1410044982c6000c1041441e142803001c9050b9040340c7c00c3c6030502d0308040c10680d5003441a88403642000c1010781d51000040d0314801004203482190103a2511204100300d424000c0540e0310081c480401e02400000b5100021b00b103030212120843c11504c9411079845644000c110785031082c800005000e00400c140001000100e540c184080c82103442c1481f0700002c40c01500e2500d4200d03840c50228509200c0851025012850700780500c217001d801529080f40301e40058401d0300042d14000c00a0360702e241c0708501031840d01c286500803030214000d500b149050030a10410001544002050079211007002c1c00e640c40400414401d85440e0858080f603412111705c40010307111801400b8400d106100101b405180945044015640c016000c1e5241c40380a031201310421352100001c4030300c0c841c10003000b01848000c3c09540c000e401d0140e60b940300714030149a0009004100c040b2030040d60004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 956089001 1250 956087751 956087779
    0x30c0e0102070f030204020705030921060a110304060504020d0c0b040509010f150c0609080307030c0807031a1903050330010b0423040c020d11011107030c082214 71
    0x10960f00c01160741c121401748c1d0351542d07403a01604600420601d541c0000e070480e075a800c20740a1448032051402083d007190696075441d4941c10030350320f9500015251035010000b04003c503505810045d481030014043c1a1001520384c0ca545100079294030082d2042e8020030300b030256140100c0600d00404200d0a129285820030440c11850400b11480b402030041d05c01e1048100b01c265007082c1001070300410401e48074901290040c0c0a00a14620940094181030000b502c0314000c1c81501450b030b140f10548480210400c0900c104154020010603040480000000004030b0400051012403098070b4a08448401720b0080000c54181c28054500d4000400c0140310a002481c181c900300c2d82c0140c0703c4031404420070304c08450084040d5200313030031904001c0701502c080e80000b2030800341c3e19260f403103000040f81c0107541422100c002d444240a410b0810129012070720892100b1191030184000078030b041c03854001302199a00e03840d0142c0c40001e01603010070540b8104450403201d60b5060310105076240709 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 956090251 1250 956089001 956089019
    0x60c09040e030339040b07120c0b01030602160203010f06030b160806090601032a0806030a08180a082e18391e120312140106030c0e010207 61
    0x4413400d903081400061031030b415101102c1e00400b148111641021342d200d46905001a82d54401d03681030350250002d08070030014600c21101101c10540050304a051079095644d100c001c3e40c0a1500d2101c000b684c40c402c4005a038081c810b0070001ea450003800220580781d40f40114692400805500c68607030ba43c810301380e11580220005a0006007203c113503520360f517041c00590041c260611800703800311407190b5180ca0909169100001c150743c40e12501c6003596a441016030310344116600a0220400f07102070802d030400242c01103e000030041070802d8090300c488220f40707070881d220558110007140e607a69480720b204403014004500030280081c494200001c80007180040e0f6000001c204100c60f1100c0a203101240c80c2e4041c0020b820486900004988000004e0301401c9008070048101a20084080c04540120000c21140080e40d0a030607800d1a4600f07a070f851500c4080401041d84414051000c65400040c0d00d002c1c1106450000358054000c1c0c00821622625008038155444050244440b5038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 956091501 1250 956090251 956090281
    0xb041401050f2b0c0317030a05060a0b04060c0c1a071a040f11210c0112050108191e060914062a0f070309061b03090302040f0b03060c09040e0303 64
    0x420a0440c424680b43c914051007510102d910240902c09003007680344078841c0c1d0f0001140250100b2500303102a4a401040000c80354542c441c070880c1620802c001c205050040c001f035800240614030f6543d026644128403030008900e03180c2c0711800d4000054100401c500004c1549010030707a11350035600c910b0140c0d03c011018440f6000a0168801c499600020390f0b034041d510707020422100e07881035141101f080342c0b03a90340c00e031481018003290000e0b01c0d81c00c9075041c2e44143c41c12182d11070020024000300c0e8860b0880404c52240075100d5402d03001c880d90603481003000c010b64451060200082d44216424980a9080d5481c4018074941144003440b200502c4203d0300c0e8204c400501d003000b00c00d55828590300a034410090188031604000c11100141a08180720b80b04482040c0c60303641e12001001d144403060f0142800040108001400a0015003025071000c61250301050b40060782e8030500b07000a00d02103007101d100e00c4c5030701c0004044843d400c141c01040d0f00c03411000010760075803c1c100c10180f034440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 956092751 1250 956091501 956091559
    0xc01060515120403030b040219020718051603020a1214010e01050d0308240a0e180d090303390219030803060f010e060406020102030901061212030e010b041401050f 72
    0x46d151025000b2070b54079541110300c0e040c183c000c40e40140d6801003000c2c1d1070f0f82c10ba114103220040c3ca68003850300100702d80203c92190b102e410602d2018980c1d0101603000b50056402181040030a030090039110105103c1e400f54502000e00302e5580b0743c5094449020300358140c2046000d100c0890509000a400071015034100c1201641c10000382c0075204403c8903442c1e524001ca510131404030001811640f24002d450081c58072800501c06408105212075403036100104200018009584c1000403a20800d80304187c003031400214201d03ca2101003040310080c0000600103000c1e541096081145814030b0660b00a10782c89910402492944d16184000e00000b050980680f444580642c01c5a109110f60020b500c0014141603c854032584000d000350821644141590310301039010400041000d00075204590000003881082546042100a4403003c503500d41c00d0744d00c89420b856150b8841c003500050f0b18a030240d514441d0f14040c108500c546c200002a4025000188111180c40c2c100c49802054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 956094001 1250 956092751 956092757
    0xb0303090907121e0f09020319060204090c031b09060c0b190c02060f01120c03020d21050a1701030f020d0809040f06060315050310200c01060515120403 67
    0x15503490b5019100450301e1010045072902d4003050402120348540c006442021004003007200c510079000a01c201c1d025640080d5165102d408d50712100710b020326030404614400c600c00340c1000d42d110541c0301510120195540403079122a1200a4240d40420509100d140c6142500c2028586400a071000d2a607203005040441214006082c510349c1c040d811842d400c40d520100504402104001d480d00b4041c0d0399900c0c5400c150000058090602800c0480c0c0794024110300b0000c0c2c915802c20920300311084044a070031101d40f400120394540390250300c8609200b88ca03029a00c4440401c0100001d051070601b0400440410050020070807141c0e0504a43c0e505640101803c1c0060801e42114040c4801c81c2e948141032140724091210260007071803c5403007544092010050034010b01103008074900406030164001071050028184582156600104a445400341c28a801c80c0c1c614081d07000340c20000481c0e4442c40f04006a041107514900c0e00d83d2600e29480c248074244586201e4000060406010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 956095251 1250 956094001 956094019
    0x1504080405040f0e0a030c17030f0c1c09080a180f03080a1e17060405070215060a05090412080c07050a0204020708041e03050c0303090913030509090403030b130b030309 74
    0x840d503c96801203003040604801c560f8121480c0c40d008000721b828042c01c44000d88143c001c0d4122a6000c0143c1c0c2c011b5651900011940e030b40e000104029030803d09980488002e44401541c58851034840c001103c0e000f00c43c03d80c0e0b910131100c000380a0460b80206040150350540041140c43c2d0110012400e90364024481a603035000c07030b80200d54406001540d9241c6603038030440400200e4107e91000ca41000701c1c0d90711061765413900100b06c00c555080b039000d409600300c2c450800350070301c0c010b101607440440241035188494444021036841681200c003116061800c600d42c0001c150049051a07002200c1c4150600e031810580e6150b032a1400200001d01841d0007003902010417110b0010755020300740b260380080620499150006081e50f85110585440c02582d84080c4d507400c0c013004803429210054001985501c64400c43e50704042507500c107804100040c000701c005da40d9071b000d40501490195a012408094600401401d0701c0c403c420340b0080d80c03401200007030310380f008000d13288030300340484400003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 956096501 1250 956095251 956095271
    0x6010806070f080c090d1a0106030f060b031f080d020312160903120203040b0a021507031a130e0a050303070215010f17160803180a0f030b0703090501021308150408040504 75
    0x207542600c2c1c84005080984407030f5901247c0c024158a18100e0b889039805200c86e1740d05070f41e08811a00c1c10701403422a90000c00010b841c0c200414810701c103200100c100c10b14010b541f544158240704020f84248010f070400941d011184003401d8165402082100c0ca508140480660181c41000e040c03000a1501c441e0410504040d4001d100382c800402d001194030341c1c1d4243c1800020345520302003044000250004020400451007449006030540085e42a5603030307101640200001110600ca10000ca20f4450110048240040c4505a50148508003c0d80c890921180c081e05107003180700018085211074004100a40c50000c06800300c0301868400460303001c605006ca400c05c690049800400400c9a000044180c0004018002e009526000e500d40c00c03401010060300809605c107e01034050744e00e600b030000c2010903801d01d0b04407070f40b400c0000300b90a0681e10b03242a6040581c030030107116100c034010012558180f14003900080d50458201042c40c1654411010340124058180600e5960711014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 956097751 1250 956096501 956096509
    0x509010b27160201060e13140c0f060c10060303090806012702220305070801060501020a0c03032109050309040501051f110c1306092d05060f1206010806070f080c09 72
    0x1030050711450b02605070a187c80551000c16000140c4120b5800034805c3c64402080310104c4d40c0b41da0300d00001c2c0071040782c5190004100e03058000e000d0300c281d0750042a60b9411b152600b88a194000c500c40c0e16400203192800c4103d03400c1040580c070140b001001d400f91241105043c00707104003041030040c0d0050310340390210b08648100c0e82c5640000b9999007403039404014414002b03038004c00ca6482000030300c5a1a100d030012170322190084802032200500034010710009005042c1d074070342404541a07003e0a800485540d005454006c001941c00e5007000880079103504050280e0b501409044d111502d000100c8200302c000100984201c0e42002507a060714480000c09001107420660002e11050340403804030041c01c0284124880e40e20030328603152204030060003049000c0c980318080c42001e068100d1132100307030740a0300008152540c4030f0168030f6100d00c982d81f42a003003d85040c106008114030743c1009070b01e078a001805080d40301844000030306850380e076921100444d8001d5801d44a2500e84c0d003504085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 956099001 1250 956097751 956097761
    0x6030112260c0105060a091416020c09160f050f1e040512010501050405011401020a11011412040c09021611060c0a0f0b0a060e070e010903060509010b27160201 70
    0x342516000802e000611415003200b030240030b003200c5200720310f550f4803d030004403880000040e4011402c3c40001e2080040e80601c0050f03000c5500595540c6040c0c0000519203441c11a82c2407070000c1d103000307062615503009801090910150500e01d241400000c0d034000c0754015850011556a07907a20070190100040d4180e4008100c0501b8800b103810300d41510794017070f01e400d01030b880c001c1d403506c8000994880c0350403141c00c200c2010f030050013100c903660301c9644c2c412a24404940c1441170303020800c2c1e40000d80100500c1285001c0b8004025418030307103410800001d00e6445618514010312041400303a030f4110807404e90541c440085281c2c0e1100e00040b610900442c0d41c414900e02410b03040e00d051100d824000c05280d44111034039100d03075458240480888015020303020004141c540050240c2d07002c2c8540c0409600305051070031140b50b0741e55400c029990121007444035651602c58260340c1c3c1c1022645a00520700d40310f2000fa048282c0044041c1e40400203142d0345280e52500c4500313070710a00039840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 956100251 1250 956099001 956099063
    0x30903021309050c030109080f0c0c0a03060603061811060a0c0602030103290717070e0405090c032a0103050618151813031809020313030e06030112 65
    0x81c080c1c0108040e050318005001804040c0c41900a042c40c4403000c0c0b80620aa460a5520030803044c1052002005d03002c0c40d40048485d400c4c40c1c890400c0350017441d80d032104104000d510030640841e08034158942038040e42c00250000303c0e040102090000000c07081c0007410004581500e5181d01c0c1c240d400d808680d801b509410207064a4400000070042c0030102c403614040c01d0038105000304140c508003403031015030b00440d500000244007080159604040418264002584d850064403840e04e201c0050220780041e10f110101c8c0e84200000d003582e040611104c0c500b110030398565656200029130002851081030040783c1003580e42c50000c0d41e19034072451601e8045524200c0c0c10414500003508510700d0942c0030600e032080c80410f10602c0140380f48140c1e40e00c03c022218680c5030401da2554140d5519038280c0038021480c1d0f40e02d9001ca0b00101c1440a94898803000305c42c102c031025141806000494099001c070300a1108000501c61f6502c080d09028000f6485600c51503007540d512070b60300c0050000c2034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 956101501 1250 956100251 956100259
    0xc0603090307050c150d050a27030305130803010e0a0905120d1413031d2709061e060102012a0305090c010e0105070203071d0702010c03200703090302 66
    0x105010046400102a02e0b071079215038111421100c0d10300030041c1c2000009414954250100100d440f4448250413260304411060b20109040d0031081484c00310048034a9a04c411070410140402455418091240c00a030060050341082c103064a50f100c0c02e220500075400c259603040081441e440282e400301c41902d07000415125989096092410a944003516a6030403070b050000c503c4c654992078007402d00594052070178030714100300c0d40c1e02a514850038420704c101450910110a04903162294441103054403500c5100824800d40c03901d402080000c0d118402d2648450204920101d40103500e0304142e24820f182d6a580c1c2e034030710040380508054039031414000316408201c84156000c40348071400160685041c0401d80e200d2041c2940c805424035035500080365003020001a50144006001603800a001d88006644500711a10034880b89c541058441000138200300080e6428030a1500d5441e041c0740a05c0010002220782c0e0341200306070100340e500303440010304508041c000d00304136000350380c090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 956102751 1250 956101501 956101507
    0x60501200f030301060503150303090a0909020a050913020a0b070203060105280b0a0206150310090206040902040f1d0601080c161a0106111212040f0f0b151e01050a020c06 75
    0x5c10000d10301d4100384d07904490700d0b02030001a15203207070210568443c046c0203000c1c501243e1821a0b240c020340710001007130780c02203003001e03000c50740352a814441031042c0010413511100c10034900c14450030801d03941c4401c400c01c009008460042e500419000c0c1107800480c0c4261840d2600c2c40c40c1240c000b000b03031074100d0f0080380c007100048c0c0d80c54920181c0b0b407020301070f02581c07011740c1ca0b480303851100b502800209604d50489500103404168a61000000a00191001d03092503102c540c20009c903807268100101c9004255010440a000c10118100c10350801000f1a060f08101001901480010300b2801c0c5001010a844030b0114494441c0b0721616080301d400d84e07024004026010340c0000c2809910006540030154400079800002c055020100c80001d075490284101320054068002520498090b180346091002244000103207441540c042c102500082c140a82c200600d556000c030494000d24840040da04040160212440103240038242142c1d10b07070000307200301e0400034009000d0750b000b0404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 956104001 1250 956102751 956102759
    0x150c020c3105190f23040b0a0c02030c161505040f0e190212091e060f09011b0203032202010c0b0703020c0a08071b12060b010c12110709060501200f030301 68
    0x5500710416005c0c03007400b006990100303510010b02c0d100f800c0701c000d030400385820041070013105181e00030361000d00c903031055030f0429006c80c000b43e081c50b0036088501d851402843c2c00740040394080341c245155250742d0911920346894224124158103251003084200c03203840b0001030b554203040304c0300300d003e21002e0021941c2c0c131110124aa152401922030311101e20405189603000c800001d820342c90b4404800050886a41e9050019040c000042209015549442c2005200c01540001c0b980c3c1c500c5a4010310b40b6881d000c0740c2a03a850845a5440d048086e000c0000342c050f03600460300303c0c074182c0c010300480c1043d82d410034103a0103071084c2c0005403094030031312270710405015110340907025403803092a942c400038000e999404800b0b00030b0b004100503c0b001800000004505600244071f5413018140484c850480d41c480314400d80d03002100b04042a200041a48052070138030668002d020410810082030703041000081004204030340851a5a030202c40042898808004801132407100358200c95603580c50b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 956105251 1250 956104001 956104031
    0x4020f060d020705060a0e0a140a080f0415090e04030c0c080f010605120303040c260717150c090f0613060323040519150c020c310519 59
    0x3d50701c1907031903001d0b640c04200c0e15100390051141040c41a8010038070025079860725501c5c0c00d6030490002c100c0c480e0080080000d035501c006041c00706804540c1980f2980791849a2038240a0300091008000094100380711070421248181d4000d0780510380380920030795a14002c0703020340c025040285c061040060403201140150400403e40f18245c80720080d07280040545a500c1c0020341d030040941c2d03200c8205103c42030900c006064513001c8540b443c260841c04109041c200303407282c1c010400400302c606611480d03030f008024401070009401c2923860f15160892901d42107026060005129032040c1c05403c1003503a42500361070031003100c0002c2a400300e81da82005001041c0303600104101101412607951200040032100e032155801c000600b1a004c00076510902241150100f2a000804c0240c5146140b90034402d000c807510203500100b421080307120801241c1c407400460304a10381c042294079441405900c060054509150001003919201c1ca0034a400e1700c03070301440c0001602d180141540000c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 956106501 1250 956105251 956105257
    0xe041505030111041a1c09032d080f060d020603010f090e2404141c030516121802090a0906060504090308240a0b04031202010203060a0e04020f060d02 66
    0x1400728001c20107949030a42104807401103104101010f2003200c4010030248148006140100700d80da500740804003054604011600300d0341d0141c0000700c0400740348201c030709001503110204a4100d01c8807694651035030010000c503402030400408022480220301c1a44604c0102e03032289900500b45074580da15151200040c850b00d00ca144106030820201002952000c2005420020401112920450880c2c010945401c000c0c1080b01e1404a410848070029410300502c405820310b006001640c0c1c070741d5140142659005802d1403001c101010385445000c0c0c01110107014000c20a802040c203c4141c885040b001d810100061f4001d40340302c0402245000a6210407156441064200180c03501c076030a200484070005c2004000c00c41060110764401a030401c0c0540080c2850700203031030f14003180b000c510140060351107980c0b41540850180708003c4403010501042e129131008500354503083c000a020b00009100c1c4021500070f0034082415901c5282d40c24808400207800036640322000401302000398 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 956107751 1250 956106501 956106509
    0x3090302120f131e120f0c08010c0f1d0d0f05011506141201030828200a03140a051e090f092701061e0509180304090b010e0415 56
    0x8610084007140c1320307503c3c81c1a903044400c00c81c4141002c42c10f00d1031030010040c1e03d85080d0f0712240d5804140b00000c805500d00070140c000c110000c20350034550b2401816410446818a00340b005000c003216260442407402c44104200f200c042c10300520302c0c108166003588000001c0c01c19400c11004001c0c02e541482d018003150556030350400d190140b81040f464601400500a4a14001c4001000403840780700107000107541020884d42d0098541e20150160005001000c0c0800d42111101518030400c0020385003c680750b4002c3d15500703113242d90091415801150344c01000c5804500e05c04d4440c400c0701500c0c480700f4402c01d0700310881040c00c904032464015100c514072441035500c00303541504000070900c0c0110504000407800101001e856005101c0c01203491203907651700d600000c5c2944920180c0f00700b040c0d050b048180744d14105001d000c1030f89401440700e0305030a00d100e0218500f040c000216021940c0c01100003c6900480004881c81c0c0808280076a0090070300702c01c6201070783e60f10251001c80d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 956109001 1250 956107751 956107777
    0x307020607080a0c0503070804142d06100501080c0c120d06080c010c06020c0129030105091b09060a1e0e060a0302030a02090717090f121903090302120f 67
    0x15500d007800030040d034540b6130b05800028001d1002c02d01250258501c0c5402501c500806000c18030b520840514042c11450f9001c0b4000003410340c0000701e070061024034449203403032028006601c2c04607120203141c40d2611070a41040030a0300022203a15046040d2040007507100c0541300201514208009a900003051b400182031408800058011002998101e11001a101c4510707422850300c17014001d421000c0d000d5810354a40300e03001d6000d03070030604219a2001540c00c002506052500b41400c40e64001d0403164030758004645000b0f2810050b0715883c2d506000c4a0424035940d03010003003108050642e1115030414140340440d903c0140d081c0300a030a840b0030115500040e0340314410840606403d2001a40641102000e04094203100802d00da0103041030505c3c5c2403403040c480041c010003004a40100303168101c0b0103800010407040c462824100c0390010a01c2c10600c5ca0038060304855045410700c401c0c55070354012402054001c0c09800d0580c461803582540b210b40008034412190702c040700030448 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 956110251 1250 956109001 956109017
    0x3040305030a0c0804051b040f062c09061909080c060702100b0a0513200706150b030f100b0f070b0907030b2208040b070b070905061e0c030307020607 66
    0x26844c41184014071554100c0010b01c032012070010712544070034031040307025001034454940b4103100c603890007180010181141c010440d4280f00740b0309110f581c0f42580040038203188400b8080704a800080c0703107400c43c0881803045038010081007903000800c08528001d11802000c500c0941e890404100d46208060035001e1740e0240164201080444201080042d8409141c0f41c080c000750810344103a404054a112001517090808040c0b903064019900d490041d82500140007403c20000307001d114170310800407a047c0380c81400d0540012140c00000c00d20b00580741085c0005541716000c0000341d0040c00303904d20742c5a94100020210b52180d11001007550541d40c2c0701e000c181500800101103080701e1700244d60b00415124000c40354445100da11404503020a140802c60124503000d000304028005c2064007551500b086c50500341030134000f4030003000d0000201041003280c030b58100720313a1010b0b15850100030403a80c1e000c031f0303200358007840000d44090712003c02045041d50300000c0c0c407401102d1940b62002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 956111501 1250 956110251 956110271
    0x903010c120b1014180d0b0403090902031b071509150b06032509031506150c02030706030b06040f03080a08090a0818011103130509060f0108040807140303040305030a 73
    0x40714810b15003000a0000c04d1441300f00716080000d01403c03c0507003d0380d051802d501c4000307019801c002c0f030301380c802c910f992091004042c3c12122440042c81074000540c190315040e88485007554105a01e102c4a02d4000f40c1e4004001e40d0800d8041c1e51020070f64200048041410260302c0c040144054245075460040c0b145c245281100035a8450382951a1a00b141c801103a0b0808503039050101200034030421140c0407001852007845501102400140026018584205660201c1000302c0c0c2c8828400907050910141c3c4000c500c5409a440e1401c011030410004c40c00b040c801c1c440d9070f01058140110a00210800404d140146900f110301d40d1844000d4840302d22054a4841040e4001d00c0542c041014202c00301c04030800c0a00348105041000c1407a10f0b05800c141158040b04215030201040341041c00540b40c4415110741104c0c040ea82d080f0f940c00c50100190642c00081c0000e4900d090201c3e411041048811059001c3e62900d01540d80f40d040514010701342d9001603440700d21032814180110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 956112751 1250 956111501 956111509
    0x9060306460507090f14040e03040803030f09010b01031802040c050f0a030603060e0610030b04030c0609060207050f1906052d0412080c16050a0c150e06040f17030903010c120b 77
    0x641654002190031841c102e20104020007419100c8c141c1c0500d02041c400001c0310340d070070300c081c5124004852082100c1c1c54044ea030142140ca11a001d2414140b030600c0d41e80d00205449090003a40d68140e80003d002800c004040d205401000d201d2000300500080c0e403146180e1541026088030300c100403d00c0395000e80c140352501c0354411941d51104d40311880d07013080800c0280020940141c0030341050380d03504405d901c85009513000c15200b81ca480da0005000c0c020418100300180c900c00800c0060f20f8846412041126276840c8076601506954540700031a0118105911400c80098038800107503030380034201034500038040101c800361002401390300b40b869024090010b1f9482129180700c02850982c203150390020f0030a801d00e00740c40307500c204e07a0050006143c125140018081c1c03000c0400054400400003880c0c20007986c0054001c403400d000411400c0c00c5c074841701040d21000c510000000700c41031100385c0b56014152282da4150300300410300d100c240c0c01000c41c881c50030f0b0602d028884d00750f0504c140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 956114001 1250 956112751 956112779
    0x30c121b081207030302090a0b03012105100e070510021f06030807021219111014070b0c120a020a0f03021c0c180f050906030646050709 60
    0x91540e07001400503108003240b5100a0400c0ca2190500504040c50303100451500d10030b50704010848080040148881a08a0000100f14a800380d0110b03c080980ea140c5495203000720b0358040700785d1a40308a103001c00040c801d140c00741c070740904079403c0080c043c64025680c000300366420850300740c0e465000c41010070030301910041d030381c219105510341040b6909010361200718051009090180c40c0544158541484400c2803440c000c40b0f85020000240e410090310b0500407000074280701c03400c16031400d40c0c1c2462041d07030f908540140319414195030b0303403021f40c0841c4160480306008001c2c01c010400040e6407a809440310a1240d511100c3e80541130005608038462a41c07040801100049500748400e150340220070041002d18103140c40a00011414000356101c2e00185101380c03c15a00740607600b0a502070302d40c000000c600070542400d0811a030030324140c01d1800600032102c0c01a070195529000900c41c2c090107003000807102e000d460100044001c2000390b5001c03002401011000132680302c8000c43c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 956115107 1106 956114001 956114009
    0x7051b010504030c090c02011e0510050901050108150303040b0f0c01180b0109092904031202130501030906110715060b0a0806040213030c121b 63
    0x145006524115150421009000c1000841d0319440305208540e200c6100062060407100701302d01408510441043c0c801c44a0540070025007a0751049200d85414140400c1c0180c032002002800202031045500103000e10006c90700c2100c00d0010310700505001000c03a0b01e0a9500c2442c0f8219400c0a0b008184154010407800b0128400303000308030031000e040300b19198044095640708078428041c010f01501c0c9503a02189000c010454241c10307084030051003010582040b07809540e43c00202110308600040058010090500050080d901f0f01e08001c2c1c0254007141c20003004400421709102c0603182c0d5901c40b104404c030b80f04000006d02190340654401420005c4004500b815180c041e804034124003008c21140d41d4845d40081c0240d0000d004070340260341c4107203100c0c902a1480103a00040c2000c1c44800d030004a0203000c0024520790761040c03140361a400944000004801d1103071207 = true := by decide +kernel

theorem cover : BRFrame.Cov 955935251 956115107 := by
  have h0 := BRFrame.cov_init 955935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 955935251 ≤ n) (h2 : n < 956115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
