-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:31:38.646172+00:00
-- url     : https://prove2.me/submissions/1f5c43e2-acf4-4759-b9d3-1bbe0cff4bd7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 7553964 ≤ n < 7733820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 7555214 1250 7553964 7553971
    0x1030b0a0e100605030705040902130504020a030f05010c0206010906120209040804080106091a0603060a09090614090a0c060203040503030a32070b0604060302060d020c0a050d110c040501030b070f0c0803 89
    0x342c00040141c03030401418140310303a550100c0c4c4554605905103000d40c03916a400010f140444500082e5030340e441c8001007140c4281e0300013400c0b014a0030515402c01905510000300142260215015aa07030341041c101a02d0450045080d1120381c0c050080c0142086418150020310030640282008d481d40107107800c64049a004000081c0c5030507080d400020b001ca1481d2520760151230b1140745180002c04110141e00714865040681d540d00790500602604cc0d10001214a109041c90348500301117008544d50340d90b01405981c50b50b034048000840318000001c43e011203c024020303505103814540241e0ba4480b0800c020300d0b800101412142c8400c4030502400382181c490280551107001c01d00303000400400c01000c0d02d01039494200c00780301680e113400550341144090800965941100f0841c00e080000308540241144101d40200380341030340090404007000d40000031a200343c91900100710070380310300f031002820306401d0101081ca2913205110343c1c02d007810581045046141c80e81c0c0d40d60196402207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 7556464 1250 7555214 7555243
    0x90506070c060509010c0c020d050709020a0509040f0e10020a090305070b040611010513080a02030702120106050f030a02090a0905070e0106120f0b0a061817010e0d0906020601030b0a0e 81
    0x500c0c9200030042d03948180c98108101e0402007203014a180405800310300d0301f0001a218440481d00582001801c001003000f46c06424000d5444501c000400761164211540e5070f4460b03410154030100100441c4211990404413038028007200c250790888100940c0800d118504100c051000400420f80400c2400c0c010300484ea00b840d41c4515140c00203100b810b0b03c40c2c3c40101d40e4104014800035017440051030a1040e0041030607a981d980595059255119040000713402880408a084003050194080e20441e24113458080f0014081802c0640b03404a40c00001d5000310482c022400b019070795401010701a2291003120302c000e032100000c8040031000d0b8448030018101d0128840340031198016101620100d00091011900001c002420f804d6580585401c1002000901c0c4a641c03000d80b40d0402441c0c3c4800c217a080d0303029101c00390b01915152441919131b220310320031142401d1003040031008071030095001d08130716400d59864480440000d011010b9503501d0300741782101600309010b000d902050a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 7557714 1250 7556464 7556477
    0x7060501030f050610120b0717090c03070803040302010507140f1b03011401060c060507050f070b09010605010801050a060503070302090a081f050702030f1b010504050a03030501050901060903110409050607 90
    0x25894010301d40300c030003403982680c82c16005c01002070604003540440c0d0541d00c5114803149513a840003c0301c0f20012020242c41e03043c070710828001007041c0414013400764030040d01a02d0b1000d17110340819540e4400c2d0302c4024001103007080480c002c1141032104040d12701d080c0b020754913071084510301c00345809440c08010a01940c100c00c400301c180f40034400c90103507000d000140c0c1059031401c44050150040441d014100580722800900054415822540e00946419078a42c40d00d2840c24208008030044428900350b40ca481c001180540c02180c0007412602c0042c1401221800c000048800340c101030407400a05d5000d00c003515031543c4201c0d04002410039080100100c8031400001c55038011300b40c104180c5d041c039003828080c820394044101c40b1403030601c0e44090790701e00c0103025943c4c48400010310303411b5a5203044140420040c02003455803180b8025a0144a241d03200c1080104103030b028400c0c1001310748a080104000344080548540791500203000040e4016030707490f681c4c20868121680f0000403407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 7558964 1250 7557714 7557743
    0xb03060705030a0605031507030e0f1606120203010b161716060b0103110414060c0d0801051201020405060a0c080702100e040c03021201031704030501020c010219080402010c0201080603030706050103 87
    0x2c0f24402c040c010401180188440f01a800241c2120980903046608040d101c0300810000a8100403040312401954201c03203041501d1902d09110302c540b0300818002070348844201420035458020b6030705a40e0f0230040589080c00106801c540c01d02c081c1012a070300d40c00a2a04024921190003600d40f038a0794803a055070104007032900302c003155202c40013907050515000c07520b181910313442c05507825110740604205480c0b04240004455004402212985210700041a02c22031b41c040100340c100caa00703403109020040682ca0807820703401280241d0b6000101800400300740742c0304001a40700b0354020a4954030308065a0049842c03502298006c1c1c0c00308217505244040c1e0305042c410800041c0072841d04600b8030b003d44202e0f0340c0442d01840b0140c05042052806901440e0300d008450042d640080215546c5084021150103504040045d4800c079016105516010b8022841b440c890b0307905949801e01010250700641d80d079140a4080e030b8040c40244101e02c0000c0d094400c080c003031400b400400243c00d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 7560214 1250 7558964 7558981
    0xf0925060809010c1d01171003050705010207060503040b0c0c0d0305010f0b040b0306040e010b0603010602070302030c04050f1902160303060e0903070503030703020a0c02090c0307020105070e01120f0b0306070503 93
    0xc0000d0314250683c0c0c5020800700800b940107002c4207044001c08400300320342c5515030041f035004c00c0d500300b0240054050020301107240c0301c4d003051408891103103040c0c907240b80d5103600590712005d0300c2c40741c03d000c100d0400000e0001201c0c0c0b856254030461341401c050a040709085014509911072484d000442d0703949005000c2c9000300040d4800030254803400c10700d094280741d03200b881408041e003602c0c0650b4403840c480c0c850000a4000c02840ca10140460383c99681d034202c02940c41d12076200580c064004c00d0b2021610b806d01d80107945c4581486040d1028030344840b0100342c010480c0740c0040340000c2e4244011500e001e40300c0c01d0071182c2d6010766408564141440b0112100900c054000c0003958010030100340010000700031707a6800495400c005032205000d000c10760721246581c2e0025404040784041021880d20035001e14060042c560003000255180036041c1e40c11b030b40c3d400c1054003040e00d0070082a800c3c4499088540340014518000c55158000801301c1d141807010382d11000420008403c001115 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7561464 1250 7560214 7560227
    0x1e1203071106010512030406030e010609140109140c07030f110f010c02160302010903030f090312030504030f020601050a0b0a030e01020f03010815010608010b030406020c0a05030306030d0c08030f092506 89
    0x603c4d04483c2c06400e00c400e01109503403842503200e58014942c03030f80c5496401c00020b500540c0200700094051011118150a40c0300c80030090083c4556645850410b504525170103054510a1b003007501e138203261101a071000d584c401030b46001d090811142010203014510306011000d258258040082144840000041e050628241d10185454040303101000542e038400c52010403290107040c0102a00c120120496041940340c0000e040c203a03520000844090b8142d00c814411400b03580e9038200d04204000c00c0740c44447c28428264018179820080c0720000001000b0401d10303245040004d4440300710703200d2a00f0380e00032403050381d01c4100c040300400000da010300802409011400d083c100940c1400310190140c00103000b220800440400050f08001d4264111030301662000b04403140d00c034440c64600d5480e0300c111101c901034022140c007143c0144c0034070410700030b550348002000e0851741c0f400d42101c1c200100504005a910500f58400000e4588004101195082c0c4e4140510b00b410a00081c140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 7562714 1250 7561464 7561469
    0x10c030e0d0804050a0308250512010b07050606010809030d06090504020a0803040308030c030a060b0d06030204060b0c060a0e0c1801030203011a031009021315050405181e120307110601 81
    0x51200b100104030010b02c0100d030310314010798103050946440e101c00c03400384084030618024000719850f000d000c410207608080942620140400c10b80070340c2e078036840c00d51014040e0080041036070b409600800d00715809070b44526070145a10089904042d05d100c8004240c400583c480c13082165641c0510055080842480c40542254802580382610f59507881d6101d11005049143e04800480482c00701300b0705801984c0104140e00f074898540c061181000b006004070722003284a180b40c59400076000c5440b030292000d408074031000c0d1055540ba03501550160500002c030614500906041d449140e880420504100300c00101000c5558114418076084545d200202000c22501a840400540d400546803025000b6110045520066840402e2005d4076801e450403e15080490030280c1c0d5401407103040071104200d4051146449440c0181448444003080005c3c1f50070000c1c080005400181d1440c40c400c40080855207a42e00321110234496030030a561040001d01c0c0d51803114048039080241902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 7563964 1250 7562714 7562717
    0x3010902030d03050702150103060510080115050f06090306010b030405010e0a0b06011b0501020f0915030402090103020613031509020f10050d15080601061e0201020a0504050402090301020903010c030e0d 89
    0x101051a00026a0381c002c1c0c0c00382c107040644400018649610034414100c010b4401c44040859507100c5c90000301815080b140204460142d00c40010b001c94140076a20780c0c07071040d4003034041d8917007000305104180f24900e08081d00514200f00303c000c0b1f43c80c1048881d00912808000507100e0403d49080e5081d607280248440e0740790700100c1c404001c01c1c000d00d411074000502b420520040f94400300e0441402900c0c01028040e0b500c04201803071152000c0000b000802801c43d031104c8007000c000038002083c04107580182d04089a01d0044c40107040c00fa0081561540c0c82c40024074243c2c1e2070351059450a80c2058001c1280e440348418003c50900c85800a0b040c0344c212500e40c1c0c03458a0000c0101345003c1c00010440944d15030760303a12000588c010351803010f4542981603032020b40e1600e501401d0342007182e042026031114401449006031040c800e80d8417001d116625507207007500d0441080081d40040d8000d5038155401c0048503015542481000300c0305d815a1404606405020720040c00c010117000e0020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 7565214 1250 7563964 7563971
    0x10f141638010e060d050a050105090c18150a030b07030204140f0d0201050a1101050408040f0e091906060b03070e040c0903050316062301091107020f10031113050a050301 75
    0x50308115901d101d1815a4507800d0768290940e0340c400000c10f002407244001c0c08900854901d6130074804103401c00ba20850900d030445800c058210b0074007020312540700c0c82d145c0c6880180085100128002c04501e0f080000500d456401074807034a515810540a50322007011030b5000404003c010700c04290704001040803911002c13520200000b05a100320094002410450000703060076886d806a0340c10101080d11200030402d81c0340510b040000783d0702502400b11141c0140c400022080a40583d00d4031400b507101c040c0c0712915643c58254a4850504811a00c0980301e100200c2d0310389030305c0e0140d4442c6c2c502c1c0d500d020040300600d0a210403a0081d02440007000009a0140045030b0300004036010700521b1458464030088a0425034001c0069000c0190307510392040629612a030aa0700c401d050302c921140401030b0a0b114010340d4041d1113520740083d0000e1000c81c1c51100c1d0710340810f0b00100d5a04600f008111403120141c6c200650703000e0f035641c20710031501300d80034403c90400022420142400f5030080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 7566464 1250 7565214 7565303
    0x120d0f14030406050403050d0603030305190e070b0304051e01091103060108070b18040203070203030f061008040f030e040204090c0801080a0305070210020c04090804030209070c02010f1416 83
    0x8000d24030005001620803074646003c5000c1500c86d0080f00e40d0310304141010041c00780c40c2d00e8028050181600c1c40c6d520861007503500c500f00106480743d071502c0d1400000805102d440c0c50090b02d0940c000410640d068000d48000050710803010750413004104111000140296242c94011b614003000c1c18114001d81c0987c0041c4500e403070000d0154141c4008403422600c44400400c8844103800007844190414008002c4c05400c503000800303580071b0000001041d21642d01c0743d007404008020301586400180b84107003c100441d102d1020000c449000c1e240c800d54000303090380418166072040d0300c0785585565440520509d03a40c01640c15001d41442d10190408440076100240320740a5004064424848401c110303080034000c03c00342446000160041c0324000c240d04182100d604544007d9000c0d17101007000411152080284019659050b1500c070590084440708071040100b41d6038048501008204070703561070540400d040c20940c820b6482100d48141c080240750406014201890102040c0c0d885 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 7567714 1250 7566464 7566497
    0x5040b042a17010b04060803031b031603050606070c0b090a0803030105090606091201050f01090e010b090a0b03010603020d05011b08010308121302091005011116090b0a05120d0f 78
    0x31041207640b0540c00d441c164480900c000c0c01481000c4810390310600c0c089000440310404800b862080d00002d400f13400c841451030300e0704c2d240c1c80200c410002048d45680309415540c06648000c0c0c20001c0076203c0c5081800c40d0796540e030511042d810501d190440481d20100519010002c203014241c0f810146085500d4040801c1d052100a001d0f144030300d0000c118101c0b1500c0f6483c0e110a40000800240554100000c1303241c0211428084c4400071030a00d07003b24441c075014003c21141398000b424000c40c9a6660500030001d00c0c0d0050225415520f80a00001503030b03034881203aa80c2c502440001035004091100550f18804408000d0284958040101b02003104002a00d00880202c0302c09881c03036440d00c2c80510030612030307034000b5449104038061020000044400704141c5800b0388440c1c3d80000041d1095130364a40034900d10b8082071501c0c0090266100740c0c0c1140e04401e034041c0c0302480c01c544401c001420807141c0c910070400396129691520b0002e034800d4a0005640060506007016084000f4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 7568964 1250 7567714 7567793
    0x703030c02060d02130b0414040c050307030b0a12060209090a05060a0603020c01020421020a0504060f050d150219030c08240307030203010204090f1d07030b0408070605040b04 77
    0x6845410003040760768400e140703a0100c417082404402c82e28600c644507a40b403c95900f00e4011507901d8418115803102c0c60030a4401c5203100905a00c4007815903648100c200c001d403000c603896036001301510740f0000c1c82c41010344400b03550034400e45015032038403050424820030310402441404001e04201c140951900e48422607802e44100d03240143e42d4842e1003a065000e48665441000f07000e0070100e800401c0d4201c400c8102c0400c3c0308480d4035400540d50000c10050380d411b03024298440b05104002c000c2c070301e440611400c000303105071226000c0520021007141260004114495400300362005140e8250b450f12038154a0500c0e8109071105042c48005900c49598109000c0d9940c0a05203010241369002c00449000b194002c1c025580c80b501d07100414080c0c00e40016840805044c01080b0445d510f41c02a2144004c0c0b5039402032240327600d140c0b0750441d040400740050f1071003002041540c000c1041c0340540d80c4524090a004101030510f841e0110300d403040020b085500d103094030940d00f4403240c11003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 7570214 1250 7568964 7568987
    0x9090102030115050309150f04050d02010e070501050904140a0203040c0603060303020309040218090405030d06050901081b06070b01030b0402090105030102090a0312020f07030501050a050c0a050301030305070c0801050403030509060702070303 106
    0x500a6206d40d1404656860618120500d001209541040017642c1d106940e150b48620300c10401c0d00e507021b801c08016070076101603025050503a009582c0620035548a8409840050707002440800d4650020801101418080e6200c1981030340000401042c04501018400204118601080910b195881c002e4981c000c0305c02062040b41c0001c6c640185803050703a502100e0050042a0461500302032411319a00d600840031110020f0400d03600003828502064080c0c101c840c0c0d030018009400250108981403130302c500708140c0c065000e00c0010003052503e010640a5403281d06040842e04150040040300c080c145c2c0180e00c281e0042020000b02d8070380c0001071003202c0e0300894004031069035210585c204110400c82400da8801e40d80004240b2005400250141c034000c2c00400440d11041c01d43c2403103120f000111030118008100401c0004d10410003007400c00e000750550341d40207888141845c252642580c007500045d8a51081c4a4207000500c50301c1e4008809000030074a50b03140d941c01906440311701 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 7571464 1250 7570214 7570217
    0x501170f04060207020907020d030e070302010e130e0f03040302011e0512040203010204080109060f050c0a050a05090d1707050c0f030d030906090803040507030b06010302070c1404090213020909090102030115 91
    0x40c00460104006078043e03e07800c0d54000c1c00c0034aa480d18260007952204030400e2600048c0c109042544540008a00d44060300d8040e91800c106001c2003003804007004005440c018005c0d035a801c81829100113014061044a803500a1540c82c1c2c0f95000040901800c100e120b0400440030005407802038000701211065142c41c2c561040d699281d0001078024000d41c2e0102d1388650811404030100441d5511603d42841e0100040049846100050000380100466403000c2030b010040c0000e0540070f84081c04407090020a00a24000390303a5688001025990580f0708190000c00c4803820050b0511205e000c2030b2084d1850711741000c009000030b60750010784c55a4410315a45412030030130f100c002d400c140c048a41003140346650381131500d4425990034880c4001c1d10300c0c9607010089042584240212034030250800114a40641440031241e080d02c1014401035000e562940c25100680355115031001c1000c55420060711140c070041030203c0b50b44002c0c613028840e40704000501403540c001805c03d0240c500da = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 7572714 1250 7571464 7571491
    0x801050d030908060a020c19110d1b06050c0609010c05180d080705060f160e1002030c1b100c0b01091104080601080d030e060f0105011211030a0207030207050117 71
    0xc07428107403007806080d0452030300c0d40a90400c011420281d5001459819442011180401d50308000150300f11001030b0010024030704000965900d1170300454450040d8010060010340c0d5000c018145028000c6a000340013041c800300381320703502e810280403035584128100c0080c480c03c4500742009045106031540c0356810501c450142506031512614005510ba002100a03900c26140c200a9a43d41c0c044484650b624034107170010302c518810040007442080140c46010048207207404110903000d444001d44114807041c0484441407c040001004804401c542d00100340711004c1445044c40030b603010502030000d400a030780c0005110042e6181182c80030a8000b811119142d00c001030341c492544413113300e11030000081402c410220721804c981503140c5003040300d440050810344d146c0328110b40000881141100404c555405401c1000480c80c05943c0001d540c0c00520752110103800a07102e80f00342e81d5002c5460020550100490741c09003409081c4414421f61303c000c8070b40944802420030a62504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 7573964 1250 7572714 7572739
    0x10021305030105090a05010b010906081302040902100306031110050301170309060d02030a0c0903080a080c0f120402030c01022815020f0304030e060301061202090604030204090f14010606080105 85
    0x1154811406884024000c1c8560308111400710f903136505500d410b03110b0354648020b040b032640c05480c440c003c40b0010344400c0e05691305e4403007001c0d2107441000d0590304203442d0484c8400503514002d80c140315a4003501c1c00180346086080c00c0e4406c01084142500a0102c10480e9034801d8001d020789046402e40402d1641c5010380c94000d40c02c5004000d1115080400469102c0c485651a0080c51040c074054804000c1c042e66010103d4146139144800b40416908100c8a4010b13031141035250b42c010300500c4414035001c3c106810400642c08202c013030b8505c01901c02030004500e001d2002c0032098100748002d0818440001040c100407116040d15804007280015000c100010f048030489503c078004011512188d503015a5a1107a0044a00b180000c55048555445150080649069884070f907914800000d21149100080d4468060613a020300c05020000043e61980a0020400d10400032000c4003417442c0f40241d00507414401d02c5140741d0401d03506200d80380d8422245811960308a440b498a503a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 7575214 1250 7573964 7573987
    0x203070807170c030d09050f0a030b010b0a030e011a0907020703080301060e010f02120f180a08010c080703020903190311060c18090609070c050f0a060507170402031002 74
    0x20940d00005040c081d034900000d4100c0c0303038841c250391503a000c01a00d00e4a4407000801d0784034081100c03d900801c044c00000c1c030450600490142018802801e010051622910f035041c180303e090b8040c180d90140010111241e42c0c1c1409140410440c540c02805058840221900c580c280c4001441c000c2041e40b0000c1c0700c1600c02c001e60401035801c07200c1c240c2c3c2c950b180e00c0020480c008108074107010032035007020803058910010300f22014500b1421500c3c10001c5d0121128200d61060010444503050a01da50401c0d90311300301c0300c900802240c000000c007141c091b20003038001d5200074510028141f0500c940680c2d6200424000c0d42d160300720350b02c2e20410034640340640d180c05242c40950494442c0804000030171040500038a0248005180f40b144551800204044d40b18101c88041d000307055800800e0300507015403544460b081c13080050711080b4214613000c3d89009840c4009a605c25141c00620072003580001c4030b41038048010064220740d01d0541c012a50b112400070001600c142e00080d00030740c0c1d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 7576464 1250 7575214 7575223
    0xe01150203070f0b06090c03090601090e0a05070902040603180c05040203040807081b0c0604030c09020c0a0f05010501140f030613030203090d030503010510080f04061e09061509020906160203 84
    0x22030b4403da011106940f60f042c20500c0110031074409000710101804115000800c9050341c3c4220008001801030b42e08200300700014007038400300d000300c2e03226042c499000150244202d50103400018001600d592405c0d40041c10303550a0110951069451103000d03020a00000c1003905039030b410b940c05070343c07030b1074600d1b003a0b29510170050041c00f1b40b0340100e04a1042d07148450f010f41100441030858410406000401c0781350711692000806051600c0020004018150064491030710200107603003035441c00392a0301c2d05c40703001500c0c1200d040e5956001848000844407042d507003008281d8400c0c03164009140440c5e84c43e04043e0607020341c0c40e8014a5141098802c2044511008026043c0b2a00b000c591801611035007081c095207204485a111074200c040c81041014441c1c4280f511720480c680f101e85400d07000302580d101c0302032303c0e00410703120f826008124010810a03510078200040d00741003075281030f44425029044103082c07600420031840159544803e0380d0028516101c3d5100841c070030b1000070f00c7d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 7577714 1250 7576464 7576477
    0x309020d0b0c070201020705120d080c070204050c041a090a03060b04060b04080a110607030f05070305040306020301060503070f08040c091d060403022506020a0b0403030b04051005011202040e01150203 88
    0x2001c0c0e428104505903081a02610516200ba002c0b103644544038010088140043d24111840303502509001c1030b1180300c2c400a54001d000c400c00b082c40c00d00d0301d80101b010740304119805810345d54001402c00004410448650f062100181da0710b003803100031000980c492071180f20140c0442e448410111045c0da5652024004280752880c0507545d5684452081d00d41c003100d001a00c3e1101c0320360b0640d00c81c3c02c00740d084500280d4555a82c640581c0399910581e0103401140c0180c0400005000200010361144000c1d4040c013416103400b500c0e4030708aa40100b1124611488008002c010800d01000a100c0c007a18410b8451401021544000c640da501c4111403150889200600c514024030081c143c0115400701d520b007c4130248144484100c1a03404108610704c500d00041e401303121607102042c0314110380d942180c4a4a07020070380510000016084d0380082e12001403407050140700308419070b00b10049120040a0b40029414207141c07000d00d402e40d140c1442820a01c4101019407849648240100c414 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 7578964 1250 7577714 7577723
    0x2150c010f061403070b090d0206030414060108010506090601110c061803010906090c1a0a20060f07030501060906020c06070501090b04060204050a05010302040806180f071806090b010f0309020d 85
    0x100325543c2c50000c48103048010818084d0055001c0031807907145040840349a1000503002401c005050341c28081554030003882956948180d0701000100007050182034024600fa500100c0d940c2802002c0000d403c0d0f001e8245c0b03044c4000484058622940070400741000380c0110340c015101c00309540c001001ca44640c0c02c040e89546070022183c2004442e034401190030f0701409600c0c840b41d443c0c07142e070300c04030340800c0c400d545412041c80084180e07446134048030044210a080b284940a0499030340d4a809019944455001d412408010303040c1c2c0d1500c9a240140581d16103404c540c1c2c90312001079119131099034014061040003541c032017032040075003010070b08541c0115000301a19060074042c000b9046400350511482c080d01000a4541c4a4026241031390f81706400707010b454480300050211103a4019451806000340102910550400e2041c0401000500c00514113034141103078031404c0780d106800a020240c606000b0094030f0340d0010900038903400604001500c0200b0f03000185c840310f030101e070090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 7580214 1250 7578964 7578971
    0x20f030309150d05060d020d0605060103020d0204121223030c04030b0f0118090201090b0903010609050702010e010e0a0b070807050d0207030504080d0e01081b070b040c0806010b0702150c010f 84
    0x2011810b15000030a404242040c04000c140c894008108155400c45c5000c0d6218514a032540301280703196024030b40003101414018905028040c030542a03820039480000b18801c8603540c841403120140c0103008503e05842c1c8580d4024a84030307101801003a0100f004c40f540000b10005d49001000c000706e030b010315049003005525180c085451800720009000710112100f201d00f825514044038021481600e0381615504002070401079000020380168003102c0e8559218000020351240724072070789011700000e0b0700200340046d0110341542550a4510034100c0d952046114002082e0030000c0ca40c0c125440d0310f400c2405440781001158280508a868422035100044c11010941c0040c01002144d182e0415145035507252602a2407483c0807801490100300040002404040202c0091490b03500c00381c0700b035003061200c2c0c4070300309403074411102100e08540b60b034001d0001c10010480301c0d00506444504515185043d030211b4015107400c0101e0680000124817545510020f402601e40b0070550401003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 7581464 1250 7580214 7580239
    0x1050c03030108011b02071401030c02010b1225080304090207050708060702030a08011e03080d02041d04060e030a020307030302030a06031212060501030e0304050d0c0b070b060102010506010e0904020f030309 91
    0x5009000c50341c85c0106070208050b081c0b89440c004111013089440c020f007000b111203031340401540900780c1d0346036520455503100e04a51060351880329400101e8140d40c0100001f8181c0021840c02000c030480000e42000185010451007200100b106c0958404100240e22613000d850903038981095604100b8030350141d24200910700303500002810016074690f49400d5140d90390300746500c12000c40307000d5440810507280280049000e0000801c0e180800b003e00624090355a406c00304503074152480900c0765100b0328140420b00c030746405101155a021000307980340c04514034000c0d41d644208038008007030540110004090038002d9021100554000314182030003800620002e102c071104980d0750403a2482c2002c0828154483e02c995074141d036002c0011845c02e8103000070080c0f2500501d5044554203450440414241e66000140901d0352242d072116a8504041001900303456000b04080d0410003440c081012503075421076000c1d0041e4059800d60030590b0084003081c00d40c891501c40c00d8024a000700710 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 7582714 1250 7581464 7581479
    0x7060902090a061203140409020406030b120c0a030b09121603110601053007080f0712020604120302010902040515040501080f1c02190602040501030f0501210201050c030301 76
    0x81600510849189401d0341d9542a10700454a0134090140c205082c6020400024020421810030202029210b42040da80e241400142e91143d00507000003929034141c04105e0a02c20417141c0e007203421401038112080103402003030304a440d51101600c4c0c51107120215000620a001d1940e002840c0e01d500f40d80d40724070021119841c0102c210803800100c1c1011544007560700411841d042c1d550041010041140c000b40d03005491608a2008420074100c1805242c0c8100400a440c01001003a001d441c0101041e4140c2d4141111a4042d52082d285030035a00010703a00c0d0401c54094440c001001e405160141c202240100180302000750080d2415081c002285400c06007030643d44011101840b6981e21b030400c0648070b1502d0541500c03694404004107200060010700c0100c007880038030454040c251354058070102d01c1401d89055814aa00150520055906004135041b1148054052009500d450407190710149914100d01008007050090011684079904035030390180060308990f00d035612107a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 7583964 1250 7582714 7582721
    0xd0e100204032009011502030c06010807030212010204050a050103090602090a03030e03010b0102011109092d010303140a020a0809031009050309010305090f0c09060105190f020f0a0c030204020a140706 88
    0x8142c6210743c01092024112a03a281c00b1142007102604011312a4a0001c08207003100b00e040928080d070000340080001100304002c0c40b0300031310440c00104103492030740c01400b0689a02e41d00c0224030381d0040100340400e440f060761040c00c80340e080c60000f48600ca5414000d00034016a010140c1c40360460740c002090540c132940a5031184d000301d000304418000034006a0132601c8403080515400700c20701c0351241500e4051a56544070080102c8690107204c6110f04010414100519002c003064000061043c164041041c03400c8103121410301d803826500315000395032242200c8004010b0000041c10303c0842d2024045500b06c1c04103100f05210343c040c50310b03082d600ca410280800e80002c1c985400140e1602000551058001a04003d81a44c18404040c40f1202c80010001410301c4000c10128840d0040b6442120380d40030690f032181c0c000452444020308188030030303031325003901d03440b400c00d51005c1122800030381c0172241d040300c0040c0e84a8a5800540300f192a8540c9050007410105004061011681 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 7585214 1250 7583964 7583969
    0x6040e061315090c0302060708040b030f040b0708060105030f04151503020310020418200a020c010305010509010b0a1101060b0703090806010b070c030204050402030a081b0609030307140d0e100204 86
    0x316200060b0031544140450780321207405401055401030030405801c1120046c07515a0242090500e05512004102c6580d801501d108000810381070070032092203452000e19401103420f25003451103040050000348980009055000d281d4890408201000040141110340c8402c2c140c0a01034a800c0411180281103248405c4c2e01a00031446681c440d030506108032800c0d42e0100d84420340d480f8010460f44020078210280d607041d06009050484502c51f440043c084d40e410950082c40e031404041c000400751841030f80040e004503240c4d40103101034801401541c107103911505e03041c200f100151a40c00e024240991081c03d580f1800a025000d0540c010200c0c02a1340c21401200e074a0f0b641e81d071403410240b05070344002c1c0c8101160a024401480e142e0001c0d500a40000e00721542c6100e146c5640b01a030b4400b030321030b00c50007101c91440c21071104c042c402182c0c4111800702450841c500002d001d040f9508140f050501001c00080340c03d00503c0c558441442e420002c4111171400c40381c18441002540300b030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 7586464 1250 7585214 7585223
    0x5031003060c0507021e0901030f080d05042004060e0703020d0902150a090608040809011b021201020c0f0c09040b1b0f09040b03030c0c1003061208040302100203040303021506040e0613 81
    0x291245080007030349031561a411200908059240c8c3c0ca0b5844601074041c0d4060100c0381d018040146142c0c00100f402141d000c0c9000380c107000d800001c500f0240080384000709050703001301d040000400480700040c41700d0764824107504003d42d840c2c1e82820244003c100864001b07520841c1210890001e03c028000307001c846102c1e450b4040f4141e00d8110950b81c1c924201c40c0100b84810030080e40c21070354480c415008940c118819086c005c0011540010726080c0d40744d4094181d23a43c041001d1201c1202000103000c03091249010300711401d40344c7d01184210000801c041c18290000e400b042440202c20002e03407011007450003c603224083c20650301499840070041510840c02c101c482e101d01e00d0080122081011100010b29056640070240000440c0404540c801d02d5610b59000600519000c41202414407904400d681c407401c51040168503031012852008550050005000003038000980c03a0301d50300000e031703141b01c04c0d9030300c800203405081811289009400340ca0180484407101e0035608034010b00c103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 7587714 1250 7586464 7586479
    0x40203010b030708030409020703120915050105010e090103060504030c0203031306080c04050607030e041d06090709060305060703020304110a121202030a0504050402070204020d0213060e0406050a0605031003060c050702 96
    0x10002c0607070f50030701c50041100c0380d0030800c4100882c0c44180d000b00f03c0383e803207070400508000b25480480211038150f02c040c1c0d500201c020704022800c2051103154003400b024202240081c00d09400300d45812014040144000d0307071031000c00c050500440c0c581d880300d0790080440e0780d258032122030702554038814803401c40840c0d0010085035841c0b106d03209840580f58064500350820455490840d00b0b1030b5031301003a1380c0003aa0741510588065100d211030f0062078494008291034200f001e02c50385000d4440d4044150b4038502402440042c0002ca505a00700314149800b41e1251a2410145041c0e61090040c5902ca11101000582600c0400b400c55405000d0410300e001440c16210507602c80c0300d0441c42000051003004140a03a1a141d03020f41030860002d0001810101580042000c90f80320031070030112260244003c02c2400d602c05c2449009030401e803401e0103994035000200300415a240224000d000303000c40050000308a04103940700844e0031007400e01040da26600060304075441090264001c008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 7588964 1250 7587714 7587731
    0xc0102130f0803030c0f0306010c050712150c02070303051e120f130206030109090302030f030903120106030b0303090f04151403010b0609030a030509030307050607080a0b010f020a1b0302030102040306020304020301 94
    0x303c292481065041c0680b460045503800c4004c40360702c000c10f52418071000c801c4000100c1c5041000e1400b030008502000da20301e42c41c5c14a0908038040d803100b402421300380031907404031543c0032a1080c1102d601d41480e41e02e90307000c02e40d018010900c24070030045072a804140b111000e00041145030107520102c51740046a111002c0c030030700d01441c071034019410800402c01040030151542c85080018080d1041e0fa05249500301c55154a82c01554034800360303440455443c44804000b83d109004102e942820000700c00a50080781e01da01521003800c0c418810000003241645442d0454180e0509010340b01c140d454840c14001d100741480e0010f94080e61a14403100324500f444800c0343c200340340003401090104421b9600301c41650103110034a406010601c1000d0004900300a4070340151010b4403045003a1510071440e408aa160350601410003082448124250b600802c3c1460790315041a6001980b41d03000302c03051100c0350140c1c0020340541c4000f50002c00c0c008076502071070086c1e100300c0c024006442d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 7590214 1250 7588964 7588979
    0x50406021902010c140f04080f0303040b06030601030c03061802030d0207030506060d1a040812070305010602060705070812070908190b090106030302121303020d05060601030c0201060f1701020c0102130f 89
    0xc10b0142400007040e16030890341d21702284840603103035509002070a00c0c54691030713641c00ca00b4443c1289040780a680040180420042140c3d080741d84881d040e4010a42c039851f5490718001303c2202d10000c0c120f140c0c2c034405100d01c9a000520903203800c0d000380458014040c1181e000390303110000e100645580c0504800704815291804034603540c25000101c50200b22440701d8145144100030f00100e404280410024070406080003c00380303c1c00c0c02d0f0314000740941c98058042d041c144010400c03070402c2820006c1c1c0001500860075101100114810218180d413031000540340e101640d00f0098061045044c880d41000c0f103450804105445200c80b03c40c59110055298203984541c0402000f50704081c11105d1032815540141c0b0703805403955407e40c00b0654980105e01c4490300c9503420b448a4101000300400e5507054059078011a1051008000c540c1c541056618510420b01502091080440140038060300c250180c031400e904481c000c55540000740fa2450b41042288101c02d031300481c0311000218070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 7591464 1250 7590214 7590221
    0x60108010b01050406080c09041805060106030c0504060c050705090117071202100f03020904180201080f0106080c0f07050f0106050307080a0f02040518070305030c0124030308041505040602190201 86
    0x7001a10f0312400c0c10705003c0103942c040001044403200910a1141c50065179850080d228108440240c5410749005400c081c0d04188050308000103040c10702c507010749030320340c401e04480456480c1e1411690310305440c80e020b414130195521481d80004107500114441034040031201d480041441109d102032764030400070380d580601703800107948507210700c070072240e01c42c000c404505c0c4034091481e0051600c0709000000b02101e400c0c40030420004524802030301103580001c1e1094110000f907a82403015031600e0740c02000c0c0080207016010302100030440c1c4101042d244c003a111000d500c42e040c0c90007080350145c120700801461103060300c20711601000145440300880c202d00901d403c0801010046c489030203000142c80702030701e00c60001c10b445529041940d0140302c44006903201e000515940c111509002c1d00350741107041c505000010f018809203d14080000142c2143e505041000c0b0540c2c441c203000c085001403508d040c0056041504000802009500901c40c1c80100c1c0040c241620600303208908a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 7592714 1250 7591464 7591481
    0x207060905031e0a1b0303030605010c0f020103180b04050c09060603010f090c050c010e06011406090108040f02030a0b160f0908100b0a08100b0301050c0f0703030b031903080906010801 81
    0x340d0410400000481c0403d810041903c000d00121405403025542e00c142c2040800d046040305145002d042c400c040d4940580303c010042442d1034200c802040d1120302c0c0303480c19104028140b59903030405050740c0e44601001226590001d0744041c1503c2e1a040151311595480d112a107e21140d50028aa03850820b003541d0503101c03040c60b111841418a5041c0004024046494051100c140910a50301c40c09000e0022840061805006103503d84144000c10235440316559215000078440d039a01a42e00c40e814950058000041ea41e8401c00ca001103820a0b4400d800034151201e014200708030304585451541c1040c5481c1d032201e001800c9010112822180d0340124246501300c02c060034200102030b0050100c10900401b1401459642c000e00b030310b85041e0401c01100d280d2100700d9031200344ac00380308580e4030000c107400c410b1408060441c006694400c09100034181940c1e489445030b40d44042105d040300c1d444160800c1c0c524202c40c2005001144116003200040c403c01001245541060245194 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 7593964 1250 7592714 7592719
    0x307050303010314070e070f020601050307061202030a060e01060203040303020c090708010501050a0306170c03100902010207050105030c0903030d050a0c020c010203043006020703090608040f020d0f02090a0605010207060905 98
    0x1c5908541d5a040e07012403641c030f12080b900c1803080c0401c095400c4401c1900842c1940c480304020b141c1da04001c0e00380041644501d11031f400144007004000e4000020382a06103690900503034a80c1da2201840040886070040544905154000300f1403680000062042c9d0380240c08991000141c0b40070024085007c83c3d80c2c90000d0701c1c05004003c55409007000c4d16110110303040c0031484513122913000608405070025600d027580100b03040b200c2400c3c1030085182424034440d0500240c1c480e500040d6840b0800c0c0300740c03410400700000042031590031806031607892100906496480c11103503401000f5080a0303413581d100314030f4441c81c40c0c140c5000060038818540c068026500f09440c2c05601c402d00e00a40741144000d40c04a550901c10480900f203040181e44103000040c0c030b41c00181801000d03c840e81e000401400402014040810092006c0039181070b41100c1d8409a001145071a251400c500c00c4020341020300c49051060318015038000c0c200380d800aa00315440c95698150031aa0307003c2c288111034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 7595214 1250 7593964 7593967
    0xc0e0f06060a0804020303120405010b010f0c050309010c080403050a060c0801090b100806041508030304030212040810020d0209030607030e061302011d011803060906110403050c010809160b040e060303070503 91
    0x20b603040c0c01030031560751050004003603030b003481ca00403045075000b602210308a5050750341d40510602507805c00b00c4a640b0b5551440c141c035080c000d980d20a640d0f485076240c818180501c2a880404100c0d034101110003443c0d005040e0383d5a500c1514240001c3d244850b5000e0104240030008258200c0344d02c00d088420b00000d003007642442680794251070303504010341415006511048031030404189009840024044600250355a1426040c024107160350102410ba14220800c010042c401002641e040191681c00b4010380d0ba0342c00d140008024803a4000c22a01030040038100103503242c06501c54289015420107840c0959903000e40c901150441c414000c0c04a280840141e000c0b0010303100080e1700c0841810542104020440080c914204507442118200c1e20780130a0400c0010034040c0552902c42e50301074a00302400c50340c0d8151580020340c040c0381041a508000359131003104103d2a100780a450580c107160755100c40d40c0c17404c80d0f84140144401c804850003c0340c40ea080c00000c43d040745400c01c000d90b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 7596464 1250 7595214 7595227
    0x16020a0b0406110703020f010e070812030703020717091005031603050604020f0301150909050403090308071a2a03040309030215090402130e06030604050709020a09080106030c0e0f0606 81
    0x200300a4007030010b5030260b81c0c4004540329192103e000f0800c81e4003980060882c0a10100450b0a45544048040300d503000365108000c503280020b00c48000d603600c0c4656549a50354843c0c101c009029548018211012000f4001c0080881500524048801356002a485007000c0c909840c544016504060543e81260b1000ea500740f103a0322440e00144020310142c5400c4460000d00c140390001e82103a00100555000750a4441c2c2041412004203200601800180f8064034040c2c850101844041c0018200141039010402d11248000503000040140001800e1040c06200f903141c0000c0f2100c9500407078132a590131510100180c0c0e1042e54036581c0e09002d07605550911502c07814a4800d240410028040c800030b0b95102d0002e8007801242c051106609841c010b04c0086940000e80100e01940000341407001103800440c4490546024040240c0ea81114200c101da0100781c2c1c1c1e0001c101540313001c001204100d0b58906c0785046450070001088151aa281c01e0f400380d01040e118643e1000d020002d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 7597714 1250 7596464 7596473
    0x609031b0303020c061c05040623040305030f0405010b09040305030603120405060702040c02150a0b0907080412030203060109050603090a1205190e01030603140106051201020c0303130c0302030307030203030702010516020a 97
    0x184218550016011b148050001c007810a48800752000c481054a5128007088028003030300c0c00c010340c6c01e10b0316501d190703040640b0f000e040d5100241090351250207036130000c1c0a101c801d4000e0030304800017501242d43c5140138203006226130819201544079011700c401620107502c2410a031020b0301c000600c074030719040b070507800c001c020a2800c0024043d4040d000361403010306043d4004034800d0355034041c0810100728650400405100081114084c0071528061001144600030002d25004103030038016602e40b00e00c1c005a89210813a0b00030783d031182000040103401c50001c41c45021503440781d12800d00818552405450a00845040403061f407103000d00499031600c6000e01c00d00d01081810005100e1340c4a45401e43d8941c0403070115411691541003c104a0808002c4c8440018480c4002c500f00761011200c280c580c0f1020340544140d51440741c046080c000d040d0350341780003107074001c04803540d5544516001c1d40740d4101312411030141d407a000000300740c1801100403640c0c0c2100d550152812305003990b035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 7598964 1250 7597714 7597717
    0x10201020423210a020102070501050f0d0902041104030303140a0506010219060605040903050703090906050f0909120c06010603060e01050a1502010b03030c0102071b0e01180e070609031b0303020c06 87
    0x3801a4008600301103d80f900280210824011508001411007481c890001920304005070f4402070410500704051101d4003080c5044d21980e402c60382d0007080c070400300c0c00000c0c040c10300128206030210002a0001c105034141d4410035440d881124202c20980c1e03080d0b0054200c0354101c0e40c1d140980c20214809140e04003010a15030054460007002a000307440d42c0201d41200c810003070450115000103103440c14181c020015000030308207800c0c14400c990403e00420030140a104015004000c90004558003520620028900144d003006881d201d04060014039a80d0200b0b101c0c070030100e8078000c8081894260b00e40c00c1c4e4140c607030103006034180350300d0104411409005c4519040031550b1391809004169400e0005003c3e0981000c00942c6400090400c810529a40d01d81002611601407003088200480c080c0c45044962420794140d1031035800d064071002d001b041c450104540180c0002003001c581100030041541d0103080304d0050a11000180351502a4501026015a01400800200346032100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 7600214 1250 7598964 7599029
    0x40602070e070903050106030308180705010e04090c090f0b1008060105030c0a020a0b01151106130807080d06030c06080c031003060b0609060c01050702010c0912060504020103020708030f06040b0102010204 90
    0x292410f0310f5a666100d03642150301581085001562140070f1048800102951100348112240030b06101444c00b0300103003084141c01032550041d5196803105080c0128900c104000300b2040e04107200812a148580000b44400c01445104d0005c070425401142c1c4200241445694180c45032403858071441000c5240c0d41051080030304501c9010303619400192040c8405000308031540d20344140e07062710080a85810844940317901203900000400603144014000f01e40441c2d04185800d0755107a50b0304049060f44950075500050314140030b000000c02100742290006c0700c015035511100781e181c6c2d07000f1788480d1205580500410042c840c003440816465448021322210052016190403000c1000c2601500400940c4915035911400c000392a5020300854040745098688145240d04140708401001c00710400034180c60341e184005411640a64100e48030b081e00300103d41c0d00e80c030b851056840c00030700c125801d6001c0e07414082ca51505e07500500a55050394492401c00c0c1c086520344071200407688480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 7601464 1250 7600214 7600217
    0x1060c0807050a051501080d020a080f04120f031202030402010c02040b030106170109140307030c0b0603030409020d0203070e011e11010906020c06090d090e010504090302010906110904060803040602070e07 90
    0x2000074000003a0200702c3c030031145118001401c02c0d06080d400540102d071050b4040c1805030403502e28094282c0e80400c10b141d0460744003040da80c44241c180c503940d01900841d08801c804000000300001030040400c0c030b107030b0514441d039920240c0e2044840d44400380e00007990000d0203d003041004c200103181c203800480300c521019000294203540c410b1803c0c21500440366006113a5558485100ad200c0c0054901580103000e000840c5490020398004200104c04c1d100944691034000c00701d41c50380e90a1007110014010003501750f44400071030600328020b40c426207110001c2810001210a603500070790b00d440704410712080d00038410f1040d040030740d25491610750301030103556a15100400140b0344e10203008442c1c40007004001d20b01d4004640e51820040d8a0480240714800d50204206407541c400681900c00982d0040342e00c0100f854103134050411003200600f807500b044000084070381d4a00190441c5002180c09018144d82c400074a030308c1c1d00c518014000140c000711804c2c403007601c07401741158002406 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 7602714 1250 7601464 7601467
    0xd03020c03030a0c050601050d080f0c0106030206030a060806090106060504140301020f040801090b0901021204030f0e0a060f030b0d0503090d0309090c020c01030506010e090f06040f02030a0c1b0b01060c08 90
    0x300300020703045034030880710b40021542c40462402800310401100340036140941d1101c1c070700d075015150100c030ba0096104807000001d0000d0381c0128140290090802580d000e00091f80b681046800480a08141d000700d8445200e0780b400a905e02205004000403100c40c2d8450601e01403c00070318500307010032426103503010340d0208401c9103480b9048004100404001c1d0002502c04501c2c9441c03241c8002c050541c5c1c516078014030500e200100d112400541282d803508282000b00841f08080d0380c0000c1503001d09510090b00c04000900581010040039902019a0100140a180010413054802c803080103060f5038024001404a801c080d581d10703100c1c600a05042c03812a50741d06504d0182c4100c40ca290006070040c0c0854401540c060042541045007402e0190368080c1c1d02001c5103e82e140246940d104280040200c0c40d075845541c4001c400400011056580c0d141c101d10000140007072000020010b01003e52508017402c0289500e0005030340845010341c9a480d116080b1140122800113407403180d070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 7603964 1250 7602714 7602733
    0xc03050a020c060d0b03060c0708031302210109060605150d0c05040f0603060311010305060609010f111603020a0e0108060f0601050d0515040509030a051b03040807120b09031303020d0302 82
    0x100c40f80a400c1c200302240300420328807080801e141c10075101a10b9044601c0050165070002a0b004064035400001da0084480401280c0005008080c6180c1e0207040070f84202030880000a064100c4400540150b0003403040e15036900074440c0c90700fa40d00d00301c0342c0c542050050160340d01c6541c0010100d00483e2074414201030310366200715203092130380c1e03c84408691364010400401c1070280c800061220309003010061440d2800114840303100d85000c41d4104002d40c817a20203020300402114850340c1d0386400f110390b002011240b1243d01c042e8ae000c2a0300c10040c5250000d181d5440041c902c0c141c030310034005040d9584640b130070100d207c840a010141404010b11800e0810a0584543c91003a08800b881e0458400450240303c00c40780040e0211646810801c460f24406801004a41c0c41809608e00fa008980d42c52100d01d08502841d00900079a01492000261549500030f403160117034001c110900603a01e43d02060390390380c401c0810000b08064641c20800c09841d004604001c018040d005031100c07140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 7605214 1250 7603964 7603969
    0x303040602070e09030301030c09051009060803070302070e040507060c0c090f0204050f01030b030601052403090708060a020405030c01050d020d050106050a090f12020409080c070b030f07030b010c03050a020c 91
    0x400036000240140d100703840c10880311212002ea40d8000c0100c101031031855045885240c5002140d02802645584032000b08850605603c2c0c2d05006107038003041000110385844516841c1c0d0f10500b000d078010b00c244803021134020b41c00b20a070b42c021907110700200040791410030142c0d0444000324054440005034800010740c8041d41c000c004d03904030701c1d0000594682c03c0c10100302548bc0d030301508030304042c5041e040b0402a20001861810340d04100c800c80008202503070300f01d4240400516040c0084004414443c0c0f50b1000155503050346c041100f0746549170f07505030020007240034074422554513920016404d40d02c1d500a400030010320f036500310058949a400c401c1001600d8003a40306000180340080c1004960394070203c2c64010302800c02c680b4003ca0b2410b00d0004810700720b0b92010340320f140d44600040410030300d81c0440c0c8011500c0019120031583e10407500d01540c100715200c0042000c07000014040c0c9110344107804001805869100a16509850403201900100f000e01d0a40c0b145a9607001d03203a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 7606464 1250 7605214 7605217
    0x1e0902030a0f06060203070f030305090307060e03030106031103090304090507110610051302040f15110601090603020406050907050304030e01030f110304120f02030a05070203030d0203040807020f091302010813020303 95
    0x210915040821264490b040c00400c54405038850411500300340044000280000d4201800c02d4141c9004286038644a045a06503c034a820041146160040781041e09401001560485020352030401c148080040010854881103a6609458204105c2072058500d070750301a03a00840d0610b0144240c1d001c51000a184c03410070364180c6a000d41c0b07050100000c0c40d03d1000386070f80000b80c00302035003014a040700e983c542207518014850043c22441e21a0006403142a21441600400080b683d403540c0d14a8040c0003040076000c140d004500f0008080f501d4280700040a0080025640365465543c031760314110381040a240c1294100350b143c103500c1c00001e50314080c41d86a5a4100340003076a80c01c0034a41182681502c0d040c40c814414551025013400f5000f0044c3e07103204100e030808590752541480020300350b124401a1003503062010040c0300500c0000b001a120791341c0f09a0b82d5050200341e110400c40a240704071140045400c1f23a608000041d4401c0214035017005640c100400d11807940c0e40040d0a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 7607714 1250 7606464 7606471
    0x9030c0b03040b011401230f030705030115020109030c030c0201140a02010b01030e0105060102070506030a0207080d05011404110306011b060c0e01020d0801051c1505010801150503030909011e090203 87
    0x401408020b00c01800f182c50f0400e4010800303c0200c1116188007000030704416009010701c4000000c42080e00d00300e2003040102d41a094020a419640e403500150207001501b0a00841134511420001c40c100745005104210507150582c4401c14100c16030b68045401130060304040781040710507a0100c507458112001351105000c260004640e0403100c10004080350000d0181140d00c0c0c3c1010309000251340c01141d450295001a0380003913999490900300d1010b03108102e00140307590000603200069008580c07006069440d09161100503503082c400304001eaa6040380a003100c40e00400c003042096000d800f28890401d0b40c20600046501c103900d60200300c0c0d025181640106102e03d0310040c0541c0c0c1808960901c094905000d00745504013004030b4400c1d46006103828010100b450f81100b8001c6181c1048d00a907140c0c00c0c00e0000d5030b11200c01502a0404802e2036600c0c00b00104040350918002c41a10100340025001a88a03803a080c001c6151220490700c110344800994400301c0d4600da1030000b51721 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 7608964 1250 7607714 7607729
    0x10f0c020d0201110306130203040212070306050103030905031501050405090705060c010b09010506070305090607020d0618060f06050108040611090607061a010c02030d111603060501080601050a0506071209030c 92
    0x25401d0400603007500e180841d0110308100400801c070f09591254100c1002d45403034007006031a03944501c0401c4011000502110842c80f4141000080180035000306058920980d21202c0d0306039110203040d035030312458000340354a02c1e20a006200605040d0b10013a440079981040300e1003580e0b50b20200310140c5c07018482d070b00e044c0d4403800301110a0800078992401060190390b045d1600d00981c07001860b9000d9046400e1041c100012000150f548600d10340900d02e0f00500c0420010128420403c480444080b00701c441d9814140040c0507003e00b0310070001120340684480074071f962181d60b014003d15410741d00c804558821320084005448040180900520600c40001c1c5240303061103844900c10960340c610f0400030000003840040c0c0703010a080c0c4000b155810b0000081503255405403e1545000d081e1054141880c80001440f10581050341201c401030180d410503621001488204007160050940205040024800080790034a10440030b02c49858600c110a480341e440d000d40c894103900080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 7610214 1250 7608964 7608973
    0x51207060f060512060106050d02070b011214031801080a0e01020309030409062304050402040605060a0f1101060e0403080405010e031612020615040e010b030102071419020d080903010f0c02 83
    0x107000c20140c0314001c09404111001c0b80e15000c1d004040d40e8407441401108208580440d400d640c20040381c06480d559580b100d174203403240da1a5004880c03040074005040d662102c400a8580e00d440000c02110b8001c44c40d4200e11f000c2e484400010748100308060b09950100307a694490081441d001e20195002e0712a820141da0343e14505801c00043d41c100e6080400c02c1d07102020300e015841d04076000c14402c050103803400705081e5500c0c00000d009101c69482240c100d200041c0c00d05419a0000000782841d00b603485400f0507400850005003240e00e1030007581040c4903200049030100c3d015980c0554003d00c181d00202380040095406800c640001003007440604407031140400700106150b168101c40d000d0320040086103803094055041e0003940b4034580c0a250781e003903018002c000039044210340900280007590341d4071031803401289124104038084043c0c080c840043c195000103440364010030b90014030044c1100520741b61850b0b581c1c0300401003681590780f29010301102245001d409050020f54002c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 7611464 1250 7610214 7610231
    0x2100c09050307060305070905010309140a0302070f0b03010b040501030209060403061407031109090c090102011503080702090105010c11041802090a060609050d051504050102070c1e06050304020603040b0405120706 94
    0x2510302070340fa80282d0f060500740400c21042560240c0e60004840c000d180c0402d14602d1410308112000d989075200c5218040c001c070748401d0540011717031602210b0302c8114902c406691080907191030301080c020340c0710305c5000b00070400c141d40c03003034001d0f0a00d401c000f807815160680c0c0742e0311003080b95520310100300c402113030368100414107400d4420010b14442d403881035450702c1460300010300a00402400c058030098040b448010f01d91007540040f140c040c0385820079144070b80781d0078103400d240c000050492050701c0344c20002c9019440340c240c100d486c9a12035400c002d42c0d190042004043c0c40086440e52600c11400c2e003903005642d41002440c010002d1040004200303007000c1c070042c095002900010301551442010070700243c000107111302d0014040b10400010b032a1890882d0181c850060050b03c00290244089080c00f859002d06002d0740b9000705480a90755030304801d41e2180000c07075000c2d510410a00c0020081203603203100b180d00920070026161682140c0e103101c01d107038011603003c1e2181075980058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 7612714 1250 7611464 7611469
    0x203100503030301090c021e0a0b09011b05031501090608070c02180c030403080108160302040203040c080d050a03060806010303140a1205070e0f030609070b160c031406180309040c02100c0905 84
    0xa8002c2c1c2c0d2320070460210103a401c009995941c2c07415401403401c031032100000c1c01c506080d4801c0c005001c030444810040342e818280106240c0050349c18130100f0140c00d402441560103203d07004100d4440c0e460f529940d6407000b80503940104101030603038110412011521004100c0e0078142d10407060810015140d04060070010401101600b1a5849a10003000d00381611508086c02044950448001da501e50390751808040c40c08140d80f102c021071050a04141f882a04070300a0503861040c0c0d80e04100e00e5540b52405550303000d0030320001d0040380c80c2c0d1803003c1c2c04d8120200241000090360400304004a11070141000300c40046410b8400120100005089031a040c41050314000f0110000d05e00c5040c400500e40d1641814800c0e07038a010717000942c030010f8440d5604040716040c1c014245042c2c455580c20001d00c00b01d540801e103101401003c00040c8541c0900c920700340703c456002c00860a0150520a001c000c203201181802984640c10351119110764601490741001c903590344841a03507280900303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 7613964 1250 7612714 7612723
    0x602190504091d1c090306060803030619050105030c0c01020918011403070b12250302040f051c030305090c1306030303050f0f04030c080f0309010c0e01020307020307090203100503030301090c02 85
    0x40f0b03254900c0d007810342000b00c0c1000190510b12410007145184081400a6054948403101d5000401d01c80c1400d000180e0b01c80048046d5200329070a40b40790720711140981801d00407900b5401400e000c2007062000c03521610160010b000000c0300b260005250208840006812103000c8443c1128909540b0040c400c0001c0060b800c0e000000580040952a080454411003801000c01201010441c03c00085590754a4200b0f000c0007600c108007401c8802174140300801030740c0140100c92404001c0c400c0005c1d40e042039070307681c0f40d02c00e0040e029520240c1e6a98003100944000350501d5010301c00c030340d205001550303500141890240002c00000e005490340c540076003078030b0300144680145980441000030308120304c00021381c8182d05250040361910700c1d241403101401410b841090b541008010813004100540c44220103421945a440c201001d0000483c0c0d00d10640500030740542003404100414005a0061030700a0702d2882d01005a41d200c6c0082483c58000342e0000ca1b42c551501844d42c0d49640500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 7615214 1250 7613964 7613981
    0xa061d0613020a050702060c07030c0306050402010e0d080a1220070b132001030204030803070e03060f09030a08090c030f030d050a050f130f020a080c010905030a030807050304060219050409 83
    0x807425030822660b05800b40044c0103005001e8052500005c0c034800054040c00b861000d55440101d451540f41c403410004020102110b08034003095595810083c00d19148002481c0b030b40e80700900c2072415031844003c940e200000310b40c140340191904d00889c00030b0307c00140c81c01040b540741c0302c3c06e0701c1d604c06041c0207010f4400581685501554003006070086007402029070300090b00207560100800780000102c00a01c40d070b6001902c140c0c5c011040c40340280d441004030303020b01021411261942c5400c01c6942040b5400e40700001d169008000030380d0034501500d01c5680c40094841911b180928134400b1a0602d40d0801c00e801240d04009240400101544a0581c020b1400001080b041c40c0c0059611019030000c0c044040c444035020314201002071581003612150750180a90400a039110205c0755507a5500c641503011415a100c00f103418140050003061094240e520304072203440d40a420b0b216588060010b5400c0b46d001c22107903410708a403402c0040106043d544640d0348038984003a9004a80488 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 7616464 1250 7615214 7615249
    0x6090a0203071706040807080f071401050702010605031b1203071b06020601060c02040509010f1a01230d0902010c050d0e0a15090303030b010e1201020306090c130b030a061d06 77
    0x15558842c03501c3c1c0005078940d0055202c1581540d50b07100781020040c0f402200c520740d80802000076458200a90301c6040d24600c3ca4590003030207246c0f603801c03003070342680e00340e00803250940c0c080d40d410040c2034141c08104020780ba014103103625200ba81c1041c50b08541c019076081d11803c0083e0b048980313011403451920000c000360700c0901245d50401e04020f01782540800040d00c01e944900218481940030b41c09040300003480d82c0100001401c0d940350b8400300a5a0304800c1c080352104030000600501c00b22551500c1144a030f100d4a004000000040100b20040003a41041103221700080040c508110402e640481c0d500ca041c9610625420406880883e404c01c0b040410010640c401d850b41041c0c0ca201525030504000c207100e0a00001203940360100480b01c2e0380640c40c640454411101036000710b015000951740c0f035010f556110451280f902c1442006210104e84a5040003144000000f440c2c0041c0c8626002c58055610080184007054640c00c8032140400c200c05e12855143c14651100540d105 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 7617714 1250 7616464 7616489
    0xb0a1205160b092403040507030201020c0109030f0b09030408030f030103060c0903050307060f0b0406090504050c09041208060609040504031106060108090c01030e030d020f04060306050609130b0d0506090a020307 93
    0x41284582c400d01443da02d071400b61103803c070071108a100441e41445020035050f4076507141c3c40c1c1410196078501081c070003640580908500822203500c5096400107032038000c8040300c00710301c45031303030340c042c0000d0080c804411400305000c04107980005200410f030381244010026140d5045003411011101c2c80c250301406d10800c0e450802c009180401a01e81c01a00b00c00300243c102141c01201d0050710303001c805a030b0300514118020400c88910751100d40181c1c000c00840c0c02c1400e4020900500c017900b900c000d01891810540484058400c4007030702d50154020f00424145507807100482c0c1038440a481c1140818460328107d04040000c01059610440034030307000d585814941e0241e038944482c0860141090f44900307000da55007108000b1520007403e8800f046594001c051450400c54000d409000b00080c240480010316140143c19160300400041c80810360714001d0f0a014000c0840c100c034140c01581000c510404201c00384007051180c880c0001400c10305106104050400400d40c03ca460900380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 7618964 1250 7617714 7617719
    0x4050a0b0d051302090a0203040c030b0112060b0a06170a02040b03010e0402011d01050a1d060307020705030607050f04091a03010504030305180102160f170408010c0905010305090c040209040b0a120516 88
    0x403131605d500d070003e1481c3e0380181c1c0da40395030806c02203d802d0341c1c00207005c2c040b412000182a40390341c48421011402507a041240a000030200100031011384642d400280c08a4140c00445104a000540001c1c4641005103807540e00c2c2607031841504268401c5100b030220000b00410742d60800c10644c170380c202150400c0c111060702000a00540100548c180422010a500f06a1609003007000e108040b8018811520782c506600000c8d550403090103000c2c040d006200c04504124017030070964010a0803400040e05007410903034002c00030310a955003007035841c1d905222140191400e10406000d18066078000c240c03850540110b00c80c52003001c00500d01c1d80e104000c040300c404140c4442c600940d61188042c1d601010703a0508191507001c008802c4202c140004e00003c0002c015448048804060b89900e1b0100395544010740403207100301ca603440c0303540180c08035411a01d46a4010942c0e408001c00019005220714049414400c5a070802e4102c44400c0e60071806100b402c001e8400760204540030117880c02d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 7620214 1250 7618964 7618969
    0x906060307120b010309151a0d0507270207030807030b060f040306020702011107080c031204030308130302030c030c1b040902060a0806040f0c020d0f050307050a0e0604050a0b0d051302 81
    0x1269048032442855640c01c03094000d0384243c001060440c7c02c00307110480e0140b4403101200400d80009420b1145c1541004150320341842e004000354250410064411540b405150011518000c3d0041e441d42c45040244240008180b019040480c0295a4004149060300c0c0213411a8410500c5500c1500140448481c0d0000041200c0c01e07030b80d21410242e120011480180da041011041201c411301440780046202100024168408a402c40440d000221060340b1000300d44100c0c00301034001280c0c1c400141e82219001c3c01c096200f84a0301c100c0b071400c0742d14001d8038250382082500c5503144c5c100b2101d6144c0100e400c15180030b8071030308503404c004519190380002c00c98032a140c050b00901c44001c0001e0180d40d150740c4030742061490143c06001d1003180181c000e4030f614419082ca0089503040c2d0b03090111500c2042524032840854440c0c51034110b1052094808520b0781e1030240d0700c080c042201180c182c6400501800400d82d01c00e01c0c42d01c80408140003015201c000380300c0c4805112645040b805a03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 7621464 1250 7620214 7620227
    0x2010c02030c0a0f06020405460510020c04021b06060303040b07031d0a09050a0c020601030c1a0f0406020f0d02011a0d110907020d030b04060308030708090f07030f020906060307 78
    0x16503c5444d280c210500d0340380c04000ba002e190f01c92640302c40451743c11306a581c0780b0705080703441600b03910140045541d0801c180da0240000386450369130911005090040d801c04415448200a590045441e4400440002816039000281040c100581071501d018007032000c020140c0c115400710041c5080c00d007404000f40d080c3c0a920000b9041040f10624200800f404070305046a0b070794050081d281e010f03207501410780a80000d1f14190b01d00c5190180158801c3d10200703080303068982c840c1b800d0200d00d140c040c0c4e1900200d082003001103140d504022a01d50302110000070300041003250050513a03000324100c0d4038202100c5a40100070740e418003035800f81044138070340100e107400d40c220740d210140201410512401d94000340742035084200300d0103020700035400140d80c22400d9800e58090041303081d1270091105642c00d82c40018074450303040c03002c18a00c50041052680c85250081100c084000d214140c40c6000c0486d84165602c2044035070080c01c0d401c2003405554000c0b02640c0561443c184500010560b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 7622714 1250 7621464 7621483
    0x1d06070b07030b0604030c030305030f0a150e1509010306060e09070b0d0507050d0905010b120109050604060c021c080a11040503060414030c070f05120a0803040f020307050d050d02010c02030c 84
    0x400d90b4440402c00303113940348003d46010319000110b05d440c0640f02d1801806a45c0140c1e4030340504040100001c1a1640d42c2c024280040c0d580050928090320302070407000c600c031014282084880031111929013584942c0c00050081d402036402103081403410102140010380908105c4143e0040c00003881244880400c130b8540c45404400043c1c50796800c401260706024800034403a000d82007001640922405401000c2100000c071000c1d40c040e4980c4002d10708807050030900070b015420070b01c0000c0200d0190b40c404e0003488540d0042c0c5101495101e40d4410b4009901070140200d2003031401e12007501c4561148010500750500c007503140605000000780d4440f00100003c190609607441c0400d030410078801d4804c1e100d403000c00c8034640313519503080c504020b005005007805050000001c401d1250000b0341c3c1244c268008840500d15282c50f201c01ca1218856001030780c1600c540788001409442d0f06499005c5203010310098070300d40030340e402e00a094402c1c3c0d9503840b0456005200c0445401c0021483e440d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 7623964 1250 7622714 7622717
    0x30306030a030c03090504020403110411040f1a07020a0e04030e0409020f0f030f06010b09010e03030a0504050607060b0901060302090108070c03020d050703030b060f040303020f150c0a0309050d1d06070b07 90
    0x807443c1d03494102d4209609800c0542c0050002c41d0000c00c008070a40400c46280c0b0848040c0149548640c4ca24080e0099200d00d08004407616001c002e007121a160341c01d0300c4040744e8022840c01e0080c0c0c010554504203070340813100c00c8000c0410441410303440079a254800c40121000d0104070701540010381c2c000e4008594510911117191440c9007540c00b0804048a03003095801e50f034442d071b076a10105100d5042090311341e02256810502e502c9a140101c101d455a010503141e080c00e0030300b0401800700384d80100350212540d664610300e03840d06a545408060003001e6030384c0e01584e01c001241c0014020a40500120244400c141082d4006500803484652201203454241c1e180d101c0341c2401c40161581440c007a80040e000100c070300640940c50000c0c0140d901a0302102c501540508409a0b0342d418507519150341c64078440031940b580c0320400240103000d102d140100d104000c6444513818150b1400150022510840303001011001c0c03800c1e00d4400320422501142441900e846440b80d03810001d18600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 7625214 1250 7623964 7623977
    0x3050408040b09130e0c030c06120a0203040f0503040905010314030307080105060c0705090405060a060803041202010302090103060506031e07090302010206041b08030a08070201050a050105010e130609020c0102030a0c02030306030a03 102
    0x1a00d134400100210703c410320342440f07000070221282d41ca400c02203c00038004e005003810700c0b005d42003040441d0b80101081035500c41654070442818004c6d080508216400b010100b8a900402c008001402c0a4515404006807175451480c08611103180c198580c400d9801c24020030440d00d40015400d41110002d440c134550b0b0b4502c00784150f05003e07035a0020703607200d42070b0350912040c018005409807080764281020041e558480b50120754a01444c1318241841803c544500010352107500901003c41d03040c140400c10a4450002406640003181c881540c4e5040540c480358209414015035000721143c20500e01a0741180c00003915024001c00c05005002d04030003440780700134140a07180c001c1141070290394480304a018002e0120000351803443c01582404042680c8aa60780305160480c0d0050315440303079001005085c000c03510507000b2090401035a4032070018002da16400100031405c80100010b07601e01c0c01400d420125505101440115072047c02003010341e45000a58000072501400c110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 7626464 1250 7625214 7625227
    0x50a0e040b04021c0303020c010b060c060114030307060c0f0e0105040b07030305100312120501080c10080709090606030c0206010e010501051c020702040f0504110d031409010c0206040303080108070603050408040b 93
    0x50280744030f28103d0b810b1046130f0034070314040c594198080e12851103000d0003813244291354020090240501910340046403c010300400506e059004c3e1000d14110250070780e41004100e4580400316500c03007000c1400710320b48207600284141d100ba00000700c0d540909040e41414100a40003500e4050b0007001000e05980e000801c00801070b881c8184000c0da0b100c1b180308501c8201c0d2600505103401e1f180b04403c1b040c18403002041b03882000c0380006ea054409010090100881502210220300c0a042d030001c1c8000100c0100b02201c0d903010b150042d20250b1004611560300c590002d151860581c0300d10700d10030400005205aa900108595041e50703003a5007034103002c8854100c00c00910440b1802513015180003c5128142480d400c0640314502074140791882c0c502c0031042c42a10501580700031700040c0c0380103004c50030019410143c941c1407070624040c7d050000560209030683e009400c00d80108a08000422200104025030b0024000e10b280034000e904080c1d58148490140e4000e80114060100c3c24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 7627714 1250 7626464 7626469
    0x1809020607060e07060908030301080c01030207230309030f060c030a02090109080d030501030c060f02060601030509010e1203090606010906090e040201030f090f02030f03070b0109050c09060301080601060207050a0e040b0402 98
    0x29100c01d0354000d00100f0112a103840c8696841c00c4c0352080f10003250410800151811000c03040e6030498248502501d14a180e00c1e004400a62100382d0481340d5008100ca184810340c1240c82003041e4004070f030015a80d80b1203000806d480c01103400e840c0c0c605607000c0020010103007105d809036904006000030240c0c075070070300c02c0c01656803101a0308070380613900c200920b0a030003c1e0f040d009103040b24000d52007460311035250341003140c0305205141d00602590040011a41300d520a9001c40e502030400c00c000a122841c80d5645820319442c0243ca81007150040288105090103001e9030350088424203200d040c19242050280ca000d00d2445007a00c0452008005030569001c3c0e00305042c0c3d490388000400540f105450000e46042c50840103078001d2044141101035560000100c840c0c441e040310100600b41e00e405440b0014110090141c403030700905202c001042d032605c001030744c0a40406409000d8541c100301d0000d00e07008555000354801e5144030800c21040c1c0c0b945031510b070000d4101c40000c0c0c09590b0f40c0003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 7628964 1250 7627714 7627717
    0x150309080a0504060f0e010e01111009030e040b010e010903060507031103040807060f020a050405060f04030501020c150f06060304060e070503030c01060e0109050f01050d06090c1203080601030618090206 89
    0x58599040000e07a01406076000c03005000340c8189490340c03994099800b504540c981c2074441850301181444511006945c0070b0151034030741901c21800c880c1801603e40c2d0701c01c01e9480828044003c40e44c07070301c80c002d4a46058051600706d00c80a03e8048005000c2d0400280003070b07401c0c13002518040d500d50100350014440d40141000d0a2002d032001d03900d0a082c60114802e03403000005880c018900440075900c3c407514001c03152103a00ca40d4031281040e081c030081040950069030145e0000008000000001d0404c2c0058000c9030580d801800d00000d180780701a0000d90000e212000381061002040700582c0d401e0305403a00170350810f41c0021810070f4041e01900d09207481e00242d6040c800481e620000c440d05405c400141c981100707071201c0a0740d0300c0030b1810560f201602e04182e95601d410050000b8241810440c030a540580c01c081000300003601c03106150385154211500400350f54150005260700500c481d60401007e00e810403c0500d491840701b81000ca43c00c910319415203950210b015513660300d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 7630214 1250 7628964 7628981
    0x105090405010e0105010e0402180c030105010f09050a030803010510020105090a06020315090c04060f03050417030408130b040501030c02033a060f0e01080a1502090105040306090302060f06040e071503 88
    0xf0020042544c6680c00c030701d82040c0882d812846800d590303841440c0c980401e48454000c40300480454256424000150740b0910607a03011400c00080040014840c2e942d810f10307400840c000c20b611533407941003030144011080180d80340d60a6a040c001484441c0318001030401e58150800001a01c039103c43d410500d101100b01401a4021091018070610300d20302d400800844005484a00c5000d801e2403064003552001c450140c022000d03242c032a4180604240207540c418030403611075241c502c10070440d09140c681170704211032001e030108003880196014410020007820500055040003002290920301f081003151200c003035035103a0803405603a1b81090012400310300b0340c0404d0080300c2d01c404498151703c04501c50055010722601c00040c8480d8082950309105410840e0000c1e5446080105000ba50002e2102030403c002004000f000c2507043c403c8200462007036018200074107110116075555400600b11781c0c030581c50071151300000c110020700c08003102d01d020f0b0100600402c0c1c0d0ba0a90040c01e0b0345 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 7631464 1250 7630214 7630241
    0x907020607180e0a0f050702010b010806190e0a0b0915090414030d0f0b0a140603070305150a06020109021003110414030307020d0309060207120c060509030f011505010908060906010509040501 84
    0x48013400382c0c40c9025005190501a0900c00b00850307601c07500203e09a9000d0703644c6502040400300405c8584c00c26020b1100030030001400c64505559805641c0389005c000c4401c03440c81c65481c89049040d180003002140c0040384240001c16100320200000c1d040903021308000c0540041c500b20222485041c42591241c8268002c10840c10088100c1c000141ca43d4060030341c03060820a0340401c44608104074050350f4040606140c0c207690b501d4100fa4010500034220010000d0481000b003c0c0e55103e550003c040c0a20354000b050596080c81840740864000c0325203800d050412000301a003034850f02c155021136890541c0e4540d001710b9040428114032504038040d422400e00c1110400341034002d02501c040350000c0c0d00301c0d8016a502c0543c0d80d03052041c072100404408881d034003045014406e070060b003001c600060540e1603420600851071300b111003881e400c2900d542044010041981c01c110300c08010300350800038201c5071a05004268481346e05019080c841e00d03143d80400d088c004254040a8580c00f075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 7632714 1250 7631464 7631489
    0x120406031d010501090209030c040c0203070f0f080307050a2c0607030909140405070902030c040905041b030c0501020f0102040e010603110409050c030a0e010902090c160812040c05090702060718 85
    0x40e40401d001950200201f01c0c041d10890300b010080d401c1ca03106011100100b540a1418a00c0c01d50782d884a03500000c4095a40e1a07070143c2800200f00c1050045006241c03948945640e103016503009081c030007a0b11111a136401c1d8140601c0c1c0031492031040e280805400325681c40c1c0e034101c0d600c0c0586e56803072940c218011140c505020030351034018000760789010718051411038454594a101500580c80111143e410f610000e200070030207106e943d0021034006108021800c2442e001c102c10001844940e801940c40e50100301041120356014440e200288882c040258540f500340780384804000e0041c27085d0020103070350300380980400c0301070003e031030152030568824030660038017031601070980c1c00550303420500c207191015088282c00c051090504566019144000170f55482100e207003d50440070f546c101e44400401c540000850002c0100b040b40d0181e05142c419040c2810151505a030b140c0083c0e0142c07148070140000039070002244e651000380b6203840000c4d20103807081000c56013255400400003100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 7633964 1250 7632714 7632719
    0x30108030405010806030313090b0105071401091b1a03090c060406020105040201090f140f030c0307060809060c0403081c09080c0604061a0f132c0609120406031d010501 74
    0xa000c00204116030090781c3e40c80c1940c81e074104058070303803056911509500b0680d20302000340304c1e520b40140c1241141418000d0400c64143c0350b0026840c0c034031a0f8521140d54580100d803c00ca41e10f41880003017214480045000e40c10070700280311005a25200a50140d40031000508a00342000783c1e00030303004003400160301c039a5a100041c8c06401d0688040b400f081c5900d0f0003107400703001d20760b22804942c040031300345521000c2d000c00e01c0000c2600d0301c0001e8241c000c0305801c0103545c90401001c0002c004554940400740b1309200b21900f0900b016260001c105803c21081001c50305403002d032840034010940c200c41007501540311500510000c00020b1031200049103240d50300801040b1a44901c0c002c20301802683c50003501c064184014001082d400b4421b03c50f40c20b120306103815000400e0004503c00079008024541ca00c0b05548415141d8152151036241e151031100c040c0406a000002580100005410b4900700060f0f4007a5002e00000c143e6600510709807001c486280c4911244590002c010a58 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 7635214 1250 7633964 7633979
    0x609020a08030d050106050306130b0109030209010f030c080a0201020606100207090c1d0406030213020a0509030a050a03020d050415050c01021903060501020d0e03061314070e0601080603010903020d080703060b0301 94
    0x200561810460913107004c00000700749008004403881004c00405240030581c2d41403c1000900d001d00000741008401e000c0031006840354810140030300030310840d4600ca2859460100081400703508200b015402c41c031015030041c0d03000a40c407608145c04a541803c94481000100e00d4485c1030b43c8000c04081c1010f00d5000d506811140412940c0e600c521141722a4460405000648a40380f000940041400a66004000d1103034091701d205510751819070b03e841c7c185400286401d404540a80d4160404c3c2106020036804010740b000c41c08003030800c42d0030f09140041c9022403120100f00350041c0800095101c0c0c42260a50450300701e2200059280c55000088200a0003400316000c0e1902522500f02e040803114004c00400d920400000c00618641e600c1e44190450092480811a200b6034424059a1200c40510200c07000c1c3c0015442c44001d8609030000400080010303002074000c0c1d14044810003c070b0307030104102180d072145c4e041000c260b07103455000b1001004c40b68003521224030003100124104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 7636464 1250 7635214 7635217
    0x2091909030302120f0403080109020306010309050f03131a0906070809030a03080106080702030c071806151206090501030819050415080105120d0912060b0406031406070e010203090103090609020a0803 88
    0x21841d0150407541d298080c4c17078000c420507103000d00400d083c6c100403c20004503400841d4419018035001c500715441740d6a05203002a161014586a0404201c4034044114602020b004000c44880ea1980588041c40b4400f1882980075240c014800061103505102c40c54086480000b0040d04a418207075003404c00403c038410030700074680022003100100c0e121303506c00016250581995405858600d20381000c1c444800f64007446c10503c1030320f6000018123032184007a9800c43c03400310b490761200c102e140c0d030320802201c810344c01c1014120300c0c0c01d00602c085020720b0251181c900200b1001c1102440d100c10a641ca03001d694001909080c0308400168543e034458120380c102c501c1a01c1c01c5610148040c042c2c0d4603038000c41c02683c00204030f0601044203054107201711500a00409001030120320101c0400e050382c49a40040ea800c1030041d2244603020300400400340d10807024030381000e40c0040b0303200007512845011586410191114940c0050003420750150b61041d0740280fa100303200796034072159a1079 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 7637714 1250 7636464 7636477
    0x20309130b040f0b060909060f0405010303021c02030a0c0206030a0906050702101401030f0816050d0c050d020a0b0601110304091d1608030702010302030a0f0603110301110f0702091909030302 84
    0x42d030074090351000d003200c14000e0515150b030080020341000700d00018401d0b0050000e0116503c09070384241201541c80c0d40c0b1405010358007a074040c014800003100007620030207900c01d0700821588104494142a40d0000039984030b194100d40050380da468074000300d80541008035016203603c1c07500d07040c05421070300060742507042c52104206102c0510b525001800d807400900c4058000880b1584d4a00003620392402406081c1201c0f10510207190340342c03500c4d46011980024440070460b00c1d00e8080a221040041c181c10241c1d0f84010071140502750790340c5c0302c0102c020b0101814090100d0451a21000510aa0f400703840003030030402100000c1d003450080003c0030f80510740395000b50010410043c7e031000c0040e064503520b0005500d0605683d00443c001d501c018540d83c11a40d0301c03600e401c810291380c06880010340c011503035040d42034100d5003010700315220f4000e1110101c50070400b00710030701c00000075140c909404880142407a95400c40b80c11035070242030641e0003e0351400b54000c00b0560164003815a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 7638964 1250 7637714 7637719
    0x140603010b010302040e06040209030f100903110303070917010b090c04060809030403030c230109050d08090c0306011202011b0309031b060206040b0406110408062a0d020703020309130b 81
    0x50020301d80010b4049208501078181280300900c00070362182019001403185404c00b408981c01c626421218134144039614070780c0c0301c0b0306448032603210605600c500c00300c05405010020754074505140c130024005801d5482050b021440221051590342002c0d40007000007840941500c1080c0303401d40d50000c1a9019009078004142000045245400004145c505481d8903807240101d180280e103480301c02c0b0b400044030364000031480c820100d40c854207010301d8140501c2000141401e220005000d090240010724180311a4418803500c500c642d0001107843c11500c512100001e0482e10380012a0789484810010600e4881c1d440083d04050f8000050030480b8040c01001c03003854542a1444d50002c2244140d0005a12a00110700401c464034034180d0824401d09000980140d0141c120600d42c000b5071003040150003100801c00c0f002c07284428080311001e046044012000003019817030389070240107001e00e40c070307603011441004250003003007207802c0d10200802c0c92422155a4404074050280500c500c1d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 7640214 1250 7638964 7638971
    0x70e01120302060a051f080309030c01022103040f05070e100e060a06030209120d020d020106080c1f031503060209010e030c060405060703030603021009030212030a020303161214060301 81
    0x10049860240e003003040d541035000d400580c4800382d0980240001811900e800e000349241e41d00c00c14140b09040b0020499503010319217408819040506244101d010b0605540088101000d1480092030b41ca002104a0000940725113550625040115184100801d17601c141d5030f002c1044162810030b580310320840300c4c600c414a40ca40801c04100d0205aa5131500000e805405011180c000d4016205036030014094210a00c50044200e150034283c03144080580c106003800c0f51010b0342800740c0e10181c00b641c0024440261800c0129400d00d4a114048200065072500c2c142510312a40101d206101101c0c400212192282012402540078610090103e507102c00d80313244d18100822807021110300246405d04103803511040c07210a81c804c01041b4100350b0340d80c6004c80182e07111046540c000e041a83c5000c462800c51050080c00003540e031b8040c0c40f5600c103205008000da03000084035404020060070142240042000b80d500321105100790550604015030900116464003841d031103208210007d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 7641464 1250 7640214 7640219
    0x8010807090c051602010201020706060303030b040b030105090d2001050403020c010305160206010302011b020a03080403061103160302090d080c011e02131e120609050c04110304020103050402150408070e01 90
    0x1c1c22074107190800c8020500c01d000ca091078807000f00038a0200c0e40117000152078002d16036140702c1210015001100820380d1851140414100b0784541074039104141e0007040300e810309042c126605e41c0c651203070078100144020582c80003903031002702211001811009204038205407030003039285c00080c4580c5001034580000039411004a9090030400c0d00750b5009003002d80d0841d0011640d0307400040f84507005200314906000140c42e110781d000300950203104820f454506520700103017030341d00c040c0e0306540ba44010310511036042c0c0c81c0542998003c4003400d0040e2354020600200f40f80000412018240e030401203055070703c80078103410039540d603039000203284e500000c6411000200d0150182250540c109c03e0070a2041903040041d4448880e110400c0340383d5142d41c0c0d488104902401c1204a862a840702e42039030400c90100070185442e4002c44013406005400408803040b03000003000641016111400300341507444070450140c078860300c42c06440d6226200e544090340c0c4c1c007641c89001450320054000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 7642714 1250 7641464 7641479
    0x504080d02011a090f061504150503090f060103032a0f060906050a0e030702041d010501060903030305150d020d0309030203030307030207050f0a08040b0309011b0e090601030b060d270308010807 85
    0x111446000641d0404c50b1903210f40040c807d405c90603841041a6a0007008040b510205070f02421010341290b0ba121a601d00d81072000c3c03800c060521f24840210b41c40f00e0010b0000a81041d50181c003481d07480b00048048500c00c007034200150b803070f45014121015000400c42401036507001100d81e40e000f80c1081c042c6460b400c01700c0046034044a01c3d20323640d801c144145001480c064002341050ba4a02c450001119102c03201c46003111400c0e0710141c04150484001c00c02c00d6010300465030712100d41a200312034994044003080301031000d41e100902c1800d006482004060096541c0e40c050354028003100d4591804510250096000d11415503051181080110320b04a0001c0c54030380076a0300c45070036424145170200300305803a04047c1011803295200c10000c01c041c50415102880100d884d60303403403c0c2260301e8041c41940c0b00e0191500b0304040c18040100120f49801d001c885082007c00e0f00042c04000d85040b2181d03100155449000c10b4071120000d1040c181d008004c903041e500d05400350f902c2290749421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 7643964 1250 7642714 7642729
    0x204050108100501020d0e0307030204110703140a050307050a0203070f060608160302031e15070201060306050601030219050f040b04030503030f0c03041e02010903020301021b0c04091502030402010504080d02011a 93
    0xb03011300680c403401d00290383c03901c101d000007060000501154491610b0358005401c1c1c401da412034110120001c1000c20505901c21020b0210840e0300b034509260001b1000000d000c3d02c001000d0300d0900800255030401c1c280b08000b182c01264020ba4900104006454a080a03140c544101d000c90f00c60b4641c8000b07a07444c00c168035000c881d4003d0080c10106050b403041110242914424406405034010b28a1800c0d01001c1c4c8170310500040e17000007902402d602c0c0c140116a4040c0149041500c1840030b03d8252180e118503008040f00d90501586400000358118101c0c45240c20420005001103000000c001c0e000000d18092410b411910449541d0340b2203260250004a9002d0841030410640801d20a140c00144001600603d0003201080c2c594021a003640c2c48030002e000c00030a003d0005102d0780050041e11041401150f062062030b02035121107805507a400645c118a40e0f00002150844e0f0103030084400a2403160f050300c4020700c4042000c1d000300049401200c41c609802400d00780b5142204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 7645214 1250 7643964 7643969
    0x30603170918061516061b05030f04080903030406110f0a02011d0f1c120801061202030603010e0d09030501050f010b07030f0c0606080c030c030d0519020a020406030303020405010810 80
    0x1d1000b000072140c800301c00d49500d405481d203600a08034015480e40200c2a40091082c0c040f080a05c2c408009185400000c41d4101060403a5040d14040000308103039000f000c1b81d07000b003207050f164401e44d11141071880c524410501c0c40d5515200c00030f0002141c50300610040c4c000007121044e80c000d49009845140c98540300c82c0000d0000755030707009004280500300c00500c241d0401402e0b03035082506140104030028940d003c20108548081c602c4400c02082d010391520041c40c41c504034076a9450614080c006205010803141469004000203d56841c254400c00f2400b4180f03045900103060b00001900594003800181ea0b19403d0100244043c0098030b2164125001600300500d40080c41d1011104550302160180421010009240c0416860301851010f4800c00d0003922003040c2c00302c00c25140000a00c0c3d110b001c0c4c1c0080000e4250b15070004c0a440c0c1d000343c5c02110035000f007032441040b810032484160095005141802c007000341035065004e00151031003070301e61340034985500d40003203940101403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 7646464 1250 7645214 7645219
    0x1020903060408070f0c090b03010b0102070305100f09020d03050403030908060606070201050307031404110a0e0405030a0e030f070f060305060102011b030b011b050303060102120705060408160501020a0306031709 93
    0x46002c200003450280051416074013a41420030400403e079122104e041065020078501c43d143d442d07820741d0380307000c1c4158200070009000801202d8030f1903440d140c03294680a060020140d9803409035000c9680ca030010040d4a9004240840c000410b1501030140c1e0810701042e40059140b18002c01d096100050305401143d009100b5401c0032000d41c01180c5640c40149100e0030181c407100e07082c1003018010305550003a48180078500448800200384603081c101070f804040004510300c14400070070310200455030001180c0ca441e408082c070000204e0b24152446441d5040c600c0b40c8580098400c101c5041c40003074032038950b8107102d540c9407040120300b603d951900300350700c10841000c0c0158850180c0d029802c03a0b42d060416014900e401200d4070307503070300340150262600e03080001041115a814000e40000025481006042c409291a503940c2c1c1c9200900003012801c002560b1a21039120316060940c0355413100c0250759643c0440301c01405230256200c00c9030100c03403051038070210540940035030303020710000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 7647714 1250 7646464 7646473
    0x90703051005040804080d020705010206100605090402090301020906120601020d05091e12010e01050f01090e060a050c070209041103100606050d09060e070e070801090606080402090a1407180801020903 88
    0x1259110002c0901500c21120300c80100800180800140520b080c054001d402a044480c500400a401c00d04014000380701c0054001c8140b04031904042560b8211009607001a180d04100011034020311239070139010707406030001c00c60b1040d0b41d85403001d180c030a403030a80c250760151075a594242d449016641e04c9940c0081d0050781a100c204560441580c400c3c8005d00c03841034400c0c2c0029003400c417840c0c0404e1400a0b5180d0080100a5188907100c500400640303c0c20010a00e041410f25102d4801400351140c1540f108080760303401d401001501e0704c4a030010461261401c05240035131079183d244000e18041c2c041d200001042a1440c420034040310b0980e01c829241a0329a551400280044a400c48a555644040804001c0200020760241c0038513010300c151401d0902c4040c1c11940305900100c02141410814803040c1d85c0700800366085641a6240c216640f10302c400d0360050b11000b030321000d04141080410491717651003290000070380000810211030b42c2c3c841c000a8240d00c128a0100d405902 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 7648964 1250 7647714 7647733
    0x30106030803070804020409080307030e010e0c060703050a0c08130303020c19050d05070306090803010e0a02090a0303030207021809030901030e03030421020a06020d0204050406080c09040b0603010213180509070305 94
    0x1341c1d40701c5038450b200400000303203c1150317510f058032500107450090009a885111040e9120b0900c2a507000301c0c041301c004c00481c3c204100003041445414001010002c002c03401c400b0b00390190304040a0290320200c8151240d04a58076001c0208192100f60f00500c00e54031008214200504091100b94200d0080f0302c540b4181418406040300c00c0070105e65a200d1303800d000000c1403031803080802d003d10841c03031580d995140c00007410b0102d0000e807500c043c00c2e00c1081525415941c48400da404c03254141000b41e2580e0b03003400000e0250700b440c02d400302c03401d25a000700021040d0110042000c60b000740c0302009103140306190244e41e800203c40052070340c00418410860703036624a0a4000d040314074411224081404e9841e44160b0700800d01080e0101d40225090100745403500501c80a000314500500c0b200c1c146100003260b0000151024240c22207800220740b8a490070340469400684501c0c500e28561f94440320181c40a648510002e0307400e24080200300b9004c004110313a411a900580149103016 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 7650214 1250 7648964 7648967
    0x10b07030801140126160f080406110405030a110102070609081002030411061602090a050c090d030302090d0c050406050306090a080c0312130501050106030b1011030c15041103010603080307 83
    0x5031256a40e414017403140c0c481c212840e07100c6180c0c0d04681700b00c02c0402c064100704001d80341c0882c010005a09200203140c0c207080f205d501205a035405a000400496030443e5842118000d102d40e0300080e4041c000c3c022101e0911240b1b282d6000030903002e80c00c03200c10355075a0200f1100070b2054010707030900780c000d6403443d03068010f9500a950024000c40344e02c040c03408140d00080c0e49a0190003c0900a00b1501410065160a4040541c8003d00d00028000b92500110b141d1003071140c14440c1c0d110302c0c070070b0181c5403c0c50311946c152112000040c10410f000e9015007025806290603205e420321a0b810020f02040d1824046034060151800e81d00924a10486580c0e00c1825045500303104010300c01440500d940644080c4080c0c09941200008840243d081c04d080307007174460580180d4181414010413011a071281c40c0c8921100143c2d14004043d007188a999504601c00c0101800d40351040b02d030980b052110340d24510340a43d20030001c1c20355503400e00c02070500f42c611505c00a400400140000703104a03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 7651464 1250 7650214 7650239
    0x2040605040b1c090f1119060815040c0e03010f09030203070f0f02180105040b0111120a050d0e010209030709090f03080406090f05010203150a0b03130c08030307020309010305010b07030801 83
    0x510038110145055410164480304031800304009844110188a07205c040c800101c0841002c01015907100c601110310b405581c54100c0240306400c100301a11001480d01e11200380035140c2400002d10500400c070304031000802405000004610a51034070340040310582181c898050110f6140e00914144910f5441d07a10382c0c01070f1100d003500d4100c1c0c886081c3e401a69a00a44190500154222195541060300344400c580032030140905210700e50714610001c003000503018441031070441d2169520400c04008452a001e00707800ca52a40e401c000150b003039014107402a0402200c03c2d81101c0c403241c0d99400320b80c156a4201809090701d220300c02c0e00c80119205002c2258464001d400105201d250350f5194001d1181c080d00a5410313075800f00601680710b880c17082d158044101200c9003099941802c403010203070311020b880c02c004000c0d243c6450080000d05542000101000300c142c0e6220b02d00322001a440e5404840041d0002e881c000011170151540c80503180100d4240d80c1e50000c6c0d070b00f03152458484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 7652714 1250 7651464 7651477
    0x1202090f070c080a050324090406050603010906090f030206070906050d0c0302070b1003030801091505040e0c031203060310050112030e0303090a060c0506060303040815040f0206040303020609070902040605040b 92
    0x40010724682c40c000b2885040040a82403559030b542c03503032482c0c104001c0301c03e00200d02c609010340c48560040096541e8400c50250080d0308260001811348030040064010151040001d1209042c103029005110350056011744042c0250245c945555404030101e036000e0b2680a1070010400a00c2081c0d030354107a540c4109034298076070500602c0c00740d042d22483c0e00107204840120b01c03603108a805104165125500e14010070b0034003002d01110083e82e0103150060382c0c0d806418029a0303030700c600c09010b000402140c0c810a0028040c0c401d00a241111940c2e96441115090300074840c86100d101030b0045403240324100d41100807190990540340c1c0c3c085035407241c98220300e42d0600c81400755036410740c0c503510400002c0540d41c580055031002c43c074046041c408010b210301d105c0e400a110406c82e243e004038010b100340e0803056000810380e503580f4003c100c90742005001f0303410100c04900401015000913110340500c94083c21038410660341c21403d0301b80c0c40786000d140c0010323805000c20082d64068a010780751 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 7653964 1250 7652714 7652717
    0x906031104031a1b160201080a060b0a05030901050609040b0c0a0309080415090504020c060c070c03050303010308030402040b090912130806040f020108070509010509060904020d0509030a091202090f07 88
    0x7800e980c0c2e454890341032920b80d0490400c1000642802040f9035140c250400b4601080001410012954002180001184401781c1070100d0300380041c04a480580c4240041c0120380c0c03d907070701c030040c0040c001c21582003140c65440300d41c6804d02103000c0b4035009000611880c0e02c05c0481581da82d83e40b065040c2a0002c00c00c01c0c0c103064481684400140c0740002800141c119046110004814940f000b008030b1280c4d44400e009501c1007010f4001300c500441c90561001c5400503066658006140000c981e5101e90701c00703001c0f800040004000c001c0c040001f107003d5030003150107224250415040210b00c800a40368000345500c03801949401000410240040a94400d11078111035600c034020703400c01d40129400c855015807d4404821913030040c2e600d507040315107850001d042a44810001e0800d1185991061003140d0100e00114142e0300c80c1c044984208119000744403504102c07000f40c1d41d07034000b400e0001c04260248030115010b12400d000808280d0000d084900035160f1451000342480b01174038100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 7655214 1250 7653964 7653967
    0x1030207050109261207030c0203070f110a0504020c070608090307060501031110020303010f0b1c020d06080709020a08060906040608030406090e0703060305030703030b190306060e0601080709060311 87
    0x10041602885060f21860007601400344900c4c2403d00c5002200072a0307802261070006100c1035449513980c4c03003441e92100450030001002c1c134100750264950300601c1e4009110200c3c0603808410041925407094042000752160b0340455281c40410060307010342d8a1850703441d44100070800c41cac80d01c500500b40e04150303c0d2051700d142c80d03540c2e203447e42500c7c000d070400e544c4841008554403050030001480350500d112840958215410300b1b001400d114002d1141d401403c00c0400d02c180350314a03d00d944075005410030300442da0740070f03401c00c190007400741407040311100d0090103c0021600381e11300846034601c010b55102041036540600300902090003500803508950354a101054440080006001030280ca46075207850620b0b20070783c4c11038004c0091044040505048040000607000400c2d14001585401c1c08038000c444c1c2c501107000b07000d1140c0c8151000007903000000500070345902c01310940d44c4540c000703842980d0f400300540e4840400e4030b02c0c0d0000390180b102041200d1195001c0705903021103d910b00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 7656464 1250 7655214 7655227
    0x2010e010e060a03091118040b0a11121906080c060c070801111b0715030515090a06050108010b070209041205040e0705040512060108070b0c07080d02010204030b0f04020901030809010302 82
    0x40d882e0300b101d05a00f010030380d908075102c00d0054510381c03d15181e404507880ca103410f8510342c24005004015000614910040001c64507400c4540c00801042d00d02c102c2c2c04e61214a8060341c44100f503002d070703150b903184205041e2000820030140520400d45900c3d00082c1601401c0c0030030b01000e9401140c40d00c00307501880c0004102c2490038000d4403981245040720540b2035604001c42906e04002c416000c40f158810081000701000c041a008949070300e5041c0043c0d180c0d1022946592020f02d50070b45a800b55610040003020300c0301d98003503c15a00207998041150780c880041070707110302c80e036800079600086a02c0000d000640c41e0319100395011903890400d0600e0355505803295000c0042c2c8521f4040340000c10b003071000741081c00c01c6507201030f0030310002d110325450546c000e038541e080d502480c0703414000080d411400c400c08204c07410092411004556010029580090007500300380011115000d8540c080b8082500b4001524000c0350018038111182c1d107540e0700c0c50055400004a00e040c1b41e0203000b031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 7657714 1250 7656464 7656469
    0xe0102040902042102010806040509010902042a02160b09030a0503030109092f10030603150614010206010f050103051308070c0801060b0c100908040503060405010209040b061602010e010e 82
    0x80c20007040598809030b00c90b400c0c04d41505041c511601d05203044800c203581c00c40075030f07840611260000c1c001c0c0d0b0009041e03103840400b54054011204041d40283c01c0c00c15a40a1106541d4a052240f403050302e0039840465081040741c407484400407040300d80a8030f820a00000c03c911004002c803000c010112605070720700d40c0da09400d50b0000da0102c182d0325612100d1070306000ca120200d200509518071101d1a020000d0030030f004403040e45082e02d010b00c044034013416440307000c6e501c604c000d1500300c00700748216aa940807210240080e40607c0d01180041c0c11504855400007508505031000702c01e007040d4075400e00300110001e01c0010040d00c0040f00844034100484c0740000140280c60290000c0d000c540d003000c12450070f407549a4040401c5c8a4104204000c10601041c020f5812400480c00309030100d003824488494040c0e904540d6040c01150188001c1000560041400110a80e020310480ca0041d0070004a805425040200c00c08401c00f104010362046c416070705143d074141000c41240000034003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 7658964 1250 7657714 7657717
    0x90a0311010201150902040303030b0a0501121a120307050c03010501030305030403030c030204180c0809030301140904050703060e03040806060a060c03030e120c07050103051b0406050a020f0d03050708060405090309060d0e0102 99
    0x1700761501940001c0a0060640c14010700c80b0030706090300e144813120700d0080002c0940405505908900390341e02d44685421059840d03401c0c2c0c04000901c4805c240d2181d110080e05c03a4040c0c1402c450b00c1c442e03840310810505043c02034074100e0303805489180c20750340c0303603241035010301403607010039041560130031012400c0b5100107100c000f10032040b01c0015a00281c0034000d041c40001801d112080d034824001000300c80e07036482005034080300c151280f0009480c0c03031130454900401508000d002c1030501044a054030000009003080f6400782040f11030341d0311050240b004510705070250a000554031a42d82e1f01090003070300040300b040c4d40c801c111102c1c074080d04141083e6402c041009d8500703130030000c0100001c2d070385400b415401100484001003c0e0351a4903e05241d84581c1c03003041c051150125030a45d00c83d00911400010130000d030180c03100c600741c580c8010010042119a04040751140300814803034103003072285c103104441100080d0702d8000d642c41001070315000103100c1c070f41c8a52100245c04c0000700030300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 7660214 1250 7658964 7658969
    0xa0e060408040915050f060a030209060d02031b04030308040201111504060213060503250c06050108010204030b0a0209030d1404080a0b0703061706070503070905061303030f0302090a031101020115 86
    0x2169030b46a42c20300e500c030030a442e080108414500201201444203a070368440740105890203c400301d6036800b0b841416406805201229a40b000021403204134001290300214821b40c4001302010304803181d5020000140580d020140c006001000010010b500911540700b50207010303c11503c00c0c92004907880d0146400325800c0381e550b0340100e20300d00e010350f440d40308101074001414518210300c0d0401410b00d04c0c4c07400071401000305488442c03409900d0301811303010f00d00395040a030501040d03840c0c1c16940e010b940a840f04690a1002c10001101c07903070140709442401c00000d001e4042020784107400c0300d500c04203054500c1c0292040100082c101010000300c40800d00c200c06803d0319180c4540e018080b255107601c1803010003140c284012009002082041d4410000e09015032281c54210040710580c00f183c001030340040c800110242942c10700d100d0310003140e00c00daa0700c400822044800310103900a1120903504407008034000e20015103c4131440d540144180300021350046c140564440d49191035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 7661464 1250 7660214 7660223
    0x1211030405011e06031707060209030601140306070504230406050301020a020705120c06070b070903060f09060507110309040203040219030b0702070806010e010b130510020304061206050f0105030a0e0604 89
    0x3000340d10080540c3c2c41d81e00000f404009402c200080c51034480c48440f032501344a40b41c1c1104001103420400c03150380d058030a01000502100d43c80e40c0c440ca40e0071803564290059910038400d6900061001e03105504840540d10107140b070b04c02e1468041004240c14080c0c40301d0741e81c000e403103090220303c81d10700b44017502155860394000c105842c40e1400b88480403a810b4000d001c07a4000101034034850302d805048541242d4040c2500c9000d984018040342c208000c6e40000304109e040c84803032000c6c109540c02295440d80118010000ca84404e10203030380202c000c0c140c0c0601d03a0800d02c0f003c51b4514250b0701450784a4000b800001c00001041070f50214032019400032114001c5000500102d1941088500042d05101d00140420750400d140103040880510881000e000c3c005843c1043c8080300032598010300b0054142c100d19101c0a0000e51213030094060100094076040141c050744095015003803c45030081c01145408441c4001151150301c000c015440342c540700d40d140c8224840401459105a006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 7662714 1250 7661464 7661471
    0xf0a0c0f0605191104060e01320c0606030609070603020d0908030108031e0307050313020d0212060105010f09030b0402040908041203080f07020102030907060e0409080f03040c120b07121103040501 86
    0x425180c3e421148030441c107503000c68040c0818807550360044402d2000170000d0800c4142d0980321001080400c408021660301d01c040d48030301e602d01d80c82c030101601c1704110300300c181d54440da620b409055a440007140d007034065034000c14040040c54046d0f8010411400c190a002c0340c5c0124540b5000903e500a03804103070558400a07c802c0440540c00d07008030407a05c41c1c0341c10b61075030628900003041e27804080c1510851807001e070212011036484050000341d45a029041b0003100d40502e00e459110700c402d1040b07501003a9054070501c0d03101e10491030a0242ca5001c920314942d6110340e0280f0000b806074407012120408100b1006c0307401d0040f0781415040c6e0b8070a0703035408480d1515440b1025524005083d00f825a801407003401b11505000c2140001d039030080c0b4040010b030303030780600050117002c2e1100042d20043c000140701c601c207590440214030860007030700c03407401c2a81e035280d04082e0482c4100e400b0f0a80c1543c980403c90300c9201d13441403504240303031034004115090040c031298000da20548088030b090b0364 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 7663964 1250 7662714 7662751
    0x30106080c01080c0a121503050a0606090501050a06021c0221130b030105090610030b0607030306030c0b070503030a090602070206030702030703090803030603071418100602120f0a0c0f0605 83
    0xc1c018603e50303000044400c050b0421070142000740041050302d640030350064807400e06001003d40b074a00f6200540e0418101c2e20340508505040c402012180220707804c2c60306010010407141820000e42c006c8400a500030304c0c106405000c2000344600b600c04103000c5008422040003200c3d07030803a000c880f5000c05040b059584042c1c011505030078001b64481a00768505200401182d6258922039911000c260b03000140b1600c102003c41c010091402115031201c07003c102c1000707255069120005403449000740d1114030761110406203880c002c24900920079403003000001c0d00c004040d000400854442e0340d0141c02d01489500185007900119aa00c0040c2d1011801030141a072002e000001428054003035071450420b080442d44400e458050541c252081c4d0f68170181d503031100d0351026100481c1c981d0303401590912810951121600c0d2207520010321524040300c003489902011074000203030030700d8403519102100c6009d0707942e08550501603410080c0306844002090390f501a103403240d07142014100d43d450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 7665214 1250 7663964 7663967
    0x4120311011407050415030c090306020a0309060513031106040507030215070506010e090613080a0f090801050403080711010203010609060c030c17130603050609010e040c090204080c010f0c170c0309030106080c01 93
    0x8543d5112402058200230700c808055820103d4003003035a4010b0f1026a56515400d401c2e4090700d00ca0324020700440c0741000308032070080428103000071140300b90754514a0903035441030590742c3c0070300b0783d0b0182841e0000001007006182ca80c403000400c1c440b042040342005450303124542800b034240d1025860005010410050a00a200065220b007100704410040002070725200303d1401764164650901000301d1b4061203881c040e41c100c10040182c0700c02409a49081d02c0c0050080b5010707035101c00841c201401c0d0000086041c001e50307040c0c1d0308955074081c035a4a4240108d074108035040c01541071268030a1808045840a9180b43e501c14903c800340c0d070360f580c0c140040700395000564414070802d803524051042554901d5143c50450f411401e44070307a180c0319030800c00c050844039441030080f54800900003441c400040b80003800004240c90341050a102c107142540c0311110f807a002802010390302901000c6c450620701410301c0700d10346400c80307003442543c00210f82150000d400880c0d070360344180441c2020390f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 7666464 1250 7665214 7665239
    0x4030e030a05070e0c04080a11010206060111100504020103110705010b0f010507050c0607140304090902040b0411030609040302010e120d0e0f06070507030507060f0506040c05041203110114070504 86
    0x50806400a10260140d074860640b00d003041d004a48030f0710010000b140c5650382e807009850140114034181c1e0354292542c5415040e5034030216004d40076004200014030551300548031540c038103030244080e2407090410701414005110040c800c0b0b0516907503941011071000c2c4075000e031460a12880000980003411b034100310021140c02110b41c1000f40400c8000c00041c4040782e0101d9601050b280c050b2694505e26016518080303004c0b0b03c2400e40300c046000260811107800c091200b034001d881c200500320300c0324140401c3e80c2412005400000341000441d821f820070348000d44d4401e020b0f1000055140a02032151305001080d01e070040c1015010400e1800d4100e944500da0420000c0b9004168500c4411601c1d51602002000b1f0410b0000c00301d11003040c140108110742000758404000c0011150402c841e04c003c02050703c03494000c3d40781c04000b10340e040c043c0d0100d90130307585840307940c8103106956581100c4502c01140d90008554860700000c1b005052010ba445c000d01d529250303692105d0500e0040100c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 7667714 1250 7666464 7666487
    0x40602090109050301020f0d051003021008070306120305030402101101021602120c010c030f0c050706090801150602030d0902030a1e02031603020f10170c09030c01030b09010b030405070305060f0403 87
    0xc3c0e4810050504d07c5400e04080b1490b440301500046a95968611100c49010150740080e4010032036000040c02580d00c645128400c41c03094400b08489030721000180c01040f032480004002c180c2c100085400f510700100d5000540c3c2c860f18000140401014190b401e9801c1004620b41c0c501c100350040b402c61410302480403c00da142401004481e90190008000055402c1c015050105203240b01d040c480c070408040c40541d400c5000c50303001c1940c1d580c0003443c3c00e030070388600b84541d46072001024580340c0004e1500102e0f56187e0003542480b07280d160030001400c0d01a8126030600c10403564800142040c0502c12050102202c01e00d082c81a81c0141400d01814548110500003100c0050005030344011000012241c02d071122880c0358114401580d640d4460503507000300d505581c04000d800003011004250061064059590100361000150140c07101e20304115444801d50f0b0040c4800c6580320040d5034081d001c0d004942480e039403a203a4506144c0306999044801c201c5600300028150003112080c00b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 7668964 1250 7667714 7667719
    0x3050708010c14090405040203030d06030302211801030203070302070b0108010506010e090717070908060906011a0c07090c0318031206060c0b060f0a0506040e090f0604050a0809060d0504060209010905 88
    0x43c509007441500e24030f4401e00f0f89042c812540e0b40c0104082d51030800c2555420700800c0010825551a8140a540c45d00039840d1624000700c0e5185400d07411120b42c040c0c034030101e1414074140780704c2030200054020390002800c00c003c146c0d003030051202007110b41807054003c0092600024079400c007440018113303401d0413050341c082d1005c0300512100c03681c42408a143c0105090340d60200762200c4908075130000c4180e0140400d882000140101c01c0004100d481c1224186040d004130048171a1444105020300210fa1031150422481080604070b250003401e1107040e5450001407030218007031014040080f56000b5000104000a80a44d5049a201c1c00380640a18201304600c98000d948101c484400100142d000d03412051190415407036101454002e4080245016111788e22490403510707a00307048030024800e1103001052400d2400c0846c515002c0c1d42c0020103890200c455848244d1160302565416804c21802c01c0700c105410b03018810540154032039907001d07a5582c001d000050003405550015071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 7670214 1250 7668964 7668977
    0x108010c0203030a050403031b021c020115060804210906020c010201090809040e010b060307022505090402010f0e0d030302090405090d0e0f03010b03030a0809120301032609030703050708010c 84
    0x614858001003500c4d40403600102c0441e21740e5032890101c000e0101042c100c28140c1c5094105100c0640106500f030001c150b00c03e0700716540d1f25404040b8280d403030309903811640c44a44241404403510032541c00da0b0290240a40d9400320303114a221407010000c1da0300940018181c00c800f031017115410310410352171040c00d2000b480004443d8664000601c03840042034421507a9603100d900c403100030742083d481400000c0131075889190404000c0d4035642c5404010180c01103c090b0030180f504d65034491002c2d03071805081032080b07544650054401c240820800c0081c46031003030800c641c0d65145100400520702c80c1d0b03070240e116030420381400240d590103881d4100340d82142140c0c140041c4e0015000394030360412070303200141190040100c3e00500c0a20703062a007501001a2101400342c0120401c0d009008040454810070b8980a951140b4002030100514402850503001420003090540304d400b09a0098000e14104e1040002403a00341554802c5482d50440740c8100f000031002c0c0310310415101d050a020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 7671464 1250 7670214 7670231
    0x80307030206130311010501080c0f06070b07050f040807030f060501140d030e0109030803130b01050d030203090103020d0b12010504140721060902060c01050108060a14040204091707110405010801 86
    0xc0d40b42d10009001c0c0348610040032509041c5441000b1100c800075468008000d40c0d6100e0010b951542d030034002d05809540a00300444950814404942045d50070000b004410744030326804941f20350240d010b5a0b0181000e0001062100c000d003c11401188100c0e0600c5500384280750050035500305902c1150340b80c0d05030007808001d0b12901e2a0f01484c0c3d030b1524000d9090511600181c90012603900050034074103001c01000342900b01800000d585030b000304c07030280140c2e91700d03420440319841d01e203001001a00240b02c00503195000c1d80180c40100583c22012800005100100c4c08404000040510a039103640901040c008041c9140d81c1d40c068000c06000005d060480c506d24244025010340d504680d140029402d0124035400034240c44e50040c0b400d5600c01c844440c0d607001c0d141c06c1c0181c2d00140128000314000245030b1180c0c0c004100d00900070b8103241c0e259000c010040031100c8068414160209411040055140040403c1d40c8140c5004142401c01c0c1e05200803294140c11911050b0702d0308020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 7672714 1250 7671464 7671467
    0x20c09010e070e03030c011104090b030106080307031d060d150501090614030a060e010b04030b07020601050d080903070302030d03020409060b0301032402040504060b030702010515151b030301080609060108030703 93
    0x281c40d803001c003d041804221846101007865803040540050403540b03007440c80c8800a1090700204100c0e64481c009000702e880c40d204140c03c84420f84910003150b8000c10400c00040d009110201d040010140035106501142010404907841a0442c24007541e5415850314025551000c0d100500000c6c42e01c0004c0d541400c2010f0700c81c60072181c0c65a644040070002441d0030704c0035004000603004028461056503551201c00310242c01038001190004808000034016500c00104541241c2c4000d110500740b21694403035841c550302c010000c039018082c003c00400541c03810410407103400304d07a82e401681c8a15000000d4110f82040c0c010b410714410401c01000402d407c12590400b180442c620109d150213a034900300028070459000307030703041400c040b0b0004406c04604051071084149400901041c1e0302c405e4030803980c0c0e6a0504c050707409035001507010700418200b0054400711100c01203001d100c1c882821868078580090340b1001282e88100e0401011400c184076042c010b02d0307030700011410160550350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 7673964 1250 7672714 7672739
    0x1030206040515071e0c0905060a03030c0503070b07120c08060d0201030203060307120b040b07020d0c0305030709050409060204050f060c0c011d04021206030613030507020409020604031b0303020c0901 88
    0x4681c4100140c0720b24801e243d2004084404c0c05a200c0030b08203540303c4280c1d0900c07958180701000c3d0364402c0c40a44c00100e440981c0695485900024074185c00765042d0b6409403042e00e40350405680608c0b05001d07800000b1400011503000d0303403141e100c4004d01c0307210350844010381e240500c008041050500030311140e500c0c0c0c0c54a0000300c41e8242405612941c890380824a00955580700d042010082694101440050b82c2c055000b03600900c00c01c001d5a80350082640d46105440c00e01000840c00448680071a204202458205400f854094801e941c2c9100080c20782e5031413101641c44030b500280c20403141c90082c1117a00f154000390740f0b090170a0032040f500ca48404285400ca8180040300c540102008440100e200c40da0000810840d2280808490420b00d0503040314014040d1103101d0209041680200314241e000f641951038a00e00050381e403d01015080d070800407070300300301c042c400440060915880f0300010101c41003501e071050b1450500030320744040c01500c0e038020390480c40140081d07040b000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 7675214 1250 7673964 7673969
    0x708030a090506071a0a09021009080a0210031e06080106140a0e04030c0605040305030916051011010905011103070806010306030c050105070f060c09170706080115030b04051501080f0103020604 85
    0x3c40c0d10b601c54150381010b0720b40c10b00032032024641d5a0a9801c00c8064115035107c040554025500c006805480345015504069180911491940070060680040c50b00e040d8040b1085514a8086007134030300c0e041d28460120168090551a6031200d009001c200000d2040c50018031280b00c044041d4441000410711102c2280514071446d4100d1001405050090040c00382040d4404e904000514050800800c980c0047d500340e07401d4060307003807204d02c0080c000b800d210940340000c140d00380c0c4a8504009503500b1a603d0700c0d0b00c800c0d54032100c0135004101c080c4544480307843c61001060741e9140140c0000e055180c007d000506151600d00e0a1020500c42e044330000c3d00d10a0804960355200d03414500c8812003c840010109402d02e040b0180007a4451000400c07034010351440212520040340e031986500f914018000000c128000420540580620248840c0e40c942000120740251300c2c0440c09a40c021600c0e20b964444d140f04614855070b01c110482d03070051021410003440e50460b270004880d44280d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 7676464 1250 7675214 7675219
    0x2040608070f0e15030402090a0507020c0d051507021e0f150a0b040f020405041d0a031b0b0103080306011b020a06081005040207150b060301120320030307030b030708030a0905 77
    0x1200b882c203195001d600018503000d001000260314074000708075201c6aa0045078224011200070010444010b00c60161741c0c00f40d509074014041d180c06010a200c0000d8620300d040c4c50314400c21042d404920040c8407442d000303640f15805806040c4100f10610080303881a404440103500c00a0080184000461078003554840700e4035801d00c5440300158140613122030089154070510302000c400d1804490f9006104a58059900748101e60241c080314108501d8105801c4160700400a000006440784842800c2c1020982171020301506179216004611000d8108440e00300002061003c50740e00010b810107200d0000e9203000741507003294003003800c0b440144605030038000c0c20350101d001c0000414440018000c0940304640360200c1c0d0900c00d503441540040f207150340e0301c1c00189070454102481180e043c0c4c3c4035208000c04a038510394048507040c95100024072070700c240e0b84001103101d5003800114003d01d202e175000f081c819001c008044c00d101440d8041201540b0800405405a800844079005c440e0b04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 7677714 1250 7676464 7676477
    0x21203131103061305060105010306120b040819020a020f0a12140106080d0206040c0504051308090301020702090109050601080601050408120d02040b030106020604140c0a0e13060501060207050102100204060807 92
    0x31494045603900c1c0c01444103034980100000c006111009501420045004400300c3c0c5c0c09903616401942116900c1c0520329840c1481070746003011032004c0702003075000b921454406151020140c0d000c4040c4000d41c3c01c21006801c0808200254a03190259000700b0000310b44035001180f070111200301c50404100014040024050b005107004400e41c4818018105441501c50740254481c00a403107413400c840c00c80302d40000c8840400c0c24141481402c1c8601c0c1580e224456040f4292203010a50700018103c69266400300598401600c9800c1003134000c02200c1c1010445040480c009819600010019810440240400c100200002031092140000c0c0c5040300d56030b408c800341c12006840385070040c0706d01010020000407460340c0040c8044c07040b03000c0c0b039100080490100c032482d101c2580c0960143d01505000b000d01c0300025602c0c5aa80000800120b0405400280d54205c181e0780241d10650240c3c000d443c0030081560140a01c1d685d852840030110300c6c20b0700b4a0300c00f41208801401100c100540d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 7678964 1250 7677714 7677751
    0x1512021002010e0313080601090c0e01080a090c0e0702010c0201050402060409180501020f0903160303050406030f0207020904051c030b03062701021204060e060906010b0d0902061b06010501021203 86
    0x3940083c58125140b810380755a03ca408100c0d10320340c0c000d4420340449108403000082c00089038480c0d9000d401290b90346c0c0062442c40401150903107400384c0740f020780365580c072220000500e4441d84c0c1d03c000c01c2c00d085100c1042c9415040a421100d8600d070503415a41031108120050742c039141180c080d18043d590004800c000c00c0704c601480311409400400b290f1000444503850b604010180c4a000c030101d00722600c400e8185c0d491b205400852200402003001440140700240c083c5d0803070074550f20217107801400c2c010a6000515580010f80342501c080c0c001414104003920340d11045071000903281024010490741c500800e9403403000502c180c05900590a08d07007140c06001e13210160f540b080304003c0d5207560421208421020085d58110754040c07400003e035204560114149101d0800c4002070034080e868401d9140b000e50140741c6d409511517607180340701d0050351110042d102c24811603082c4526042542d00b424074250068000d203055501070042900510340341c10403603510402582e1409000340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 7680214 1250 7678964 7678967
    0x504020f0d05040c09060812040b09010c06020703030c0201050c04030c1a0c06070e03060601110d1809021204020906060408030414031e03090907110a03030216020a030b010915120210 80
    0x118400d01e80039905150500080c451a400d401c1c058800c40c00082000343c1c0d8408850f580c2d00384e410702050101c0340502c8200034000014000d8212150113041840440305c031640c868040768090402140440d0351900c104910035030910074070358331510b4115514070b8070342140c0301c08080c82c405228031900510820280d18042a00205544c16441d030b100440d03005044c44800070b420310810100082c001c0c810480091203640c03140c2d00009510f8010070142240e50312214040314900104011149200c1c240b0030000383c1d04a061001b005d00000000101507542020310402a0115001d40154480e00040c84244041103000c003c4030204c5011903007900d08400385101003420491b03000b815010300d4480211b010301340c1d1000f01c02050400400c49104e01c80d542e40d01c0c1d013500c021650413140800b07503110840b01c100090003980100f60140e401d10081030514a1640010381408440e041103444035902c00c010400c5200311b0003000c1c0403580c034070b10b003031031481c141101083d044241071800fa1142003154000344149 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 7681464 1250 7680214 7680217
    0xf0309040207022403010311010201020a0f0c140609070f08030c07230405040309050316150507020612010906080f030f0307030209060c100b0307060207080705100912031206120201090504020f 84
    0x80640c800b113002134440100c0c03441c2c0d00f03810034441684c0c42006036450104641c418401c849021031035445003104081d00c5d510485440c0c2c03200a00316101103018100e035059100c2003002604c81c0d08407070001d0400500b042c405000c2900c20364060500d0b1f5106100c2c448000b83c02050000c180d4648210302c40480740c05008040c20046a0f50030290024038181c2400245030340180d121080d0345059045034450031003050f001e01c0d02c001a10840c288039210f13480075921548908014903141e80003c0600e418240c10b801e10400d000c0c001e034400c800b0580c1d1200204401201440a4148448888051400c01d4007001240c1150f10008110508250340090540100ea4400342621140c40d04042154416006c9400c0c0100030034078101359504c0382c4200080004c2492000a516096030b40c5103020300102d5141800b48100703da207031400b00742403100007a8082010441c633160210000d0281d951001045109001d09040f81c407150004005400c3e4040211301603604041d03600304583c82a200181d0301e010042083c12030307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 7682714 1250 7681464 7681489
    0x90b03030d0903020c090105180c03090312010914070903030203040509040204060e0a0b01080109060807050f0103020702030d020c040f0b0f011805060f0903010605010206040515090111030a090b0106020f030904020702 95
    0x54030710700b041c10030615500164010100c00c003034824030403d0340c858040203003003885400003a50f48004c440006006034490340113180c000070400212828080141d21040c2d0200c000d0f00a0442c880e40c5400009808101070441e9420070407505004003110700b0b5441c002d440e48200d0280602500085001c00d04644507035100c00010501582042e84a0425100c0c00300a8086250450700007106c3c0000450318403641e114400840710b12800401705185000c0500004072170308a0000e050543c01e22185016031410300926044180301d80c040c10880b103090040004039260b43c40f10002c0c1c1403800724622000d0b22202c2076410f4100f4242444611081036100d94221020960801030300a070010a00f04407041035000a070007101e908500038088161100d00499440034200c0c0c000d843c5500503a45003544000d40c2c80d0740307900251020000700c1c01010b05030141005a00995549030166600c0a102080c4075404021038050324130391010b0150b10750003e959603524043c1032a40c41c49660b00003110030855a4a4001e40309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 7683964 1250 7682714 7682737
    0x601090b0c0610140a0504110708040b030106110a02100804050f030406050a091d0402150c010c0507030806030604330c0306060f030204060c080d0e0609010501050a06020703020a090b0303 82
    0x169188211403080e116541520340600740e0480590104e01c0101080c0e1080c14441d014103440e03105490070301008054902210102240c8004011000102e0203400017840580440c101e03065803545072000041c09042d0840f140000c68210300407540040c1da44480d41100146d11703161612480d00c0c4c50034942d04121120311186028032000030001001030300300e0f000e055514041d4460042d0940d071148004000d59682e0100715501300c40c98009001868a140e4881482c1c01d04241c1030b0402a140d03410608554992000d8030100b2004245a010154080c0e0860344c0544280c002d4004c40c00c1c2a032352200b1485010404026801802c40e10082194015203403a40414001c80140300d840310140020f03006003094014000001d03064911250814000d0084030308a41c3d082d80e815891003030030f840c1c40c21141c200c209c044034165180e07105200c04202c100401ca003c0d8420400000d5076524000420070390349040c1d0f101c0c20641d0400c803c1040035a6501c00810120345502c01c010412051410005c1e0452049646640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 7685214 1250 7683964 7683967
    0x5160e060d0f0614030102040b0f0a050705010c090e06120601060311090306040803010303031401080a0201030b0a080a110a050f03030f03060301090209070315090905030703110102130b071502210601090b 89
    0x2d2800e606410407811901e84141c08070480b200c05080c14240d10490203016034298003045483e41c64003100008119144030f9190203818000c56580355820745803002c42c0503000900c810001d07c00b0310724003024590003500440d441c0d58498100400607485250521500701450365401900c0a524045412038405034402016a0061714161400d048660002c0c00290f001030326040f40303070303a84c21283c04050381691416001085222140c0d801100984240d00d0026000540c581c0f000a41610400c011022103100d28426440025450103216500102c0e03844030748100308030503002c6203544010041b5012198910740040d5203a40c1c0401090140c00031660080d084061141085070305607050303002c40045031680d296540496525501901583c900d4040906150020000700d0002409142110703c0603003560b0016040400c4040c440c6401021680b28050b0030074002422004c0144442106420380c1840d60210f04240300e101042850b1400001da80c560304e9181c0380400c000c0d82c045c42d2100000e005070300c86103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 7686464 1250 7685214 7685231
    0x140906010c02182e031a1e040215030711010b040203010b0403021201090807080a03230f040501060b0301080309010305010b03010f0506030403030603050102030711160308030a020f040b04030b0601021005160e060d 93
    0xf040c11100d611059451b02266110518400e101c1c112070f5000346083c02c03103031480610102000100e160082c3c012680100c0b0000783d505901c1403100510311400c00d54407603081040e9581d80060130345d20340d1704c0e0f0148664410001441103680c114142d0781640e805441e603500d4407450088039401055050b001400010000c607800013000800401050510700c01e643c00d00451035942c0d00381c0c2022100121000000f500e60000514000e00716140d554000d01030b030000b00341d4580c7c41c091141c55034402e0300040441c1d04002030210555826008082c010841740e010140f4542c07601200c1004948680541480762400001260506110750801b40c0910b40003070003150b50b0309090401508041051f2041c144501420b2911081c1c0f9460001250440342c00005403851650b6402c003101c025840001c4440c821002400f001c40c601c0140f20203813004c5c42c03145402100505105001900d0203243e0035100e200c5a0a20702002030395541e40c9601d03034102c01142041005040e243c00000c0c8180103c40da1407890b20f10f4070054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 7687714 1250 7686464 7686541
    0x1030803061206070504060e031c0801060212040f05061c02030c040306050c070201121503050a050303010305011404050a020d030c020409050601030201030f0221060303040e01140906010c0218 84
    0x2140203420031119070500c40b00181006403218011140c0c0804a001070104100a034040d00d11080140c0004050710501007800c040c00e600c00303078000326500000d039030a001807002039010020022200042c803075413818603182401d0007001c6409400782a014403404940c01c41c4007003510f10200c22004049006640341c1c40c25504000302c0e500030f44000c1c2d89845c103110204d000e000221086410040d01070756400c81026480d8510030140500c00c1703480400d280b001c00c000000c900280b18640500d84070344040c0d5074075491402c02c42c0c00c0d644101411140e052f0300d5018800060b50000c2d5601042d90706441c5030384030252504080e510101007190194000d82464440c108000001c078205059034400d880030803115411000b450224061608010000c03650300d41081c240d14201c1524907440040181180e00d4103403107840e1a4182e4100382d001c41100e5503198885403542c8cc0050007194003490a03c0c240240301e9060300000d4150b28a2106002c111600360301087c8411000c007004a0503030b001000440042104411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 7688964 1250 7687714 7687717
    0x21608060403030b040e03030a09020f0604120b01150503041212050a0903110303100509060307051c03030605010c0f030e0a080106080706080c030c040b0309010e0703030801170604030801090908070b010308 90
    0x4049001a1901c0100116460302d40b050710b00c4407030490007c2d400d40d80c80b907440100410310804203a81c804211260032103650303100c3d4001e0025004619a40c00c0208043c038002c002d809068004000444000050700181a4410141d81d4804d8000040710903000e680181a5213241c19034540100c0142000200200c012498120f182030350f200783c0d112807a17007450442450300ea0106450710801c01305080c104010702c1c0740c112000c9400c0700c401810760305c4440e03903130700042c1c143d0030703600d15510824203400414002c1c5500751242c000145401c0c200014101e030f040c2e84210081e56200f44c020140304640d44d01480644a544010001e0800c941c02040b21030740750142d1964036207070b521030000055102000204884203c40549001c0e583d449001428641000d1801106030402802201999a22030b801600341c1c1c0104065401940240c44000b015414400800104241003120304a150300520500000950180c00ca5046424040700010b00c9480b41c40c00302c3e464450340341e01802d00203c030300010090000880 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 7690214 1250 7688964 7688971
    0xb04060207060501270605010e0f040f050a0504140105060303030403030f09020a0303050c070909020a030314070b010b12070c030c02010f1809020310080a0b0115090801050702011a010905031c02160806 88
    0xb80c001150140d005d002006403080d502500e40000c021108402c0a42052801216510340c0140b011407031004945010088400c202d070071145194495060005124111884808121015000703110078940030012035520320024000408160340c442400c806100709a00204400303a0080c0b98610341a60f904000f860307900684059940c0d4041c141c0001440005446403455a40e40981505070507451604c055030b140c80040c02e10707641381404221640000d0600801140030741074036040a0384803d414405602c03038100040101062000241100003c26081458a400c003542407070322421030001d200341140c0c42c10380e0854981c44802d43d40400708082c0d40c1034001d14030990002c4c0e030301c540e83d03980c07101c90658038002c241c030107020001c1000040c8651100fa01490341800d000d824203800a554408005084640440381c040c0141d41d61040c0c030041070314100044444410034a010080c86041c031000940b65100c000c421442c008400201e07001d01070081c00b90405101c0340c4582d650485688080c0d0544406045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 7691464 1250 7690214 7690259
    0x19080402030f0c090604020a050405221802060702040c05041706060405070512040303050c0f0c03030603060c210406090203010e060403080105010207030804050402090f030d09031104060b070b04060207060501 91
    0x340e546411080c40003072010f40ea000d00034501d010540300d81050100950041e502c43c0f08004d4100804181510781f8113004948003450740c080101c03004490114411943c1c451442d0718200c0324100001c01590f01c0340140c45909804840c001a1410f042034150f456102d568084040c0624203508100890404148e0500c42d180682d01404141d513821000c8909120740485594020b1803500801c000c28840d40c00b86600c12090480c10f0300e00080c2d07210b0168190045813610559603c00802c1281a00301800300e03903080221080d41504001c614248843e031b4102d0f043c48414602082c80010341030240c1500119508c80d000ba000308918a240000952102ca080302c05402250703101000080e19407000680d00212600203003180d013084d0400782040042c2d805021340341da03c91007a58a0680a035030900c0f4029460b01c01e40ca4205403145103141800c51403c45903515486245081e100308030b4801850100c401c4070b0b50040315030070640d48502d403480c003e004460002c2e0540380740500100713014102141420150091 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 7692714 1250 7691464 7691473
    0x50c01060b03040b070c0303060503030f030103150b0f010e010917010501030b070503070206041416060504080106050d050309090c0d0905060601030e0105061e01020f011113050a08030711061908040203 88
    0x1a1151090703144000c0c2c1e0b000306007071207440c0080d81d094405d14203412018031038500403d5131952100007900c1d50300301d1240c4c2004181c0000c0108104110103400c0c3c2c013204030281003440040034000006100d0b505040300355052104407822800c0caa80305603a00d41c00741480b0280b41003c0c40e819036895000705402d000880d06410f1034404107810380e0084080d05d1240b140e40e030080103903558a5990b840d0903c80240d402505200380400d251542004401d840040c0410355034071500c0324034104400b030a40f882584940d008074103001c54500400d08c0803088a014440c160703402c0380581c450040c505914031030307481d503400c04915018100c000c2201c0894035900440d02660140060200c031842c0c982201c0c4180c07135040d0b00421501c44820244500c000701c0c401d0301d805006841040b41550070031400e4400c40001211504400140d0202200811841b030010f4103050b80e5421925040846a035603921400102400301802240c12981940e1034800700d44183c00000048002481040b030301500703a6000361401c9200b80a07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 7693964 1250 7692714 7692719
    0x21002060c0405150f12040b0106090b04030803070c05070b0403031701080307060b031207050c09010902070503030c0c0a060e010b120d020703030509040b0d031110050601090306020a03060510050c0106 88
    0x400100e9038014012101c88500d401c1c540800c11820018150f62030750369280912401403d0307a20700000c2e1075a6003040101036524036062604059800c0140c020314103000300d0410a1100d050400199400d4070740c41605507940341c8900102380d4910040c214000e1007031054600c080f80c0001043d016204507071203521203030242d01240b5545d001d200002d0041140030780c418001d031804610703607401c00c0310007481c00360903a82c2118002c00c4c0e40c0c8555000d40f03001e540d00d07806070b5880203c90403d45001c038014040c2d80421414041c1c1941c40e10749904c4060300081242d0000719003a101100309104002004e54888820010b000d140c1714920b0103410020140c610a545240e80400b5190010a0f810600c00701070b4090000d5030308542e4227076800d4118051041c1c00c10360728a041c41a03601d41d032002d605064007d440d1540818600d03400e4515200140c04141d080d68280303002c1c440241d070028010800da03a030100d005612010946011001800316a0107141e01c8500f02d48201d1149400c040140007440401c2d0080c0815074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 7695214 1250 7693964 7693967
    0x106030c0c0809010c020618031002070305031305030d050a0e2b0518030601030602071b05010c02060d02130b031503070f050103050408041203020c0a080a03020a03031e0f06030210 79
    0x2046940380001141d008400380c80021010001440b07849014180b0300128907440c0c0200b801c64103d4107141030660944083d101e0309141c108203a02d5000c020369415403800302255402803c601029010307000c0305010b03907208000c000c0d0030300c141c3d187c00c50083c0c8100f207241303090b55803e80130f00201c4960b10070702e002e600e9003070285022020081441c0c0c480b0840414101c40802c00480d40c951256035551242c1403070040e40a89980c05200b800d009500403d405a200c00980c1406480ca4059100e0803d107288107500c00c00413a600301036600f4503950100c4600703440725141e40032240a80720b01c0501c001282c4040c9404620780701050042c50081d840902e44511900f848008d16075994a00d0207081c031200b43c204010091507200b6003020f42c5c0700b44240700450800313644003140000916690b50407800b40c0c00900340349506007003403414000101801d01c014a17000da0b40782c901a4a4681c00d200243c10141c03039907501700301c42a0318003082c01d460019003010001c03441c1001055006161900003240324180e802c000d0300e0b605 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 7696464 1250 7695214 7695221
    0xb03030a0c0b150301090b091e070501030203040602120403020a0c080f0615010207050604080d0305060d12030b03070510050706050a0204060206011509090207060203090114150f03010605030304030c060206010603 93
    0x9564035101c1e58509609a101c00b41c082c80010b2014140070340e0700503688190b44081c040c4003005446203080703496a0034403100c0c0380d080004020522120620790004910344140000307902088907400e090051342e94580e400d01e60b01a1003554008032604200006000c1016400038440c4007460294079003594181e1141c04c80d0707488030001001847d99600880100f104600781e081c038140301040500440c0c50b210365038008100d81c0c1d00140d03c441a5a04800358040c15160180240b83d88050110342664444100e580d0b813520056411441d4402c26646058113403440d03e00b0040003020f000000e00c151100c0900c1d400050440d401000220303595030824000c20b07100b001030300a8509481241c3c000d00403d03800d03c140c480304071075560800e500b00a00d90304005541501c070f200402c000c1d0300900300580e992074a10700031404c4d5080d1100d1018440030b0802004203003d0160401d20140e042240c000450208110000340034000e41d4000c980d050100040c00010080e0f02c18040e421507403d6002c0c0c400c0d50380d8a02055048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 7697714 1250 7696464 7696477
    0x30c08100501090e0a14070305060906070806030c0105070308041a011203030f06030b0103080d060f06090311030714010e06040305070608091b01020304050409061805030409060806010506250512030a0b0303 90
    0x2e81c3d04c170a810710009100d1642c404051202ea40444203d650b407a20703034a2038031500f80e444454582049003844030780b680c41132685600c07030b500382e00500382c80180c3d0300000c0181c840c0400241c2003014410200e41000b0010240300004801d6074624500c0e56100c90410b0441c1c00410421030100e442e001c0d0b0000300fa0104e006080071207800104001103a0b18544503c0101d50004150203081c1c0e80e11b00010907908010721181c4003070708140c2c0d42c02c0b280606619000c100384010b1401e03130303109500c01003081103010000c0c015810146001c2c80c12341040700010020451500a607000140b2a004401010807040e52010719244141081811a64101c0a011030843e24100c608486401a00200070074401400d060300441452441858005058031400f01445142105894102e502e500001420071200000d4000c0b8001703000154083c210b03551519000036110b03c00c4007036500344012038003042241c1e00e0702c0f01020384c59581c01030706482c064414690322860b01e0740100d81591034103250907480b207400d0400000b0b50701c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 7698964 1250 7697714 7697741
    0x501022109060c0307020a050703050c10031b030b01020c1201050624030106031109040504030c050d02010b06090f0604050918070b03090604061a03070b070b010b090a0e090304030c0810050109 84
    0x1254407080d8403e0100c4e40000c5c0b00380290b01c21581b1050000320200488001107000b4400303003ea4400c00020401800080010320b020103091505401c6690000c0d141222400180d050028480e040000140c1c144002c807140c2507482001c0c41c4190082e0b40043d00801c0c0300703140481d0341292000d02030740c4840e1a1800f030401103494540a02c0180030150081e80444c2c50404002e118074200312401340000c0c01d681088078101c000980c41f23420402005410440c40b01d81c50550b0009100d081584404940c80c0d004840c0810300c41d130441d44411119883d0700007264041c150141c46098075291880d80b441646d240150006900e21a410000603000591011b407400f9402250252203075842c0d68440c50003400b00018501c03c07044150b008059150b80c1000148011305842e85c500da00c41d0300501304200241016070103035403120400c12200440e80e642982607010b68400300d100344915211b410a440c45e5008580004120603000b4401190303500001885121031020000107100982e220303041017040d2141e20399103a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 7700214 1250 7698964 7698973
    0x109020406020318180712052d04060f060b0301140604030b0604020c07050301020a0c0c05030c0105030c0304030e04062607030305040506070302150a06060206010803091008150d0501022109 83
    0x158000344041c0d00f00300f000611384c0340e0b50a03602900c900a44800c1c1c940d01b0100e9051916036040c1801c0c2d015050340003003580f03009405d0468561410301c00b00c0246030a041d416503030300000703401c2040329408005440c1400c501004141c0d04c9050700e0820794002c0c0503006802e01d200700c1401c0b0900e407181c2141c099036441102100306460f0402484040e4002c0c00300e1070654003404201141e251024400303801d1240041c0e5903495080850300b840c5071501d02c140c000e24000e80107004001c4d881d0b60807204a07034120002c60341c000c1e90b0381e8640c20221032111009901d503500c14248200000c0700c040c80b881140012204242c1044110450302c40030383d454820384001800319509010130400382ca420805007607a01c0c000e00548069a8030303880200c072075000c00c55202c0c000d5940d807001441132a504110185c0945050340040d450300007030000160710801002c3c442d01c10000607100084500564141c1d045100c60090b041c104080f80924180c0c0c040e4002480740000300149130715665203120500d003901e0141c4420000342 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 7701464 1250 7700214 7700227
    0x8090105040317151f0e03030c0a08090102100c02100c020f0a020f03011104030b010305061014040c09120c03030f0e0604050d02060f0d06030204060504020f090d020112020a03060503010501090204060203 89
    0x5000145004050300701845414100d85910b8076440340d070482e6105017500c0514032661185010700103040c5805058003070ba0040c03045a0000c2c4001441c0c04a1541012546480303503c031000403843d1072440403d10b01d0343c505008507142c001c0d4001030400c600080c07901091000040c0c44070220380e80c5207104e603070001030340c000142c040c0581015044400c007000d010700082a0000707030380000d103401d49c0700364001c6131502070000c01007003400303400d200c407607003052003600d0180b8120302e000c0d1114680b4201c0c0306042d215031365905600818a0141070110000c00885145214110381800c0480903e540c0348003d80101b001803810310510b6100741e01c2e5150207240104028201400c003400d00640c02c1c415602203030460300800554011101c13a00140c925490501c1c40455440c0c00c5105000035206150b0006005600510042c0e5201d041e22040c0c0f81503110940745003401140314001215109103503100c1c0c0b09154800070b0403403030380b03a416000182038820960090069999484000080784218401e04d401a0424001e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 7702714 1250 7701464 7701497
    0x9050a09030e011439010203010f06030213050409030e0109080708070b0d06080f071706070804020d02031f0204030201080f04030c080309030903030a090501020114040c1401020a06020409050106080901050403 91
    0x4c650312901421501402e200c2c07885002007139a00504000104814075002d042d11100581c107010f0300d040c42440082d4115403404130105131340c96190040d0020325401090422080728030440c000000c0c00000c05c103210700300d494240039104514000c0d44a00146a05501058420001542c001121118030007004200d107005484030b05908411008804c1c580c8425000440c038031308100548000038898045e007000d51a0208050a00311680141042d6401402c00c01005940200c1c00075402a01950406414031032480001e06103000480f403035001c11866401282c00000d16405031082d0f03031003a00c44440075200d004500d450800211001000102c00d02001c40c0060641d6003d10740100300081142c1c1008210070020342140c00c0005200300066011604200c1c1f0341e8240108202040e0100c5440c9043c1441c1e11900d05001c0180500c01d002c18010030b0301c03505644204480c080305900110110b444031388070035640019040a11608000880b20004991024818440ea5008035450b48a180b030074210b2011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 7703964 1250 7702714 7702727
    0x30412030201062c15090c070203010b04050a05090709060b0315010c0b0c03070e040b01021011040e04080405010201061706040b0c120f060103050705090a12020406170102030109050a09030e01 84
    0x200c0440d522100002403104035519403c2c112100c01440c2050f5001d09245156810070043c105000100880350f800c240b03455032203855402c09607060072039940c1d0303006002003400343c0401da107469003051500d820004c40c4045548024020b96105d42070303171940c0f075452494905480d03441c054032f407a4240c1000411415915086a40781c20041814a15100c0380c890711500807600007101c40c80f035034250000401104aa00c9400d4043d1107000710740401441c559400000e549030701e4010b08000b0305d0b0b9500c24036100400d01c1026a4000d000f201c83d002d84c2841d06141c207003802d80007481414055801c0c0b82011640390303910202c0e8000c00c0a90340081445079500d4480b081d20340c10280203080316000c20020311402c03180208205c0d116960006950341141089000102240c0000308100100082030014402030381d00c00c03c1080868111074a65030b10051140002401002160f20000c5041524941c00d807940c070064010754101d135200b540070420b0b40d40300280c10050f02c003255070090019203252800481c640c05601c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 7705214 1250 7703964 7703999
    0x7110f040e0706020c130603080703030e16030501060503010c0503040b1308071203091205031003031202090406030308070f05040e060121050a06050913081605100203010b07060b040c020304 83
    0x10004a0200740c040c8440d41418916000306006803c6000c0400a070706080c003032500b00c03c0c2c0740c0f9001c00c0340c24995282d02c1c0d814001c2d00d00080800d501c400c60400010810010880d0040e00c2c08599054503a891400d00e000703140324442e4502a5080011010b1094045d400360392289411a81000c0705680d00c024035418518400001c45031401e041c0312080201d0428808482c1200700394400007424051b0b414a072450100c03400390142000020010801c1141508180c5000c0701d505060001081404940c0b075000307030288038200d90700301c1d103030100000a066002e4052400f030340039501c400da041601c00e40c080b80c440c03040d0b0203001c0012070b01c0700228029501c105202c00b5030380c00d00f06104800038800307a00442941c1040e58103032110b41d100d480c18001e5103016040746030000c05040040c0e0119009648940060180b281c0070800d0248003501441803050600c403184c0f036502c64840441d1b9070b6841da2800641074000c11000e4075002e103411110842410544503283d091011394000b50b04092402844511110214 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 7706464 1250 7705214 7705219
    0x50606040302060c071e031a0402010527060309010c08090c1008040204021605100c020303090a0b0403051306020706080a0b03070509150402030c182704030915020c03010c020307110f 80
    0x2048001800c0070141b60a10111924158006906165081181600440003070102c0075180302414000140e800108882c0c0852070710450b06550181660091a10b88014000e0354200000000f0051800419480611141c1c25034550480c50744444030481d40c0c0d64080582c240e0040045e40c5060b44581c0111a07591780180f0040c800340ca00701000500c5191100801802c980a52084241c1e06200407540101c401280c41440254114030b080e1102075500e00801e0b101519600b581400b2a05142c0b284003241d1120a071a0796a1200ca41d5450700250340e03820910545000031b030186d002c01d61074107036401070310400303080240141620b504045c200034041d03001402c2d049081c5401081800181c0302c50000e10300c0b0304c1010480c15110144a10324010400e08240c0c821700c9500f40100c003000190008044580c8110301013000c004940c0d80d444e041e124600c036908101040300c1810421116694002070010b1140c0054009110040c070f01e2006982e41d010b03c8800404d001c418100003000c0f400c06103506100b501b0300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 7707714 1250 7706464 7706473
    0x103110405060a0908120a08010e0c040b030411041107030c2307080604050c060c0316080f0304050a2f0409080702060304050607090f03020f01080a060e0c0d0609050606040302060c 79
    0x4410014100703074424140034000ca1400c00c0108601c0909000c081d500c6d01607040c940c0d05d0300054003801020301d4414000c0041e21880d82c0d01141c42121200203a038058131045000c142c0d603091508201c5030300e55441c4003541c0302e40e041c25918240b0041c200180d03904190302d030322429060202c0d80d031100d0341d51402c0d044182c11b900c0805d01c80e900764001000b81c074008210940c05403807036090030b00744a8200401e481031240500b20411118450a0000044400300702c5402c17002800b810032854004200c0c8588541c1e58021350b4080148030601c1004160b4504552264000e103c07000d1790001041e00b88a04180c0e00e6000540e00c031422a0070341000d0700601065032040c0707192441c00f01c842d800a4803641081d1401d480c0d5500c03e10801200a401c0856003019100c5001314030b2545c1d2841e40040c4407040c242c1005810424100c020500d9107030720360004d00140c034000780c07801c3d9545098014901030390002c5e49200304581c1071910001e0703418036034030440b4010703400540080e24080c215001d008643c2d104401e1003506114 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 7708964 1250 7707714 7707719
    0x30a0b0a0609060305060a05010c1401021c020315090c030711160b0301080d0203040e072001090302010b03010b04020c070302060f0403080c03030703060501050901020606120a080c0d090e0709030201031104 90
    0x8528803a003000d0100c030385a40344190f080100040444000900850003410207039800c5c0309aa8100320b080b48040d50007610742800103510041c06004e0f0040f0550141c022410580004841c502e0f600507620402c01903d40b05542c0591608220486006880c1449882420004a25142d100d01c8039000396071071500449410154089400003011225031142070413401c040300502107000c0c140301200315210b0340d1008609142c00c110706e0814510307001d001d18081c4074103680406484403070050001c007580e80d610000c000c00c01043c20040c0c040c05588100d14440d500e440343c3e0380d07540d10f081d200342d44249904100501da4682550f003808201e503c40c0301d14848440050100100081c442030007092140340860103140c8a003480d61024046d1592a00050b061103424010303480d960340d0000c2c400f5805442283d4480015411112150078000000c0d00035000e90f80001c0d6040c0354800010f6840c410441694510301c0441d65030052521051060707881c48001440c05c0c204201540c40703904802512a55035140500e090b5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 7710214 1250 7708964 7708969
    0xc010207140c0103060503030a09091d0319030b040908030105040908070f031d01030603050c0f06040b0a03021201090b0d060b0117011403070801020a02030f070812040b090c0a0302060708030a0b 85
    0x242004100351030362040b00107a00a50381030160b41c0003403800703800440c03d10303100300d0b0081d065140d2400350095061703440340e500c3d8250400c00412646100e0f101c0c140c0e03503145d580c01c00e880b54200c040c000351030100781850541c0e0410300301403194030401c5402025947c10359003040c081001908101406a91600c0140041c1001c6805000c2180490384240c50f903d17800003034010b2050700d800b052000e0368185464004200007140b804600c1513507140c400c8a003010001d81c0200020024026500300d000440c1010406811540d0154024411030307001a960411a80c3e0f102c140c0070648411a81064001450704104000901c003608426003400050501460828601700030b0303131803da800d90010403d1140041e540400342418000c500103440004000d615051603440042c4da070348902e40b0f05c03088004c0001425001d2210000c1940c1951100140000280c20182000d10f0380000544440c215130203540c2c20b5651614206905c182221317030117482c240c20b0203c01d407143c0145400003450140c501e5201d9051103407a9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 7711464 1250 7710214 7710233
    0x1002091801080601030c050409080301050f12010203010f090506040b0a060c080405060d0605040c0f14070f05010e0309010f0302070203070504110d0608010c03060503070e0f040c0e1608060306040b0c0c010207 91
    0x8119020042c0701a40c954141b0400500c0d0729400b090056142201c0c1e480415503450441e030640d0400c0e21a0000154140b010400c040d5040450309082d5201000101c3d5901c500d10640086590301d040500c07958072244108006c5031201c404090f480b818414040008074000c0d18800900d9002e4a01d0506160f62749000c100580d0000307402801a41c0d0307403a01803044d46801c6c800c2c08054459841d080c03d40c4154110302500c04072500d2200d40b40c0c0b00011a14000308000d451048410ba80d00034001e0040c00c1c010301c1013a07901c1d0040c0448601003900c400180c16054807034420307a50b4094004004000d1145000140001400000c0500c01f40080420101c009440e8900600d4020695500005010305030104d0003411500541c204503c00c0e00310313800030000306103039008107a04034489900403c0191214644000c030b2116a90261b8107030b024201c10040130907102c1c0b03d01c450303c0348640c840600715512a401c00d80c41e040121707001800781c0c40380c00c0464611610b2801070701300c2d11101000186040082d0b19401c001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 7712714 1250 7711464 7711469
    0x2030d02040905011d090a03050309030d020c0109021810090b12010c080601090f0302011205130c0e04060507080c031305030903070e0603010b010e030a0303020304050a02060a0309030e01020705031002091801 91
    0xc0e0b90b10f58004108404100103c001060402145e031a02420036441c0d8070344900401f90003074104540400851401c500600441e06440c1e0314a1046540b030042010803030103804218003e0380701e0b0301c8482a4003408403219040f0303071040240c800410000c41c1000c90351001001174490b51600b09003c0c403005e00d50f0810134414240c1400c0c00c0d4a80c0c0c3e440c1d181960006041e03124540050b41e2039982d0000400040c0d0f0014410319900148010204082c0d540b9090540b11008991002d0000341550320f00050300700290314488e000e00e0040c042448195207054090710000402e0340c0103003403c0e104000007564502409041080c4500c13800c1980c0ca800000c0001a00d06205a000310402805020034444640b07000d11a160280c4020b00703080201108030b4001948172503c880e0040d050680000c002003c02c5828411140c01540c004e141070b8680541e500c0060080a20120403004282d115001d03104a60000401000300c600c01401003c0c00701103541d5600213500b01800680e0002040070456a900340480c480030301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 7713964 1250 7712714 7712729
    0x3030610030e10020f030a0b061806030c091504030b06010302040e0117011103010b041806120f060228120921020102040801020a0203090a06030c1d0105090d05010b0103110c060103030f02030d0204 86
    0x6c0b40e040c106030940131101000b981c5403181501700405c0882034280769056401301011110640c582d0b840080b541d890340320390029030f54069007440c1075142c0d003d840c01c05001a64042d1080c0001941d880e0019000c0344900d011311345c0000f040c8401009000000d003071400c0d010a0f020004035450301d0b000da143c00d00d60002c1c0c01c04200c00d10042400c0c0500102040d56102c44600d06e602808800d00c1c0c5500b8001481040307034080c00f804c440f48031541c1400700030780490b41500080c0050800310300140ba0484441652901c400000401034101c00d4618803071402070201c05500080302e81840320000c10401a24450064401c06554007400009884502032000d00701720f0001380c01460341c40707088000300900700c0e00c0d40c0c0101080c10320340b4a00048442d82b01a00b402c11103506c8401000c013a0600d00143d81d5809480203103903101241d461900108135064103d10380300c020a0703d092080c0841160820311900502c07070040c02039404a801080801e10070007100c811110180152464194200c103d8016a4000e0704030740d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 7715214 1250 7713964 7713967
    0xa0b0d08090301020d290102240c04080a030e011106040b0c030603010e15011505041401050904060306050414010501080109030e06030a0e030408030a090b0a020a11060405040207050c0307060203030610030e10020f 93
    0xd41440030002403201c5911b091010b4403101004003050b00a50b5449820a407510300e4403000152140d03205001c0794003820140044405420352490000c00070703a804021180054444001c2c4400b0385c0001881e28000e5901582d0b03e101a0f49003420b04103203800081940d54150340b01c00300150307512400d0001e281d4503404118041c000d5030401004d6403246a0f80010b40f01042410402000381620307054128170505400d1810554521040002401801c010f800c0501000d1030202400204984404421b20000645009000980e69005d81c14225900303000c0290200310900e4034a8843e260a50045078010f01261000940a00c0d40384868615003050300203410729400040c085030442d41095190700208000701700c8914084406100a48407800c0207c0100b22080d14060815141d69880603540640006802151644201d00b06190b40c3c03121070721058024000c00f500031032102d2020044903c9800064100e0101507a5130200310000c1005200003030317481c0038018122805410f13600042203641d4800407c41d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 7716464 1250 7715214 7715261
    0x70303090515060904030507050106180203150f06090405040804080712110a050a050d0312020a0201020a08060301020a08010b07050705040c0c02090907080601210606030f0b0a0b0d08090301020d 85
    0x502d890352503020010003060356820402540e462418440d409589440c0c2551505418038080c0e003d0200c41e0844042030700c08803440343e040b540c00e9000d588030740d421000f442e01c5190680e051003091210405c3e02030b0000020000a1482c3c2403540240707400603c0754424a103066694a096424480c6075080a106104030f40240001d01403000c01c900180300007142c83e4842c0500c2c2c0303800a00f8100f03041c4242801548400030000c01c0c54052403520081d01714030b10341035540d1040190024001d41c0b12040ea0b03404149400c022a07a941014802d0310390b080800d03140d0025a07401d20a100f0000c1c0c0222004840520030850089071585aa00501d4202501c2d515641c10501d81da2041101c2803500611049155020800410040c400010021f04460a0340c44e1051103030f025281c1c0384800000424064841030901e1000410068dc40740c002d0b80c041e000b81d83c282c0842d19540d25a409480140d00e0007507008140007003900c045409a0010692440b0083c0010314010030700041c50b043c0d5002000601d921b0076045d040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 7717714 1250 7716464 7716473
    0x30a060903090e010e0a0c0e100e0307081902010c020604030f06050421080c0901020c03030f1b0a03020a020103050a0207060e0703020411070209011203020a0b04060608120405060a0804020105040b07030309 90
    0x5040a01840900e05403d5070411481540d4040020204280c85403180b1210160074081c0070000752501025040c256485240e42015003a06080000c150203441003850006080001040b2401c12040c6101c0040c8a00c2680d001140c0c43d02d40700d003003640e00003401c100c00800514251441600315204100200d41c510345070034001c00d000d1030080904c0c40c0c00a950082501a54000415903201081c501c3d07481d1a2016100100c1c5440c503040380b4203400d0710001511050400003038028020b20146101005002d1042541064946a074900300901580c000b00c000380040d8000d40050741d20030301002c0018101a425280c0714207541c40d1070300c00f1085800044040c4103505242c0510000c0c000034642807441c00d420759003c80d102c080140714502d0900450400c40080610a01c912804a03810405103ea903081c242040c0008200e81e104444030f521640e01a51450b904034030a94040b5040101018100000d03001c056804040c01041241001010000403030400341800c007070030015001c1c0e0b400040004c0203150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 7718964 1250 7717714 7717727
    0x5152506140115030e010b0d050609010b0102070503030a05030910110901020610120605060d050303040c0e0601090501090b03100906060207080601090207050d1b05060f06010e010305010305070b18030a060903 91
    0x65680900310707040014486440010540303000e82940d4500060256001c0600500411800c6e510645c005085200300f0140240041c81c10f00940e0a24020402c0c103024030016680c4140c580f0500350560000d00c1440c071840c2c00b0704050f540c041d0314003042c0c0d01d078040400040822507580741142040c8910224080c0950750b810480168070818644185004604040e200820751a004100521281e100c0000802e5500c500c03440c00e092a50000c1240c0d12420945841002c55025004035400e140d103800005034079607c541002011103906855140000341421000394299100621400d805240b000000505800321321a02d03006100541c06060f2050824004a05280d0184c0c01980c40030700621824002c40c4010803036140c0380c0035600300701511034214010400c42c0c251a04025040340513400c00c01100c600070b59000d5120b0b4078241e840b170040b10941c00040d0215003080c000540151b21a1506004800d211030040203d00d0403011007002d00b12645000915140c0c0e2079608403041d540314908201056046032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 7720214 1250 7718964 7718981
    0xf12030f05060102060a0e010603050607080105090a0209060f07030c0203070e07090503030702030c0603100b122517070507080304080406030605030703080702040b04060503030a0305010303080705120105152506 92
    0x61005080c402c00007503a07102c0140c5803a1259645020f03100c0c007420254040d00c000d5910506944440c43c10306c1024107091400d105060290340d1140024403d550300380300702d4521003c010714a6041c82d08080c0c0000850300315040071800e01036030074901005a5002c0140d20000e14003c100501035241003403006203002d84907446140a13034014081000182e82c042030000c18017006403a581d031a9900e034105458001740e0390f4029012840b0000311019288044801c0038428551252036005151101e480c29403000d040d0913001c03000507180b000a100c20f4146510541e0860303c14a450740c101003080d114070220b503002f0341d8101d80608002a0401c01142c05020b00f100402003200074000240c51502c03500c2540c442c1c004024800c036907900d6404800c1e41e480d809203014000140490307480d215564400b400518003070100380c0208120100082074648a1011560000c0c14148210b00c581d180c40240545480102c1b011044880300f4042d8486604403035404c80040c01c90002806480d240c07a0600e08101c81c40f01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 7721464 1250 7720214 7720241
    0x1e2d0a0b01090b070b04080405060412050c0108011d090309030d080f010501020c030a1101050403140d030506040b031b0f0301020a0c030905010206010b040e100b0a030f06050f03060402060a0306030f1203 89
    0x100810010480042c013525070440c0c002000c0b14950340d40d840c00102500c01d41e041640e000e0713000f14001c83c001d100402e4851100380314108944c0d020b2200e00054408140901c42c80b030b5007030344020552140c0c040307000c2c0c91a04402c9041c1164204240c540009080c0001202030b0000960082c0402045032408400c03a0300516081c00942001c01c0c515010035250841100007400101d880d0031010080c3e4416001c6074001c42e0401c445000d81e030b901c10065915241c00c0c220110000c0e0408000c203c0c03601c1d1501c2550760340e4000038000c00c0c06000b410083c180300b5080070b400590048001402c0c540356107083c002420241801e80d10a0f48a5402d031a002e40784c4000c941181c0e045501c0b00005122048815049805030b90300102c040046a440307005080044003260008074a841c008038041e2850750f010f4100c0041c40034120300c240240b82c1c9070380610524034100030040342e040e0b0240002c24090b04000340201590f250902e004100c441e00c036140e40c0d0070600341e2002210000c0c60781500b402e100368144a140b41d8180c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 7722714 1250 7721464 7721477
    0x40605040c08060607030207031a0403030c18060c06060504020705010203060306160203030106030b060d0606020c0a06140306040c0c08040305030d050a090c03030521160201141e2d0a0b01 82
    0x680c0c0201002d00c0201820b001c1c4100041100625008100c0003004540c094040408100700c20902a07400c50b00380c1d0100c01280c1001e0100818a0041c90100400000600100201e515005040300d002c051003401343c0745907507030301404074454855000501c1c4a80c00f0314009662820400d0525150420043c01e50324034056454054098942c0401100e045a81d58a4042040c0c035044001031482c2c46000001c0101ba45842400a0060f402103046541c210040794048001992010b0a8900e01c0300c03c2c10305c44000204200284007032a15070311120300824540340a41c040003595854051540c4150000c0c0e58561020440c4010b000d40e502030300d80c5c84004918184075650f03850b5540020007110380001001d0200221b903c02241d90703403540d49642242052424800742c20f10480070048403446e00c0c902030040d401c0600f142c018803c22180c1a001d440103140d03040268803100c41c00009070781c2c05020500300d54810340704042e1507041c80ca002c141b010030b00741540401e400e0405566049070341d4804c41c107041c80704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 7723964 1250 7722714 7722731
    0x10903080702060703120905010606030e030c0a060c09120f0203070506070203030a03050408090303040e040b01080102030106140702060d0507050310150e0108150d03020a14010506150a030603020310090204060504 93
    0xca090380d030382660540b03015031184820310b0107480403045c1c0101841c096240540c1c1e04240300054100038200c0e00705881c01c1040c00b06807e03050b030b02ca10414084800d580d200540c80c1c800503e49501012070041b00303181c11042c6680700d1203002c40f000b05a0100390394480c0c02101d8034042d07203402d200d2a401881c048455a00d0004554082900e034028900d2950502d55204000b4091110704d070119440e0300001410b9950350740d15601b1042c8504001d960a43d5011810b200104000d481442101d040e2205602c4507012101d20546044480c1c0c045d8500301c1c0c00038001d2207150032420403801458020302c5a0740380c5070b80781d03d81900900b0000c3c409a1181d84000c081c151080f100c6508007048527440e60342860b0181d20b503036400c0c1903001884002400e07250001120700720481030540c086002c0805d03034030407082034942e181148a460701342e42003540c50030b5000c000e03142450a01411309004150329030660802051280d0f0301d80000e4104540002c017030030840e84400d0310008614181c41150b020b088200e4042001c5a07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 7725214 1250 7723964 7723973
    0x8010e0114090a060306021b010e060403091521050105040b010306060807030903030207140a120504050102150402040914060105010e1815030f060901021c051e070302041e0311010903 80
    0x15100200600030b50a120118007078144030341020b4041c640203102559960107100c00001140e88541400045510300054507103190008a0001d01840d09603494041c0786040040510410000c1941c0405000c0882c0d005c9018903000e07025013200400e550300000d910740c03421091005480d40b03d40081d0405161000c24440280c110907030541181c0c203450002400d400320700e403e070001d2080900c0a80505003142c502520a0000101070749860701c00d240001d0480e46207401a02c1c50300a50180c5405038114848015030840042d4105038082e00080c8049018891601c1705c0508000d8200515038580103038006024558000d001e0300d8000c00b047d5400d080810180c500100c04100103840b041010740c2c07040110600c1c2ea030801003031602409220a1340c965041c0381074994000d40c001040001e004100000740700102c9250b1040600c699040c2601c00b0100300592001c241e0851f008010105150f42440045000400304007900d40800d08404a29410790031030800280d14621402c0603410081d820308240001f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 7726464 1250 7725214 7725239
    0x50907021f0203060108150a0b0a0210060f030302070501050c060c0f0712090503120403050303130203030f0406050d0f020406120c051b0a020a0f05131a10030504110a08030901110c0a030305040608010e01 89
    0x32640c0c044070362b40b107080d0544124146008400e510310650300f4560f000c111000c222082600704c07882a021100200d503150015903403801200742c02c01d1660040000101c2c00c1568000a060464180014901c4c00080c0e56444510124030028440050600382c405d010508007080311011051420a038507051910f55a00c0a5880c8030003440c49000a520001040c02c6490410907510282c0250a0043d1600d85803d00100203130030880d82c3d403803160304080240408541a2084074199245682d820054606404400e0007900f0041080402c110741000704000704000c1c1c09070700c0c542e4080d48014221649040c0108015010380750001400e0b044030801c00c0207140c1e1000000d0300d070740141c1311001c2450f0342401c6041000044000c51580c1000c00028032803646035040e44400d22680c864008800c5000c08001400850070b25801500c0141d031082040c07020300d40c0102207081d0070760a03070401c4420340100d0001103907030341e699503000f01c011510200f0203002d02d0342c03c004443d001d8440c0811141c55903250018103910b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 7727714 1250 7726464 7726469
    0x9150a0905012c060c0a1202060717010603050601090b180103050603010b0307030f0311060a061d090303010603090206070804030f140604030203041a0c06040503040f1e050907021f0203060108150a 86
    0x1150380c00140e0086910307120141c1d1110170721281510662502c608151681106803568800140200700016184074000c0c0001c09442d0080c40c04803907540c1c2884001d030010140075000314107000582d403000a41c40403110043c0384440170b04078903600c2c400c1d80000243c141c2d40054034191280e4140501c09a15890005a50080383d03082140c40f071505111b42001e5801e44681c421041d001d00848042204070421038101d03004603480b000b141c40926600d9607404101e860b0540c1c1d4001d441c1c000b04010010640300390040442240000c25032071070300359544c2d519151a0f002da03001b2260081c2801040040c80071000d058039160740054058411443d065600275242e11a03400303540050b42d030210b21001039050b2034041d91026031b0058200d4010b03041c0360600641d25005407050035448014800d004c5441d098610040c0c07034003030707a442044032414100810072800c0b4200400780e03000c5104103288007040140c420301034103040c9917131500181d49080c044c0004019171402448095000404401e1855a8403a000803070304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 7728964 1250 7727714 7727777
    0x705010306080a1e0812070813030e06090f040204080d080906010e0a09032006040212010204080303010504020a03090b190506010306060e0906031207050615090108030d090809150a090501 82
    0x8902d5410881344038801c0350720101509402d17010420880d5966140710290260425880304500c0d5640e41500110048100ca0001c0014500414041641c101180500360040008280c1c1a8460850340400c04903005980510250b074419038030f80c041d45400c0245a900099001d010b4100d030741c141030000703c01246c00f40080c408141c2d1603a81c14281442500701074814600e10840c0101d0041003039200360350300301c2135078168420360030741ca03125480d00c40510846086904c403001841c02c6d03030701c1c0a040000079001481600145502c0b03141010000b0b040c0080c09110360070801d840725604003351626002c44a0081c0790b28103162403d2400d0100d40d40042e98101c02070011500c0001542e68000400e04103802d4101c042d11a01e008203040e0100607020131020b02c90b0707200000d810490101c040410138000400c1c8103014040d041044214030010b400d4001940203800344175000d140c11101004107546500091941b0b074030380c80c049928128075070b00035000c0000f4107091030320040201d9805070081c0e030311007100038524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 7730214 1250 7728964 7728983
    0x15010e070203040f030f06020f0a0c050105160c11030a05030a020709060b0307050301031e020310020a020c0301090b01030b040809060f0a03050a09150b0102070306020d060609062d0201020712030605030705010306080a 95
    0x6e0400030740e40c04a03030807039802180d0940c403901d4400018040c0c2405003c222011b501742400244880038071512040c000026070360b8098100c0701500c9404080c1080c161181c0c043c010700003020082001000180400c09203a030040c8140741c0751035110000c6803526001105020000c05c28007803180da001d82600c1c15241c1152510404005800c100304844001c104003d4243c041d045070326412904603405802140900d80940f50b249014404042c00c950f00b582c00100602d074080014808102c038180c485510511900c05149841811800140c0780e42240c1d6a50b015803100240114050307038107000f040d030850b41403401440f581e02c190b5212103210314040c55142e2203c1c3e40c2c0110301c0c1160b1081000030000c60704402d0455850411040300c4018280502480b07000c201502c2000401c1441140b40455804e003d507403110180c3c4040780d0100d8a003780304a20821907400340200000b00e41106c4c404103100c40300fa1000204280340200381030400c01d50341d101e181070524084040000c402c012580b240c0b010703031001c41d00307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 7731464 1250 7730214 7730243
    0x30307030e030903060a2013090b0a12050705100201020c06010b0f040909060902030f030301060203031f05060d0501030b0612030d0e011503060b0301060e060d0b0403020f15010e070203040f03 84
    0x1490b50003100400c96044c412401440b4104c1d0055010031034080c01c9135140040c0000003d410902c46c4940100b2440324644000104125592640491360b042e600501080b00e841d5030f0481001007000c1d9400680c0c241c0c11080342000a841e001d41510300b1040d50340020f5007050703504018151503880c14460205207040c0003865a001c103c4003c03c55001d00740d080c034100024025030410100a202000c0101d02074852210140071140703000095a040301d0740c1da0300035440c540e04c540581503100c64050f01061070a040c800045010b80e074540140c4191000781d803000401c2e6146d4105042c04c454080d1140f40203002c003e0f200481003078040100c0f102404c03000d1004c611029590580c50042c1600820413030305038500300004c02008010b82018803016011402030000e00e4942607101380d602c409407141c942c030404a44c021400190401081684640a8010345074441c114160f0f030780c105520602c40c010321011101c0103010341880c2004a80d04a11184001c500f01400c10006d220001e42c00e000c00307030580c80424904c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 7732714 1250 7731464 7731491
    0x5060915011103040b0309010c0503040206070f06060302090106030c121802010503100509180106050405010b090409060e010c05041d06031e010207060606050a12090b07120213120b010e070203030703 87
    0x2000070b00c1d8000d00c101c036070340c666179880b061140d0000d4905910303550074220400031140c450415030780281d4004009616000c02507842201c0401040c0d01190780c1903d910f4000056039903138520600920325030320003042c5050b03201d1004001d070b060131102900051501c643c00c005800c0c43c40807490095428202141e880c2c5408180c1d807414101741e807000c2e600c40103030700c208008200c80150091944403042c00034804030340c0ba0400c201c291a02402211100842403048108900e4503402250596020307110001d250340f400044a401d44440c100d500c0702040d40080c5c2085680c6150f0070b40040030300d072034074000024284003000030748400c140c0d40c9502001c000d2001c0e800c200c10b402e50450726402e50000e010000c00360345250140c1150414600c4501060030804030043e80d044a001e5134044aa10168265007680c400c0d00581d001170b00c0c044c0390000d05900f407103080c8821848202c00c00c0541107400c6484440080b42c9042e20103000140c10013074442c42c0000030b0100b095000803d503038004038241000b08054503401607 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 7733820 1106 7732714 7732727
    0x1005010f030b01060f0e060d180303050108070803120601080403210f0c0804050a080a05090405040503030f0912070209130f03090e0a0e0a0623070e01120506091501 72
    0xc5070602450b00c1070003441c00c1c044504001800a0541d09a009903889e140c1048012903038031001800148010000040140714071001076103404500c0501381c0c0b0030320010348801d0512031400c010908043c0554018507086207042204a01018407440d00c00c040c0003c100b0b00a82039183c400342d07101003482149994802c0e0742000043c80110070654503114264415503044d02006000e010002161b6a80d0041602450094004580301d00b0010203268080202810039105544070f04810005034150005540f03107a501100d110542e651241407012254450172002020749511400400070117820503000c4059510079940c2b802566902c428541c100c401c00603205050b075015120280004150380c20441030310340300c080a030802c3e1202031801e00d013403d010fa48110102383c0b10700100c032032541e2084d20744882075500c5009000318240344002c14040d4001902c1004d032019040100180c60340110b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 7553964 7733820 := by
  have h0 := BRFrame.cov_init 7553964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7553964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 7553964 ≤ n) (h2 : n < 7733820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
