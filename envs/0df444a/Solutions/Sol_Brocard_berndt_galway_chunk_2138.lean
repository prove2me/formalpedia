-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:45:44.559552+00:00
-- url     : https://prove2.me/submissions/35d845ed-64b7-4db1-9e0e-a07706c39b47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 384352517 ≤ n < 384532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 384353767 1250 384352517 384352561
    0x306064109090106050a260c0f120709170a0302100218120102042d0605070201030204170c101d100e060a03291c080903070305060108010c02031e03040503040b03 71
    0x40700107d0034050340307816201d603c1164119885003070085290b0781041c5014091243d00c1e0004c0764034049083e41c41c1020340e0011555400000c5d0901d10074000c4580411025409001a8000340042c07001c0356800f0b5150b01089512902c19075020802810f0410b000ca02025884030181680565910002c0701d03601039841400b80c030311104c041142c18040d6640c00d00100c045103581d2074500c0440740c2020ba0031210380e88a40b0040c0c0c1010307000d01c000310392001d106c071100305059000f10050080c11101410712411003400b85160003402441003040750341c412070700ca503101120341c2220311001c07881c2084420f840300f481d040500c603000b0801081030068190960301c095007613044110000e0300d005028461040b1500c00c01c0001c0c0e04144003c101803081c00317080300b581501e984940e00c9281042034500200c1d1604810764000d8850350b0001004012003170b028803410302c101640f840503520780301003070b18010700100c0e07040c06103401d2140020004041c00030900585001c0e10f040c5960617607a06100e5105c04100d40d80813802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 384355017 1250 384353767 384353777
    0x2412021e0303220e16030b190b0d2a021203060a030602091f030207031403040f02010507050c0607030e031c0801090903051201060306064109090106050a 67
    0x2414015184811941103004001c00031407801610280003414001d11500c0340380e01081c1d10001084121a104006100d0101c01c4034540e6110b1a1944c002d0070f0300c202d42219030154281e803400c41ea840b542c6031403603000c1d1902040400d646410200211005114a8600e0001e10715402940c04001c0c1022440f50715510301c503821500e0500c2042c80c40356442c4000da55080d405100d443c0200009500f0350080c2050550040a00418101c1c0c602d030341c03008030715000042000070b500180c10402c054212030f003940c0b00213403c0039850451400baa0b407a041051b280901a05102000c03404108021003084a050300e25400342105486042d54a0048e0045000710790300782c800c0c001c1c4c1d801090054004c20840200380c2c00c076601c95445034a4a0042e400a00d480c00040d010407104002c030503503000c05120701500800d0b4640c1d000030000d103010700040080148880700645100400c0130b4031150691210348a034031120523042e21500000305c07055070b82e00c1d01c0340100309600010401c00010315584c006010700a00b2606d5112 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 384356267 1250 384355017 384355039
    0xb07091a0406020613061416030c262802030a0605060a020c0f010c0c0b030f070203160b0c160c05040b0a0305070311030721050c04050c030703241202 66
    0x44200c0e00940c001d010041e80003000268030780d00c217000200c0f42c0078000d042c009101445038203049581c0500b00d034031140f42d0070200780c10340710035501d4400d800b0700c00850f2412036810150350380b01510341c01280d042d80b602a80048045607001041409410270340709070b80c1e40b0302e5880d040c00b80c044000e50421149003c49a180c04000101d034206641102d000101c0c42c1e0142200b400c0c24400c00c0821075450040c2c0341000072503501c46000500740003844000d01450f032010758580c90204010010074500801c00b0b021500140545e016018556603007070905036208005007450313503800c030041c5841d02070785110500c168a00340248040c05140c0a192040d00c8050301c0620010301c4500074044140181c2c44010000e904c458001c2000c6040c1004005000c0e90003800d407000d40d03684203a007003c5000c0305803200c034a007a40d401c2c2d6101044010042811100c0d001d813005c0c022454030000c1d4440501000b0026000c1c5512000c655a02108902c09960040c81c0d285031000c0d03403900c5d406440c08420010608038040d07014000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 384357517 1250 384356267 384356309
    0x130204050609150405270a170a020d08091204030f050c0a0506180409080c340902030907030506090d14070b010b16060c052d0313030c0b0709 62
    0x100d4402e03c0d40718000c00e500c1e54210b082c0401054000c0845002d5201e4071080d40b520000c2d8024040740ca4207050080040785a9414a000200003003040c2c40340d550f42c10800d4001c010b0300444d5446100189080250081c3c0d14042d01504080c050186041190400100030040021206080e041c040c0285c0850389070021440520010742044e0143e0b5a1003042440003000c107110981c07601080d80000381c0089011079165032025031a80103041155055080b90710b032039944500d0340d03c5008074900c20307028040e01d144184010040ba440180034039488940c00000054000108005400089d6803043c2101c4861030607051711034032080880300150000b0490200074230781c88010f409440c03075650011420300c150303442c000800304140d229614002018035540e5025010a1551143c42580600e41e20b900c2d503641441c52030100c01000303044084c3c4002c0e1001800c610301580b080c0c1940d91001802c01481c00c2c40c0c085050070784100e1000c0c6402080104500c00f00a8016070000e034030003c49030000e6016482c0d1002c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 384358767 1250 384357517 384357529
    0x20f0d1209033f0c0209012301020d0203190507020d050a030f0206060a121a010605090102101e0510090c051b15040308060d05010f0f061505030c1305061204021014040b030711061302040506 83
    0x940c810018dc0c0705000b00c4003403800e80000c840a01070740e418054648441a40410400c01050405456580040a070503040c50782058182e140301c0300c144081c2000d45020720028001907218000c0400214084003808200201505070301400028601864000c1da0b40ba0802000e90307100d00340150041c001c914401586220360701595046840304446e11903031040303002200f4000c04006000f8106406010310014183c0c80c1481a01a600d08907680c245d600d9100d5a200792151402840e0044180e029604642031032034136080c003e40040d40340c0b034030700d160307440b2400000c200c9015141c000d0300f40e501c5d1003040c81190110340c0c41101c4690341048203202455907500701c0d0440e10441c10039880803483c20000650240400001020041c07440001460a10303103401c0850016001594200200e08d408000c0c001507151000200c0d8040c0d5280c0b503e4031680000000041140c0600c0c0b0584600b44001300109030404d0191906050200c0d00b503045600c94030344030740501c0c004c040b20242a805030b0302e04400702d10b05051034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 384360017 1250 384358767 384358783
    0xa03061d01150b03010b030a090f080a020c06070b070f030e01061e050603010b0a1b0c1d0c04051e030304170303010e070201110304020f0d1209033f0c020901230102 72
    0xc00443c2d0031a803a0001c0303008a81d1000300465902962006060300186580c982c2003090b038010710310240c4810f6176a1003e40f400781817110591242030140500c4002585e007000003035000c10b441c54402c3e600140d07680305070050a59003000348019400d059001c00d42e0b04504404007042c0c10010194000181d0300c106000c0320307100038008c0c1491440204901c843c1d450090104020118003905283d60000f1180c171b50745084003941e00304928080381c2419969204460701c1d00250040c2c491071410346010303d88800110022a1006042c5074581c9040050300607030307003d10a43d0002c01144000070001c50585424680300e0380309019403254501ca01002c98407240c41441000074030840558002c0c42d43e1030380e0302080a10050690095400705221000c000061091055140507940d1070301c64500c403504519021055500003050603018034081d45200d0810310b104100c42065420b440342c1e0010f8040c510404440c0c0a41440d8082e420006c8880006a0f46181200c09440407000712500300d0b61300c0714000120303101d501c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 384361267 1250 384360017 384360029
    0x3230a021e0108241905091005040c020f030d0f020405060409050f07032f130602010203070e030f06010e061801080a0221060a1a130e1908180a03061d0115 68
    0x701542000359410007172800300e50110314041103c0d95545d00c00028a16880469003207215450614081009003003500075441c001c003041c00607008031515003072811b9a0340a40d0302c8012804d84c44141c2c8d60003481e060f074100d5015200c09092165960303100c580010290105a84040401da10980001d0095110b0b11403031551502107600d004c86080e800d90b1440344540e00e0b00c0c0007500540c0030895100c2203a1015800341c01807181d41c0005d6280c1c580610060642804101c61600a0b0001c41c55070101c4d203004500c0d01e064030031442c0c112140c1c0c1c6800020540c1c80c8000da655070b80c0301001c1000131505120014958003624030882c2d2084940040c010741e0288a02079211104a65000101240e5040001e421100b000012000050520701895000079101540703044ca00200fa6074903100603580c002c017030000c10b44414858031440c8c086045a568440c040c441c810348007402902e5148003034050b07a51484441b005540080c0180314007540c003040000c5003800c01a5004056107021180070785000700507540e10456803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 384362517 1250 384361267 384361321
    0xb090705070f0f080d020d0b010e0406181107020303030415050a0c05090d030203190810060504050a090e070506120915010510050d0e03040803030f1003230a021e0108 73
    0x221036503600e80003020303a400840c0c02d0304041c405c000c3e090b0b04c50f1001d1304c810060b402c40855820b401c3c0001401e0807404c2002c550085007008420310070408110b8a000900740a4440040e2403001c0b004c911010340151900250b00d03000000a0006005800c0c80f4007110200002003040291181045d0008895141400304007054051004401c903184c5900101200d5002e401940c1c03601002c0c070b0005801301e80000c882008100041c00303000410003055010009450359081c642e1400d03040c00c000030038010440c41008030554842410040c82c13101844000d00800340075141c90380703603007918003080401d072002c440596807807241e201c40300380300010170b4000c5040300c401808841c9501e010341011103088d800a22807118181d114401101540f80810040000b40703c01000755403241025806462504000f400100390300440b40e10034400300b50725403005401024200c1c0d029400c0c400056100341800700a52000c0e51042444412000440f0360314001d04184c02d090f070750143c06030f0300d002d0f00503604c080403011804000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 384363767 1250 384362517 384362543
    0x2a1503061508010e0a0e06011206050903030106080c0703050705030a05040302040b040527011404050303090613020303090d03111204050a090618090c0b160606080a02100f0516060b09070507 83
    0x484ca004484c2c3c01041d980c0c80071652050510006c0d103018000e84c0800700b40317240c0103001000e000712842031a81014010001e9465075250000043c226032015211790701e181c00005024082601410460b80b4840e4084180c03a00c0303e00d910000f9113940c00910059018500f06210184c6501c5e15100380b6200d42d5201002d60080b80075829660000400d070f070072085142d035988417905a600e178106101c51140344550003e5640c0d20302101d500341070101c05040e140c0c0e0280032032500f20040e503010007a1050900c050740c4500144056040072a241c1910f2444040503016407110b001c1581c412400910a503181942c460287d1955070000c1402c8403440e200c3d02180500310740180c0c0c91985076801c166039003070080410b040c40944420841603507900c940c00841800d0120b01880080080074041c4800034151940500b140310582d40201d003d90b0030444803101004032000c2014145d82c019400e81c0d400c5000c0304940780300b108003860440e006082d491680780c410f01c080d00000e20007038410f004441c1081e6118074044220 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 384365017 1250 384363767 384363779
    0x14030a090b0c030403020d060b01030b15070b070509040507020d021e07090f09021c050d051c1d12070507090b060a0804031202181008132a150306150801 67
    0x95003182642d418140010440000941e49051281100c0d038018600003c6a04880300003400b1a00307400e01c0d8502510650f42e001c800c01d501282074500030b86c0c00402503103503a943c40360300700c640348641001030b90700c240b80605115119a0004615901801036002c55107506a0140440c40001c20301d0444072803640100c801344590546c5400071075000e41a403502059806481d8005009c902c084081600d5071007403042c01e0403d0040400c014031804006040c01482d025a410001e124005014a2058101d88442d240c40c9581442580000c5035080002650f600110742a0b0b4040a40d000c1c2105480b107125090740425042c0691040b4000564003c202030315008646006550101004100360240400d003220000891554001000c1c101e042c01100c000d0040d84034200420305070311155820401010070200036003400712012084c411074110121441c41c910355403102001d0141000f03040341900002d040020040300302a0004580511500c06020f41c82d218250030680c04030304580b00300002c130040010000c0e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 384366267 1250 384365017 384365039
    0x18011a0d080f0a23070f3201020901111c080a0b031b030f010b060d150302040f0603021e18072606010e0d0506040206160510060314030a09 61
    0x85100d100024144011818244a0783e0028465200840d4001542901c640c266101e00c950309058088080d013000d0198464000150b0100002410501108040040d0220310180240d40311103007100d0161425849002c0d03400b0b500645030050105010a4200300300c54808900c2504041c05070b00108068114980100c0760400003a0032088101c1e981c64161000b510140444090402200094040b10840e181070515012401062500c0c41e40361520010160340d9540845124069140c400701c0d0740c41d260107403041c054806900c001d50051902030300c44c0d11100560030600807640200ca041101c1c4502202c0b1460598908010960080c44414010080040d0061450704440340345001041030200103086011045210003000001a454080111641c2d111000f4030704100d06880d500c02d400c03585d42e200d668039400a08001d10543e004540300c09440d015880020700c2e00c0d0818200d0380c038114035503c400300030000d40c001510b02d403030161503600c00c400300007049444414080d40d41d8400305203088940302e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 384367517 1250 384366267 384366289
    0x8030307180e0f061216030206090f09180d0c08070807031704060509010c050403150e0a08071202070b0c0316110d08030f010501090509070302071a07020618011a 71
    0x8140d001c04240440c1206212182c0b620440351005482c1890a2850400061008507034045d2650b500281034403980b100c0d482c0310300f03040340c1c3e0503117005448441c0140011f08100a444103140c001c0038020070828180d0000744a030382d1441e2094240d41c10103030344c0d000c1112a074a5500b009070202804005c42800120a840148071680c083e140140d00101d100102035071858003030307a090754180e1301c500c1884035082c82031003104401c1c540b034100700e4502450b641c1c5441207101161000c4d0410396482c40465100300742805000d03100740d84090034076660100ca10342441c1c07800a0648280c01440769500c00b1900a5200c4100e6860207415002181810101c501c40e0150848800048544072441c1c1d0f059141034880310540103c0c544520a250344170f01e016510340042440c1640302504124030300200300003c1d240c218000b5007080041c98090307503e5045080000e00311400743d1000b0810700c1420204140107a0100e6114081c1d00e85100d4040c1e4600400503035030030780360341001010410521602503140e038900114505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 384368767 1250 384367517 384367547
    0x304031403130804080a030314070903080f04090204030804060f05120c0702030703020319050105060a0b030426161e0b0105040f0f020705070609080a120807050d060b090f060408030307 81
    0xe00d080b580d02d019a642017603118201980c80b6240060805416000362180c450008503110011300e4240c80c02040500107100180001c0400240d56504507046000c480150840e04010340d501c40c4d5910381404164043c0c4100c00016136200701c8501028400e004441008114180340700381c54136801064800ca03401601d080780d15100b1003a0010050301c0034840c00340103d02558600029040c1414a1030a66500034113980c03040f055000240440f0407104180c0341c02c160031020310301041c00d807400392568441f90800050201c030000724000145130144407403517074014231903085880b40030210301c410142486010710042000c09000014485030404d68030290007018180b10100e0384500511265040303174400784041d0f0301da4100d440706015848e004440751000301466001030a0381c900c1500d40c000f0300d8294110790001c10808202050001d84100c00f41d030b024024615081246c59035800e04246190b000060081c002d0f80358615020580c90100f050320100c5507800042c0d032855641c0f000407106a91840044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 384370017 1250 384368767 384368791
    0x20f030a14092e02010e030712090e0c041a0c0705040507050f030112060506030d2328030f0c02190816260406020a0209090f01020a030603170304031403 67
    0x10301c44940d5070100c0c0c3e1802002110011541c1c40d01e61000c0002215152803182c02e40e810140e990000040000c03ca42c009604030704560138603207505904588421495000ea050020180207200307400ea0780c04001d00c111060504498541c00485298041500594100f503155400a0204000500301604a103074080701d240f40052618072f80702c40318071440d042a0890401c00906007140400c0043c20300c43c0c1500444110010817034001941c00040000b0b01c0c040036100340e98081e1081c440c40360080000d8a0141e0020380c4000010300c0d401443c1e88035100e5891a40001070305144818103440e01c81d20610141c00c9107a1302030010746846171446228100400c0c0201c40d005030400c0f0030290810b11000340c41d10544107d02908c0c002c81d91441060102541d00000e0307a485c001040108081e54000400e45078042d1305541d0f00442eaa240c02920b403d2469641001c03019500001c1c0b4280c0042d403652120042e81e205005507c40311024800c50400380c042150000c02003845076014042d00940d200c040c6901c40080d00c15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 384371267 1250 384370017 384370027
    0x909020603160302160c030512090a090b153108030403140c15071b05090a0914191b03121209050a030503060f121207081204120f020f030a14 62
    0x50000042050500781c031214610301b801e00410105120200c085166041c4590130072000c5000100030300903d12502001c25030318003101009442d0144508910070007400c84a4513820400782c07464403007450842401645005102d10780d80108445000025901580c0007182003e003960350780301c4280540b103424455880b070604c030038443e0740d02d6440504585503c0c1001a031141c40b80d2801d440da400140d248614908580c00c0d0030f006584818201e560700504400c0d002c110003115080c04c01c03410701015140081405011100320b08040d401c0c45041a55201d0303001c0201c0d04201d010102600d998a000040285440792400a810341c498140d4590054681030001070802c2256503141c07170a125944101c0205502204000740c84c0b8001ca114030060780181d981c69000740503689100e40b40c02040b240345019460104824042c0b2500105032a076034060010607141a08050800103103100841c81680001208034904a030307042c0c400b042c5107000c5580a0300039802e010841201707595010756410342810300001400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 384372517 1250 384371267 384371287
    0x201110d02070f171504030c0b091614060304030e01050f0a200f0c09150a090501050319110121050f06040b0f0a030618080301150206010909020603160302 68
    0x20000d4101049500100a914a00500030840c8031880e401806415101070342207258110103d0707030700d110f40440d48034070840740e40303921381038510350322030a03025100002d52010405181c0300000d411000c1d0f07080e06006090a5a03800b0680070702140d0701e100c1508210140007060009005400c1c10030300f02d00504115041920002010a05403c04507500c0009102000b540d046000d10480389104103414401500d21417070301c00c044580d2080c034090301900400d00d55002031030346c4180044a01d4582e00080c904241296174900c281e01806080c0292842401045034200100c0120400c035071015a100d268031406c2d0540900549552455800c00410300708543ea041e014106603108440c403541482c0c00c000f205042100500c4101c074036240c119070281e0070258804401d9a680390b407200881c1c0e4002030214000d0300c0400c0884c880c15042d80024044d41c0040004074030501016408180152940d088821070303070381c1d0312081090780c122010283d0443c401300f01151043c41c3c543c400c0000c8150505025140a00090b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 384373767 1250 384372517 384372523
    0x40305030706050109060506070209070e0103020d0c0306080705010c0b0f0604020714060403080a1a060904020d150e0f06060a1d1c03030509010e060601180f06030212060306071b020111 81
    0x2107012108583d80c1c20050000501c144100030103080107880044c2080496030202d01d81c1c91018052909200140c0300e2142d6a0b0311a404540342c0000c200300910000000e08405406442c06028510b903038000c42c0004101940300e1000c8a4000340c2044541810b41c481d500c020f40c0c4000e002d00a00d070400e80801118000c40c14918245038110840e000900c0f40b8506810010404d04000e82407140c1c550801c04843c2c0c039815074080c200000300b42180c902c0d81c0d448201c00081c00901c143c1c0a00d61815082101ca861240c48544070301c030031102041e40320303140c1307a440d020710018a40080780c04d80d034003400a000501805104d2111101d1640f21a05a010301e03c08010000350b202013010924000784081101000c00c06615000c0c650300072055000900403000100d503d540c49034001000355042145090007840c901c0b0304030780b03031000a02081f850044100d440c1c0000401070341c07006e4185d03880c4980e50004500c40c0d04000030b9142c40b600465854103d1440046800404180640401ea0402c9091050508001414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 384375017 1250 384373767 384373777
    0x20f190e0f0f0702010b0618010c060905010e06130206040909020409060609050603190c03030f090f0e100b030622090c090f06060906120507141c0b03030721020304030503 75
    0x14611401039840c04803819010b40c4401081c0b075045904200d041e00d184d0301c0d044244e80005154045040305d0200e0100120b901801d02440500f045007403c2d054400e0000642c0b0918482c418135003034400c11f5403000c441d040a0508c220009400403000c2104010112040e40400c030307400d10080011610341d210341c5550040d12038a801299880e95036000f40074003842c1c104015034000d042c510720703080190700e144c0720400104014400a07080c01585d400d42c0e4a0316128a4402019003281c61031010801e869841911030020212210040092a5903012400c0c50545007600d200301d000605000464050b0f079040610f0003004024561265107501203200040c40d2000928041d103c1c4540000399009507201b04000d982c00c0368498400c1c044100800d010075039014141d41544016241c0102d080d49501004035111307640410241707001e00c404030b5400600d06c49000302481c3c4403185042801901101e404254a900c580c0c140103124a8040c0802c0c40e0414140d9901c400485003401606d040c0f03903594648034295440303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 384376267 1250 384375017 384375031
    0xb030d0f030b0a0b0a091503180605092a0306010b0301140d02060d0c021006051008180703170a02060f010f090e10090308010305060f06010e060d06171018020f190e 72
    0x4900b0042c860203101241e010140c072400e25007270140140d8182d01c04c20400141c030000e0400303038072200024001041000b100300d901c000322082400d454610744001c596507503101c032070138842c0c050980000b8080d0041c3d03050704d0594400c0c40d41c8042040086080002005000b442260010401d02c030030700c0c0000700b610a031080803003140c024020144190b0316000480d445500b2680c4502c0c4540000402030b0707400000c055100003408410300440c80180e440318a0004164001010160304581c9840210481c5000e40300c4000e4a80031244941c0701c1849040319502c0074003035502044c124040401100100ba008080000c010340103840001c2c901c0c0034440706803418014183c1c08614404010400c00c4402c1000710740c000c45000c035455681c00e1060000341400d4200030aa13215030741c0451a0f003044861580514014004003848d01c1c0b89240c2c001c0100e44440056680450140c0781c02e05420b8159021107005264990050903000041c456408120058a194409951f2480300c94008181004110f04170340c000c0134 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384377517 1250 384376267 384376277
    0x90304050307090e061906120807020f090f06060d0608160f0909050a0308061c11100309020607030809120307020703060b011803150b09150102010b030d0f030b0a0b0a 73
    0x205200a040c40c0c0640d5074000030f005480d28001c408158404201c03140c000701c007469803890071800040c01d04040c1c442600001d010380e170054050410000340740014880e21f442900e90390760940e41e110800c84850380c21558a01a2803181c2d00242d128500346009001c1c241c251400000d9880c0c545c0000c92400200c0107a800c0d4401095005000904400b003020300100f25a403418040e03608207940e941c0d1207a020143c01000c2c8500e1002140003a070740c40c4401075514641705140303510005942000e80418148800309805800e07203603009581548640504051681c001d800589031409c00c0e50101c0f01e42000030003000c2c140c002c02d18221844000d0030000c600801c80da5004020305400e50621300121010045c0310340c103000189000201103103002516108607a00026049445001c5c254540d001c5c012120303480350b2040c0000c08001c050343e0115075201d48417100703a0080048600d00f0b011306a41c1d1701a1f01c00c6002052081c0300092002c0d100e43c00004041d0b0001d08140d0600360303942441c0b000c0d034101c2040400414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 384378767 1250 384377517 384377519
    0x60603050106050a0f06050d0c05070b090a020a1a0f07060902090903090a0605030609071409042a2d03140405030d14010506070602071707080a020c0f06030106031a0603090304 77
    0x1c40d02038000400f901e17104404000c0d0500d0050b02a08902c10707843c045240c036031034504540d01ca0740250141c4070701e250854001c070280e00d4002002ea03150100c08804a12400c1a0f190206401a40352040314140c0c1540407003924100c4d510007492120380181201325042500c500e0722600585540c0d0881d030141d2800402940c580301428200000204a6042141044801d004120180c2d80300a0906c1e0865a03e0038100072045900c115000c6600c1041000e50700241050b099044010701c4240501d4007104070702e180e000710138401000711100d4091003aaa94018811581992108000300000d08006028100090076881c03003202d04031105422034068555420120340b100c0d000c0c00e18003580000e0f1011300c01c01c0c00305605001c0024914024000c0c0586050b47c0890f1800401410301c04030241c120b203e048041e140c2d003036031a0a8000354445030380c0d8001405149800115814501029080d110b00204410308603824500114001c10b1603030401c664194440841c4a000d8964030010b50060010300050b5a1300c0e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 384380017 1250 384378767 384378769
    0xf030f02010203041a06010309050717070f030c1a040806010b0a17040312090317041112030301050d080d0b040e16170703030810090f0203060907030203061003051306060305010605 79
    0x1101118064206690040080000040312685407003460601c02c42400169190315004a000b0402c1e072400500303500c030300e4a020910b03e030f4400040c0d40810f60030048691564440c03005201c0c0000610000b80072008403030060109403404400d01d610b10840d440b030741e810b0594503060320385064001e82c00b4010f59580003130940c810680c85401c00040d4414ad1840101900741a07038010080c01000548004140d41c40c0c01650802d841034046110402079111400e101d4201804d040821b0400002400d01c1442007600742c120303142000c4241e81c1201da00803c0d0408a40c919281c0741e040b54800300380f0007043d42e6200000d80713060ba82e0388600c0d03015045000003003030407034606420042e0280b0190410807907240201000d0a050130300084100030f8a5052800319020307154400c0111620183e07404c1008882d0071b020110030076800c00d601a602c41c820031a624009a202c0100c1a0201c0c032080c0c404e550045000c6030061622400380d0001c1e40c110818540e241030800440c2c0340c1400301da05540084030036075100e030020829 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 384381267 1250 384380017 384380027
    0xc020f0303030702070b0c030d060305030c0f0f0d050a03090f060501050f01140904020a110f03180109060f110304170c031516031e050a020c1204050a0e060a120f03 72
    0x959201a4000d51940c2050040a9501ca41ca489031100c1214005995005801c1c24810b4880040e900d16051200c10703100c0c50801c0c0c90342c01c07070800c0100d544210f210203d4007042c0081c05003070181c00a0007411400003800000c8904d07900c848500c83c1410f40b10b030840000035071242034485026001ea40f00155550504080184010728a10b032241008078040b040c40c4410580812200c20700c004a60060b583c0301c000b24240c8406060205c601e04a00440c7c0200d002e60601000070004080c16101480b004410030b00159420715007405400001200780c2e60a030107990040a050f001c020782001100e0070182e8072b1401c04071855503d0307404c50320b03034201226160305070404119452828070140c0b0032900c18641600c9402240b0364210207903040544420029824040050b08014807d10b10242801a80350099600019600481501a4520400d108201d038582c2080a03101920801003511030b407e441d11482030407007200540742c10390100c00a500041c8404200c0480300840c0c0c032401080380c080c00e85040c0070305 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 384382517 1250 384381267 384381289
    0x302030a0b0307060e0103150b070803101e030204200d021c091a040f060c030b180721020903030703020616030216021002010b04050a1a01091a0f070b04030c02 70
    0x4060f50040806202464101e854106102002e1070002a0644482c0e81c8981098265002c4008440000340c06020b21122100031841105580442c1d85a641e440ca02049211b0701c00d215004804c440840520040c54550003601e42c0d040c1d0544480010911425070548951001c18050302039039002800391120480740c02580442e24604508006203112500d4103182c141c080107003000b400c0c45460006042002160070070a55a0300103104001404003210301400a0590405c00751203001074104010079011140c40e42485041c3c6030341d404100c1802d400c5420f0140b1603a81c1144640b540034000c0300720741d440410147c080c0501030703801800d00381445510368050680301d4030480c042500420592035800300c1c552004034180d9060300e00c0e2489540c44001280103220680e60103038803d040c0f005200783c102c001d800c440c824840d0b02c19907041c00ca501c400150f9600750503220344800d246007502c1036520032298002520240d010048400d1510180e5a9031074201e81e0201c0303084004c501c2d588915015405d0800d4060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 384383767 1250 384382517 384382519
    0x1203040602010e1912050415080f0f130623040f0c050d0c03020105070312020d29010206010509060f0a06051309020f07021011030408010504170a1b0c030c060302030a0b 74
    0x1c89018413a1452601205200101401d1116942c100965452203003080303d0040c1222640c82031918a80000100040c0c010742e40740071044034540208881601d2941080d000c0c0000308026a6091500d94803100a040d2030343e8000901d22003019503098041001c1410380c8124801c984c83c40c100000e0b413804d8031100b203032a08068051744c00b501e061000190300840801c26260242002500d545080c5011121707054048901e8400c680003241c42d40580039107400c03601c100d14119001074050100da55642c08850403800c850750040c0d204c0401004241003040019402c808090b20040c1800c1920000c6410754405503c20000680000b40f02c1c2403032000c1d04c007c88041c180600c01546082c10740c07520102a4003d5400180c031440120205261450040124502d18914101a640c9480c0c1c0c8142190090900321020b842403007001c101c030003c000e4154215050250309450f9120303641000401d0000c15440c0b440110784d0000c181c040800802c0007600302000500d03442d50050717520300d810f1381030005035100d00d1455 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 384385017 1250 384383767 384383773
    0x80d0f0908040b0310050a080a0302120a05090d0602090411120106140f0310050406080d0905091012030e0402030a0c020d0c03020c010c02031c0c0201140304020303030604020708091203040602010e 86
    0x1800a001d4504aa044845040b48a5160b440303d4810b10411a8140d204079403011035200d0004041201160706107034075000c0e809840c960250180e10720094030501c40b00d180060700801140c400c1c1d05d00614410000b900482006003845000c0010904580c03940400b01000400802c401030000b00e03030741547c0d001d80064501040d0340002011980c40c0c501903100318440145001c80003c00c42d900c0302c41d00300001c00c4014400c0c0001941e400030079882c0c2c0b5100345d828000031042e18001c1000d0808005081c02042c060410301651480c00c1c480c9004aa510b0004604103d80c400403080c81e84d91318000f45000314800701c2d0000d98070b51000c0c006440c0602007110368082c0001d0000c4100429004140f000c61040300782402040c0000e6403000a0034030314080003030042502c140200691140d070110750103400354800e8079241c040c11881d08c01c09201e8041214000d61592080001941c142403c0d005401894440c1c1c0005050100802c00211187d0711444107410584c0089000c100c80e40c0e0900401d406c8200100107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 384386267 1250 384385017 384385031
    0x807030b07030b0d12030c0e0d02062b090c17010c08010302011b0c08030a080618060f01050405040e011e0b010212130e0901020405010306062a0212030403080d0f 71
    0x10103098200041c81c08082c140d88559100d260345509140a07202039120444150020b4a14806001460705d41042d600180c00151212114186281202e0301039800802e640d04000d0500c41c582204400c146c403210710021254a84200c5000c113029180c100e030322035021107510034200040340e4241080e4082002d00740c1e0400040110040e00013186a0540c2d070280781c10522012000c002d107214641c01080107044800700c5200160104020000e440700008a03070b500032040d142d000411084079460121440304139101c0011032114680703581c0148a8600c1814090308068cd1000081e0854005a5041100d07035142c40202c4803100c0403802070f49022003075207001c00c004c424450000f176071140c00604100c0007440000d41201c144a0709150f0b03000510000444030310030310745813078054040d411601c1018086410940d0115038140200b440c000c20071446088406600203c8a1811980c1c143c000f040c3e0300702e0903510013404280f40c01e00050001d10b00601c90566203a160b910404102c40f402002c0540031460849 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 384387517 1250 384386267 384386273
    0x250503060a050f0f0603030919050909030306031e190b0a05010504020f09010c020612071106010801020a0e10030f0f0603020a0506090a18180308191a0418020415030b01080703 77
    0x11035138000c84407400c001a141d0703a96002c81e146200e029150b83e44018081d8207518210448814a0309592003540c805403191240c4440c0f580d68001960101e5140e0091041882d101540d0760b02c030941c1c06807050440381442044140c1101e490440745040d124201110b00b0031040c0c1071a03000386d9004000c00d4804500d0860104c140e07840500441d000c0e6810462048018810b65030f61030191041d20341880458070143c00c2802c1e001d42820307060303406083c0e940110f200000b884101031090b038108031029102c1c0102039000004104a01a9000c2210b040c103076103210801e0030040902c07542d8041390308000002290b0b8210300401ca0300d051154008c0d48070b0705080113001d1268884094400031140705a001c2004414030341145000340456a5a00c1859010030f00c04006156002500a01650118010008614030154103500f03a94004000c0c4440f030450710260221400c0592183c200d0300154019200c0801d03075a40007505441e0a0030b8070b40d01015202d10103005014103c185c2c14018024040241005480c0d96 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 384388767 1250 384387517 384387541
    0x1a0f0c090d050c04050c030f1f05090705120f0916050a0504020a0c05011a041a0d0206030604020d020f0301060915020a0f020a05100305150d020d0f05250503060a05 72
    0xd0800e90240a1001080d01002010000311802c801c00400600080c03038481d9080c20190022984640800c6001001c2100e0107051620864400801501c95810700e040105200c440718004d8942ca040140400a500e081d855444895020302c114a00c3c0100301c0c188a409146000e070318107a85000c5a072021001c1146980300c0d200441118026680587c840c01d001505981c4080ca0644c080d00f69400d040b8100c01c800241d8511200c540011581000703010010f000c1039143d0807246403040c2e0443d00300c1c90044090308e0404040c40e031000004002501c2c0011440d00c0300182d030406000140391b0b070340201c0103200190704001c5410240111250100045140c17180003036841c4100e007800f0780080d8945035404217544030f072044d10010b400c1c041d1501c00140004d01c2d000b030040004036216071f9040b200c19071040c02c2d03240101400103000e400400c2811650402c0d241c0103100080d0107011920b522405030904810b09650440c02c15110261a40c2c24190b03190205040c02d042004002800c95840e203010403500360310032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 384390017 1250 384388767 384388777
    0x90201181d0a1107350307110f0f1506041e05060f0907050a09051002030702012f0715021c0c0c180f11040b0702190b071a0f0c 56
    0x1096034140c00d6103402038401c0041114a02c1d00340035540015410060040c0b110104a0482c3c48030b488207002071441540311740040606000c51a03144e810008180358070720509000078800c3c0c0040684030861400043e481c030b03081402c2c81600b002e402001080704801540c2d44400d5015106480500029000c010405400c668580b00a0711860f684c8010401e1500c943c00342a00b001c03005880780c0701c0c1d400d0922010700540c1124000030001045d069003c00c0c54106010040a4181d0580042d070404100f80c0c015220441c081d0022860011181c2141d51410700d80d80484c4806032141c406000d0082c1050042c00d0845815010301065612040b0503107002d682c1d138402058070705860300c2c01c461614554a0121a51115944a00401909414000c03920880303035201c00c000082148040100c80e14078a80511540118480c01c4d24000c0c05120074000744c04e03e9070943d00c7c00199000b0b45505243c46035030a00c1940c1056105407031642d0140c055140c03103e054403180740c0000c82000385000e24038040c0c600402d00d10078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 384391267 1250 384390017 384390059
    0x507020303040215090301090b0a1d03040b0a0e030706030e0f030406082d0a150929031606030c08060103090c030311010f0509030901020c0901030c0320031009020118 73
    0x103c3c04d500c001c0c4043d00256100d154005000307021020f01e1742803440100000703607825681c02c0c0c074005c400f24044070407900b001e005040b000c01031030a052410b1200c064035040134404100344490a56021001e9409008500c09046c0c0b41e10300103071440f01c1c041103a1030403000d2551004158410031080c410b40c4d80004c29154010245940143c1003607130508202810140800da2909005590050001d1a074090700440b10118515113009000740d615640601a00d0aa07400c0120301122041243c151610b0b06001c1d807e03521000c0c040760184003412604804240182d1312480020b55180c60210b04039a00c11411030300240309280030702481e01292501c0c40e0740601403100405105280404500641e429003240d040400811020081c0389000b00d4075a460317910200b940790042c0030f4480c0381c50040c0f83c114500c50583c0d4200c0e604602040c1959110380503a04040000c204a01860380307031940559007041030340c1441c02210300219086845100251a005002e09071258074811400c0074400000e042c5502c00740a48 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 384392517 1250 384391267 384391279
    0x140d0503120a0b0d030305160f05030606090f0d0503030615070308060405071211030103140610090903030b060703051207030209010c021905030304030b2406040b0702030c060c0d090905070203030402 87
    0x224440440020b207030043d040c40e0030000a040190074190160f02a5108080c8800013000d038402040c0c040b10f00c800c5c2d0100e0b0002054007031011400d5418054068107500c900a80300d01042c000c40310000d807900154100c01c84030742c2c2c00082007001900b00003402946881e4111140c60410000d0380d00079002c441d0003016140115901c10020345c1c042e2085101040c0f41ca43d01604204440400b4420162544240000d89034400d000200c0081184000b81d81803149000124200c0000e0506061070301900b4861030a50825032140d10f400b8060303452000030f000385071094440e960f80c0d0560b07100307200050500a2201d400c1c10b1040c070064500340d0704081c910450035030495020700803030b10001003102102034603044250103100c049008003c1082c8007207054080c0301c1345840000014a82c14552099050200d003050708402e0a0104110240b19035000d003402c644024107851054141c0c034003040c03640d0800301e40303040d850340002c200c80711003500900800060300042500380190319003054041d40d03900c0054402800340c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 384393767 1250 384392517 384392521
    0x18030c0f0913020901090c112404030201021909031e110d080d0609020a1808070b030405031215040605040207110f010215090a0b060d0b07050d090f0b01140d050312 72
    0x80a0540c0b00203040303500801030103103544c4501400c001018403401d92070100c0c00d00c1207118035080c4001001d200e0018011280d0101c1d14003004040c1d103040c0058012015507400340403680502042c81d9040708110100d603240700215146051103840310202012080e218940001f410f030205500d1902d07010203140035036141070031155074904400c01e4480c00b401098218604000420b00350100d400420064003a942c8403842e00b0200d00d20300400b1107513031051580c1903104840800c40c01ba18140030b075a00034020f000780c0742000c0180074854004036003210040c0a061200f5142061460079104201c0078010a8030114101903c0383c0c0d4402c0c03400c07041d5030b10074850301103d02d000a0582c400c00510313460150494008000d405c1c540318291360341029030380c111454045080001e940d82072000328045c44507005150703d022522a51801c0d55954403124604242c1d035240c02c030800202e40061240700f81280705a91024141d071409045401d040700910381c0034402c101c952684004100d0010580394030030151049602d5503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 384395017 1250 384393767 384393781
    0x9151a04020a17010b070308090304060210050711061608010605040b031504020405032e0b09070e0a080d170108030f0d0f021e0a030c03020c070e0c12090318030c0f09 73
    0x16245410b4480f00500400000c2032540c0c1c0280a17003003441c0309031202e1025484100d40d5036101d004070700a903001a401800e50b209050501d810064000c2c50b05e0600300782102c0315032a11410403104540303422041d9800c4400e204410f9024281c1801007401d89881c41c18035040c0391910030b05d88005403485129074030341d40c074000060b070359a4116802894010100d460114405c0c000b049030342241c3c08541c68084586c8a040119a641e006543d0115002040c0800300d41e51752000303070b44100c044a12943c20416401001c07414500400200c1446420381d200d02d00c00742c4038241a8511807005030041451500180042c480340d000300d4043e21440480640301007134412003801c1d001c0003801510343c0c5401e1000340c013440b40032401402c4020648a20b4a50b028412301b009600c096042e8401d06440541da580098410880320700050485500030700708000403480c0c0181c0415200b6203120550700071429802c0000c001d407552000c4401c12000306001e501602440c0c1d00c070030005040c80c14000c42c0c58001c698400c001002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 384396267 1250 384395017 384395027
    0x306060f0e1818160303090b1b010203090c030601120b040f031b03030b0108070801052224210c060305181507020c0f03032b0e0109151a04020a 63
    0x58000d42c00c04620503c0d01c2110240c00300c2c004620030100e805100c000500061400c9800310540303425031035a0070a00d180114a40f040e5011b08042c803562842401c600021007030030b00046020702e42c031000509013004071000701030800e003040c1d000940f400000240fa00c0010a10340c181e682c469000620705ca002084c40c2000d449540c401c1061030311240d00400b002c0105505a40205c041d05002ea0b929802da80d00c00a0513510b9a400b03001c0e8561041620b01e1000502700303020000082ca144130b00000c03582204200d0344518880ca1408007038181101818240311140c204a00740728862255051101c00c0900d030303180c0410243c050700646c020580c451000030f0001c480c6507040f22078610420b00701c0d030304c49001c00c0500c070b00000182d84407001801401072005103840d1944201c000011700401442c6441559494500480e20761364079480180d00a40095000140c0c9100b015090802100041040203192521010185c070205100ea010f40c030b020ba481000c108506101001000c0a480040e6070b00d04079031007521 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 384397517 1250 384396267 384396289
    0x20103090524240d080c03070602070b060315040308040816080d0f060f0b091918060311010305070c020f03030904061d0106020718050604140702010c0e010306060f0e 73
    0x240d0084506000c1c0e1000c000e00c260601c5103500400c08803450100043c1e00f4800c5a4114000b54080550380c1034802040085000b484501200c20440349450342c156165000c2e03030019101501d14240035420071280d81014081c108030942c003030752811510328043da4064090840640054454040480c1c03605500c007007001e00d140401c2d040040c2d162a00300501141c00640b0706502c0c0300e618a4242640018000c40d402d0b003a00c06e44402d400b000d41040700c404280103550a107001c400c2c00140741e071200007928091711881400c03501a50440881e2081c11030808490840c43c6280759410585004100100c80350301c80c00444480394100d48402c0710408007800285940640c4100b2640240b030010f0000f0743d10000c100181c0701644c01c0c00c03a541d4681c1c1c0c0d880d050340c50314554400d00b00b070740c040e00040d4402580298031455110b1001000010441181101e1004c07002c4200e0340c81001d42c2d5524078080c4c9180e000a1203203805c84003481c0600130241840d0000788400380607200f01081c4a807c030345814041d0341d0b454000b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 384398767 1250 384397517 384397543
    0xc060e03040518040c0501090f090e150705120c0405010c20150a08130206030c0310030609060c030b2218080c06010f09090809060a1b0b01050a0b13030201030905 71
    0x512070300d03051002038034030f007400761011990702c00780138800215540145100c008a85400c9501e18416141c11446809407111445031b01581c0a0303a0003000c204860320b01a940105541e40d0b44980307c007400c440440c10302002401c1c202e1100d01c20302c400c0003581c0e4420414080c0c0d40e0300802d0007410200421804402420408500c0c0e80501d00c1110360060704210809402600c0d00355640b0700340c640342c03103450074001e5084400c040d400c51010000249012203080055401c0b17403401e046019120380e01c0d00e40030215440e003481100d1042d10341c040f1080b280d40c90702401d82051000caa050700c25040c0300c1030080e6088060136202c1c1100340c03540f28100e0308100440b4412101038110226030303a21684c03404550348801d024028040b2401c0382c100c01287c245042e100e01c4148550005c4410718140c80b030010440d0f41d03000480d003542001107408030b03901000040544601d5451040d14404c0300355041074100716031014250404032843c08107001c10110711641c1c01c0141c1c00c494080c20001914091810403508002024540c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 384400017 1250 384398767 384398779
    0x1806230303120103080315010801140409170d0f27290a0c0801062a0f08070302060f010b0c101a09040807050c010c0b070f03021b06060319030c060e030405 68
    0x801d002c4864000d41c800c41590000c071442100c48030049d102c80c0c4082c049c4840d00441e6120400070f6050030b9203c5110140541c010005003014103d0040d80c40e07000c1040509040d480d0512a002600310f8082c0490b500030000c5603281d02d40304030f200b403c1c0c40c00c01028050400366150080410750b0f030041c00540c1490700740c0b4400024609d4080711440c00781098030901400144290000900f1510522404520444802495000f1905580c07014100341c00140300355030241c8800c040000041040e8010904180710f0340282245144c000091200d000059001e80c6086408000c11690903d01041216219101c21400220710a1014042515082c23841c0101d422200e000244000e0127010006004024400d500300c85405607154011610402c81c2480203044064400c0480c41042c010600d000381940240780c01130501c41c4409030351000d80c0c00b0405800c860f800140c2800b009040c1888180c1c40e410030801088102c2420b075400411300b42402001510300b507900c03011300c504400103008440041200a01c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 384401267 1250 384400017 384400019
    0x51515100306050306010e01270b040e06040b0c0307090b0c01021902061b040513021c15140a0f050d050312010b0a031a091306060e0c0418062303031201 67
    0x5030081009002e1503100741720301400082c1c85500c80c075a950596461092085422031503c80c007446103488400074142007501e6040041c0103072030f02c1c4640240c000703100340241070b0360600b0b0810f005503076000b52900d604441d0400800c00d82c0c0d60002c00441c01c41c0c03144840c49689088011030240240103200d1288118008101c072104150f40c0090f40c1c2d07010700103407000c01103c20380c009411000c611462240a40000010328018585040c0354090400c4150611280301e181d03442428040031520408049683c80540b14424003c240a868101210302d1040e80c00e03481160401c41c40f40600e250314482d40d4822070b04130000108200080c81a600c00f18900300b090013032961120900e50050b00403030b02120000345045030400711400c81903140710f42c062018240008076100c00c840c502a0b0380480300300340c503d035440e42000a940811407c2c428407821101c546692030301e041c0314000d1895800d0301d40310000b180c24140f081c00111301d00010035800341001c1107851745200030a400709040d07000e2841028502001900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 384402517 1250 384401267 384401299
    0xc0102030a1d0d0f050706031e0203190e01051503030c032215230a0804030e01110615100207030b06130914070305010b060c10050402040e0d0c0209060904051515 71
    0x100000145c41a03013503911481d2200c008404843c0c65a21410fa901c0982d041960168010b500030b54214018505000880300410041d6094514684070f006851307644400f003000c19401c070701c107040e6900030403000b652900c11400740703059036409008180d401c24502d4071182110b0200001d40d0348000c0000f800741282c107540704600980f500c0e80b000c0250f1140d0203141614440002c200c003c85880032550340f0b9112854030707182c07002c45010301e8401c852414000503001e41800800100006441202c4a14400f4039003190002408100200e00d0400340640d80b06500502c001400e03007400303a9000e80c09864119001c070b020301c1070502400c0d0b0302030050724040207079554a000000100f4030100381c074020002480701403044028042c05104501d5103020a030070001c0f58243c4a50340360401078115000800111303100959040c80c0c0e042607001004d00300810320060440c000c5042a1684d158030100031039106d0032a242c6600d90a03180c040c0e0010040c8510f1164002540c007000c1200700500021000c0c2c900d00316965542 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 384403767 1250 384402517 384402533
    0xc090604051503011e3f0602030108070f050d080901120c020a0c0e010f06030f0b031203100803070b040f02240d060e070203090d0821010510020c0102030a1d0d 70
    0xc010300c84114144030024540711555145d4000300c464101c803486007613810f0000c000044680d075412080d58030006a0201821342800701013841e80340102030041e0f6a500d400f200d0703494003e803a48450280f0007015001c1280790745034040d902c1c1c81138014030340d641da0b001c0b800012110020891948041d003450224600c034000c0c0d0009119202611a00412458a480350700820b01c4070003d100c2d5400c04003060b501444580d209800c0114210b800c00742c00700300c1c403200d41c0020381032900382220065605008000c100404140c07019010041040401035460300c005501d484030300d0030004002800c5840c0d446146021519402d200028000700a9141c482000740c0980840b031a42c00110399030300403800d10a0105540745a0b06031103001d80c00e40d8000f10300e010301c0c1c00140901540403043c1911540f00c144000600442c0310040c070a44440c4841050b5842c0d130602082110f5605201d0040085500920368050241d0300003040701d110300c00e20b007040c01110b01001c0d0784c641030288454a0b250440740f1045150200301c110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 384405017 1250 384403767 384403769
    0x11031003050d2c0102030409020a0e13020403020f04050c0d0903030c02010c080f0402090c070c0816090b0d140a02131a091519090c02070305061e0c09060405150301 72
    0x40c010b0340e00030140000211914204002c1660741120514001c410b000728010400314030032018010343c0e08095554a69204036000000c83c0004035121402544072841c4c99125244122600740c411404c0ca402c5402181c50a022486800d003e1542c07030010032008440b002c142e40304104050820701000aa0307140082c080d0004004001c090b40c209040c6401c42070060104038401c07040e000c1c06603196035460b004c2000c0d0791009003502d04071403001c100b00c03000705001074003580282800c0c0f0300510406941c2e002c400c000c0706c4a644034000c1c192401c3c0c2c1602141d41e400031b42c00d100300d800c07040703842c8180600884503040c400200c400a5000005003c0c842c2c0a1500360000e0000e034104869001c20314000d04140850540304803004400300300002c0b41c001141c40c01e501c1c041b9048125a50142549840340c0082c81140c0c01d0560040c00740e80701140410411008005141d848000005141060760b021550300c1046000548101103844000c5154441034640c1400c0c1d42c01041c1c0100f1540c038440c0001000d100780d0340700b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 384406267 1250 384405017 384405023
    0x903050a0c0812040b0f07060e1b0108060406080d08060103110d0501090506090402090109020706151d0c0f0403110d1205030f010909020603060f0118080f0f060c07030c0611031003 79
    0xc000f0344190101400c000c1c3d40889000a440a05d0440c200303850b00040e51000d80e080b07039602ea54030100b844041003006a00c00240c54103460074603400072600050070125004000d148179070300b000320a000c2003401288502c100c1e001418440c484d034546500590240c9440c620503000310300701003460000c04c42e094000d24101d4400c91420030254940105020a8020844004e908081b004c401005009015401449002d024020000741d40038101911941c94556520801503aa20086d565502c115468015030304010030810492074550034640f030203914040c034403003e8440c5211900280c019118601c20b50241a440100d03c1100c41940c04058a06d8009817103880e1005188000400c11442070300c10405041c2e00280b025086944100800c2054003182d20544d041007260241024030a103107600240140c00c042d00034040380117040000c01d143c06440c00c000111a444001408880b200e44800c4684032501407400142c0c2448a0800002a208440d03034000164000001c120f10502c0c0c094010041c0c0384 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 384407517 1250 384406267 384406273
    0xf030d090504110a020a200402030103060c0201051305071701150b0316030e060408030604020d09080d0c09030809010f0912080a0f03020703080c030907080a0b0601030b0d03120c0903050a0c08 84
    0x3030303c1c4030300392a5005802030301000d81d10445482000c80c0060307141d5840d110555103292490300e400d40100781640c00a078811903002d034407100e02c3d404054081c01a02e078002e01c5000340e0980c103c07650320382903954040f611445c2c8003001040944d103010f0380d003900006580324485000c44441580c44e0b41c486242e600c02c8032580014149c0406071509036110b402002c0d0148406801000d090715240c541c500b0540c4054050790b4010380c20401032520340900c0c000c01d0760140c0501170712501d90451100c0c072402d440c0041c14080420008140601c00904c1da001595a000030a2900c040c030a411407500756400101d075040840c2c00b50340d80d440101001802e0380140400f01603595451001400c864083e42a800317410f2004000c90601e000140a101940000d150700c016100304440b26695900009803c100740e00609a928585500400245580502032115803403410f645458031201c1d1354800400b1010b4601c0680b003200c0c0c68500d0810380740c0c0304041a10140d0342040a6500d040803030b2900c101c2030030a034030941d14a80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 384408767 1250 384407517 384407531
    0x9031e0607110601150309050610030605011e0902070305070c140406170c2202070309030b0c04030f080304050a0b09030a0801090c12021606140a0e0105040c140f030d090504 76
    0x2500c41c0107490103500b40940100026401d1100d402c1090a10090708010156200090008104100714042c0903403030b50000161140c0c2541803110540b50305810050034410306c0030400040007460f42c1108210384004c08016210119032400301d40a06c141d490252500401420102d80c250003690300d2004518100c404008550303460038024640d80702e284082003035800c0591424410700301404046800e05090342e4003003501045503019012604170b400181e0015444135070a004100141c107aa94110300010112820b25245a0b103411803891031480081881801001041c20040100000428503500851211092500c20b01682d920380050f42e00d10b00241c080c1000150031110749c445ea40200401d40c2e5003019425500802d50007a50140300c0314501500422001e0011980c123110b2040b6528810b01404001c0c24a10203007004e4400003104800e040e49002c00b880009401315140c0011100585131036826000440000303100c0748040300519030117025214000c908568020104025250210b40c00c010304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 384410017 1250 384408767 384408781
    0xc03050f1606210e10020418060302090606130e04030e09100b1b0304050307080703120e210c130204080d2f19030e040b061602011409031e06 62
    0x140500d842050007040220381c0340440255440e00e4884070381000c00002c620404c2c84514180b60880d5400511070880d40490180501100b282c81074546018084050003200d095800040100d000600003600c2010002984246c1c041c624000b40000c0c40e500e000389005103000d08020f8454078110010900c5031080300f00103409000c82c02d00d040d094800c030080301818001115251100c00003002d14010f070070f21050000141170360381046050049c1c03600c00040d240040c91880c043d5001c10000b0a510180107004124032015181c0c88000320f0210491100c0c0b0821070842001e09040110104003141c001c600d5904000021a2680045c01102e50440c103c030301140d0f240104980c0351000841c00050403100401c03051250041c6600080c7c4084013000782c1c0c00c5405040180345110b40d08010882c041010802c1000702850180304500c10514140c544c3c502e8083c070544240604d1081000090602591042270035951301c9c00300c182c600d42c200180c21995040c0e00ea001106d001c0c000a00c0d0780380240302d248009040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 384411267 1250 384410017 384410053
    0x100e010b0108010803161b08010e030702041b23070b10080d050c0604060c030617070303120615030c09120f020a0b0910032403060b0a140f1c0c03050f 66
    0xa03440803106c9201c0f0150b560342d00c45004201c2807240c0d5042428405d004502c0b55000e100b030b4005c900002c1c000355554580c510500040d41d41051002e20901c03145900504200d420000142d0f26055510004020112105611580340640900540407418190070002d181c401081c03441d003a580808201e82c5040143c80c000c4a0b1441750b148500010b821881c04200004c62580080084450304d090100d00b9030b03241c2162910f103405000100c51030394418401002455004a00c00c104040201707024003445091000540c96a9407104a01081558498462440074403910400001c0e1030070071840207000c0f0b030900f04520741410090060f84227200210002807010481c004540c0c014001405a04601007030030783c10340081069070065052440c01c10002c40d407000d0340107282000b41d80310783e03000a42c02d005101880340e040d0321034018040c090f002080e0b030312850342d688550a407821011560100c143e2401b02950083c11002c000003003014021070808420000c001c1421b0084001a90448981034109840500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 384412517 1250 384411267 384411277
    0x1c1206050f030c09040804090c051b01060506030c07050106081c031b0c1205041505030702060f0405030417033c040e010608040f0b0f090f0303041205090102100e010b0108010803 78
    0x142c0741d4449402407800d42440f0315502d07403203801007540a060559031a154801d807020301001038005100000c6248034540c01c04001032100b8810002080b00750b0078000840d06074031014068a040c8213010481400b045001d4015030301a080500c04d03905106001d54105c0c1d024000000d001c00428203006151151244e6801e1046100403da0b0300c2c480b1207105510b90000903480f001880c010000100408191180d65058190005145e070791460b549185c2714000a0601d60090704081c000c3c80700c20709203c08108000107540541e8105403103042003181c2100e985141d8401c0c144030310381c0c00d45050140e0002075100f00905c49645240f400704816003080b100320700701c1d0784210b028440d0a40301040040c40381c203203e400680c0c4d01c01c3c4125130402c3da002c440d0f200c210240108481000c2c0074810202048403241080c0201c01c144031651008500b0760509036140300b5072030b14013540718080200103c0c0c050410ba01c20070581c028403030048802c1107118005860180039018608295010a8011000280341c40d00042210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 384413767 1250 384412517 384412519
    0x1703030f0c071b141e03060606090f130501260d0804030306031e0201020c01021207020909070302090114100e01020c22020d090b0a0606021e1c1206050f 67
    0x18a16554066440d030075400c1140c0590340d92120400310603040d002e2807000c40240241d4102c9075819900a420031144444011049036000f22902e2800c4050301c00050780760301b0060844a541e1902000c0020a0345074109d03c410961010b449c002242e0300c055543d100c10305880840c001851b02802003a88643c2032503007144a44044d50000d00900c1d01d55201e192201d801c20b119180214555036291201c403224440143c03822151500350104104668040143c5c00640d002030000d4402c038600c860722503c0178014604064001d00e10200018000c00080c80500701440e40105041c50550311380840b034402d002036004183c051700d10007054490403805801400e4444405078020908a02c0c0c07181400300c001801c0741e00c3c1d00041513120024542115500180150013090100022500e5040c1008175103000301400c85e8446500d041400c1c01165170108a006410b040c10400c03400d800381c40c2c44100d2504c91440ca0218269141c0000c08000d268061401d030404815104c0a12410b5103800c20401c1d150301d400501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 384415017 1250 384413767 384413791
    0x1060e040317041110201609110c0111070516034e14130510050d1406090901060810090f0501020f041811030708131407170303 56
    0x40c40802202494143d8000e2140074083c000101850104161051480e10200403640015030001d11208000003824082d001d500205018000458165401003803030203400005600c401101e54943c42c41421a030302c2212110080144040c40102d0801e180c1040fa01210b007401002401003810511315420b40aa0790481c41480c102c915103040c5070b90880c20300032440d440c2100007142d035040001c108000001000720002074404520047c0b0010455014102d440300805410300980185607d600410b00c20ba030002d4600d040180f403d0b0030261214081e2020300311001e410001190464494028040c2c040d010964410100380c03141301500d03098522502031419550f000142c2c01141d5002600100107203409a40482c0603403219480d240d09a901044031200c2c6004002810400480a00800300c0c91910b035110402c12202d903e505c006031803002900603020882008042581031303005040b1481000d90201040c40c0c2c40310300f13a1956031151540d102e000c809003c180700d01c0400784008400c07288100d03444201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 384416267 1250 384415017 384415037
    0xa03051e061806030c09040305031504060f05121006030804060305070302360a0e0702060105060a0e010507020a1203030603030e03030a141308030408010204050a171b0301180807020301060e0403 85
    0x50b400e4407001020140c0c14030540c0d07145c0d1710030385405404501480c0a030755415500d10f01a0140e41c0004414820306001e02d00d04501004500e40340a004826030f40219180c07644003504c1e80c0d00c45d18103403000d020202481c2c5082c000004100c05640100708480c45074a00740300300d41d240307a0b003542240140d92200c050500e0200710801000752040c034403030691180303052440c010184840400c152001c507030040c001000d220414840b11035010498540106401c44030185862241a0018501841c03041d04a060000200d0800110354074103d50341c01401e010704519003d00100d041c010301819042c80141d0108821850740d420508020007203401c0c44c2c4264560110845030700502002c581d00c002803405030b104d512075022549036030500060000348020000961210b0402c401c00c408580d4a0707111150700d0307109141d0581716050100e42c423001398407400e95881c9580106000701e405000060381c0c54000c1e115100500c0300b0440756034040c2c850f090080e0002c1003000c0d20340d403100c0c140b50010f403000b801094000305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 384417517 1250 384416267 384416299
    0x207021306031a072105010f08060c0703050a020703060f090c0e13080304060902030d110c300705060408070e1e0f1005090f0703141501031107080a03051e06 69
    0x4007080d00662207291203038034010f482c41c0c2d200204010005c201d4056880740010401ca005403c0c5010103808600082c11003030600091440d07141c401d6036802414000c0201d07410b81400d000b44025001560042c40030300c100c1e107a566003030008040800301100e541306d410002048031410940301600c242070700084100a4152600c441d549604000d004842c56522882c891005850610800c2402d02461312500504092601d80c43c0c100909000c01900600880748440f5401c004c171000341600301108103d8000007081c581c11036080c00d03115000983c008200080003e000b070400520841220a014114180e5445d482c030100e540e00c103229003145048000d2030100784032040d038a405c10f4111840c500070b0450302e0b9454022072000b8008980c3ca0000b0091003040002c203503014011442401e000601c000028603003800460420f902c02e450b070a04259031040d000590102c44000c4540c1c0d60f03001a20035441d030380f074040020003504084610801c00440041c00e1803032451400c0300f04d400b429009014040e0700404e04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 384418767 1250 384417517 384417563
    0x6070b04050f0a33021225080f04020102031e0307140f040521071511061e0a060b0f0a0201150e01030b061f0216050a0f1e0b0d020702130603 62
    0x45104c101e002c1c603048030724180c020b02e100814101c8109100042035160024482c0150011850754044104000c008046080d82c0320410729800040c010140d10240c40320700040b495401b50140c0030b410854500c07803c0c01d150340d000c805503200c3c5e5010b98030342c1185d00100d00c0c0c64500f4090040c5190400000f40300a11540c80c005030640c82441c1710705442d501500a03111050301e080c00d2944403101b12826880445c03502503200e003201888500079401001c8034104138800001060038001c4030400038030224041040a6055081040200070b030f20b0415031106504164120319a10080a681c055880c101d00c91003801d001881880c01c5807030102c2c03041c001c1d0b840c5444010f04060018041503212000c0d58555000510710003510340100d095a008040400c182540b00b0f03040d039410f4110a104034221481084180c0001880c881900d82010344041c0a0821001207601440c640e088000104c0001c030720f541c0121040c0d401340c01014000c50b08031100c00b413050506012100f03240800751200da425805000d0264601c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 384420017 1250 384418767 384418823
    0x616090803070809062101090f0207111527091e010b03060d080a03090303050f100b0c0c0a060f03050c0a050901030e0c030607030906050105310b06070b04050f0a 71
    0x160142c0d16010100e1480031440800a003403006e01e80391400180041410b52180d200c4000a6270021490102d05444900400040c0b07048203100b1460b2030584c6c0340f002c6180c0107070f840541d0440140440c40c90711040c032191803610215500d00415020000400080c0032088100c407000d442c1007020426404e02001c503610758001889103411452024400c030002d1f580c10700070050101c01350340024035183d09240090644030042c028444d852404402c2c020514030014001088940040f002550354200c001030b181801030840d110b5501100e0340600240458105d10410702101c1c10795010000c40e900c04103034030b000740154400030000613070500c00310320254060b50060180f000e600045442d8040c182000914003c01100c1000000f500c40c0d00c118101305075030080b640075102c00c40359404041416240d0b00000b062a803050310303041030440c078040d03c4014260f2010101d650301500096803040613082c8560b00100540d4119030754070034034410810141020071408007099000303520244480c444a090511600d00e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 384421267 1250 384420017 384420019
    0x305120c090a060801090f0c09050607060b0303030114100903030903020f030a060624020606030a2901030302010912020c0a060305100b03240a0b0d1d0a050616090803070809 76
    0x41046015654940044000800391644d468080b581800c9000041c2c501c040c51813031034281496444440d142d080381c4980c4c151541035034042c0c0c41e122607052207805403480070390710794042c003000002150103030042c040d5800310ba00659210b0b20202c007001044807002a18840500010300a6009100621b0010407841480070005e00315403251407951160800ca80c034a9000100030b4210601000c061600d440740004503403094006032055161542c04651a02008140100b86000211500001c0001207003034200304401004070018039a100e1074041d0003004200b206407582900f0104c0846051300c006420000702c0c0010706511016031078140268003504014082c202d81103c400808075069030010051485401c800405144004030807428036054542400b2003802a16000c8041c0300c0400d200c1d045803014a01d100c030002e0300c500000400403180140800c2c0502500815000c1f01c28444e00080542c041d640d154010284407600d4001601d0b2a80c0c00d10600015170014010030020070100006050f0010f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 384422517 1250 384421267 384421291
    0x103020f0c06151c0b16020102121e06041a040504050f0a0c03020a0b0a0801120213050708160e15030406090807080c0c04060b07020f04060f0815090604030512 70
    0x40241c200e242410002c070ba01503030496105182c034070301d4070b0034120f1a240041d4020810070500015114280300380300041c003500d490045140310155952003541110250300f408410142541080380301c0c0c3c100c82e089843e01d40e01c0c010122001c503a003890141305182481d0801e44000c000080090203010260100500c156428020b07030b03101c031944070b0f401d21040c0189482810445c01e40c2e8214810008000500d802c0192140002c2c032502c2c0900760401030f0709064940c1c1241c0c02c00003174a188000b17419480903d044801c1c103820300040c0405542c01c001014003a543d00240b0007103140818004803107170262040c0c513a038040c114034802005800503c00543d0001e0148401046802942d2680c41d41a131041c4021504004001920703500380c0b001f4081030341d00c0320b0122802d010040c500030402213240a07031074010b4410413520310b208800d561580c0c0315400500581030740100311076403000102c1e01c804c0d02042842007082801c0003d0208100443d51070712840d89a06c46600304225041984002c1100400d007100c03002d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 384423767 1250 384422517 384422527
    0x190e0d020f0a1715150a060c06020705011401090e0f0d1404030204050f060a1710020c0f0106080c2b06092a03061802030604140c060409060806010f0308090103020f 72
    0x501d0341032a81c1a072070b03401801000c060340b5042c402e08100e0340080c03071709442464625100c02690345030800c640c1210107529160864110b41d04106c4001d101e2040000c0c295031030011146403140c084104e0070b04a071100e002c1004540e45070071410383c40700580168190140c00c081407004c41a401000d885903590303c41184141029103c4d80840c0071201c0a440c1144001e45035001c1000c0d07841c0c207840c224040c040c242200801300b48400c0040da65201d801a156140c25000f02d03038194869401c002514060360f0400003804a00d5840a94030b8641f070130012030500612140b807686200e4183e0506070980c204482d48980814600b40d22000020114584203c41e000005e00703040710030100422a85045184030702d42c07042d1a900e1885c1c4503088442480501c6181007666001c000940d07401f05900d5482070700554502c05040b030f0707101e80d20b040a0401c0c405a9102001150105100c44113034054029168040102c41c5966250143d0b00c0e0b6a240a210041c10103404200c1100780354400c0d005840382e010262411410f01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 384425017 1250 384423767 384423779
    0x30901090501060815061207050f12010c111209010801050609010311030c2212030815060714010b010206060616030905040207050105070306060f050912030c12190e0d020f0a 76
    0xd80c405504c04982a0300c42060513124100d50500950801d0781180c01d00241d40700c2010440e00d9089078850f40c0c0c03086c88405900c00d07030394071614200d181205041c4000c02000c50b04034030107460002180365034121441031a0107130f10400311070070480c3c1c008441611000c1480c0e01e0700003001155070050560b90b0406d0b031150411001440100c0196026104140c103854503443e01c0940310b02002c641740d02401d500107012400f0082e55490b0040f10080c107806240c8084640d4904840d200c0c2e0b901007140540c5c10107070002d101c7e424410f09103c0c2c0c0d142a40d4000007030000701e822000490382da460030746069501540800400b010003200f0720741034424078804e0509664455440d0b0000e003c9800552017075855035112070400ca4070950500c144000f03010b060400140701c20450710010700c1c0d405500d01300350283d00380d2080060b00903c00c20503200c081d0300042c11500c1040100800d1085c03600500c01d03042d036182c1c60b95071062250740107198411200e20060201c0440b1660b903000c12064260310407003542c01c40c13039211000c00c030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 384426267 1250 384425017 384425021
    0xc1407090510080c010519081b2a070e070c11060a0f0809070e18010207141c020a0b0708190c0807020c04050105030a020d0503120f04031b05060c030901090501 70
    0x1c50b807a40542465410300e00381180d401c0c040011010b604005080003001e54844e0340c50302001c007a115500d845821950b8540c0092451030003060440c1c8424030108000040c4040909410701210285110b41c20b5200d2000d102c581d24181070013a01403014a007000100303218840c86407100001c0c010300c414658101e82d1000301c0d0380d55218503003402c000398008100007030342504442d00d00d030884480d03030007084142d1410100c3c50085201070304800441641c10a1810260b800b50192401a504a0800e000d11075180c2152a82d550b20700750813004508100058800e45400400d500d4401a008461a40e250b03403001d80899111000030807410070205e2070030341c62680e64080c2c840c481c003066180d26100e81606101c0d40292502071a954164031460a140051041e0b44002c104284c0c100d03415541c0f0590101d444c9419421401007104503440c1400b01e40400c08020140d0000f9805940280c44003058203031040d812a5100f03006801c06040c40d03001e9408241c1040c610700081d580060250700020b810070203960742d182 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 384427517 1250 384426267 384426271
    0x1050a0c060c4b12060b031e0c090d0212030d05010f0b0a1704082713020c030a0c0201020c1306082b05090f0a0305060a050c0a0c14070905 61
    0x2000481c1c1c22140c20030849a202000c060043c120481580e21001c80c1010041c4080707107111901d00d400c0c0d01d041030350032401024040110440c0709001e00416803504159010307134104032091515803139032011310703c00300c044551864040c240f440743d030a207462403038800e000c800301c01f13150103d8000c401070740c07804003614007480581b441c28070400010a055241c40c5040b00051215009800b00c1f1400300b1007c1d41903900442d0b044d149010b0301d226821182d4840c1031041d0740340519500c05908000050070740c00000030002d070003a09501e00303c0710300c00e2000a01e01c0354000ca00401400402e0395000f0043d51110358014401d0201c2503105104031408800e0b003902080b4130240c000c1342541c0d99521001d0a00901c44244840d842c800b41300458500a107107071100c0e030107200060480d501c3c144040001c200d22141c03140c04201c4083c46015044480345c0303541f4600300380e417808203e070708070f86051a00c00400c01420442040f02d0280350301d0b556100b84400b084e218441d9015514180491602c14100001001c5209020b164 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 384428767 1250 384427517 384427541
    0xc1a04050a0312020d030b01020309010809010204080105010807081c0c0b1503030c071a0a0504061809020708030f0a0b1f120c0c1505010e13020d1401021b0105100501050a0c06 77
    0x9002803d42d480040e1500e5424100c580500d401c1c2038860f20240d03070000c00d030b6244034001d107000e0080da00c1c5d45904900920507904003140035401e2400100340900001402d104903001002101c1c081d6101c180984881d00d601c050314800160800d00d06404190603045982c2c00c002c803003002e2800403c1c8200000d15503449180100301d15003007254100003512205010314000605046100c3c60404148070040580c491802420300303000c0e140d90101010503c0b00b61810207003030f02d44c1f0704550b9505641400c4116070401c48003035103e481802c0004500f407000307008c1c140c0300c0b00c3e01a00d001040a2000001406044202d41680070445510301262080043d070003003003200d4100d0740740c08540502504042c1007080850311500040c43c185001080b04041e8140c02c690320405030300c080d010380100b40c40094862090820b000c1c04452685881982c3d0030410b50081c8000d8410112403158102440515801e030f600c101c441701c40254844c0c20800c415400b40008140040982c500340789049107a554030310449506074018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 384430017 1250 384428767 384428783
    0x3120212011e14030c04051e1311030307051203090114010f0f060513050d0807211b0b0402040c032406080a06120f080c010612060b0405040c1a04050a03 67
    0x10b04042103032801c0b01419020f80d00b160300c40c0200c0b0102e0799440700078000e10b00440d1707140c0000d0868a551401c202039000c0340c0800e10303080d092850000303907909085181500c4208102554114901d000000c5468066020740038103d840750300360703100c40217400040c081c501035520b4110741c2d1410352012a0300340c003a04040900718030040c00d044584065240030f401c64410700404108041c40406c0c070325080012140111960241c4250782d20700110b590061120003096802503042600c80810009940d40050b662030b5224106002412a003c405051803000641000c68410104000d4145504a50a84505424042201d0011140d1005656010203220000807080c407802d01c2455400391030035800452006080c841c550902d540002c010403102c2c40241807504c84000001004003100c02c0d00c4480c51007000800083e640d5100d950300817481d81030200c0d00c051038240550001d16040c03150070b001d641c110004c3d000703850074015441803101580c0407103850681b041c030000a25555140140b03014500c80c00c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 384431267 1250 384430017 384430049
    0x9120f0321020c070b04180207170a0c11090c0708030606041a030a050a0b0a0b071a090a1b06081803040e0403122f0a030906110405030f06090a0312021201 68
    0x2011381000a903410812600310304003c100840203202e2031401c80d04034040700059075a1080d10b0441c01039030a401c07000e0080c0c4c0d40490b03010365043e0400c118544140c05500e0541f102c1c2d01080030020f42c20401c07107400499200034000c40000c101e800c0007071944441c01400303507071900b038030f803624000c4400c1c500c0b101a0501c0400810004075036528014160058110241440750b240d50600281803480a4091035203100c2c004101c640520250b154034904403000c0da003018a40341805080d440d1103195041040d500704110460050200480e0b40381ea8045030880ea80da400103031203290309074400020681141940d0311052002117800c0d10800c1042e0f010754442e86903404540441101c400a484100c1c21051038140c44000c40f14926a121036140c8042c0080307040582c1d15104072406600401824034050059441c069034080104240b50040058403411012100240c4648100c42d542e80c0c802c89d8075034204d8104000b00e10010303016540060091074180400360a2a000000001e0814801d0b803110440c1744140103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 384432517 1250 384431267 384431287
    0xf031005180f070e0a2405030c0102120405040c020a080a080114040903020c01050f0403051603060b06041d0c0415030c14090d0803040606030b07080402010f09120f032102 75
    0x240c400030000c5140945880980202c00b00d07201c001e58450488405000c0b00050302e90b880c0c503070200740381c100141da2859840c91b0b0f580d1480c3c03015400340100c0d4041d1152408064940d800001c1d18102004a04441803500c1d04180c01d10004d8852000142c080d842001510700010380110301807c0080c85a5032034801961408161500f101008038441b80210320300321000020030b60105203818919000e09269039100250640041c15108681c000b0300035014045443c0160001c10b040001102d0103810b050103c2140542008014403403481407140d04503010049190121503601c2859101e0109040e4604065840e9000300c14005001403003000256642418000e543d0410041030000c900e20301000e04220101020810030a4a90700207000c0982c04000601001403607003100c405568000e03211080c40c24501d001600c00141918200d001c540d10101140c8000e1180c4a1842268039000715024140345c03589071b0103655504040181c040041c3c244901103a59004072003244504410040140d80c2c407810300b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 384433767 1250 384432517 384432541
    0xf0b0303071104230f07090b0703020a0b15091306021306110f011a010c020303040b04060503070305060d1a040311010614040501090b1f0302090301060306090b07170a0b0f031005 78
    0x36400366402c01c0302001e0b00e400c0381440500f05510140322808011755803104502940d007040d80350f10140c0503642c00035848041540c0840d01d036640c5842203401903070035201c42d030f0b60103029611002141e0b006070b8180c00040038a0500800303c65a07a024820061070000a61041700c9000081d41141c0042483e4680d1080c0a820410003480c010402c1e600801c840743d400304408020b15400d4519a04018039030498605556040c070495004158610b5526659a9035140c0606550030403500440813901d07100015486060282d1404807141d03006d03440d40004a81003040039005003001d0025420000c480b019009140c10901c00c44002d405201e0700c2c0c040303c014500411086d1001608001200d0b410683c64908946030884004040c41d41500b1903c0d080107000d104030300a004101205a0646c2003031400018024194001103156000ba558108541e0329a2801d0b180e08003219420140c1c02c0b4a03100144401d9a181d000c141100c000a04c440245060000002c6c50074982800d10b110581c1d0311000e00088244c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 384435017 1250 384433767 384433781
    0xf0c0f1e0d0c08063f0601030b07181508040f061401080f010e1b010507050114220c0311030a0b18151501030914100903030b01030911040f0b0303071104 67
    0x1141d0328025110b0ba0503081c000c403000440101703048540206a070040781c0c0d42102c515a02c641c100e00310f501075a5242045941d1503c283c41760004a1f00a8000c1038400b00341180980c140d82a000c440c0f0130091f50300070100d0f0104401441556550b100c602202c0005e1450b028280c0e9161800342d1249055060189480c01c6c80300500291007960b1401c4c041c00298440856004000003052050201104107000140c540744105030000f001540b8000119050310fa034441800d001d00c82107940901a03031604843c003e01908000d4015100c412119020400034540c68810050740802030280e480407110340c1e45404000005031441c90020f65210369002403044100f0000c80341004000142e400e90422401ca85101d19039010103d04160710390400310705200e038282c40c0d002d0300901401141c0541002501c079000810200d401180000e06003043c140c89903109001707061020b604008000f1980c05890200300003026040d0070007492a0701c9103074071012540e041c4098005240160500c00ba08840b02c81000304407680 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 384436267 1250 384435017 384435019
    0xc0303090f0806010509090c270a05040503181c080315040902221b020618012d0b0918011103040f080c0c0604060203120f0c0f1e0d0c0806 61
    0x41d42040108920020700c042c11a14251042c04882d01d90b01c01090800c5103410142e5005040b0000070300c1094103081180740001c80e00c0b50102d01e191207501c60300c0c0070703038a080d28040c040741c2c81070058040d450506440096030a800910340007044e40414883c0d510a00e001030152803000c800300030020f000409040c3c4c5040c3e560101c0d0100b2980660340e000822040100c0c1f4080049860804201c0b070300e02256120382010901c820b6101d441c4240114000d50b599812181c044c11038854815174590818140502000d00b80805003104d042c0000002c0c59030300784000e0003000400c68480c5c000a00689402d5542d070701071541e0461404030407100002040c00e5030003d22203010710b46020400c11000c0340c44600e140300e2280d8003600d401d5569690386c1041e40382101d0300c45245e0b40b015000500040381c2c0d40002c000e000c821150204008642c0d03641c3c00800300c0c203400701c3e211307040c418007004035050850341c020050510280d4103500788140b84804590b210203070000045824050343e1a002c641849400200642d40040c1c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 384437517 1250 384436267 384436289
    0xe010605030f071e0e0c190f08070f02030418090212060709030b0910111c0908070204110d090501090614100302040216050f150606070804030b10120c030309 69
    0x301c00712202e035220f40e03d120702444180c642000012685000c41c2c0c04004201e0120340c6516400d0104040040741d0100c00301b40080c1000300801c00002e8050301c41802d03062038a40366100e41e80e803500b4082d02c10b500c4080300310341140000c01c030210300e5600b9040103180e407441c0c1c52000a4020744d40d10611444218060f6050429400300041120442d44528180e0980b80d0012904550351220b0141624110900b1050700b00b007800c00c540010b640148002505101110088003906a00034080910854030390f040c0180c08010100040000360a2a8010082c2d9089904034545084200d50041c1c088804c0c3ea44115581c0e5140c0814405011540c0640743c020207075400103030303c41e00746609024680892440024011500400d0346400d68440855980f0082c1d00306043d9144032100b81265519a010100790604480851010442c2c504280c01a58091944005218605402c42c2c85550400a00130700d034910b50302540d0804240c24107640c3c030580001d84200d01805006081d0715010f4122142904801c0d080c3c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 384438767 1250 384437517 384437533
    0x109060c050d0c0309030602031f050423061903120210060b09040905011b050405030d0504030f0311191b0510050405010c060212091c0203070c03140f0d02010e01060503 74
    0x20340049407008803000b00c0d0400716035103882e919040d994010a5480503181078804020001028400c100340c0700181c041c5d4410344041502c40c41040700300c0717444100404100740d0030140600c60349040e510058108100a14107200e1041c20040c600c00581150070444070451541608000e17541c04000002c40001813034410b1000e141440290211801564030580c4a680c8070642c000510000f0350103c00c42c44150449007600c107554260180282c0d105118941c02441406d01680c0c850b0301c20b0040c5c900317403075009191150841c440c0d201159600982d0061507001e00036050702c450702d18418540d0500b400c2c0715020380760b0285403104104840441940c000c0f07000380d01104110808590000407101503a100b42803600721070710079051810080c01440b1000d03a61a036400d042c40030341d080c0090440d85000b105100c2c8040300c000100c040b43c070303400b8906000303106d01d4a820b003d0001482036030884000c3c540701012194152103201708585401404860140540d646142c903904604007800b642d8040d0030b090340141010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 384440017 1250 384438767 384438773
    0x1902160308151e0103060b04060f0e03010509030405210109060b03011a01020601061815030b03060c0412140a05101a0d0b0103170c070602010f0b0d020306010614070204090b060109060c 81
    0x103030701690f90711a03400c080000c00c09081c0e020782c3c45500038001c507c46a80e00c440c1c8505000c1e1624602c81141000b00311f850381044014501401403511070900c0f000994282441c1000b84158800c04e1030450850031911000700034071030700074820221807500406000c00c41d14102c0c0185421503c40c1c0303d40c00f0008022135090b903226600001c0c5c0360f04444c40b03071401c1d10340e40242540ca000041c0d07490f003142c02c05440041d80034407000d80c542c004961a14044056a20640703d502003004644100d00c0b4041c1d002d4400e83c0484003140b540d4403c140301607000030559030f804142d55030312410a140c0303000d0030081c1039840004610b5060859203a0401c5181640d210744c02880c0d6841780489408140300043c040d4026001010101540300709645540d00030310200c82456880c0c030301c06400b07407140381c030001541c5150100c940c4541c40c0a044403104c1980280140c40b0350b900b003074411507018407805c00d80c01290504100080050f1a540718015007280601059580790608030001814802581e200b00200b01b0034003245404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 384441267 1250 384440017 384440029
    0x803221d07120906090503040e0f1b0f07050a1505151e0d0b090105010e0601030902010c0f0503091503100b0708191704060b010908030a0215190216030815 68
    0x4444242000d59a41102e104001d016002c1108010700103414012544100000040507109032410014030240d281d841c840644804a011a004e520340e0540c0300c6044c0c660341850000782030148030f0020355031400b880741e211645400d1142e14101c509800007a185a024450340c8549a04400c100300407001000050000480304400350020603000d440304109041107556031605034810981c4101866114508054010700070a42441610852403000700082d01c0756119120302829994140c54407082e05c801c60304d44100401c0c4281c000c0f50710b48010030841d8403990325640e10091003076400d0000c50b92071820a00324441d055081e400b01d01740600900c03100000543ea602a00c0b00e001c4400c18201c4040f1151400325115448001c48014070b80d41c074424041840115005900204003c0c1c03035401900799110b00840e03681c4035915420006030045001004410b54100070260888203404000c08600020300285040341d20000c12804a900c44051404c10107400012148e40030442d01c0e14904481c0b921404100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 384442517 1250 384441267 384441271
    0x2150f150103060b0409020d0b040c1701120c06080411030f030912060f040f0c030602070309061e091701020c01060602030a080c030402150c0312010312140705190c0803221d 76
    0x6140c0c3d40115100c800020a54044018200c000f4800d100c2c400001c3e00203433040b8100b0002041c4219801c00118152684148090246501078085140035140200848805102400844041c0e80700070703003082e15a40030000c01000c00c80c0315010b155107401c2c000070000350480c0950510780ea50443c508100b440d1005800c2e09500540100741054070b4821450300c82290700750f5400050080344041482c17001c2c1a40180c0c4601904c40c00e484010031414019808070088058035501c0707000440c40c500c18407181401d6413a41307508091000026040a0701032a281e030a4070b11641000300141c0c8081201010b4503801010b40380c01054909909180d410141c02064082d40480540107840000003a81c0b440c00808104a5107110350300900340c411540c492500c01112516460402d000640064803a01c0c0c1c01510f5044603105036104000f8119580b9075100c17000103080103502561078001205000030140702c144002c002c030607211006649102c400340f1040c000300285401520f040d15800701d40001c01d1020001040d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 384443767 1250 384442517 384442529
    0x405101a0913030203070501020d150e040f020402090411120403020d090b071106091e0112150909170d0507080115020303040b0606040f03060504120201050702070e0702150f150103060b04 82
    0x10b07504060900713074594030540754014090341c030000307680c040d403419603004401c02c2480500c8010750668444454500d10810340b00600400000d110050052070310f45c0c010160410094400f0030000503440b03450a03140c001100c4541d10158980c100000c05505000d0020201c1c0e90b03040910b0302e182451031181540c000c18400800000502c8600d0020340c2da144103803030740c030303140146031183e510b0b00703005410100036051418502240d90083c95000040c2280584812041ca810008200600e4101290041c0c4986038003540c0c100c48840c10b15030700c5c9a820004007426060b20384082041d00700880010143ca005920140c840b2a0340070125800c0ca82c04012241c000390041c0f1040c200f9218680081d9503031107154480142e1400381c2800004001868200074822401040015440800c2c2c5070b080c0d0a89408035803410040c1c0100a051000b896064451a0440000d1048410300400c0000c1c2003403050701500c4a0160309080410003541524981f80750000103400c4ca401d0101c00e10b81030041e4858000c600540c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 384445017 1250 384443767 384443791
    0x4050906070c110a0603150b04050f0f0a030803390a050901020705101101060f05030d050307030e0a030806031e06340903021305060a030b0606120405101a09 69
    0xc4020300001d0640503102c0f00d0010700540813140d9640d0060002c0800306030588007010301c04000914140d091381520f003102c01c0034001e035842101402c10480b105003100301d003030741c0b00b42d1490001c0042000c0c000910301c00c4040b40384c031903188400c10300442c040e06c0c42e19100c06c40300a101c1003051a1640c450054400c2103040c0d080086d218446180140c2c100051030304000d410842c00c0070042141541b0074058041a04071070003c005098945107125030002c03071800340d03a400d6401051038803035440c0301d8402140d000c001450b00040104040740460b00b091188101a400101a4400d01810b0b14061040c02c1d0380020049140030341b5031102c0b200e84e8503100d00914415144500076107070194040c00b84254000388115140c6400c040c02402406045071042e4007007030b0700510318081c036410310718003601c00c9901400e070090406601500d1a6a0f500350060014001a001041405290a103104804209005910500240c00103090000318881124131014209002c110980440304468a521081640083c1301601d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 384446267 1250 384445017 384445037
    0x405100b18071e021c030501050a050105091c120909020313121704150c05161506030b3d17010608031303020406170c12120708180405090607 62
    0x10030b96041400031101d07240120702d00410a0300c0f550100d03400f090102140b2821444000800003101102d900b4021160403010b010001e10040d070140c009044050802041490401d881c030071f14421030400c030202182c0c10210f90300e40445186d006011107001d80060f483c11419807038079420901c0443d5810001401e2004159201c2102510038440d80194100103040ca5140b410310b4030342002c0b905c483c140c0400a2620385491b15410302d01c1101202c00c0c1a41c200b90714000c403101d907260064100904421480c81e80e655210000000706140c030007600c00c01070183d12048107200941c507030140112000900c4100803004050420171042c280d410b030151210040823134907e588880c000d80c01480c0a8001c0b208901c070110b05003040c5640103c0d80c0c420342c3c0c400d944c10f22a0603074400041c03c08854551404440c1d801c540c000c008941404141c40307040f00310b000d00721038003040142d0140003664000e0700c2c180d0340e0150000740f030290175084071806c24001000341c40030012460415800380d126034024003542700b080318002e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 384447517 1250 384446267 384446281
    0xe070f0e0c0703120f110f0c0c0d0201022e0608030a0201061a0414032503050c0619050a0e04060906050114040503070302090a0209091e09070e18030d06030b0405100b18 74
    0x3c0b118140d55030742400d4658804413141860b0747d41c2c10002c0c0007061403007040624405400c05d1000c3d446580e41c1a0003e015101041d00c034a4084130800722120360180b0722251003030b03034840d003030040b10010b0041001569646480c044000c2c00c0d45c659401180410751450350304a903085644003114200c0e500c0c565042008941d140002e410007040b00d000d1a158445031280c1000d80d549400e98a0031680b09400f19074400480741c05204842c040c004081d03541e0080c900c0e50002107401100241840d050f949040c01e10707040d4880c001400c94002d500203070b00c400e81d034190600c19560029054404c00581c0c3c4140d40c00d291503c0001b07a81c507000ca0100034021030300e640201e11049030a030144c4182c100014649101403514000420f104612600044500c0c02d106000c12001840800c0b03800c283d41d05241441c40a54615404404041d640d403d10466480100000025450b45100b12005944121041d4000782030509103940b602c034000600d0300686140071541000b943e42e103401c1c00b0501000304a001360550b43d00d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 384448767 1250 384447517 384447521
    0x12170a0e0c01050a0909151d04080a110a0209100801150e070f11030309010903031406030601060e031f0902010f140406030510270e0c03060a020d0e070f0e0c0703120f 73
    0x130340282106c50600307020f500140780c10071070501507440200583c3c2d200c4a4810a200400340c09444c0541101002c0000914461103500d0503200241034000301c4c6e1001c0b40c65800305180700021660300000310340701a0140448042801807a0182022100c0d01da14141001080a04000003404a0080c040e0403203041d441103004103444000440400140e03601d0b40307042c1c0d00d6540a00b00011302200001c1c9490302c44112400110a4580034078000b41c0100340d01d0303092580c269118140c001d8050b600d80b1400459001c04000c0781d03540d01070f56188650118049400b440050580c0030300c245031100f80189604128280514981510200c8180340340c00303e281d84400f407826186140700d400141d0b0100e01c240340003c00c0811410110380c440342e16141000341d030000841060b1200d20252100d689a00190042010f120254001d402c1c2c0c00400b620005813200441c00c840d141c581c841d841114004441e100401c00780e507011801c10780c0028484041494000195002070007010460720300c020503130fa580d400d41034103034460b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 384450017 1250 384448767 384448769
    0x8040b0d1d03130501030e03030406050702030f070303150501090e071d131d010605060708090a0e070f020607030b0609190f0603020c07090e03160f12170a0e0c01050a09 74
    0x64041d11880c5803100458032039120718614003903404480800501340d4441e1062001c02c404440180d415030701e131079440380003500010b407400781180301c10700170119941c0a130001803030707554802e80b8000380d909038070503e800441c02c107540050706200c60584104041407908162a82c8016030780303814190714080d824000e8043c00c18426803904041e9100000d02076002942c4201c260094015000d60404080d5100900382c130101d002d142e4100704e052144800241a01001c0c1001110003480c0050441d16207680902d004012902580040c000c4441c1c12040c0350140803981d0030500c070f8039003446a110100007086143c030407100f40a018109220304142426900e0085801804c118144c0741d0150381c5d03c54000f03001e034100c08828002805010302c00110601d20380700e22440000a00051400c0101074180c0080036402840282e4004810540b03d00000324501c20170a00c0052940342e40000025207884004007000040110041d0f0746042005042d09034001039072001c0c28002d00e041995040e030281e0071a94802d070303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 384451267 1250 384450017 384450041
    0x4020603130f0615211527060606080f04030828050108010b012a1e05010608030d050106030e061b1e071101080408030c25030e0a1208040b0d 62
    0x1a004402041c1101c203004c6008541c1d210020044c420400b001400e810340000c0001010b003040c01c60000c15510140c0c02503110503035607201002c00f0403001a111440d4820003c0d0490342c2581d1951309000d4160041c9d10160001e10250300c00606141a550180c00e82d107029020307044002400042604140c0f800c0141c18042c01d40c442c050286581d81c1100c03901a06030501344501062040ca501d18549503052090404602d41c00c400c80380d070056545421041030415500c400040c4034084109020a0003406032030000d0031800029a5644030044c0341c0000c64406801032010076040c0b0142812b543c01c005020b40e08100305c892020039072032805441d084c0394854010400c1800400081182d81007000001070111a80a02d40100c80c0e400c0039401100c000004407802003104e902840420407140c0e5040c040c0c20b0b12805001d40c00c002d03001810100d5810a02c21008800240200507000b8803818074240c268010300c0740079035011503003419640d01da9071402980070f0020850710101d03e110811409402880316860 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 384452517 1250 384451267 384451271
    0x40807021801060824060304050313030f060b0603281b05070605070807021009020a030803040f14031602040f0b0d0507080708031e03150603011e09020304020603130f06 74
    0xc0110709821021009104080200c1c10b4080014141e503141d414a040c0c0c8900a908000f800d4500420080305410142013550988004e000d50b16006900c40c1411010f1401a0140b601010092031708506032494003034070798005c0109000b8810700c0640a8444038204111544684040d400040d4810082420711000e0071000d80201800c001c050304480105070050055009100766500d008013500c030584140c9104005900c40c3c6500da661441c0c0d9841041124801000301203400e950b900d1305010b64105413000d86114401c08230502c01c00c500b10071000703051200700e00554280002d54403204212041144064026511042e110b40f0345100b03130740000400040101054800342d440d00704281d544445000d1407035a84a80203020581c02c2000042e10800004d11600b5440505800e409a8654002030200b90b03602c4400c2c00540034665414028601078100744045458031004441038540d0240954001c4416920400510000da203680c800c030390740001010320300001e0703403150f00d4040c080031400240601241c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 384453767 1250 384452517 384452539
    0x90d1d0f0a06121503170d0228170606030114030a02121c03050910020a02011409010209040c090b090d0201091805060909030901020a0615170d0f1404090504080702 72
    0x20760089502000f0210400b030400028956802c0441e4030011808080c2803080920161034501c50448010f20f02000328400242c10400003448090750682e80310181c80c0c0b00000c2403c075030718480e404200340701041c60741c4008044600b8050042400c51006025084c07450540001722182902c0c10040c002400c0d9010b003035014802c08511120392600640c4910400c900c1c040c02c00d036485c0a11034000d65004d40c014002901c0ca0041c03c030003101c02035104220240955485410141c1d215841003110742c1304000c000001750366412510100303c1198980800e11060220030001031006003040001d03a00440b0054070103c5200d121b81c00140c4035a0401e9100801c080c0d1141c0080b43c443d101c4c0e0b0402c0f401600f003510001007680301d40c20403079100d00603441c0c05801a0711480c284004120b00d604108520b054009000c0c00c55501c814010044c0b001c003890b401810f6100d40341a140740c55000e40d4503182c1c3e04041c41c0945030740c05903010b5039546205038031031810202d4448002c90705002c1000d049481580c0c0c02081035090b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 384455017 1250 384453767 384453779
    0x213080a02090115090608040c030b0f042f0d081201090b0a050f0f0d060b0a1d0109020f04060809070f0306090b06010807020705040915050c0d05090d1d0f0a 69
    0x1554000c400301d0060000400000344603004400b0b0700504d04250311800101c82c1050411282000d00410030b4502040083c400000308954003a000c0c000c02c509004012035140c5403d00e1580e00c56030202640c1660300301e462014684c100204000c0803203d0848124031801a40d00b840d110900030b80080c0c218a00c20a40000303a005099809000781203815074100c4150741e500c1d0100305488402680c8a60010a0349266261616040902e034408034481c0000007900001400480d00440d526008122185c01c042800c142c58560380b12614014101e114044d860040e586810b882940520b11601d800e10001c000402c04000041c020302c4041c0002d89101141f0395500d060200260005a0080d601981002e010420b1540309201061140d00140c0050003a03d24200a04c80145400c41050f00c0d00703819180800d448441c94001e80b40100c3e906003206448141c01d4041c001103c101030280482d40c0d00c42154100840d800c035940120307503003042aa10b40c1134049100401d4919200400d1280d01181c1d01c80d021400d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 384456267 1250 384455017 384455023
    0x31707202e24030c0614030c0309070b0c030c061003021c051009080a0809150105131b021606090510030e0c190801060e010e0a050601050d05010306090b1609090b04021308 75
    0x40f40d00540e2280c10703040e61420251040b484a40204441100810000b2507841003a0002d541142c100001c440e0015038079050007006401003401c4403d690000601c1482c0240708000c127a4000000507107c0ca506403a5a00007000c0c82c0b00c0f60034114000440950303c405000c0d09000100100c58640c00a0001d01c036640303030240041d488401d0301408568041d0115501000000d4072200c241880044240c00381d00346010400040b10613440c1c079410315180c03810300c615401d030b031045000300b181e007900144002e0032031098240c2d4901503a0007641c108981c2c203500300f0265a4054030112401e10781e00b4005400c1c15031005403800d25000d00c502e5500103a0341c0f00c8800e0700b0b20318011541c00f250b0074030000b0402152944c041c89440c2000780b1036200c0701700440000c0782d6941113035801a074000d40141006450018490346020a5481c26030040da091543e030400d18052005424010303070b01c450b59681400b0421101203010b0400e10031801580340c0b40380d4501c01c05020391500d82c1211103104c030701c442612091355074000643d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 384457517 1250 384456267 384456269
    0xc0309030b0114090c1804110f0d0212011205030306040c09031a0411030d020a08032a070b0c0901050a1817010e210f0304031707202e24 60
    0x4004c12420340010700b12a00340303059034011030b280a450f032204649502000003400b038809229040070410081007560445000080040c1e000d03000d00561545010040342d052550f05030300c0b0740c149400c0c130703892440060008000c403944235400701c40005140c0503480e42141d0601d2540c000a050000340e0740d140d50b040700b900010f00e00c81e5214118918411091f941415250402d2541a60150b0301000c0080000348410018540c0891007801d1040c1c00140300010082070840c0010011800c400002c0880a01001c031600b10b9109950410244c41c20141c500003c01512580c44040200304040d00203a40c86141c0041c848003c0c504001da110700480008059030007882284494650b900c18110750101c1d9040e0114045083e80c1c242c0354039410b000c038942c0c0c001601c1d40010005c400b04000ca951050000200c00c854234024006682c40300b1112041c0344003041c3c64901d41c11140d40303c1e404400e404030340d0044455200d04c9081c004540a17030390300d50220f0150180600a0f8448110300e901590140442d01b4844848 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 384458767 1250 384457517 384457519
    0x30109050c070f1b1401050a0503150a03120210090c05041d0d0302090906150a050c0c030307030f020c011e0c11040509240c0a0f0c0204090606050f030601080703030c0309030b0114 79
    0x44d0b021503031440030303440001e8411080e070301040080c0b00c43e440c55400360002c3c5a0017015220b4070f00c4c0f200c0c28070b40002e0002125801c100d919036120b22104030042d0b0304001c13010403002404420440505c007030312240781c010702c140f00e541d02c83c948a1035118100c00c00700500100d5400503404a0b640b603207580101030040c2d040a0080b50190480344000b903800e00d450000308401e850b00c4000c4924000307110341d085845030301c0040304010f548151000c01d18075460400003413903142d000307035185d920000484c0d0009041030703000c9070350504000040d00c0030040c54181040c03030002c021080c240307480159214502143da014001c0c01c3d15501c81e140804000e14440d01142c004400301c3c0c2c2c2520401030320885a10300940607400d0341e041407604d00c107000c07178a281401a43c44240010391400d200203844c05641c00076003510701e084811501c00780c07900410440b606094001a104140440141220b0b42c14001040e85e54001c51001601300100200c0d81030500d0700a011102c043c60b04034400491568481d00120100b07541a00c0712 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 384460017 1250 384458767 384458813
    0x50f0a0605190203041709010c050d021e0a050705062a0d030615080a18020925050c0604060209060408030c2821050f0d0b0301060605030606030109050c070f 69
    0x15102d8001c0c1803080701d00c201e51110a43d0104080542d020501c2d810042d0141d042c840c41020040100e82d0411000c041c16056600a00000f0310207413a052084001c009d41228590001010350b00160012860f102520000d071100b5840d00c003280094401003207002a8244484102800d032403c5c0580840d0310340c00c1c1c140c1500c0c240a15503a82e000003420104110592000401d080302103032030422a9040300392103000c100e40c00d48550081d0380014030504401d40e01c00030101000103e040040c1141010b147c400340039400e0042c10321107071001903034a800000f80000d00c5240d000410044584d80d050607140a07010340d0007240d031504071310605140d503407040165924166009004000c000002481501000780c0e00c0300b190903808140c584101c4d18454088940c00a20a084c484c80081002484c007070070600fa800c1c80e010800044400605003150b400360052010080204104007041c1c03140c8040301c2c11201030500000315a541c40290001c1c5004041005207891141022074050190003404000300c540b2603030701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 384461267 1250 384460017 384460051
    0xc01050106020a0f0807020105040314030c061803120c0f040e010819020f10030e0609072402150c04050307030305041d070807030e030417071a25050f0a0605 69
    0x1c10b907030700c4100c41d2008140d0450038821400240850f00681203551060402c00d040c143c41e40c4c0d500003409400346815040b44d00108030303000c018904120080c0c10444032015280a65401d200582d2207201c1c8030070400e2030b45007000115071008800c0d804ca4012140045c400f94440351038001c082c1d0ba000081c400e03e101d5216080e20050aa01c070040c2040449600803c1c009000b130000046c00201d64071007081205040d41c4130318150b40c02c2c1082c003805216524040151405505061030400100703202d0200211411045c0030000c1c48503000a8440280e4081d40d1200c020741d611a00c0c07141051042e43c21454040c016a2030000c105074000d07002d0815135000c2061000d00345103440d40040b003403504840d1480020b58690210f05001d00a50100c0303a40546141524541611030b524036000074162040c003265035100010400400c40d02030820100c41c501020039a1604041c107141d43d00c5000614031201500344219010001c00804001511108242ca002d0300c181c2d202c503003408402088101c5030b801d0201800c1c0a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 384462517 1250 384461267 384461279
    0x91206060816080c120115032105120f13080705070501110a051216020d0c0503010c050c0a032d030b191a0f0702150702010909050408090925050c010501 67
    0x1c034000f5101c43e24000d0040403400e40400c0707101d0f071551450195555840200d1500031182c1000180554022407100841c0d01132142001c1e10501c003000001e0800600f4802c82e000c0024200d4802d80000003d01c0c61740054844034038072480b0260703002d402080c03601c0015101040083c045901800c482090703d60405c420468405079881d420a07000041c8035410039615510100440b0300600401c82d81918050614030156000c03c412504d0180300703031586d1010860030001c5107824000d02440c50600c0c5009800d1202f0881c1a50347c070700c6102001400d21080440051002c40100000c0140c00403000e40c800508200c0c2c40064010401d10b12014025400942c0a00244461046402c11100c001c403d80c07030202c50100765a0b15541041c9001e01a0110802c0000c0150340c402018100200d0030201c00c0b603a4181c548005010700407039522541005060408001c0444c0e03c001c01d07114145425a4450020380e2201d4650b051821080c0c00e1040b101400c150700c1c41215800700103402100b03843c1008106a03600e5071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 384463767 1250 384462517 384462553
    0x1e030f0a060b0703021e0705041d060a020903120711060315030c04051021020406030803100909030c02010f0e1c020109170319030605091e07141602010912060608 71
    0x20501a0143e444268101d0032105420381203c295403205090300c80d008d8a0f81e0024050f42d038022140c40c078441c0b03940d103071a400910070f1180c5a00082a51400c51408084a01203901c840e0650b2403002080d034045003c03020b210214a0000d41100c000f013125a0f80d02d070045a1921070541d18101c03074080d1003488100e0001c0e003010311a41c0c0c000c000758010124098a400004010040d60207040010301c07500d00707010300042e191406110051031051258640300d2034a00c00051a2111503441407030018149440200466086020368050a40a04e48294654403404081e10724a0301c0d81591138004220382020310050100b00c5a80046c40d02c01d0f6190007035079030382d1845244056440d03058003103a80c00c00c004482d1002001d000d91200b00036136040c0828919540c00000c1c07a00350007140c0060120899120482101c06080003113a4407040b1800d00411603550000b0031380880c020401d0001031201d014108000396030182070000010040c03002003101e656a5031030404090300f00d91080540300d10070202d5040c02d600e0781d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 384465017 1250 384463767 384463777
    0x6031104090b180a0501020f041502070f03080f0714060711010b0901060c0c15030501090e0316020f0a03150b12061303030c031409070f0605070b06061e030f0a060b 72
    0x4110310141ca0380b19000d80f070048641680f011030051041e4240040090420300280441d954210611034513145004800d1f010008604c6401d0110b4008000a016440302850b074501543d41045055031120001040344445104480001e40340003080f45031196840e00000301035101e05145d5aa00c501006840320003420b991190320290380c0000300c0d200602100e440740064801490250f200c08500641d04d50300104c00e0060201c0440000b62218010b010003c000d0103100c04c0006d50000441c5440d00a501c1c50080f00c283c1c0e04000d00c54210421000703190354400d407000c07024580000003150301e008141000340082c0100603129015043c1140100401800801d105200d07014404890700c5004032031f81c04400918008020905050f5601c5031010849011080a407069841c0402040200d041c01210800f8500950140b000c000040013001c2c0010305000c0003503041031040d00c0c12512082407500c094a500750000d20500b4090f000300c10800c0360403d0300c21660080d91541030800c0343c103881d110303441301c40c0c452 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 384466267 1250 384465017 384465023
    0x1104091b090f05090a230a050609130816020a0f080106170d120c0513120303110306150c0319120b0423090f06091015061e0c0b01090603110409 63
    0x880e00017150781c80707113400074401d210b48400d80d80302120404188001015041d00c101603400e82c0d0b20700b0040d40d401c00000c0150001c40d0b10303942c01c40300d010039602e40800b849a10300c0e0048040040741a00210f444124002000d040e60280d24a046611031945600134642c1c4c0c4150130f000240c0e460354034440c074004100c41d051500150345503214014600388000141110a11120803c0b900b00204d80040c4280600d001c00781c00c0d04508410140502d050003001c0d58690700790300e01d1030541041440026581c00003021000e0300101c6001761903450003034900c0d0540c05001c0d083c0c01c0d90000540780c00401640420404c0b02003d10201c1000380c1c94800b0284002c03990840310700329103c0000c010340020084600d2000381e000c28000e08a170300c80d0740303250111402d003201507803542071543c024858110501940e015114000c0e070b8202e5030442d81c900d0294010101104401c0d046107100340742c8280709005101e034030000b03141504150030015079603460350884018100c0f440103817000761110354440320270f250074068540d290750 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 384467517 1250 384466267 384466279
    0xf0902090c031306020d05060414071e0207090c0203071703100b07080c010c02100c080c0a081009020f09010f0e0d020405060d020d050d0f020d050a031104091b090f05 73
    0x18500c41c41180c294005003800e4450346803052a1800a929400100a1940d900700c001c0b43c6420b02c1d5040c0816101429070128500100b031040052240d071015040051001009118003150340c04c050590802000e40c001e00703283d900305040d5401c00c580000007414120b11620002c540200300b80d684030006c1c00141e41e8510f031a032054004000501c2001c4c041c2442c0e9018101072490710440384404c0c0e0860700100b0102000d40c00940000c40407807610312510181d0343d541e0038440c8552800e44030703000c0d041c45540c041d401808001804035664050b145001d202901100c0c0086544030482000b2802e250400300d22580003a92440046040a10543c000080884054032604100140b5803c20001d820000d02c2550001c0a00c0707035940140e0384055000c0b0309603001d00302900202d0031081c4000c050075040072850301998001c50042001a81c810111882d60f006490006150b450303081c4184810300c01e036030100e000142000d2031011030750100200380b90102603d031144514180e80b0100005091114880c05034807030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 384468767 1250 384467517 384467521
    0x30c090907091e0507030506040e010204030308061009030f0b0916060c241401031502031608090c131b0914011206030f0f0c050f0913050a05030414040f090209 70
    0x10040e500318054a06910405508219440c048032041302c808486010004c0c2c0c0303550602090381014401c1c1c6160b600c58000a515180c210389000c1c00f10b030302c05018280141000024805603e104940600141d03070701107a850310340e40484c24203194134a02900c100b185400740e2010b0101038080c03040e011080f201642c43e011051003807038070b48100038038044141039003100da80c14800041c2480b40c8120290403007000d41010595045040c00031055205075460525030f8070400611400c1510100454079480551504802564030340d4900d5041545050001e0f41100c0b80401c0803800701d4850700000d0303604032071594104c41c441c501001103c0604452007051502d000c840d150f440254440d4034480c0382c00300000d10102d101552983d4440d41ea4003545420344480c004006050700300304440401ca0010f040884080c6000c60043e000106400d50260111110a8403009900d003004401e000c0e20002940240036240c03620794989941c030b12080a030181d548106e1505040524242d224810710404580141c003441031a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 384470017 1250 384468767 384468779
    0x20408212713060603021b01140f0c0f03070807120b0924030604080415031e02030402040e0d0807020d020f030a180306020a0302040501030b24090f09010311030c090907 74
    0xc186501d80c854020188146050000d05140a01d000034490b81e6070050b43c4071150001c110b408810035241015a905041c07202010002000e90340740c100ea112100f190381030321001d442101d54071601600c814400c0e00482040500e40d08100300030310441c55501c0d82c641d14290400041c04448240502d179910440085c00318800d001541440c0c502a0003030301090704c02600810020b4a400ba0440c0c0c00c0b568441c0c00a414402c0e22045a2500803041c0d15040921682403e0707104849a00c07403132500342c3ca07281d5002c00084c0030365071141c02c0180c4203a01d12042c1c4030041c1d50000c1c000c028401c00c841c00b0000d0310411028031181440011808454002d01000d10704180007000300f00c5225407104400200340c40c0a1001102052451009100c5001e058800580e50352800001505a80c01c824401d1b105500000d46405500130000745540c62001254100342c0e01c00011002400003101c421a054000d4040b0001004020402040406660046044480c184424020400e02d44d04c2201d004a05d5005450b042140e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 384471267 1250 384470017 384470077
    0x120e09130b0a02030702070e0907031a0c04050d0201090509071701120816020a1d040302120307050d05070315080a150b100804050a060c051c0209060a05090f0402040821 74
    0x5e0f86881a6903280d96a044100aa104183d80c010200c0e00508010001c11041d10123460b2429160b0380f000000d80740142d6001141e004900c03d079401024008407907001c5a110305040c0014020040461000d403c20550090500d10303442228030780c170301c0d9903400440c5200d001c030220305a00c5e03401202e580c90541011860380c0c03000038640f4100d810240c1c600c00804c0d0006248840b201203500034051009a142c43c1c14020303e4094419183c0a60700010024088000d174001c0407141201c1d400c280c0400c2c030381c640346402c1f0000c219007008030403854a442c2020800950201e001212070f40071307468241c42c010340000403e0807904502d500c42d500c00c0c0c00c01800303060b42e4041e80c40154003500920554541050715110034082c0c64041010038001030340041c1c219209101c80030290384a1841940450402e480c00b0040303051441360341100d00a10801044142180e9905222044281405002552525520880c2c6d59880003601c6001740b5184000208446814180003a9400580c80c1e200000c0d03080d00c00742154107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 384472517 1250 384471267 384471271
    0x10e0f150d110403140712171c1109030c040c05035a0f07140706060803030123030307080304020d0c0e01140d0b0708090a120e09130b0a0203 62
    0x1041d140c4904850401e20212400f4200844c06640c4a81140050309451800c0064503000f100d01001c0344900803001c210302d000f1500c0f20000c62400d107a03440c0784600c1c480d00f509103414040e600107030600301914540c61900024003030404064003100c8999104e84204001d03a0802110350001401c02d00c00100c0100509014403080c00c90302c0c00400041d125420241484902402454101c00003401c01560070740d1400c20305204081c518414440b00e082c0003c80c14486403001d482041041507c46000803500c4070b000484031041e5102c1000c00c034095484c0c0c01e46442e50800d10a0301c9080b002902c0181c80310903000e8103551041c0c1c0080286141900b80d54520007681c00183c03003a42c0000d0486054800245102030000184c00b5551290113558909441c0b210003219004040380515805c0714120005002c00901c960807002508110065070344070b40303c4500d04242600050300c0001c02c0020030600d1500021881500102580c80040c503544e0b441080304c0181da1408028201224140003d050040f6035000d0341d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 384473767 1250 384472517 384472537
    0x603060d02010c060609150b12161713060507050301080703022710030c05040b061e070c03060b090a0c020d0e0103020408033405070e091c0e010e0f15 66
    0x46002d45454031201c0445400b60407200d4039540c0d5a0382c6548541042405400906000e00340d2449e1561002c501640060302510a48c1d45144662000803440c3c052415000303824070005840d00c0d50300c1c10b00302c0d12603090201817003918001e10b0400490b0000344598102d034180c03181c240040c15500d01e184d0912126196049060542e0102503843c1c021504092100d103002e200c2d09281d6075115421414040c1510017985c1c425480340e4640002d10030562a441c0130796070382501040f100a2074201c1c3d01c2d0513032294466039100600e59014002c01001304541c652000081782c106441c1881c482d5034808004040b2640d5800e41e82c0980e0120301e00307140c6103100704d02d40c01c480d1406140c05810182d56205103840c5422285548050625214115200c10610b15069840d14107071500726220303500340e4641c0b0740c4501d21800703981c041c0c0400c00005007074000104410340c5c20311402042040c00400601004005160300b8800c940007801d87c0c11040e2680c50410b00011407043c00910101c0c540c0c2c409140c3c2d940e142c1c4900110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 384475017 1250 384473767 384473777
    0x605030c010903080a03141501020c09060d020d02040608010c120c050301180e010e030408010b011202041d0405190308041208010f0506070f0f0516090c091a0d2a09050603060d0201 79
    0x180040c000080405030042c03a2304c0c000c0e00014a01ca2002a040a00c401ca00034001d60040c020040d840e51072844081510350103a5140b51030003543d0000c90060000380c2c01888a640c2002c211030342681d448004032900340c654083c00c10025030081d02c1159580300a125000500f034031807940030700710850356000680c00150035000140410411800c60305640242d0b1150909941d41c5218001d00e582290340b104c1d00110350902149098100b80745400a91800c018803014003504000107010070404000c584518580341c00601112240b502e8010410794007210100da4404031240f1a40f6082e002e42081c0e41603c0c0007030140880e035401c0c1824050b26130072500b02654003840d5030459002040440c0892038505016102a0480071004095080c4c8050141e202040702890242d441c1d4613680e0154940041c1d5906520b40c01e814000c920205415010b80005101003034a03003401c01d00d0b14841da120702c52001307c1840000b8026400403400f41c1e503083c0d003441f0f02e5400010800c0040c5240c0360107480c5d651882d1050410f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 384476267 1250 384475017 384475031
    0x51e1b0a0602030106020d110304030609021c05010b0f011b0b070c0b01150225030807030309081c050c0703090b09010c0b0a06180501050117150d03120605030c010903080a03 76
    0x1009250a24106080d10032030b07030001c01403200c00e50502c039003c0842d42d0b0b81001000c0310a440d8446075680309601c400380006035100002001c640c0d0f6943c81080010000b140303078988510380c1c20114001d061403a80240708100d07040b0f0344005c035405400e044080d90900ca0740200040c05584407100301c0c0c540280740380c0410504901c10400640460300c0d5502030040d1400520000401c0030003e440c0203201d2074841e5041c2503030701e40c024040c4c01a0000b9001da17035010364910b4032130100b840c0039000f405001600410300000443c82c000080340d40f08840c015002c402c4000c0c0f02507240c1e840d034020103116800000d4002100e1200a02100280b1802000040810f241182c0c4034407131601c1792031400c2e2003500c0641620752076200030010b4004401da800321030f42d204401000b26524100c00a00a011b400303130300003141c0b0190310004413503100c40c43d1820310104000d001181c5d07100003460004d140703a640b007500441140c82c044012441d03090004145444100c1a1528a1400e0946d281e02a00340c0009010034105511418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 384477517 1250 384476267 384476317
    0x40f020c0a08030f09060402130c050d110919080307030318020901080a030905031203010e0702010906050a090b010e010f05130b031912080f0c07030e062107051e 71
    0x44003031401c502039440342d9102d0502901003404000090b103d4034059200c4418400540c0d164020492806100b05c800201a1079540c4107a815010b0071150380b0400386464220355021019800604454108840080401310352030b01c07800001140b40540c1d03281d80c3c814402400041d0082c3e01000550802d40114426900700d98001000810240c0016403240c028244060415401280e058042c10301200034041900d800001c0040901052040104451801c2d010a001500039400329000c40d070400c1092040f4a849250400a0464070004454082e81480005040484d1902c594140c3e280881111800b23440c042c01c002c3c41440840207200c203c1c0c0d9490501300c0d075940800c0f810400008900e0000c108010078140b1005002c1700342410020f00c4180810444c10310070805840c2d501811640c0040c4d1a4041ca0400b25080446104000d40014000410300b440a800005040b10045c0d01040c0e00141d030b9902000701d400d406140d18501d000c41c084101617002c08c0d4020084d0201407a645410881c0c40d450f0f079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 384478767 1250 384477517 384477523
    0x40b040b040e0702010903080a11160c0519030206041a0c0a0f06110304031e0203040b040803030627010e0402040f1b0315060509090a0209030a0302010f0b100e040f020c 74
    0x80d0044a40000008081241000c00440d0301d0780111980001c014900c200d0720050079401000b402102e43c1e42da64156008448941000d544543c1400e0603c025040590f01d4589030100e001c1c01030038450184184640c9611f82c03100b41c078000790ad034080d00e89410907141414222000c102241e01540000081c064200b540c60704002084145000e40c1540e640481f56081150442c0c40e038413505006154200100804a41c1007801c051598a0581000340c4c0094400412403c500468000401c425800500050b40c05000805035014243c00c031100725060700040749050311020303900414004504802d0040180c680c6506045502600262010565541e425444400c035407810105120040b01d48040101d01d40d40741c850026074051494101072060300b06000039019010721622144500e04403c0000c00c0d000e1642c054171090040641210b000d4411490080c0c0a481040c4551060f42c0c81d2400c1c8140da4600b08884c0c40c50f512140c0c50300b03681c0ca00c1f80e90520001d4500070b801415465000c02c01100b00c64410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 384480017 1250 384478767 384478769
    0x9030807051513020d0f020105131d0c0301031a0919030512010b0307120e160f1e0b1b0a02060a03021b030a020c010c110307030606090506041a060708040b04 69
    0x90405001200342c0b800103080c1505024140e6021007030090403a600581301c0e061080c019a4118400015111310344c40103c4280c8036030010b4542c08046001c000441d406001c84000e00d0b041107400d071142981d80c0b030f0312440740d5000c2480090710301100c4010211741c81030f500703403030700d41010b40307082501d1560300d030010040c40d03075808000f0487c0040c0e00002c3c050401200c020207c0d02400710b100041e455801c09000040c245010f0107040d00c6019940c50705030820740010880460740009800e90fa140c0c40b40c0c1c49192442030001d5118140c0b0020060702441150702401081d1029101c02c005520704100d812000d070340421508413006c0f8554030500780d02c500541c0c0c86501030181c81034255030150751580e0300000410310000086601800d540140182900c1c2900428001c2103400f0a181c648421b00c0181408d20403014400982074140c014500c0c04003c0c40010b400c20801e17140054010300c80e544404051004a50318480c500c002c4a420a442642c2d03894502e000b04030130b40c007c58031030342459111400320802d0b81c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 384481267 1250 384480017 384480023
    0x1030b041b1401030f060303050f0d0b042a031427060a0204050f03031903180b01091a030c0919020906030c040f0503070e04060203070c050a0303090219060c060203060109030807 78
    0x2d00b802c0b4407040d40c0d01d07000d151340c1e0000c46181484203070b145a030040c040c4c0c0207a1448104110f00490354a000c2c0901c1d80c4401c40310b050040080c00a0007011038034a2401d61403034161640005864001100c140c028040d0091200c0b021510213219607404111006c1403600c0e801c5111880b22090f200420000100b2405024144004005996910302000c003e1103200b01c1103a140603800038002414403918200d40210404000c0c10081050b02c40700c24400c0300f9540410008006012400001c50307a1900785e400100c0411000000c861140f010504142d90348000c5110170b94881940c100140300c2035156440d0720001c00b4501405424050110001340e144d030012220845c0745000071030104483d4050803a4800206000d1f00502160760900d808101c90020007800074201a400202251645210300d44500d082c0d44c001e42502d4444100e440c005010341488503060b4442c80440014800b009008595682180d145895807002c08403d590f905000c0d410081c00241403020030200000070544c548020b00b00c2c03507c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 384482517 1250 384481267 384481289
    0x4020609040e060105120d1205060d0b04030201021806090f19090908121605030406091b0902072618150c030d05090604020f0d0c23090603011401030b041b 68
    0x20400052184500340ba04461400d6444800300d02d00c1f0035004550461000540355020410307564001c0461039403880d104006019101480801c02415410b601800c03c100c07480c2c04102051100608000850140142550303100055135040500b520380807801803c2c101c16681744014142d40c802c059030407030310883c8043c0e030020000075440900264814029501108182c02c803141904540310040c09400010700040c0702540d01c400043c2446403030140310181c88405000300b104140ca031082c2c00043d40101d00111041b244450072003080300b0110140c210b101d440c01030107608201200c9101140504076508298005130611540e40c3c80d0012440100803500c1d102c1c000703555468804800e003040b0f5000074515040ca4000703006100041e40e801c013050380016400c071080c80740000c00e410210305a4000e0350002e140884c45c22820a00e03d40000b40c104280c40086844120668402c8141402d0300c80f140140c00c6040d003244014000100c0e00000660003d0090100c28a010401d90321925150000c3d00002d51a027 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 384483767 1250 384482517 384482519
    0x3090f050616020f031e312103140d0603050a0809010207140d03030903051b0f19170703021218120309090103030f050d02120601020d08040503030a0504020609040e0601 74
    0x98040202d0744000e41100c000f103160600d503d04640761041080c084615840c40001c2e20b072046000003028401c7d581d65101d10904000e6032140d101004852407042c0c041b1026180b04070320201601000c00300032540c05498408100001e000018426400200b0064034aa61409c0c08000300300d0812007080c03003078803804865a94040032400039182c00125480343c5035800881c4e1501c036994a0780015082850340c1800d000c943e40c40c8624003034455008031401100e0840e5802c206101c25500081c489412009080c1a00c1100903203070761802c0c0e00b200380c0c1b0340500600c1d00c148600b00803403001001401070500a105031f441d0910200e120606c10380c480c80303108030010910709982d001c82c0f900006410010400700025860644c594020511407081403001070244440b2090700c25100d8050800ca41c000d00518608545d100c0c0103089078016484140e807807500510940c00034104903070040d465039000d150464000c5013580e469201c41d6000e00001802240c0213034060000d040e80f070310746010362108482e180001d80140c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 384485017 1250 384483767 384483811
    0x10b090109050a080a021017040b0406060803131a070f03090e060103020403020f0d0203010b060403210c0816050703020a12030f0e18060a0312170601140a03090f0506 73
    0x60301c09400940c0f04086600c0c3c100210710001801e074042c60b07410307a040d030031440e045902900d441c05203c18422aa4540ba002c0008100d00343c0c11184c816481014200801c60320740c4c0c02c0039903038050521030303014039042c40f6000e020340303002080191106031085c480d0a141c031500b680d42c942e10700107441085000c030720807400038802c103241211582d038010800e10f81142441d1031500082e0f0003402048800b8040c900e40100c80c82552003e401540c04d41001070b01d141d40d00e550301d140c035913141c010ad042e00070990f800c66081100442c4c403510710704081d190450406801e04429116680c170907110510111000d1084510000050b20b4856080004080702c50746101d00550780d05001d40440f4000342c0030010400c0340a034844440e40d5408902c69202c1090380b03003410b40c1d0b407280301280c403000c5240c0000e029454040904e06000394480e0900c050b22141c22440c41d26038a9440040d5800c1c458100c150000310014024001c03040c1c03283d80502c11150092250b861000a1074807420708100055507046040c2e8100c02c01e551213 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 384486267 1250 384485017 384485027
    0x106120c05010311040b090d0204050702031209011404080c0705090c09091005012a2a0f0e0c0d02071406090d17040605090f010204150809010507020c011214010b0901 73
    0x1d02003030030148600407055030703402228400d901628400220104113103050380c030381240080a084e0301900800070790410000195132074011020400400c40100001401110103015003005806000342400e22501d503a40c4a0510b50048e5901008501c0743c1000090740e42d451a11240c00740703049602d400d5590041406028182000500b034000c03440284100b003005990014041c0401e603031060424110342244c0010614013645078030081d100c0c5454040f01000320311101846050765200c41b03000b420117503898113200c2101c203c610600c00c00c40120b50014400b155000018252900a11f000515008460f40c9403880080403405181103a03100a0412000e480100105403c02d042404c016210040740151007080d101c004100034029619880441c0e010042001381d40050b060400080d9161511120300011140c56240d0310800500300102082540c8018802c590107400e43d07a020700011107101c03006488441504400b900019030303c0061144848444406ca0301130154450320355a10a031b01d03000185 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 384487517 1250 384486267 384486269
    0x170a0f0c0e0109050f0115030605210705150304060b0d080a0201060f0503120f070606050d0f0c1202100e1906030f05010605270f120a1403180108090a050106120c 71
    0x7103c18a0030041c08000103a0094560440c0c9803003807101c140d9a00750702e0032400341c222588034542100381e140004d1040f003031551003900b0b118807440850b0304090762881005004500707007040342154002000441d01091070f54000345980301000d04000b080c42d02d10356803a030865002840f03040060b5540c91003030101c0107040107244010031044004100e070250b103214001881c40380400c400d050300400507510f41001280e400150041000604802d010b104a0521168500090303400f2149184030031008100341c06455129064160050301d000c014420444050301c0318003054081d01d9005070942d080303484840601030f00700054140703030742c001c40e80480c064010070036650b06810030030a00030280640c0307207080741108000d00e541d00c030034110052a00099001c503002c007100c602c1a9070020b0744a007401140000c0081c000601c0d03442411504820509540820740328000c0c880d009404803060b100389000d645c400d94100b0780000d8a142a5001d1500c80d07038030135086624940c03100350956500742100b02030100340402c1030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 384488767 1250 384487517 384487529
    0x10080609010f08070e0901060807120b0a090804030b06040b0415030c0b1908130c060504082e1e0f050403081303080601050a020f0f210c07170a0f0c0e01 67
    0x29810b6040000d12501d401441c02000c0d1001c1003400002c001ca9002d400c001c000341891070070754144549980c01d60219a034001002d0701c202c945813021800007000f9110340d801007030300061a01d05050030742c0c0d51142d00d0380001e800558480c1d142e0380c014990340d64600c13440780c456071500c007107142281c914640201c40501c182c0c491040b445050003228101e410040d00d0b0008603905e481d00030001d41d6a01c031103490350000800098400b140c01c07000030a80c190404002d100343c0d038550301144c210540081c819080e1582c1030003101208400f400481c6903880b1941c0104128810001c101840b0590280d5402c04480389000c4108270951904240014160805100741d08501c2c164801c10000c0c49644015008110141081e03042000004500308614400d0200400d6050a40280c4850708030380e100c996514610110300414400c81e02130303482810b240d0702c8211451741c5800f0003e070556900d4141c2c84452190030400c104070a0046442201c0014180031800c02c041c0e104101c0c200c190360a0041c14585901d058100c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 384490017 1250 384488767 384488789
    0xc060f1b030402060706020705120a02030d0f09031d0121050f0f0f1f05180907050d0218071e0504061805180c0f0c0105040501270f0c051008060901 65
    0x1100144c1c48000c101c0f000309400940240e682d81070383c41c1440c688411503204050003040841d40c41c8485901000500c2a00000202484403030801d8104e40100d990a0300020045860440c040d40c03508601d0100740214001410307c010050700c296000d0702054441106200c0d810740d01d008000d40c0400d0402c080b81c01c05005c66020103503140c03252b280d034081800a016030705401303c42860b00c0d100c4844405101c01600c0080d01e0380f4109601c00c040b020410505034cd4030759150080e40404689400c101d8140b58203990014441625030f00d102c96100c102c0c1001820b04000c0040008050f16409410f41f141108440c442c0d446940e2079250030402030214001036201107a000401404010039541d0080802581d100c0ca0f09901d42601c6100c04580c03184190440103100e00c40c0851079190900c01944082c0c03086008100901110251701c41003082d008404201850944502c515030001c03641c0c240252074607901c0b46800403440798a80c2c0010b400d50b804154107100103906141000054209920000e00402c0213920b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 384491267 1250 384490017 384490021
    0x714010b0a140609060a0c1112070308090a0f060c06061e21021c0507081203070c0c030b0109020301090e0f0d0507020402040e070807170106080a110c060f1b03 70
    0x211000c40c00c0c4150300148550500b514030b40d545420403183c070020020003c503030302c0908031400342c10442048025039121080d580d40c1310090034021100e419400402d000760010071304550f1006481d40025021903048290000e010910500013440c000242c602e44d10381c032050084d5850510240e03007107500082d0801404c9010034a0305401c1030852020360f95041c03000086c0440040f901031200814020207903204040e00803036484d52403809250b020050140c01903804844d2502c910715600d50045c140201002001c000140701588652020b50681e48070307024031110310359a6200c0d242510301c01c0c0c0101001d20b80c004010000d2416038030540f00c0340c1e11a08090706c059095028a540c6842c108000c0344188400080c58030215600c660440f000b800c6074000d0851780c0d0401d100b006081d0802210620085960040502c444c00a050783c2a8100c500d0fa945240c80c60341e44e124054082d00c840b22420341d0300101488041065076080c002d00c0e1049400d80540841e9147c620300c5101c0f0b140c10310002d0600034a003002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 384492517 1250 384491267 384491269
    0x21305011e0803040603050a140a02030121020d110d05011406010306080c130c0c05191a0f060d300e010e0607060902030f100516031a010f0e040609020714010b 70
    0x816a0200c170924240007416507114101d00c1d01a01c07401c2e801c0d0070700350103242c1044903503e0031b035000c0c5041c0d50000a800f210000d071307450695103200d00480041d501c807418003c400005a140b5400d03d01031000940b00764819105551454255403a400041001020342400c015880d40e0520030b9030001e1100000403c400300896020070410030b003003400701c803089440300742000c205800703076503c8002c0d541d102c1d0442d42e60300c1c003981e4103001100d00c13050100c0c2c5031600250001150a502c11100380034030219001103c2d1902d82c0f004115440c4a5420225520040d140340074000e82402c80c4c2e80400c0e1038000228a10300c100040000f0721200841e4150342c10f1103220001d000c001d480b884161910030354001c2c0005200e01c003d00001e841c0442c01c0020b60100d201e45001000e20f180c440d000f1a0003409080703c1c001c60300d4100035003074041d0307200500098079100e0100708241c1a50701c1065010441c02d01070429001402051020806645d1603800c000540c6400050311001c0081c1c0e04a004d800d03d018000800400003180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 384493767 1250 384492517 384492523
    0xf090405010b030c0a150e010203160501141f0b071106040806090c030f031b030d2d0513030e040b1203070c0f0f05010f0203040f2c0402031c0309021305011e08 70
    0x1b4100081080da1001c980351359008004444e1658600c01c40035202c402c19140160203064180d64942048842c900410340013550f070781130700c0d42202d2050030554003a800c10113044074680204030305641c1c90301c50300c4a1800310303114000240080d01074200a00a20710700b01c5180c500d010f502500c01c50003907001507400318001c00e01005603000c0301c6001881e04003902121035003034554060b00141e0b00c9150714010b18070014042c1161240509003010500140150b006804201200d000321003a07240010907410030400a031080d1411401084001d000082d03030fa2044001c120030200100c084082c0b84d200103102418014202c900400030701050b440c1468490602c0d2009100b50100e103c1d080c1840101c0d144444103500074401d48024045c04008980c1066035201d84200744014601d07084440d0320b05c50300c4001010000c0014070b20032070300540100400b200714071886451641e50720303180c1300f050b603035000c810010303691349502c0400c0f148840700200d65941802101c1c1c0760081140310301c0a041210140804c00d1744804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 384495017 1250 384493767 384493799
    0x160801090c0e0405010f0f140a030209040609050d091d04050703020f0d06020f07030e0f090c031f03050105040b010e0f0601080a0b03010203070309110a06090e060f090405010b030c0a 80
    0x303260100d0403030441c03801660303224180d02640f58058108000455994440c1141034110b07426040059000d41e55100300c0d84881c00900207403034008510380800e0000d41080c418054210b13129040005200308141c0b03d6508001000e40c0000008804440400c1540110307a8080030f00411b4410800d02420135640740c07680c0d4161071100a000b0007584800401030750301c12181c890069008042550340301c03200000342c1130603071010700101d0216004c000390821078201810000600600908000000d4403100c01d031085039000103014828071003c00000c1c40144a401403820011441a40041440c0c00d003894400c19060b0144c0061010940303030350030440c1c3c0d00c01101c1181c0e04081c003801d204000351924101c040280c5a506580ba0301503000000303000ca000c0e0f1641c0b101003c07e01408415000340b03116810800000e42c0d510450001810350101845160526000560800700081103542e001030b454001ca4001401111305035116590f070702c101000343c1000d001c10055200c08a55511441c2d0810102070321500f24 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 384496267 1250 384495017 384495029
    0x10519050f010c080a1e030509030d0506040605040212012103050f16140d030f06060c2010050c010614011209031403011e0801020f07120203090a0914160801 69
    0x1400200c95110b0740100242858283c02a2403035644007503850700502058255080300d0f148130f441201e0090698400d02c1524095640c0700c1c0a1032502001803091005884003801440d40103580d04070000d103035515840108960303402041108120741c500100b4520342c00302000f0b03210303001c0701c82132002c40001ea004044901c656a030407022a16170005071130103259074200348401024100d007c0030b8046244400500607010392180da40c00d00492071305030b060030140c42c102d04c508004141034184800010302039007821461040012941030f00c44440c5030015180350030740046240400c00c00140d0401980082c010350000d01395a5000b04121082180001c0caa0303102003441200c0150b5030b030805010544039003011681d01c0c2d10014025125610754080210300c09000c101090140607070240001c2120040c02030780c00907540f181d00f00c0e00b8509540c03500300302d00440781d00030011400104400b0100c2e94079003500d1005082146170001d10b80d00e0310100d07000280000b0f49110443e511070152100070075840050f80741541c0d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 384497517 1250 384496267 384496279
    0x1e1106280218062d0306030607020a05120a050c010f0b011d060f070f1403031f1505030405030c060c0d0b0108040c1701290301110a08010b0f0403050a0f050601051905 73
    0x1107200480119050b940100c004040c484d40044101540300080c3d400389000724182d07441503c07903010aa81d207000e1090000e1564115080e619921080080980f0844c080341c00c040f40340110020340c00d400c51312505107400c2c289030f603189101c0e005d5a1050403881e170416039a00200310040d0100008603240680c96a49038013250005540307003000f41084078400300c11342c40b01340c50000f0386400389200e40700e80048071071740840d034015403c0b420740403000d11200701250030728242102120100e07001200e81e03600c020400e4501e444104081500c040f0200103032131140101c108820707120b14003040a0001d0b690503000e481d04002d4000705010201d15a624210200c401e04001c01e0000b1500700080c501400c2070360140316140e4100800d0303040b201c42d40f08141090308021070003080f20203102e01b008501c41c052000c1c1c000c0000c0602c8014000f940f1100001d14490f01040345407420b0075569560185000510b54040300c1102808108808001c0d00700840f034007400701107032440368240c0c840180fa25419803510a0301d00c142 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 384498767 1250 384497517 384497527
    0x503120604090803040c03060e0102090a030f050304050a0f0303140c06130203071d060306091c08040f08071a010602060108250f170d030b011e110628021806 69
    0x240d600e60048040d9030f401154039840e881d180c00c1412008845100650303a4505029001100e0b0506200304c0d102c4070002082c0010240c1541c0712109940180401112a840100808034465840c1c1038100010b0030381c501010426403e42c5002002c0e03100786510b1203007124080c000e48100440214402d54413207000182c40c000b00701c01e03000003481d015140c0e1141d41104400801c1c2105c4036103400c8040c3c07155000b6400c407100d41d1540708005070381e03507000040256440c480d110320140261007020940d80081c01140f50701006416600c074000c0350343c0688000c6400101d0040350b003040082c0300950328010442400606082d61404c0e0f121501c44410740f4800300c4000d01c030041149441c41d500d4540c1c01030003000600485650711031003083d51601901c041401d4503c151010f03409400e21034022071440680680da05030011210b0f0b69415075519884100405024901d030b040070285100304400c80c859440000c0d00c3d0040e8074410310000740b160413078846290785401002252403090b1041011642da00342076a01035664 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 384500017 1250 384498767 384498769
    0x1009110720100f0311030a0213050a030206070803130605010605072609191a22061b0609020d12090605031b36011205100612020f0c0f120705031206 65
    0x74069401101c1d0f10701401b0040c40403050840d400303401055a9401c1088036180c850b000c103c09005e0f580f1000b0343c0044c08000c0900090109800395420001142031070700b08405035a19103041ea6026000b00e03001510225141c1e00740500190700c06c0940050300344102203141c080001348881d10444a440e40110700341d240c001c0300b0400701d031110401400160800c40426035500351011850307214034819600c0480408076034410120740000001292115114160a007400c00601e003659405000c0584015070f4500c0e0050160b210300002c0b81a280c8990b021008105080c0c0c4043c1003070056800c201708011050003003040c0303c031004410100c50607c002286454400e0814101d80b020a000250300304000c20849001d254040004001c10510003600c45542c40012001444120b86048907014250343c81d961080007094003441c3e400810906c0402c0251600300b40d410541c2c05540060800c0349254000721001100500501022079038010700450b5030b01d010202c1d2030315a0346c1e00030140310502042d0000041201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 384501267 1250 384500017 384500021
    0x1031505090f010f170c010c080f0a0e03010e0304060e06030a0e070e010819030e04051b1305280e130b040305120603071505031009110720100f03 64
    0x8080080801e449450482c4002c00c0114007881002514651084082407460000440103088414103004050006c100001150300740d82501096800903000c001035455803071010300518040c096911003650103a4450107160071200a8403103121640c0040c0000d0011551240c500844142c040b6000c0b5100d03102c9195400052144010300c0c0304a200b41180045c0c1c0c4015402d0540c100c50028050340c02230100b40105406104103800024000781d401c0392440790b030340b8041d44041d1300700520383d015580060300c0010f803400541c0318001c4003c1e622012002041903103040700c08109014600c411420070b9806808003243c103114540610102d0600420003d202c040280001c001c001e03412201e44000c4c1d0a0a00780a081d540c002950b03920071541200000b022410001115400c48100244140c41c0000940e001c660580001e4200f860869107064000783c00c0c0c10a00070862040113690700c40342d0b212224607201e070a0f28143c6260941d0461220084040390ba10007084c4a5a48a28100395420030540501140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 384502517 1250 384501267 384501269
    0x131206060b1b010f1406010c150e0309040b040b060f0c0a170a0e01020c0306150409060c020106060f09230409020406091a04020c07151707080f011211010315 69
    0x494100003180b01e09000c034807902c0504000001c40000c0040440300b0000009a400d1410040e07900070090010076915440b40c403000d10824010703108072805010660307540050340c007081006003441c0c1c004981c2019914040c840c4071501c0000321010130101e50f881c40416624000d0419039103d03030300c01241c5c00702c1000b014440f181105070b000095038041c03502003c020b091a0003604132000010b0050034002d11075400060001096080200200543d076610300000500414801720103030455102c520400001d02c43c1c2c000c150f20806282c0001c00c0e0682000c100031301c104401200d0f02c08010040381c0412051b00780d425500100d0b402c3c81400b802c1207c440000c100640f20002d002500305103800e00003c0c04200d180c4c0314889054030344c5201c41100b0740c0801048182d000c4c034452506590400d6404100c00f00d0550382e0600d9001c00340c241200c06140310a205040203030b04030b410314003162040302000181c4040401d424054580305440c488410315079240c500154450000c0e09040c103503213942074009021203980e0b81d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 384503767 1250 384502517 384502529
    0x40207020d0c06230909150406080f03031509160e0109120c030507060e01200a0c030302010f110a020c010c11030a03050d0b1212070606090501090b0a0b13120606 71
    0x8201c00390f43d8200184000003503807407031100001d1807088002c44030150048411000b001001c6c0c0c1e0070b40e10307601149181e1804c0c00d41450360280d611007000401000c24800c50110821000c0507545a103440c805c9114011400d1103218841c844c0107081215418424250706658011490044164044040140e40070040c9401c50401c0c40200802c0f90304001c1d50220b54810359210b04180e983c1c250703454405a403452650203085010400707418603a002e40c130704c01d1075a84809404004a400290040d1504410b190303090f0016401070351100c200c40108005801480c421680000005251407080c0d00029150700280c1452810040203d42c2602489490b10319010040c0008080d103480c50305074540580300b50b00114194604a00340303511340100345410003011102d107580308054540102c02800141c1035501c11403086070940e94420011401c1001803040034082d04100400043c905000c03004c00c00324103801d500083c404042044a941e0b440d01c24100c100c215880c0d60301005c1030900c2854400c029040d650001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 384505017 1250 384503767 384503783
    0x2060a11040f080d03060902030c1b2d06090307150507020c1f03050c07050a0201050d0207060216050c030d1d0a03170a1101020c070512150709060f1b02040207020d 72
    0x440d070a02c3c0801c50745403004154900300f11044d510406007003640002c0b0740300c04810905106000303401c40640c1c00f020b10a1030190a2b52030181d003007041411543c0c1070814008001c0601640740c2c002e40c004100d150b42042001008505213082070f41c13801208d10ad641204074295480300041185103000700211000300301d00400d6407800008a040301041100001c0d0312100080c1400c010504c0b0f007601404440003070350010090250440c0d560010340b8994032542010041035070800030320303001c6407143c800f030008041d240c0c00c00c8254220500303015141a200100441c401e8212103d10940160442c83c0c9900014007419004584d002903400114221420760010744001c22007086020005802d00007800307604181d031a03051902c44071425003400c034040c6014440240c1d211040601c6a460700c65199124441e44108a0750341441d4100340102c50a420f481038004100a04000c1c444140c21030a0310a012441e490130321807550300395109240744072003043c2c084c0c040c0d40e0008441c0107540326520722410842e00700f490303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 384506267 1250 384505017 384505019
    0xc0d090b0123091b03040f060e07180b0d0b0915010305010f05311106120712141603060803120702011d0604110301021e0d0609060602060a11040f 64
    0x1242c2200381c0500014040804402c0d5410580c540508030314001c3c0701c80b03480719120301c030a07000440f41a03001400c10303141c901000d080e17080051054019120540340040140c84480e103802680c501c42c01c480c080850303407641000c05002450b1074001c03080c540036400c8400c041c102d84074140c060f418200c00e80034500c040b031156400482803080540108079001c252190411080c0c0e1804803524a5440400500c02c100003040d05001e18071010f200c4440f25a4040c6010011040401000030380c56844407001c004408100000c01040750341051000440301d1000ba0b040c00340c0721004900404a0030020030b09000304140006503400240f2075400200540b580204a84c1da5901030785400c0725900e02100d4880c015800c1062400090561001d20301e1080c0c010300c003d00d110780311680c81c10020345080001942643d428404d00c2050001000c1c511440c00810307201039510800c504080041d901950401e00b070203800c0a50412440303500040300c6501400c0c1b0800000c003049000c440031014440c0c1d6000031148410410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 384507517 1250 384506267 384506279
    0x10f0e241201050108060601080403140903010b04020d0f0609060815090313030b01081903140a0e15090f0405061c151506020f12030118110d0e07060201060b030c0d090b01 75
    0x4015410781704000103c5042da501c0000445461800b00c4004000403008041c2c400b001e01c0300c0e0003801060000a0000c6004640e00c4080341c01c07a0000421001500d403200ba00c070f0030b856010321400001d00201d030800e1028506100b0101e035504880d4040d20090442c060000d040000148182e5240005540860415070355908024a00c17074028001e5561500901401d42404c0c801d000a2009140c0d164513401d041900d299662406604406100c00a001d410b8200c441c2d1551034000032045554228000ca84902420f414880b000a071325400700d006e14544801d1082c01d80c0e41a58400351000c1010350649050807900d000c00c1c010911003040100b15042601c80003000b001515444261074442c1d08030b40e403205400303105a0781d518803401510f42403070042006100901111942c40030a101e0b4400218040482502811a5901c25103d441e01c3c2c6640703d001da00180000d0150100411142c8001d001180c100240b44e01180f00c048c1520010b840300050040c1250555004080c1c501c0d00040c88145541e0344d04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 384508767 1250 384507517 384507521
    0x420070206091e030625030b1c0302010c1b20060f131a0a0c02090a0608060c04081c02060601120f020a030902190b09040c140403050f06010f0e241201 66
    0x4003058400e001d400d000926050300c2c2e50106c40c60b415030440c10340c0c1203001c055080d0000e050b80102c050304840c04500f0007801e01500d051241a00d44603500001d01d0458a550003801120307910864440f0304445072606001c910000b481e80b00403d5203080c0c1814001020000400034892040641030504003c125005952141c40c552011641c0d80450010240c6156a4403060340c4140550342c4080f0700c0604081c000340c00c00304030700e80c0d12441d6401c0004207551580700306031414a08030340c40c0e8200180014140184e20050003041c0d02034440c0d035800e500c0f090460102940b1a44002c04203810001d080302100118011a0080c42e035022003640d0031540e5589612004014284144040c0e02814003928848005031072207400d00111010072118508009810042101805203ca0080c1c10445640200c40c188001c09000340700562040780107110520b040e601850400805038480108080864000c025030010114010745c4522050741084024003050500f4000044030030144e034010005403800b60f0240015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 384510017 1250 384508767 384508819
    0xc030601020f07150f030504051f020d0f090507062109050a0b010803120c0306010e041d071203080a20070f0b010603090b060d0f0b0a091a0f06042007020609 69
    0x540d1484240080b085c030507000e488083d0740003005075003c0070740c2900c483d10750440c0720707082c50310100c000d4030340030301d20300300343d003512080c0c0c0d49600030a684402030410004104a01d9000381022b00f0078802e640141c141001e10010380c0413940c81490b40711038800e010860240100064554801c02103811035840b07400303180c0da03900280580c1c107600b4008400300da03440201d02c0c1520312464059450070010b01c5101c0c18080034010055807250342802006407a04200e0042c000c12002c1d01501c0481ea56030a90303810020450701000c0c0c810521140b825510058a1508807211408909280303040b0b550340c1c115240041450702080000342440c0c00a00002c1056a41504050303d03e0f17015900304040e03030f100c0008001170401301d110010070880c00c0d002c004c000203c00d9035020341d00c0308140c80001207606042e03c446c400c0d11511804041410401000c00c240080100400e0341c00c51402c4e1410001c0c411903000300381443c91001d5010031050340103d080c0c7c017191340300300c12503500082c041c010001b1080860100c6d10401c1c11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 384511267 1250 384510017 384510059
    0x30307080309160308040b07020a0305070825030209010501211407090801020c0c0114040806041a0112051e0c060705010218060a08011206060e041109010614030c030601020f07 77
    0x505800483d100560034150070540780c0013400b4914242c500300ca14403050748100340803a005402a4400001301d602840500001c059030009002202000700880c03c0881003860741c10441f004001e421700268480d0300c48141510020f00300101c0505a980c5040c4141c00d520034080a2141000c0c2c400c9410b0b5280c10055000c2d41441c2c03580c00da401d41354000d02d401d0307002d00c1c1140c40e4540e01000d8840120341c0b00318080b40030060080c00070703031501e9141d07412541812011601600e074001d00c0440e0340d002500d1060340c5401809200d00c802c0444501d0741e03800b900d0780140c0b13840c030b09292034010520710030120512a400080c41e004041d1070f60380c0f41c47d14100b0b020750003082400003461700d11403400d0b14034100402154080040d80d40c80800c1a800d00c041c100909030150300c103540013503584401240030b0304045140c0d400741e400b554005801d500e00d10200010f000c8140c01040401012090659000c41c410081e04d8020480d29480f948907910040100e1420702001c54464030785c07003078190001709182d0f43c440605440d91 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 384512517 1250 384511267 384511273
    0x50a02030d030204030b0f070c0c0b0403110a050105160302011d10060b09030a061802040c05030405011a01020a0b0a0e12040e010b0304020a0306020703021213090501091401050d0c05030307080309 86
    0x507860506400720f016501c00540342c0851400011600002459119808a51400e15003031100c02500c40c0500e503001c075000020722802c002014018054501e14460b21003030308130b80c905038550500000800302d000c0c0c0c036000c2603c44000d480000405000f9080364000c0c10b4103e4030a0f254072035890026a94a220b01c018201c00c07071a203080442c08a915504480301c44001400801102030a17135180c80c01031035028901d0b05d0107400204042d0050b03503140542410684541d4400341c0340e00305410245d01310303681e0805150704840165131100003030f40c010030803140064000e0300c54082039032414101d102070940004c1c45150390280000a02c022200003018005444034004142c400b61703241c02444c0d260f84420749019500c4032040000708000307005a001846084d01c2881583e8a203c11017415514540050707d40704140c10080e40140b00d002600d2040500401c480c210a000c0410303c075105040814060046c1405840958648018031a50071300a80c010200a41180c1e9140700d0740c20f2041058006980c0c028640c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 384513767 1250 384512517 384512533
    0x61203032a04030f1410050708040312051b070c0e04080705070603110904020304141615080c03060f0307030f06090b0708160e0a0f08030408151005100c0807050a0203 73
    0x181c00c100580d81a260321001ca07101c95482600c455008060040c0003461034410044c00d0158401365000e03444c0030300e04a84428485050500d0090b04120001603910700b0b0501e054100310980f900031201000104003098101e40c0d45001e0f04000c64945507a4010500311040312080c881001703a2200284030040c010426501c815031904400c40c10b682c06242d004001a20a2003e0380c0d491805078010340e00f00d407055000045d03510005a0701c0f41400a40300e10610a604407c60800c91017052444100c180c0700107141000c46490315500d0380c01c0900000d80b6180c0107010150a11025480070080d140165420490b2071920100c280f5000e07001c0c00e5840c00455500f84841d000c2418940154103060040c0c1180c0032110101c60000b0040f9180c0420300c40700c50740700b03132803680014050b1f00d914880e07009400d40c400659035490030a0881881c00341407031014994140304900300103040d440440c050007520380440700184c1400004000711446205402c0203807140d000060310401300a400100d00000318400d4055075506 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 384515017 1250 384513767 384513841
    0xc04020c10060e01030308060f0609120604230a061503020d0c090f020a0206071119080408061510030506030106030614040c09112203050a1a0a180b06120303 69
    0x26a03c00e21005011440440202e8142c0c6401042404148406041a81021a0325002823081c51030012000000d401210600007804608031080750b400024198140c1115600300c801e55552184c0c44014040950307804d400d0038a41c0c2c3c40d1510340011a0002c0c450f10380120301f41802a5408814410021b801c0d10344588070000410310300a403200e4581035005802981e8407140152062051010001d2050190b102420190090400c1800555000c1c2c5a029156803e00d281c0302d1a01c400a0198980300c041c15601080d20f9403a44164022255549400f086907203440010070b0240065420003800c80382005148078070003250740745152141d401500a0200c0c250740788071a03c21290010107140c00400308114041290f1212101d640342501c41d00f907010b22165a0f91101420507034100011145420700203c45102c82d040210403a40100c2c10140400c190982182c202c96944190301c001050810070f00006001070ba10034840c0c03001400300c0b0f020b481d524501a0300003108200308043c0246504050100b664903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 384516267 1250 384515017 384515039
    0x11104060215040b010302041505040c0e030f070b1603090806280501060503130507080d0206011502030f07060b0303071703010f060801030c030609141510051f050c0c04020c1006 78
    0x1150444940c6884c0c1e400c54003440043c1ca200c0e0f5184082c5407040000007899240c510902c0814855690740320113009114080504221420424042d0b0358094542441649600742c11614000b000b0100607603540414a400e4600b0350484d44000d40b031303020381020014100f1544802288a480115410340400c170350b41d070203401315142806011b000a20600c0065500d05406050341e45442c000c000700c5a4483d500c104251908110403410001a04940010880c1d605000c1000c143c8503c42d0010f50b0400d8810000c500722402850006840561504210304003614240202d40c0085e80000c00e2017151008d01030000401e078000c1c0700312140301c81c0e44080094080e10403400c0505a070b40c0041c5101c200c0b4a03584602c0c0c05401c0c103107405e566048400d070103d0441001001401c000540b513103003000c0c061416800c81200100c01d80c4c42140a06980508400c006208500007020900141001c9172202c280d48074180c40c000403811440d0300039200140b01404408000307220020803a140600340f1005440b0310b0034001e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 384517517 1250 384516267 384516271
    0x10051f06030513030f210b0a17120306040e0f0d08010f080c130b0a1415180114040902071505090309010f051e0412060c0203160807080c011104060215 66
    0x6180d038004894400003034170a007494100361a651078911032020881d40400c2c09224120706014045a0ba2aa42003007402c000010b8801090b800181190326900c1c0c040c040d0300c601c003011074007009090000018282e682e8541c016103407103190b4000c0f40c40200304c0550640da11f10f03039410031002180e500c400005040c80b0140a8006440742c5801038024600c4010502c01c442a1400711242d03116200d0210190b6511140720440c001c0c944020241204008042445590408002c407011000710820890803048486541d5604d907010030303e40f5002c0082c0a55240c0904d005542101c001103000150040910105c42080703409484003150403c002d49031580b0071a52031240801c014040740d40841554403060190307029183e0054648001c81d0303c1403020000000a5100390020b036100e0303425403802d8040c000148a50701d64480303680001c41c07030303d1000080d49007440348026000b00f090900194081c04c1043e18026a41c032001101d000b440710440d40c42e50020140c109015200c0140724080018030081700b04540e0364 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 384518767 1250 384517517 384517531
    0x1b190b0f060f130207080c12040914010b040510020a051207020103051326070c0303052104080405150904050411090a02120a02090d050a061a0405040803130510051f060305 75
    0xb203e038811840100c00a50000501910031401c01d0081e400c0662040c003181403009212a40c20f80e41c3c40c2000d4440c01128030002101180c401400010701c1100c81501c04c99040d030388125007060681c0d040800403880c208500d00000c089004035140010800241c1c0d02410440d8801d880500190391a07115941c41c1d644071520290002040010031114481e014810051400c00b010b8071624051042d110003607900b15641c0110000b94001403152040c4040800e207d0303441e0998914241c450410341c840c68000d0159004a910030b000c042c4248036541400000c4a0303110501410078805ea241504002101c2e0310303121505070107100038100003004a05103200700d03114102e0480c60111213880b06d9903510000e401c40400c1c00c0d0004200020b10700418410018010220710074000030130f68184c2c02000030703041010030884c42e02641c1400d0900000420040c240c951098007880ca4010b181c006007032643c070f0f003600b20000e44e028602e00400d201900500c0d0400490203072000742c014078602d54414044044400c110751007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 384520017 1250 384518767 384518779
    0x30b060c011104091a1c0507150207030605010909020a06031104030f140d1b06051504020c010e0708070812300402030c0904051507120c080402040e010903051b190b0f060f 75
    0x211600706c502c1928172003031030700600c201c0700c44645546840c0f0000b41800c43c030b000944d0201c0c50030010400607000300c5001d802007a10512003205194041110742205004501c141611036059180c61001001aa0011074209150211071901030910300b1200041080c410340074000c05c10000d001c140601c411000030309284807420625040c5441d4500100400750026401403410f24895000b50780e940042d101401404000080c00c240304100a443c0c0482a480861540c02500007040101804616149442c9403680095a075000c40580b118500324000114024040c0c159440c3ca00501d01d812002d00c030364804d404442071040e0103c00c2281e883e40032100141940d009962018031050300c05c031200c2e005501d03030510085841f10201c0c200140d4560310801000030f4a03600400c0309500d8980140b00c6403207403410081140285030b840c0201a0702c100c403102c3d0310031080d03040002003c0104024105000c40516400c1406441501c0c205411203010380e054918003d00d400405d9991404130f2802141031001021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 384521267 1250 384520017 384520039
    0x70305070c06022d030403080309030c010b0f21010213060203040812030c040312110d020f1c1e09050d0308060117010e1b0d050915010f0b0703030b060c011104091a 72
    0xa072511041c1113101807001d0380030030f1000100086559000d5405000b0050140d601c0d030343d00100c400d0848814001c1e6911a4070055100c4035141c8806004550780100400880b07180000301d00c49901a116020002400321b0313271517200081d2964084064810342d5800025111035182c9000000d110380000c0c1d5407103181c80340c100010000207040002a00301d412060030030b4000010007030312041c189020500b591000d03030400c4207a40b207050300c244410002420901031021b03803c0c680b004000d04581d1482c2180c4803030640241c0e96008580038088440081c40002c00380c0c000c5509501d001092041c050700c10502080030344881010000040ca0a24180c8191590171601c40d902c7d0400054541d64804080501203020407840c001800740e030027050b2180341200002c0c0340d1001020489141200147d0246c2100711120005101c100c064400700e541c099050300c0c000c901d01c11340c2030001c0c40c0c2c0e100303016003103642c2d6103040b41108001c02e80c1030117031084a900309802c100c8006452083d0151805010003143c0c028410a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 384522517 1250 384521267 384521323
    0x70320071203020114010305010c27140102031306050a030b0402070209041101090b04030c050f0105130e10090e010b210a0b31111f030c14070305070c0602 68
    0x81c000105078000d2002241c1c00398414290b8820b1030702030b001034590f03035100c00403951083d810031800d9100c401c045108440c0100b400e180d134050a906030041088000b0824400d03a0580e01c2003003590085018001d0304404203a85290207002640601800004641800c010180b01d20b072a20960b9011500540320881550f15982c0d80c0b11450229140d0505100009402040c00d000d000e01410146120b401084510341c1040e0810448414901e00c09042000c01c200e080710300000300c028a401c48800311140101d81c1c54288003010303450300d0358018140180c9058018100c1260540192000c850165074015a078400034118944100d04c41c21991034680c400b4642e040083c0608000643c8111401481440034140c2c440c48425811400702c0e60282c22074844100f03040c000403000001c050481110f030013a54a06d141d402c15102411110400c00741990780300c0500005000701c1c4d54940107494500c015680368150715015203241c01800095800b000003c1d80850118000108110020105015840c050b43c0f100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 384523767 1250 384522517 384522539
    0x909040605181b0901140307151412150406081f0e0a0c06080a02091f0c0b0c04030b010e13290a0f05060906010807030f06120807032007 60
    0x6802021a42a10003110300b40807000e03c25a24841c0c905078920b00d41200d540e00304002e100c41a0044013880c6201081040c003a580000c4840490356484c480c0e91507a1440b0105845010a000b06500c0512001030b5801c41003181300c2c030252144491ba12690080002d0704d040c4001c50b03070a0b020781c861a40c0402c0b04034200d86294000b1007801e240d003c0021509984002540d4108419018211502d4824190620010750802c12096201c80700321011410031f00403074001115000c00040010340c000c401e001d03074a0701501c9607001c1d00c91103821100914840c1030000c0360050070351140c0b101b50f40e80000c8200102d81210902c2c05503001d0078602460240ca10f59948452203400c2248406001c1000d001d501106c2c2e64004e07018a5128421080340003071052412031a400507900010320a5119840d0102009101d03070b004508179030080c00910b40010014183c1c00e10b5401030242d500200c1c1100c2403400000100900c3c0401401c05038425540c1c01c190b40c0c8001408008090940940c11260b00002410b0156034680 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 384525017 1250 384523767 384523771
    0x17120a230a080115020d021506040b09040b1f1409060d300c1709030c1c05010c0807081b09090a06050102160e0f0a0b330909040605 58
    0x289544003140c206841900559400380400d04041040e00c0010000b03613074403161090341c08846001401c01804007000080d1210300b404541c44210480c0c00102d00e154030b5543c0b06010100001d800c202042c141424140003500086940136000405250301040064424000c10211144804207146c0b11a030a0100402100010000d0380c00c8103841600f8400710706004403a100f41c10040c0141490750002040244481c0c208014200c00e0081c03d00900000449906480e64588920304800381ca481501000030b00300003000d40d00c5036006c000d1044140201c2402e501030020395204d04020801e1500f4800309a0303403510111400c0c00031903401c100150090b404d04c040c0e0040000c00b440f07000d150814140005900c40000e40d101c0c80f484e07603101400d00c036558041059001c7c8031a0000d003035800b50700c1e0400503000814000c1c955a04c0c40744520100e03000c4071240d003101282050047c503a0781e4000c0c000310354500d01d42c09800c1c074001c8040d505051030903030b8154004440b49103c1c0540245025503860703e81034090440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 384526267 1250 384525017 384525047
    0x30908041503021c090b010605190f1103040902130f050a0315140c0705071e140d02041e0606030615030504030207050a1230081902040f17120a 63
    0x3004a180c1e00c00040e0004e104c0300da040c1000090741d21150500300c403c1c0e02e058001c2ca0a011003042101c18904050440142e40100d51800c1208182d0920b012140a482c15099000c00c0c0320108012940e80c61a801500440e04044032048000d540c1d424070b080f8562840c4075264000c69250b0051010601e0181c4580c00305002281c046045c42442106070f404940403a503c0048441c0072030000c0030000240300341ba0003048403209035031510419102e01e498407050f0348580d140c0d540301001549055280d050968800e5034004200704a4210102900407850645950b5035100780d103064008104540642314041c1038401010140040340c043d41810360080c01c003e48194154490f417403000413155181c00080c4090624a103a18000c40158505280c80d03031040d400402d882c62a02c2000450703422105013600c404041072501381c140c0e44400b0002c94110100c191440040c500002d004181c4842088403407049070103030445412a507c032450059210032a0141f600e00e650001c003c0444100d01ca0181000c034804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 384527517 1250 384526267 384526271
    0x8010e07051f051905031509072f030d1508010501030302210702121b030c030c010f1209032105041a0c040905130b010e0903041e030f060e060106030908041503 70
    0x11400311354640039195100300046001080100d40541d0340799120003e60b0660340b101a81c20070180240c80a24100001c07002e1208409030f207210707240c0110b140300384041108182d0750380301c00f102510340103031000b50008160510411400603003d0414407445048a405501500c500042e148038031020002c2c0e020780000c00d000074800d070005a5501c40400c1c0150304118018080d492040183c1c1505410702c1168600c070741c10000603000141c07000304001e0070104007481c1c40941c114042605451850002040c5d056481c41c2c44498020141c015076a50710342c40301509628500703660f100d1504265201240d0041803038108181090f500d101d02c2100d180c10006d840744550a040e19070030080c1c1180d508446000c0d00c0c1b0303016504501071001c502c400324003412100c91000540e14000d0401613030380c40755110b032010300c0f841e407441000da00d0020144500030307590084c0075040854007403c200021300300c5d0b64040041c80c0200303000040c2d094001e100c0c0c1100c0035405100d41b0704040c43e114520710380034110b844041c1456 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 384528767 1250 384527517 384527527
    0x7020a05090a1e0603170306010215040b0402090a0b061b071a030f0105010806010c0f0201020a12030e0d03020901210b12060a0f02090a030209070c060e0708010e07051f05 75
    0x55a480c0c4214400c4070740c4000040c9032003c80c0301c42e0094204014820044601d0180188003090800b007600241d0141000e5030f903943e469040040745041c42458040015810160a1104110350304441034021030003156503244a0b10b90701c0d2200c1c111045c0a000c598089030400c5698150f4050000d21080c0d9484241520140c4e83d80d0354221581f42e4084c8494540c1002c00010031020302c0113141c0351805000c003131810b811545000c10000c1c0504440240242290400310f10035030440e03200300101101c50340c1c840c40c070f421850a00540134000e00b80341d07064018030740540540c0644481c420320a40b031a640050b564414841035000204410701d44c0000340001c441c0d02c074410401d50b07031140d50303030b0040d4260401e004081501c1e000424a0446120740c25800460b8010442060311303580320040c2c042580e404456082050716008070a8a5003201454010724150426642400c0c0600100c1c081040300d030b1b000004e00c0703110517800c0340c0741c0c4a89080c000c1c90f500c2003c4407030b0f401c2132005003d980b000d1f202660800030320705 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 384530017 1250 384528767 384528769
    0x120112020a1e050a120b040803040c0909240908040504110f072108060d0605070507051507020c030303060a03171b060105010f11120a0c1509140a03020303010b07020a05 74
    0x8401e220180a2498500c0342c0030042400c24100300030050400701110b600002440d541c448080d9809003024002803030100c042030a00100f241c0040060000e907400700042d29003494844c40b6076001d15424104810000c032001c210018500821401581c0820441e1605080c8000c1000030003404031000c5164500740308810101d80184002c104807802510400601c030aa0221260714502c001d030079801308015035080c40780701d0f100c0344000601260700c4000465165600304040703c4d24040c040001d400c0e403140300320303000341c400b224103403a401a0b086909071444401c510042c9540c912043c0c8010b9081450381a04001040d01c1071450201c03040c1d80d1400503e880300c00b0030880441400300c00c2404054100e040100071540c0c21810803040c1c80b5007400e0080c0e4444025001d81d89400210008010009002501400c4136102e00041c00d0030560003203110900202c40c9001400030000d546003101c8841080901c21400320f400181c080d40715500d0344c001c0d40b03075030300341841c00c001d0b50050f12080382c01c624407940c00300b01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 384531267 1250 384530017 384530039
    0x10203280207200a080304061e1214011e0605070807050c06041d0a05090d12110c060906010608220312020d0e060a1e0506181e060105120112020a 64
    0x40003d1541d01a54065054100030304403040b07900ca1a030a0b07004101c20808250403110303460310205011001c00090b00844401c3d41c02c06621042000a07620340107012641d01800010300741654051907081852017190304462401c11403a010f410045072080c44182c0003e01c0003c010080b00e442102503416440e2440c01040c01038019410410a0120380c52a600c0c40001020000d640541098028020350034118042134503088450300c480700308814400b02c00124906600402d5010030000725050755410f07041c400a48905e025214503501c0e0148400005000d0b100d1500740740141081401110f01240206114209070300c3e44030101c0501c00c40140c01c0c0240304171031018040b80d00c4560804181741804601403410320394001c04001c502c070316001d1500c101e04180400c00d13000c10515a0005007a03150074001400c107180c0214190400c0b072003071040044140c0349644c06110518080c12500040d15004010b403014020a0b0a1008485282004202c01412403081d1928540042d090108640d103d200c5541 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 384532374 1107 384531267 384531293
    0x10303050d110a0203040e130314030a0f090c0302011107060f030b0301180503040513021615020c060405070503070b0c15090f0d08070908010203280207 67
    0x1800c0062030303800b444852500a0015440b0409641c001350380768064020450f09a4520340401d0000e5038200c15201600d60548850b02c200e012002043c0e55500010400d03131740d0325220491240d44c04418400d402c441c901420768000158254000034180796110030144481340d010040422105c0e030b018000c0605803403607240c04a4004507600000740580001c001450381c03542030004400400000100a0040b00c000340d412003020851112850f0882c080d9901e03540c04d074003508052000042034450040341048071081d0050905c100c541416141c030347c017241c0c111800da1169105218914042280034014200c0c007140e9440c00d1040c0e105241c90300044a1b040304100120404210080c2043c8050418441200d0880309a103114900040444070706403446030214641d8080440c0328030041c02180e1042500c101d080e1011400401142c04d540008070801a1455080c04054001510071304440 = true := by decide +kernel

theorem cover : BRFrame.Cov 384352517 384532374 := by
  have h0 := BRFrame.cov_init 384352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 384352517 ≤ n) (h2 : n < 384532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
