-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4358
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:21:39.047971+00:00
-- url     : https://prove2.me/submissions/a8b969e0-b3c6-4a9c-9e55-7ea629e29baa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 783633093 ≤ n < 783812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 783634343 1250 783633093 783633107
    0x1206070903051606020a020d03050c1603020f0a0e06042f09120c0a09110d060306020901081006051209030c0f0307121425080408100501140630010303 66
    0x2402501520b00f501d01a100004a5181d01c1c02000d0150744804d0303000f0010f0030901c48070380c1701602916165040001c451303c05418014aa600c20031882d1188000707109620303008801e481c498008642c41c2200c9450040404c40c1c0840040c8468803e039502c24941031785582c420506080c10458500c88061484107052243c059001200c0050107201b01185509405a00041700d00300c6100042c1101c0c1124030713060560f00540840c000c0c03030340a00d800380f01c0c0c400380c03510900030040030714859400541c862000074001031645000815501e9030207040407017008070a0708201180c02c0f000707411340d40114550324001070914500c03800750800348600c150108503485032004000b40202c5441400184641d64211004980781040d5100f03200c14684100300c0102c50a0078404116580c64465098200c01e507500c0d02d881025400075409010144c10109501050400600c40c05000d002d100f81807419105e100d40103d1a0750003901e981d15044000c1142c0000c0b84071200c40141c1710843c440240140c1c941c0c407450700501c0b40f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 783635593 1250 783634343 783634349
    0xf180a0803070f12020a14030901060f0f03060c021f09081c02041a03040203330403080901060806090703060b0604030f110103050a3b150906130b060f12060709 70
    0x1803180b04844d691074042d0088400285d52903541c0c072000138084009184030340c0054002c81d040d42d44e030b41001030a0b21000c10741800030508080d040c45114178604054050b00c1c001e0b20214110341141811502204023500c034003041d8210120009460081440c0241c1907129503e41c20f44101300403102e11a00d880d042d0014016108440c0100603491484c0300c0083d03040c0800d6400030340c90b800c81c01f00360203150301c0f061280301e80c004002c10585080f58145922840a80281c40c190f001032908420015010001d009200081c43c07020020451498281e10a544072409400b0040c401522852400c0007a03031614113490181d03030044a410b5031000145080390940c5c03070180b201030209082c01d0026076400c0140c4580c00400e034100c0c40400c9000100c10070710400c0c111102c03806911034040012000c8112007045110780f040710741070220180b41840c0d0281441c14000404030880030f0310440403c3c0c00580349039281c9070082c030107441701d0040d40c0c5030a0000d00300d0b00b892483c5d040c0304d00c036800800145035071110950b411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 783636843 1250 783635593 783635597
    0x10308030c1b0d0e010c03270e0906151005030f09330109062d09320709030b06030c120105041a060f060d0b030d0c050c090f180a0803070f 61
    0x400c400040d140a03c02a00c06000304464860140c1c8a03030300b131845007680c1000c0b8501048201d8a414280c2c009c28810345804c00d1a038440c0d001c01100b101d0780400e03280d03c0c85044901128002c9480f0000b060781c400144601403040c03503503000c100c032f8000802c4080415103980440115542c0d0900a414259013a800d4140c2000d9100000140524240c4182010780b642c025090b0070030b1101681400001c458000f015011189128001900302d0347c500c500b640110310003602c04444000300f410072000c03040a0a0440032001d26000340030308160440022411640d01c4041c02020f90b886c0e00003e4180a00082142d420803507070408580054410f600ca64850b41c450300001481401300e190b048050f1204440c00c0d5000f240e1616070303000501d0a080680044040e8580c0440c07a0084400400e040080b2500030701c1c0415994003080303041207000d0045001500013074841012901d0130241103c0d901e036010b00a0081070303600c0000409080024004000000e40010205a0724104002c00a10202c0e0107005000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 783638093 1250 783636843 783636857
    0x1b0507080a0308011d0106030209010207180f0e07061707020c1005071209030213020d15270203040206030103020d03021c021c030212040303021614010f05060d0209010308030c1b0d 79
    0x141e0594072010b05d8510305492420440540c0c00d14030154000e5212220190541c49421800604175000140d40c08240c070240102180c10400307124001e055400802402c00c998100f22410711449500030f04044001001009104003a10782c40010780c1000d000d0208190050305414140c50340c950018000c0608520032114041c4200749500211240132607400000d511100003600c021894280750090803400d4070f03403440082d545134107181b0390021184075407100c0428992201541c25081401038034880c40207061806528519090740003880c24801404024802d8030a440b00d1814540b0800520601d407501c015682c040384107031040655101c1c903106041200182964480c0310b264803134001d039103070041c18081c408140c2d01c41b0354080d07000e50090800300c0c0020b4602d9101c1d40103e00a0070100c007815401400004d0401c0c028030038407040d01c00c0100743c50700521441d403040005072100341340b00b41100e41010303035941c594441c01203040c0320b445800c000d50401007600030400b0003200003080c41c240c40100385d1118a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 783639343 1250 783638093 783638099
    0x408031917040c0b0c1006030c0602010510060c0f0c12110f0105072003030c031306030b09040209070e01030b06180a0914070c030309120c0311120a1b0507080a030801 73
    0x208001c800b110001d002500c881c1e02008a4400c100152050b03c2860301515004e411600d029021103116a20a503904014000c0c2005104e8081c4145500a05c40744a51580b10303040100240c40112082d1380200701c1c2c06020b0f851010702001241d001e005d4080c1010082242c4024206850540421410320348250714460b50f11801d0f6014004403600c5913444203203030620050340c840d421405068101c0068060008102c106000314040c0010192000390708400c110682c04d01e80d008088400030880350340500421004d0002603074a00b405640d00c000b107440e04030354410520300120040e0404e4490281c003c180030440c47d00c907030b240c403550101800080d580110b01c0740c0d81c3d014801c20ba95182d020419101d0407080454406442805603141c0c2501078100410408902e40d2030400701c0342030300e80c07400008122500040415902c040303003440745140c189c002e20540c000001c9440b014840c61083c1400c0c003087c1610381c5442031744115101191904241079803501c664842926071190707030031101100003a5581c030000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 783640593 1250 783639343 783639377
    0xa1701170d09080a1b050a03051e0304033809070e150108061e3705150d0e060f1608100608060102010e011d01060902031e0c04080319 59
    0x70b0800c0742c11450041c010043c19407140d000d81c48000c0540c1d44030b0b901a000108803619802541002148500000c200b07000c18244460320449103540e0314201c03078204100400104070308102e0141c17404d102140c040889843d0100203109680d18220088000c3c0c1a01d007041031045000c1085403c845018802e12165901c01d803a00c20031005007582c1d2070202d00504041480340c2025010320b0391040f11304c004081030001c040c0002e44921464003000c10708600d015a010442640f00010360681c03035541094030401418000040d6a44100d20b601300c0c080c0706c02003800c1200310340c80c0c1c11401c2c80403100800c1c1c41050030451a54851a202120301c48182e01480030316034025842075040c140325a220f090990700290800380103d80c103180240c0494119034a07003980c100c10007400c1c03285032005140321040000015400c0445401c0d114140c0c4000316a82c030600c20405507080704034100a00756041ca04035417203595082d030780038214003854100307498a00c40811200c2254034405441807081c4859212900c40307512407458 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 783641843 1250 783640593 783640607
    0xa05310e0c030a02071a04061a100f12020403020415060212031009050c09091e061813060e10050103060b040b0f0103050402011115190e0a03050a1701170d 68
    0x7006029080400002d001d500b0b207907001d0301c8500e1003407800004820000c40120302c000c40984003aa031040d5101100107110b108500006aa0941640e803c540805d445c032025040350183c0780310b4424070045110a80e11804181c1c100c4000d03641c024000c010020320700802042d51399283c000e00015200e4003041c005a2010542603c1c41484480d5200d40c0700f81c1443e000002510016024800344001800a2005984c4a001ca1031152b66000a180e5841c0154000d564031030b00007504050042c0580c91407a0b503403040e1445440c0d03110004001000000c04146041802000ea180303044489000b07020725004244550f0708134504980c00390703905016050b903110030042264185110242d1041d21404200180d50003a000907030312500506000d00f002905141b020f06002e5600600e290031441e03641040f80b5800d074040010003038880703071104019092082c000c0680d94010018040e0600201140c3e03003440ca403083c102c0908040c2d405502c0341455945071913640c0020f814008844980c042c60740c0b6003040a11482c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 783643093 1250 783641843 783641851
    0x80c0f0a0203120a030612060c0e1002102a09080106090c1b031205010b1209010209010c02280b1b010e0d030b0a09051e070c0213020a05310e 62
    0xf0346a50700e12030180507410703400325101d0300c03e1644445000a151005501c10300351a030007000d0100d050b515a0400422209201118611401e0584600100e59134001159000c890395140c00041806106c90002171801c148207480301d0060315104182e4060382d000360520103c0341c21a000b03008080e21111403000f40c402c41901000000d500600c8100004070941500001d28082e0800000d0082001c04c0130050f40c4c4240c10104981c400010034040c184d4440c0c4207941c4c0300301d070400218204802240001c103005002840a84200480e200541c100c9508040c195140070001f18440e500720754070b00400c101c6800168400344640100e541500a0f2101800b45846800c034076400b0306120701c6080425002410b1000009401814080c00420f91602c04d10405010701c8800008500c580e0b52888440d4075410f0003803490040240036010200182c0f50440341c80c0b9071415010b03004d078a032940140c0c2111203000e00408407580030044a82038181000c0b0950059408030002071710703418641c41c0d11190541400c103031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 783644343 1250 783643093 783643099
    0x4050901080a0f110105130305010519050c0a081902031e07020a03020c010f0201021c050103021f1e1b030e0306010f0b041707030803040b0f010905281107080c0f0a02 73
    0x1050500004c20714100c038a2030795014140309044c028500842c01000c0d01607082107805a41d10002d00100c80e8000e1000d10200030011000e02c0fa0789480000004035001d881d40120600c000c0f0008500414100029041e080000202c219260316001c0744420403d03540d80d200400700c60b10721001c103c04a101140b0040d007940c1507002014000120b00044410148500440045550902c54000d84014504990b60b80b00c40300c1c0d101003065411801004840360320001c6045908000745000103c3d2900072028603030b4098195500310306052000380503101c1d1004681d191203025000d00d601e0b0101900444a103054060507400c81e042a130729132001c1507a01d82c890061810000c8244403c020910b101040c1410100c004001d07203502d00d540c0d9407410300c10341050b501150196010020480c410081c40103190042c0b10540d000d10142c01c0078031005941c5080e40b070105038464070441c440e21110210b034114101c0c8500d0b500a0541c4e82d000b6041680b51504801e54241d9280191517001e0080039000980d034040d15002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 783645593 1250 783644343 783644363
    0x2030708180a0b0c09040609020c010e0106050108040605070c0b010801050406110a0c0f050304031b081009080d0b0f090112020f0904030206070809010b04060b0d05090a20010219060204050901080a 86
    0x1901d4040000343d00400250399240d042090894588542c0202401019411005a00c40c0c021040087c03d4541004e00311034a070f8903023442040f141c2e1748201901e8100f80c00c05c7c00011f540e1101e1108846090300c0040c09042804040b000040516055000510441c0143c0e02003044d0a10003004500c144100c0204000140c0009583d002250f99440d010103c03901c244112444c280e034940e9001240301c014110101035104205080200d54014403828140e032414080030446002d03940e4605a5a0048040001c0c606507a8040034400380c49044040c40805801465a4019a036900c04601109400c0000b24092003a901c800c07400d90400050131409158141c015100c1d5a8896100300c410800c0102040c1c1c041d034851420306e4443d15103105100103400301040742a5100d501e40c04000039602c010708080307100d600c900007420208800840070103060200500003003910744200c2c0100d1a10000804454a0841403034891041004039130080085550589110006030b81c0c440ca0181c9440410702c000d0859601 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 783646843 1250 783645593 783645613
    0x61b0206040b092e0908160b0f090909010f11030c03060603041b080c0901150c12020c030709201c2c1e0706120903020106050d060203070818 62
    0x10007001e418018009041550824141031300160302c0c641c500000c0309000389034540c0683d92540004071705c001d800e113035005100000303554504d40407400311031107107070f464075008601e91001408143c1210004040207051801034100030600278005c000c0d600500c140c41c0d1130b08003100e0219507408141c911444160700c0450841d44d610040c1b1100e03510051007102c2c0e4024410f804c0303216a0300c42142402414101e802010f07031a01c0c001c1441441c0a0681140003051000606030000300c1d4040400852070f075200c3d02034140ca020404059291001d0802c1e42c80d1b042c010b010b0f01080c0b421459100b00401111010316410292402c0d0010806104501c010018801c0d03034602c255218800d40c01074452010741005400c80e0360030070240c14848010103420b20107a074109408441c0c03100d175140030040040010304040d01d2034500c0c21002401700755150a00152268854030850117142c001e601850041030040d107003058413072041c0b034450000e51003216400c0200e40c00b0800705100030500650581090045801001a00720f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 783648093 1250 783646843 783646859
    0x3020a0510030e030a030903030b0901030506060f06040f060c21020a080c0c0409050a0605010510021e010e030307090f06020111031306060308180a0e060306190e07030c061b020604 79
    0x10041c070404103064841c1c2c00c103000e1a0f0104010264040d2560740058400d01c0c610f0001e0076101c5a0102c00d10841a80c40140b010503001300b0071540000080724801081035058021845a000c0c2e540200b198104020380000e41d103030030641c04016244078581e03000320340500f21701d5a41d5001345800315100503440458075030001740c1c80300b00600b1800312400444030f9640c810030001e81540d1004c0c40c120348541042c0e100000700040713402440d0140404540c0c56401b040b512000030741e03a14203046042040c08000c100e40d54611002e5010760800140c05003034a5480c40c0c5220050134011840c030404403003107021100044c140b1310610400b101c0740142c0c80710500e1a2108a5813000d080b00104d0242e62480d95045c0c00000a0402d0009184148203240700c81808542c40080140085503644843e10a980000030814203a80c082079407503000d015807282e0410740303081034004402400308080041403840b5111011082c0901002c03100111881d664801180c0301d1505c8110100e00e039003a80003900003005000038441c0c21 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 783649343 1250 783648093 783648109
    0x90b03011412010f021918032d0f03020c090c0c030412110a0e0a06080a0803070c0c0e190c030e2e0609020c07061b020114070501020307030b090a0603020a05 69
    0x100102c000443c001d1800c0c0800d40480e4041d0003034031000b401010704a04038031341100340c601180c3d500512141c00d0070f26645484055108008030000b0b510903866443c540a40301c0c40084d49851307001210003d1100702490b02a548040001c0c05c2840b6246c240001844d501c000000c8a0464404801960815107051540407001240c1101210300c404411003800c6203803540c080e144000c104502c0b102d1340c00d040c80307803d80f0100c807069040300d1055000005081c001c501c0301c000316070b0003c19915040a002e40c450400b1b50038100e10b90094042407041d0020700a0000a01c0300900311000203150810100005d8a01601103030004200c62400386c2022030302d5035490114440440000d240d1140758400350004c8840041152400e41041c05000e5000ca041c0c080c440040224030090801760030401c041110400c5406e80905a031180241004840f0309841e40240f458020b8070042a0302034000d645a0611140140c0602150207402e4003401e040000644c0002c018000c600450342c010f4160150300c2d00300400d201800b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 783650593 1250 783649343 783649369
    0x150c03050c0625020307050c0609120d0c03090f08060f07030b0d1b060309021f0e091603200d020313141b0103060b030711010b040608010606090b030114 67
    0x1009041c001900080018410680f2484030b08401d800ba119814107481010703501042c3c420110341c024402500014400907800d01c0d003000446640d40ca034604200010140900100705002d51700801c0310f841d2400d82c00c90307480c0c61308500c20341741c051750b01e512000038800986480c41410345a5200102140001c11140d004680007516480c010503a0400000800c090003e041350803164069070562015421010401e110098103161400b0300510342c198000800b10820416402d02240b007003c403541d0110301400344030b002544040d0004c086881d243c1c26018680903400c00000200341420315030b100d01c3c410255450a1140b07400001c0e810302c0b42c15050100203400c01000d848011043d900220b0119001007540c2c04207150602c0144410f42c2c04c050541d00c2d4112100c201030525040200900440265a00796a0310909901c0d11895504a110000b07014100c1c0210b50354009140ca0300200d1144410741208064440b562996078680390f0b142e21411291100344200200483c0c400071031038040c9170111241000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 783651843 1250 783650593 783650597
    0xe07090e040314030621030702120c0d1e05010f050906060a08032203050604050706021903020c0607110406090501080c01021614030f160e130201081b130825150c03 72
    0x408403040c6c0300c41210f11100351001c041d40c00460130b01308501c0d01c0e02e0103007401039170200036103860078011010512071006494000c01200ca86004408040151200c190500d1303044802032125a00c2001240e00411082c0c840305558003032070700040d01908150918800311441440210300c0c200306000b0207124403030700c00b030010441e00343d100000011540800c44140928010070103000da451400402a03e0008480302080e40e5007010500400171030f80110317152465103030030b40f00d041da00c155600d041f4460500c0705003225131180c5041e20209143c0307c5980131506950981c4c1c21103111b4024500160390303902035500e50813041d8442c00011b00c140045803170030148020001d02203446110850302c070942042083e500d01e00855400940820000e00007100c1e1540041c0b0782c1c11000c00038001a00020003205d402402c0c0d05000703403130702492050307240341c40c08036000150b560a900420603140e006141c0c50b8254034070726234500001c1618a1040071941100042200ca5898554840c000e0001c0c080e242c44c90246020740c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 783653093 1250 783651843 783651859
    0x50601090f0905031b01150e06040c030209130603030e1c12020703020d050a0201020c010f1e020f0307050a1112030403030e03150a0506030607080709060c17040e07090e0403140306 79
    0x8001031040001d4008500740500300c00e00c0e000170049007821504100441907102c10101420000c10514844103a041002a034020561101c4c2c2c1e5010790203489000110b40d0031441c18501c045400080b80c0c48401528440d0341d520001c001090104070340134a0b11152a041406800c220a00081b0803001500d0420030074015980521747d40e0700040e041140c240010360b85908090710260441d039041c000c104c003540b07003424800c81083d04240010a1518a420304846085038481c104400600802c0403808410101c0110390750385d5540e14042da01c1c1d038500c440854581911003580702840c038100d52325034003003070b034201c001d60170700c5d28523141180c05d8254114080d0f0140124039800c25904843d1035000c2c0b02d42e10452020038141002028545070460040c5114108110901030041c002c3d44000908116511442c0080f9810000e080010304400c0280c0401602c200000b40050307410402401076114070360301d8444a0940e665a203212442120483e8020300040c89071030003081e01303080c943c0915081030000e01204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 783654343 1250 783653093 783653111
    0x50d0f0207081207140f030907030206040801062318040309031e140c01081b0904060e010602070b0c0606011d030105071e111902060f04090204150c050601090f 70
    0x104903484614203680c071600000d80800008941001c89400c130710149050100d5881c03407814080b49018240c0140c001c41c4000000c54842e86d01084070030051a00207120503507496552503068000e105a10860790900c002040300105404c3d0503254030100c10700603010ba11400e1592503003c81801e001070085090041144020000c00d034281c4000ca03d1040c6580d0920b00d250242c14a0090a8071a030310343c50032a030010301100d40c1d50741e000301d00c9500190040d0b08c01e00e841c441003190320203d02074140d00ca5005407030400c3c0010b02d20340d10000346048950507020344a0272501d030201ca072101c0c41400c0001282c0d03848039001c40c03204d503c01e07200c1140a0504090184c504540d01d0006400d44d2000d0740c01ca4000782d488500c50721a00c1c1000c180041c2602c0e20f0034940b0001c080d060205445800818490a0076040c04180c1000c0d0740b0786200711005c04005003402d664958442c04481c00079005030250030003d41384080d0002c102400340010f41603940d0020002e0009a01e8449000003400b9035501180341d1a4460600b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 783655593 1250 783654343 783654371
    0xb040510210209010e06031506032703030a0506030601240e1e0a06051c020304031b0c08150f0a09050c3a2103060e010e070914060901050d 61
    0x70020048800140e40d4100040005003110440c44c00c4503c02c090030428071040c2080c2c1880c0c0f2a0028064a580c0d481c1d60321740c03d011100007241020311184016480a800280d140403004511690714080b04100b0b50300c80c1802d00d0f5650809014000088011000c01080300700031204480c9113118601e080420043c41c0000b0410440300e0800201100c100c4403d110131614001c42003c029201c28a8600c1c24442d001d81c03c01081c0c0450070248049540c0040403500707240c8074100206d8090850451a141c05d200740c80c0c1800c25400078420b0b08076901a20b041c0c13910600799549280d00400001c02580302c140c8515400f4001000d0100c400c540710703c22108001c200f034885070100b0070441050405102e41c2c203540c00010700b80c0610090740c9002c6040c0304802c800020040205941e403d04003c1e110141a203141d4001d40082026420082e5000300f0070000185190010f40d07520f21400c080da6a84d803125a480384c00080601c841030006a004905024520340346d48aa40580511441103001049103101c031052 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 783656843 1250 783655593 783655637
    0xe0f0a0801020a0806101b0204090b1603050a09080403030f0909050705090f0a0b04060807052703010e150c0918090a051213170109060519150b040510 66
    0x20340c503500401c40740310b0641c01c185450303480750080ea20340c0d64003030310300d20020300c0b0520740d00b00300e822003403c031400b0002e54443c0e5000420b041c1d40b00040b0001800e01c00d0515041421200348070000906000019405071003a001e02c08210768444100e90519045039815a0750010a10945e400c2158004000440070404d01441c1d005d018030352130b100d694071502c209001210b50300c040e009026031000e51041110100e2a011201143c4680c604a10f054545003030403580c1c1d10039041c0b0700070410301d12424000148103151840310000c1040f002000f030100032103125621555460b20003100b9142a400203409001e40c100104050140140a8050704042290030345003410180d13015002a4011500401005410001d03d40014a0328104604099454031f040440c0c44103802045103420f581c08503451241c20940203c0302150f4000400c0c029032401d5501600f0004041c1c903002c1d250340c10f0414041402e201404880300b80c80186480a20340f07420030060045040a010b41381040104d41090b2066000458a0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 783658093 1250 783656843 783656849
    0x50c0a0809190803040902030603031c0218010c1a070233070203130b13210615060909050408120709150302031618050a0b120a02070803070e0f0a 64
    0x2189a440320600002c1c0600002003185040410700c2c400c1c03042c04546000415201101c0442c100580d581e40e8100100381107007d08180780300f0b1000e45200081e04040e142c3c001d04010842c1700340145510240304011111814841c0b006440304c100845078005a500c801c5626500c511107004903900c55980c1e4080148602444804003034010700e94a0080450311000c10702900140d840c8000c46c10a0601c01110f6105541480b515140c4900000c010620b400300316400d00c0101215051400c4000f000e0b03064010713441c1109812100185000004144154502000300907100d03290389000c40c40d410012480300900003c0d0003a0b03000311060081d004681010034010748a07440070f039a5a040c00f4070385100c05500101d0a0000e409050040c0200101754466a00d100c1648140e880c2844200c1e4810b00000b1079558940c1107a5040b01840e600846c2c51244076004204132010021b81111703640e10440303403500700c1c01480c50040c076151040000c80c0400d481100800c0701c08a0080800410b003141000150130076180364 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 783659343 1250 783658093 783658103
    0x2060928180608010903090905070210020a021b012606040209030a0f05240408031305010606051b03040b07020114091e041a011209170301030f1b0608040b07050c0a 72
    0x1c040e03418038952070107042c004002e0100203100740c8074950360140400c0744c14041c818025a4541c00504944d108208401807065401e90441d03a0f000783c1c140003901d0700451603c0e01c04d0750307115000305005544191742088000c009040350a00c90207246811016221001e0042c66009409104403800c555080c071120844a10034102c2c0c5000004130b1070028200103c640c400d284420355060718170701030484050810392007580001003039901d944007c0f00d00c03031000a1100240c659840d102c00030441d0742d0000000d00401503c444401e4041c0580805a42d8034032850041c01c007100c01c10f020050040d4040c0d451205402c0b040c0b03d2250400346a100803803200b415106c8103c03200145068180c65609262242000c0d60034410b000110409041d07001a2000346100a200421131341c1e40300e04401c3c410030300f82c1141c0200909158640d00d594074200b55078100341c505000c0c0c456400d2464005004d00c01c501d403e04c101c441a0300d0b140740998994661442c0c0103401030001051000c2048250003400082c404540d44034850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 783660593 1250 783659343 783659369
    0x1320f0423090a020f091002010f14150904170a050c010e100f0e070312170f1e160c060e0a0c03050f01060815070c08070c031a0402060928 61
    0x104003040040300014105010151040006800c45c1619804840d16107506a500c003c07c0c40031840b0403030061212840d07864a061424255842079208400441d000341d0281da00c1342c0a80406408002d03104005aa00600d6400407070070f84581a9002030107488030341154100682032100c101c200f40d0035150900041d0075142c124021001c1c4840361480390034400072403240e0070082c80060342d069035907a0329540009030017040d800080c01c903000d11452841d02e81c01c002d131800e4a9141448001c8035000c6006559421602001c1e01c0444004650301c01054402c00003115840110084044251000e500800301511240d854480b11445401c040000300e000512801882d14181d02d541002c0e03007001c2244030040c4d4681d06012040213240c1002494009030660f003084403500380c8170410300b9a421102e1a60050030301300c020607104140400d241c03101084030f002e180c0340382c8020b096082d1a6800d40c42110003d600c0a002c1c082c40445040c64840380b8400d14500a46c511403500790000244200402d034840040300c064 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 783661843 1250 783660593 783660659
    0x4020d0b04030215071706011206170601080d020c030604080708041a070204140115080901020c120a032316030e06011203030e070b2d0d0b01320f04 65
    0x101030158020091b107480103541074100444805900058862810480c4086994000d0b42103903110800825041c03e8041c0340b40240c6098a403600300c00d11810580e4000c8100f200c4010b400400c00d00848072005010309a15a46d540c0d6951140d04101c0b001e0355188070600020030058a40e046580315841c1c60f10710141c6074020380c81084251060501180b49090340c08004105c0c0200c0310b024101150841d05056545039100d04140d8024014180c84041e54481d160036501140d0300c080080c10406540c0d6400d00a050180000810003080c4088002c03180c0c052000064030383c0340c3e038012516840703898900800d0007840104000d142032401e030003d404500414a0714010140c01d4802e180c030700c00540c0041c0c02a6072508a449009004030410308100000840c0c58a0382000641d0b0290348841416990944501820000900500003203801c47e02248140050000c0034031101c1400f040b001c0aa005600b90720900d044030003060708030060155400000340004162110500030038001400c190b09a0039031500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 783663093 1250 783661843 783661873
    0x10e130602090a060801320f0102030c0d030b0108091207060b03030c010603080a021e120f0f030a020301030b061c2303120a140106051e0409050f09100c080f04020d0b040302 76
    0xa48034087c12214064240d0080d400c030076903001454420100c03816100300c02c400c8010307070640c03241b2801c1c0c68241c05030048507440781c0e8041e4450480300400703a8414080382e0b140c0500076694502401d080c0316100040c40801c1c00604140c00181504070701038243c0b82000c0310b04140500759007803600b0031074101801040710015142d041102c64140c4680c1b800b0440c842c03108543c6c080c1c840240c42030701003c0020004160344070f8004402150b51120400070700070b5a0b440c082c55690000d410a01084450200d8607021078124a030500c1d082c40c01000c5904080100081c40e5145170340030060500c00001c8404a803028100ca0105102400d2000d031111000101481e02c58060350840d850b07110312031828a00000140017065011007038600210281185540070b41e03884c00086541c0c025170344003c85440c02e00082180380000d420250b4020714a0300112030200342018940001d072004160350500260100c00025214a6402d602c20b800a001403d80c001a01d04e40c0c03909421900f00f11415405644600c01400481d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 783664343 1250 783663093 783663119
    0xd0204060509150316240201150807060f05091e0f030307080d050610080a0f0617010f0608030a0512060a03051c0806060301180c020f01061418010e130602090a060801 73
    0x100510070580f180e0030b00079028920306d804038070416881081904030145d603000351b00c402002c448202201c500303990340c0c0350107541c0c403461800f56000107501c0452022450b4011401c0da10101d400901d0099004000c0c1c09190003030740c5501070581d200e00310032150702c1151401d00040016600402c00c0503507a174020b440000941e8400b41a0501071101c2900100300f10360f100010941008403d100401c0f00c000200003003014012540224490034032050050f13000c40c80c150702c20010b6105d074070001e215051b628460b6588034000c200604010603000c02030b10148400d20f078034039035000304020047ca40307603500c0b615000d02e0040e1000104903040910308091050a4011440d99845402120600c0c035540c100387c07045a04000580c040811945c854503030075481d500a0007450810803a14000300300c03139a076030788120390070b03004010f4642d00400c1f10306402c4135440c01e0300c01646d050350401441c0d2030307031a226141a605a503900f02ea017600c05035407c1c02804032550720140700720010603441c0d980105650410f2000d0000e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 783665593 1250 783664343 783664363
    0x21f09021c0503041e05041506021b100f051908060a0911070201050a021908030a060603060803040302010e010c0c0e0a0f050402100819021207110d020303060d02040605091503 77
    0x25104900010b8000048805450410000c2c0e0b08003150150102d011880b41e4001551186c100030740c0344013400380c0c066840120f524603400c6400080b003203500c035003d403210700030720740d03003140146250104242c064402c85411010f1072034918500f0080507901e0280303698010b035480c0041c00c0c00085c8281c900d81042c00302d001c0d1032400403c0040c2410446058120b00c20130100a0502ca03001c1140b000306e5000b40034083c3c2002c003101c000d0004280c90f2a0080c1250b20895041c502c0d94038208000c503c0501c24810003080e114040015440d01d4115001902c42d4a02d083c54541000308441c02c2400042600c2899402807604a40c1c00055003408141c4906a0b080101c004809520f04010040035035030750a0000380b0b00200e030034040d12586500ca40800390b0f6400c1a4403907c0359000160b41190440c2c4c030001c0d00e210b2069642d4420756507082100060f00c5010503103140c070040c0c0c02400840c002d8a014000845a640b0051001517441e03525408121003510445040042412034001340141b410107101060308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 783666843 1250 783665593 783665629
    0x20313020a05010203130e060a0e040f031e0206400302100b0d0f060b060a02070e0906011208030a091707020103064e050616030911010c03021f0902 65
    0x2040d40e00d41880340300d6a46c0c2d102c1c05010350110700105c0c003551110100c0c440501f0750500e120300d20f0300e0300303091601e02401080c0003100040d030f2070048680c01292082d034240c07103280990302820298032544454592000e001a80306e912600c21001c0c02031030614442010800c00d000c0da40c0c41c2101003a41006800c100c8a92508003007141003e181d244030b607840109200d880c540c4040840b91010050920740c4c0180003002c5d240340c1280d4000390fa03050907500001e04204903180f800b510400350f0b03511002c0e1a11088203105202c00a40410a900300007420b9401460340658010300000c0e0f04d52080c0c40c0c0001c0f1003001d400fa5040030f000011040b055583c54005d13900900140120103d00424804001d189852491007200d520f218240c0244001d0714181400c03189000d00000e5450061075500304140c0f510410741d00703144603201e550ba11044007802809900f038a190032000c0c204001403031000554148c0c0241d0001c070114055403518080002c4082407000413040460b00024001c4554410b01024107016900710b85 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 783668093 1250 783666843 783666847
    0xe0a0f0516060e060d060816090b060a05030f090c06070309091d0c060c0703062412050a060c02030d1e0b040902030a020f011202070812060603100b0f070501020313020a05010203 78
    0xc907000110f0010480040e12400d56903075541c840040105101e0700101c080e03015081c9a80f411040d0f40e49480f050390006441082881c2c5411708000031486001c00d0344002c150280300056494201495071580421000d040e1034080b0000d40000d17480340e00c80d0400300c0110740401030074040c1c0c6002d07100f1100c400b80e030740b030700328445150000b1000c7d40c2d040c50701c1800c0c0c4105400600224402c005101c48401903600c10401d01c014000488504034100d8041200c00c6421140e10380003410080e40084903202540000c041e00200840c0d8441070f0150840d004007400b984820044511509114480c040e1516100307003218100104042160081c0e412414009214500b02440326016aa01042072880f599046666014166018005881c808000322006070f02d9880410481c0900010200030400000610449096603031004208400da01041c0c03030440704041046014031000c040031004114441182400e18103010346591600e081e0380c0704030b841020703002c20400500c0841c03d09014903805800d00740050343c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 783669343 1250 783668093 783668099
    0x304080f0a020328170c09090a0c030e030703050f030a0b091303020705190e090f0d020c09180a0b06190f0503060609010312080429100e070e060c010e0a0f0516 70
    0x4081d0303640403405ca030004a000c0007041d05000e8983c2111004d85003d022150395242c0060310700020200c03841d068000c20308040d002c012000001c011201c00c2175242d00c40c41d0420681ca407445002d5000200790084071170342c400f5401e910380e950b44c0f5068170516885c800403060341410b20340242070800c6179004901a03030780c6400320074500f0107400c02d40301522907030262000d15582d0550814981a40711700050719030f00030382c009601c1081c6d01040b0114154020744503010f20b5100d1280c800151000345864111940002010f0303070001d490381c841c0c540c00010041144c20040d41401c4040040c1e10300743d110500803c04e282e410081c42c102400b00d103034012403c4460210b6503142da00c1c0c4018440c200c03001d81c01041800e100103800c0019031188408002e01c40107821060118080045810410654041c0000070600d48000380e2488211511441014a5690760803802c5140080c014550000f100b07840c000e540310914030706e4148042003800105405040c00c84115061428070a00f00103a100c3e88181d01008a1018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 783670593 1250 783669343 783669347
    0xd06140f010c0611030403180503060c07060906320c070203060103170f0403062702010e01121b0e0108090606211c0e0118030f080304080f0a020328 65
    0x2030303000080c01c0a4400701038500d02080102240c1e00d0001d814a40031041c013007890b80c401e200d02c00c03405182800b0b40ca902c2c0c94104065480d0700c22200100e0400041200d40001401d030b4103c846441d104003000b02c0c000c81040035540b0684810b202d4400041c81b6800b04c0000180ac00c2d0203190400c606070300781441c1102c6500413a4596a0502001c1e11502c2c1005c0d410742040890000c0781c95040c002d130318580d1039548a142c818054405200442030000325440084800f08864018440c00c40c1e050b1200301d0f115030704800554a18043e0b00040c10001c0c0c0c0c85620480c0410b1080112034040030580d207040074003c40c5000035080b660050000203a035031101c810401c1c1c07521001822103050042ca02d003800c002d405459158070388003080b00343c080301910607040070409a402c0a071f82402c101d002d0f02c0b0030b40d030804c40d8682c41c122000c045c80068008035880450030085000c5200850b04113000c0c0310010714101290600b2032442e4816075015005074000105540451803840c1d4480c1c02424207884004c42d25809800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 783671843 1250 783670593 783670609
    0x1060303020f250e060d050a050c040608030a020735060115090f09051b0c0f0d0507261b16050f0d060b010315060c05071d0a09020a0302060304080d0614 67
    0x607100700f652501300401c0e041c2c2c3d00c0ea070300c1d9400039500c901140e0307106205140c510b072180d4078800c44134080d80c245140030541450100641d142e1003400c1d80241101da280000894245015141100000c00d50761454050882c0b2010740240f504041d038024031070b551510345020000080f049200c000c10021400600c00490320320626421150450804a0180c55981e0b107041d031220140d4200d0340c80800010001e004000200d02c401605601205a81d43c07039080400a0fa0036104021000300f5400c04c01c121a40f80f0324843e4000e002005080c50a81d0816180c446074184482d10302c1072121180c0e21400c00ca04500c8040240176001d02400e03100c0075000600f107004211204a0700710018481034a40704003181c680d200c3e41c40030a1000d00c2c49402010580d40b03103000351124103004826a918000d00002264007856604000900322142c6121240307036440070640b600500c40c41c01300300d0348046803407800405071350781c0c3c0040e40c020f5000c0d2090302e540d042d040070003504a442c940d011a0303004150b0400b0344c0185e620100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 783673093 1250 783671843 783671849
    0xb2808060c0403260d0e0606041e112a010e0c01140315060406030204050102120a022d06010f150309030e120c060a020a1b050a060c050102090301060303020f25 70
    0x9400d0280d11500328441c0038164041c480302e030344440b02245140b080541608146c2078015040284c0307620352121820302040d00c0380603090135038001d0381840c8004514941d900500070008040038890809075040000000640e0651560b403168900e03021124851100380f103001a20341441c4002c080d140d801c9030018002c00e0100040011b041000f00019100e02e854015100f1040c00007000c055803283c03510000f0300250070074041c2c6801446001042a2444e0894044a00c4001c880c1c00800380203a80e480c50000c207901d1035641c0388038103443d0700104982d1401004518064007414011817003690070300301c030f018041110700303010b40415080204003004260000d00c40c40d04110262802c85041c0141c600403860520b487c00c003030ba08044c0c00903500d003000d58040f41c01080ac0c2e00c034480101403644c186c11410020038442c0076055010000030f0341000940d0007450400843e81c03250380054102124100081c0c21201c1560091780960058a034440079040144041b140610f4030140544030070480b0800c40741c515420b40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 783674343 1250 783673093 783673103
    0x816051615020c0d0f03060b0301080a0210050d150311180c0904060302090103151118040f060503060f01030c1505071104020c030a05070209071106190b2808060c0403 73
    0x240c0303503500300c4900750103d80740c04036403508440b0303401011040288000e00303034012040020324001010840c904000100c9048031002801804400096002c008001e101d50800780d0500c4010019404403d444d07007d070500642e544200720020a18504000700f540462019840c800c03000c0d8002150002040e447c0d480e0000038480394140c6400085011600410840e0800395025515070000410060026840000c40301807038428001c813110030710340042501855035142c0f121506010461418200b60388040084900f000002c06e81c3c0366103101190504106031201c14480760148011b0003031000340611a030040030400d0621041001c0e281d0018118011403d0003441c840809484182540d140e8042e509807104031001d895550200d42406030050784422400c078080c4c41000d0006d40001d014030a6011600000c1b009000c19a8511442c1014084022114000d5540d60031100010340c130340700d46401850580d284038425001170416140c039020301c02da00400850b8048001c03c01c4184100e0140e504480d481 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 783675593 1250 783674343 783674363
    0x1903020a1d0412210506040f020408030307120f020406050903120c0c060d1d07080d2610092405040b03030a0c0c12060605041a06031f1508160516 64
    0x30241202c4039030000b09500c00081d84130500001c032801507400507014010442c0c04000601903180c81c80306034007a61051b0034076900180000b80203540140e0f4021f4a040c550301e00059412105a030380000c913007240d04044001400800d20010f0f9007800c21141c0e581c00c2c9000b02d20743c06c000f680354040303559101f0410940c3c061400864010b640903800e17080500c003076403502141c241c201750004603281d0341c4460b88503040e100d100d400300000c8054000e88080d10380e048805442c0c0400c004200522250100144c03040701008030703000001130b54200c54418090460316103901e112002001490309100c51450303402c180e20661800c4107034a001daa00004451140105003003480011129081c40c1d94000344640c0008185400c540c1c032001001400c0d8460026204111070402c40307000e81031455102101582ca4254019000300003142c0070400344400c0c3c42c0c001e1034191204000d0368a8660024507140f04020001c041a4104207111183c40f010030408140f034000e141890401d294030722210f42140c1c0102018043d01d40c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 783676843 1250 783675593 783675623
    0x3451302090307090c090e04030e0409020f04061412012702030f0609060609180a060b151303062a051b0a050d020d0905030721021903020a1d04 63
    0x655010344522140050580d280103039141c02c0000508071210081001a41140002c034048403403c2c441c60049415503106e408011500301400028511403800366402110f222241200b40d803640110405030445c080d40035800c0102c00140040501301e200c88140311307410b202550070780801901540062071064541c80f01c81c0e484c540040307418690807120354401b40c02070200304040785100280381402071005903410050f50340c44e1940c00c644180340d200706802c20b402c110210004901d00360000b00004070020407107040603408001703004940c1d100d141c0d04d402c0c1d032103040020018031038140b16800e03003043c464102d200d102c40a0101c80141c4002010a0000c0c084007080c00d170800084c20229502502d00401156101206802c11039680c504c1421103000612681c8224101e842c030402e89181101e4000d0300a00c0309908240402110b01d450195240031100c501c08200301603039908035944004007620f002c003010a402e50041c0108510301b9000b801c1c4a62200405207905040312140d150f00c0354100b0111078460403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 783678093 1250 783676843 783676879
    0x120f080706021e03040506070c0209060108060121050a0f0b130906021204060b090a0e070303050c16030c08070605070b060409031403070f030506120d110c030345 71
    0x4451101c02120001c1001c3e010030f0a604000f1400b0700c0c05041165290380c0c8800c021241c0e07420140d0002d412120b82804550194000d90001b43c2010050400d20448940c401d88420b28155040912100702e448406020303180700c071803180c66482502c03648140440035451021030307010074400d21600e00131503030f400681080c05600e5041d242c519880754007205190405080c40f0018014015044d4828015940410300844280c821804251062000b6002c1d442c59030320140c1d0590032021800302c240c020600c0c0072030044100034044000d14810102d4081d040c2c00c0440d030f04d00c4d1059a8100c00240310f003c002501c04521041510b0754800000c0b00c01240a41c0646801c480915684107480c003d26400b005100300180c05c58610041880180c0d4200500d41d00d28080058880894502c044190044410010f895104104003405803030300004a5070301d06014404a031459024004800105009410401c4200025103609803040d410303c1c81c05500d40c2c801e11041f0b215807410717001d45200300f050740074000e1085 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 783679343 1250 783678093 783678097
    0xb130606051911060c2104020102120a0c06150e010801060f050d03120f021b01060b030c03070c0503040603061406030601020c1201060f0b030403110a030804020d03050c03030916120f08070602 84
    0x2c003c142600c0041c20031152404294020780d881800300c02240c281012001c1d4007000b070301e1051b50142c2c000c1482c00c4a551041000350300c403070003100c100100c40c440440410158010800041040f968030304007149840b00903035041c44c0c180c201e0007069050102c20446541040b0a660a680c0c046446005000341e6185c1944e245c1780d4000203c040c241050082144140300341d0192003403100c0340b41c0a042a40d800c102c02e50813039209000361090140f05001080412080c0c00181d64450783c0c40c1011400d4001a0715083e00d50380245d482203001a0300e0343c0b4180040101c1402c440082c2d0821f950050640c1065400070b5200c10704080a01d0068101d544035a48062094020a0084c12032580b000340543d282c44a5888540c0100c0341078001ca044c401c1454055000044c512401c1e0744c055888a03629202c684c20040351025030941582004814400da0341401024002507000d102c031074005040c051401c13084022004d0f202d07404030510024140d0b10740049000010a214103e51005000d6540d5240d89040b200034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 783680593 1250 783679343 783679367
    0x105100e2208030a0f1b020111041d090c06030a15090b060d051f0609140604030816150e150603060c0406030510090c091a04050a2105010f0b1306060519 67
    0x442c2003809241001c04031060306c40303089000780d009000620313510290492601c80d500c00d1300c0b2914031b5501804440800f510200e03801c0341d160750a6030a904070503000a902904182e4840507926034408405a41c1d403c2c102c01e0100600080034180501c031940000143e241c0102340812040035144d20008140101c100344030b0800d0507458409030307441c54035248002c20803001c80c0150a02d0401d070f5011009245045000c0d42c080b00d0344882040d00d0b0038101c164000410785012030071118610740f40f075010501105401000071701d40d113010042c1403015464507800c51480c0042d18090103500308109111f01c10b0091811142599007500300800c080c2c0b1160400c082840560384030080803840c2903003140503542d005802400301c8095840341e10004072842e928150360321640c071030b9a91100e43c4100421100c184e100103000b068450280418040119460746800d4402c9204c0c0040c020796103c084100516040441185000240c4010403d03c1e040c207502400700d105054041c803403075081025250407035106030529010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 783681843 1250 783680593 783680621
    0x30207030c0507140a30030e06040b071209180e0705030f0304030c0608060a120501090f05010204060f020115031704080d03050a0c1809021602030105100e2208030a 72
    0x4210b5a501c0c40e08140000000030603c85c0c2c584040c00540c084685c1310f190210243c03401034565050b0034060218043c0b4002c0030880c00d000400103000c0c001d5480c40084c00082c6644010300b59901000e01c3d04c0800c2c495000c0303c180a0182c2d100062081a0004248030000980540c1c00030707c107580c1c2c288107413030065075510141d4503210310070000344034000200c050320031030784101c8a008032540c035160107944a100c00c459040c0c200c0c060a000b0000360710070180c0f00b500503004500002c0c20700000e864289900c50000000e440d80da400207401c201040d88140000c0000c20188000c02640805a0903803100c0c0f001480068840401061709450032034003a0f089400410001085a440f003441c540041c02424007201e4110300c80b4981003c0c1a402406980040300070002090b07445040c5081c14100e030003d4002006103500c80148501340d0300180c909114250042103c8017400c170b62640342c5203451081000040030f031110f09100c059030685000842c80a2100d071540114110b80380e0f981ca00c1360100901f502d84034020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 783683093 1250 783681843 783681853
    0x313051306171c09060e01030510180b030c0f012003040519060206010e0105010c14070b070b06130e0a12030209040c0c0c060908030a03020304060609090507090515010807030207030c05 81
    0x58004001650f58803070016520100d0003070840340340540782c0800d80d228000124240050000300c941c4a644001d500103101e4a000f030001d5202d00018400c3d07029a402035010036540c1da18250030785000c025811400d030f412034504a001c000c1c03200082013410307030319480d0350240007013640c4256071142803040d107010b0720003d001d4062042000b040c180c0a540c0e140300710809405068000700d1b80e1b804601000303043e82d43c1a1101001c840641c2e690b842d080c050750030351003c0d1b401500408100710032010300419000c0d000e400c82c1401d43c01d00004014007480c04015071190249007080d6030300c1c844c0c3c010502070040e0390840b541070f034008600c00003580a4402e54019690240c0340004804a150b045102d211a090080c0b48a841c050740315142070712840018042ca000c164400d015481b4694440e4000f5640309100d44400325960b55102201c10a0b2810300604940c1c03030300840020300800440c0d2103000d07400200030019050b6940180006000d084c4098840410544c00041d4070060500515400403801c0e0701000701c80b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 783684343 1250 783683093 783683129
    0x50d030c06050106031a010e040605030f0a170703140c0c131d0c0a120305070204020f1e040e01090504030e0915030c010c0b18100c18080313051306 65
    0x400d10255500c08850051414002050291013403041d620111441c0e45902c401e0200b01c001035039042c2610030200d40c0180c4030100030450361010f000200c62a00440b0050a1005280c07612404841490421407040c180900485000c81d901c07030700d01125200b10b50241a03644504510040c1440f907045242500103c8090341100f8411407503002c1e4040042d040c015040848002c881191118a5004410303071109038440b05026200099230710000b281d02c24141507113848030940c00304003a60400703a0240d020400205c0c1201c0a4000c0c20503a914041400688920f41400c08240c6060910103005441400369558002010036000303d803501459600240409041d00c0c1c030340c0900e00c4161068628034060302403454650595400b515450560540c802004001a541c0458859210803a0524160345208030101440541010b00c80c003070969225076600341035980b14240d0700156144e180c2c008800355004121000b26142c84140000549404448102c101400d889842002c1c1406410030b600e804101c1c2015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 783685593 1250 783684343 783684347
    0x21308070605070201140703200f010f0c0f0203030408190e040219120905060604050721060503120f090906120106181d0d0c0f1a0f0f13140304050d03 66
    0x190040c113200341d80c0c3c1025180600c1076442140244440100460300c2e428a00c7c0e0902064121101858950000c48200d03280b08418030f400c1d03a002ca644400300c9a9a100d09404150b4000c510002c0090030b400114034609050b40d03560294032803400c4e0001d41e048000601074007075200d00e90342c11454400400542d103440f40344400c107a05c01c40f00c0c5260780115402d50900403404107503005004050b90007130042e10441e074071402071101600d0b00030481400c1010044414005164000101d484400c18400015600e801c01090520f840641b0b075444101034002d1210044501c8c441044447e0080c0c25100c514041c0c0b96400030030394818483c0340340d80300ea508100300440c1078034043d081c281c52007502403001c0c408481c440004020000322600c000222360403100b8007c14180c042c0002040c928850145c00c2d03240c4030580c136940501c000c0d407043d40e001010300200303010a80300e00031030058104110b581001c01e2420011444022144590780040400000303940d503ea00031010b0060b1801032502400346600104140741c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 783686843 1250 783685593 783685597
    0x6041e020d0501050312040b130306090c06020c1c0212120d02090f0f010e09040c081605090906150f01140c0c011d060d0504140109030f021506090604021308070605 72
    0x3260784840c5010000102460001640c0020381040b400d101e113050704152888101e9800701c454640210303100c01c03002000a0080c400d011085028a804103070789810103c0083c1801ea134000c01510031003440f48521540c1540303800c04500a41d040f9481980550000303e19401c0518441c1d011314800c202052000c840a2550014080e071201281d4080703282e0031000401c486041c40500da035000514094540c6028141260b4490701310380913212aa54003a6151616031800d00d0008880700c045201c400700308400c0c1002d08103290000c4e01040503140518080d44c04410507051802c03668420060039004040c40d034022442124050b8000800d1640c45202c401d915988a4103844074500050354291285c0140c2c06800d203411a035040142501e1038140c0017041580508000b90040d2000001142024461107007481208841442034460010b000400c60019003000b4400745a48001c40c2804104120740d65102140d5621260031100141c450884017090614003000350058041741c807514101041203034000300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 783688093 1250 783686843 783686857
    0x3030b030d0c05060a0519020f0d050609060f01030c030b091807050307060206070e12150105040b0a0b03060922080c10020f07240606050c010b010306030506070806041e02 75
    0x10072260890500d2004440c60310809001a20a41208011aa9400d80e40d080725800498400d950304006900d491a14101d90000c445140034040000c1c6c0800c06088900400c0c1c1e002c03004071002255454100c0118502c4003491441e80d04159494038502c11160199101c10f141d41ca024102500916000c515406074804041c481c4400c0e1045500024161400280e140150340b1030351b015002d15140d41c1c1e01030301c03510b0f8550700466025102080e00b258418081000c008014003490906045526010500003200c4080344201e0054140d51418010824000d04807508200b0035500d40c04030b5502e2a0303921a4000d2490240c8801058820080c018031190030007510900405a003520b960024001d500e5049100740c150184e410340f13061201b00c1c08109100c114182a880340c40031050b05ca07a0b840070300d500b2104150040804601c011401c003a410300f0912490400a8081c02c00b0441e45045440b955501c03200103240d00104031a4400150701d54446400c4072882100598050300b80c10880705010003e904214 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 783689343 1250 783688093 783688099
    0xd0204080705061c05191e0509190219030c0308040e0708360d05070c0812070209042906030609070b0301050d170409061a0405220b0d03030b 62
    0xc90003260ba440d01800302c4081d1014240400351504d201d5010030081d0100071700300d104800740012a00c010b0070450140e0079010741c0c0c1c2c20841e1044110480500112400a81854015881b003140742c001381c41c4410481032850f404a600f501c5085107486040945009500024040300024600004000041c0054000d40325483c524008982d03070003070101c426003000c40380340803026201c808007103000003084540c02d42d68402c4d5420b08205a0004441450900000410030000d880040c1850034420464a0100a44014400340103510070f202ca213100c40d4000da410203407085941c3c60110f010008203800a03181140010058107128a181d500600300b5041140c01398081d000728400140880d801007510300956038240500d40c01c43e400c180a001805058003000c4552240300620004008a108080c1004000310300c008101e890a08030b004002d0140d01c0b00f0000048000e0100b40090f9480320308135100a02c02011008038010104d5004003d00181103800d81c01180c211100400e0681c590080c10f5401010303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 783690593 1250 783689343 783689353
    0x3200307051008190b0a03020105090316081b060708030a2d050708090c030d030f150e0a06150f050f160b0a061d06100c021005030403140c0c240d020408 67
    0x2e250090641707000d10055a84060780c42c0307007440198003c4d00940020302002e01120a1130b50303c0440070400340583d030455155980210b1030b620400d2004201c0c1d0b1483e80056584506018160b81c0c0c01106001c0944a43c52003074807440800891100264400e200141c0d103100344444081001c3d08078000c11098500c40c0001c0c181e1000110002d00018040386039500c00390040c01148411142100100312255416400f031303440701d121100b09c5207152030000240484a02160365400c2072540782040b07072003a900445003883c12400845440e07410011a408400180c2001640c804c0702c06040308003481045d2080a005484240003800c0c00301070158644102031781642000459100d021f411b40504090a0740c0a1000b44080025010b041c01c103d01d141c0b040082c24640342102003075001494102501c1030000004a0100400c424035038403500d03224080c07040041c0640b0f441c0d6841105501e901105800c140078840c0c5405c0220140c3c4d00d01004010072808074030640e01c684110340030201a600c10710542d0054468 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 783691843 1250 783690593 783690631
    0x110a06022212030c06060b0c010b033007150f050a1a210312010b210103020a0902070311160905060402030f0123030d080f1003200307051008 62
    0x8001e007010b0b20742c1140070420a01180c0e03811940b0b454a07501c01c5034020b0b203581000607000025000340154405003000840d0409002051518001c00c58580282203242180344111500758003002484408901c4480740c0e0343c200c00c2c01c0c450b000620f449503a044d401e00d070403c403c41c14140c42c1d210f10301a0446c8d007018003000f140c1d01c600c080c81001106826601130083c8181c0440e4411180c3e0400405500c20140c0b0b0a20318030b03025030410404268800c0311400701c00183c201c500c25031900d5a01940701c4106546840d54195008200b816501380200484ca55002403c901418040c40b0b01c0340310384000100311404503a000801d10414091882205e41d0741e8200070200d40c1c149401e00941c0c0c440c200d034984210180c1e280034101844692003e01c118185082d800707080030304c0d4030305100c2030390308005948514581d410242046490014003c2401c03483c41440711f0203000081a584c100340c10761245183c50105031841d580041d040c0145680030b240d114001c5401d60000c140c210354141c0c498010321040303000d8418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 783693093 1250 783691843 783691897
    0xf04030c0f06141830040306091a0c0409020a03020c01150f1403033c031503030315010e01020c090f01080705011d1905091312031119110a0602 63
    0x4000d0640800d19041045c420000c03841c0103e88100c0c035207004084100030740b0b00c0400044164426003040c6c1707107a6107030403500c000e000d8420b44410032006010f20780c286501c1e2604400c0528002c80c050240540c2d0009500320307006229406550145078840001c00032200e0807188119803103468030643c50755455004001450150401c2c040c104040e010f00650300d8545c986d85048590314856102030302c0341001c60803043d420700d802e0401900c00c00440145603501d061686e1074010216105420b030344254010000c0103000e120507980e03c100e4413000c7c02c0a84003002e03810010f0703003042c000f000c0b91a002803000003000142c032170240100d4100c42002d0140d404042d26140110350301200198070f1064003550f41c503e50800d0800c03154410100394100406110661980c4c00581000d4055603151034a581026034070051040e074101f240c0030840c031402c00b0041021305148250784d03800b0b148180900c50200100c2045150b0003988683e0454520000740c031070304041e80c64280001d4105c0011400081801841000540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 783694343 1250 783693093 783693121
    0x51c06170d1e02070b090a0317070215040302030307030c2612071806080a0225122a020a090c091410120e01110406030e01051b030f04030c0f0614 64
    0x1280c0d42e40a0000f490410f5503460311a840418141e400c9601250004080b4405010103055609c40d00c01e944c0da1740c00d250041020035800c82c106007480c040200000c00040e82d00004680b1040d40c54204401000154200b1070721721284003880d04408079801040c009884c034284006c0c41c0707200114401d03182c1c940f59a00215402000b00c01c40422403541c44100748111401402c80c10307031081ea6840701629084000030460340c0301d08c07500290349103e8410740302c1e0001c009141108801d40c10041c82c2041640317a100c12200c078822080c01c00032080301402c0d41c1c1d01041d902d41e844164090700701410140020324507903a000b07140800c0c0303206044800755540340300201450904400d17120310400e6941c0074260400702c01e40c403004012034400002259a58100e030394070300c650800608000c01703843e200020241c0e40c01d03001c43d00f510720040110400c0c2501a40c0c12400304085e0081d641c10010201111205580303d01c0c05442d00c0840841c003808001d4800c500368204100358004140201200701d0088460f1078006038601c0304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 783695593 1250 783694343 783694397
    0xd0609050f041b0302041b0f08090303180f03070b1006080601170a0e100e07060206010807031410050c0310050303070b011505071a07090b040303051c06170d 69
    0x31086510205010491151100c0e50103c00c0c0401c51000b180e80303a00040807641c20b00104200b4014000001c0406c0d90800a0341c580100903007480d61311450305003800d44d16071100511a03c42c1c1d5103019451840c400c1c0402c1f05840355868281201ea440b00c03942004c1d84240811144414050040000854014414800e490081c8010f0f1922703040f100101543d002c1e5207500606110540e80e490070103085010041000e2107285040d440c00054900200c0b075080c1c01d09515821010555100c417004004049001414a08503a003001010324502c81c0000c000e806d01d05d221843c26203041c10f00341030003046a03140340154082da0030b4001c0b03100d80aa48406040c0c490140d8000585050004c40c010801080341040980028140d03240091400ca4a65105808048090120700c007010903001000041c23900144268040c10301004464102032450354005c05a00c90419001d042120046c50600c0300d81650b00040060040c3c402d0044004442e202d940d590780880b04c8584c0006004a00170600303c05884002e6454 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 783696843 1250 783695593 783695611
    0xb0c0f010e0a0c0b0d0e060a0504060f09050604021e0a0612140103031b050c0d05060402040c080105060a0e03010b131e110409090f0206030106020d020f0319260c0d060905 75
    0x55034130b0442e00040642081d21600400c980700d0050004e012010b0101c030b407065845a600084506213805c1800c00c80d00440d42d40080c907450140c3c1d001c045500010b0713160b031107070341210b5609603100e0b034044420464403828a129045440a0301c0800e18a40001120031181a071402c00c20081441c0c04c103000c0700c11800c2c400907010455002d0f40020213035400c4142c0751264014030494220340b0011000c9800403800060030348254204100384000c52070180180d1040d05280d03d005c0465506020001d0a9807180443c2030f02400b91200e014404d50314207400c211007040005040724558159082c608000c2d0042c120703c0d00c11089501c40b040720700300da00e206604041040015413401c05080070030b10b000500b013007401540d685c0b105100724401a5600002940030b1b000d113502405c0103080014000c0d25100745141e580419400c2400080e030030010f9030942003000c405600c0c4c81d000c00001c0c0d804043e078020442e0840c0400701d4002041000d240e402da00284042d0240701030402013641d1744c0c11030500b00d0307800341e5040d54 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 783698093 1250 783696843 783696863
    0x8060c1602130b150711100806060a170103120206060411040612090213090c09020f0717120408041509030b06101115041502090108040b07090b0c0f010e0a 68
    0x16082c010b0204142e0407006400040da4460740740091410400d0300203010780309000166000401040d8141030580400c1074441403040c2400040140c82500000e1030745002d03650128200414512450710071030009100c420400c200c2d40c40c1e080407120050300740003810241c480c0f080400d003641050301c102c031302404030b580c142800c040c00d050046a003035000c0300981000c19100c0c80004c001d6a203858030700d07011411110001501141070300d8100c0c8c0500c495030104407a2841409040d0021030140125000b00754462881e038131401c1c1010340c0c1ba155010348000611640608010401000042d800610a440a812001000c4940030608545c40e0207540002401a880100460400d0234031603540407011a01e800c0c054172031400521450f2038083c0e0a507000c00ba42c51140288010b0199480c4441c007080f8074140700390b25109926001038480d03c00944010840c00c450380004400c01c0c40358032010301030f01030711146640c0c890780100c1490f41c3d0b10f2100c40310340d03055281c03101a46c146c1c3c4000410342d0200b40c1c040c1c10f0b44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 783699343 1250 783698093 783698137
    0x1005070c03080103121106090a050c030a0c0504150314070905010b0c100c02010b10030b040507050702100809033a022502031005040b0f090d0e060706230108060c 71
    0x6203529402e01043ca0611005200b5140c2c6d44105026061069030801c001740400700e240e04241d85442030302c85610b8042e40200c81075070b011425804507101540c81c10307280031524440450b210b4a111a4036070010b0f217007070b5445244000c0030382c0c0031030074504850b9049003d005a980381e440c040740358818240b80c4100c03a40582ca02c940205040d80209184d0503213030000141c20040740c408070f0422128003041800195030344455250f90f02d01807146540103c01d520b003283c1040401c1e8003158090707024000c08020303c81c0e0303600001c201403420401c454001c0c52521b0107426155000d41098940d507605412400014082d002d05c05c06000d00b8401e4806e8044038550081d181161205880d598544002c003d0760140290240c8098800b224003420307015600c0b0b06860031440c0342c03040c00112448406451240541c0181d04001c40039640644a0450444100ca4003540c607415490000018141045013a45820100021410f800740b0060704604aa2503802550515a40e80d03400072082d00c10348203c5201d400c00c001c100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 783700593 1250 783699343 783699353
    0x601060906170402040b090414060a0903090e04060b0406140906120c1e040903090618030b060103230c12160f0e190e06040b060906030a09050a141005070c03080103 72
    0x3c2d00b00340040d2000815140c0200030521214040f9000c2d10614100702c0329220b49101042440c2d4403a02d600800c0040c80030540e001006280349105241c22508203101240c2480519407180000c40d05c020020061165030307015403000041042800f030b210344010000180035041c03603541c0d402c8002e0310501804c1c0b02003400080241d4101a100c0840500d28646070b0b95160b07494070321070711030043d0107030b1103194150f4504107000f000c0603030800440c190098211030402c00036910190254120344242400f080964019804c1941ca0041904803080701031044140301800c260603000b0600b99071101c00c2c48074a5a2542c90000c211195a5074001c00501c0c003c40700707402c0c540f0035400c050792400018000712504404c81002c62100700550000701030791015409001941c40d01d03109140008406590325401c0c510410005039182c0002404800020348a010340001c2020900429102951000c1c1c2c2c0031a8000341c00045640c0e0300f401340221b201c5880c10b0040340410303015050008441340e2581d1020f03c00c2c1e0031035980d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 783701843 1250 783700593 783700637
    0x50a05040203090a050118110f21160902040602160806060105032203030c120606121a090408042903180708150402090f0f01060f020c061206030601060906 68
    0x3c0100e00e0040d0441440014801e0040010303042c100c03d0b0f03022080f1580c1c286020004800c2e11a07074840c40d030202e0103a0b5241c80c0c2e0f09441e5501e0705603480b86042460b520207443e042452000030501b901114074404694403c0c9580038100baa4081c0d42190508048032440080894490160110035482070000482c03d6103c2e80007184d01a10800841e4410003142c0160550030101020840110343c944011070310007513025450308480c0500400c18882c0b2417034800e000e0416035410040b50082d6032140041c540c2c400b080c00c0600300140f0f0281a4a01510300303403c118865030001c0c014610810034084507545a4944c00d101204801904c0c0c114624644401040d0414a4910744012405010b0300d40d0008841d0828800503100c000c40d0181406249010300c1041907244005000c0112001c20390144000b00b03521498240c192072249c02c1c40040e07007a01c02c0c800d034513200e01040c0c000d80c80140000d550381034601d10008a070090300c0542c01c4826690321420141c0d401010390060000151181400f000102480d01d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 783703093 1250 783701843 783701851
    0x4060510052211040b1806160f080c1507020d0c080d05250518030303100611070e0106030f0f0c081308040504050a020c0607030908040303140c060405100c09050a05040203 75
    0x2e070004402078070002c00c49158100f43d00641040401143c0d040e02c2c1c1e101103418001c0803c0445449141088034940d09220b00c6603101c002d840450400c182c201001101411071f12284040f10031030344482003040c542e4180315011105c6000600544138001a102c0c003410b4183c3c4da00d076110015034201140180050010300380100b0480e454503e02100742c84004e00140400c08050843e900e05644000100b4894030410b10f980301140281c0c400c00805c03403500c5104264009551043c60460b4413403003038501c07881c948000c03070b0060b41b291088403000140d0380f50103900c80349441c107a0740802e000c00d401c2d02000d04119416a408500400c0403a000a18405100350703420820358400d2048a00781a120008207086441c03c807982480c00f54009a2500d018500b0440c984d801200ba02d800d00861820703907590170f20b5000b60300c0010248034610100540d2070b072a6105039828a61600100d9005141505002e50b845800e0340703003e611399290005412005110358103a00503240043e100310a9580b41a0500001303505c024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 783704343 1250 783703093 783703159
    0x3010e07020a020a0303031a0919050c1b01050f090a0b0705160f050607081012020d031b050c0111070f12141902130207150e011d060406051005 63
    0x80b02410041e0b5400b20104c01560099400140b40000411120003010800b2409840303a4901003c000341c10000f42d10b001001105140e02003280e440b150b846041c20702800c0d00c950103855a401021b1210601503022a200d404034201222040c0ca60100868840c400d003a00600305045290020782524003d0004011011a8000303950b01101e6030388481c1e1810f4603003081240e03a604200113100c40075500107a013540004220800442c480c4c50000102401d2181480084c0925511080302c0181360051000300040c24aa00400b540d241440ca05551105103000820b40030400c00b022074050448000764103016070b580300d903c600055080801115000c1114102101c1d9050030860707200003070303c051001e580b0b00c01441100e902400c00342c0c03040003468a140b030806440c240c814440390b070120350620380041045a41020005090450208160141c45007000c0307903a0803a0301800030001c41900151452250340607000c100503517103880401003521185441410ba03c42464000130081d80030307203074100c030182c0b1000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 783705593 1250 783704343 783704353
    0x4050622060837021c0807060f0501050a060e040e010612060e030a08041b080d200106030c0314011b03061809260409090b041a090303010e0702 63
    0x4030000c009849800842200e860700c0d1041048007050800041c0c0b0315060843d01d8031480300c4014070a02c0b260700701400000106007803507901d40564840f085140400d6209460903240c21250341410011a4004902110b01e2031501103100e0302008d091040c503040e600c0080c8640c8000d89803d4007103426451000c0c20640c003d42c0c81c520310200407024800c100c000c1c02038160744c0c0411007a90a20070100c03062600705c030320786820400c14080460391045101d41c1c0246c1c4070035903d4000030742c0882c5130044401504003140500c5034626804610b40c001c0c402903a80f820207215011030240c0640c00509170743d201d01c0000c20110200f101880002d003441e000c01000c48071800000b40307600001c0c01c4045100840070205002c0303640c0d010203002001d004100078950030283d00d400e000b040070641d6801c50311004004100140040f8810094140d29028102c174010061440c06000e0f044882c140410402400d49080702d542e280205039012000300d40e80418800c410020256046a1030002c0801044400a11f00c10860080c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 783706843 1250 783705593 783705619
    0xe180601030207110a0f03350c100c1d04020f070f0302030d150608090133050603041110090b030f060a17060108010605030102130b090103060509010b0309070504051302040506 77
    0x15405d2400300400c0f000c01482607036440d50510380344454999005900d000d1541401d404441601490201070440c0422140c0d9110343e444c01d00c50406051070b442c2401c4504080602c0041c581c000002103800d0007008004041c1102c20007088101d1140c245019624030303080c0510000302e52622200b07640540070380180c92500902ca050031040f40d003081d02003000c40e008903c003842002c0e48480d9040e8801d4400340204052003a5051542d03880c0c40c3c0d015003010384c0d07042c1c04103800704034002d01074500240406409280c130f03030034207280030384000c801141c103580140749244807910300d00c0c8034015603412115500d00061650702c4402581954410050034a03803c034180380000108107011503601070092181c10090b00082d41059a040c0c00e4481962101344641e0060110782e020b441250b60507000c6030015804250707110a0800140c000d4800f40d8040b50f4000388800000900d00c13800c0005505c21598041903800c07498a56040104070b440948604184840b1499403000504182d40401d401050081800c002028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 783708093 1250 783706843 783706849
    0x11120f060115090608130606090e03032d070809070e0108031306020c0a0501080a110a17010909030516030309080f040305010b06070201051c0b0a150e18060103020711 73
    0x202224041119031156004002d18030303180400b69405000382c60881503843c5050790041c8401c2d4050122140522011300e4402000290b5101f0310041000905c1800101c410a0071980c5a030002c8a001c07940c1604840c0c08100c480c00940c6aa8800d590480c0d06461620f4008088460090040c0b902c1c08604c9901d00c046071120148070301e02c0c0209a03140003141d494258982d00101020641d00810a5502c030424482d116614000113405444081c42c244040c0d5517070041100182c510750281c1021030400150f12a50a80d1290312001a276042c0305000c11166070380c2140c01e04607102030b0b9010300003410034010030003c0807019040c8400c01d4028030740400c20103407a44030222030b68421840c0c612980c100160410402c0310a000356130b4440b008a1790b183c10041d1035000a0800d00c18648081500d0b903008500b8400e1a8166201884900d0082c1c60303840f4064864081a211102c0c0c1d0b18194042052027094580c0c510b060346400b0f464035091600b100b019101d40d40107401030341144000b101c40003150121112161 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 783709343 1250 783708093 783708103
    0x40f060513030e0a15113f1801050d02070b01060e0310090b0703091412040e0a180305030628210308060d15090302010e0c100c1112 58
    0x1d0052500404000340c030740b8016000030044041903024104480d010080010340c48001604403945040c428000b003141035415080117180c2c0a0030500c0782c1c00a0140711448115003044402c0200c943c41c100104214140c0403409014184a44c1103040b03c1800441c481d520440103020201400134002d8188080d035074078002d81320f000b60425400038510030282c01452404200400681c00a1102000301d42100d4543e40c202d1203000f04004149a242e04d84202001120300310892106900820b5680f206060760800d038441c0d00502c10340c9a1070140340003092003043d1274402c2c2410340d035044880042980c09a07405a540d500010911369121040e29003022004c074106c696a1758412804095289079400d0501180d400c240ca90003c001042c00010302d03200180c0c02802d802d802000483e07120440c62828644030215244550311841c15600304420700d001c0640540251101c40b924106a41c040030410050245400d04148041c000403124403a0401160700400034400b84800501035100845010a085141c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 783710593 1250 783709343 783709351
    0x51504140a0317070c09022217060c0f040e130c091b0c08040b0a090f060c030c0b0604020d090501051b0910030509010b0a17070501050405150919090e06010b0c03040e040f0605 77
    0x44420400032300c038503030900b107580c0303000c0d11404c2065400c0f06400004240d448000402c1c002841000045038a02506250b060b10000c0406a00051162902d0203a50008100c082d80441d288aa80f071400b00706032106001d02c008002c0400014004640c05a50403240e05c40e00e11821350b0214410440442c0344130000d00142920700c500d44505401c0740ca4805100302d68642e56001c441002481c141101c002607100c0764a403280c90301710300403942d15114200058020b11516850384451454101144104881034004a11900280c1078501c40b04200e070384000424031070a80c040d544001d10000d080c900d60301a92100303810000d42c40c0000381c2d0040c0800821035480d070a800c491210030541034045c8051604005007000f82c0070031b1810500b410b01d03101c00304840800d414000e81c0300810204600016403225401070b0b00039080c80d010480034959918250b8024414100d541c141401032000101d200c400150848281d041c1110065143c41d1614a980740c9500002c1c00132070741c507a42242c0100100c1c407240601401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 783711843 1250 783710593 783710617
    0xf02090c1e0405060307050a03020c070906150806031207030207030506070c0c0f15081f030b0702070e040c12020307080715080610140310051504140a0317070c0902 72
    0x185000342000700c01881240c0c0c40409a006007004203103e507440c3c460070b60381c104215040c0f0585a029007003098000e0b000f050200f05013445a890b00280140c003603080b40701147e00c0350003640060544d00204580220b01141c1e9140c05901c184000c40382e009425000b400510302030b2065585040d00e9984603030511400380ca40b02c0003d58828458814072280350002d1004000015200392218501840032102d102c02e60f0902e400d00c050080020a20001d500b15200030701c51400e1032580c86601c9180400c296442640c4503001845621030101d00d00140110450042d0b4001840514461804e40018031070351503020f00300c2c2c050042c8200060300c60300030070008026101ca11501c4a621a00c600000c00c51784004010904c110f5480b45090b40d01c40c0c00c0003481c81100c4540103100d55a65807203085030000801544030075001442c040054410380f080d14060410351700c40015588096410108100419515000c0642200300c4c00d2a9011000d04100007800d031a40b0690590b61660b0340d880e40c0c10100d80210180600c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 783713093 1250 783711843 783711847
    0x60415140f010f0e0607030912060c08010902090607020918030c010603061b0c0b0a180605060a09060b040e04061b02060906160512090309030d090905090118030c0f02090c 75
    0x219034070300304008481d02282840c1401c405242c3e18401810b503030749600c0c110b0141100103050300925224010a101130001400c0c03148a41c0400e1400da0700915552007114001a03d54001081c680070500842d4600b0200400350b909000890702001013441c405030100d10101214170b264030000b44180702402c0045c03000c400000d9464038505042c000c0c0c3c1c0811383c00904103140c031605203036120381013000480d030541c0000c00d2219540d00c843d5601c00502042c1820b10b018000c0d20050020041980c119031300c0380006840c5410500d40e51a2000c064031141d01070414000410b000c140200f11200c600290701c00d0140b117020a80000c07042c2c068071101d480e0080c1c440160001d504101c602801000303010340011684501880748180c2c100018500e00658100380c2102c40c2740008101c500c5410419034400c50402804d41d8105901c03440c0c0078215440314419038448500341000519040810b204083d1510351114a405d03d0242c5540c0031244c41c1c0c0000011122040001c04810250b15003401041c800e40a26a100e9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 783714343 1250 783713093 783713129
    0x40b090a120305030a0b090c190e0a0f17010207030c081c0614040b010e010207061107150f18050f2101050a06051306120f15020d0615050c070e060415 66
    0x170160f84084502c1e900415002d814017121031503079400c5540a4520001c1c800b000c40d00114122143c2d660282c845a0090f40101d0200c1d2105503800381c1e404681c00f00c0b1140502c1924180d04c40c0c240e010307920b80030340030544850b0a0804590b4030740051504004032500a8401040840d4000c1210078941050402c900c4001c440c51482c00d00d440303040318140d02400c000e98034200d0000001d54842c0a40110020050301d81921385102d0341c204030120280000d150f00c83c18400c0f03094001002c640e2a4484000020852480c207545082c07445010820364a0181201d030784042c0a005000411070302445505480480352113410102c1001c1c480c00f802035101c10404607545240408101040c080c98083c0503003d0329090003000000b0300d1000440065900c40441801e4008a0030040c4c0007050480b042e030701980c00014000001c540c1640114165040a00d20707050308414044101d410b800b940e800f000880e807088800f80001c400780000103501402c0148003081c0c03400d0725281c3d004290a03a81c402c145910050605e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 783715593 1250 783714343 783714361
    0x6050a03112b03050904271104140903070303050c0c0d03020a090b070c030203060a060f0510020309062b09150902040e03181203030903030711070e01141e0303040b090a12030503 78
    0x507c806202c603214020119801c6050300880c12601c800107040520b000380f40f00d4651190b410080280d41612030403681e6140200005860354081d000445c0000e142c040080c4100c9005400c0e182c11000c403100410f140403044400340d000354401c04c91807081c0000654002015000d200081c200513100708000c0d20780354514414945803400207858021481e007004c000b4412940c0c500c031014100c07141140d0f080440403040b4801d034254030404804d190008400244404141102c3c40c080003100600380031004045a4607074407d086641c0c1030300c01401440d035030540b0941200541c00c07004103140018400924458065055403450b88100c80034900000821420307111883d114100c03880071480c0360003561551410f440165164880200040d06004401001440f181f1040145c0c01c0503000c1410035040d5561a0034038140a40360244409100380807100300300151845502c000c141c0080c0c050025820103080c484c1c0c20120b80c1103203000540088525a00084030310071804800b1140f03000707840711992401c01c0004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 783716843 1250 783715593 783715601
    0x7060e0111091305060607080c07030c083f041412030c0718020909010f090c1d01110a0605010e061203070201090608041b061206050a03112b03050904 66
    0x124800c4401c1030001180a890303000041442c0003483c1c00008803a03035000001100c0c1d001d072120190005501280d102840500001c03000140c80c003411801d103601d0703a1402a16500e441c5107981001000450f00704556000741c80000c00500da004060f03c1c0907080450500c203e807900a030748840301a103250540400c4038103249007404041100d140140d49000841e54039159a140c1c103126480300c07049507520f82440268158140c0310003200c010100c002c031707580d54000c01800090500803540003a00d400a4114154064503014005415003200d81d4416002d030001902d4030000398491002a00642d04030380d0016600d4407c03e07020744849100c001e07607410f20000b4803028182400b007d4200b0b5004010302c2d005072703800106070400c4a01c0d6207010412940c2e01d140c80e9524440c5036882000d80c450041010902c5034010f1849201841d8130300040100319035400410101e104c280c800601050350750b00b0905c006050001c55100c204580c520002d40c802100340c0d0440001c18030b1b0000380e00050000c100c0081d5842d003401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 783718093 1250 783716843 783716861
    0xe150d08130e0f0f071101021201060f0302070213020c0102070c081c0804032109050f070e060a050f040b0f0a1710020a202a0f0312070303180807060e01 67
    0x40c42d0301242c03030800341580d0035910162a00c0380d6a9050400607082d58459050309240280340740095490700744d01655050044000c1c0550320205444100f1021654460b109690f00c2540085c00d1443c0301c00c51210020082d0b0007000700030b03400d540070081c00d004101082402402080c41a008100340b60500340d43c041c21104010410042080020500021a600c00304a40c4203103c0351200907410707020340880304014405004d0081c018000c0c2034000700d00c500d012034400103c071a50b900d000a5943c4042c10402c40d0403090103003e5009126118003c400d0415512072200110007030200c0603a114240d00080c903828240d800030504e03090254009203d19028030510340594410342c015410510f80740d00150003100e13841c0c8070280d030340c1c007083c40000403003001c0000c4180441e1522041d422030341c450b00303500c03401c2c100c45240301e01a0461050058060500040c80c494904075050440d04000c00c590302100902442012268030180000814012901050080c0340c014452200001c0c52040b40b103050703003903510041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 783719343 1250 783718093 783718109
    0x18020a0e070504031b0909110f24071b0b0c100204050d030806150415021902090112110a060e040f060b0a050703030f0f0b1203070c0e150d0813 63
    0xc030a0114094011081d6801ea030f40c840005200f00c903511480310600145680401d00160030301185906001e0540484544207101783e450282801e0f440d42441301c58408600740580d82407440c071003244046501d030701034040c81d407142c900220101c07034080c000e4240750300c20303004006003110006900103030000070001800c603450b581c5000c0d82040d281c2800907041e11201900901400560800210103507120055056040146103078144c855861f810102280321400031180c0161040c0040f40c004201700165811000ba80144059407aa01380890400340c0d0102007022907212603003202d62404c540e511114800074003011380c2c41030311005440b01044207848802c14150940c40c0340c075800740410741600085031815662810041d03a22046840e049009018031540c41d0b0015240003440c0d02001102d030421012244126481c04020b1203240065032248500300d001408010b400c0020010031100c00002c40c0e11a1143c0208100c200414000c036204100d43c40381110076510000341d6a507862130054010300945005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 783720593 1250 783719343 783719369
    0x120f080f190b0310090c05030c0301110417190303050604180302070e0c040503060f07030c110d0e0f0301020d050906070504080a1e081204170a0e01080a0f18020a 71
    0x140d003072069085500a032084015881d0507a191440e2010420a0188004024208086103260a0100d0800b456000f418800c1c01041c041c000d19290500038000c0c2090100da01601d02031400381034100400c2185040d503080d001d910840e280895642f07a407500f0140c02600c0108070f51a0260400c801c64407060002c03005a8001e2941c103000c00da000581200380d4a0481c001c00d60390700c4044068503203000316404a64180304072000c019a400b0343e050885d008c1c19458900340803000c810031040c1d400e40720768407855103035034419513042c00070500c0703041511040080070b840c1e034600000810110303003681c0c44900e401c560b00742c4400500548941c01c02803d0b5010304907241c49401c4c541007203000b60b2100da100c440906141c8485a100c0000d1340800701c20720549501046007595907241c55413840791b07403108a5080d40d4410002c1030300102e610100d0304071207800010f548e41580b10111603006589142000d083c0700f84296803021703038507412001031044c01c50304401109490703c0070106104210344101c00781c000804000c19 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 783721843 1250 783720593 783720601
    0x6090d080106030615180f1205010b06030f040b040f0c0801022a070b1b06091c08060609010305040302250e01080d050301030f26030114090412110703120f080f 70
    0x202c4085c0440031a02454250250028071501d0090300c0c0701a000701c1030709084440e0026910f2012500066139501c117038000d00030501400b080140324042200e0803030b59000707044005400544400b0085034000e00c00c004445800080d600c40d01101c03002c0340c12802c442e0794005502c2c984072505204140e040380341401c1e174a0402c1951400f81c0d03203c0702180b2580c1c822030000304140e44d03001405183c041410d02e039242114824601958030f0307540d500700d41e00742e0702d1000e005441d0700506d5131080340074034403520004c1c0203039141c031040780011002000000e20503401c5020b12081400d03034501074489810000d0b82d035502c5c05402400c0191003280618107a01441e41503000e02d2255015981090590b81100d4011642001d0894941046002d41e002c56414100c070248003000724041822840165060b070b100340b142441614200014000044029140680401c0b03050804003101441050754050910004042d03031b441594070f60350038242c0912032409002154200da01404040ea01c005000c1e4040b18102504070f80d814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 783723093 1250 783721843 783721859
    0x1410170109081804020403080703030222030506130201020c190602100e0d0509130f0501091d100e01060f030f140a120e0f09280b13090302070806090d0801060306 71
    0x100b05212030022203c0d00c1a84041d5580d2a8141d03002550840045683d0755038610340180298003071440201d103c0003c4a11f4520351902c80340c05400c5c0d990003030041c0b0301c42d00c07900c010318030844500104a0443c8103030709000100d0b40f0b602103416540180070500c0e24040c1c0c03d01e43c02906222035428240011032030850242e44a090008155000d54414200503940740c89917404074120210301c802120400e4140308450300300c820181d20460490301c02e41340030410b81c5203038081410603441001d05201030307a00103942c0b07110240c083e5000c040d0720480d80d0300000c0c0b01960750409889429007640146d0311451a1000b440501c41070143d03103400e04066402070150301c03107036644441d5103448101180341000f491010441180e101c0d0f840112a0007801040740240e031410315140d05034407a03084464400c0700000c52244820425a02441080310f0004201820b0300c140090306400a10b10050250f01318402c8980000e401c2c1c1040c04034a0080b20040040c0c0b10a0031101006400210706030700603010146040d10030130841c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 783724343 1250 783723093 783723097
    0x30206011806030b09060405010f02041401082502010f150b0f0c011e150b18060304111507050c0324060f120c010818120a03141017010908 61
    0x2004080e210404144034181d20005094940009091410302e1043c0300480d00002103d13449144904e0080c811440100c0c901003d070701440c070582a5030307400140014074540c000c80c603480c1d004120402ca560780c019034490030381281420a0800300136035520812502010751900071240e04011441481901501d0840e11134028852558102001c3d08042011007170614207402084115204600e00c890094060310017800615600e00c10700154603070780f000010768401c29000e8030001200c000c0b20b040c4904080080c81003030380c0000c0088641010b5403114484d20347c1c941020029110420b0180c0c0e440301014a007070340c41c180d002848103200ba07101300c00310445802d405a50011400d03207400081080c0c0c8826004c22242013180d420325a104a800d42c1c2d80045400001d075201030b00101b66101803e98440100641e4104110310304040550410f02490507148010307002866902c44c546000154290034200e9069030b0300c41581d17000040b28014008100c107010300f50f07603004000c519a000b000f00c14060b035500305841c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 783725593 1250 783724343 783724349
    0x6180e04030c0f0303090b01030b090f01050c0306010e0a030507030f02090f0420012610090b03030406050a170c180303030906150d0203010e0303010609060c080d2d0501090c0c03020601 81
    0x382d0264601c10f03042501ca500003288095109101017002d503120b25084115400c00c4420b40c810344104400c00c4020101401018010383c290305200d0324546550004603000340101103065008480c8110000000b40100b29010080d07000f40700f901030f421030900c100144954041d000d225009548030a21000ca1200001c521059100090000b00c804409006135103001c3c50300009010b0013080c03505250000c5a050700c10b480750f0942046141c4158580c01380c034048448400400c2d03096030080c0000e01c99103010700000c03c8000c003039040c00a80c0c1c000c10301c0021810042250680d2103600081010141e0740410f00c1d108900d99000c42c0614154901003010380d90f500c40c010800e80711043d04200c83c8909071280052103c080d81c002d4000e000325072007000f815a90394000c0c03051500040b00340100150301c0744034141104010f98851000e030315000301c100310368018009a081158107504040703003215641001c060106603c5501440200c1c8962400303035408211440e1500400500c5000d030307000d20029502181c61819 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 783726843 1250 783725593 783725603
    0x3110c0d0e040908030406050a0b19090515120703030215190902130e0c03061305120d0b0406062c150c0330090109080a050309011506180e04030c 64
    0x1520075007000003006052180005001e0901c000300748010301186803c020b10412501a040c41310b102e030319050000c40c04035082d805081052101040c0030f80c080700d4101c42e8200d03025103000d450700100b010002c2c1000041d09540d001d9507000c04401c004140d01802210712045400751038214a1414140b840380202c10100c0c4003108030f80d10b01d000400c65440d40351010844c40da035001080358040d90844d00d640c7c0d4100c20130303c034070912039100001d206031182108041c2460740103024003a2842c2e80724100540c0d42004000e11402a210001040d19407501c0c440d5500070b201940d65006050b2112040c0c200d0841d903c156822800c80d10b001d68451780e200c031250260b0320021001c2c00c544d0b64020507202411400340004400101e0324110840f2405071411085c680e034110b0a900725250740d01d465003018200c41811100504150091090202140c00344010b903500c2802e4400205550802c0658480c407417156400c070101040071918013041b1f6650f01c182d034a010f0049200c140c0580e007000e460103043e1403a101c0c07000381 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 783728093 1250 783726843 783726857
    0x60c0516081e04090e010e07060c2015041401080405121606060801022107080112020f0d0b07032412020616120806040507090b1e0d050703110c0d 64
    0x2c20401c5540302d0b201c894841800641d00c0e11344500f207120103000e01d0304040510390b0030400d040c4024180401d10784121580780c2c8454003094003556400408d03202c141410f903114041440401d2054031081c1001d5444402105002d40e110700b007171000704160300c40d40311042c100600380040000147d40002d403844000c0300940107940314180514281c3c1c3d81d6009101c010422410034100042515054025003500601e480c45100b40d1014030740c3c450080f9504903000400180100010015107010342c84003510301e8001f030a03d02d9080c0141001c00c0744a41440c001326643d030b41c0001003001466143c460004c268009280d440184c44402110f40d6460155005001ca07010741215020119510300302228a0021003c800300013100c1c4605000d180007419607116000f00300e0f101d00181d000d01d494410b45d4483c25180e1100c40c0540e00b40b8414001c02c1e0002d01c1c5407420003036045408254000200094a0821120740d0082100d18243c80010143c960000241045034024032401c0c109034008204106000c00610b0403407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 783729343 1250 783728093 783728107
    0x901151802040b1b070e040b0a090807050105150109140102030322051507020606060909041101030b1c020a0503151b0d0509100608031624050112060c051608 69
    0x3009105681c002d072200c00002841d840304204903941c0d0100c059858085e0307003d240c0e80d20005e40f081802220010461403107840011040744031070f40020b00c640c2c0194140c9040c8241d95681a08483d01a1081800c007201d0b0714008400f0b60b40901c1400240120740b82d03004400030010000f070341d40e000140012a29a0981c203400c5040c0503c0403000c200c02d6085000c9400000101c580710b81030030130540e04100180606000282c0e68200103048400000700581035040c03075038540e12051121003941c80042e04250701c2d580d0078003140d6104240c2c58005440c01e403562031585500d104004800406a00c400d000b40c024148118290300951084c641c0101000c2c14030310118034901d240074451040b08407202c25240b401c410304c19070b9000065201200c8c1507a100030400203850b00c2d07038182c0c0c0b07010b01003080e20010050698500043d44001030034a540303126942509281d0030050040c030503180240c21220902071801d04110610100d0701901c010580142401441d00b09000c0c0340c0051042d00440183c03895130300003451 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 783730593 1250 783729343 783729389
    0x60d0218030d0c1406010302130218040e010e0606190e0c090402120a0c090807090902210c1302040f06050705031903021345090515090115 61
    0x10a11140003001d032068204892005440c1e4403103c1c000360360119072a2103030105100c00250040c16260014101d03281c3d0040c0400c80c074043c0d8400514005000e4890440104075211401208600e00c40503002190216880300030360702d09040107108910810110b10649120402100d0704000e0b00e80e14031464070541d8481e5000105031041c107600c0b5402610010b02c980c0d26000850174a4081ca2455005020b031070054001110b1032138150040110715000301c101040818042e611003100c1a101404d140c1050120380700c003080c030b040485104420303900568a00708161030403082d100400d01c2c1211086082c0341c01d24041e850302006900904041c00b00020703070031090007000c20075620b40c010f4400e00c5202d40d240307501006000e034211042c01c82e03480c414100c012814009190340762504011880c0f002104800e46010040e4091402d4102c1d074026002031984400350909003d03035503155004d0001054000d20307600c1d680000d00401404680341da4500f2008160743d0303103000390103002c464030b03140d8500c0c0d80340c2044d0035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 783731843 1250 783730593 783730627
    0x10b0411120c0c15010617062206090f1506050408030403020d020d0807030207060f170a15030f05070608010b04050310050a150816090b0a03120c080d0b03011505060d02 74
    0x480f03a0710480c80c0200d56207060100042c10b840341c0d541c2c3c81950031118045441c3d940e03004d5410550002e448400c04c480c20781d40030030030303038042c401d055010941b070340d41d06000400c4882d8489001404c584030f40d69601d40ca041c0c0c0305184001c080f140381140c541803420100c103481e40214000240324a01126a04080d91f1b113000f007034580030b0b03008504c466440c4140c0c5806540c656030b52265901040d01e584075114103a0042003140c1c45825868107440083d918603180b5401080c00c0b400100390601029004404106543d501c0c0d00b09500c580001c1c000c0d90300345032000d841c4140590000010710b90411003802281c03000303d1340070821080f100c400304958445001c3c01014240d003126100c3c44407400f001c00100b142001a0104d00307880d00904c4060000e89440461040c0d1b0308102c0d105400084445003000000c1014a18840c001080e00c4c26000c4140156500c400c0c9a20448542c140c10381c80e520f00c040303d03140a100311851000500b00303d86d203482c0f13018081080d0740201d050344000c0d40d03030105100c03011044046c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 783733093 1250 783731843 783731857
    0x906030c02030f040b0310170712050f070b04080105011a160c03080a030c030e011a121c0c0302152e030c060804120c050c040c020f0d020708010b0411120c 68
    0xa034640c8680d00c0c1c5c0e08010140c1c00440d0301c88070145a10350006600e182400340323803100c03003a01005840c12030305101e00c804081c0c1d0f40c450202c0d140c0c4108034200c0c680043c24000c070005400e940c950280d40c0c629240340c40c1e0949a040e0840600c08155941600203213103440100c6803030b100180140e4041560905041d540c8420a6201804441002400c13101c6c0700d505902028510007503407030400c40a090611120f088504001d01e03a1a144d8504141c0c4000b46070808c074000d022000d01c4215070b00a40031404002c002c2461040300000b040c1040c01c1c00f130170190140408801500160550756851510103007030310300440740e82040a400010080802c80d08200720b840ba002450f00141c201c10015030b40c80004041c20000c64003a941000180c406000d034a02c04c0d4101d41e0103e8101c0004d10007000c0f40000c000003884444801c0055116042ca0b0702c811300801d12010802000c107802410b41c4500e4801d146082d030b582c0c0000e0a208500d0300c0d084855910284040e50540b01f41c601c0c103000300b41e41d116009400703807150403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 783734343 1250 783733093 783733117
    0xf0c0a060f0315091e110909040219060906090b28120614091b1c020412050c030f0d050708070218010b0702101e03090203011d030c010501080c010906030c0203 70
    0x91004500c141d11600104000402114403654143c0445c140d20121940500c078801e043c80c0410000c415031a0203404140c0040c001040d04110240760460640d40752116408200410311104040100a42000608000704502c0c180c02d8540000340720f010150408071103045ca50300c075008410a00e280c2c0320780705d142812081c9003c1044042c0c1c407210302c0354041c1029244248a21241d0700000c40e543d40051a0304100c08588035041d0925250707100000041403400101482c80b942440002018803c0081d0a40da0600034006003990307441000905080280b102c090354110b0b804940c1120a407617012040f50700094010070f8554440072280700140d040402214090000980000041154512800144003130f40c8200c4000040c0c1171026410780381548048a20071441c0ca0408103020300034026005030324907a00c020000205810720001041c29000200105102540301107040c80f4190001d10619000d0000c01005003c50510200020103650702c038014101015280d690051980b80200165080c8039090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 783735593 1250 783734343 783734381
    0x120f0e0303122a0d0b13050406020a0305060402030108070611070305060f1501030506060d0b0d0203030c0c03062203051e0d09020102210d090305040e04050a02030f0c0a060f03 77
    0xda45000a840280c40114100800550300100d038044a1214007190110150340da0804e55a003002c0c1d401804001482a00403100181002460744c09100e014400c41c8200307001612120041d02c01412281300804990240d80b0400051011000001c2d100c421515689030954481c206207204a050003d00d6000810340d1080c103041c80710f1b4003805800740b8072662550240d961401180d0004405413030065840f99005841001400582a099001005181c0000d0400c41c0592002d42c0841e20315404101e51407980d40050303450b0f800d18601800040c1c0c01010000b04450320b05800000002860a51100181030200c002601368141401ea6425001440c406103070369180c000b440c074004003500444104a00602454040340701c1c2c8102d8010825002c20000c04207410044c0410400009162044040d02800741c10f0200160b00c0c0c20f11a10644204c2c401c4014000200d107501c1490300c0c1004507801c1c10040e40154003441803541380c00c0c003000c0c21036003e4540400400c62418058004200d8000160f1291400f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 783736843 1250 783735593 783735607
    0x90309030623011a221503060b0405011101090b0a24050f010e0a150207093b010e031c051305121e0a030912020309060405060306221b0804120f0e0303 66
    0x5008080c00c03900030280c003076004414800120200c40c9140500d01d49c2c04410f01c018403443d4172556800c2ea81d5030141000203003944898403507403113200c0111444001c00c0c1c0c84094040c800361412002c0800c1941c40f0f8511443d15080000080b0000040a02d460400490501403826656140114802403400c070b8071a034540341c0350320340c020340b18400741c05100030843c104682040b02507084904490b04083d00341643d080c00c0082800300d10341c4e0400000e4000550740343c03698030005900500042c1003410480e1014110a03c0c5001c4035410303200300030700003446400b403842094003081010448001c1d510040d51403035035403114a40300c10703090b08808012810213036000c00d002400d6034041d886000018001e880c016140900d008040ba070ba8880c02c8506500410180000c01032070501402940c2c00c5900148404045050240001005002c1c003921a000e19107074403204a008001c181040c058090500d405052441c181e01c4040b4040340c40e68400f41002003a0390b0b0300c50541c0c8580c182c100020030003015281e40b440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 783738093 1250 783736843 783736897
    0x270c0f08010c0f05160b0702011e0905010b030c060a2a0503031806060a05090a0f090c030b0906070c0816021c1a0f072001090309030623011a 62
    0x10740221007002064034a5121104113001e0b006039032491948041d840b01100c103a03a0340710302500300582203105642d03c2d04c90071000c41c1412444200c500f0b075095030010701d040d500d00b8601d080d14002030041c0d0081d04040440b1000c2e40300c01c01241e0244001d802c086095000e07050403481c0d080d0022004040d85c007403859506082080210041d4040c41103c09113042580e041000381e070305c4070307001c0c1c0341a58040854841000503003000216203610811001d030000303030300411101041c282c50000764200c41308a0760f11024010802c0da511241c3c0c00c17030350b0348004124514000f040a0b01c480c2504101405000022420008070101d0417808542e065002c1c02c4096104005152b042c000d92a000013181d11504110103c41012200700c07035284201c0841d152a48581c0b6414020b403540c90b0354000c1910f84524a4008070700b841024000c441c2502d00c2941c035254502d196043c4401294105a59aa495107001460401c8602100000c6054841c4210743c0382d49030851300c80c86040c0d4070a050040d8800000ca013440a4851 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 783739343 1250 783738093 783738101
    0x204090606090b0f030601060c0819020607200c041107051213050d02090c0903150115030e06060102251e0911190f140c0c0f04270c0f0801 61
    0x5007250341c24891075541901300f104c10700d800100300d50564410801005901e01c1080b51010840c003c2c5420382c640401c9900030582e5808a064120150344002c0c240004558400080b081d41c41079406141b45444085003481e84030201101128030480d00e404102d000d00c003a035022503540030783c05000ca80c100d1018040d850101d4005031030000181c1e41203e000034903030401220b507000702c80d03006040c8400c55940045901c4030703822003903ca075018846c0e030307244a5959560151040c003a01849424010200c4c02e1400141500e00703003031010610750070200174440720740d800003101c0e00f900b0344418410760388611030031302004182d003d5808001c14001c4020307980f05c03080104a040f4103680500301c050003060071000e0320454610441c0c0d0150000d118210b000e0308142d219541210b2803225604d00900100124500500355400049902c08a600700c500241c2e4a07280c925801041da540c240d509000109180101500d09040400401d40032000e8114001c104815543d0b0030b000791400e0382005015030f4490f0340e00b500134 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 783740593 1250 783739343 783739349
    0x40e130201030b030c01020c13020702060a1706121c050f040306020403140a030c0813050423150102031b0102040306020c0303010f0b040b0313050c03030406020c18010f210204090606 80
    0x40380c0740c4502500f040c200814040e0f42d951040c4c00915410700d2003002e11411120352814040859824001480181d031100001e2840800b04d0740d80346401c0031180346040ba589006484248a0f041c00b099244000c0380114043c202004001414401c0d50030010042d01c581c812000c511152403000038020003004495809801500e0040c49201c0c2e12081505807691b56000b041070140200c1d986a00b03100c0042d02c040000d10700c88000d40b500301106139492002c00d09448071314050070301c40c0e02e001901024010b1401c0240e035016a25201c5e00401c1080310300040c0d128428641d401d080c0031038516800030b403c2c0094045a0007541e000400f15502c104c040039545c0c03250001c1c0a00e4031420b80005000905040c0c600969040d15000c4007018a90744800c0484d040c00404075208840c140546400000b140d9070900c084c00042109030003500004000c00104510128203c0f0490004000c40c0014082d8460014840060318450303103603903140b40003000001039240c4060724000c0d071190400301300b80d0402050b60002012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 783741843 1250 783740593 783740597
    0x204051008010e01110f1b0a0b06040b0301050402010f0302090d051615050405060f072609010f020a121b0605150406140108070f0e06070c05030d0206010e07080408040e130201 77
    0x21101e00f44005081e0782c00003020035441c100612400da03c103000b10000b0882101e1104545025040c2e00d0300850801e604c00105481d150712201c20410a401e203400303006030004048000300318030310b059030001c0c000402030450712003010f50100d0099002e84542136000d03c0c454204044500d0200e40300019030301c016031760090300c4641040d02c0c180c1100c2800b5106407420380d28018078503070034412004011810b41e0000c1405035002201c0002c04a681140d5035140b4003991584d4400c0741c0d0b14104100094405413104203904115403008103e00b0104450003201c0150752183d20b82840540e0341401001c81340314444501034152494541880541c0c04030010b0104485000e07a002c3c030090366500000d028081007503500a0100303031000d0015403801c3c0700e4900811030990350b0030312003900001c0c040429516003100104896900e43e6900911141c6010480550646803e20080c441d96040600103100d900019207400c0610003008041810032130502c0c25500a0400152007444603c2e00030501060b212108000340c1c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 783743093 1250 783741843 783741851
    0x304020102071703070b07091716050105040f33050c010606050f190212160605010b1e21091c05030c160f02040219090806100303081003020405100801 66
    0x101d1003c450003069074110f80701d001c0e6007021403c0d1240c0040301c4000346140100004d00310003041700707400036a003801c072094240020130b07070400b103007551f80c03c001310303e8018506010092104000903144c02c2c0e4401300341c60428548a21b0201c25000000308001044401d2940c3c0015110004040c1da202003d0071107403c0540090100984d00c20082c2d500e07204004001c2144081000318045000c400c031500d04207103600784100c0c3c242503014029004a500510351505240c8410301800b0140300090140324050040c44413520314042800c004041100e00c1d00c801e02841c1c0d4404613000c2e09108111308d290041d101d101e801003101e894140c0c0001d0f110108600e424602d03001408a003040d41e40300310305a902c07900d0b508180034a00442c01540403442501e0803400c86030b4040181500340181c455002400f0035090341800c0155402d6403103c06010101144c102e02020360050080040c10b0921080b040212601030902800c140c550b02c041034455002d541019400074107280c2404102c4c50b44200c850203c0f040790300204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 783744343 1250 783743093 783743099
    0x20702040f062d0b030f091f0905100204080a240501030c0302041805061506041205010606091203021515040c0509031515100c0b0a02031e040f03120e070b030402010207 74
    0x12141c44103802150f130308071400c1c400100d20709940704d04190840c0700c5004940c140c02040603203242c6d41c3c00c0901d090041540780e8032a641040700421a54007840d140d400e0550500d4108004513903907400858000e403195104d038424000c5104401d089071003080c0707110000e210310341c0c490425003800d18552004074000c0740f80c94507417442e1401400c001c10400394000081c0200c3d44880242c405581c404001071795100e0002c02000542c1059040e08900c41e510901c00810f0003450850090b00ca01e44540c0400b6210584004140c0041ea0120350180c00d038803045004003d40d181c00044091100b580c10496400524103060b030030f08036400001502c1c0642080b0102c1d22500781c444100c4918410a6641c441c4140da25032902210b4580b50300d2410075011b00d450034140c800d00c00e0300d4502c505041550108412036002050200101c080500c1c1000e0f603451849000d61401c166541c41040800102e0207402c0007994014103103500c01e503030000841c0c951084100d80b18191a011250030550042d035040380580b042c01000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 783745593 1250 783744343 783744419
    0x201020a11030304020a0302040203070e12010e0c1c06150308070302071406131a0f070605150a0b0d052703030109050f040f030e03010209041103041a01120204020702040f06 76
    0x202c1c1304a42c041c00c0185958039507400d02001c2c2d04050004000c0c40032058442a0507201c0001040101e0640000440d4400136403140b00d085c0401c800c07030700c0d00411854a00041d00c60307414060040081e072285000079450194007540090001c950070080c60068000b03072540070701d9400078200007503c01c07094252450481c103000b004601d220b0301c003520000c0e070360741c40d400c009018400003041e20442502c41018902465003420b0b291552102800703d502d503954400380154951402c040d00031000c819642421401c1c2000450300150107003040c5200341d40d0700e0b070001800002e5250010b000072011003e840d0881da03094001c2c035440e07800034012499594505000200d551012205007805a50000b60000c003420345a203046803d01c0d120f0074100e805640800c110010b0f43ca5610410300003103c20092945c0303c1c1018034142910f80000b00a43e400c0500400040c00000c501110245a481d8103d40045c1c0d00c84d121700c0890064601e5110044a1380d00c1d000c1c00142c41c20414175101c0041030281c124494100d0700c0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 783746843 1250 783745593 783745597
    0x813030807060e01141302120705150c0f0a0c030b060f090c0a021002090a0b131208070201020f0f1b220203060109080d05090d02030a210e0a21140604030201020a1103 73
    0x1804003006c05a8100c0c0e405418002500f00000c0115420340b0b40070364460011070000030b00140444060500000e404001c81c0d4188002918646408098203140306541c503462045140750002130316140d206804540181c3d00c1003044650210040d10110161416400a15580d006464a40090f0148804c0342f0513800c130a100301d50800d0801400503040c82d040c51407810380368000141401c05070760589400308841c554150400707001841000c41607503c0c0c01a1000a08180c00a0544109a4022603641d43c01d1f06001c40d002c50800e241f007140d000e030808040001040070000c024600f5001424800080c88a003958005510903203083c2c131110b0645560304a1680d40b514840e803c1d200180301032004a0051425040848240f80010100c0ba02840306468614075101e02c00000d41d105104a0145d0702047d4020011404d0120101c80c1c5801c0185031510036002100301c1070707a0207503c600b1200c00c0802c00c240030500e549c2d85140401156580d2030b251a000c3d000358071a0060201040b03001e1000c0320800300c0042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 783748093 1250 783746843 783746851
    0xf031d06040f030303050702030c16031703040b0115050d050901060e0c0f030708131b060e0a060801030b06011e020a02011d1311040902071b06050405010503040813030807060e0114 79
    0x80c0e112843c9991001c40013070002074942c90442c081000700344100c002c01c000510040007141d1003091094558500a07030112181c0d003142e10440d03801e000700000318004410f41030459030302c2c044044401c0c071b460404031038a1281d0745551040c0b901d00303418000711200540c8044185c0c0c185400102e05503e400303483c4030b0640150392444e654201e0820018211031f2182d00800d402000321410f9400110003035580040496020884541090305c0c2041005225409128076030a0700d416254901454200040105112030501000c1c08030b16402010a41c42e9206902c1010030502c80007801c802c1029010000f903c400800b00306900013503120103604a0301200700004046400004c01444d80211400c50140c090410314202c00718001c0148000500e00e0020b00041070000d2040300200c48402c0b24401c1c00c4844042604003c042110a020601050340c10104076a0040c1c0c11840968a03124040c10500ba0b9021582005120f0f6002040200412189400c080122a02e0500134007034906107150000c07035008222 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 783749343 1250 783748093 783748109
    0x140303040b0a0e1507050d1a030a020108041502131404060f120609141608030306030307020108090304050315040b132f0405010605070b0c0a0c0206030705070f031d0604 74
    0x8012400c59030307056001c1c0896500543c1a0303107081041c108103090900c0100c0d40c050100704005074000041005100e0520b404801c85880a0050a41e0300480d650301d4150074000d051008800c00f04007489268a550940c00d040d05505560310424090000600100303445042e02c0c48164007013149240c90180565010348000119004d070b41d904e02042c950007031604040a403016940ca60351030001c11104e0b00c030801000009002406181102d00c44802c1000040c1c1c4400f400d40c00038428825243c0c0e002c01101c07806034091800c80c415849040d511804c500c42c0b0341c0031b43e40c0b510a000c1038500c1c06004542403881140100e2503591036943d8800340d1084240060b10080c200030b40c2140100b00c18400c0320036404103035071041e05003100e407603080042000c4420a0b0421004200040303482030030469880c15581c0d000074458410ba04001000002608030101d850000348602008400280d40e948510261100c0e143c01c00e0600442c00b00e50301740603001081c40d03a1400401c08661600800608040040701c0480c0c0d011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 783750593 1250 783749343 783749363
    0x902090406090f0b0906100e1b09030721060509030a08010317070f080910090b09040c0c080315030601091406040e070e011508010f2702041703030414030304 69
    0x103a81d0040107040041007110310310b00e400320600115041e03c0126100d2007990340107080c0760502031200e5441d031039590702c090140e0000310200481034810344441c051031016000c0c16502d031922600024100f01380344c0c1200449000d0184072111810203110004c003102d0041034208410b4507208045c1d6280e10650030041c5c04103004c071004000240b400c21021908103880c0030a00d08020182d0f560310188000c4100c15122144045100c20301840e10300340c0d00d4551111030400c00003641c509400d0791998000c1080f1580f1440c1d40b101d015903d10f02070140802c06940c0101d002e0794901e40403038a0301c0d032008c0da03a18150080c03080c0c5001040e0191f461241308035030010602010441c0d0b6443c0c0800000d40419084006a40282c100000e003400d0f450400501a080d184074449032a8010b250080101605a1240355160358504e01080000881991141240b0903102000d941107000800600030784907560110386420012aa400d080807808400780d80140c1c4181040d0301405c513001c00e0640d40780801c0e034000d0808100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 783751843 1250 783750593 783750601
    0x90e240717070f2015150a0807031a041212060f060203070501060911093a0308070903020a0302091b130603060807030c15120c030b0306060907140a050702040c0c02090109090209 78
    0xf1154516906c8030103002040341d181102c1000c91f4000d01698054646507111103401e000300540c01240e40400d0750010188080d40ca01074581700e00b42542d500c5a0014403120030b80320b9101920903003000e0b0280194440d000e010315500e201c007d41da035002140aa88952a103080454030686071f0280f2002070a4004465092011081c100184180706e2000200c2c55480451550007070301c2c0c8240e810782c58010131b0005060031052400d01038002c05005007903804006c8020740610059450000c0501900c2c0c054405000c296200a0112811015458a80031280e07020500c4403071443c1d000b0501c42070381e0f2035607070034020607a07100c40056aa20080c0001072213040c002070103020310079003804681c10361700305841c1c22458120341d015900212860403480d6030000340c81c0e00004189060402515801c0a0103581c0d102c0302d80782c0414000c101864844448002e10780005221009a20507010340e00c849030010b004201410070294043d10403100e08400b01d0044041400020700880244541c4200e40d4009e46030600780d80d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 783753093 1250 783751843 783751873
    0x6260609030a0e01020a1202010501030c0902070b07030f180b090f0c0616020102070b040b070204050610081f05122407090b0a050d15090e240717070f20 67
    0x443c0110704600c2440546000b1072503024075030a50303024a13000000d0550450600342d07540081500700c082c2582c0100300030400103203048a80c41c0d012005250002d80f42d07000a101102402c40b1400004c0c0c0c5d145c2d481c1c9074070280516511414000c04103541150300d0000e480b0f0f1890388500508820607804442400b400c0c000303800000d0400080391052050300c14480e150109040306030015000300d82102c80100e4200110b00342885695000001210a4400d82d4001200200004c400030114000c41400081608491210032042d030003529005140c0c0b0000007402d880380d42c0d500c0c066010b0a007002100eaa092103011601c0b1085801444076070f9074070403450304110700c0c2c0469a000580c0b0808010081003900700c040828441c4901000d0745440203a001450030710341d00140c560740c007440f9150390010106102d070700c9200900440d00a11072011b0002c40d50350818160394480c1002640340d041c041110401c03042c40d50003c1c4000030310101c2d0b2920249020f80010720100c1419803448124154808500d00e03c1c404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 783754343 1250 783753093 783753107
    0xa020109120302120c07151d0114130e0603010f0e030304320c040609020a120908120906070f020706080109051306020c030a020c06070f0b0a0f06260609030a 69
    0x42c00b030700454030211407040b000080703503103d441c01d521503400c0390809000b0010a008681010016031500c18034000700788000003a100041040c1078140603052800e5030f401020034040c3d82d404020040b031030311000d0f40d40d408002c00c01c0c0211031040c400e51900b0110400c4001d5842030303940341c1c3c0b00240154150764903540e4412060b0401c070b840b075240b01241c1e490002d00100d06400440440350042c00341c0564001d00f802d000603580e264014440080c014040d502c0d00c250321806820201d411000d011039030200c182013064803480744e0070b070b8102c400c0650740410502e840001804d600912640d0307070706680280700e107400300e827606030900901c800078824800400c200c21054000e2a081410746a401d49043e50700c0c1c0e1814120380c08510300340019000070441c542d1094052020203141c0c0c200756031a0341303400705550703424200f01420f040c014010f070040c20200b0f0f01e00c080365021034004501d1000400a1030740b90248441c0e00241085103a4000c0c941c2c4600454401c03010985902074920700005504010350013030b06603855 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 783755593 1250 783754343 783754379
    0x314060a140915030604080703030e071505070311060c040810050417070201021c080114060414121014010e0c070b060906130f2007030801092a0f0e030a020109 70
    0xa00310401c8643e50310342d0140407403800b86209080300d590300e803c42d14002e41070310b940e40034110341a0881101004a814454600c0c10034445520301241c0c1ca0965140a0760341c1d8503a95041111841054100603640c0000c5000300b0a5600e41c10441e42c044540080190a0b1542101c00822911203111001c554002c90b0020b4108a841401aa0000303d60700f904071030304110a4080b080007590300c81c0100245644c4000c503008012090710309500e01400c042e0300200790480004042c1c00780c1041da4070741c4006403042c0902801c0c0c0725048020301c00c1114104404140002c00e015072082441e2800200e0005e4000c001100c01da0359219941c40e00a0761aa001c200440c1e400901c55a00881c0e103444a0408070302510409400202e8190002500103505880d02c040381c2c41300002405524041044201007508994030070b04481c0c0b40040490000c0318a8110703028110000f01e1b1444101082c0c400c0442c0980003082c1c0303a100041ca954400003c24510f0406903241280703d0047d0110341c44500901441c920000002c0c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 783756843 1250 783755593 783755611
    0xf0e1b0f0412050105060a0609120f0809030f03070318030b150616050f070515030c1e07080c0c0603060d0308090a0b0907080c0619030f0e0d0314060a1409 68
    0x14650380ba0300e00707560111400c000301c03110395442040007464504400c2d010060f056502d0007884007030034520001d14490345243c0c082c0140b01a00c034003408000345201280e4010030301900341c0c0d12800302400401d942ea00011011400f007600800311484d42d03180c09150383d088030b03002010700419417a800070a0410b5400d00c0d1a140d040242042410303403a005039175070101045d00c43e1005041550300303841c0030f600300a5150080c0344502d4050404800b03030400a000c2d242c01ca0748550700b55a81b0a02414035100300350b80307403081c0042e025001c162034003803010f848003600c04004554151007122400108102c503500c022188203130b0150b4106246404288901403d50340a0b03401c104552503807655846000380c554046400c0d9000c0d501c006004e01058800340030803040b074102581c2c0d403424101c0682c29100c1070b03444440e00c0c10406039961403800300d0110981000f910781181a06550b02c010724890000e000e494891400005400da41d0081070241c24200d0814046403088118491060490400c12503820401303890210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 783758093 1250 783756843 783756847
    0x221e1b14281a1c0506010f080a06030c0b070605061906030903051201141008100510020c0a08030a0e030703020a0e1305030c100c0e03072108030f010f0e1b0f 69
    0x180c124005920000e00300000804180c8680303c420b6800104081d00d401402018240700901800740d802018001648682d400d26100380e90300c0c2e5a6550088c019a031002e0100b81c041c41c4001041c0301c03200d00500405008003c1840b0035612070040c00b601c110900a155401c9a004170f04108d240c0c481c1e0b005440d1035102c0d00d003042c500b00c142d10722041c0c4e02c003080e040100200803071308401c1650f1522190a101c866420301345000e0340e29180e49890302c90701417889014018003002c1e5640000a2003803045100c4910000c0007200c4640d02c1e011541d5481c1c1081c441040400d54506d2030701454580021680200c90703000700010641c40c14075003280401e20000d450781c040c000b034584802c00015028006402824032060003840307d860403010480649541800c28010300002c00c0d0342080070744000c209502a9254040e5200340640b600c420307004141441e400203000070201006000056600380410390480f03610b5080c10f50103076221610b10141c040107407030002060351440c40881e800345100c0302900d06072419415240c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 783759343 1250 783758093 783758099
    0xe0a031d040222300317100e010815010b0f19080604050f01031208060f0402120f010609080706110304050a03050102070b0a05221e1b1428 61
    0x1a0503604440f07402c00b408000c03940004450041050403070028081e4941d030341103102018040b411100d48584031a15603e40110000050600400c410300c3c00d5030000d400c40b0911b1810001449050710715000303503404004803c0000a041c0000911044003079560b210803402079107010040400ca912260361808032250030300a400f140441000500302c00210303605c8508451610108100840300700820b4081c0401400f001070010070900301104882ca801d50402c802c50b615940d0000d10400e81c1510690307070050000828014119500000358001e0140103071030005a6258007056980f02d15070b0082c03041c070b50300403182009401e204100065000c2800002e80f840d06486d1004a880b0810640040e9056900003404108008613030181c40c0d803018283e441040b803820000303070340c0700d854038484142c4440c40703100341100f414020045101d0280030703c40180740e0510001d0346049070b90344c01e003c0d2901c0313000098035900141044144900b50005100102880c0c070a001150b40300c8903c2c0010b10803d520400d4020001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 783760593 1250 783759343 783759349
    0x40b0f031b03070c1506060e01050a210204060306170a1b090c170619051302040e07020105011706090a0b0403030f2901020f030f070f080d0f0f0e0a031d 67
    0x6500562160340d4540d0203c1301418100c02e07024001c950700c0405460540300b001415400441c800120f4024a40355941d150222000c45400910381030010b140f40003000e401e00b40440300e900070801c0b241980c405000d00c542e203800a10340120381e100c7c48051038004c151f50b90001204460000c00740f00c03102035003400542d1203000c0c038000c481c060054600800e03d2000020318a919070004a1340c00f4504032041c901009100e030f09040c8000b100d100384d070300810901c40400160500cae07030150f0713020b4048038030602110f20b4030000083c0038246c2841990340d450140c051a40c0e0200c00420100e10030142400104403ca0701540c501e907201500030429410195150076001c81c0020901403001d0b00c4407480c1288035900080c942c210000280b59040c9030641d40080d07540811401b0200c10344410081e2000c51030344a03d90760a210040e1030f4449001060b8120006000c0c800f080c03030303500190400380600020030442d010342c3c3c2c840c0100c070341d115041c000d16804240d8030310009118041135801808032640081000300c00c20b000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 783761843 1250 783760593 783760597
    0x81e011e0b0a0314070f080a0218090a06330b071211010e0a12050a09120507171006090507080f0403020f0f0c1008070903080a090b0d050402030d0203040b0f031b 71
    0x1340031864000d0f0300208080e03004290400007601d03194000c4c05107400150b001036100311341100800d6200c9503580c00627417601420300c800240503400103401e11240181c0008030032541900b0711449006c0aa0707443c0042007e4541c50618103941c0702c0700009141034140d88851100c41e01c0002d005003002001740500c80519800e0107540c1404051100400100c50545407004221600500010411505202c1800d03038035800303520b40c0102d44140085091200d010304045003841ea068211030b010085225082104400c001a0007081858a04c01000b032141c030b904452051702c0f015544a4000341c0c014000c43c44409072810b88503040782c0b03c0c1c01111158030240c4003440c00c0284000c01d04a42d03402c4090101202d08144036170f40c1c00902ca5150941ca24900780310054411300e01c500001d045240c001c100301903032038041d007454400b074400e4000c0e00ba120240110b40501911048804a010303014030302c22010760300d00000a17a8113070b03002684030f030f070400c0500e155024003a0401000c040183d034144c00408010700301180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 783763093 1250 783761843 783761873
    0x30a022109010506030309030a020f0607020a15020601050604030c0e0712052e0e0c0c0a1703090f1b0609040f06080610080a0b07030c110106081e011e0b0a03 69
    0x40004041c509866000d0031100014102c5019070000c201e1044180d9010030180c81d0f13181e040707a007403800e0041c1402003451070065000007500900f4102d00400e401008d20050a81c1da8034660846003540e8030340e0140206400b80c0d01c00100f0121806000340301c003c1c015440e059102210b07142040c0c11074000081c41c410b5035400c1e5103983d0811a5000c20500d0120b024623990910a15522680d4849103011208070002100030801604018040b6804018860503c040f8401c070360804507424011841c141c44d100c040d0f2069501141c103101d44400491800c00c0030030b00e0000300c01d05070035110200c3d54074010320050340d01c05164154480d903207011a82c842c1d11148100000740c1101030051100d0b20381a448400c10240b60b4100010aa1004034450001046008003680c4031516141c0400c0741d00721990f043d80c0a01c09600c000d0003a5081c14004601e0140000320800e60001d40c10f0804200302c98000e501f82220078001820711003491244c480080d600f810f802004207004082e05441400f5925100c00c60204d403000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 783764343 1250 783763093 783763147
    0x6020c06030a180f0803060f040e03030612120c074712040b0106171003060f020702030d11071703040909020604030b07120c17040f02040615090e0a0e12030a02 70
    0x120078401281041e0a80c004023420941b42009481d10459607203036640002061240b1582400d00d031221010800d0069041c000082c1e001c0039280c491500f0b00702d032280c80300e0007902c4800d0307203144150780fa4441d0181144604a01c604118109007108074003012550071b0207030752000c024410810342c2b00c5030000f40f504500c1207010791568041941400002004900d095401c1c1e03c150b803003a014042d06002c101080d508407135110b500010714a00795440080079020700303000a549401071708910380502c1d0300f0a0f90600040500000d54898036100c03040c414a46d030b08a84c0c4074545900502060052400c00e41c00090040d000401040c00d00e582d95036030004012080f01c0403c001041c1d40102c1e12581201d0017002460011070919241c58440d03800d0003000080c0c0140040c05d00101c044015055450f5913100b01d01420070055403032000c041020001d014111184030749810394449600040100d00c0751301c904804644c608011b04803080c903100c0110850341015002441d203581c2000381c0a2019601140a118900d0710303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 783765593 1250 783764343 783764347
    0x31b0f09050d0602090301200a12140906070807030213060509040207080313050d0e0f130b100c020a05040b030d0c061118030f011406060a0c1502070c06020c06030a180f08 75
    0x5c00030300d0309440740702588030a102c2442000100c82c1c90301006943e900e92042c42c2c842c0310245001a050094905d0200110003040542c051100302d10011803000d1041181d0303201ca00d0207445424080f01284613840c6201c2c10000b8401051082d64468001020380d41c20052016042443d903458000c41a4000d846200f000640b4a40800c20041c003400481300036202030500f1801d0540d64004502c042a40e040c5082c4180f10005014440d0906648002486480901050441c00c03820001515102c038000c0241d10441c85035100049500d014042e2020700c480260280006d403100000503200e00b581400c040f14403e4448802000715507480015280300c104441240c807090101c2c41c189400c002e094818603856906101c01c003176404520f070588070f402070016151a5682c02070002c0456814480c070f4001404c0a81c0c0c81e40d211400f00345900940300c0c00780a002c04e6540242e039000280d96030084002c0c0d0540000d014000180d003503960740d021403c080c0410f003808a003400655140d03182074103014011141d080e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 783766843 1250 783765593 783765607
    0x7050f01061413020a08130525140f030703060c021c050d05010b0a0c03050c03130f150f0c060f0e060f0a052a0702030a080d0c0e01031b0f09050d0602 66
    0x101100c420f41140052004510b842c034503500041207000024580720404201d09060382c10003008005680a1842c3c0040c951380507000d030404181e4848140c072644032075070315005180c031303461400b40d2203d80490317402401082c13801d00d95560300b0050200701c2d500c041540070f103001d40c40e4402c002056022540c100740d515a9900c00c2540c0507041280e01c11f03002201501da0512070700395825000100e249407142c150500d03d4507660402502e62031845a9039103808000380c010b42c001081840501001c0940d20b1519501d400c81c084080220340e0351005000841c0011904001100803641552104400c0b20500c07501003954496956071074035040051f43c142040d10403560400603601080c1c400c454204100765400032521050300c0c803001003030034060b940140c0c01e54001220300840da8100b00d4180c1440c0c1c40741e407250300d03200080b5888004159851114003c02c80010b45d24070300f90b20034800c2b60000c01136503a20210106090000b00c5160031201106003e11403610f0700030405a07203220341724101c2c0b403280300c0150341c2e406 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 783768093 1250 783766843 783766849
    0x50706030f1a010e0f040608071212030b0604091505120d1106070f030e0304050301061206060605040e0109020903010e030c10060b0313120207030f080301050315040b0c07050f010614 80
    0xb05200580e1072100c05003100102c0d90f07a0042441e011180100c5682651802090004009002d594000152031083e14000505800c81000c8000303100c0c01185051114090101c080c0c060b10585004580c0c031440401007444035140ca684010040000105201038040e10b410209500201d4055607190b103921140b42c01134401e900c201e9900242c014403025040a09100202904001030840030405240e15403403000c401d40420019200180fa0060003440030fa03690f0840c002a001c42c1010544049050802c04030350300d806102107a0807102c101d489808580e2901621500a40210000d00d42c15529078241e000c1c0c8400810203484241c080b08003516507110680d00031011286203600c144038102080c002c07c010b00036441054000d668200b4003240483d507503104200d00305142d98000410380c0040500d01c209100f8201c020754142c8005600312031a00403034041010341100e0444000700042010b03030004d44000500c0303024044d09441801180c1400f08581401800d41d02c9a8000c9403a011102140c0f840d945 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 783769343 1250 783768093 783768101
    0x7050c07091118040903020c0618040627020f0313110904060204050f0d0b060918070303020d120b030a06151805090c0111100506011e09061101060b07021c050706030f 73
    0x8002c9034100031500103680d01035105d008c0c051000e841650080780341e900c43c2d4426602c2e2440e190b00200100503168440204000c0a4039445000c00b080e02d585600e1180301c081d9100b103a00040d945580c05045585400d03042d1140c1041e01e0084601c090030302150300c000e40321146024080e912610015803650b040a0030301484071202090b40303102c1e140890603500843c20781c0700ca00347c1103041901c03030450b2940c895100200004012018006034400d41070000140759000c1510b0741c04880c10b07522a51407000740072440c025110802146070303154001c0015880003a0135a8003405121001180f6600060340c3c40d0400010520758640069025071104104580c3c0b90f4140243e101042e800d09101c1c10721707092040c03020780da40342c40d403a0900350542d01c00c007141242e070190384e6400040340081e00755003620703020080041c0303c222607100e6000130400c1e00d550049072035410701610302640c46503180a070500c07405400700904074001c8600e1252016a0380c9200300810300a00c0020040c20b81500c002c0780070710070384109504036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 783770593 1250 783769343 783769387
    0x90203150103240b030408090a03060b1906121508100e0601060201050f0a020906120703201e0d06080f0601030309120b06040207060e19110901030b07050c070911 71
    0x1070202003c000c8500c040d00641d21094995610905440b5960f0b031030120842c0c8038039801180d0020b8a51000000c1001135041041403180c15944c071072591068401c0c120104650b4003c0e04080b450b4407075529091819a40008800000060f441e528150783c3c40c01142801048860304415940b01c0074000302102c01040b07820b00500c810b10003041580392200c40c03960720f01806018840d8550700014034a070ba5641d00401e403003140c551810542441d040c1040301900400080100520a415440540b10406228001d440000b10495000c0d82544281078008003590710084403140c0040c0c0d50f40001c24080020417072521500c1c80c507001404554114100a0001201e0b0b50000180d003e0843c420000184000c0a05402c96800e0b174015850709424540030024041030b101040c014800d14400c00c0c0d035800040c040c0715441e070284c01a244520004410700000351001d0001a2121081d035000c80c4419105c3c0e00103004600318074007503400040c1c407071980c0803d44444213080c50810002040e00b14604054070303603800030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 783771843 1250 783770593 783770621
    0x603080711032b17010f05010c03030f110c1504030806130e06011511010b061204060906051f06030e060403180b0c03030f0c09150d090203031c110a0e1009090203150103 74
    0x5a580f400245a11074000c85c0207c0f03041100300a503841c01c00d4040c0d0403c9404a5180000f48945000c0c01e04001d0360782c04c02c1c001843c0500c00d9190f901d1010084c4110301d0301968045d80e45403619543c64080c058105d18445000808540c1d520609982040a01085028220444071304020703c2c400d6000400740083e00418502c103901d400740300c2c02680c0d550401c81d001440d2404103100250b480e81405002070944c85c01c0548840d080004101002d8206044040c40c4001c3e048030710340d16500c80c1d01c00c078100c560940d605040d039030006020401003405040b00b003144e81400880c80210548545a0035525040115481d0080d40f000c0240048031242070304603a0b01c074074001070b103900b0603030550001513075104494040c00c654840002e020a140300646c2001c5605034000d03080343c0d1380d42c040c070302c3c4100c0000c8c03682c08a141d402e140908101040e410141120341081c110f036903844100050200700220392070013140c440140051500005140036950000e140b2a2110b05621207100102c100050140c4d0008010803c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 783773093 1250 783771843 783771887
    0xc13050a062f0f0c12150406020325080405150609070e131a1c020303071202010228020c122a030f0318040603080711032b 54
    0x5241d800104951a0195690100c100b80d003a051000c440c10700303000c08011030740500d503040c1e05000070008106407055025a185e000c26215152074640307841c0b0f007107040da0b0304800d083c0105010454a8021b950403c4007078403050301c11141c10300e0340d1100c6e0004a11010218200070100010302609005080b61402c20b00c59104040c941a0000740400100400400034080300d8441e0001d192a40800c2c0f5480415000f010000154070941d00c41d01180d640da02c2520680c41280f40c00060300303180c141c1034400c80c1d02400540c107240301d40e03035446042040c03ca09a000c646d03090051010392a44001c040310010008440160050740c400303030081c10910101d14050240700310250cd224900000144402040c04d2010300003021505403845150a544504c00982c2c103202d401c2c0e81d0b940c15500440100a00b60381020f01800340c907600000e000c00e6030740328400a4007080302401020040307460300c1e041100064000b0180d07040d00d202403104804c2c0072030141511980c140e489036203084442e004600c17102201ca201040031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 783774343 1250 783773093 783773099
    0x18040513050705040c120f061505070b0615040509070512270c0a140d080301031208090a021003090809031005180105060a06181502062706151203030c13050a 69
    0x5005a06a85150035104c7d5407144400065481507110202401c000e52581d0314001c45e07824014129005440161503030300c07010010403201c2c905200185500c040318000c00b4201440c100402c0740b180e40080048080c40003c004100d80c084071007940070f20410040380c1810401003079124161108003110000480e60740a150300310419500e15821000b150300f150108000d2400b401d001c1070b80718000342c100400441d4088008020003000c07a030612440c003225590101e4175590489003580d11884980c020b034026201061b54086a40b01e41c0003040558094041e01e403a103a401c03000300b803504042c2c4407103e44003a41e0300e0600c804228241700d0843c900c00d400000340110b00f464400141070303003040d00ca038200303101501031a6000c020b142643d0300010030f240382c4900c0d0b07550598400a526520300b01d800e81c42e10850540144040140342207501d164411007030081100303940d103080707000f100040d018005038040d03000811804002c80400c001e603c13071201001516210103005000d034202c0c0c2c44c0d90f0130035482200481030034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 783775593 1250 783774343 783774347
    0xe010b0702091503030f190f1707050d0e03070f030f0309110d020414090a0c0906061b08040f032f0d060f022811030a02070303030218040513050705040c 67
    0x50398003d003140c190200240c0140f000a4038601c12030780260316004001c545a901c0311541c49500c1405200f50700ca4142041c075480c000c0324200e0302a82004200b91080000c11a0700c0d2003080540007080045038009802c10301100c0035131854021800413500500c1c03202c902070405900101002c0b003650305080030b0005039100c0c6c0c0e400300c1100c4070741c140501075104a0000400e40d91582c120b00c202614010404840b8104000650788600b0b441005650799243c0303620009544203140b0410381290708681d92a0819051812201c401d44070081040c0c038403e00a00000c151071210f175178050021481452281059944c0002510305807100c00500140100c03400442e482e1900d41d84d000e1aa00381d030050000604901107240d50009000e40d010107a014107501c0e0340d01e1030380c00380f0000c0c00c0b541150326151212200f8501c044190350b8420ba00881d00160046001000043d000ba006000d40301c203441484503822600501080c01c4400494503e02c003560084500300034000103109040241006540c2440340418039280 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 783776843 1250 783775593 783775609
    0x11040e1b13090f02070b0103080703140304080d0e070f09020a120e0c1c0b13020f03212b1b020703080405061c1407021006030c0510090e0406060e010b0702 68
    0x20b00410342d407070f403900c5000c2e00042d604642c036299000b2030050182d41c44e82005c0b030081e00300d070b041100443c404c81c0d0841c684140101c1601c0c8610f44c1f006520b440d21a500c04448054103907020707a06010302c45e91501103400c2c100031350700901600415000607280c80240900404110401f060480094906149400e2050000c603249005a40642ea00b2020310490110003070094800d0902400e072044070400e0007044410782002400072402100e06060b158401d42c20507071141d21008010121a14041116100d000710101416010034818070b10b01502515103101c04e41c40e03042101c82c1107000d5a4111603020342c0b901c031203815100c18162004001c4a4110350f10180e1910807809194403440c40490400a2082c40c2000b103401c84000000c14441200001c2d09400060000d64501d005402280040181100148030703910072a034000585001d40740c43c1906110000700ca2094050420648442c0800c8951481041320701a47c0320f854000b03138172803401c550586c4000b07068004510300d84040100c10050399074444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 783778093 1250 783776843 783776849
    0x60a0b09033c010606030c051603120e06130203240f06120d03090606080d1707051201060215011a07200d080903010507020f0d1211040e1b13 62
    0x8444900210042c4003103030542075540403500451014541003140041904440c0498000791000d00c05143c4c1203605a0b100d004040c8080301101c168041400468414500d9025146180000160a94580008a040101c100c4000d40020011b082c0e40003141400c00c00ca404a0f401704980d0101012100100b0070400c0b030140030300c000000c0c0e04021400e03907a960049444281d40710344c1224030301080484080d001d00060f110035514649440d50000380b190001c10f080f0b800e800e155480164054100c0b040301f44c0d1040140c508010840240700b104241420b036520140a03000c036400820b03994008040706040d40d0700580190382d00c207656080340920044e6000555181d41c1d40100c0c03d07515000050100150300704906001c42c1e0003680c1184038001e10102000030089400294002e00c400d03500c1e100243e1b03980c1c0b24404120f03001d6020380001d03003196100d148811000d0b0308045020507140800c00348070400350072580103280004048070500c00000c3d0f024800c025502d050040d500c0c28480c2c2440380651080d0184 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 783779343 1250 783778093 783778123
    0xc05031b130c020c0d1110051804051306050c04090e0d320d0b0f09070e1516060c111c1d030109141216023303060a0b0903 54
    0x40c0e02c000300f40207016071002c0d040c001d44a1003011070181080004002c56190890244107030501d00c1c180c291280c8100d50100002030001510214202c007480002e20004000c42c5400124016010000d62503000b22400707000036505150701c45080145108c100c65481d80a40c240d648040c00100c3c86641181c00380f9100ca82c400c11444100d03041d00e2041c8404026007000ca035844000140700c04502840e54000880c0c41c206403800070080144800388001002c0958842020a40c02d244e40032030ba03d0814603040c000a11040c0c49814051401c1141d140d10000150440c4c00c1500ca1102a400c00d610030000307424264584020f15100e400c03942c0b026410301c0e178071494004100316034001c8448242d5070b0b61402c040b15000740c000c20406005003080da01424408160034130502074404842c5c1040510019180c43c9031601001d84066029582041070749003a0120035150747c50358441200d443c80414805070001703c000074506a40345010001c022080c01d031038129240c44c4800303106c40c2e81707162030004400300b0000c465 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 783780593 1250 783779343 783779351
    0xf03090f120201030c17240d0b0a051b070606140d11090903161406070f090506161505160207030302030906130f030812060105090609040506060409090c05031b13 71
    0x4407806c40c0e01c00e03800541c546c00269040e0a0004240300c03240b20454407400d038500340c02c40f00005030400c008413001b1100070307100803a2030740850082c01040c0d00030340d0040342c52150b45101310810a5015102e802c108410346c1d03000d650310710400c903008800c1051929001c08599240381010280d445049040c150824503014021480c00242074030700030400c42ea00000201c600103c40f15041c40c2945103214954056503c03806400d01013141c181c002c80300c481d18002652220402c0c0c80c1000c0c18014160028078240142d41c0340807140c04040390001c072005881c98000080401c161070007003100501e140b0114044802c650002d04c08102084e404420380301c2c40340044440646c3d4021080d00c9082440c05900190fa090b00003280000410813210010540c0405000079405507513500c0006403440d016000080360030210030040c40308540b405a0025620001c02005641001d03142c3c0b0f80d06044075281942100c03403510901d001c2c0030320301e02000046010740f030803140d4031070700a51900412050001803c2c3d4000036525 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 783781843 1250 783780593 783780611
    0xb010c030e0a180915020a08071412070206041a01051c050703230607021f0e011b030c0305090321130209070e18040503031801020c07030f03090f12020103 68
    0x36070b0499000034401210a00040e07107080c8401c400a00c0d00e441c0480b0310050246260510441a0099880002c0c80340c0b9142040c0d5950030301951130082c014203808986004006440c0041100503030f1502034540b40e0b00400b03052410346000300c0c164000410203405036900c00010032040c2e403a60420a12844494203000f4900c0c80c03440c00d180b81c4240c07600001d0181c1d2803070513402030740030540e4005901034000d90201e07811030f16600c6090380c40c0c00d01400a06012007600001d120070a0a5400c00040d1100110000038042c500215000507008401c6880001030f864580e1405010380c1401550781000385500174516052284180441c201c400099000e40d050381c04000408407080d4545e0406059005003403400f983c0f034590002041a07081c2d00350b0310301c12000c117807080603107401c1440c0c09803180c0d910000461454a0b01c00801c1d00380441e03850000c88540d002c01c084034490300140802c1c1d004501ca001402c00600b01d038036010b4501040382e088144070b24a504001c120b0503881c4110b003840e203030b020300b000103000341c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 783783093 1250 783781843 783781849
    0x18012c16080714130c05030403080114092205070602070f0b030105030c0d02010c050304060e040c0e09150a030c180e030c0c040908040905090601080f01150504270803010e01090b010c030e 82
    0x850044d2014035249045125080150071400451046100740e075030030351036070301d8000000400c01c0d00305200307401c00c01207c00100c00c09104a03000c010001010b1005031103a85035551546415040d800250068001910800141d5a48901c9401030100030034010f083d58100008039980e0b610001c45540308182c02c400034025640290340344080d103900041543c1c0c2d5030f0f0b00c030348025089402b170001e1940035601d41001510105c0c4228580e4035a00c100503c480d90743c0d00c540e0a0224000c10030b5062076131003050048004005414421142c00605540d034109a480e50b419412404545c0044c0b0582001d4004112080090b80702040100079440d00b240c0008031880a42000075860141e9004036504a20305010b2051311000012614106d407250411200c5959004104600380c0e0241030402c000d8001c02c07001480145420f402c242c030070352201183c14000c940c07020040c8800925020082d5242e210020040c40401e200700700c11030252411070014000200803a000904040c9401005420001001c000307620f59070f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 783784343 1250 783783093 783783109
    0x10c17061503010f180507170a021303050c030601061806050a030f0504050a021509061605190309030b060603010b07120c06111c0e030318012c16080714 67
    0x20306421001a1650b03140d098030000d0044e07501031711041c0084240d00c2c0f61040900c1c01440c1c41101165190545002e101000c00301e118005030641900c00d03005d12004030201940c4080300011341c0200020004009090145410f250040e00054100320000240a81c000080721303150040382c0c881e29120b9612003280380c08600820210210b00d11960425040c0014014001894080381d8000c072809a030103d80b00c0e10218141c85102d140940100c010300128406101500c100340d40c280c081c40c10f07900d000604500b84000861000c1044010461120003401030020b1a80c01c030741e0103c02912002d1071541000c0001c0348502a802c001408a25105082c4001511901207405c01329070040080c8031042d210110307658207070480300b40f00480c00084042045200c0850148a0442d21850051465901c80b8400c001c3c1c200c5960341c0a520707a640fa080821915200000c0d0140040c0d074134040d2980080200301d825090203080d843c4c20080100c00d010034005480c02003507004c21121402002c031124030030358021400b0340d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 783785593 1250 783784343 783784369
    0x60303140319090809030607170c0a0905150301030b010b0a02031611032a0402030c09010c051e0c010306050103053102031606090f08030301090203041a090c03060603010c1706 77
    0x201d00f082c01500030065014081c100380e1004a003503600c82d55464104503000e82102160703a8480c0c26500200d41c02e805140c0c0103186c140c1e02c038648004000d13103940200e100c0501244030381840d110000010800e20400e080028050684808801c0c034058640310300030350701e005404400004484910654040080100d65445901c401809448091400ca0729095100c80fa211200059050707440030380c12540342a20890f8820901d40490305d081000e0400112860111414100d0b0301e4814491702e42d01d0505107030303030b00b900104090340140055040c0c080010180d0303056610441c14942030605006021a03070890110507161003e800c00b8003800c0c80c01c1d0119600c2c1204034040d405006401001c0500402e90807000240d69460300c5281085a0b1100c0c0ba080190043c8524000382e0003d0005000c500401d030000c641250190000c140001d420090904880100390791924081d4031590700c0003201d080c00d010a030340c4154114020400c101c2da810002d8004580041210810071100780041c1150380d50306071100c11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 783786843 1250 783785593 783785641
    0x40807150f0c083106052a09031501050112111e07020307050d020607150605040c21051303081e0414060c1309050a0605040218010905040603031403 65
    0x100401c0c00c0003d454690300b40d50000202400c0d0380403003294034242d40070b990040b030540d14212807145507440340d20080030080d181036400b061001c0c56052418156241103441107072148910768844000c0205881c010b0183c051480007906c4a00401031a0303001003004d072020400582c08101508850035101003441140081244e41e00343e502c00491030701e0508040c00c0b04a1082c0d08a44040d92140b00b0801c0c125891500258000740401c030039000600408003469180c40a0007000c10861b84410000c0c080e600b01c514205d000824058284941007040105024551582c260801c85400c00703c0c0ba6850741040300d00054184040d070400301d42e014038181c010016182210490820b07a003031500d0208018100c0071055034491280c2030105450011030001c8038070f401c0c6a0600355000c2803800e88100c019041c010b290f420728aa8400d80000c1c05c1c0c40b940004c11904400c041d020302044650000503004028039040603006034500403003840080d07080070700e0143e079620440946413280e4901c00941a201c01c41805904 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 783788093 1250 783786843 783786851
    0xb03030d0e060f0c190c0803040f03080a1b0302090f130212070f08180f0105010e01061115070302091c111f0f2f0705010e09040807150f 60
    0x1040540e15070000a0004100041e02c0c05502d03030701000302d071030304081e0703000100000c007000040c92885114803091802c804a05010980c4003e42e200e442040d00220390903100449044800020550301c54240d1707070301c0114041d003003140c01202c00e00110610402c407504810705500050400d49552000306048804030028014003400320a80038040103034001c4240c8061500890000c2040c2d14010710a0000c840c3c0c0d5660755015958510034044003180205e07020070840e00034a101c0101c640000e0242030f0280020b1942c0303650f15450000c0041540e100c0b081400100d8100d20f1510781c40094143c0407540200e4603150168490340d52400081050000044040b2584520b010304010005608100e030b008150803a009081c000150307110088a10420604400064508400c0201c01d0300810b4990200b4501c8907420381d007041170020060110103003140301c1030700e58000603041219691121326080d940350107680c9042507041c2540c651049005076000108809c0a800384889440110350000c2c040e21414007080c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 783789343 1250 783788093 783788107
    0x1030b150406121208150910030f121103070f06110c10060e010501090302032a0a09091103030f04151421010f05100c02061b0f06091603080a030b0303 66
    0x80c3e4800c0460421241c64811102030045907008041c080c0c81284520b80401c0c50311829020049007a0004000300c9042139400b80110205104060409542d44166000f002d903c03541304001d0060348104039441507990041000000241c680065140c015900c04004200980300203034100b80c0c2d015501202c03805100c2e428010044030400d402120071102c0070105d0002d41e91b00e0f100111394920303240c00007039010361010540440e00000c101e04881007120f03500540d81325646110004d03449050550000301d146860740616003d11408001401141c0001c4001350300d0169000e1144001e030141d48207011041c142e8101d103098280c00780302c4d552980c03041c03070300740c1c0383c3d6405030200c842c1403610311400c480281940d80340080b138010a580440307010350f0340c010000c09411101d1681141e88010048080b41c01ca203050003000076000802c50803000c3c0f10304000c05814130200036a072091414038001d200c48210350001d0f180810481e03010700c0840589070800c1d46a9952062403209030003905000444030f41500c0006512 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 783790593 1250 783789343 783789359
    0x3011802130e2401020303130f020a03020a0b1806281202030f010e0a0b0307050402090402120406050121030903020105030618090d0212180909160311010806041401030b150406 77
    0x2043c41d841058152408180e0b1441c01266a400121048400a000100d0400220741804502c611091000708885035440e12640072503207072002c903840001104408607481210400f4400c100d460144103030380360350900c01c2e402e07400c201100c43e0758901d0700c1000641d5400d038079240c1706410044064134200b40942d41c9040c00d41039881c10990074494200d00c080e024021898885d81070144000d01c850080050020f01d013002c00700300081d4000041c47e81d21a5003001103c41c3c2c0421551018412400741400003100d41c50916440604025100c0803407903210002034450000360418000c0042da41c0a10f0075503201da6505000c03030342b6605d0719070724804641034020070040203a070005140005843d165003500d80d4000d41c01906007160289104568007a035007240e2410a42c10803041c265030010303448040703681c1921000c0c0c40404a90064009030380f8108015202e43c5503507040768801d908043c0c10381c1d080000710320800300e90300c003401c0c1030000400801e210000307d5400c861140483c4100e000041080107960f99807054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 783791843 1250 783790593 783790621
    0x1508030c0d14090d03030c090512071514070b06120307060510050a0b1602010e0d03080f100e04030804020622030b0a050708010b07031209111503011802130e 69
    0x1c40030004180244205141e0000c00568100038405803024168000340d60301035014095001c442c40400c00020400180c030340c7c800d9030b2088401d1524001d00b070158200f1100c0a1205240310f60384041c089414004058840030008481010380c20044000b10740d150000000c0c991130829507001c005100204607031040c010700d5400325000d007030f6042c940c1c0b070740c10303541d506021000100d4840d42000e00d1061025110450030010329081261051404ac64107010f00000240d2080b05084207400150012040020314a000703161281c02c1b5200b0701109c0d001a240040920401d8802400102040040800700d400c546501094440000c110502081103900d0713010080348a68032484251815002600803416403202e62140c2c1d8050b00156903640d816a00300586c0c0901644417400440810400814a40d0380f0700c0c0501c1008034082c864030141c100011410f04100c00070b08005060121100304000401040403880e03035541800440c4000962180d060070700d5010800419803280058181c4c04082041d454102d0b12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 783793093 1250 783791843 783791863
    0xe03090a0608130f08070807030906030f02070b0606130510020c011205060907050a0c0b150f15030a090606050616050f060c03010320030f010608250302041508030c 72
    0x2903180c0031165a80400c5a10400548084a01405264842e03021444e0401040360700d5001d404810314021481d651201b1035800201d0030340005800314020f00071941d0502495040070103c65080d401d1038425201c80080306c002403c07181c480c603800142da090610040910310001d110040000b40342c00c00310080a516a500c1450650000d03500041e1003941c13004038031a083c00351102070508a16640c5011007034507207510100c0c02d0402c5c4409002d62400003040020000d12500034003590300703c51501d0000b8052203030f0241c0e181c41e109540b10f0341c501812003004005c2c1d0782d00c90305c58880411500c00a090660040c4031035084550450070009030038528101d10f42841d852148150708580500e100711401c249c030780006880f0050f010904000410201c0c8040d102c2490b0b00102402400c2c400300e08500003440d1122000700a001651150b40030001c0c82c1e0706000080b13408170703445100c003010118401070b0b00c0640d2242c04024407459540d6003000c00c00e0000042e2001901403c01129581d604440702580e031000490 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 783794343 1250 783793093 783793099
    0x10219030201020d1404080a03091a0412080f040b0708060402040f0b032205030301050402030a020d090506060a080c030304090f14011e120b0a0e010b0622060504061715040e0309 78
    0x902c0800180aa031700c1502d00ca540c104000c1400c008015074204d0241845803001d0b40d0800025120004035012070b00181c4c0071b20b21170500f10107214050300021b460548005c00030549501c21800b0030000c9503990400382d521002c1441c0100c942da1303402c00081c00a0041e5044045005c030b5000000c41c5c244a29002940218172084124034011010840f490410b90032800003061a0400e0004005504240c1c01445d000410b00704090f0504aa04400c40215040c40340151030541c40001030001e02e0500794040e0f80603281c000f02030190b90f4100008299603100f01d221f0300c204950346885210401e481030b40405200741c80302d51098225651181c02000c019040c44580da222551424009032120b00d41286070b41030f981c80501103110780d40ea0040c400080018150001295480c2c0441c5011541c40768010040b44d5103810005444010307080610348a030f41240c01c03807403e00030100400c2c401c4507003000511902c27200d0000f00c44002c2d6264011001035000514583d50800d050490000f4a400e0100140803891001c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 783795593 1250 783794343 783794351
    0x260d08100b120f150d08030a06030230010b150d062d05011e0302090a030803240319080a0e031212071805130e0604060606110624010219030201020d 65
    0x108a070121002d000032011944028243d820b000080d2000000d160300c2340c900580042c1d065a00d070045281d0280c40d00b00400e85840000300401c2c920701c10109009443d01c0d401c001c0000484400119440081200f442e55900da00880c0c011428066900441c0c00350040c0c17039020301b602c040040061301c41c1280d0401107035600060f0502161651194079480d10a4811200c240c03070466101c03006400070b41c84114482d412124044010020904920045004807203031503106d41501c5894002d1070792000049102071084d00041c00c400034061b138502c1c000c007000d134100d0b508550703482e41210266822490012040c0d0540030701890701c622410350b58040e00e060308511441032442c2d503c1d6031040350b01028185690a07001d5a0810602003424206d000304250340b01428009041405143c0261a244041320100c2d40143c4850381032103600d51002c62500310640c920700511540c00c01e0107070b02d90208640702c0045407441c0002c05a50b5a41c2c0308101e201d001003140250810140c0c00c904009001c2d62008109007151030174 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 783796843 1250 783795593 783795601
    0x303040f170a05340b09010917030d110d05010807090e060613020a0201020d05010e0901110324010c080c100b01050406021002090f0a0f260d08100b120f 67
    0x401c1c414005079209016111004281369a0b449940741c13240303d40001605000100c03a9545200260130141281c01c0760141c841880200040442c9290740010000d6480c080b08500c00d00300020684146002078100861105001c3d04c001c0240e004403000d44641c0f40c2400000524054046001410760381c2295007446040c00c01c0c03a04a80e114002d0340c00325040000500da1107001d00712076026007034001443c0f00240c034007c021880b07a010790720281c2064400d6044030301440b1503c1000d10403600c080b014800c00034107515001c528504042d08040c10011100c58610032402d01d41e1107040094036990b8011800b60b10b03111880d1000d41d4415160b0807050381245402d8090619600030810380c0c0481c3c8071039000b0480c00d8441c48141c0040d421030a920740c1c1001d5484918075459858103120800f828a0401c2c4144051620701307070255a06044445096920384610044515034000c10072542ca42c81c1400e0031406500c3d9007802c40b100b50b0956110001600c408210850024208400340340220102e010603226070b25 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 783798093 1250 783796843 783796889
    0x7060b1903020117041a0612070f0801180f030509060d0e100f060536041a0c0703080105040518010e1e060c040608131b03060c0e0604140f0303040f 65
    0x2500c3c007802c010b011b5641d030b00403035001c0c00e401e9600c15005800c0c6003964080054840c40c001c010340000d41d0100060f0350031311451400344950700350240070b03600e040a44034560311602011104404040e0410000064806c11900c0d41011510304a01c861000c11170003281c0c8000302c0c3ca4051816900324407900341034403031003c480f4900504081c4c4400605041054039401403041c00009960718000c50000c02c005528228441011001d210701e009070845450f2449640107201800780013824908000d40c213201290109a1106419054400646000483d0344070308124400d0008112500041d5600340f140c0b0031111500455000c058800360032504201c06031080c0142d0311007070101c80003003000800703010401c8200d00c0741c050250081c10001003107403641d0450301d4500c1a400f00f03e005407840c10f50590100200300d035510a01070003c407189041c00c0102511000a0400e1040f44903603031203078a020041000c9661642c0c48550380c840e00070704882c6e4440e80d8102c0d01c241c00c5141d215008401e86881308480c9051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 783799343 1250 783798093 783798137
    0xc0e0403120621020a0503010c090305061803040315090b043206150d0f0c060e040203070e120114040f02040507020607020a0f140609070e060f01120207060b19030201 73
    0x5080020461480125202d0b0f0700150100d8801139030711010200d0002016207080c8203c002400c2c2c00d1b521600c6060540c100b02d4540701c40a00f4046988016805040007a0008819502640d5110342c4031004a060090048054480000c01408100d40e500502040046d1442032201200007404800031440e81d02e019000101030401c02e0103420f030401400a41c05604030701c128401c0900007000102c81d41c44e152034065003210b1540086a0400c00c459040c4401074000c805401074210440303040d459441c0501e00144030701030980c206e50051490700390700e41c1d5030b42e8203400104118a1203c0710f0002850142000b80030142100710517801285404003203022035101040c0c10b03108215a4008182004181e40c034030a901411240a68400e0b002c00341da840038a2042c440a40159441c1c8020f00d40710342410120445c0c014082c02c038a100c0c120300f0300c9514076660014107210817200c4111006803030301c4103820940e014019105046502505d9400e103511500641208513042d00d000b84e81e03070041e044030119650280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 783800593 1250 783799343 783799349
    0xd061401170a020706020408120c01140603030a0f02120c030d050709030b0f0a0b121b10020d1b12082d0f06120106230306160f03090c0e04031206 64
    0x95001c100001c03501c1c0b0a540062032403605ca01e170010307e840d07550340d4030030304141103848841c480c41800a0f00f1013400c8401d014202250166810900c3d041c01d0880c0040c1c3d4070704c40d800d41d16080c000c0020b04003a140c1e000784030303950075540020003050750b03440d55016103a120760180c046c1034001480d11020440a9200d801e0340703015207500102881c855210070064510285004200082c001e4480d203410f035050315842c0070440c0024a0500074280b00c2e20312601c0071480200f910515006110006100a038140d0000301c00c40c2202040c100301e00140f20119244000c0070311040003a10314041c0500074010f2540c00b0006920a03011340c1c0c0c211540c080f0903000e0407100c2c02c050510308524000c50b008074400c25815800c940e00550001c00c000c0041c40c4c034191a900791080c540c01508248500800d07600c6c8040301c00d002020380c1c10100d02500091601c0c20a801c0004da5a24203e0100034042c0c0d800c008460180d0300c020541c85e0068010b400c1c0c20354401307012413020001c40d422000107400e500f0050324100031307005134029 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 783801843 1250 783800593 783800627
    0x9050118080a021e19080105132307050a060c0c0920030c07330213120c0b0708091c020f01081e01151119080a0c05030d061401 56
    0x1c224503408010710006885a00080c003d004c00090309a0b540b00c0640001045080c00b20b08405482c01001e0750031100d00400d1072400e501c081c0d04410000d02058002c11031341c0c14529480700d50051800045141c140981c10883d08000c000320042903c682003200e800d0140d104040b8000100d40300c1c0c041c0000d5444100113504040c0070341d4510500010510051a07006207885889414400180c4811072240364180c1003d40ca6a000042540d00742e0a0303000328035420404040c20761900005d030906030b12804c442c0c403c0c801480c584c044e000042005c406e000400902904410503210032250a110341540d11601c54144569008160f043d85020350320790003a080d40c0c009122a14021000b03005482c800d0b4003c1007400654405681a600040100c0d2400d0103403400c201c4090b01e80541c18405030580036244000d4a99030b212a490301940c8010035109138074140d100000a40311021800140c455085186004040f40804905e840306c10030240d02c800115250484a580444440001920407004060710400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 783803093 1250 783801843 783801853
    0x810031401021822110f19020106050102070501080109150302030a0b0f01060c0b04061109040606030218040203060d03030b011e0f081825080109080d1b0504050918010c0905011808 79
    0x2130b00c010660112000c2c0080c03109aa2612081c49406401c0d1341c4003540b0400790304a001380c500480d0f80e09110b200c01816080c001010414100030010340801c40510903c1c50b0360f51100c00341410f035001260748100555002e822120303021440e14005078030b007404807407501c81e40c040c1d440009241c61007400251003064004072503c110751121340740c0002802180700114070404040040d00d9513503d40d8802c01d8010039240e40e0043e242c0e444442c2981c540091901101e120714018000c0c00020396402c800783d03c105506042c0007901c13185420060310000004214140409000021742c4a803540200100b00311900c541e032071a1841c2d03030b4207e020003409500f95000300c4581c0100c11010b1551403900301100d00261110300c20302d0096440e800c00d801c0d0b901241048489860104402c001e4042d0340c0204400000b0100210710325002603a0014094003c5105081c030480039100032607940b40040c1e12060318070001c00004c0c444184d6854003e40014404e00c203450000340d0b00a048028650409289019260900c010302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 783804343 1250 783803093 783803149
    0xb030114040b09130f1707170403030203220e0c120f04050721050a05010b120307080f090d0506040305041a072a0f0609180c0c0308100314010218 64
    0x41601d202400c0304e0201702c407080c600104001c082e1041502c1c004500e4070b6a59007552501d102351211102002d030103610140824400a6004010380c1e4004a0700d03041b041800794960201c2800d0700e00360b4050100d04c202c00d0107020050105500800084c20300096036180d80c0c603406181090144d048401800030307044114144040c0320850040e00341e0300e44552481039442c0141d11140d04158541c0802c603802da549200c8c0d20741c82d0a21040000440038060040d604045081d01c4044503440380402c02905020001803d80c081d9842d480d11030310aa03000350485015103014a0081c000d0307400f90085054041c038820071000801c503554211517080394008105100c0075450700d1904800403400324400a290031040c40815001d80209403d0028078a9684056804d0b00d081402d0101919910381c2140d00790401003400c401d42c2e00320000c865004e90614022019503110040215504541d0704000c01c2100021020030340020150040c0c1310102c00001100c801030003880801072100112210180d00c103e1000341c0c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 783805593 1250 783804343 783804361
    0x8070203090f0f120f030c06013204090812090606062505190317060a150e030c0d050c09130320031308060f01060315090b190b030114040b09 62
    0xb00024201c003030f1840400c000d02d4507001c0d017007945e0501c0d420560741c0081a6955250130400501c1c1c0103185d9400401409454507804a000ba46050044040700544d600502540c2d00c2d16440580c0c11070304074200544a841c45111950341040c2591070903d140b10320b40100b5402e141880031581e031420b00c55010440f407030041c6104a0850700d0070000303840c070780140d004d00c1407c10690382100c8103007486681c900c64088101c0c00d04505034100a031400e0f000c3d00c810202030005d80c3c10801507c8200c6e1325402d2483c01b4100d00c0c40024640038400c0350241d0401c61204a03201040000141e00e00119001c6401641c2940d40e46001d001c994000318010700050040d0b0181301100020032440c2403141da5450660745008421900d03d400e41d6000e5104039090790000042001d8030701001c000034090042d500e000c2c041c4080d051103101c0c102c4080c3c0203190f42c0d955160282e403810b9803100c946030110250040507007000c2c2d035118011002904240b1a0309080c000040314242149001c1c403c00c03115540007404802c0300e03100d240c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 783806843 1250 783805593 783805609
    0xc0e101a091311070b0703050c2517040f0e09030a0215040804030515010314151b040f0f0303090e07080c031e041103070e09060609091005130308070203090f 69
    0x1602c81c0741d550707031950042c590ba04801002d030070380a000044070070705200d42c0c01800c440c001840c90a88100a12104044140c000302006e5079500c66000f050a040d80c6042c0b007200300110055600c0503440019002030f03503103000490101140d01ca0603242c24540da0342d80740b09440b817090030f401c080182c11a070301c0400d040504030031142d0404c1c0220802c600f41900ea590383c03468040d644081c9006110940010400c100c0d20f008104182d02c0b402c0c02412410b41181c03601c80401001804246102d107007541d149401017500402e80c2d0082c0440c001c032610711542e030310b4226042c1031a40010750000f10180b4010035002981e620705401840d40d990b90407510354590300ca00d003241d00080c113100444006551000401c0c0d181c3c08250b4000c0b07004003101c03400d64800004051420fa25580003520200c0003600b04101c60b40e000c9403056104030305480854556507000c08080c2401141c1030350141981c5000140042031030300c20140c50030f080c0f098450304510345030080c0c1682d59004100d4000d600100301d035030b07000761405c0480c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 783808093 1250 783806843 783806869
    0x5030a0b1b040b120121021f020c090f06030c12070506030703060b0706050718050906060d0b1c1506180c0e060a050c0d0c1a130c0e101a09 61
    0x40014100b5807140d036000880e41c02259900380d001c00c01801403158000311400280c5401001c00c10560041107940803c3c210f005030035080d40c01c000c40c80245c2c40050f009002186c0003c0d00100007004924102600c0b014014040e10494028414442101054100403c4141d500c0c0000c10082203118030b40402c0083c2548009d2080042540780d1000240302040080540710052180f2004210742c5004040180b42200009421849140c44002040b003616950401904a075068034102e81c1e403800200e000c40601040d1b2281c2d6004040588600d100490309070a01544501c1400b0760141c2102203400765007034800c103004041c03d0302e840240c3d08165400d254805160401182022003d0881c030500051564100c004048040f400004d0780b60b0303445000b880321352100351640c2010681000b568480050b80e205032082c0f0441810500c0104600c112100d9040310704c0303940020461f500035105c0c99040511030702510142c10b0352888900118840e0340c25008502c0941c22849401d0034036075030104000741c55081c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 783809343 1250 783808093 783808141
    0xa092a080a0e1615020607020102130b0306040b060301061d0904120806121c090b13050d0618060c0305060a0e0a0207030e1002030c0f06070e060c0c09040c090605030a0b 74
    0x16119640c040e603e44400c03009000c141c405101080d1035100107810041d000f09240c045920421240d900ca035107060f581000d5500c00d501480e01d903911140854010115800c0c02903200c40040b000044181d40003a01c1c401481140ca00c0e10000c0c1484802d1040803e82950010710740024042441c1c0300700c2c4691403103a80904002e12081d03101c024010703002d0511000040b01210700400c441c00055850b0040881d04c000c3c06174014182c60142031a558210340742460042601c10702091240d0810300c0310781c2e005444001c2a240065508603242d04d86580201003500012002c6810400003440900e00f1780c45280071294000703c481c240b036a8074800742c4000d5201d008118140240d040204140e40c480c0000103104410580080d90384801101d8510302d00f104c114900c0c115580520100943c0d66071101c14801c15090907103e442d25000034000c003034100704580a0850704546410b0400092000800b40d000807121004010090241c44500749501c8131b400309800b46c2504170050108040741d00015440c0e401c1d100030b03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 783810593 1250 783809343 783809353
    0x70506070f020a020a23010507201206010b070b0c09030a0809041409032a030412060603020d0b0144070b030103050102040905160f08060f0a092a080a0e 67
    0x30364005141703000c0540101d100c082002840c4007468400c138150003464502400c5c03403030520606680e12000c20084000c1c48900c209605282c0700541ca070002641000301030001601c20301c0d80c4a0322010000e4100d81402d9500046603004554403256a20484256110141c0a02034202081d196207540c0e500c8080013542140c0e880e010248800e82c0045482d000300f152001455a48507248010142103002036140c0041e011004004110804000200c0702100c0c1c00651850980c04581000001408192301c0a500000c82e02924800c204940d00c61324180c4039a44c01140e031040c5000991660b00f8000c0381d05004181103498070b040940b03200c105002d00c0041c40b074200d840907034980301d10b054150003e038070846d426074000c1000d10400703060303004195100000c02142c000ca0321170000000c0c6410b21590102c02409134500109400e9206d6540e2030740c001030f014000f119020b5543da0003a0040c90314001d00b07851250242c0e107982c184160b0155a080444803507071919541e0712404805401050403003c0c0a41c14454 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 783811843 1250 783810593 783810613
    0x3030904050c09040623060c06041b170f0708060907090e01020903010c0c0c09050c1c20040806010f0b2212030e0102010507080c18040608010608030c0d05070506070f02 74
    0x29401040c5c080c2c540d84d58580e050600036110742c20701d1038103429501c1c4544800c1c005001500b00000741d135a4001e801c00c004190f0002c1444c004107500c0c145811400c89107171112102044e0130b030b002641c0b45006080ca82258080d503500e12109845a20907642680c490700f01000400210b046900410040142103000500d08140c000002e030031607900c454140d01040744800c040061000042e1440c0080200300e200388454600008604010710440c20118404c0c11245c41130203c07545564812012503015191301d01c03030f0020b03003100c1ca04030740c006208031042440703400b002260700c0d544986842c04031074144100d6400d0004401c00400c0c40107880c6088205c0d180c401800189401400d6927a03082d0754069214804c0b0086800002429a100203084000b804518400e114540b41c4440c101c0701c0b200d0b514040d081480f20100000307005041250700c13122042d07090880100d48108007200074145070604c08200c0d000382c0360028050b102c600900c000505150050030015030414011618510f041071188191034000c18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 783812949 1106 783811843 783811849
    0x1206040812071106010b0d0608010b1c050f03040b071101210c0e0307080102041e0b2532012c0a1502030613060503030904050c09 57
    0x30781d00340050209442801a401c80d20700c4081a903002d540c1d00d600250141e0008403915030800e02c0c01034002401081441600800700300a00310080e83e56004182840c1184a8801551540034015040c99881c10520062000c0c208008105469030650300302004e110b840c2030083c41c1400b00d0356100303480d00710403107030ce25042840d0302d800426044000c80c0102c95080c0d4942c100c1c0d4151003807080c0410100c3e019006002550845880d4550140c100d03207030900e4098442c4100036000c5410410008090880d98401c1e0883c00351000004040d861b40d912001102208a0084150720003584501020071009010701c65401071070000340328401340c40209a900c4010140046200b200d0750340c0d981101801030000081d0a60007441c001000080603016201a51040380c08520401c1072620020008425204090584101030021402d0242030341c1404020716010700011034a0313805200c410762580e = true := by decide +kernel

theorem cover : BRFrame.Cov 783633093 783812949 := by
  have h0 := BRFrame.cov_init 783633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 783633093 ≤ n) (h2 : n < 783812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
