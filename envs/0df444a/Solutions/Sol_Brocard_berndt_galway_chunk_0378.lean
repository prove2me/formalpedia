-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0378
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:30:27.305162+00:00
-- url     : https://prove2.me/submissions/f647ca6d-969a-4632-818c-8f472b2b1058

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 67805757 ≤ n < 67985614 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 67807007 1250 67805757 67805761
    0x801030c090513061a0321180114030f060a05100503060d060b0604060c02030606010e030706080702010213060f020d0809070302060706020f0301031a01081c081005060d090228030b 79
    0x243da040c41001100d40c20010a1050a90172100302540103560001140240107458030080012480301841c81d1500c884825645000144846035071814a41340c0d111781000490100d0540c40500c40d40514020070308038001864a080413070400001c102c1580c802c3c1d0151a5003d000d118250b00301c81903a030300510030344500d810713584a40b42c4a40207010b111112a403109001c00c002c150294000720500b4182d02c2a8200c1c2e205071210030041d511401c40140e6154075511030b031020b020031482100789035004080d9000240c00c0041e0003c02040c0c0c0403468101a002a00c10301034034450a034100003000b1100450308044120f8240400e9003038550000d0b020103802030000060180400c031095046556040c100c210480c4ca0b947c4a140c4202c50840f1031107030094400d10b0100100f808035000c6104003201003c03a8410f05024040b01058075841c038000c16154a400c20303000c0028640c1c5a80008142e0b4103040c1100045082461040207103161650703511121a100c0000c04540585a54048000383c1b0341100c060304042d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 67808257 1250 67807007 67807021
    0x108121207200102070c1d010b07030513330f0309030c0501020301060509090a05010803090f0f150901110304050603150d0501060b04090501150f030c020f0a080a0206070801030c0905 80
    0x80380c402515070036031241c07480390b04105507010f6002d009901d01c68200041c1c020b41e58081c0b041341e005a10b402010401111004118410401004181c290b10900f02641040101c034031b0b003c0d6500c020b6000c5650040403041400342600c0c50903040078044000310300c4000d51510440002c0c401021007180768140b503681c659020505004881c40908107a011000b50b5480d07850f2940105542c0246034400e000d401c522011031038071100750050310305994403200111304002c1c03450208000c0c58050308400d90042100b0001e80c2c07154482c1100100324a4194500654500c90307680010640722508aa05005800500043c400c0355554411207420014510000c0914144440042c1804460807002040c540ca841000144e288040c00600101c84402400308011ba0781c070408400103180180003c400601d03001e80301410540030f5401800d040c2c0203841100c9c03604c58203d510030715000d0300030740c1915401c00100300907075a04d90410101d07600140c646040d0010b9403569640d40408a130a00441c2c200c40c0e1250000303122 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 67809507 1250 67808257 67808267
    0x506010507080f1b03040806040615050d0b060910050a0506130b0d050402010906030204030f17040f03030305092116050c150909010501051e03130203010e030d050108121207 76
    0x1a42c20a40d440c0e901d81e0184020340c0d695003d2801001807440d06408040c41e60400f00a881c11504004040c2c151039450707650301c00c01480c00c0300306a003040d809800d01181640304c000101102d40e12428840c280c0f802d040301049000c4900800703d0040b0329210344140070949a0030108000c54209485c159101c03802c160106220011035002001300c040c004c0380e00340c0b4102064110034080c50003030300e90404282d2640030032002c0e0f108600000d0101192500c1c4080042c442d605510010080b42d400c00741042e44541880d1138206841e4420b600080d15001440442e207014000340040d0113007414021382480c164409020a802031710503c85820100c111080c041c00f409120100287c4c800405c02114039021030440c1c0c607190072070340180e40103800d120004078565006100f03c0d149411440841d5550030440c1089800720307070004120308440d441802d00d0b81c0060700c00b4081d030380982c2050806151a1071014451500b1a0303016400b1508960010382080d079155186001c6070316000400c60b10007103580d24a1000d40d2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 67810757 1250 67809507 67809517
    0x6070201030e010209060307020d08060402030f010e040f0b090a06050a200c0a0f1202061e01050d080403050a2f0d0f23101113091e0f0b0f040203070c020405060105 72
    0x2400c034400004202318136502084403242940b00d42c13561a0f181d00c0300000d0000720701040300d10b981d007802400d0040c40b15a41e03100883e54000d106401050901c1f1b110b0b40c8030000e4250a8800c1c800c203902141d020740800c0042c0c0115548154640c000f084511114401c0044030b14401c240044407e2001644207117104c0284117440c029238214030482e444211310b00d4a150b40c0700d41c00112500500402c004136020030001c0000840001140880d0002a401c2400308580258156000ca401860400001001600a201c592201801140b0802c0c031500e8038132039400118404034015440d8500100c0c1c4c250b09680c0c0c090b10440240d0070107030b01c014a41c0c1c03629000400300c0885a0901240d001c08403001401200042c01c0c00801b41440401e019050210014000a0040d0500f0b070045001c0240c080c44404400e501002e02d8141c80000e41400c91810304400007114400b0489102c7e040e00c81c10411303541e0612221006c02c0a8007920114038600e044a001840f501058400a03c07598aa2011072544da1240c01910303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 67812007 1250 67810757 67810759
    0x1c12090503031602010c08040308090f1002030405070506030910050c0408030d09060c0e0f04240308070b070801030305090d03020309130f060e040c03080a05041502011a0f06070201030e010209 84
    0x1042940c206107550341c008540840c80968194032242c0b10510602800c107183d030181c2c1341c0d0405501c070ba41d000c1e1a1000010b02c482401c3c0b249000c06071503d00700300714482003058512401607981c10181403403410324010341c0040d030059904009021000d040000d8040c04502000740008003070711100880c20940c0300d594491643c0f8400841c015001c40c030a80d00c0066030390311130b420402000a034040306440f0041c80c0c0d030203103a0049032401404043c0c10642c006010203901c0404d007020144252000c644001040e40094503800d001146850420481070141a0400c80b50308001000e0340c91a50000c10354800c880c0000d0040240d020070b03004042c002c02c10b454012000512144d40c403601c02c59414010480c122103154200e04110300001c60f1007803448a903005030f0708060032100003800d6868003200f59106119007001c100c0d04001c00159860030f600745030395000c0d8580c004504420756101c041c03507080c02005002d11801c1040007078261580c0c0d48045500391503080c01c000c50f124030003800940c020b000d108075807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 67813257 1250 67812007 67812011
    0x40c09110d09080a09080105070f03090204020705011d07060203030c04170a120c0b0c0a020607050711090103061a040e0309041e05090a0302060702060c090d050a0507170705040207051c12 82
    0x342c2000f500314050300001d4615514441c880f0b079a40c100074242ea809450960100320a4a00c001c401c5103c0e4000c000e00c180040d04c0985040342c00e9880c1400c6030711072558001006071130941e442403038809216010061a442c03000314298104991030420b644264491040740798440400310304a41014061540c0f4590030580b0002403c000360005015010840c000700c80100816001a602c01c05803819540384400a07130081484e5681c0300425940d943c071210703064a000c1d40c0412182810b60b20380d0307a0540a036204035000300b80c40840503e40c61165140080c194411414020407091500000040d1100000c040300d004c182d81c1c02d1407801080f01211245031001482c00c3c0004c010803810009101c00c1014403903400c540386135480100c22a140d0100b501d081c041d454042155806500e09000d0610040f8003d0081d90b18140316a5501841d00781243d10801d010071030f1025001c406d4109210260040506440542ca400c030785513681511080794008122101a400d00c003842040e12075011890003405030340c1d017 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 67814507 1250 67813257 67813271
    0x70804231509010e0c090114042a02010b040b120a020103020307030608010203160f14041202040209060c1608030901020a0b180d05030103050705010905180615070b010f0e040c09110d 80
    0x21140a446400d5003804c039072241c0c051100040c103082101904982ca040c480f245162141c5040002818512010148442d4090364101034410800e403103015003d4213400002e00301403a9004d020980c1c91459101c0d100e80540004181060004038001101550910340142d5076030701c1c080c0540c000c041c1908001a1988003000b0040c241184100300341102e461900d690200d0017001c0801c9501c885d50b2542c902400c030b4184000c0101c40d07005041d0a415920041015040c100080b01046132078200300700006080c1d2140a220021707012607944103001e4561f40c00918508510000082e6450f016101c0040205001000081c2d01c5135004042c42031018001090f1040a0444800100036400a00098856004d4010001034640c0510031440c211500901999182ca0380c04503440103050f8000d20035500140c0c00c07a15085040c08540041201900c07a4180d00d800e94140042114100101e4000c0c8000e004142c0511000c200d58018020841d44c0012000c51001d40b07100b488030302070087c5482d4250b0319080c50a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 67815757 1250 67814507 67814521
    0x6080111130e07050a0e0d02040906020909072c04200a080105060403110603040c030b101805060f0909030c01020a09050915010f030906090f050106030b0708042315 72
    0x500601c0152072019032569251034034001c98030000d60302c000118400300000b07001c19009032000c03640c41a0040c40d08010100c5900428151654401d088512650002c0c081c0d0b15441c0c032402d9140c006c0c42c1d5151082c014210364021280141c0da082814400c401805240601a503443e00300444188444440c082120b541c0914507490f90409144900400ca20800101e264104802039800701e13038002507013000c42401d481c00c0c0702166101038001d031780c9426007140102c00b080d255074580d4085d076110f003000005203191140100a2260b1010100036140c281414010b55a450030146199601c048644600c29202c50380e1052131480781a010001950001c50010000c40d00403d13401c08446090b1000303d6580d80703010466000700e000c50001d0307002c200c041106034040d40c03007a0702009100e44151400034101c1c04a07110902000c5400604a4141c1e440d00380c10301c00c1254142480740c021382d55041810160810b6941d1203a18400810b405c2c0000622807058260ac40c4204208051100d80d141c0081d0301e802c100c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 67817007 1250 67815757 67815791
    0x60f060c0c080c0d0f0510050408090118050901090209061c48050408070e01030201020115080a03030f020702120601030b060a03050606040c0903120503070e0d2301060801 75
    0x1140640341d030110940001450500401d80e01c2105030000c20b101041c00156940e425900c0e034042055400b44244e00510034031800c0b52240e00e00640c00380c81581d131130350540790004083e440760589100560011040070816502c44600d52415148070000260f112145134020882900441100c88020300343c0c10401090300403189d1000c1204401403580e4030707032505d585500030840d00903401401042142000884020035110905800190241c07424a00d0700343c0c0e414030185403c409400400d0310a0140004200715a0248660710040001080b03011615183c02541601c8a01c00e28008d4149503c90036502c440c3c806c5c0d0b604940200d58001d166851b400d49140301e00b41e941c5000d0000315050130001000c03400c5442c1c560721510460760b02100801c0140e56100501c0b000d820b0082484083c000700880103c001080e00c0380c0c400b582d0881ea07590079201d2a00800040c14085a18649070051030203410750710102d02041c1040003000010122803600d54443d200590041401e64030400c01ca51a028031500c0c00d00c04a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 67818257 1250 67817007 67817027
    0xa0c12020d0e06130615060e040b040605150c010c0206010503101e0f09050c0f0607020f0d0605091506192606011706061002300a030e100504030212090301060f06 71
    0x606020020940c980091132846a00c0b401403902203110942d5401d02849d00780c2000b80001000f50020070881c0e9560041030458243c26001402c1481c04500e04071554024802d0340340440343c910081c4002d514180100f9140c0c00044920003815486a00100440620b4107a000c10301d03034140070401452008001000c014240001b0440d0f084c000c0071901a801e28140c8440107100000800e140d15145c110303401c00104284014140360413000000524010498074880c62744a561001c4c05050310b483c46240000141c1401054940b003614203980185a0a155622680a507801121622030902c0c2080e043d640c0c1c42920410112240b2802c000890310b0109680a810101c007000c08560554451104124115800c0d0044200581c08000c100440c8181454503003010700c7c1042840c1015052500b00207510340c440105540440d44a03080b9034071412040000c8018001000020005070900b550001e40710302e03000403550302194004c2205811543e0079400003009100c00c454080c0c0305607482d507014000d4800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 67819507 1250 67818257 67818263
    0xd02120411011206030c0909060b120102030105190305030304060e01090219050a06050c030702060a0c141c08071e0306051903170c0d0f0509030a0302060406050a0c12020d0e0613 78
    0x4003045142c83e0708940c0941c100b625403008031490b4580c1445002001400c207100203641d816100c4d550f0b1744540c0c503001505040700b2211800540d4030344c1008180240440080503400e000c400d040403c1021035000f0090700e420543c0140045500c0440911407409030100a20195000c0d00303446110384c0c204518030340b41c0d0844a0555800320810b603a0f00043e502c0340514401d0000325042002036600614142d801410000340904100c54800d80d00d0701d610300c050700c5602441c841c44d400001c1010f04c8050410300320f0201080783c80c00c0d80300351510740401800544580e0801c1420f1a803030310083e803120b0090700100007520b0b004d0300d010108614070310200650303d228841502c00112952000040c1d184240849020020100050070075009406e022030750b511805013407008000085c0309640072540c00303020f60a0302900980c010600e900781410104110380c0082c108c1858a031030301e2586020940c0201541c0340882c03280e40010b80fa0207800101c04041d08540b4080601400f0300c03c01c204018040300d00306401c840c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 67820757 1250 67819507 67819517
    0x3080d0911030309060405040c090e011202040b0904030f0806010e12010204050405010b04030c060804030e060f0c1006080c0f1f050703020f030406090b0702031c02030a08090a11060d0212041101 85
    0x407080c082c10380f2031041000c0e080e00068200014012070902e500103401d4030f4050300d0200b00250380c418044813045000e8010031250a00d2800d400150b1911b1301070200282001c440c404a28201741c1c2d8081d0184245540040602240c100024220ba00501800303402c030402406040c2c0032204030003003500035405401100d218518110000c02d240e0b03081030a440039a072380260403001c0d035420504140d4412a00030001c40400241c2c44c01c81002c0e4071500c024201d40a0006199601c0b43e40e428a05030500c0d603a00c03003103802030786808020450780000041c02d03a441c080a8a404058020074404940d2001e60306030104004098016815107869001c0e009117502d5009500795048016000a041d88038401c41c0700d81000965812014880c3c0c1882c02c008004451004046503681c041d41e0680c4180c1c9400702c1448405030300040340074151290410035150340056980c3c0505000c0103550307942d05e03182590586072400340d200810f04040407425641290030000c02540e45200f189420b240c080c0d004845c107601035000807 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 67822007 1250 67820757 67820783
    0xa020709050c1219020c0304030b191103190e19150203040302031b0109051b13020301050607060b03102406020607080106030c0207230406170a08070c03080d09 70
    0x50300a020794020001c540e1030a03040d922080441300b001d20106041220300e9070708114410345c118040004000540c89154502240e280c150003031501c612131419040641410090980100780d200011031f0b5110b604045440c0c0126000c0c600308005000c2c0d228420300c10702c00c0c80d0001c180e021901600b80d01d014411401c03540480a104908c20580c00190b0300103000d644144001b09090714100c160501906d010304c00010f0a00c0c0da0748483e844c0c1845c601081000e4002c035484c0080500b07114a003213680d8681020150303c1c40d40b620380482c100e44120940544110742e40c1301039140e10b54060080d40302402d0300d21800c2c45103907003500b43c6034009180f03500c44402d0242059400500b450000ca040c2e84a803085444861140e0700c0c25105401402e0b85441e00e00441c0680b00d1301207200800205040410614058440b2960f07240400740800c69869400280c0440b5201540b8a50380e200041e10321241503001008a0712454640360071200200c0c641c03c0100fa1140c04079890740305110b01d6000101070384c051803180c0f641c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 67823257 1250 67822007 67822021
    0x50405070f0206010312140a0905010f0311090f0619080609060103050601170702100c110709111602030a0209040503031e0601020a1b0b0703091409010509160e04020a02070905 77
    0x61080091400035030808001000414001c1445800c0304c43d460901c007070080c47c1002e40181d00d6003c84a6280800c0c17403184180070035640000384441190160400f004940d208124a020b140a1200755a10a0307036100c010701071585030007003907c40b50710080c00c00502208103006d0141640000320758890181000390300140701507229010b410700507881030315003401400032554440c20080005007844154491006040c010305114030602c1980c02095075405032051580701c2c060b05080242d44003002070303030800000c0c0d80000565003c03910103061000136010303959600d1010a00300442ca9078043d41c410365800070041071103004801075218600c58514904240b64020521180350006d9400c00d005900900a00700011010f42c120f010725841300814000840c1c1ea060020582e0b4003004007180003034045181001280d4084140351b00f050011900040b580d030400c8003081203454010600c182c055407280200e01200d014141070800d122010f48155518199110042d68801c0c0394440c0b050b18515010010707c035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 67824507 1250 67823257 67823267
    0xd030c08040209010509041103030307030b0102060108120f07060b0306040f0b060a030c09020702030328110705130f02190815060301081509150115030c260c090a0305010605040507 79
    0x2081d58003d000c3c000b1a4205824031543c042e009004a6112200555000725540c0c100040d5201c2d803401d6034041012080f80000900388001a800104694046041a50030616010944458410191401e034840805007081009868092f880319010f014a006101c1481041151a03101c2030088400d0046a1202c1041c4160a9403511000e0040c0501078800d000c4900103400802c9000d0002702102d040c9542950040c0e4850100c403001060000003403810300c40b50380c004100025507072084c0040c1c240d80b4074040200785000c056202d41000d0581e281c0c01001a060035038143e42541c000150b8008202d01f280f000a05507140580701e101a11424500d02c4400e8500f4004690588607141c01a002c05056038111915802d4083c1c44420b180c01860401050424540800340c000d1a001041003140c80d040400501106c03007002d429810440003400056030280c14100e00d80c0b854400c0e01c40500c141c0d403545100501da0040307965a9501c03070940366002050080540041d410340e03c0440b0100010b444601080c2c40c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 67825757 1250 67824507 67824511
    0x317041401020d08063304060806060c0a03080709080f070f0807060c0206070606081002180109030218040c050d0309030212010213140f1309050114010b1b010213080d030c08 76
    0x1070380f0500000c1950900114841099800310030501c0c101485a80d43d44407907468046d4040d20100210301000641e41c03001015400c0702c42681c00e90700d856001404180c42d0544441b000c0d060000102c04a01228440e001c4600107048403c141c542c003d0298001c5ca031140b440d4424000351029610001c03414100c00300b071820031101c05840e0118000c0180e0b003809a99007015400391006a030341c00e40044c0b81641440022003001c1310f480010b81d51448800b44010400383c802050381081082078041c4010b840350680900c2c00c40350400c1135207560380c0c2c1c0c1c6400000d004007a0001d640001c1c0c0010100c040540088605055a100320742030310680c1403c00010f4207d002e00200c54100d07840d4030004014040e03448032800d81002001d0418601504e202c000300d0446025070740240e244558419030082030120070f1050000c40c0060300c08128007540342c403241d82c0e12402807850b5085076107000f8143e0300740710390254101c509228100074040170241c2d0b200c10144e1245c0a03082218086030400ca4030a060074801d180943c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 67827007 1250 67825757 67825783
    0x3110d02011b0c15020a05030406050a0c0c0303020903010f060b12091504080a0908150a0f060303021e01060e0109051b0316050309010f0e160501020c06160804031704140102 76
    0x80540c1000008540c4203c0800080e0b41102c3c420705068003100281c0002c03d441a03146d101d0355906c0c14945005022290b0060800407514508040d482901c0da01181070803000e0f41501c0c000d600c5440000c00240101501c0c00c1312500c4a1425a0002e580c042c20009007040480c0c02003103241c180e4401c40c0c015222100c180c02540e0700340c000c0c0000341c002407042010b000507106601d0664542c5440702401c524108902c90052801c5a0702d03030410019a070b0350701901181252081c02407004502c0c65601030760302d09803803505408a100e80652107101c6c280942c0301c0401402d0560f01c0600c59603550a00d503004000c00c0d00c0000c51088407a14201c4003800380030480e0f009007030b82c0131011502144c404080750641c02c05440b01c00302d07540759401c003d0000510300441d100d0a00c158040c3c40103101501580f1254020b5500076419074000d08081c030f8407684c0380003c0d070f501d00c240d1650206c1080e09a1402e05a07511480c2c0000308615141c0c0035400794883d0407c06801034a401c2c58003074500d03060443c0117a81c0c84607050414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 67828257 1250 67827007 67827041
    0x10c0512040b0408040806090a1106070b0f060f03190308060306070e040903051b07050102070510090e040809031606081e15060f0c010b0a0b030112060207110d03110d0201 75
    0x200780080d1040d0300c6076502c42c0c011100c0030300b056180c003200e604040040d1032001e001e9100303007041801e0201c00800c41c8019402120054500512552614000d04000385074600721001c54002400c1d94450104074a00780c10014113803603c298900300b4040000380b070a42c06900094480b00041c026040c0000c19602407400c0361240000144e900b010400038054036032b0100c04201c01072040c2c1503161008040c0300b0394142d50b80c014003105420031000928101060b03208030300c82d0b0034a2410320046504100c0400541e0100d003c107003400d40d202e04045440b44504010306800d4440e508031518443c56152442098600303a559901d041c1d1246007811880072000800d00c1c501044107000306001c903680b0f240c09540c24501401c0542007030a5a103c031011030b0050301c640800d99450307101c14001440c014507004050400d5061003410755040100040031144a5200180400c2d40004c100f0b0502c18400c07103015003207070020074410043c0320f5441c00501000c0c43c03140d20070140c030900941649580c018000c2c041c00802680c16 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 67829507 1250 67828257 67828261
    0x703051c0603170307090e0103030522060504170106030804180e0109030e011206031e0c0807030302190510110a030f090803070e0609030d0905030706051207030506010e09070e0102010c0512 83
    0xc0800f00e40d00c0035001c1c2c8180400341d4000201d10708210f264038000c501940f5600d44a44402131030b44140512412019409001030303000707015440e00b06c0240c5060700d82c006d054018601d01c00d1041c1c2d004003025080509088004100041c14106044a001003020801001d0010b6078008901034280c0790f0041c4000c000c50880c000c0f030101d6512030111403076070201009010410544d80e8903452803022117804513a008580b040e80e0041440324101c4400300a11341e940080850342c0c990b0720002c0d00d441560310003803401c01150b143d92080c80b1041204403e0851030320f50800c0b040703c205c103507240b20343d21030344241001c00d040840b440e0603c40103114106009030814001d919641c0d8a07213085448400e00600203030700810501c8224925202044840c4203880b6036102c8807d0981000101880e000059110104000c0d040040c103c4120110707144e035400240c0c50a001c00c0580318240180d13084d0180c06101500210030f80108000168450501c0c500c01d0002e030000c005d030010030841203400d03214404040c0b10715000000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 67830757 1250 67829507 67829543
    0x6170910021c0903050904140f0112210201021213170a0908010e0105011d07020706030203070e2205100e010e040203120d0c02161d060a0b0703051c0603 67
    0x501056000d450105042002266000200c1e14150b0f001d400045020510030640e040c180f19542400071041c45680749480c00070f032018a000e4050013050700304810314404100704241e824041c102d111101c0324500c80100502030081c000c0d0410602c8030101c10f10100400d41c41207134030080a845136040703042031400072078480904401d580900100e00801a8103480000c2c8220203100e24041c400c02c0400101c0c0035407410f0388401c5160900d460b85c0c094480940f06008072a600050050112041801e000d6126518520195451030800314150780080402d5040383c0e26601703a10310410310131200c6c8001c009649590450031000390300d038011007503a0f010a000610111a840c460580e21078801411680c03000000c40c01d034041c540200368985409512030b1821410160144580c0344000c1c14203140d00340031444c08444850000030700c030b1401800b00c1d260010500c140c0712156a400a00b0249000a40d0750b152464028100c0c2d1103055651800080e100702e08a42006600642040300d801c1542c01c400400551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 67832007 1250 67830757 67830761
    0x21050f030a1a03070308130506040e0a0507030b060a0201050415020901020a030305060d062a050a050405120f010203100918020f010807030e060a091505040209160c0c0f06170910 78
    0x2800550a041c41c80000300b041e038007040f20901840c0715000090316800c20306041c00c18108a500914400c070000d0005200e040740300144564000000340f0089159194120190010104030044076000400010f00341022501500464040c0303208507100b801544501603910204c3c0590100c0ca8010717001000c5940109110703800c03664014100400c26070b004030a564640c401c68450484c0b01807a101d05c180c9003640c80e20404103071889294142401e6140112068005029203e54003e0318440c0c0c120003400300040c1810002c4d1410072503040002c40d42da00705038140c051449084d1090b00c1d90079090040d8040000f4050440e409015800380030b41d5041e1107a5001076406060040c80b90080603581c8581c44035240c010001703a8014048020002805641403c003201c030000c45030041c00d03500e4240810710006880d032900d0385500602c1495081004550408112490784d4440409040e05000140215212501181a0044800035105e0500411b07290165545540c412205450603401000c01450000382507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 67833257 1250 67832007 67832021
    0x1020f0111041712040311180708040b130f0606080d050405030601092f070209060904050c040e010b0a1421030301060302070609020301020a020703150b0906040f0b0d21050f030a 78
    0x103c0c150f9401c10454103030480c181d0007544c4107a501940d0201700300c02034100100050040f44090520000910f8139010250042c0e5010340010400184100007407000b5041015000001e41e115442c150340c0401030614130b0146c0b040d4000e0300c00310b000308000304421078043d400b02c074102c0300c01a0251226a182c081004c0c018501c4203050089441f813a0503011507a2525540310f1031590b100c0e4030352610340d816401400729490006004902514100080c0300228000096020341c0c2902214046001381c180614036003d41400020306410090710000810b03141c00e2214580e00e10101030b0340021080070f442000c017a0080070224900866007080005000c024840d130000d1203610301884011a6a01081d40441c0c02c99110b44100001a000340c9824002c000380302004064141c0300c1c1d5030602c0451034460000700074103006400306118075510103040001c00c0c0030343c000d10310f0114000c00d0603000d00143d0605a0440b1003800c0740010308801003003003240c41c1c0d002e0320a44e02007480c41e8460304c1c00c2d43e8a02e200c0b80c0c000c1a803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 67834507 1250 67833257 67833299
    0x6080609070903080a020f010605041802090603100f0f18020901170a0803070201050702011506052208030c0304080d021b100c0b0c04030203070e04030e0114070503040e0601020f011104 81
    0x4a002d020012507110001000c481c105580103006110004a6484c21504980c205a200e5410030b610150a02a0740e4580c03003080e0f4040740c80071926115200005c1c41e1040090450301d9503407c1004c50380c0798404a034440c4000b55032212050005100c00c550705151104100c100a40c047c56500050010200c050780d080d460b030b48400704550050199888440440d002150242c0040c2c0d181c0041004540d428001d682d519801041d128401d0b0b424018060028040d03181449500c00c4a0705040c0312070421100305034010103184007501d50b00d01d1003a00403038495010f40a2070035540309600e007040000340f0001e24200d41c0003002ca141050b040c0580e04100740c01034484040410400001c07031042c007041d103440c54070b8004d1982440d4503a0f120320310310515007041030f40d50240854180700010000440d8101c008108070042c2442d0170128040b180540340301900810b0009801031101140108110b07442c040030b01c3c090707e4243c00f11206408110a05801c2ea05980c00c0c6a9101c042404108003140c00c81091044a003d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 67835757 1250 67834507 67834517
    0xf100e040302070b0310140d200d060e03041d0f1305011b02010506010e01050726040e0c0a080609040c050103020d020d1a010327020105090d08030a060504050c040608060907 76
    0xc3d0307540c01c1c07803500c1c1c00940c1c1c80c155034101b4032010040c81000f0005002032050584600b003482540d0b444039072214410705040343c50007512011000e1030b43d4a400c119404d0580c4024204681e10b41c0000c05070741d035002402031103115045421a6a480960203051611544580095100725960103132240681002c0346001c0b2065900c41c200b00d007481d0244415002c425002d80d0000420340b40c10302c00101924881c031403490503c00104910303004507100240e903030340300c4101004803249003854460800389403043d54002c1000b02d41d05000d0003140da11001c000e10f601c2249540b00d09240e1221002c00100043c280d034000c04aa0540c07200b040706500070b8000e040b04958050006003000074030b000c00c40c00d031818071036801c4100b500d10f61080010346e01442800c015103d26480c80e00c940203100c01410000f05800c4010303040c01001b040c5400d8a6485508001c11700b50b11034030080d100e0401071000d00c050402d038001e10788520300300400955140110000da4040b1012130340c64810a461340c80c01e00000c07001c0079210340d08100d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 67837007 1250 67835757 67835759
    0x103050d1b0f06320f0414061806060f06071101110a050303040210020d0f140f19020d020d050904020c030c030708030403230904020a03060e0106050c01050f100e04030207 75
    0x290556002242e400d01507100825126841c0c1002c0300740009042c0c02100074240c0c180c1c40c2d554080305210b4145c0c80203180481c84199210340c01d20700c81d41c07d803c0d025003c2ca8420082000582000e854510401e070403a2002c4960a03104d000801001c0c844402e04c650b0440c00c1480310901080c6c45054030480400181007200604006440305410030000117800d9038030340d00c00000d010450600080540c5c0100c03003440a040409800a0010012513074410380b0420001502c00803d441800b41044544403140340b1941d6903560b01180e803542e80e103150040c1503009405070844080d9454000309007610503854540d19035250143c0078080000a40200c07101d41100c0c8000c1c0481e10203100c040004014141c0584080c079107900d014a001000078034101e50f0006040d111484601960300c246040c2da000100484015840c0ea0b4003190440080c002a4041a0382e14212000050207542000092030304594001c000d10499131205030940c2045803e660026420011804c20007000403c041516001072107032060315103c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 67838257 1250 67837007 67837013
    0x90a0506090a0f0b270c01080a0612030f050903010c090e10030305030703021b0d0903140102090307060809150705191403010618080d05090f0315040605060d02030703060e010b0105030103050d1b 85
    0x354050b081c2c9178000f40c1c00150104815a0002c840c150302071500303c000c2c001c05061452030003220000b4540241441804000124000d0240064500b606009402000380d2080510001d01460191055105940d8600e000c43c01d0350f001d80350310905403038154a816145d600c82403000c80c000d6101982111a01100100f04000c0b0b800074003451217008002e5450083d10b50031401e0884604020446941e40f0b40e10400807440c040d100400e000013140e9190502000c6550340c04031103420700e00300e19441003045180704100840c99030400c000d00510404500840c9000e003160400783c5100603041100090030906100420143d8070640c0d084000200281510720482e56607106c10707181040da045000c0110350081500e001508100b8061101d0550490061003e084004c460b070381d03011800f4102070a202e40750000187d840d22201c00100307040b98003030101c0d80c400380c1e41e090010040c100d40310707030014550903c070f84000c1c2984603030283ca0589402201403c0071445425064403542e010703030b107190300c0c0c0d040511428000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 67839507 1250 67838257 67838311
    0x3030403060e071e06020a0b06040b030d0f0f050c1f020c030d06060f05040b0a0c02030c130b03010e060c0a0f090e01090e060108010606090e040804050405090a0506090a0f0b 76
    0xd0b02500829501e4105401807041203440c00b0010a02e140c0c0c01d5013004000c1e40082c038408001e82110900310a40c41d420003190242c855800d049816200b40445140426400301a03521047d40c00d903240c48010074568400c0301c1c1e5203e0300040c40e12035070200710100601e400340229034a504040c40c42c010710380103200468505507000021081c009564422041110f84d411040132038a8540618001e4074081c01c1404030001d81c041c0004100400451044110442d24108006410030600905e101440c071611480b04000d080072000e224041d509050313a0003402d140006d940d5004000c01c0010604240191100700d400b00074040d810820004603420010b094002062528040e084054000c60744d03c2c09039100f00e18001c1c069111000c6e42e8508a004c010180c0d000b0005410f581d2101c103000480e40312400c01c0c890074012504429031240c542070030300154070000a25624071501c40c0096034903681e6000c1c440c030b864001c0305101400b0451003100101c009038140c0c18403541320030010b5005441d801d088403880c01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 67840757 1250 67839507 67839521
    0x20a23060105012c0303131d060603040308070c2f041b02030f0a1806050c150105060315040621051903050306040e16080607120b0d020d020d06090f030e0d03080103020f0303040306 79
    0x4000e08c5010720782c03916507820981e0a13900100c150345041c610300303041d40c0040003a00c00420328403c0000c040050b0080003000040f6986003011103282170079000780000e450300f064050b01245840741d85440c0045601d28032040203c000011030390003850504500041c0e440710340d40030301401c008000c03000100c5d0750544c820070300075009001035941d50360f1502c00b0a01e1013031501c040c00800094224880004000c0703641c0703040132658804012000c003a54a0f40d91800f00c2c01a040f00c3d041021100d090321000c0005e50100c1d03041601060290742141c14000500b8134001140303403440f101a0000d40c003000040d08038202900180e045444000032241c0b210f41e408140d007420309680c5c112605e26040401400040c036840703404030301407821010f8104001d001c8000001e02c2e04020101c000d01401002c0d00314021356070307400f0028006a40201080c0140d034071906d0500340c2200030310780803000700d9249900c1e03501a0038000c81038050544e241e101c4030341307903400e5800308a101d600426402c0e80c507100400000c0005107444c088e01c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 67842007 1250 67840757 67840769
    0xc030118060c17070207030b091618200304171e1c0207030f03051602031b0f070305030a080f070509040f0f140f07050c061501020a23060105012c030313 67
    0x960f0451802d25148d2030090540b803119401814481c02c41594000b0f2001207808100346003514007071401d500009000e500c070030b80b01c030003034208a80395280c11804025842941f0881c10020f000003002440131442c050385c51401569010803021303889107040c4a000300750400d40400308110060481401d001660300510040b00003410606c18401d020360103009203600309114071840c182c409440c000c001d58900906551a030b258200c01d915800c007510a0010b070001410f0041034803d11a1a4108156281d10a10411000901901c0060302200865400390b001c0d440650302d00e40341c0700d076607400c12015160484680702c0d030f030340c0c1d80409107488480c1d4451500c415500c04554145460100903920040100420070f00512800304911300f00c4410100301c031a446840c03a00d8201c091903010004030314002e4051001000c10806441c4950700540d40c40c000d601540445003103540c0b9a8a40d001110500900303000400111440d0141c6911620984144040304038003404680c28900042c4c0101c4480440303030b2000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 67843257 1250 67842007 67842013
    0x3090611270306010b0f070c03020a0e011503060b04060c0309080316060f0e030a05030709051003020c0c10050a0c0203032205030f01020309070302120c0405070905030c030118060c170702 82
    0x203070581c0c0d86580015072003011800f0f460350b03605d4100070040c0c0d072150b00c50b00b03600f440c4006800c408000400151001031a0060518000c0c0c0e901d5040c5030000711030038054050380d24440440f403605644a4011001610820100d442c01c05203070601c20f440e40d00c801902182406600d410100300c402d13082002e41030121003014119418400c60402c0340c00c403a2441c030780062071420240581c410302000800c48040718aa40b81940d603c1d43c507010b0890f20f4550642000d94850b0b41c024000f000c465058018060400140e0103580101c01d86130104440c0c0c41000e48000040b90043c0b1030340c1b1a187c000e19203200310500240949103050b402071030f56500b4a03000b8061804030441107400380040e013020000003e008030b04600031869800d10000f05640d644903840024440e90000400c0302411605005075185040003420910503800d2061015200e2449070250078060700c902d1050144524050050a03540c4a20a00b51080440183c442d50043c0c503079200c0d59824011452040c40034401c1d40c4503114851807450b405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 67844507 1250 67843257 67843297
    0x20c01052401031107030e12010906020d0612050705010503071709010c080c04030b01120311010504060902011b030804080306190312021203060f041a04091b0501090308030703090611 80
    0x3001103421903039000d20304144c50507000c0da403440501c0003113408058240c00c00d09007105182000410340484000300050325401e00104a04109482d00038012044a507a801c0c420300d5290599900303010241800940968011503080004d94010301c015600500386140009900e4023060f17005031040802c0c0c4210100b41e6580050300a519480072116400c42c05103003003e0324252440d1152100318a0600039804030300456a011803c1502408a02c0035003a41c1000034009403420f4103140c401840034070826800303d20742c9400c000d00c9880000d09003201d00d90544031583d0a4840d0b44480d07506800040c00c140e00b00c201c0c40d18400c047c0c4681c50020004500c1a410b503000850110002401d101c000802008881003d2080c00010b680300e12188000402c1030b01c000440c0158222405c4000e0003d10403150064a8501d555050054200f40c41c401c0e030600c0c00588003280d40c2c03000116518003e521020b810343c6000c0c00411303d4544203412441100d40107040200341da5030b500070b0a940c103902c62664290b0b0440c0c0790b40c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 67845757 1250 67844507 67844551
    0x102251d01030c0b03010501051b010b0d0f050d051903050624031902090d02090601020705040e07050102010b090403020706180504050109141005030d05090d080a02030304020306090102070c1701020c0105 89
    0x291a018003400d40b591410740d41f4150020b440ca015400c40d501c080c43c91441c41d12800c050075806030a11400003000700810441d5420707e0174001d6034032074060f03a5038040c030b028503280140240219880b0813481d07070624540301c1104c001280105406070101c1e912080d06c51020014890141044003c4507030a041a6501e0a00d1040e0485600d80000c0004a07507005006088003130b40c4460185060f5601035444000795965030700100d040900701c0d004560310a1401a1071840450000740d410107a03074083e0020812140c84100f0084480700456000b8011f91020b5018481a84107a9030341180c1e1100135041100c8681350320025094500980000c68a140e852040344402d85a05910030b4110307070f8400d03048082c4c0c0d0170540441d8840c850340080a080c81000100312425403146c0510840303860308181e48645540010074003d40ba03500c1914280d1180c414000840c6070007106200700d40075254000e2050380c1d03c900d010024001c175821170b098080595424003141c140c10740c0138000c0303c1c456403905507030032804c43c0c01d44c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 67847007 1250 67845757 67845773
    0x3020a03081308060402090a09062d06080601030b0a020901050706050c07060c0f08040b101206090b0f0c07020405061201020310060809070b030c030a0e070801290102251d0103 77
    0x143c81207651390b1083d400c1c003002d0384034084a26005a000f1501040919541c14240003400a070b611112155801e084c2d401d11111042e43d000d04140340350303002489590b544040c4180d484a080c040070301141c1e41c00c00425034001c0b0a80c024801c074107041c1425410054551900030032200212803100076242d0000315881007181078032481c0c0302075070391303080c1040902c1d8600001080303040001c03c01407640401038041039541103801030010081c8145c00c5030550080b4940703001c0b40130f024002c42c2141c120550300d0116841c41181f1100d1031240100748042d50a040b800d40821000e0a8081c20752600900b00562040c401e405c02e000440c41000c0314010521501e2801d500100451002070804481303412004040c0a45501c21302125044a9010301c0141c807a1035030302ea0038004020551058030144925100050755000640000307220345601514102a40c00e100382c200c22041c4000c8030700340180c00081000032094920b0380d00315001603a070840d403010280c44034048101aa45151401c3d4942d590500420802200d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 67848257 1250 67847007 67847009
    0x1e130b030f09120703020604060c0207120c1e0812070305090a080f0c150405010305040c08011d06070e100804060603171e040806010302090a020c010c0c0201030b09040302030a03020d020403020a030813 88
    0x203000f029240c0941a20025250400988010822501d035899601c2c0e0610803c159030140c07c13140f032255220312907860881d910301000e00ca40c202480e0a450588149411251554121035030704020340540b0501340d40d40314082d40942001c80a01005005880c45500c41007407100240440400803d210444801c4039441e10861094041c0b10306500000741b584480c0c410103440c1118030a080214083d2590f01d089418100385800c07a6072650300c0d000c0c0000b0204529160703100e1104202041d81e0268407601341c2150003003801da0380581c2040c00c602d110a803451007140c000b64040d01a0fa00081d002c0c0d2299a24500b41c841d508a0300c0c02c444000c100c0e546914074916440000e4503503043d1007441c040c1b6003c6510f4071070005100c040e20584403500020010ba01f9601118500e400140080082401001c0b0180c84d1a80c40001640001e180060000d03060420f500c020740134030303050b80055040850040d01207003e940030010710140380742c003404004016120b0b42c5110700039520600f074040d207403801500031100400003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 67849507 1250 67848257 67848283
    0x30c0203100515040915150e01060207050a0312020c0409060c020c09060906010f0c0f06200a141b030d0b040e1204050103110405190303141e130b030f09 67
    0x544803d000420804401d2804004800e8a02180b000482e040003543e462104802c032001505080ca85414003408100303010070381c0c0c5c02011601d00e03662501001c0341e86e403a650290640205400409002180003d5a020010406441100c0d50200e00c0d03800b1500303a803680441168082e455442c540300040d01800210f940007016282039009250150018030b00c01c0d0701501060502c000815428101c0b80700b21100c6902d0303600f00c0366100100c02207182201c02071544000003104414281281015916200101c4d40d610b41d05a841c020584454110b40c80340340d010100a150150b030040801444940178000303800103024844000600d5801e260a1006403030040a07a0081500b143c44118200301c0030009940a482082c80c0001e140500c9020360080da12654005a40c007030411a024168080044842c0c025680300360b0301c42c2800002c07403120031170f203000e140200c01440c0321480400012800c1c100141140c0d442010410704038a50f100c04048c111743c8240d85508003034158000f0800305401c100309070340342e03100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 67850757 1250 67849507 67849511
    0x3050106050409110909010605120303010f0914040210021f02040e07050901090b0904020409050a0516030e150c070b070507110d0f08091f030b0307090e0303040f03020f0a030c020310 80
    0xe510f81e1350014854000b81c045119a5074480805d40d518425800340d0090080680a840c44c24400580710356603130000d03c01d07062036012340b10011440d43d0f5280240c0e0300f4203010102c84041900e840d070802111414400841d02144191700b0105004490150100701c0061040780044c1d403a410110680b00c01540200b010301405010040c0c101e050f40d1201454048881102d08140c0314894403000401900c06d60740545c4280d400d11b400c2c490b21070b02c07650000b4040c900400300b940414488150503030580f070a00030050300c0c50300003c03100302014114800e010340c46480511914a0700c800d07582c9200141205503044030005201042500c1002004401460080c03011510021406140d81e200000b07900e05440051003da004121581c0e95110440303452070b082c4ca80c101c2e180d500030071102d00a000b0725442041d188244130b11080020b02240c548074a1400c0e4002d5805507145039210317140e000c81d100301d00e6011411071242c118110110300c0140181309042e44207554804c46c00c2c40d140101442c4c074107100c4030454118 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 67852007 1250 67850757 67850771
    0x50a061a04080304170102041d0609150a061413030b090706080903030c0f0c01060308090414010509070f0c0f0317090d0903020126180708071404090c08030d06030501060504 76
    0x1002c000252001c40d101000620a18100d038a038690180c061907101030703a6900f5094800c03000000d60511184107a0068034404429920203d40c003110038101031545401410105d028000d4031b2082c144802940c8000f01d00074a8070814807140c1e03004414507407040c0d501942031824032260321014880b200080a213407a100c00281449a40f2907120302c4040c100380e40c0080006070040c908112001516002c8140304020002c0310782e00d00b04007045070310010101d0305c2246005801030600441014440c140d540151901c4010740c0e59900c203946840403540d800081c0640c1d103006000140705410700c3c414a0b4030075a0b4030160507821684003031000802600240c011341200302466003150740000c80404407902464882800d1100d020714001d08602c000c3c1240e61403202004001c1800d02c540a000007228203441140d48081d0303030f0a50913859001601070800b0140b4061140007441c500b9030000442e55014203441110303650380e400d0061442d80304c1229100303d0f41d00d4510400501c0000c0c8030742c00081006440030301c07440d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 67853257 1250 67852007 67852019
    0x80304090506030331080f060106110a0302060103020f06070206030403050408120301030330060b090f09010302030706110c040507030e07140d081b01020f0403060c0f0507021c06050a061a04 83
    0x41c0c0d40140e031380c40c4058080c9803491406185845c070b580c01001c0344001e90340d0010301120056201d9000b4010351002c9410700340d07a400c111000241c1c00d4130141c0c055020381010390841c0c3c204600321406124459001005002e10000350361100000c5019501c2a00c2d4107070b80340d10f848201ca0400c21404101c00b0092800d00c01040400d410804161304500f078002198042001e603507203065051840201d840416140080214113225444018581404110340141d41c009030b001c100098002c090000039015040b6030810440f050148400c45448105903082d20040c110041c00306044401c102c81d00340001c0d17120024296200b8041c82800301401c1c060003201d40690141c00070400c60807900382e000344409000140034814802e02603c00f000b9400500003903540f100360712000740c11a00315010a5640c0ca140146001800d406078800071150301040c0c803840d087c84456003c000201404440c500c0c0e40240c3e11084800003146c600c5100d10800403420001406400c03c9541160001c0342c0c5c4408031032640c100828000c1b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 67854507 1250 67853257 67853287
    0xc0305010b07022106010609030c0503011505060f040e0f0103021e01020303060d0807020a03080304141b06090103150b0c010f0e0a0b1008030c0604061a0a0308090604030c0803040905060303 83
    0xb0785a01500c44070890443c1c0d407401e0080e10080e80c04c1d0840f40c05448008104a0380c001c10040c100c901a02d0007200b900d4540c400c150032151040c1c880410314988500401581c20070401801c003a05400c035610707080c10340e00c0c40c1030354070706101b02c40c6084a403140b05c00510440c5003214920450100300c40c44d4040031180c0b000044d40c1c902c406400e40b440b40c2440c1c00c0481c200a0031a04550f0800e602914140456540b413400403c19041582c048581c42484c2d405441026800074101070354030020318194850050700d0302440495400110410b04241d220041403400c0860707003611800a022140419984001c444140d038211f50a8040051069080191a84032064002041c080b0240c00c6924101c003500c58001d58501b00e20b2650007403141c0d0001040128031a480420403510030b901a120038080c026400030b55a6440c044418029407100102406202203020b040190020442c041c0c415031030603880f0303103641c80112140c0e07220580a6000040c01c0c0190201d90081c035401a109500a504100f4031103d4017170307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 67855757 1250 67854507 67854517
    0x15010801140703110705151503030c0a03083304060803040e01030b06030114010e0403080112050d08070201060b040b0915070807060506030a0803070f030e0c01021b03070b0f0d0c0305010b 82
    0x200305500c4645010240980100b145c1c2e00503813010880e440000c44480c04c0c043d40703d04403012102008a041303400d0081c2008411540380c03240b000050f203401ca110356800d4504c000040c0961600c0e0140b80e001c0002e1422180c0328851020340e50f8031844040414404000032380d10b6503004225113400c144001c0040f00040c010300d90660341e01c02101e840e1075039000040384c01007070042015421828074900015001800640f0b02c0d0055021b5501d0034680e03a00c84111401000500d00024110b600c080080c410007031082c40b0103604900d0b144004143e2550783c440c007200a4005030000341801c0c400188040072490f0a07070381d0200d2340100794240c9007071112030340380e02500c0d004079100500320503101c0b000250655401d20041c1d94150f4801c40098480c101480014074410101c00300c1d4010914154000010900c005a00007402c00140c1c0101203030049080084c4110386111001c80e0540f0590001007800c2c01c02401400312100010800c90311f0744588620b007010f4902181c510028140b4000042c4180e41c10842192 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 67857007 1250 67855757 67855771
    0x3180103020c0102070203062406031b03040f1b050108090c01080711011401060e030c0301090809040f0b12060403090e0403120903120f05090c1503010e060307030c0303021501080114 80
    0x1030300c80e0b10314940a4068418110025450b004150802500d44804a00605100c1e0b6014004803210201c800f031041a1200303490700d204040025403800d0721290410f004580c01442400c139000994101d41e542c1c1c184141d0700120840020158074103100d20359202d50301980c484000c200401200100c600040d188120180c0980c040052042c40300030351020075085100c52208110444c00950781d181001860248681665442405103980f84810b07841d0500500d5203141e001416203190104a1041100515690035054195504c680c8503e86607910328060514500f00200501001d00c0c0601d001405006150841740f400031881d01840042640040c0444074000140c000083c0c008140c2820340e0201c8980e46021201810281c1d6035006684640040e03010b90301e400101c4041095500c1000320b204d40c16038542c4211103042c8010010a074100b00b02580000c805429502800d0b129100c0f03150102e4250016000750f03000c01942d210801c410750485004102450080000000c245000d04189501074407031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 67858257 1250 67857007 67857011
    0x109180f0b100b0406030b130903090e0a0905010203090f16060503060103091103060907080f030405010c0602090f090901050106080c0c061501021e0a05070f08030409050411042c03180103 82
    0x8180303142c0524098040e11144581503126a60313614028050044000c00703500851084800080c2030426001d15039034260b16888034003105043c41070645512000a0900c0c0320f09480702d0408000c51000e1009600540c21500601401907402c0210780c5000705d03003034861000d08c5045c0001c0003001c1d80b21059035040300702407030003191200301030900f44803006040c8201039240c041d44050201e503a000150010403558064140d91080703040740600c42d180c5c000da205840c0031070031100200c000100c0c154002c0c083c0940c0140310500710040140451483c0c03904541102c2d142c0c0d510001444256041440a44e024028080c0e991402004400c040d03203440e0b0103805c0c00340c1250940001c00850f07000f80240c16200c40d076004010414084440081d0381d96013003190960304ca004029020580403206580002075031400c0005614162910406134001c00e0000c1040e6201a000c203004690755031039010348240003107144d40e5040d0414000c11244415140b801c9a0a1558020407601052520032005010455024200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 67859507 1250 67858257 67858261
    0xf0103150f09060c0f03200d110d0903170c0f09120703080f0d050108070302150d0908030c07030f03090209180a020402040e09100c090510050712080109180f0b 70
    0x5a507002c0d1803200c4000744850305140c03850500c035600c07100344404c038442c695007030014052010b000c400c3c0c200c841c5500302d0040f01c00c00505000010303c2d00400c0c5603124540b40300d442c21440000203002c0700d842d9031007100054502040310361401c03040c200890308100c0460b43e2501d80f0019100d0000c603480f030b03410080e0041580060051500809004010003150420300d52607542e40780c1e900300035859103c003040c04a075601c0c050000c502280700040030010750740d026107901601030140c00244043c3d080490f001400381e84901802001401e0b1002843c05240000d613940e488424515001c0c01c1c0c1c07a640484241010b18000091000d41d46640f031480e00009054100304401c1281d4515a00340107040c0e1000e5041400068001003030041c0e451030074800ea03c0e95041d20b00540c81c448035101a80d403540c0f01a000200e1000c0309110914004200c45c40f10145820000e00c0c105032940c5150a030542042004080b42c0b07031034010030040c400340c000c007000111101800700320100d0302c0e82c420381c4414070540058034600c01500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 67860757 1250 67859507 67859531
    0x1506070203060c0a02010609060f05151303060902010e040203241203030411041b05071101050d0f0c0e01030207020a09020304020111060a09050705011d0108070302090a0803030f0f010315 82
    0x85821454010701a10914641446070a030190701040c2424010b40c45c003400010b5811442c840e11b03043c1c8010003046400e061030b050030451600c0100203004c60b0790310100140245000490f842000440c030480000c030748107441e030001415030303400c1c43c800c240114010400c11208040d1005d2001c00b450b00310200c0200d130341204020503170041c252403042071144000014030040c0103414064100b414070444040c00805142c0b281101d0012011031080e0100c2d01c10311806000610b002407044d03a50f1010b145c40b6040414102840b0b0654000c1001048041d80c0d4420607030f01c140d8480300d202034808013130070194034100c0781d540440ca0032070662280c041c0d179a50200c00314046a1082c000130102c050b80408071405810000340f80341c000c004e41c1c58211400d20500c00c0c005042d50107100001c01d1505100c5100104040340401920700d844010328410801d87c1c00c0003101500d035100b800090240404100031526460610400c8140e044042c180d0f8060441c1c0c1001007001440710b03402101d001a604101082c540004c3d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 67862007 1250 67860757 67860769
    0x20604060f02090607080d050c0f190c02060307030207051005010506042102061201080c01030527070902030c04180605030a080f1e090906010c1e0201050d02030106030c140a02030315 80
    0x4140260b010313000150880034000700d14042c080d640c29034081001161100c04035089544107030281c07100711a40c1071007400d0000f034081401c0d400c01009418014001002540080d00c158003c42c2c0500c086035000c0b0784001889020009071250320284581040b0650400c000106140180c1c82200c903510407030310b619445145013039041a04a039016200d50b48400110080030024070003401034944a01c03507229186480e40c070034003070f6601900342c9225090005543c4d514401d00316440319000182031007103020004a000381840198490800340810b10740b00c9042c0908030401140c10411180f0b0706040400901c0566004508040020f030301c02c4000f542c0e01c2552901c102c850255400d9810101c3d000301c8040070000c0480001d0010b0f0b00c0449082e03a542c2d8030100103407400b03614408090079800b010410100020790903220800c0c828014140a420300b20350000714000d80c0e00980080000036100c42c02d8a00441e00054100e400703003614200c490600140910081d41c81c00b005085074039800001015081c44c0e1a00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 67863257 1250 67862007 67862017
    0x705010b01110705101b03020a0201081b070602070f0f0506060a0503070f06030b011107090c0f08091203090a02060309070302030f072d0e0403080609130f0605060105090a0806091606020604060f02 86
    0x4240c020304041c4d62800c000c9e40b2100302c00c01c242d010803800d20003d90100c218065480c01800004105424402141c07200c0009412000b411211035840f00440303804628820504086a0301c904014030451074442c051001e0340c03030035030301283c005e0703222881c103000780c21492a2890645405150024414602d400120380d0410280030059242c000c0040104284002d9000000b00403402d81301c0a01103900d0080895201804a580440a4010780030a008012801000b1170b00710241c03c0454a100090780c000807403540c01070301c9402c80e0303910a0b0010800c40c00d041c0141d07c0612110303005040041e00c0d29100303407402044000755400c0c143c1001885c81202504110420141c222800e4900c401d140c90301e8050504441584d03014400d07040040040c0c1028040c40c180c4440c10ba010581c01d640003400c0c0d403100042c000182074075042c0710060180c40d825880c3c1042800003410320340000c0c0903a0500c01100c0d41041c0e0010980320640258a009028282d00014400d410a500c00342c009640100c0700042c0b402401a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 67864507 1250 67863257 67863287
    0x60c01060b0c0106080105010b070203191112061006020105060913020303070c030837031104170a060f0b010806010e01030e01020d290d02060c10110705010b0111070510 74
    0x10100304001d020b08154001003e6620580003042180d880302c100c080207001d140e00c0298542d001c9111f4003c124000d00039a00102d200c0c000341640d0400041c00615072001d0002c8240882e400507041042113440c04141000030550b90000704800e0408101051080100400400b201b070212802041113440400031209400d070003401c20000d9503141e19000c4000d0344074100716400040b410380c000020001503100381008007100300e4450440440e242043e8003408074503600c061030403002e00c4006584100c42c0c0789442714107801000350440c0c054906c0d00b0b0f012191002d201e030348400d240143c00f03109a40c0150b030f03a50300800c09080490401172000300403005803240b06403d01725540003080c144035140385074101e2003107190000c0403440307441c44110240640240c840c51f0164020811644000981000002020500041016140c042059014680543e00c14410b8241d2160b400108401840000c0c0b2031800c10300d400340b81680003501e44422896440456000e4544244c103000b4440301c20310f024201c40412002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 67865757 1250 67864507 67864529
    0x6120912030c030a0c08010b04270908040e0f0103050c09091603030f0f081b0f0408160512030c0c01030507110a0807051e12070f240f1109060c0106 65
    0x58440704481c1140c03c10b462010030642000c005602580c000e100f00e9041e50500348806040c80c0c940034240b107155001e41130a280d490000b03036104440d14154000e13000d04038002c0a1965a4600d001c10808610230001d2002811120381401880010008201e618500c0c0d800c840080c0c0381d4440e90507480c00d09484820012356107900c2e241c00001c058000d1000f04c004005c40d1207501b54111541c80c143c1c1c0014040301c58808802907034030b07881192115a8060100002440140342c00c0c141c03201155440c2114016500308415441c507410800e6150a00b1419160960907005d11b05000031030603810382d02d10b03500b4001814181c81e14000345a6510034501c110005005c00100e40240c0600d003804d5a00e5403100307a00350346500404c2c100705124081c1040b02030a0300c00c81030040200040c51302c808030413508040b408840d8604501d000344041000c41090300c1d6400603144898a042d0504401501107d800c0222514081d0800000c51444c40700001075408840c400d441059465141c001c841c0d00528081d00a240700b82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 67867007 1250 67865757 67865761
    0xb07080f0d0b03010605010512010306090f0203060106020f06160807031a1302071407030b010b1c11180306060d030e060708040e0f100b0403032709091e020612091203 73
    0x300e250740114042c80300940c000c0100c07070b444000440f80780c4500c038404800311422800400000d00c5950198600074084c1c03001840080d02340d13000030f09180c000e03400900180e1081d895100e5000040c0200c0b80c1003000040110380d0145c1c2c3c0d4030003825114008007840289991025018001e00c0c510544004001004148600c541c0780110401c1c0250000081512a04620900d405444200150a5003034903042000b10740341ba86803018484042d441240058109100148203080781c984500030031078509102c0c41d810303842c0e4850b02c41c070030188050b00c5c840034481e40c0000240b02d0f0648407802e40302d90442d0146002030005c00c0201c0414400e200b02130006240130070010b000210240e03010b202c580520b81d062055109501c60003a505482140c40c000d00f051780c80c0800003080002e00a5101d002207240300c85c0c260b10090100031017168100d41950200c0c41158403090b0301400c011035a918407480308000a0030701d403c03048940104105004082d9055035032082600803a001080400c114454848211072503aa02c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 67868257 1250 67867007 67867027
    0x30c030f021909090203060d0f0611040e0906060a06050301060f02011d06040309080105040803010504090f1407051302030c03011e270605010206090d120b030304030c0303080c070c0b07080f 83
    0x80c1115240b55000200841400303d90441345000303c0e40142401001c41411080702d0300c1300040210784000403115195280300b03890740c040001000d03100818401e810502c80d440c08112103428030100400c010f1003410217420510203a43c001041c1d0341520018540851030000100050380100302c82c2d408100c021203102e40344136203180c000408510492003070741e44121403aa80c1c02c4d164269041905c0043c01070307805100502050609900c1100702c0ea005400210700704505440e280304000e06079204c1801600085070038040c500f4490714046520400b50300c1103245160800403400b0501041c090014400015010104800b081c0040d02014000001c419004485159070502001400100004d1400c1c103101000450b90700214840d44200344d00d40207031030899204203040f10040070506080a4040e5038009007007540c2c9080014202561044039000310507411802c029103110340041803000301c0042049602e000030004001007044800b00500c06440b21290315100702c40c0d01070201c50000d40f0074042764202a07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 67869507 1250 67868257 67868287
    0xe03071211101404031203110a090503010c050c071202010203070c0e0105031002070b18120a03020d0e010905150c0d02030901020904060503030906090d11030a0309060207080c10030c030f02 83
    0x1034000440d00028100d020020035a8000d00022400c0b1107400103000820102d41c14081801b07003903240c0e140004d5000b1000001c00201c2d04282204000154036000c103021506007442552031080c900e0500904000d4a0848580d0311062400f64100318503419071454110390081040e1a2441d81c07201108a54580361690501b5810003407247c00e10a20075504812285c0800e8800c40d4007581c1c0052100c00c076940c4da0119103021901841d40450306110360385514181701d4091000d00304210283c1d9025a07030311981941c110076640c11187c0c90074103902d81100365001540002d401d84580c01060310208180d0340315074110780203001d081c9101c100c00e0300020030049141c60640c01428200021601000220b07115402e1565a00500080fa600086d08204403005d910b400d005d0341c840144102d1b4041e50240d035a82c003082c2000d100100440201e01034420600c440c03901400400040d10340e80c0001c003040c440581c005640f81007010400c005142e40e036081c050156100360411220307803054031002e540d00e5a0801300259 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 67870757 1250 67869507 67869533
    0x90f21020705100f050c070906060302090109052b08070b04030509040f06050a091503020a09090b070302280c0515070201181104020306031009060c030f0213060e030712 74
    0x20040c0140318001c1400d141c4403600c6058094103590b0800030b0400c0c03060558a5a000a80280d06445061400600895580a550003400050b40e0158030b803212040050880402900482c1c41200c1140c00e1919013084450b507030303d0000000d005880910118105002244240003018040c2c6034080100070030300d80c1040c000e140c2c3c114140c0303040000201d080602c02c203d60190054503800200c660082107055034941100c10301200c07180c01030540b0b596984c00261581501e50123240758503150b4852509010342c12003d00c0d48559582400e601c0c010ba01e1540858600018840c0540c516000301c0880074144652918007030303194400100d4444100d004044c001c1010200d514900540c20082104040903407001400031240c0c1c40205442481c0044082001070b4000414880d05407017030f91062840400d044c0100c03984140900000600c0b02082030000302590015195020910300400030b0100f414030700030030301085900c0d0b0b182411782c03160402d0000f41080140e910101e00c0c285440c640c0400e2100412101ca = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 67872007 1250 67870757 67870823
    0x2070b010e130314030a02130905060a0b25060f0c020f0c0102070f12111c0203010f0207080d0c0201110f040e070e0a060f0921031409060904090f 64
    0x1140b40c1e6503030703a4103030350009002c2c000740015240d03418a014456040c001c0d41c0c014440000250074046442001c0c1103661640d44080c200c1900e4000340b06050a0400141c000f8080c4100003915089030242c040305009a00700c81241440c48008001085c0560b95000c0003c0c50400705040c003100d8100704000750764004500800c5120700844055180300c0d800040c641080325010013402215515004003183d00c0d40c034050055800300b21100101c00183d030b88c2d9441c08007409400060710500040da00505007110041102c05660502c10003850300411000000c1e0b405139a4001c4010030300c440102c41c00c030b01406143c022010b402c80d02091940340c050300d20300504250380034034002031095607501328111160f09207014429040004000c0070300106201d240d4030540000325041107d40307680d0701c8080c14400c560318101c004002455010a0040541c030401440c0900e501e0703c030490a02c080980003414030f01c6500d50240c4210354803624241080020540d403000703250014521810740c2885070000b8494a4904408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 67873257 1250 67872007 67872029
    0x207060509100b0303090d06020903071212080a0c0e040f1103102301050a0503130b0f09060f040819020709140f010e090304050418050109060204180b0312160602070b01 74
    0x30030241000170996800c49801003e400c0e80300015100c0c0300007980074200658160284850129a4101e5450b42a980034407420049481e6101548002c1ca689000790200140f503040811482c2840e40c40710585080700740440300010800702d6030551200a188901c00c60512080210820161a01341201c0b10f08460701c2044054900351144100891103480300800c5011170303020701c24000381e0f911490203540d104805080c4007100850540780c006d420326003100c41500c1c8866810810420300b00612160760403561000003c240c038105680e4191481c015265003800d052202b50303110300898400c01c5070f40c0003042000c20410181e2648440c98081c0c3c0d0f022124858004480c100005004450015841c403039034503400034604280c245801c10024000324541c0c51806080c13001c406c0e0101e0000c0c810501028810080180d460745441030500c0c044810740080b040c2c0c14038006c003110041e1800301d0498941044868515500c2e4108500e00c1004004804058a00d80c804a114403c000b600c4082505030785074040c00e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 67874507 1250 67873257 67873271
    0x15080d0f03090b01030f020a0902040b180306090d03020d060504151406160b040212010c030509070f0308040e091606020a030216231f020105040b0703060312080a020706050910 77
    0x1034040d60202c1100030441c5411100400205c0c6c80d0445841140740300030003203043d80742e490f83c04009030380043d00301021048001400c0b02d245415483d0b26641c80c041640903002c24507101101030f4440d15518110814150000f07040409540030313034095405080000e000304000c080b59204905e0b900000c2c01782401c2418a10350b19566854080c05a81500e0f0000300c41c140c8414155484140c0000050812a0410300080d8500702429080c05003032121360380c03968001411300d0304624403850010b0f141d1207009150710082080c000300322071201321f03420340b05076086141e80d81d120004250b103400082c60b81c0c03400104c004140440c0041d400b08120b40164040d5084613641070317038481e01c0c44180b00203120f59442c00310a0303644035400c000c800d10000d0310200d00502c40c2066103000d03007096100845442103440103035901c0301040104048039121a07004503692404101d1a800c41c0e07901c080281030724402c01d05100002c000500c03c90b18075012039102550245d02070146007024041e155903411011310b0b040d80c0d07900f0405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 67875757 1250 67874507 67874537
    0x309010c02070f06140d020a0c1b05280e040c1e060c02010c020312031f17060402091005060a0905130e0d0318060203010f0501110705090403110115080d 67
    0x82c11005448500c10014142c624020302a202075440c0107611aa0746400c3c04a0005225548040e180201880d180c0130314552442c500690000303010403501c071010b400303100207002d81d8640300e4018003100866405c0340e41d401d420b24007400101d03125510840c3d4905034078040100700041d591041081b541e106080444460003042003040d009014002d410004003201c0c0c1200140d845180c00852541c00607082d41c0c20003041c111030038280d030301c215003c09405614500051042000c1c014420051080200001303201c0490192140c9504001e48042c3c49404100c02040d80d4940c0340706103900402c3c00400a90380c070408207034068071701c910703d11520703105040e411200240000e80b801594590b44040e40540110302911405074020405442100d6100140e1011030340080c030644003c4d0701814001001008551a0100040c03d608113651040c1182d00f00c5042049079882c2c040e10150400c2d4142080d00c100c0341070300002401800c620700320725903001000000003840e800c04541c80c40105610307a9048000e06140c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 67877007 1250 67875757 67875763
    0x5010e0f19050d080a0f06090c0219080d05100b0307020d1b050a1b090f0207050c0117070e120610060f020a0305040509060103060e04080306010315050f0f1906050309010c02 76
    0x1d00506941c002c40903407030364a84a00046070388a10500030004550311100f0040d001c442046d08084002650382418060040c0c041185401004240c016012081407030340d00c04c0c0840c041c10020400440d26136020800000c6600c00c07500203007160040140e00d92400c0e5100a40e518000032003140451504404031f800000020201000c60382c12000070311581c4880c1e0b5584001060507008581054102c000c0840c80c605280a0b0098075480c0d100c026844001c0c504005007440d41c22010541400418014044250050b01003240d11100f5403c10071801c82043c8081070b824555400c007076005002d403404228402544840742429076140d0b80d5081d5240981c843c042c1d81d254202400940421803d2004000500d0300c040a01c0d400704d418980070071183e43da8206041c845105480446002c2c1c0d01104005203540c2c54460070701e5010032030710b07140c42d400e00d84030100c3c2c4607441045089008801e03031081c00e4190344035030028466808821508004550b660380c00103002d0b400517203a546095080c03142d55403820b4800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 67878257 1250 67877007 67877053
    0x403080307050711060301060c0312061526071d0105040f1d07021603060504050c03030c03030a0c0f0806130914030913090209070f09150504031101020601030b0a02090d05010e0f 78
    0x2988412440f05040c0d1402d88281d0041c880400a1070b485a80120b00c3e203370301c8102d42c54180701c40e49401070400e04401c402030909000045000708070f0790100803c0450340e4050600c1d100303a0082e15017011180c4510004882e04e1040d0380158444031682580001c0c89020425011071007411103000d001076440e2608100e03203030f10081440300c5030074142c40c1082c008120035600403a001032160048480c48a10200403a040d07412151410001e41c0002c400c1140504240c0079a94a02903070b4036102c6032a03000c0f100042d201303001c007801703041c050480c2000d459900380866100da200c0ca17800c0340111000d010042c8800c5d5803a40400209400358815801c04110304842d80200985150f008201c1412650b03901e40c12035240d10455054410040c10110001f80e00840201c442c885c1c0449690b9641c1d1542182041450700c21401141411540314400400106900c8201b207038200000e1b00d4050b0740c0314001c10020310f400220320f4014000b9464210070800c0d10b18002000904400200d0549075103080642d03020b20a9914 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 67879507 1250 67878257 67878269
    0x20c0102010908031b120a020c1c020304090c0507060608030901031104030b040b0702030708030a0501030201270b160605010f0906050306010e06090c07060c0804020108010902131205030403080307050711060301 92
    0x24400300d00da00900d501c804c000d01c5242120700e8101202004451021603064525042043d4006012500e501040c0860808ac0e0380442e58406505c50070039000f50b40344207074424055a41e03035582010504a104404850341550803900501455448401e4a43c8a80c403912549011030314184010405003c0b08051314200c07038001d80d90b44843c4c2d030b980d1a0026000c4004120b10110700040043d40b0022f61344d407000c2c602070300d442035000803036604505c00500001000c040340c0090030300744002240c0c4000400c55450a82c1c00361121182c42d581e000001d181181c4810100810982c1840000b282a8240c0c1c0c02c4c3c81c045a103201418066a80d41e40c081c140ca5240a006e00090a5965000500e10707050950085400c051018001450060151901c50403110250414800145c4900902c0b06641c2d2103410036000d0480c14804520b410301d949100034182c0d049100c0d0b6904d2813a91424a01401028400c0c3d074011038000a000c0d5a80c507204800614a0b882a0000c0b1600e801c0460341c0d09890629109481c1a203032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 67880757 1250 67879507 67879523
    0x705040e0307060902210303040201120207080306010e061614012409020f0d091208181e0106080f031c020403030f03020c010f06060e01020f01090b130501060b071101020c01020109 79
    0x94162034090103000711031403c4c0c3c0c011b04030b0440650070504210a04d000c1254140156440c0e003000d10004109900c490000f0400900500650000c0b0315418102c9800200900340040c80240712004102c00380603c48606a0303a8401024210274082415811209040d0344402003007400c2440319242410074806c40d00d040740b021122414032079070f041f84e8020300c0f1040725035000c03a061030201c2200c0000d403090b081003202c00c030700c0240c0d000c403000d078018a4664021070051586504002030301e40c2c3c2940e482001c1c0e4080900c00346c4203104107601c002984003101802e80700d07081d034049001000000e41d403070b4071203800b51b0304841c803500b000811014944241c809482e41545c581900556082c000c60183d04120506805956901a01c50383c4038158850303040104550b0303c8036a5103185090000e0300b0500003880d5100d441e41808180e07000601031048007540305000e40600003032420b041c20030b140185060b80001038414070000700390060245403031a942610800340d00300e43d0307860074a400480c207030381c0140300040a0794 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 67882007 1250 67880757 67880767
    0x603020103140115140903011b0206070e031f020c030a0306150302030c03060907030e151506130302040207080d0908040f150c021005211008060f0a0507032a020705040e03 75
    0x2d803142e020545c0383c512042c3c0d92420001460f00080c21980704454801e5480d9020001c854002c2d01444201d600881c1c0b13080490702040c202011907103d01c07103c01154200c00350160401445001641034541c40340e8008100ca4882040940c0900242014080c240601154000c1342289510038000c07240304068580f80e050954880000b03120800d803002d080402415220242010f1744c00082103140080c3d80c0004090b0030f2030400007290000f81c0c2c130009544e03018400800c203900d00500484000401c89505a07401665a001d40c2411002402001d0300040c40a08162685040c0300140010b801038840070140900c0c00f80e070342c0003e44103404501d00f40e680468030103952070003d03103488220f00c5208103e50a0161030414030800042010751010740f16084282802e00b40084021011188005040d00720001d04a90605c1c4528020859004200038216030316880050100391107a00082c2d03840a080b014a901d0903030540080410b2407030a0100360040c4915040000c0518141c016a0b250b41d4001001d1440d00b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 67883257 1250 67882007 67882049
    0x803130509060d050609100c0c050613030513030c080c090609072111030a18050312040c050d050d180f061805060c0a050c0405190c0e120106030201031401 68
    0x2044000303108a510410f060302140201c0c10500c0441e204540200203000c03a15150740340041210a821085001c00c40741f14104400608001025a000010402200d11000b01442d00300d40d244240c3c1c050240030420794900004005102c15010150742e031a1007594140c450301d81c20f110100f1011600c490340003005002244556000384401e0b4002007c3d0f183d00c00c440d070100e8401500380c54415034458003039030000040108100141c800c008180e034141d15121600b4005480c5d42e5075a0166150840c4844084004181003081d44580c1000508000d01442c0303802400f4200785458181d600068408100f440744031081072100d0014440541e0b00801c3c00701d04d514101079040b01d40b20f41c500400c815175004100c01042540c0c80c0300113030101100705402040c180c0740b54a03110b801d01d40b654055502a50600c410b001d0b140a1000a00c1d011040d44140004c1030550403500b01e88007003048501c0e5400030348407503d440000c1819009403040c2c0e4000e803000e11050300c001611000c0c0e407c0900c41c055010310381046900350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 67884507 1250 67883257 67883269
    0xb0603010303051c0213030201110a030509100c0c0b040608090d090b0f090901120c0b04050102070911070b01140f010206010e07030c140409060f09021c0b0303040906030602090301050108031305 85
    0x20400c003c813540381906290a0844080768040440d0b42c020301040c1004108560b80100441501c402c40400b5100260584c0d5002d42035000e0200e1062082110644198200c0d100b41e0100b9019600018400007090b522241c04056a210b40a554002400d080010f99451400200d0803046460741d80d50001ea80d2405101034100d03040003444070420007041182e4405030b80c84c2c40300940a030000c070034111a24003051505416800c04d07603000c0c12880345c092000300480d0b0303008a86041240c00041d0042466a810303960100b05200300701c00181b007115154000300c5e01c4c81103030740d507030503190001c0e01c401582c403040500681e501e0b03074244a2080c1c7c0e12ba0f918009090640320341c2204000c0350740c0e814210181c5044902100c1d207604503400c4080740543d0f810b000c1050781300c070070b940000404c02c00d03900b1032505041108440da03424056044040c110389840c008900341e1010800c071401810211820044030780c883c64007201a40c032040e11a4405d42c2494004100810040111400446032004401d80c03245002d042c080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 67885757 1250 67884507 67884517
    0x1090b010e0f15070f1127040209040c080102030703060807050a0503120d090b070f0e04090b04121e05090307140112090503190c0b01080d0207090506030a051509010b040b060301030305 81
    0x11140f1001d203d5034001907030100d06156014401c40104240740303810303002c2c032108500c1001b0380780c0540e2000d011030341104603c41c03540d0b03007240c0c05507001021a9940e061000650710b03207074000822988004104a40d4036419440002900c502000b139030f4200b5030341d0081041d01c1490b40a4560b050300100c4c640c0e09542c03040c20041400c001d2207040421580c103c0d848522802070111500d9002ca0110074880d44078a5000410b031415010883d401c008001903602e400c10b01100041c002030a05030302d46a5452601c0c000c120380441d407000a41c9000b08164242001041900500c40003406032003803030b0300824007580c032190b20f034004401a91400c8894003100070039000342208880a807410302042003280d03110360340302d010b00c040100e154440c0c0303405001601d0052241c1ca0140c0c0030043c1e0350031040c01010046c7e400701d140421541b640070086010340303400e40083d0401d00b070404018561310802a009803401c4240d031809114040c03001c002c00102e51102d00340426540d01a60f02c80d0f01500401c0103100080c01000580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 67887007 1250 67885757 67885789
    0x5041106030702100203041103120a03050a050f0103080c070305010606020309030601090e0604021315060306030515010e0c0d0e0a0c15080714030a0f0905010605040b03010b03030901030902010c050304090501090b010e0f 96
    0x100c100308c0740d86c0840d0500c4c030b1030569404a000000b841c1d0050a4060280c139411090040c4100316a10388880800c01d40d803410300008041c018001423030070140b0000c1103180091504400204255991a28040d68035805616900d00a0140380c0c000075403101244201c60b465a204005004503944603401c03c030241c0040440050703080e80d03d03d500d03143c403410a14404041c2c02d41e13850004006003103003440d603e01119031503805803445041c0014800c0e4a0103542ca01c3e0880c0018110a4840303031450080c002510903070540712440e03ca00c42c0c0d08010311400e41110030459802406480c05204c25203030490b0940700c1110940003180380f8500c03001d5107002d4400119071240c58030034001019010b40103d442a1001100155501e0791103000a10440c9041c0c4204070b800741044008210402c010350100e600d0b03001d0481c030181030503621502c910039640540100c0c1c85690f0321134207690396540c0f2036805400a08080c0126940a450440c1c0700405501404084010140060004196003014000c201c003124103540b500c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 67888257 1250 67887007 67887023
    0x11010e060f0f040303110c012001021c2a02030901050318010f0c03050901091a0405010b0904060204080d0e031506031603030504080c1903121709010504110603070210020304 76
    0x150101c1c80140c4090441c03880c0a0074016a40e62030b5080c0108901d44082c00d184503030304002403021a81c3c0e04900c0c9182d0b42c5c2358800f1000c2200c00403038005802030103040c0e850004e211480c4105a004541588a00c440c1c022a0a84c035000101541e00c0c04030040c45130342240c0140c0d00411981240c6d42c0102c001d95030100502d401542601c0e11440c0c654295401c0c00d144080282e03d0703811180c407854140c09407a6000079010000c10015200b5200d184198130203540d040c0d4114640303408541400001e40042c000d040300039004021500302450280d0080d403244c4200b03d0107000d1460000202481140c0c0500c45410050007040c03926661240e1041c0e80300040e01250b4035116080c519010078120350704001c001d42c0691100e6880300d1401c40c445040828101d2268800c0c2441c081c0f0340500303112802d002042e6071700b29203810880107031050309540d05441035410f00c00c8543c1708410051541d40540040c0d105910503151040040c04032814405c00d40003d44400015030065000d42c42081c0c850380c0070b554024090151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 67889507 1250 67888257 67888267
    0x112020301092a23040b030f0607170703060b030a0b030c030f0d030f0c0207030b0a150f030201030e0f061305070b070c0503060112021c020609090705180d11010e06 72
    0x1070080c1d603412010000000b205686419210100754480303c20080070120b07241008058a4035150070443c1400b8443d5120302e90318100702d46240c90401c91034007a00f111300c0c00ca40395410910b85c0070f0202003d02841c04451180e1500288070300348240141000c60708000f00e01410b64451441c050b010f02034458060380c06214100c031203030160b9410880141d09000703490142203801071201c0b000b000d4409e84040c100104e81840c4406000ca0b5000820000320ba030440050301203034640c414890003400040c0c40300281001c07000700100340300c0c41840c8010304581c405d880400064541528040d155003008e030889007140c012800280880003c1401c00501c184a903065810741602e034401480b40e41c00c008402c0d00e01c1030451409101900302000700c280980512903501da403642e2980c2c001880d41071000c518081e000110080402192110b80c01c1d914840e00080c85402d4510707260340005d00c2c2e50000d00c081585182450301d0b440f040c1c00d09a03103032b041e01904950755400c90711303c4000548405818030156608200d040003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 67890757 1250 67889507 67889513
    0x40203060607231509030703030c050d2c011a0f0301060512030705070807081f11070b0a0b0103060b040905220507080c010f0203030703090203010204090e101103060306011202030109 80
    0x2500080001d42850140d281d42085003c4525102a00c2100d01650701001c050040d03004002050310074940c0c0c075203000714002d118240304a0b0079000d0383c803614040500381005586d0183c82030300d600c0f0038645034085030424924100d03200c0c0c0c00c0e9088010443d0042000b0b00d000150360411200c3d1001c462801340010a44d17607901c00108100c1c50040d103418299030400f08281c010000700340a180000c202040c002c0840d1428085015210007500541c0566154498020b13102120b40e5049803240c00301107510161248110700b0f00581301502101c4190240c0d141000030341c2950300900c24001920001d021150030541041c420000811000d032104560386036607445c141c20b55040d0000710035007620890140c0369051402d1803040c5007220b60111181842810550b000301aa400001d490b0b0019139854040b42e00303101800443d00a11568211164444c01c01440000c07508000032030317a010749810700c000c100b00000c6400c001650301003075070826810f400160041004881c0500c403031a000d40000c0000440380c5041e6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 67892007 1250 67890757 67890773
    0x20103061806090509030406020d080403020a0b090609010f02040b07061125050d0503070e040b0a05040501080c120307030c02150d0204030c030312090b070f110d0804051608030702040203060607 85
    0x1040c80703051544499061110401600903e50841c02c114015800c1905146000e03481361b5403000c02004004e40c036000202854820029680c071681c1243e01c40907036003454481181c64a1048174188101c3d801d05146001642e0307580700719030485000d5081c0a092036071030398030070001d00080d946448101c4824450111100c0702600103400c0c3c1d202440f1040e10008039031401c04c1c10a8400306240041c40302c1442004101074120300045001c5100729400501071070444000303410386650350010341c1c01500d002e0021403148000510441c0341d5200716403451400e49000d151030317540d10800c2c00041c000b82101c554400142000030318103a0425540342c802d400c3c401e5000014080303030010350042d2140c0c8101c079001c0050503000030034002d041c20950418400f88407181c480c0d06188502400c10310800400080e00c0700b072a03100c0c0c410310307882810a1060320108030204600901241040d00c098a040c00749080d1180444c40d2060300d2021600000c0c0558204101e41e02004000d4100a08560b00804104032440002d1540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 67893257 1250 67892007 67892039
    0xb070305120f0108100914071418061f02030d0c03020a0e03061e06010c1b050103060605130311010c06020c010902030f0d021207020630090d0207090507173310030902010306 76
    0x30308012582c0182100421544417074070f12070ac0040c2e010070300511419440c0c2d40804000140c51705490704113400380580807441d601c2008590f1011514203440c25032100e07030540082914541e41d6465000c3d080100040503220041a9020007502038240000e04000f228104001c1d800300c014146101500500d840e10100c8402d03240710140b440b103400740140101cad0b0b0148a06409054240780c82d03414400c06540d0b22983c01c151340800341245800c08040b01140e0310812141c14559402502907403102200c117541d074040c01c043c0230228030a0140240030380580710001102d1302013030030702e03401440e4000c441c241001140c2c0c0001c2e400e070b0300810100030001e580c8104541c0d00d0b13012114940c107411f0b00c0c2c0d10704001001a200280c60511142c00035003007549500d900140e5542a545003500001c1d1544504000f40c40510b126a4814a03181c081d00800c500c0f542c102e40e070090391042d00310041c190806c50301d0503500c60342100d41499038456a070803100e9002d40d1280e803252110901c18100041c0840c1c444021650803c44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 67894507 1250 67893257 67893269
    0x51e1003061a040f061d090405190501061d070207030b100902120601080a0605060a0e0f030a030804060506030705090424150f050a0e0105060309070b070305120f010810091407 77
    0xc00a010001c440b99080c4d07110090206281929030300d03030724803411034080415100040c0318181e0392002c2010310206204000040309140d401045001882c03400c0c9018000c00e00c101c594800c00b03120014200300f4006c0045200b06800d82c0034262a500f0f5940304500e41c84054608202c10382e445a0114414160348001d00f540c42c001c1154101501e0550001022818003d0442606a0078160f003003015071030b01816503e141c24241060003070301c0c500c2804540c4103442280c205a0510030401242e06254204190320701850084405100036502c020030f040e5603810910078030390401c0c039440005d00492104110f0050031444600810406160110010151000c150001d45c0c038a001000c1000010101103481e802010142d0300303010214a011840d0042040510070039004550000008003c010140010009414540032107511048241402401500112800055100564003040384200c5801e80d0034100c40c4010010600402003010f4040038005031042107524002d001d900c00612001841604082d041e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 67895757 1250 67894507 67894559
    0x2041206050a0506010e0a15050c070608040201082508090c040c0906091d150312040303020102070b0901090b1602031303140d080f281406030106051e100306 69
    0x810700c00d0a4211500a040117050110748500c000e071a480b0032503540d049481040310558001d03044131040c0d804c3d00c103140c00c2d14607078003407008003103a030503007000b1214041d60007a078400340c0f990f9815004406848140d035a03207071540c2a02e4420352042c0c0c0302d0311140340e0140107101070f01c1030440302401081c19661759811100c00b0681e005402d000c903950001646c8020070b8500891107550781c2480080d510f1141c05054032400340c0c0c1e094030340615903e00300405403012085c50380c0560b0700d42d074a0800030300075005203004070342c1c4d0051000460741094050140f81e80d2190018617050b50b5403540200340030300401c2c101a6406501082c007003080c01c034400c2e0560b10019030058051f0100500b50a00c00380c10719002041c1e00043c4042d00d01070110702c0c0780c000417450b407194043c107039500390520507030040410303080c05200c2040c1603081a10441d98810101829801403009800074001c04d62030300c2c00c001450207000192110701241140340703061890415150501c00c400f03400c000030210b840741c800300048110032240b20f016036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 67897007 1250 67895757 67895761
    0x120703090b0a0c061508010b010302090d0f05030c030712080a0606020d0309020a05060a050309010b03030c0a0f06020d0509031809060f06030a0605090903070b07090e010e090f0303130b09031218010204120605 91
    0x2d41e0a0082c11000c0c80242b030304500d0005d04000050f854980580d0103408440ca000349441040002c004544003146190300300c81d11201c0c5403800c080d4004800480308001054a004100d0500c00c0340100c60940300290080c0440a0820100f1001490740403826a8072080c0c0020018250b11600b0013051381c0c2c000c0d41d4445070740703240041c4003d094500994842d40a5802009416500358011540702e110300d501080e40403141e0014144240640629281c0d046501d00d4403003808007489001000b40301800d000304405880c840c5420800404900442e062070704041d80b8150690309140c00f40081d640101102c000003100ca07100c001040f042c48003140d14841503031001400400380304886600c1d1354030646030700d024080d4509195004240c51010300c90603841d40700c0400401c2c1142c106001c2000d0344a200f00840782c036881d1100146424507180c1c0b0065506001900115100700d0300402119504820300c1481c0329071f074844079541c107a03c0c40d00c0040340c01155070074080460b0180d400300d02111680c5c040c3c01e0103c1d541c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 67898257 1250 67897007 67897019
    0x3230d06081911010f110102130806130b061201060b03070201061a030103120f02190506010501030c0e030c0105131505030a0f0b010e0f010c05030c060702120703090b0a0c0615 77
    0x8000503181d05000d42242c1c0300d0324000100d030303849045003089080c0b9140c0c441c40400403050f00c0c0108000c3c01840c00e94004581100c02c10300159000d02120014000c81b40a91290888040c150040c200054034140010380022420f007070062840e00702018800000038030540d05c0507406029041550072200603515004104000c00604800b0745124042c41c850501e5545103654020b000c90303455001328280710301400110304150003070080d510300300900103a08100300c802d072503d1030b2aa01d007401060b010901e8402c010000c00d01c661182040140044c00900090060000648144d0000b00f1508207011b040c0f0304c0454440c3d00194150805d8506449254a9040500c00c500c20307201001c03803100364145000824080c50380c0c810380a001201c0c042e00d180c4600c410440040302e030142e104202900078440001d084180d030b0000160640702d00043c0c1e084d280542403072070081d0814880e02e00098001140064140040c00c00703007005092040c0181002d03403400303556a4450703040e0382c0700403080804144010030400003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 67899507 1250 67898257 67898263
    0xe0f0108030c030901080a0b030d0e03100b180a150801060f060806010806042c0a05010e010519020d0b100e0f0307120f0c030215040801110a050703230d0608 69
    0x5032400c200914144401440810781c2c0f4069000780ca41001402c2010401e070071841d500501d8283d0f405410380d4462a07120703101400b80c89407c080e150082c400da602540314401248200000e800000741941c0d20141c01e501c25030180d03000940201c0f1441d0f9950490241c00350741c45804401400300c0c1d00082038143c0303003140c94101e050345544807405000c00082080940da0f402000c3c1e9030311000855001070782a110b03503500c8001c07101d500c0e5a00b044c02028010712401c040b00040b8070352003a104500034004803514030401c07400c0c0d420507500c9840d0382c0c041003d0500b031183c894001d005903a19100000034042c0826000070000fa211003c404040f481980740307400282892a02401843d000350000c1c08001d1078254510348143da181e1000c0c0004010030707a039000308220314114000450300203250001102000a031400580d007d0b12031050190319040a1500701d00c2e80d0360a8510801c56500c2d05400e2481a8600741c07200e141d85004603189c0394442c07021100141100d40a03100000e0000e500094090034418614a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 67900757 1250 67899507 67899509
    0xa02090a031b082b1205012306090105070311010b0d0f060c02010c0f03020a05090310020c160503030703030903030b030a0c090606030e0c010309020a0e0a021201060e0a060f0908070e0f01 82
    0xa154100d40507813a81c40003680f480340140080c00c001c500b150380320702c07000300d03010b50f8103000100040b4204800000c0400328007160000300c0b100300e42c21a109100741703010040d051084035903013408500c00380a0360010034010079075122102104e174004118070040f00d0018031590400007089405c1052111040103201052040c0c0046800c1c07030008009698031404064000302c1c480300300cc420150000f0f0503515451042040d54030004028080301c1c0b800a5039000c840c040c1d0401c070580b1030702d440b42c070f044800c3d40b5084103010400c81c0c9010740910324002c05901c1c00c60150000d285c041d024507032100003e04050b00c0c00c020740b5000d103000d00006034100f03090000f90805d99002d640000101400c18012001d030b0100420003034210f440034200012403803030a00c0420404032255100c443d1114010040010591031900106401703418801c1503541031b038a421054400d143c2d2141100e03000300c861242405010301a0750081480301135410320b01c00c4180d43d0071205181031481e40004040074441c90a02010105450402e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 67902007 1250 67900757 67900769
    0xf0201020a0206060f0a0306050c0414010f092907030c0309050f010813141e190b0f040230010c050405010203030c0306240a0801050909150a02090a031b 67
    0x1501e8100784140095032841c0c09840a4882e204100507204141d90f00c0100300021580480c0c00e000510740380020455036009803142107071280c504100c0e5030301588507044150450007540c645034140303400c01c881c061004c00c421903840c154008000c24a042c01e8081d001030602d2900c01e945002001d8043e1900809200e295400385001d0f18082015402580c0c0000303a640c0e10045002441d44240d0712810301c80300c5101c5a1485032064043c44000341460040c0100441100103194111a81280603503070301e450194081c10080e041720850000305110300c1d002c030310150b000f82c0010209200c3d11004500802020b51600d403500d5000034003031070307100b0290080c0507220822a0307034140241420315003070006c0c1d00c84c48010035408200000100060303580d40d401c3c41308203080119a94084d000420340010401d107500c00c0340c00c0000300b01210b00024031450480040d0344200109030281c90204000c540b4071084035800703411420710640910031202c4c0c0361a00a15080118050800ca064010260220060b00c80040d0845 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 67903257 1250 67902007 67902011
    0x10204050102100b031c08070816050304140a0803070504030c0509090d0804063206030f0d0c020312070b060a080604030806090402010c0c090506040b040e0703030810030501050403030c0f0201 84
    0x200256030b0007083c1ca40001c500c2d60004508449100c000a05000020042d41401c0e100c40b1800c0d0312042d0702c622500c0c400c0846446503545501e5a0069480d80c40f04141ca100000d00c0c10000140010502e0811500c080c607400200c414191159603040c0054008079064000910040350070030a1102c4540100300411003500c1281003418802d400c41e848104410102c014084064082010024a64480d901480251444610f03144494260b02000e0340d1030121280044010b00109109103400728000d424034040000030050600ca00d081540e04003520380c820b0fa0315000c0c00109c0d81c0141c91100090181920a550614662070300d035040028100d1143c00101a96201104210020b600845031640000040307a03094002e0303603607100403104924840300003080c220072408005510700e80b42c2c00c181e0042504440c10b0009801d950244412034400c10141e0300254880c401c01c10201c1d0180308801d41003a02c1d00c12140c14251691141c6094a00c1510110000390703982d101c880c0308a83c070042020041d8010700c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 67904507 1250 67903257 67903259
    0x16060608030c010f1a060702120a08190f0806041e020313020108070804200409080d1406011107150201020910080a060504020424030f0e01090c05010309080a110a08040315060503010204 81
    0x20780ca40c1c202100d80c011b4001c590000b030080c250756403c0004035001a100c003c40da03030701c1140d1610f010f4541100c1c02c554154040301d40a068883e0264080c682c1c07041607030380c074015241d446c1c0d02000302030614a081020000007a405129800310940025031149000001420002801d4400104110313801059101040000024000001e0f403408440a0280b8071200d01042c4864680004008090120000b000e2100001e0a00844460364110110030b0020182c407105075501c200040d190b500300c1420030381850700900000e0181960241844455074860310005042c060b030b1001003060003401030542ca020401041c2044203d18040c0030340409881c041d1410760800d8900031170386451001c0700700c20404013500d0034000700b8800d1083e4441c4100f80841c03442449403a0314001a1402080b500700181e413000c8440e000070500d07500078021b240d2403d612041032031800310700002c22334007015242c1001d02e6501448a9910108058070054006503005041407409800e20090340400c07590241c1c42103001781d0040c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 67905757 1250 67904507 67904531
    0xa06080a0c03051e0a0807020f04050f0405010c0306120311070308030f010e06010903030918090602040b092106040b07050405130e0d0309050c1003020d02130509090304030c0b16060608030c010f 85
    0x45000c0c4171a8030171500d43c3c50302c0843c400540d03000301e00071982c0e40091403e400c02402840702020a40501d004000030000012500701c214252440ca02030304860440c000c21000000c2e20a1110b41c2016542c00c041d104400e4803a551560140d10556003022440010310041c090101a40d004640140003405d000d019036247d40e4015103400c04034803918800d03a118222221200c00e245c1c201c240c80c580e11032811543c81d82c0710400f440d410340040d80118050820568040403010200109134403040a050090103150765598130809032050040c49002004418040050a602c401000d10805c0035817500210380c04510000c4245020b1648443e0410581015100c0c80030840200e110f5140c1c00050325400140c2c42011001e9002c1d220310700e01e03080064400038010001244290008040e00c8d03045410009585881c10280c0d0382c0c0c0624000a80340e01545001004803080c18001044080d070544544140300f4030f0b54490608607901359015481c15040060248864502031096032490406000c0030080786070048 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 67907007 1250 67905757 67905763
    0x8010e01030510050a15060201020c010b0402090604090b01051c0b10020a020108150103240603060e0c16210305010305060106050703090b0904091209090b0607020f04050a06080a0c03051e 82
    0xd01c880d40b07994840104241140b141c01030481b124040704000c0e050396407014002d00030742c031040040c1b456500c0d01c0c0281c112480d00d4000c0322200c101c000c1207142000d0405440034001e11034119030f02d060103410040c145551070060000300c08025070240000d41700750710340140a075002d480c0520a04640000b01c0a81c0180e8221200e550400740c0c6004141404c0411b8005a00501e0703e4810900c41030b00c0300b15001d0840d50400d1007041590700c40e50b4140070880e610f51038090f003510f06030b0b0245910401403280403005140d42140854042c0200d0760742d0b00c0464000805101940912480d0300040d480c0c80052040c05000c03c00c032401071465141c0b041c5031030441d4500504040302c170f001d00a561040007450080e80e90341c43d08921001500310b5296039403caa0410040d040040d0303842001d0301141403920145180ca400000d1728803668001e003500903421005d4040100403d0020f10444100b6903c1d807011411b500100805442c0901c5031090303081560543c10b0aa1500b08c013400d10110300000300c0d1444001007004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 67908257 1250 67907007 67907023
    0x22080d030b1e010518220f0e010204051509010e06070501020304030e010f0f0c0516080d020706020c0904030806010c05010501080a03080a02191808032a060603030421020603070503040308010e010305 87
    0x41c05c21280780210a8006035550811000e442107140c00c0b52065038103c1401c1d441344242820b8014204090348250880c20709078051342c8982c1da4014205035100c00046120801885040b40500d04503042c01c0441c400500c05410601040d00c0c2c0340c1d404410802015005035000c1a004d00900b021b40210301c40e10700082450b03100014841c2001000c2822070b040080401034588503592000c80e0305da16944a05520382d940281010310401482030410019043d80040b51210040038094000c000e01d40c4d56807001d40c2d40e50780247c41c00c0d04112050100801041086c45081c6c00f074180480504040b1406080040101002404205059104110f03035105100710319008560a0030a003002080480c0800d0304a1aa0700d0943c04407405020024161003208561a82d480d0355400d20401041c11507140030341d0581d00c100031142c05405610400051202d03202074100010106103c02c440711480f0440d0340410710765003003920000f000c100701109120401d90482011805040da00480358015899500d40031b40d14112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 67909507 1250 67908257 67908277
    0xb060d02182e090801020708030601170403020d03020a2d1205190902030313030605060108090d0905011809060f03032a06021803010e1501140622080d030b1e0105 71
    0xe9541d4942c0500910040c401000184000c548440860505180f56030040320600d000a43c50601c04a240d0040802103000340c0c0c1550082c01c002031510010b8009500c82d07803561003071014109284800000c28006050b0941e10b10440b0003400c2070b50389003d01118001c2c241c00600c1400c001c00c20911640d030b4404000d5512940e8800b081c0c466440c00820305510813401c80c20704a032000740001c42800aa41c010342c0c0100400c2c3d90b590b0381942d800301d1a545481050145000260000030b08100c298031030070031580c0ca004044e1280d03032500d50b104108001c0310b4007548081c10700c1d10145410411715400030301c41900f4800204000300c600c240010510502c2e40c640400818030743e80881c01201d8056001401d46540c0f2018008001d008040c208645e80c510004400c251824030340d07800400d50350b004c0518000d220320080d01da5070520039a0440d05400c1040b1503800c0642c0c1f2028000050701c8041001714900141d0b141e1400104d500040060011300d150040c0a080710010620032401e050768810104e82803044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 67910757 1250 67909507 67909579
    0x50d06050403053001090506060909060109090207140d090617070c0210030e0c060c0a02090a09060510030302010e0a02060d0504140607030e070510080601080702010b060d0218 77
    0xa01d510301a01c10b402104030300200c0c60400c84c0d80ea0110b80d07109100700003810f8403240c3c80c0070507a0f807202d42c941501c0b4225002c40c3c00c1741c014040c00030303242071246034a5080701b0141803200740c07103849610090482e042500c00740d8100012102b21620810144401c50020610349044442c090070014041e00b0417165480700708006009030009400c00f031190803c010140e0f0700420701d038403030318944500402801314882191070b5406884050455031400c8402c5031f2105e07480802620701d44806400700088020020144140292111034800004a491140c98418074846c00f458440343d0031420300034211502503425680300c1d03021861000c05030f070711002540c00a0003006d6001c40c0d60307512440c0102110140e1188894540b0464092111264054009600c80300b0190300301c40090742d8038030801071b41d407034040072803004943c0e1640842d400394440c2d520580e2180b4213000202e0190b1601010a9843d030140b55990400355020030310a12480000550300c070380d404d04440300e10380e81c4141e01c40664103100d02303607503880540c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 67912007 1250 67910757 67910761
    0xc03060d031101060f03060605040c09030c3b1006020601030c050d020d02040507030506131a06070812010b0d0606020609100c0309020a030f1a0906040f030e03030a1d030106050d0605 80
    0xe00c250401c0000d003241d0048a007850b0346e00e15009015060314041e5a00c680c1c14256045a100d114001440499402c0354201201c5e9181c0780c0c0402560200c0c0e14980c444100200780d040398441d03468420944414000302e801d0759441d1101c2c50750555580da40005003190024001040441e105a11a40640341c0484495180c1c8031144002144110906402500b00d41404100a20944c0540c04981b180c0d006580c0c0c24001040390b9078110441e0a90300c802c142440380d4409000a60802101900e10307948200110f40c640780f044040700d400880243d0249070340b5400024808001081c3e806035900600180c001481d80d0300707040d03810644510300080c01d00f00d001d54034408101d81c0c41c4203401038054190040c1401e11070907140d0400448200301c1010039241e003030358258111115058007850511074040e0201424445c3c58954a0035011140d1910940030031038442080c60141e07400340004c180c108016180c0c0413004003070f894154154404681224031030f1349040002c1203540c0780c68050720a004d502c66000691a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 67913257 1250 67912007 67912037
    0xb03091b060c0d021605220902040b030a05030d0b0406060804031110060e090c0118030305090a0906090e100b01050a050f0c07030c080c0301110708070c050301110904050c03060d03 79
    0x14011001540090b202d452507244070f40340c011800c000c403004a1100c1d0300c0295200d106208000381c0c06014104803560400d204001402c1c03642c054180b451008102040b6484803400080c42c203111031601340c2c0c0b60b8000189910b00f050b0307103128a005002d01035800b4440c0030b150202c051300b0701000800241c1805030075040000d00c1c54080c0031400c002c00048c04c04120007a1121085802c1039000c9610754410300c50492951420340c01201001365a0024007400001c56086607401c5490343c100180703140d0441c441407000300c0c0b40e125601400c005482d030a10f00042c003030000703604e01c1d2602c02400004032149113031121042c3c00780d07840422944003541c0b500b049030b580d8019111381d0441c0d200c1c0a05010f00c1d402842008010004001a4001280c0b5503c0442d94003400800406080300c600c6e903003800c011001040781c600011140c7d005840c0840c001d812110000d580d482c041303800d4132141c0020020841c0001a0340d003451a003442041c3d040604140c5c1103085151000c08a0143c020841016051081a00c0c1c0d042d44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 67914507 1250 67913257 67913269
    0x1502160b070215090a050303071404030506040305031e16030e032710020609070909050109020a09060f14030c0402090307150c110f030a020f0a090908070308010b03091b 74
    0x1540400101000e240c030700c000035200c01e581a0010290310000003c105402000103140400b10b800001640ca10b03115040161003107541c656081c074100605200000101d84c050114503c55402600d6080c2d0321b02c2c0c152040f0340740800c0d140d801c01e080c440d81800d2103443d400c41000b1400320780590400185403014942c8541c610b010b90000c0712a08048000c4810034200040042510700c2c10a4603890301c002200c46c020f98840200300c60f403d003242d2103044200600c20241e004448510302410000800c0481600031410032400d42d0020840d05072264420480d405040230510010210206a40c41c020400d10000e911907105800c6144a2600403541440c150740030b00a01004010b1118442e90145001c0000390540000c0c200c2a10701d601090042400b60806c51105d0f122410024080d000e483c05aa0070826002d0f10000a644c0200c070710b08011540100c0b40c842d02171494000c030300304d41d114445850028000f040581000911450034005d2220140b0001050714a4401c00c802000340030101d4808500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 67915757 1250 67914507 67914547
    0x91a07030207170705060606190e040e1b03070609030308150f1003150504050421030e07060203090406080309060409050703110a0503040302010b0a12140102070501060f1404091502 79
    0x400743d40100c60303145140c44100001c0608034842c000b5100550f54040c00c01c2907070301801e581480f004039414801101640f2170b516210f01e08000400000d50300d0702040030f152900300c0312002d041c042404400420710502d0708200780310040ca81032800003404c038110b40d4010300300c00015004500c45c640344903019401d03a4500340c0400301940c0203010580701407038000c4c00901070040744440005040d0076002c003040505050045500c02d40d04004503038210034031854004d042d00141c203040c1041559076140f5016418007441010001d02c01c0e50300658582d00c0d85c1041000711070351940500a180d000b00b00b2030029403182000d640854440c072200207681d640d00700007070b400b414004106102012002400600d510b40140146000310302943c000c00c04a400c0e802030010f501c00364041d0340d095484a10070580042c0d075070b0411881d00c014000c005410304100e42d460b20f00707541164000c17601ca82030380482803100c0d440c01c1c5d003a486a410111400d0020910a4031064184680c09000c08016500000e0782e80503101c420000303032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 67917007 1250 67915757 67915763
    0x209030a030503180c1c020d020411040603050a02040609031b0315091104060b030a0209030c030601090e06090105040c05060906070f050d03060b09090106111e01020306090604091a07030207 83
    0x4415403064500102203510840c1d40f10202814007420541d50302001440406a0001516903a002176013514941017404000701e007280d200501100110040c0c4076406680344100d00014482e0f1a60b0520002500b0f41d41c000f4402119144148810000701364031003c540d0490340c20580c2d03018002c8100441039141c050942000e00302c0040b0340140d40c10301540d80e100c01d07041380c003805240040b41a031104100a5812138882e40496503000e0005c2510140c84d90300802808000a0403100d0450b031500200741414000d920110003541c0e5a00702c02c0e10301c0130038810303a0b03400080038000300807078a03059480702c02030b04e03d07030003614061000460324680a88580e002c549450b90801d00002104489207422569803140b80040c0f00024100000021300c0c03110002038400c0c41c04010300b0b128081e0b080800850f418118001000c01911510f06820201082c00a4202c00c844194001681d42c0c13820106000c070450700644240e005a1a0580002c0842e4050795911901e00e40b1507078207100c580b55084d00300c01074081e0b5a805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 67918257 1250 67917007 67917013
    0x4030507060213090b06071218030606080a030305180a062003090a0c060c0b040206030a09020603070c20061207020c060d0b040609051306050402010530010504020f09040f020903 78
    0x80f000c166041c441e018200c6a4042045c07240c2880701c014060300c3d015109000701110650401454442c4c00342209140350007484580706080d69481e180e0500f51016036210b40c4032500314507080410f06034540100c40e0320480240e04002032105010009940d08510040541101d50300d20000104d6034030b00c9507015640342c413130200710348a050000b03e00d900e8202031002224580040840014614020148030034090380005100c0380d80d607200d40038491113610040600c281541d0354601000107a8a10000e03501a596903a55101220444d01e0318010070b081164a080010804243c00700940e513400701121032496064002001a80328403609070310344000b0420f1107070b1014000c00d000c5000300c082da0103502c148004690070301215694401c04021140c0c1980c10f488910200100b040100c0e80c2608020740061040c03400307600c3d1000b400c10710030303c10090f9000c0400314409805504601032990b1134071405082e04540851412207080000d00c2d20717103c1d0007212402a604c50301144020101541680c11009018040e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 67919507 1250 67918257 67918267
    0x611031201060216150c080c0f01110409050106051216020c090c0a1404060203090108130b010914150604050f010c05010204090605030d02010c0509010c06150308040512190803040305070602 83
    0xc1c1d11102c00c030300d80900411100000040c18106021501172586041d200e0307404541c1c0c3c42d05c80300d03041c1d802031440101364440c10360a04180d5400b441202920b911a8114507147c504040c1c90303a080c0d0f801a400241003000c00e004441702135038054101500500c05e20b051014080c2c10460507801c00c0c18556544e07500044200800032105581c0f0003c04056030581d0302c00102890050b0350b460240224041d00e80164020311105c11954040e40c40c0d150004000d002700d0380500380c90303910740030304d10001d800650b5020f40f500c1307001d0a0081040521030700080c80490848aa03140500030512034060751080070f105440381805181d42d031340941c0c032820202d07820600940d510364441300c095000e00a00e1042d28000d1040da00d0b10400caa1061048054080c44e5035034880c9803040c003200440310000401c0007600c1051f512642e40c03407011116020100110301c100c3c0065100d1703141504004400109004420898103e4000782d2852080072000c44035460340800c0c840d4907611641001c8485000c1c4040c01881e403440019 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 67920757 1250 67919507 67919519
    0x1a04051906021801110a0b180307030201020a171b0f120c030f01150906030f020405040903020105060109060c050c061b06040b010e06010306060e04091104090f060f06030206040611031201 82
    0xc2a060590750800041c2040f4200119154405468402034a8009210380c50002c1c8900480940012078149030500442241c00c90906541c068001100948c1d030000318207100301d810070340ca11071b05105445028074500d003080407410b80c408080c070440c01c0140e00040745d003481c4982c0c40680384000d031141d0622105150040c0202e06540c000c1d40c41340c0b410904400000743d031450010000380b0100321582d8001401e0b141c80002c1d00940451000e40349016000d01000c81c5030784941c0b0460712440e0080d8004107070350416400141c0900c089801ca0410044a400c254010440015100907144826104070350f54007070803c2510189481c10a2010283c0625020310042c020400303840e50513500c41071403507001903c41c03038010f40494840b4422500460f40040e880e8101d49000d1b40f0072041103000e00783c440503050321040001d080340d0319040110781c0524007900d041c00703110b101e114208e544050040100081825038001034824015417042808021008210900c40720051048e9422190151a0503000e961144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 67922007 1250 67920757 67920761
    0x1d0109030e12030301031e0302070515031b0f0406050c03071e0606061b0210020f0102030703020d061409010b07030302040f0f15090608011202030f1b1201091a04051906 74
    0x482070702e00c10900781c0341490b0b007408040100c0e4100c03a030111400750b185846462485106882410540550055040014454803074030048000740c40d01c2c1c0019a5285403008041c03032075200c8100c400310350328000d000e45985e95041078129400d440050030040e0316a0341d00220f440c03662142c1c00c8010203000c80c100018158003401c80d5042111449500280613141d1a00320072221407000d4807520b074070b01c8803aa8402000d0b083c801c00c0055800300702c2c4165084400d44d009030342d0036030340182c0d05400001d50000d000143c900c102e100b50800390640c01c0000789104a418002450000e040c01040c1d200e84000400c0d00c109402641204e000f0702d4800354540955503145002d0240c5c62492007403200d03030005481c3c4c045109104000e81c9007515490707161800181d003020f80c0000454600081203801d0712030048460300c04001040700585158440c651000c1103050202405600c0b001c01e48110302d01d03070400c08000002010004280344441910044c80c04036a90341c1022071504441c10b605403040081080e0300702c18400c0036 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 67923257 1250 67922007 67922027
    0x5071e0602070815011526061c0c0605281d010507020a1413020c0105090d140313030c0206070b0604051b0906030a1d030d060603020301080c041d010903 67
    0x680903204010354800c1480e4544061390700c130007030f42000d00005110540303900d0304d004003000c140d10341184606c0c050242580c01c06812581d136207202d5103920030090702c0d00d0620045a5050b0740890315125400c400d6441110451035030040d50240000031030100c80741c800171082448070034600d08105c840384018150151040900c240002102c09078059449101d50140b001c856034258080e01082c006464040700c00300464030714940da0380c080442e611103290350201d80050414415800b00000d02424400000c5181040c0800203106010382000c44505545417441a20350000c0250000003d04240d0718085400400c5450002d51000000c11a5424440350021051160000343c0b4100300544607240780d0980250f00980c44114007074200544c00050801031301a5820000f400c5000c16810401107090b900281d80355041d078003940c80840c2c075891051190203a0001421181400c61455041c00c06081c0c030b440d054080f46014507110034884e4406440c3d030303c2c0c4a046010b00c0c00208080408d03850020405110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 67924507 1250 67923257 67923269
    0xf030909180c03071805150d120e0613080105090f0703061509020a020309030609160311060702030102030108100b0402070b0f0601122915090d0807050a03050702090708010602071205071e 82
    0x1c1c10b1b00065000c150891260f040407002010a0f03c400c6003699071000308a0b189440200304130200d0400211902c4010142400003680d10041d03044900f0000744a00b102c00040400200368080000300366840008110441a01d8100d0008200304a501c2d0319500c10400307541c02400d00034400a48030305216404006054801001c4081d240c00d902d03001080396440e4804418000700400010303041000520f06103002c1d411000c0500b160382492080c0d00002e0890300264003440300c41d0090140800a29072901c00c08140c054111011400c2440340d03214200703200c02c001c16202290180c2404200c10781e0050702040442299008140440c1c40301a01020800055440031a000c107420340d0400d0f039038034100c01000b02445900c8560741c100408001003110f5121400345c151032040c4108074060110b40300740310f01c0c0c40c5e20740241c55059031081184180042d43d0070041100b010000e40e500107000942e40880c0070401c4503200001c01c00c0c034001e00d041c0300741042c0705644503100e80d0200c030302d0303000000065519410403901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 67925757 1250 67924507 67924511
    0x30a090e150616030e0a03030906050c01180803070207060302040b0304080901122d1e0b0109030b01080601180e0a060b0102190c2c0c131e03050f030909180c030718 72
    0x14454007801b203880d07020f020040120b403c50606000c007500c03c0c405003104021400001c00c100d052030007441440da1a450094a401c034000007002a170940400c00e80c4028138880c50114501844c051070b40c1218040540020a62100000c087d001680304110140c0e80f520103d03c10406465003182d1400e00484110040d01d2904100c1e9504560300894403a10100702040542004090103101d029402018085e520a0500000340b00200c040340c2a2104e40d80a4040070f0300030310155040c00c401c0700c0c18080c02d141180300c8900740502d0002c040340214110440030f40c0454046039014040005038188195404035101204503814130700c2c01d00030b450b61140c0071595001b22031600c02c0c0d03842e00c485051406603452040000801004105e10b1843d1400a0040005da0000300f41030310340320201e03c200c00503601d140d40505080b0706402e0050000900c01081d400692100942c5081c0c5e0607070110700f640e04010400c006100342d2034200e040080080c4241c804002d0300a00340c507030480d00c2e074084148040900d001e181401d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 67927007 1250 67925757 67925777
    0x90f060513020f19030f051504150612020d0201080c1905120703050106020a030507020d080301090e010605090106090501050906070203030307110607020105040c180609020d0903020f030a090e15061603 88
    0x801d10101100603c585a084c00440c2420368440d1040b1200c0110100e6280c8111240c0c000070b855035a1880c1d008600c00c00d04008000d044212400a41c2c013150401c0b4580403844200c0320050744c540700012025036080c202541d10703071780e003110302c03040e6004001100d1030341903408150b9003005511200500000181410340c1040352030302d0f503040707040303c809000e8440581c0c44205040e002c40d0080d806480014401018180604501d035940c4806400a0744468109038a94103112031803802030050002601d400c1d512240c00b580750880c010706210032445441d051080005140307030292140800c5a2000c1c0c0c015003100c4d50b80c00c0030100144a0300321215981818081d07007000c15111481809514002c0e9081024018500c1c20076103ca1030718101400f81c415902d03680d001c0043c03001000c1c001752030070320780354140001c03c1250740c10003908004440c281402e05800030040c6808103900001440160307090f01502260075a01c441c40000d107401c000b0852680301d00081000e0190030814984464803034480e0f50b80d10303220 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 67928257 1250 67927007 67927009
    0xa0801091a090a15020708040303030e240105010309020406030506010b0a120204061e02030c010c0807030606090e0109021c060e15030c0f060d0914010608010c050c030904090f060513020f 82
    0x1c08002e032103882064001d10311080102d0056480055881c820300001440d03d003107aa603c107013543c4070b68405c07000b00340c849291058442c1c0c00e1003010612038950b500f041d08a00d980d40100e051050501406060541d40c0b0544815506e45500140103154440210340c090f50316120001550b80104241d070001031045440031040070001c0c029242203c90507160040001c1242c56022413082000140104521040c4000c0d821030909010300c00e05c07040c0703d40392640d4505203904003c00b500c20503040764050041800041002e40080148a070440d10009801a01d8820903020356042d241e0840c2038114140c00e10f00046000003100e03500038061043c1c0c5030710301d200070b88900074162641142900300c8e502c10000c2084c40b0007820010000c4c000d081c50b400000074038a41c07541c1c903d100c000c06029504c005039134940c0c05001d0b1800c00d214800c90b2205508109050007080c1c20480e507a8890040243c0c099074551000f40208140d44000d0801701d90300680502c198a00304c4150712110b00e0f0104181d12274000d000c014045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 67929507 1250 67928257 67928303
    0x103110f150d020a030e0a030305160f09050d080408030a09180b031005040503090402120f0702070302090a0e01060510051819090b030c060307080702060c030c07110f0a080109 77
    0x3680704801140c6081100c0011420000e401c100e40394014951150101d01e00c9100502200c41b11500ca9203001a50381014070b010407803440c210390f546088c00803140d225400d02d030304550b080e81111380c00c0311280400c0e800391400c4030030350140b40c2c00b03a105488080345c40d0200c20707001182001035a20311340211506407e10840c40d001d8a41013460550117801c408a003003a9040a44c2110b82e109000c0c00c04c0700c3c0f4140785880441e00302c0e40500803002c1310442c940c1c18400008801c010180c1c00c086a07200604009095030005980e420700036208160700c6640f070b1710000340440203400900c010a00200107500600886101030182d9200e801c804080010b82e051118540c0f4082c03001d20280158624208115828100c00100503d01d01741219807500c50003690301d800d580e4442c000d43c45060103540b24031240c181020060319029000d0b00c0c04040440c140104603500c00d401c026500f5403500507440070318150008011a10680c1c3c903911103500711400341c070003140d5907905401041c0700740e12509800c0304003522003e0501d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 67930757 1250 67929507 67929529
    0x218041a062b1a0402030921040512010501030b0f04110a031505090d0203040b1b0102030a2403020607020906040e0a0605150d15020304020102030d050a0c090b0705060711150103110f 80
    0x3d815400d014507207a980c1004d6001d568000481000c9560b0580071031030401030340c000182003024411001800744001e00707281d03200c0125120440028811541941e5408201c1d5000415078082c5000c05000901841000c41c0150000343c0080c2004003015243d0030208540c031b60b0203140300c0406041c000401d44070344001900138000705040c1d01440c1003c1c00c0182d13000c3c2691000c10300d00c00c42d20416040f5060030320300f0700c003c50040d0a448030004911644280343c0d070103854020614084061680020009601e8100c112228035504a5a2007411b50714140000c00a00c4180c003541d0341d502c112442d0008011301c0c3c0d8000703401034080c0c1885806080241d8200411480303000401805400e203105c7c1d4002001c201d402842d0050720500503641000d02c42d080980840320115035490b05142c580c0b880c0900c0580002c13910000e0080d11281d580341c00800d44901d99900c0001d00020b082090030320b1245004030b014051400307a90006400c03803401c1d50750303420030800680d0505280b40c401d14080501442c00e142c0520410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 67932007 1250 67930757 67930781
    0x180614160506071b1208090703050601290f03070302031810050703050919020603090f0a06090c0b04060c02090c0c0f1c0c02010f030f090804030501020711040218041a062b 75
    0x148140c1c800880d503049020703021220508c0390190100001e4401d10a80b40640811a00121843d50003207804405007141c04015410f01c8080190280f10340103441140d51140c040c0c00d02580d2901c5140e0f01085907640e42e00104c205026542d0390214036440341d0840d9002c0d4020340d03828081c680b40d10413490344036912403003100c00049403160311b4030050404001440e40301040c001a20501c2c04100307051820920b41040c203d84e82580c9000c6a4200110054604003900c3c04c100450704150030058060400c000c2c03d880070b84502c205100007644007110f0b100302d80e4034404200a40d03407040c44d42c9900e0b40d41c9074002c0c1e5401c0e60352221040d07c420124440c1c00b500014a03016555014650302041d0207500500520f40b101c905a82c0307031030030701022440c0e48004000640c4903100059a41485081c03080340304000080c40d40c460b82c010402c0040401559480f070381c01c03a908507800034682da007d0300d2110030749941840d41354101740042114118190140590080c10786460f6600d100306010240c50411100111198 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 67933257 1250 67932007 67932023
    0x8090a0e061e030a14210306060702041805010204060e03100905120d0b030d1d010206190e030d0905010501030c0806040507090e15090d030606180614160506071b 71
    0x1100c0c202c40b402d204260a200060300b5644454000c0d25511074100e000b80709101140c0c0704483c2d460500b00154903080c0b0b2140c02000042c01d504109000502c540304240300a441143c40756005071244c000d0340c0c000c2d0303444c82d170040003150f4595480708054030720340b000068544280038102881080c2d22440c09034818a0341c0c408050040d03000e603001d442d85c060300034285110443d681c0e01c1b0701c104036440c02c000018501d07401e0b40368101c03a003009020742002c010703c090002d41107402c04414843c8400a010307541a0200c1500c0021440f40001003e05180d8082c1100d00300489003891038110500c801940101d05032800351001203000754441c50540d0703a55009a030010302c1035104e10410028a0000d510400c00502c074001540c07072003484002c540100c4242940c0282c0d194210b004451a07264151044000130172290030104000b65201c22404000e10243c4a00400e201111851079500a00101140c4030018101800b001c901d4040c20801d58405d4121080310200d10b4a0030b42d05444060504a4207013240d0110316 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 67934507 1250 67933257 67933279
    0x90b04020d05030d0e0c1315031218030602120903070c03061a0409060e1b0d06050a02040b04060302180d0506060d05240411090903041707030b0408090a0e06 69
    0x780500c810509034151082e01050000718010303401350041d46030113602d04001b0b00c01c01402000300011459501c0c035082da0540b600982000d04422640b0440032290040400710b54560441e905484007803090b8503c85800ca039809000c802c002141d40035001c0d050180108000646d1940c1c103070350756840f500e880500a400907050400014400c7e8004040c203007510350f43c1c10010a01d00001c01c00380d44180380700321b46031603e48003250b1a2040400c40c0000307032415100e40c01101d00c2c100c00410b015001c01100600740700d8079500014807000d42d580485008110600b06503503100c1d51484010020340107058805041388512041201515001511a80301030300400900741a403101d40400c1151254017208980502031103800c1c510a04071888000c032141c92800a0002d0f910b0940f03455411300801d849a288141500320500c8400300c0004151029642000031418028015844107407800049600041c0310341040e804100030000c0040103007450032025101d81c10a1511280450740c0f03028211401600509243d0f4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 67935757 1250 67934507 67934509
    0x605010b0a09140f1c020301050a1b03020310030210021606050a090905040c050a170c04111204030509090103210c0206090103020d02090d03080412020f0601031514090f0709090b0402 80
    0x3051910f2584000c00c54407081194401080d0003200074901240114061080b20080d0b04003801440d0303109000ca8002c000000300c026050800c41e0348880701d601090343c08030015203243c42c0d910340304d000741d6001040c1e11990102c4d00c0000750b0707403c3e045400345148155940300181c082d0056060342c01000254491240c664240322040c002041c00a000b074130301d95450340002800d511641003003c042d100390744a0b40815804088850b1030440300030001801a40380c41c104e80352002403041030b910354614000400105859905003142c040c0101c04000791300642c0174000208000000085101070011039200c58401400207409407000719a441d000780d0002000c1040c00007a62003940140010720a4403401820100300c080415124406400101e002c15410014003041c01482e4104c0c3c51048128030042a02104042029868507418480140030021900340b0785500510b42e00301e44a6140070194a25075840c10501096650080180408443c090000d02081201e80350207107d2995402c20707060020b58541358 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 67937007 1250 67935757 67935779
    0x504020a050904061e0b0a080c0d24140406050603030c060406021309020708040503011107080405010c03030f02070c06082d0414070f0302090a0203160e010504050a0e040605010b0a09 80
    0x80c42100c005035600d0300240314040600311000101864130380011221141d070244140f47c40c0ca90056011503001011041d03040d507030202d07400c000c07560044540340881c04035051900000700c2c5806604244d818500d048a10070561400184150b0085d081441141c4500050540300e10071090f0409036500800005001f14009400810f5000e20070046004082e54961080301240c000900032039000c080050208003500e03090062050b4a00c9180700240360404503070b20010640b10f81d02c40c0506000e1000403100502d4042c3d44415203a46814030190769032441c901d003480c89240c050040401050400b404550621003641c0c102e40d60f88150829140c20411100c158680319000820880d0801d04a4048002070401404018028600c0a4000006034250b1040040d4843c008003c1c40025206004216030039400705041050740030070381011906100c0c4000100c4451180743c01264201c0c2600400080a41c54032803030b5071045000300410800c90762244400d04c403034490a40c2c00303000240c8000080c03041e40359503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 67938257 1250 67937007 67937011
    0x110105030f04120e060c0102031f050d110a030c030f0204051b090d0c09060303050c0c010f080403120603020907020a030e03070501020a03210c090302030c0f060414030a0b011707090504020a0509 85
    0x2410684c401c049031a000558580c4810055006030350044144962a40c4028506072010400010004000d041c0800316400100c01c10b03024026806e03070468006180c0300e94010802441e0802c3c040400203031a41801d0042c0c0310700c01c404038061460000050208105a403400d00f40325030405182c1c0c0750074603c80400200710f040b10310590b8590340e0300300d002444a0341480342c6001140f1035210592101c1600c03200608041e141c0e813105050201c1160058503180e071240010380d000341e01d13041c00d08507010040a444c0050669401c000c0d0041c1008003030068080d00000e0540c0e40718401d603910048400140c0502d52603000d1441740c54096485404000002401010111241c28415403c19050b21020750302e001503e10602140340031070b65620701072081d41400e121a1307000b00c40c161103911141007418040342c0c15206c1c91280c820013920350741401110b40d4007803044010b86a044032007031186585980355201584525031407104148110440003c1c00112405030521946c0c0040200380341c245058107001b808140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 67939507 1250 67938257 67938293
    0x9050901050d0c0e0703090302060106090b07060e01180501060503010b01030b03030703030b1305010f0f0512060a020d060503030d06090501050915010c020a0503060708060307080c1f02030f16110105030f04 90
    0x8400480c0310540c50040301e2158141b5070b008203000b440782c14003908052041e000441044140700050102748181000c50740900ea000000061030314030030f80c61900400b00003059a288002c0d4105803000c1c0001500204240d03907045008000c100300c0300c0c00640403103000c0c101542d0160000d12801010a0203580401c06040f0050400f061200702e40d25181c1c01c6803400d0f0800b130100c1d0b00c0151f00703108000d01002c0f5100902015503d1076500385c00a28000d540d81c800a200d410165000103052800c00090307000f20380104805003c8a0b01c400070118400041c1a0902601c18840c2c40c00000151340c4c07400a4906000b6038042600c81c0c1d91500364001140c040303464010980c1c2100d4088030020b901d4a0030070580303109150580c1d0320b00007410160109820b2104c3c583c070080b480d500003001c0d15019a1894804034446403444180c55401d00042e10503402c60003800042070030a10007144100400c483e0708102c0f54014410f185080d41e07160000010350f0540003c0d100980300801442c001800101591120211404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 67940757 1250 67939507 67939523
    0x150903040b070b040b070c03080f061f02030301090f090f0f03090b030103050307020103140601021b0d060204120318060e090a09060203011d061203121e0c07110109050901050d 77
    0xa1544585002035008103021910580030360208024003001c0c5c01540e800c801c0c81c0c42d1101c48010161002400d80c040a010f180801145801080380c580e11012803034160308800c14070401c08036103c035000e034030ba80091040c0441c003402c201414460365070764820305100307607171014101c0c100388407646411450041c012400c4090100c988404501540000080d500a601c40e100540d924100c0d440010103441c1d54601035550501721701c042c420541c1c0c0102d504e2002801c1a03840e0558900384400140003c0c8925101612480c03000a0100f820381c00c005c85209514081c0c0c0720108600000c0d008076802c240383d0321a1200041c40c4c8c2c0c04003102403401e4200290060607815010440b41c1107500d640c02243e0086e8001c80b200e100d05032000041010b01d800c40e0b0b0b4045412a4919a001018415541c99104010100c203035101c04c0390000740700f00d0041c00c1100988200c0e00c5a45218642560101815480341105480316a44218100c81c250b22803e03c20041d80c0f0007a0600680f6460b110074450000100d050845501c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 67942007 1250 67940757 67940759
    0x702010608340503060c0d090f060c23030f0606130e06010e030601080d030504030c0f0305040e0a02030601090306020904110f031b0a022d030a030e070906050315090304 74
    0x30820415496040588110304103907042c004034140701900e01d4481c0074200102441d081106940120301540e01041840f0704035920065103103624010107000358000d0400105400440034080d940d4080003812041c0d1320b51240a00c481c3d12628542000c030700c40e48600c6442040024011102d40080a41140b8090031050401c1c005000040c260001500005006444d02e0100503240d0780c0030100c901c085500382c0c0546020750406070150f427500c601035118010303d521640400d080510640d044990982c005000501c3d0582518000f001030b4050320900c410400c0e4032010070307641c4241d8401c8034080c0304140c603000c2c03240c0d03c1d507076802d4080e40185010a41c000d0ba20055280011002802460400c9843d8180d0b80e4034500103094210291046d26895140d0b1030602c00c0b03c81c8282c00141c00d1104580600b54030268414070017102c80c200b08030080d4035050340004a070042e5800e806410020212601c20305a6200d10303221000300c42110440d125a80c2c0c1a400103000d0003202407104245a000100041a64541 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 67943257 1250 67942007 67942019
    0x613110f040e010c09050f09060420040e0703051006020a020d0320160902030c0f0c0309060c1506040b06220b07050a050d081e1e0705040302030610060c0b07020106 72
    0x3541001d442d030316140d46404501000c4c2d0341c843d0581c005030100311002040b81e207100021030100c40f4001c11282c00340c5d82e0380001d0550a03078109200303e5a200445000ba0740c850f21130383d008203814000c0c0d541e440800e0400c4003046840019038030440950340660b0081110400c1e540800040460f002000d60501100d941502e080c0002040080e50b100741e61401000030454044807180280c9050f88101c0c00b0034810700a00c001382c0f50040403110200801b042079900d0b8804c021407a81036118540c04207038010400640011090710104070860a5003a031195140305a8079031060005451114010913403000301004500c00b070070b80001d40544000c8a1401422070076407505140c05146d800703101c0542d0641e01643c06030040090400442108030070707510300428282411400241c0000340d071a6810018082040011101002c03802071000f031806242c2d10700c40c10300b488200038009502c03c3c00140d020b401940c0010b140d000500110f64111a07180e41c540303140d0076a40e00c48801403800540000219502c5080020b15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 67944507 1250 67943257 67943261
    0xc06020406020109110316060c03050c150103110405040209070c030504050405040507080d0509031e160321050408060606090a030b070f031811040e0c0603010e010510020613110f04 79
    0x2519682d000092240c1803810102406415a00501c0c4240d10404012803000c404031006000c0300c085040600f0002027a2500742c4007800343c50320f101d60b148a807000031002c52082c2d050080c1224001c10154040701902d800388020f88808440103500055440b000c198014450104035040c1070203441c12600741030719140020142c0d0800e440075502640316020078840342e07005220782030000500303091081c5440090b2000c0398640c1a200221903400401d0100582412001d1080c002c150014a01240b50142c1b41d01d403150b03039075403024014007540c468640d9031076074107015404031400d8440c200024142643e840b010400c0741d510505003640c20154a40e4004001002024414090322032600d0300896024041001000c0300c0300d0f02c60300411100c400d25008049128041144254101924007140c40083c030940f0034a0714907103080060704a00d00100000b5001500040365040e120126401117a00d2004034040340e40e40401c1e102012800c80d80d80b611800940310000c94420f80b41c3c0034000c110015036800005003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 67945757 1250 67944507 67944509
    0x504080102120a0c0207030302070b07060e1c03060522180209040602070204050a0b0105090d050f0a140606100503010902031312050d050c03100303030f110a0504030519080a030c0c060204 82
    0x194002c1e0020510500340300f1401444122565880180b004900d5611300a5130b0302d45034441c00c90b13000e400068250034000140c000500e11254035007142da00c101524201d49003040c4d8008801e0029140c041c01203071900c0d000300d0b032804400040340368940041000841d60018048502140d2004100100081c0162503036040c66114031702130900180c80e4211401030106a90009000230080c81c50402c800e5016038000041c1e40203440184d89406141020345000391410000c2ca24040c200e01c00c03414032500304004181d140c7c440a00250a880441e00c1d20f80600c401440c1c4d0306500310100380c05000620060066601440d40130303900050a441066454662034540340c4081e07040700015000144201d600f100780d004d011340205164084034514545901c07400c0807600140401003c041e1121841c20f15100ca40c0c010341c1c0384001c485c1c0402e40d10803c804014280e5480341c13201b210b09000e007642801200340d4809900f011140c12651103442c0280d1410100d0080052a000c0001e20107000d1030040407400707904c0504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 67947007 1250 67945757 67945777
    0xc190e220c09140106050f16050f100e030f07080705030723060f0f160c02090c04030b0108060108030403030c02030a0b0c1314130b0d080319050612060114010504080102 74
    0x1030000c03410030b244076003a1460300300c03214511040c0d180100101a03104007103a0080c61005817071525070000041480001844150103400e5115024030f203c81c0e4800415010460301040b041044480360440105840707008072400c140c4800402d20400c2c0114100c00e00038003445202d002070300e16044459955540160050406d04503103c41d1254041507003404011072900070718002d251001e240340c81d0404c4058075000034008002d01e25140754440303007103005001d145441c560081190080340b0703040c4407040c0310350402d101c00d40d810902d10b400000c0c038032408a40c050603500345030301840c030b024210b44007940c035030700c88200807a0141b054449440c0450b0700c134110039000d02014005155183c4030088200c00004040d000ba00c031440d6900d81c80d045541c0c44e40c044c07680c039021a0314040b881c0468038002511a1040b14000380800e81c000081111031a00b0f2000032240c00406101080161101e20902507844d55500c403500066000c034006110250f0255049201018149007082c901515201e000303003a030300440041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 67948257 1250 67947007 67947023
    0xd020304060c030e100b040f020301090504020a0608150423150a1d0a0504020a05090f07091a070b0a0b0307061106060402030c03040b1321020c190e22 66
    0x44000c001d400d004841c180c424503d014082c1e5010140902e031581107801c0c60440ca5969289000c026464503081117143e0980b00340115105e694442020740034040c01c030b13812481181d40e402c01045050203609040e004217050603803c8040c2da294018003000305920103207190031005484881017100c0c03080c20400c0c41182e5502c600c2d140ca21411041c00420328403900070b207500da1660080c0c40c550252102082da440703071021401003242d45030360001c60b054100503003180307400c80303808010800c8400d225058103020b0002170b641e40744400c0e940c2c00e203080784501c000c501c021300e1042040007001254408140ca900003800070380010b60550700381c0c0043d2900002d5401348020803110710b840c0ba1200070a00ca842e070b0200003138805503e146082c1c13254800c5c5200c0148020108035001c80441c2c140c0c400440c0c07a514090744081c0007501c0c403508407015030746445070913002d600501c58009070100e90308103200c3d00d5440c014a26880340e040380c1080880812000024a40580c03d2480303916807261250400d61080c1c443c0c020352007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 67949507 1250 67948257 67948261
    0x2010c120e0111010b010e0d06090609030801080606040204050f01120e030c070306050907060207180b150408011a0a050f030f010212090d0519050a0c15020d1a030618070b0d0203 78
    0x15280b9100314403c0e1400340d150103c45030081c2d030000869100200112140c413404213441c5000c9008101c003071401b408a51815250b5000c1681180249050b80c10310070441c0c05541da08001c1205a00c281e0068a4011884d1008040f49502802a4814901c1303001c00114502203011045031544e0020a14180c440d0b000c030300e040040c03010764420315800c01d595801038910103051a0303001e980c0b40c46038803400e20f030f100000c0f001d0481050164440000044000d1060040903102c200030541c0341c002e4001d01c1c080d94030340b24203c20b00811000a000740010050100000ca07850f01d4200301001c128030304020f41500076003100000c030020070b100910704040201c03032400f9641407034402145080c04056211042c01402c0051000e80264940a4151140b9a10348280d69000309441120400c1d400c0b40700038203400c1160702c0005e80b2140e0b40c000d450009180f03a070802118681e041d0914080941b0002107400d508020040b605d601d00d4101080800b01d150003c485065a0702c09900748181e002880e41d400c01680441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 67950757 1250 67949507 67949509
    0x306040c080c030f0c0f040602070509010e04020d1401020f160308060105030f04080a030204080f0a050613080405040e0c090709060e1203091207050a06120b06160b0402010c120e 78
    0x1052031030242aa241c03401e01e920b041c00e5401190311001d03140c081c414010000241500c1d110104841352a005404001d89071566020042c1d039440d028058a4401d00340310700082000800e503456070f4801c94000302194429112515000e0500002144039510f95400704994900200560020046610381100000e85600309081c001c12212018003401c1c1003140400070b001c1666200c02c4610b40064012400b07640d0b42140c88000da00902c1684d001ea09a401075524070070003030001003505201940190240c0d00f40d41d4074010040705101c1c124200416055086c401401a41019132001c414456410101c0e80048107200003c0e5215a00726581d00010b03031342a4007800a02d91082c503401c1d145005580c040c5480f103222000617246d0140100d01401442d120200442126081008400401025040c4503000d911080000e08030080003c846490b942480080211410004210381050003024107002e007402e034540e6105030306400903006074100310302d851141c4003248422028190411443e00d520710313910781601c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 67952007 1250 67950757 67950761
    0x513030f02030f0616030b03070f0b070302011d030f0903160b18010f050304030305060d06020f040e0606070201170a020403020a0b0c0607021501060e0409050d05070c080f3708030604 80
    0x1c5001d5a458100406129040c141c2c403448640f8421181000707d4030004c0e45020038503101c82548056050b04c03001d14000351498840f801003804500035402403041d045002406601208200e84180580d801008045844c50305c0c2000303040780100003000d4808400611030038048009007500300e0081d005002501554480080307110441c03040742801c0240001d043c01074050300f10b010003000a020b00d91158005001651078120381144994809401c640342c20030380038410007130342183c0151841e0051400108509141ca201500e001d158140d580454280a2003490f44803840083c010200b0f11741c003071101000507610071649402524204550544074410760b0200e502d82100940210207540111400200e144620004070741503440605202c06481e8880020400404884170041c21030700550b030f1100c448a070f024008040f824094594549099140d810b010703100e60064002461035440f41c0682c00140b82c1031810140020806102010b040d00035150510450741c0940007180d05040000070070400389818 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 67953257 1250 67952007 67952023
    0xb030706030507050708070201020a0515070f0e0d060c020307060204090f050c0304050705010e060d090c05030c0102030c1c0e03010509010b041104050a0306090602041d0906010b0c0a02100513030f0203 88
    0x19203000d00040c1041e03d4003070003502c5440b502411180c000140c003002e69000704441400e060384001110140c5400b4526141c0c100400d490800005c0e1495880c500700c5403080080c0b0004400080c00311000481d01e65854000b09800c004007002c0d03000030300c452004102c0a1001e04020481218007162069528000f80100c660060052030104014030a02002c41d0700040c119040d11001c3c20800340b0850304900181c3c40d03024042c41459000e04000019040007024881c4404452003030b411074050320190001661640104801040e140e804405200e10101d0040c50307440307036145503040000c0d5a0082101081c06d4070000c80f00c02003035039110300c02030764a03007020b204285542c50005401d038101801c02e00041c130860110f02c0098080c9442d42640c10a001042d411980181009008019003104184050388070203400c48101c803282c041e41000090300104102110f50580e00c01e40036009030710a5508000200e00b04803010810400306010885444030040391000195005503000fa110b00001d00c10545850a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 67954507 1250 67953257 67953269
    0x21809061006021506040b120709140702030a1404030206180f0f010c15020d020309071703030402010804030f09030c0602010207050c1c0b0408120c07060e0708060a0906110a02010b0307 81
    0x88010030071509502061303194540c48007002c00341c03164440c000003c0c040e00003610724551140e50003060001c1d8840000f21602214210701003808007030351803080c070780c0c6441c0105c40343c0025800070050a1006071046203011284000303540700604194998001c0f5289401490940c1108141020404007a1910084844480104a800c601160000030008000f82d1105c140140010300c00421962800d071550140c0300f029242d10b07011510780c80c00e441c074207a4409042c458550b04940d007000c1111110008001c4074407464060711841c147ea1901c1e41e04a0303204031800d00366030801c80e4a0b480400002e0801d0000401000541d00141c0c4841c50340c14a0f505044d01008914400d1402d02000030300c0c1d114006001d1051600f001c1030b5041d640e65800e001c034507481202c0182200703e400008000d408000c0c0c202800750240102820844201800d100350b503038040e0360107041c41e95401a00080d03102c2c5450340006c81c144d4402c3d40c1c00b0480040d8051005855013001e00703041c015035141c449040240c10100043c0c401040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 67955757 1250 67954507 67954531
    0x21060f0d0312020a0c020409050a020114190c1a01080106050a1d010618030506270f0714030c0d05060105150a09120f050d08010e090307020303090603040c0302180906 73
    0x100d40e58001c1c0c6807003003400d100751106070003080e891580c6001c2c107488250580c028005204488551603c2a1203043e5443c04030b020503417886090002d40d40440940d4060046030a161803440784017107040e1100603006404440600c1c4082e11009044010030505000700402c00011581c1c034140002c000450000c1c0d0800e0803500d6441301890b010b010018207943c1102d1060800d00712640e5182c80384000700c01c464001030002d21a410034406580d020340c5175980103850400c5c241c0c25025107a12203e403a42461040f0b44c4070f55201900078012098440f400f110344550090444460903010b00119010031212401692035802c00c43c01003145041c914202142c0756100f03041c0c0740c6421040c1a002d444401c1c24040c940090333810740c1d0355104001346d00205481c00c680010840301400c0b40304c140101413103c2401000322001015000c941c200800000b81d5481c507a00502850800582c902803050980000f03105584a1004190000160702c0e0603a040020392884031b40640d141c6800480a80344c0000505030f031000207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 67957007 1250 67955757 67955779
    0xe03030c0a0f050f0307030f02010b040209030d0f09080d091d0403080112050709020301091505060301080706030915020304051014040b01030204090312020a020106180207020619020321060f 83
    0x1950200340303904030650000c0d040805000d541001840c000400c44803256a00c40050b0100601d500050f0702c0b03910026527402030010944090a0100740d000d1400e6158050340310042e5206d05034090b6100d00501c03001c7d0300e05010302c55901c0307a001d4a8043e5485040c000304840c1c0328180035075a40c240b0704c2c460200003c8110310346410150781c01403100304148149000400202099400c02400b401751100034082458155125611b443c10369004141c1b01b04208401c120300c100020f403c0c240001920b041b80c03081005410001d1405106501600c1000360031204219410b08404991206201030b43c00b4a015400500307211580400d0b0b40100ca074802d044408040400d020080050b50013403000381580e50589003c10100f86a1406584074100fa4481066550001c40d40d0800158154090f01c12150483c2a001030212030740404000c83c4104a40607405c014100140001041051601440c0e0015441103034503022401c50f080f2600154500001c1701094800180440e40c039040d00e400300521422a111041e407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 67958257 1250 67957007 67957027
    0x106090908030c0c0109051005061212041a090406030c032a0b0d09050618070e0c0d02070f0b0408091002030a0f030f0b181608040c060311040b1201060e0303 69
    0x7408003e08031500207000191070f01e007001081d0080400158040c0c202ca81e03c91003a1a81005800200e50b4a40650803030135114400703c4001815403498110441c5040c90305052104d94180c0a83c2181c0f000140d0100700104c1816846900c1007400650003180007040781401c5151401080c014200d41d080e5a04800556400124a04114004131620541e01a660740c030211101000345c4080000984540243c0041005038980e004691103114000340035a019181c4403614072a101009546011001c0014000108440003d074000c0c03200b2401007405c524400420740d100801303024102e4040701c504801085400203420201a485007000d101c0c0003650520b0a04840101601c0c10410703024109602d5080e2403103400215408003490b1039026104016800320050b041001c000250384028a06030380b081001c00070381c89103c449001311360095050720680d18040c800c9010b402c07465401d44181104020000361019110020855441e01c401120425850440c001d8809040d1000d441d0090300200a50026 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 67959507 1250 67958257 67958273
    0x50903040b0a0e12010903020d080a0c1706031e0102070215040501020c0904060f0e0c10020d2001180f020108070815040509010204050301020a020a0b010f0b03180c060a1101060909 79
    0x103110150f103021146806103000044150700024801c0d500ca52810f4002c0041c1130b404900102078007895224441141c585c0c07603001d402c50b80803018000004080300180e89070783d202c2e0580d807508600d004045a10000181200b086500c04a0000060b41c5e94005988421407c1c07001800c140d507901050700c80d0509141c003001035102c403200c00840d80f04107000c1e40014204882a80084881080e0100803c075402004c4181c1b5035071403024a82d203104101c0b0803800e441c894030024500302d90100030313900c000c0707005003002c100c1d5000e00b10b031400c0d5400c654845031401000c8032100603580b41e4034021186042c0000c400e0001500b0550083c04010400c040c800402c500b000660144842802050f10001055511007000d6402402250801d0f903140d4000507043c50b91aa0001c0c2c007500642c010681d00d40d050341daa00103481e0f1600309206600d41e48809200040c00c8800050b2810142c143d01c2007a40c480071041c000180b03190384000e41c0b00300030034240c50081d40d02d80002d2007040003514502d802044441c00a4079020a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 67960757 1250 67959507 67959517
    0x60609320d150f09020f1f05070309090c091d0f0129040f030b0108010515090402010e0931020a031205041809030f0c12080c130305010b0103050903040b 67
    0x200030000720085808100c1c00300369504000b0768000081007a1080c5800b00c802500b4001c0081c1d10070030004103110047d103450808421845848030080410002c00142910701d600302120503400d02009080020700301c4400c0c02104186c0807180e48400b01c0b58181003a42c00340848501e0301801ca14819801c2002c01070364118075506441c070900b03040261104e0500500060080d224450600400c0406d0009110b0b502d04c1e6240d090324466401e20100740e882c0c14445080310b000300d440170a00394882d05010030038207000304a02e82050040c0340010321041d050000c6092040250750215807002d070b071440c8402c1c0e6021751020042c401148100d15550130482d80009482500034003000c0c10042c2d408075210921806070086a006104e103080c1c003c0f40000e11810b500c0102450786090340461240d0b00101070f024414000c14440c680e00480f0307005d1802c041142180c80f2180140b07500009002085209035110110311700c100254030410010800006100c001019030350050302032007143d4028081400b2000300350080d07034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 67962007 1250 67960757 67960759
    0x1090c030216021c0c090506030f030c0a020105030406090203030c0604050c0109030803040204051005030d03020c070e0c1605011d0307050d0905030d05030a0f140402041523030a020406060932 84
    0x440807003d013040d95144000c0d904002040d041103c00f002610603070b0358000078031451048060340d8003c09249059912440380c4858480d00303400100c0080010740c099809950098041c02c0c00003508501c59010910f150311071101002980d211604000400104004800d42c0d1803080c0707003415a0514554458509000c0500024401d0303445000151041110074282d900400e00142103621812800388041c0c000c0d8070200050b000c40c0204e41c00803602050a8403810300071442d0400b82840c00b440004030b96264024000210b07565504d682c1104851603000c0101e2074040d6405002d540c3e02c9080c1c1c035207a40780c09000c404034000d105102c0c1d01000a80e90219000a0390f10f0941080c0f90b4907542c0020100027003484880501070a403400d07211030858640300708140c1c8221300c00d0350100400b00c0c1d43c00352041c1d01d806d1403059040b00005031074400c1c503d6140c48003162a9500180c1200d85901c0d541d03001505640150b00b0410003c0d5618408015008454085210501c001c0801d01680c2c0c003d03200503031000d56020b64031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 67963257 1250 67962007 67962019
    0x1008070b0306031c090611060c0414030c03100b0a0806150910120605040b060420220b0901020607030902030a03030506061303080c070501110304120c0305060a0501090c03021602 78
    0x8a0303d44060001d0780700c0c48104412a40c0780281000d020b02050700c14017031080010302010f5841504180003409030301880c808240103051511f0904203000070421a25245d4050081318100225503c0c2008000d28003042d0386004640d05266805015420129601008482e440a800c5c41808004640301b03001c9042d0644845240ea80c510074062011045a408078001c44419070a036410301c07500d07a102c140034a01c11442100c00c0e4841008100a80e01001171560307a0401c1c4040314900d404c483c40040000d000074410600c10f08102810000d0184041d03400340d07018030380004209400d5070341031044951090240c1801c0140c4c4880da00440e54a0703039041e10003410705a030b540103d500d542da510140c40180c0d41c56011200f0480c0c41c2c3c94098465000307107036034182d584982c0002103404d40c05000b4107008098000000c40c1481d141c210f480890342c0006000b595001200200403011440622100c0e00c42c41c10b00c0030110311940344c5200002150b86d0070308140b04041c4107100704031320b05030320001014995804a1307107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 67964507 1250 67963257 67963261
    0x308070c080709021305030d020705010f03060503161703030c03060f0105040e1503061e040803060109080319090501050c060f0405101404120c03050409020c0c0a0603020702091008070b03 82
    0x10050040116070412511881150381c0080d800c021900204000d044135410344406940c0d41091566407690070b4507440258100f03201c14002d075403061030155400c03003003440c000c030703070283d541c008603041410504000d0000c0300e4405041c044941c24030b00c40d0351641a104000d40c614a40b40198040f503000203480b480c45028016a0501160b1058003641c0141a8501c000c07130040c1428144540e01034440981c007406401210b0018442000366480500500e0745050b540d2016030300c55549038030f154001000380381031000540380030070300d04000c0028050041e1070301740f103c13082c203951000944103100a40c403290410601f0081d80000312070214040c0c0d00006e204911440a07203652034810f0801150081c64189185009070801c42d4001c1c0303034480d6009601559428040c041404070131a401e07902194091b01041d02040200000c00580c0d0040042c1900042521043c0100d0000aa640201c0d030384610700183c3c001c90200c0c02e510307040e4400ca410482c1100c00e103000502c0d0000d400c1e10380c0114810749a1190300400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 67965757 1250 67964507 67964513
    0x3050d06050603011d0c0a020a0320060c0307030e1207020d02010903060e031806030402090115091508180a171c020c0706020d0305010302150307020a051b1302040f030807 75
    0x180907050040440f500c030b40e1280240420a5860450051000c1e96040843c0e0b10500d08000c440c10701c80c0d1079018041c040703030645041d2070050008600019a80d014072251203440803d10145001e004c0140d085a40c902700b00c0002419a1000701801500743c0104900c0841100340c0c40444828544c180d81c000300241003400141d600300d0482c0c1c409081e440c14060316027440317031001c0300406050044020041442408906014440c082218001c1d08116030500520008412968405070b20145141540c065900ca5420010550101e40c5200c0484c03001400c1c88205102c62240c0103050000e48001c100203c03045d21101113a05d42e00b8109101c060000442000400419800f15201d030034114065644111864000d0b980703034a28800d500050190300305480250348a4001c05040b2500102000c0690b4800c0240203520340c000343c055070562164504030000201c040c4000030f408402107506081c0407440800b88052003a0f48851762404c0c5104000a105001000b100f00054035000a42180c036a03010380317 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 67967007 1250 67965757 67965761
    0xe01020910120c1b0b040f050d0207050109120b0109050705040801020f070b0f0f0703020f09041508160b03150411030405030d150501021b0102010f0c020a050f060f0403050d 76
    0x408240d0001c0c41852944916500040c0c1002c000c0d440302ca04010340300e481e1800f124503210341113841d0040a89608260049150400d480b41c005001d04140308002c501940d5881c58004960004c030007507084030030100324540c2c00264610040000001c8080e00c5d0540b40d544143d442c0050140f03c50072941c81012034203143c45441170f540900300c03010007107590703991500402107150040e440485002c0760b40d00000c2c0700240313806078046c010507041426059585450001703801a420400c24000240810b120840c030a544c1c0d030289115194860062004507400d0804240c01c048091000b81c105000e240e070100a507400400032294805403440f02548000e8a840006010340755039100030a0300007000c07050000703000011006221640d03802008214505075042400382480c1c00b44100c0f07000d40c0003844405800c1e551400360090040b070503c0001001c01d10480c2080443d120040c4110060340601d01a408020040201d07483e49083d000060020707280c50a480181d00340c0051000b001c11401241c80401c56002d6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 67968257 1250 67967007 67967017
    0x604060906110d051006020c01020d120b04110c060a0b060a1d03120a0206010603110909040c0302030d17060906150a0201150e070f03110306060f0d0203010303110d030506030304090e0102 82
    0x1040b00155102c0c4886006406458243c62008082504072400200c56000189a0b80c0100e07044c5c0181c5103000d0184800d031494180821006229529102010300c140c0d5141702c0c51199034600e10040f42c842600240507071400704001c001038980792808450043c180c0c1d4180580340c544800745004803e500d5a203041c0f1038440780d25011650103116180402c00c010f80c516010f0081040355508988181c0c0e603503101201030312115181a59020003c112084c101d08160010542c410300648040150590769804246000000582d0100140f03200b81500c1881011141c816000b281c1140c405c1402e0600400003085544078801c03070307500404005100b80140f8001c0d000700b4110001841d03080c071403507aaa01c284a12035411914000056001e01d041c11085000c0d1003a094511016820380e030035560b6080034001d09074080d030004e5100c4981800507a0b89c4515a000550103148a6501d0104400103e4011b500d044454124001858280010031a141c1c400205403811110b4006010400300743e080c40c0c985c024424 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 67969507 1250 67968257 67968281
    0x40e03040312020c19060f0e210c040617120304140304030b01150507030206150a2312030c1009030c020306040c0807060207050a090207030504050307060809010516020604060906 78
    0x55101c200910381c3c02190388694418143c0f10100700c000001000703c1101c0c0f0078040c007800b00c0c001c50020400b49110f030040c0740000c040a0229402205400000c000304080314016020030740c805605035402c0e007024051a4000e200d620000140034410100050f15401e41d02d50509090b803010001030140500800245a0f07000d40c202500c0c0d80710f0301d80c100501085001d020321681d01003007d91040c03282d03218404803042c40790140c3c090041900e40191400c1c0c40019654455070224002e20701080300c4484400e1800c0302070b0113440703649d01481d020051200c045c1d00c00300e2000c0e0715007003445011054540420000c0c0c9a0780c038164009220ba5162509488900601401a405d445032a04000c00c0280700d5180d80e003aa40c1e0b1000700c0b0031aa0361003800b240c2c0c0d01410b018440d0445603c0340e04000505180d00604400c0740b007400c02c5401c2503181c8001c2071030030450754080c0000404a03824002e6280d07081c401d2603003100d542c602c00310900c00c00e928003a5942801520003040c1c2c5903201c074003600340000c40e4000758141c15 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 67970757 1250 67969507 67969523
    0x7020901030c0303081b1b030d02270d0b04110607061a0108060301150302090603122b051b03092802030114060102150c0405040c05040e070905010905040e030403 71
    0x103103a05211042c06941c0c04100d010442400c04550316004c40c10040c0c100c145010000b030314002d05034255a0341c2024a1300b002c00944424000d12401c2d29050001c1c1c070002442000c007610a0394400c1480b00081c00b228161800b0f08a110b80120108011000fa0750748260010703107007034220005402103250b40c441e4000c0602030b60720704089500c2c100d801c244503024021007680c1788000c507120041098200c1d44941120104268106070400040c10300070030442e800311001341902c00c81d150040c0075407000c0d4042000004801210b45020311407030309080c2c0e00b10f040d80003480200070340e14080c410101e00e0880c6008502041e03202000242120400300201d00090f40c004c2c0e901c4100401ca214940c00a03500303003500300d2082d428804000c3c02d1f480f1810b0040d1007420f0503401010320000c61098406140f8001e400500609002c00c80400d0310b4840d40201d0111130741c0c40d55810b94807885c2041c070414040001d070046042000401040115a80c0851050143d4201325000985000c544001030300e14822a440141a11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 67972007 1250 67970757 67970759
    0x100305010903080106030c0305010509191806090c0915060302070212010c020105070905030303150d0807120203040513140c1804090c03061d0616031d070f050d020a05060307030207020901 82
    0x343c0e000103694120344094030b0a001c00110030350b0a07002d48000f401801d0300125000000707409034980f840c80505c00d2802c0000060b03400390800c00d1030740061907048161580d0344c42d001d05004002505082c6c400405903620200300d289401d4802c2c0d2440e4030320307202e00b004042c1c02191a0040d0360b190300c2c0c40c1e003540c1446002000140c1041c00068041c084c122001c2000c6a150100010181070100890b445840c817120103464000c04030741004540b45a8100503519807005009800000b1001043d0800450060b0000c40c0c40e24903003000c0000307004490f1403082d40c0318200224414000c200120454224650020241c5c455400100b8841a11014a0410361084c00c240c5c480062044031181d090584e40208014801e840001c01840e80004101d14061001d0303100e070000400e00203c894001c110701c4540d203404512a55440c041b2148407200b296080d59540002070100000d609005c074a000900058684244031020b07500000c10118031031040f07034000e5100200246120f48268116141c40c0e0340284050030315 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 67973257 1250 67972007 67972013
    0x5010806181c0c3305060103020702090c220308181032040f1509050d06090204090803011403150c07030c1407060f1403011a1810030903140c060106081003050109 71
    0x490381c010301d0404d001e103402d0209103994400d00849103056000b90040d1500d866590b0110307a01c0d07018030f003c101c1105240035225a52042e80659034021805050070945403098100c456209506607010240704003641e890210107250403441600041c1100a000f482510040400d012014032100a20350450303800035002c01d2081c80c080c6098181d82c079003500900d2002c0d121a040c1c034048000d010f00d55201320200070480c00210b00307410201c1a18800b40001c256840300d50741e0034007540c00a81101c0180464841c5080d100d0904114406041e03442c01020191810200703003011a51096480207410420b50901d40c105000c4006401e491141401e411109183c3c1e4600b4024185500c6000500008a0080c034141c004aa141c003640c5c1624100c0c9565409400d18407100a00707a83300c8075000140114581a0104941c0c0306c10b92207004030016240419804102d01c2c009040800300381044a12190038003442c80c0c041d400140b40d50542e5240c0c20700b65100e45580500310010646035000400395803d104c1c180b010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 67974507 1250 67973257 67973333
    0x1b0305090f160e010e070806090403050d060605030415050421020102040509010608010e1510030e0a0f230102040320010207080a0305071205190e010504030605010806181c0c 76
    0x200e0f2010740c42c149580c0d8036411482c46202d0b0540310840001d208402044440c0745c250596500301e4400d080440c50b0443d0210701a041da5101d0b404500403804c040100401d200c1200d19214502e104490108050319080d6507107034009140c0400318040502d6400d41000180c001d41c1142c001d044001e01ca95950342c0c4d1990001d024410901a0303007012691a4045101c80859000f07031102c80f10000d0102a0714a420102100105113500844029108aa10400c081240c1d8408100700078080c0910400782812200040b5001c00146917005a44c1c0c0f040100708080350074035503a03040d48841a0712140c03161403c840100e00e084441e40020800b405070a03804000c2540020091441521640361451400c05410083c2c8860140c418885418240c002e031600303915218800c40c10149605060080c100354403a281c0c0c804491007600000c00036808001801100380d031003801c0740190344c036420041c0030300d00380c841914480ca40340c0c2c0d61280500002c10880002c00c0f4142c0c1c0200f032180754040554900c2d444251030302d88 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 67975757 1250 67974507 67974509
    0x80301080c031912050a030f0c0f02010c0f0c02060d0603080309012702220e030d092604140301110307051206010e102f031207031b0305090f16 63
    0x320034468048440c6510f078010440e80c0038150424030b21080b141c41c82d00281c8103a0f0010096900b090b44e1440c20b441c100303a0f10700c9507001c09901555a01c1800040740006401c54010003c00b10030f101ea22903803041959030000910444c00e40c1514440d0300d51172a81074100c05002150001000c00e24040100048000b05600c00c24140040c9504003114280411000c046c000b80210041d40040c3c004005240581501c08020701c55035560300001030340c01500c04000c1c21a0030504000f01540d40351504c9500b84103030707400b4074a019070780c902418003002e0520502d01c00a00c103500c550450304244a10201301a6420f60000341c440f2811842c40e81c0c2c0b49002c0c000100542c0c442080a5040c0c540305020940c1ea512a2502c48010000580030160011444500b560718000701c0081c491030f282c000340d140d515524200820744280700100001c54488651550344e6280351001806c43c4100361400c000c1c0742c2101d88c80102103c080e07446050000703940e00c864036954240312080c5107002072441550030003503465504e2581e4030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 67977007 1250 67975757 67975759
    0x1b03080d0b0406052b1b08010e01020408060612030c0d080412020109081b0a02030f03041a130b18150307020106170703022107030b0613020c0601140409080301080c 72
    0x101c0489000e080004407849402083d401c042c03950640700441003413210343c20400c50008100c1c1c101d1912540c0d0001e400f010b0740c01e50000200000010031840c03500340500300c541c4502e43c1c001e50034a400d0907140d940d80c0c1c4000b803180d442000c0c03000500300c40580134000c4400c50680807090f103c00401c803c0c3c000d41000420343e403c0f60856000c03000050084d1044c40350307551140e40314500c6881c0a4541c400030b080d40e8115140c02c003d900400100d10016541007101001d0110810059612145030040c0009039111001d4030a02c4c01e8010062070749100d45d034018043c03c1d00c101c540c05944510031803d08252603c80881810380198100c01c000c09508000c00145102d0b015aa0083c040c2903228044110000c4251a065040350300000c0d046c0010300e400300800c1c0c4802d0801a040c0000c010ba200d40720b2601d5480d078426900303154424144240c03800c00595444003004003020541c5000e01ca0f20303005949410500c0780040c240c00030102c0340d0065030b40d070b00445d11079508140503d0712075841c1c80c410340e2144d0610f8055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 67978257 1250 67977007 67977011
    0x8030a090c090513030e031608010f06050108040302030a050f04051009031104020412080a0e13020309160302031519020d02090301060905130809040b0616020321040605071b03080d 79
    0x140616260041134850b000d2038402c01020711031aa001c1d038007807020703541319580350048070304109401606031340b01002018008000700b4550f06809003a0110345268000904004d051800c101c04a6000030440c3d10743d0041e4034002d80d0ba68a022001c00b81c50180b500700d00c1d40211102682d150841c0d00c0020a07090f43d02840558170050400400c00040384141e114541e0182c40c0c404085010800000c090f1002c5000da080c443c911519035000560070602e81c501a00005a012084c030100c480c042000450f98800c01412504c1141550006a035980441d1607640d200b9802000151840c0c802d04111640b02042080941d1a11903ca581c44040e400403503605001c1e628003000000d071034000c0c1c001c40d80696200382c80c4016210b4aa124100f00740c1c46927001940194450220040c1521980003e103800c1129480c2d433040071382c0f0b41c8109410302d030480d003200f000c10030000010a94041c0303d008032412504507040543d0745a141c0e240610b124880000781d0485003400380d4000092100400003013058088103c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 67979507 1250 67978257 67978259
    0x5090c0315010f03110f091312050f030c0304050a0c0b0403030e060405061204060b060d0203071d030309010f0c1217100305030306010e1210060602010c090302101b08030a090c 77
    0x20740c0281109200d01caa46901c040d0003000401e05e410003100c80c007400502410046c0d03480b0404a491080152221026290420040760034000070041c503540c4c006241c0b80003071810a0030303403a200782c03400f01a0030220352110010100b81080020000090b8080c0d10240030b1206540c2c0b40211100303604648410b5000c04d245600c01c4003680784c00130442e400c0d01c80080c001741c189a40c80d00c1c40059034034020012118150b55954811481d501e031800f506408003821300141e0f482c5080d60000f41100740c00c0c0c07201c4510182c00074004071103640100507101500340030310300f101c140e08030340750121000048400f015000c44500c501c900c11107a40041704480708503040340e0084440e15451460411010141301c0500b0f01e400500109100350f00c2200040c060380f000820b4080b040c0d80f80803069040803407108002d0b001e07680d500001c116043d0207005046110711103082c284101850364003c191240b010490031740c2013082c140b880001644000020a603483d420003081d545a28000c4c220100402070b079541550404541e1030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 67980757 1250 67979507 67979533
    0x70f02010504050a0303050405030d1b0e0919051519030b090703030c060c03060b12070206011a1c020c07060206040203211801021e010605150a090605070c0905090c03 73
    0x3075103004a5105004200342d2041d51402c4000f020090b00488a030f0108015042401d0080c3c001c030802c51052003010204811600005003848900040081c01030b600c030010844a4544172001a4034801c00d80c1000c611075440c47c845032075080348202c1041c0d010090000800340890309040500a40e4416105044c007074452407841656403007548030041c00200490030f14000103c160b004000b00080f01d040115260740c07249400c501981250140d5500101041c04201e61a40d04209481c014904030078012030044095284010621460800c0000b40500340d4007800324481650480301d0195805013500c0c1041e454541c02502c640b42510283d200b88541a40e4031410b80c0fa04003004904402501580c2c5003034281d0300200300c0303169801f50b002c1c1580200c5139140c48030070790b40b0411107082c0702ca03800020f80207060a0401440e007482c10022012403009005840c0c0d820f8018680c10240c84032070404036260a960720b030001e5500c4039a0002c421041c00c14062080c410000a422520810100e00344c5841c2a0040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 67982007 1250 67980757 67980761
    0x31e0d050a1803030c020c09011701050606090a0303110c090115030501080c1c0c0b1305040f060501020a030c1e120201051e160c06050106080106110105060922020d0506070f0201 78
    0x1d10084000b104410381c0c0000603019a001080148007401540c010115030b000040d54124264058401d0f90011640b41f40152428403501c0d604c45011511682001c2e180400b18080381039030300008052003c40b1122074403070401044106440e49000300040e20560b103030b803400c542c55010b4180280209003004004101074901056404c8020800307032000300321014440421a08120131403050b04d101d02040c0c0003092010412004125000c02207c22002083c40c080034041128007140d2000314940c6819400e003c5aa40420300c8040e446e01850300e642804082e05080b0000d03894520321901d0071140d60001000c0004081415603800d56603002000117a885106440700620380950391a61040500001054000358a843d03590428092130619030f0710000d83d59260840300e0a80240002c84c0310340c80100489507001d00c5241c0141e00d03001c001d0082c0d0070000f0204400307134400b0b0040000e440454040c07049004c841c3c5180300744140c0003010442d40c074869041c11a01c900c0140c840c00000340194a154420b64014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 67983257 1250 67982007 67982021
    0x1e03030106080622050406020a0905030610092403060603060c0503060a150e03150906010b040b0f090112050a06030309050f01080a090c051f0801060f1d0102031e0d050a 74
    0x5610b6881c0203940b01404c010090380381c01d514a00a003200304c01107140301024851248100e00c14480166200c011050103041c4420f41c0e40524401e0b03010b10b0402440c40d440710303001c400b1190450700c085590540701081204001b0002c0f421180302c50101c80c00400e0088680103d01182d010307400c100030034009100d044034288400c55419800c503640f9581004010410360341c000f00d40001d454000d0001800400180c1040d00007400f9a00030988641400038400e4284184d40c014180304981c4c51800b80362004c0300300300340242c840002c4081c10100e8192616401403260030402d401c869410020752400c0203850b4010700c4d0b82c0c0400e80010300f9120380400d081c1481c0a410f548240141c480c4c03c420703550ba82040018085c40403080302d1003c1050710001d0703a500e4540208100143c106448980040503ca0040c44400160305c5001041a02002c070050146c0280982c91400d44c0c5401d900da0700300f440d5005138518894103890240d41c003400300304401504808c8020b04400041d450041c4030781d84500c20098192410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 67984507 1250 67983257 67983269
    0x110409030c0b042301090204110304031b020f090103080a08060301020c03040e060a03080a0906020111130b0a030608071e05040c1b050106030618050c0103110a03020a03020405121e030301 82
    0x600452030106a2200c0c059500030300c84c4401d01d00c90200040306500e000080c0c1d408664507911581000118074060250b4201c11500c0b005a60035450036072802490408007200404060620880110554039100c88240e5041009841400c49507500c0c5041c24003540f100800d00006108100070130041d10f8103000303e80108651100450600d4109905076130444405001c1030f500100e0394000000003078100020306051810342d00c404d0781980c644400a403c1d52a0b03042c0c05240c000081109040c000c56120039a41070f1407542d00c11a0b251401450b0907001030405800500c0d1074410080c00140e440400781456181448810030b00101a544205004c241c030081303141d01e00820030b01c10503040d44103901c803600013030a400f9400100b0355640e070344c641000311510301c1011514100c02d00039000900c20300700214140e503c020301c0c0800c90b03030b107482d0203820b400e0141041d1300f810180c0004518080f14426010756015040041013207010902d02c595131a80d94110000c00354800c01e45030141200502d001c002d803412141 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 67985614 1107 67984507 67984517
    0xd050703030f080108060c030a020903010e010b130e100504022107050f090702060103030e01031413020103061e0504090303110706050a0b03070602120702040e03030c040311040903 79
    0x2c121442c88010301c0401d0f00108000c40e80040e030076034000d00074140640c59444417010710010340b040d00c2001d50f0640c20300d15000480310042d4042d04101004881c0703606d015540500e12815030b440d0111180b80c6403c0b0f03106401c0440c0c02900001e621500c018540c6412600e00f05581010b45030080700030046600c440e400b400035081000119010340002c6400000601d81144025950081408001d040140e0400c0c15291a4040c0c3c118100e410074044000c45546004d00a034550501006000d900103414010001a10411500b80d036a03502a01c207401c0e00020306143c1448090110760208400309075035900350200740b801c00f1020341400b80c4100d00100d814100555003006a07003042c00014400d1b00000010045190000707a13065200c428881080d403603600718000075000301503075840c04000e030100004112250314050300074429a4803400000403420100402e00044480307002c4010003040d = true := by decide +kernel

theorem cover : BRFrame.Cov 67805757 67985614 := by
  have h0 := BRFrame.cov_init 67805757
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67805757 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 67805757 ≤ n) (h2 : n < 67985614) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
