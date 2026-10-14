-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0623
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:47:06.796784+00:00
-- url     : https://prove2.me/submissions/e3443111-97f0-4235-a21e-2ef7da330c11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 111870503 ≤ n < 112050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 111871753 1250 111870503 111870527
    0x80c06150405091e1c0801062706030911030d0e130b0a0e09070803031303030c0c1203020c030d05040f0302060709050d060c1b05030c15060f04050601170c030a0e030a 73
    0x41c0c0d40010403a13005010034044c01510318081d40405005072002000540303403040c28815100024906180c2c40b6403000300181031a56544e0050f40101c0d60b500d0000228040d010005040e907a1007807600403081e040e6820401d000c040b4400740c840d08601e08600301003121a808044c000d5420b1030070180304200c075a644801c100c05450410403444035a0f00d03400790740d51402d00c0355000041188000003d1114280c003c3c00b20a410728400c0d03a040c13150344008001101d1601411000070300c150038144007040f0f000c1c02a000b51105010403021a41000920040042591015201900c0380d400f0010110149a41804101c2d804005030a284000c246000003003105660380c2c9030003404c0a65222102d100c8503208255251446003044181c1c4495011801c2150726640000346894052003441c0003c007411044001c1032f407040a004184c010300e0051603040c070024000041c40345040110054481d07402c0b038031964009001b04000c2159945a20340080b286c002c0303a0400140c8401c42d401844a4680c0660101166404c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 111873003 1250 111871753 111871783
    0xe03191a04170403061409010213150c051506010801080f03071112011409010e07081906060e0103080c01050105010c052d07090504060c05030403020a140307080c0615040509 76
    0x115039950b06102905074070103041d602015400040003c103000705904140b4614203850391000480e210860541d00301e104200c690030170054010010001401c0d0303034282c8518443c080c24071a440c03c076140c3c0c2d40c904000d02c07001004200480c007020301066503405444540540903a00c02040c2441803110138903602c1c016144010b0002024940255039038803050103400240c96007800034801080484603d00e410350048036106200d600c3c1c148016103060000800d4021924540c000d400580048803228190a020300410794a807034944c1000141d181c122a203113030085001d03c603000d844424400c080b60079960182e1002d41000442908400403a40c0031600044013441c164003d10f0604029015404aa6174004031444500031010002031504081d00800d1241d88541c0c8100310030704070300c54142c0b035600050b94050016880901840e00103502183c1e883c62428a41040b241070102c1640c0340ba03402c0d440404c100d0702076000501800b600140180340102c0342002200d06001e245401d0900c243da6580000740004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 111874253 1250 111873003 111873053
    0x303021e09010c170904054002010e04020f04080f10020304080f220b0d05060312090909010f05010b0c060709030206090418050f01020304050706020f0304030303020309030d06060e0319 81
    0x10031301c4004110f0b030902c00702910501c900d05d0488600c080c1030031003030400c0540341119031803a0010b00b90b904802d08540b84294040b582e01c5000d40045609241000e03186030082c0e4200910b990003400c44000e0402400c0f804014000c01e440e280300142021034808020705c4040c010b000344000503c80b2402d07038400c803034042e07403c0d500e074040780002c1c088134015445c04811814501002103605240d5900501c003d2803665014801c9480b25800e1503505d44140608880c0884240450401e0745411003003540c0116100b400800d41210134281b04044a000f82c3c400342161500040b101000982030004687c03180150600c8940035156030003207043c0d03105142410b407017265503a404088196007a2f80f15000030340c20508941c03410840000c140c3c000d605c01c0d03d05a030345110350680040c64500c0011101c011380d010401850820786184d8055000e90006050350b01075010520048049404034804d4600800427640c49940d48004001414180201585e03d0380d03031000b61054800200f0034040d0484104001060410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 111875503 1250 111874253 111874283
    0x60507031b05010902152a06130f0501050f010e070302090a060e04020c06011e0803031b0702041b0909060603020c070302060702010e060708030601090b03070c12050c07030303021e09010c 82
    0x341c01007261582c000e5000e04030b0120340d030180503201c001d03250340344076201303c01c0c56504083c4007c0c00001c0382c44410130003a4012000070f255440981146071020341f00359216030509100380d031520b003501c4044641c0301d0a050301d880100400013040d06c103543c10035814103045241400e207002189149516003e604240004141d1108242c1c0701c83d0704540340c0540c4042528402d585429003464200d01c1c207188011790350085800850780340400710442e80184802c00600c2c40a00c01460300480781e400c2560207030380c0705596925400301019944484550100c003540d5019119042c00c0343c3c1f07030448641d60443c2d010148140f0450f8501040080c1d01002d49404558458a8611a1004894013000c8154103604100c2c046644402c008401c4061030094109032143c40001d41c03903254503012400112554000120f041c55032001044003181044500070103460103600c0c100f1038011071440c0c441203503c01c40c0040c0d40041c10b142d59454401c502c5110310759810102c3d25004107080001d00e01c200d0b185005c2d0040c0c660324582c7c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 111876753 1250 111875503 111875513
    0x2100c0302070b0a02010501050411160b040203030d0501090e06091903052d0706111204080a0e040e0f01060b03072304050a06080702010518120a02010b06031609060507031b 76
    0x24004000f2000030994904000d00005d011f00405e201c4d160042d8145420040040325400580d2500013a408062203118815244c03d508108080d0040c0e8250200700b000012000300740c0540c80c060802c2ea1008226100c90200c405c1c54a900203007010056045100b90741e20140c2c0a03100050402c0d054030300303141c0f0303150007015051800560040c0990b403484416103c20402e10b2560180261500940d0104540d801810890145116140c0300d242c2c41c800750070000d4006010500940543c031300c9031a01e803c0c2c090100c40032408680c048420700400380d001c0841e90303429007001d02401e40944502008681981480c1b000909080380300d400c4103550030644401000602c1e080020344004010040c000603c940d07580310042d10860301035030307060b005508080c00906081100c4c4100303414590800000d01801a500380f0240300e6400040060003155201e040c10b182c0c40d0740e91030280d4062809034107410328952000201400000f480ea02240030702c80244004c50210703800c940e0700f9a0a0032507492400381400281340c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 111878003 1250 111876753 111876763
    0x120a02031b0a0e0f040209160e040c030e070e09210306010507210f0e01020a03090302040203060d1406010e180705010318080d0f050106110c040b12070b120601090302100c0302 77
    0x1070030700c024210f00300501e031103a1458041c000c6000b95011200350b16100304800100d0010a640000705a07042c1d98280700c1d041582c400100e0061a00d400503007806000ea419050030100d030700c102034503c1844244a002d003070034400c1c4a04160506040001c0d0740f00100c080f000349c040107100905002c1c002c280c46042c403100c91401c0c000c1c40c004511860b46251106806407000b44541d000000150640410207150750001800107a05901600c03166503491841e8200300c0a07600060219401501d00110140060300030903840d602a95001c000d0801c6604140082d85280300080c000313040040854554590ba13003000c500c40c2c003a00c00a10f008608101c0500e0100c01d03001803100000c094170300014503800381c1000c0d603200c191070303c100c0102840182d80c0c0e1401200c01d5a020821040c0356005924030744a41d250603404015194009848910301423480508282810280c2d40300c1c10107000000341d00100001c0903004543d2208003420440740d8a03080d500030a84d900c2801ca078603421700884001c80e0050500800c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 111879253 1250 111878003 111878009
    0xc01091413230a0903030501050906010c060e07080718050709030f0b07212415030e0109050102070c060206070302160b060d020a08150612060c07060e060c030402120a02031b0a 77
    0x2d0701c0d03501e4108242c090009104900c01503000030310300700002c18a4034000c80e2003405400305a4a98208581a8643d40010171300301c0f100401901c951030b400030300d010003071003443c005000e003158100440c02c000e07452005844000f803a0381304010801c0418000500214100414580c024243d144150754108013950714030211405140d22070544150079103407000d940c209607104200f08107031100303417011340c2a20040c4014500030100c0d1b035610081c0304034005200e5440288200d03200b09c004a4100001c2e02c0e41c40c22030380001410707150030024101c10710200e40c0400c441740d003088507407a0441c900012040c0e0441e2541c0000380c02000d400181002c00c415948004554145640040003d0740e40c170f0303480000700e03610707003921050394641408603000801c01c0c54007040c03500b00742c0701d403a000e05001e607075101000c2c50741da1082c081180d01d6543e6900d00034841c03074100415445080d00f0100d241c1e803814180108441200c0c0251040c01c1640700284410041e2004501801040b0915152008409600c00081c0c490038941e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 111880503 1250 111879253 111879311
    0x3080a05130b091807080a0c0306031a040507060503240414090601080f030304050d0806030a08070b060111010e0a060c030204030f05010c48050f0c01091413 69
    0xc1d9010480b140b0700c200404405408860012901e90b00344020054400112900d03000f00d29020001503200d40543c01c0041c5202d0640380c00180035840380d0f41c2c6c80003241c41400c00b4001d200d040c1c007008101720041000b0310113030419081450462500c00c42c003059a100c13800d03014240c41540900010706e070f225a00309100c071240c16440840180b40040e0720135902d440034447c5450074440ca0031031601c118070110440380650340110203040c1d0001400400c0d103868101519094051050115540108070380764050310006203c3c3c218544075040c03c40004000000307800b007442e1107034504004c60340c56040008201c44030941c0a003000c02c0007000f44a043c1c00034050b56102828214107100c5020401a040d0b0010303034607100719140ca450388803454401c9a000d5440b000342c43e250300b266a244040491804040380c038003901d0f80090054003016913a0701410706079802600c603802d51100d90303500015a00800b04030043e1184084500c0e0141803500002c20b000d401428050360196248100881400084180e50440081e8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 111881753 1250 111880503 111880537
    0x218030307060e0705010504050f0904140a060209101b0605090f010606020105100b040f030b0903070f050114010503030c03090108090c1203120c070305030105130605120d02060a021303080a05 84
    0x42d0070010040c1036a4010544103004031407011800c0e40c011000d0710255103000d02030040c1c901c184018446c90000103403007070706c0c0e6456000c07420090b0b01c42040707a0280300b4802e101c096218110310701401143c4d2401e24a10302488540c1d90f0004043c24841c681090440d00018082140c2d101c81031618100b101c4030042070300035400c0480104440d80c05400a902561340100f01c10050f03a51022945814001e6002e0818608074043d010401f05501444e0b003a08200400283e070319041e19607a901022103116401212036035100c030969440403070101c00c090700426007540510315080401c00e9003500d81c440c00f80d810b4113001c00540824861181048008544640904080c4521070780c440f4107030f07a94002e465008003481407440090b450040407800d07651b00a90603220719055909150422141040031900024a691f1319400000d50b41c0c2d400c00b940702e03244091805070007100da00b0203000781805030062a0640701c034010008800a04c14828180084a401c48030346901c41c6ca42c01401c403624850004a08280052 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 111883003 1250 111881753 111881767
    0x302060d20040816050d032007050d061a010c03080703090f0c0b03010e0703060518150301050c03071107050d11060f030c04050a0501031404080904180501050604050f0408090402180303 81
    0xc0d5000304564030800c180045543d401041400c401b10350005002524200480c2c0c0100b452201206540c0f00c05010340e090f594a80000c14040341c2c10b944159000d94550048804086a984860301a03100030710b01810004007548000e842500c025298400701079581043d8014048500c40315114150f000c042d080d03001d130b9103c0035124650070a0041c242d20580120115010324064030071082100c1d00035101003280100780303494001a0b1001400255568846030341049255401c1c490f551140c0010340500f51203062081005003400d80c0040c242d8800ea10050081c00b05980c0c8820312854503510440103120704108a01084030b5008030214110b041d840072091104001074103010b00140c0300305645468040d03507140011003d68406100c130002424681d4042804241280000c03c41c21401405c00705055041d01c508230110b07c1e580c0720546a99540344207010291a040c00307801d810089a03084880b10f4149900d0f107015500c911038556205640c001445d00700d22481401401340070344010300f0750307817030303180c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 111884253 1250 111883003 111883019
    0x1103040602120601050705071e090c030e0c2e050c0d03052203210213030b18030301150c02030c0a080d030f02040f03080904060b070804090c090302060d2004 69
    0x101c5090341c80c5070b08411001603682c1d4441c00a0350b940c0343e000001008110304c1c2c500e00d8030706066540048018000000300102c2e4003943ea0184030408501a0360001b040c1d00030840b000d0504581c0e00c10340c0e00c03500004555402007004500304015800d036910b00030800a003204025900381c450740410744014011142c2090540303815a02840c800c020141d540e04500c0e115404460408030030160040206203002d001190b0000d0095522601500c0340c0f40040c42c01c00a01e4900240701050340c400c031040000c6000700301c0d0b104041e0b100c0301221a07500c0700440c02e650520118035114414002d5200030003100d0b62810003955420010560b0045001d000e450072039881c4c03100c03035445102c2d58014001003420480d1407410071703d081c4211000c4601505801e44940e04687d60081c255100d81c0045511a8860130702103030825a2000401241e4070070306009555a160006440030755801489000a200caa40c0003007000da110322003158807569081c0780c00546086a01101c1c5507040c0c0d10f00003585020070201c0c010843c52 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 111885503 1250 111884253 111884257
    0x603070f23060a090909020d05010f0209010e030d020309190513090b07020c0306010512030705030301060203031906060c08030a0914010e010b03010905070902030405030421110906150d1103040602 86
    0x4200d40c04401084440142481840c0c442c0c0079240d80044d0703407008200040c43d001d51180303000c04c0c40106880b441a0081d1140c500791194011507540041e40098103640a40c0c10220366101c051055000d042c40500940c3e001e5182c1c000c06035194040c0000621078071105a2200101e4040d160041500b50200307001d8889400405c01e03d0f5003101c40c4000c4d400420360440c0006851100008000d0061140d03a0900041c00301020b5452180c1d42d039444140061400140140050b40c081c0c0110380c025900e0b86044050304c0041c4850342d00039480c641c0b402c902403180c01d51081e2440102500200090380d05e45407100f940340180200b200203062070a000305070008081064202641c005035000080c0701e030110010402d822030300c80210060032588820bc0c10085c45035260040c603802805030003601e0402d42c2c1c0711140c1c56101c2e009000c0103e4403003806011420006054603641e103c84003650409001d2408901281c02501c0030b00070302d01841c401080b07a600c10403c58120b4407540d4104800f081d140c0c101403074191f01035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 111886753 1250 111885503 111885539
    0x60c05030106030b040905060a1a090f060102070b0f190c020409050618070b18191701060603020903031c0b100801030c060c120f02010b060c10050106050901090605030603070f 77
    0x11341030041050040c641401410300c1c10303030040b001d06090384440381c04e04010f00000829940c0d075a8030f0140400c00c0d680390302c1c00d6441400401254021850500d000a0421a40340c114401c1c1413801c0c000516045c0b102c0003503810048040c0724450028a1002c03050300d5554001000035402350500e4203110411034042507003130090422507040307100015000e44003502ca0185000300c0085607000d10110420300d000e405120b050080c0601444000300d1116000180300309581c01c400d45942485415031002c00c0b00344070f0300005101501e0210704014501000944905c200004084070041d4800b80e0100491982d0000050342070082251340e0740c40e084800641030b40002d02c416100d841c030003000054443d001d03120070000f640d4801038003202c812441c80103507030030400800513004541d81e411042100b0340b2000b008016030500c5d0740c01424021000a024000da64050b0000003c21200b400807100071b076000f03502c041c142c4549080c003e1700c079554900444e00c1c1c800c607a8401150160408000960034180d032800c4002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 111888003 1250 111886753 111886757
    0xc0d0c021b0102010c02030d1806020a080103050610030201081501090f081e0703050c150702040501122307121a0a0204050114070305030114011112030915010b040311010903060c05030106 82
    0x51901d00016801c848201710108007680040020310001411a4024140c0841c102e000400c40b08894a070401281c00107051036000c101d00d1001401803240c04c10409510210140d030848036542503900081c5000c3d00901440072141c028207000d80168011440d45015003411002202d41c5551486070503078800c001c0b403c3c0340003001300c52808001c01001103003240646e90040000c1a10f0f207841d070144840301c032000801607040c50050000b10300623038850260600074012401042e0313854032541081e2980038590351300d00b42c002c4501c0c04504070443c2c2c04110401160820314100b162402030707043c001001241c0c0c0001000308104681040f91a054030743c0500143c0e2000ea079001003030710b4014403058a072322908070040c02051042c0010041c620188020140a080600d800141c0300c1e4a05505032808013403c1900d490503502208100e40c48804010010103d681942c5004040d4904051b60001d44581c2c0000b8100e0071789000303000300d01d900542d529801558011810800300100410052454000f80281c0740 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 111889253 1250 111888003 111888043
    0x7060e1605030f030f1e030a0f0f051302010f020c09011514040b0904091e0b0402030d020316020d050f0708010618062102031002070b0609010605030c03010e0c0d0c02 73
    0x1e071604001500c1d482080b4204001c5180650854400c10207070000d1b1111004488100344e1019030910220295000300c04541d804200b0030400076028060300d80c0c42800400051508080000c8400040151001641c0a01f01a600390400c0d40041f814011076100740703900107400d47c00001e03000f0000080c10001d03004581d05c3c2000100035816080d61407140f846913150940043c0080917aa140560010190358865040c0e0603c80308680c140903114081e11a0643e5442c1440c81000b05500703051200c0c1c5840c184900c080c0d0301d000096081c01c2101003034608040d01802c40c4081c820104081000304680d184d406a0031681c1d1030740c0e0b8414042c040c010364000e50500c1c4201c074810414001c554012001030710803400600c1500c4641c644810302d280d58800050340e040c89500d42d00070301c0c0070452008016042c0150029200c031b141900c1446101d08040c0c0c0b242c010083c042003040740701120007080d2410340c2d884860000f541c1c0c66181c42000d29003e011552040d003440c14681c0c020482e00020102202d02c03420504030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 111890503 1250 111889253 111889259
    0x82d0f10030b0c03130b070f03060807060f0c05030c070312030f0504081207090e100509090a02150a03060503030f0403050c0307050a06030e0a140a0231020304060207060e16 76
    0x200e50a030261100501d140400c90200c0c01e2070b00600c0140d41d02244559029903030014544a02e0a00b450a45100c40814000d00404100303d80c180a004054145580204012440d103078005125030b50078007150007084003000c050003c12509000300c0d83c41c84c511004403882c203500ca06143d200b049900101c1404213140041c1c075040342c1c00ea4040c0e0f610458100350b8817401c200400031990107001009140c2e00c108007844a020070002190010203001709048200b01d007415042400344038000c100501001c1c030720340c044100d840040c0c0d40d1081129441c0c219050064031703091155815005003c0c1d503080654503000101e40e000c4448015000340045902400c12200d074021000e05054944007031740159030700300d00b22507000c3c08064026040741001a000e00c1c11554506a16100d00d445103011409140355908024511020351030310002e120303512101d03005498040c07c1c00d040c0011082055514006440c0d030080b0015050141560688020641100c400d00140c4900d01c0000d0b2102d01c1040440790303000c0400c5001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 111891753 1250 111890503 111890521
    0xf0a030f080a0905030901030c0c05010905030a18050907030905071a090a06031407030209030a0503030f07021612020d060603060518061b030f040203031c020a0305150d0201082d0f 79
    0xb940004e41040c061803404a541380114084c0042e140c0e07110511140800b10b03000035000748100c8501c0750142c1c0156865542480008001da0001d990190f0420441c19090181d0f59880484640040a60034009040200c61a109082006a030b00500e800c3c215800c1c80d0117009400e0000f003082c000c00f140c03866503160700d17044203604a8404c3c4040a800d9100100041e0105020364018000d458009080722801e100b20f58641e031540e4012541c00d5100384104080c8000c894040090405540704034038440e03070340c0d41041c415a510000468000c0d1140840c4407446003400a5035103c03001554120070244179518060001e0403001c100c614a0700d0341c92251100003000c0000500850600c400c0c2c00d000349156407140440e290f280a0085d009030780c1408200072440203100381c015101d2140d08607040143e11280300210180c2200d500a24840120050300c0804580b50b480031100a00d050f030908081000d9196081c00c440c1e10030600b40810a4100d25080f403400c04034030381c0006403003528001d01e6150317030b59208007403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 111893003 1250 111891753 111891761
    0x207030e1507030c110604030501140a0608061b0f03150901060206130b1510091401020a0807140c040c0903020306011e030308040807020a06080103021201050c0a110f0a030f080a 78
    0x7000211410900c14000024441c203e0301d5080c1d80a60030042280703034804001945a40302d035008403100d0b0b6452405501d90404014840c0d404000040204081450802c2c41926034400074801400745d1a4564205d498540034030607211001c244d00c095584a142040382029414103408030030384a40c0f00040001112440001d0780346c428030039894480c840250590340e1003104a0054440302c4a542c08002004481d11803011008003802e0070303035990150600e412661074030f2800c10700c0c0c0e450441d00000c0c10a40030810034000c55107031340d510644c2c01d0540380202c0c0b802d074200112440311a038024184400c841010b5444200710003038900840540c0e5030ba90780c5040c1e600039402c600c0c1c0240d601502d000c1080005c00e0098903c00d070b105003d0b5400354580704d0300b81e0000743d020010750004400300d100d0400600550070980c940c02081040d0000030000c0b410050074080d400c0c043c400380c800402451801c0404500005d1008010f00c0003071004072081d003c0f6170324024180c808940d01e00800204400e000403030311121402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 111894253 1250 111893003 111893029
    0x305030a052412100207030c02090109020906070b06010e12070602010c020303160f0507140303040c09020a120b0a030510020315030a0b130218101505040501080f1017010207030e 78
    0x400b00c4122030007040c070144080b40d05003420107015840380c0d0514900070f0300080420324402c2d074881e44803611510410074070308410303007040e0544e500c1481074421030b48500e000c980350350360803100e240180c0d42c03a100104d4104161006254200c20160481805132074001007a10554120390000e1020b022223010403070f45c070302007202c0f1000c101d60120f0311420b03000d000d141e0400c4607056038030300b840c6404503607282c80340803400d141c021950661000081101b13018005207214058031036800250300e0100b0000d0010480c3d22501140c501090f640c0040c0c0d0016501c20300c840004550042c2030314600c4421b44c1030b00000350000c442e1003000b114284602e900c07501d0301180d0480c6107644400340e0368454540d10b20700b54103103504c4401242c0003036100c0c0c0c000c501c0e2881040524400c80c050306040300c00e2414080c1259001c4901120340d42402420320051066a0f00f142c140342d4461082c1d00492215a40c00c5403070078100e0426881a0040c408810b80b1034807540f81900205440c80c0640c032201d4806406a040c001d064114034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 111895503 1250 111894253 111894301
    0xd03181d010306020c0c0d0f1a010e0604151203080103050c06070b18070f0e040302010c05040b09040f020d0e0d0801050a15051e0d020403150c0203070b04080c0a0305030a05 76
    0x8001400050030070750151a04010203011a030700303405030402040804a01c041c050b60032410000c01e1100700142e00c1c0c00d01149c2050b0740c800e142103524000c12980071107009400503208544644e080d00c4101407110344000140103603582a0f04402d10b41c20701501c02d02c0280070584040c0100c0189080c9402d084045a4001e90f11014450707842e0384805c0b002600000701000d50116000d032480001d030784041003881401808002c0075403280c0d400c0c18a0041d0841c0d80c00c412060511209010805c8210014401e80d00d17541c0060b1804a001082d802c041c8009115880e12004003a00e0a01401c0306020300003007401010000d9114601c05903290000c11185441c644250002244e030084010b07040f83c401d4000d03000384100c40403041c90000d441200040c2e01c0d084244006804d03940810208140300544850601c20364010741c0c1000240e0110300001d489100da02c8018250004a90205081081c90012690045580010307900e134480319240040042d8015184080800e061201041146000705854218000c0e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 111896753 1250 111895503 111895559
    0x417061e04060b030607050c0609160501120603020901090204030311010e061519380405100908030403030c06142a2203050d02031206011b020d0318 65
    0x140c1010110200040c4102d503895103410103821681c808124107805608661181754480000100961609200a0485802c0d6000408005c0310741900000c03607082d12070078600042c4131504481d0301406000d01e58070094019403034400004132010564060420340384660340b03400d0f081044c168039030309803241e5a600d84034940000000c00d40b1503c51305c41300059481d01800340554544440784404092a1326402030802d0b00185001101d80c0100c080c04903a04141015140045880b808204d09207000b50f00500c3d0280c401c0052904001e8043d03020000140700f084200c907962501c030301d4000d00e006142442101c00905000c1c0c0812001c2c944100b0501c40d02003040001000b003980d80752500c01c0008000c0c3c0000f40001003144c454090806082050298601d8071104030b010b2662038524a0110030f101980300319082807103560020b60a1019a40e002502460b0420074000c000034110300d141c05100b4004c9d0b105607041d100380c0403d500034145040408840041e5035840b59200101c4d5200d503049260302184d120b103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 111898003 1250 111896753 111896791
    0x1e190302091f0e15030f0c0108071701030b06010207030c03050102070501150302030c3f0c0301050403080c0c1005012c1315090c0b040923040204090f0611041706 71
    0x380d0400710758008603d6404c24510314041d800309040884142003107a00e40c00460b4081400d5030000385894000e56280b80ca2107032401080311628060406001c01000d22452201007101603208100c16005941c00400702c0d811940e891912034000c1d849007108039007550030181c105810008a0604008594010340a0030359000c001c4208040c40450321503114985100390f1040301030368580c2d0703030f50a10b68120010b05d0709405810418030785040e50342c484440c480d070b04110802000aa11a09813900001d007120410b0f250660119501d04001c0303140c44c86a412403400000040c440d0081c44100b0250030300d00300207540c444c420b244040004600315048910200521080c80026400840c001c0d5241c0071490000340c6042c040c2d4541144610a80c0110b50351140464144403c0142e40b0504454103a0301c0c00c0508043c0310703802d110105400040c0f029204543c0e8105c82c1c0103004c0c0c0303c03000c11707580c40d408942080072031102208481c40c0e4003d400f66200c080d41020368100340120008000d80101554881d02c041c0b800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 111899253 1250 111898003 111898019
    0x5130308090301140901020703140322030912030509090a0903080c090d050a121b02090f370b040902060d0203090a0602120f0a090c051e190302091f 65
    0x210a010858240d91383d6009015a0b540b28100e044c06400d03200c00150f40c451807810010030701c16003c80e14540450f020410b12649011090800003082d420100c00280000c99046c1580c0031030345980f081c40740e480d5208210041681c0240240b00c1d0520413282100241ca400c2808802c0302d01c8400c004011541090100701d00b0407646000d002002002000365a01442a54406041409035081151002c0f61400c050b140d41d6004100c00c1c01001d100d0341068850643c68000914a400142842d20a0008200481c1800651100780e00078910580c80040700c20004040c0e00d1883c00f011192842100e207000181c55041c9040c3c003e10402517001002542004400c2482c2030081d800501003030b03860f00c995902d040005545001a10070750300c50390300140661078003800807042c003007000f0941012540b520804100050b82e0b80d007840c0540e1320545000340ba4080c8070f003101101035036090b1690343c0000c030031803144a000111017041c0280ca100703542c204a1515104d43c0204c45140d0f1f50040c882d000280003050100344 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 111900503 1250 111899253 111899257
    0x50f090604030e0a0f0801020a030c0c1e08091009030215040806160c0b070c060b0a180b2d03010f110415020106181401171e120a0c110105130308 64
    0x1002c0201030f601d519030358400390081c09175194051411650086030261505800d8850800000190304001c1d5524001c1da841c50180000a01134000c10300c84400c04405002c030400540755041030150105160000c441c4026146248030300c0100d10480d407202c0c0c040f050540d49400e0720105c50700c6400404403521003403c0914429180300c4c0c540304124954803804040307034040400c04d002e00305580700d00e50328007000d0800c8020350b250032a01078080c01c00210b0402032940300041541880c0c0b18640005040c01d80310340003800450003101440303c4a145201d202c082807035407280c141c80300c0e1011402009003001c032100402c160303004a04003c1011500340004c101c3c031040c000d030190314880d0358400000d12540b90140044a684420300036400d6a0382c0342c50400e00781d074840128a02401c6802c1a2460601106003826078961800100402c180c0b401d035110100150108400074400760707017801c0c640c6c441844520040402e08401402e80f801071040c010b100155005000b02d0300c02110f4452043c2c1d0301401c546540301c903a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 111901753 1250 111900503 111900527
    0xc020f0d08030414060a1506050304020103150611060a05040b040210020f030d05090d080f06040207060b060c16120507051e0411130608060f09040c1d0109050f09060403 74
    0x10028085a400004071610001e603c91407040301c41101c14503080107440e1510800600d610001d034035100d1841424600b5410030001c030b81c1289002c43d80e076900d0b03100480141000d400301d840214403401700400c0040d005040006d421141e042161900c0e40c0b4544084143c55003518040c0482a800011802604040c9000c019000440c012503103103840c8403410030301e50303401003140e0360365503a50302e0034400f03202c4081c40042030240c01c1d440c1c420081d0410b00114485180e0282031148941c1d8002003507010848142c0154840c8400100720f10b894074075103125252586150001030701000d07000c050215556035912941000785401c130000380b1400741000144000810110b11381500c070040b41118980a0780c4501607004882c07141c03c1807903150b0003010780e80c07030b0649000d800031014402a071080005940340c0d030020071041c5908a4101a1544607405c0507a580f000a4112000c208500c0003015071211246500c28103c40c1030810070000e43d82c900704c1641c10008161000f03011a0030040206000c244039043c41101c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 111903003 1250 111901753 111901759
    0x40f050c0d02030603120406020d0f020a150216050109060b0103052a0f0408160e070f0507060b0607050604080301050f0603010b091e1306030501050702030f07080a03110706020304051c0c020f 84
    0x1203040c51500c160391b1a041980300ca40142e10400d100110740d5444503003401400c0c0c00b8001001c100c000366964841c0b03200031110080e00194003103142d140b5100350400402c1e6494101000b08451500e030700b420b80c054040294054042410840401e6100e60803400041c0004004620dd4036107000c120b42440a503800700b960324002181c14000410703840000e111400d000d010399200350820b00d141c0711080c440c0900041c026020301c0000d41c41d451429400c00126061309600030300000c0c2d10b0f000300b000600d0074000d21101030000c2c4070304400c00080008110080d81643d004490543c1000c884400b0091188424010401c1e10079080c4400c94407400c281c00380b0000c2a5041000300800d20001c00801e00680d014038401d00c5982d12041c081007841400c0c070a0907000074852018600d400d08000310151a4418020001c02c408000075210844178401d0f800141c1c4245100340c01a03650703029082000180d0001d480540352400b4040070000e4002004010b0410175080d81c4940703c003c00075808200c02c850074001c0c0b46030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 111904253 1250 111903003 111903013
    0x303021b0a0902040b0304030f0207080c01110304090c080a06050607080405010813050d0c030305090a0c06050c010e07030f03020105060f01080c0703050403021009150809070b090d060c0e040f050c0d02030603 91
    0x5802d02990014102901803011226120b2415003401840d01c3d940c40d882e841035410000e002e10a201000c500b1303105041081c01c0258050118840907451031184d6804818507503c1c041101102d070b9400b0482c0f50290701809414000c168541003081348921803010001c00c00380c0f082004000030350003401d01c60750007424001422842401a11480d042330f00302c43c0c2000004038200403100816801d44a103a0300140181e0003808400341c195682c0d440c50303d10303001c0d43c0140b14001c5014000424250001400500c258068808050b502e1802504100140400f01d01550030800020b101c2e06080c50341229005051350740c1012504c8178102c2e2812540030340c000f90100071007008040050b0315024410348000c50f80b079881d4a0741030f00c0d00c0c0210103140d108611803c204800301040c03009070000046c1c94819100309442c0c03180d80c0c810000020381c801c1d05003440140040d00b48220000441c2c0c0110b42e40184400654090011483c842e140c00200d034030841e0014402038080c4094854080a5406035900a0014003102c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 111905503 1250 111904253 111904259
    0x90e150603031e0a110105010e0403050304021f0c0c2108090604050618040509190b18060406050708060f280b0705030901140f090415170f0609070303021b0a 69
    0x164504000a5140c20f1090700000c00502080d8091902c0c901c85d00f044c0020485941889407003042c0040242019042220100c0484d0640d942c035102a01c0c110240184038101003905440645040c21241d0b00b961100782c01c210000b8071035a01c8001c0040083c1c1c0d0031021030401c402d50380e1248603400080203550044010b204c08900e94076884001e0400110320741c40340c4a4401c2040c104026030310024181045a048a0111180015041c1880d8044d95000e4090f944947c3e510305c10408101000343c01c200f035031045105210501845603c054018412990b440303d65907601002c1c0710540d040c03503120035045440c100403100c078030801d50380800c01102d100c402c0e86241550341c02d4038445500490025100d58000280009803583c12100e003901d00340b2840c00c0a402e20451005504080c02010455802542c84001c00c41105030416202400b074080b5035007001e071300c640c01c10803a99103414440946002d8403610000c100e0201000402c40c00300e03a8107a00130705050204044207042d4035070664610b50440c09058005c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 111906753 1250 111905503 111905527
    0x5010f060b0d0c051303141005070c060c0801050d060218060a0f1d090a090203070522060b070f03050f1905250c0611120c01050709090e15060303 64
    0x46009007250440e26840304009032401d0110780f8405840b000344001008040389141c0207406400407a504246070400360240c80c042c090400100c00180c098041c509010440d895800c20724a171291405041c0411a180f580c40301603940301c2080c020340da4010748070000b14002905c02d070001c212040b1507110754100c116268020640f00c2d0483c0d01c401c00456030f012820301ea010350103c0c412210300b041c07105026500703580b68089804940c02810a00820b521104007109540341001024010310b03018126030700e1076400700c8403803824403040d04180907090304000000404c2c1440b1410360f000e507a0401070000803420613640c1566198000c03402000340180900800c0281c0320442c1c664039014090703489295980000c403084511542e841c0280d50416100c070404900401d4041e06c01e04180ca22504000303c668810b903d407035251064900f00c3c407200400000e90441d8806064100d02c7c00352016494000680b901e0340c04a0341607a2064038645029804103d42103200c440c165002600a40f01070152840d0420030100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 111908003 1250 111906753 111906761
    0xf0c0c040c02060f0906070f4a010e03060a0c02070e010905070806061303240203040f0204060b032211032407090501090e040c0b130302150a0806090405010f 69
    0x403140141e00043e0400c81c5000035810050707400408200503010601d440c00740a400500e400b40110100000e00d08052042e90603051000200d00c0811400181d0f0b0701c4d00d032030110054688d06240b209000c260083c0840a5000341441e514942004002e810070f07a54420b19040208200104041140328003100021501c0900010074040c121a840210359031501c4007000d0094500900303035901410080040024400c2181c5500c420303203500000346d03c1c4c0c042110003040008540e141881c0891072001083c8000c01020300c2d0040c2c082072003036405020781981c619041001303002c200d40a2036030044088000d13080183c043c4a41c40305030311030f4010340360340c64010020038586040c3c03014000090384d0800403600c0b20480301e51000d51200e4185040c0c0c800604000000700301580c9407103032600510b4018007080400251658250251880c00c0f2550340b102c60b040345c0c031190a025844142e00441c0c8070b0021001000d1202c4c1110703010005a00c6842140c0ca5050900075464001801501c82c0e55a0b018001d11ba90700381c1c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 111909253 1250 111908003 111908021
    0xb0415050603010b0d1b03020a1d010f14130605090319020a0306050403020102160b0a1a0310050a02040503030703020d08100b0301030201050306040b03011a0906042a0504030804060f0e030604080f0c0c04 89
    0x7d030050721440c032204041d10789084e410280c001805804091a103d81c1d02c12803d2840011320300e013910303207442030344407445050141680c408070f0030921000200e01c140d40440503242c400000c0303085503607041c00d03c541a482d07030003120b0020303400c003c060b80180b02180c40b5802c00c076001031107880010710301282c0291810712841d13843c0003114040130400c180a990801030050518071001441c245d000846010002170352041c080894404e055100c00009035113401c542c0c140d8000342400350540b80c3c1c0f10800d141c025150001c102c41800070461043c082041c400d4907900713180035103094044042c55a401d580040d00e241e0001000c0e1070b409501c800c181c2e005a107080c0521200d14044e0112843c0040308081002060100284520700651800c2da84040e0b00e4001640411000e06a03000100020320300e11003100d16101e0307500013800d4108000b50000340542d001500c1d031400e220036a0b560140743c0f541d038205500c0e02400da501508264042c00001801034558000340121406c1c14125401d110400c0041002c1d151900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 111910503 1250 111909253 111909257
    0x309120605010503010c020105090d110a02060304080403030206130203070924090506030106050904020307120f0506070e01030f0c1205070c02040e0a05010b100f1b05100b0415050603010b0d1b 84
    0x3078010883c0d4242405040003c0e007242c0000d202a00c2d110001c82d0b40c8102d84411203041007840c809a00002e6820301941401580280c0540e0b9246403c1c101680f180e0702a00c4124014401c01000607120442c1f10b481c4c002c11603004002c1c00d0201d00d009000d2028007203490080c041480e00307003c2540c0c1c0c034402d05681d800030100004081424038200c010142181c2c842d41c0554004d010010820006a90120780382c400d0340d1850b00010450b0820303042c400d03010400a88000c0440c4940c4051210b900c1d08080d00d200ca03140260303401d002c081c0c0c0d05200002511640c103428400305a24140110071000380d5000a03901404900d01943e854019030001000c0e9105000d0000c1c00b60842021301d02445000e01407036901c4a41500e8000b41800400001406081100e0201c000c008690326103241c2c80c9584024441010f4100c01140c0b044424100302c840202000c041d50ba128500d0400760281d120042d40c0c0c4001180c500400c500d0450b071804280000681c8110510001659507100f62205500e049409070848403031a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 111911753 1250 111910503 111910511
    0x20109020f04060513020a050708070834030e01030b030703060b0a0906051309030e060328150e060409080c0313050307121e05011d16061b03091206 65
    0x500612580c2802600701a02036030410b40140b0594545401c140706150380c041e0300580e035080702d0b10211154007621034020130141c400501d14040c4030064016201c5810b60f10b42ca801e40d481003a00f095404c1640c01c9400001c28801d10f030380d40200380a20301c2074035660b40c18180428070000d2880028200415501304a68450341d660101501d42040c0303115201601c0c40f01002c0000e03508007000107039040303401c001c1441401e0f2910f4400081600c5204941d0b8000405405075403241440301d20000e4ac0c46c038503404622402c00100000750f00024074041c2d0a0345905c4082400310760b906180300c080703409800910079a000360710f80306503000048141004200a802d501c014586841404c00c00756600c1d50541c0c0716510030382c17020b0310a0000c0684440c10581c681c1d840108852050045600310b5096003241d0b1b4060282e518000c0010740000100081c050740d4103040080e103140c40110120601c0307800c0e0350300a140008655803c0c803a2050003000461502c0c41c00f900f003030b007042c9945200300c5880c190407080446090f925 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 111913003 1250 111911753 111911771
    0x6041503140106240e0d0f0605040c03020111010c05030106030c0203040e010306060608011205071809050d020303010810050906040b1015030617030c06370b1f0c06050a0209100201 79
    0x3a00c19410104010328150b050b00800813004000c44060030800b40b02d440001e24901c04c01180426020b1559800b0f60140007500e814107144500a81d684002d0b80800d8404070142416030045c0302c0c00843c108503840d101c1c10b590a01d141100140f182040203400c1d813008200100f1201482d40c4458001d511401001c00c50341e04020f40101101c03410383c08030b40602c8880142d800000d00100303070f84098030182d8521640f0b0307500045851026007500700b0301510b07600416a4034030309660b02000a6040c1d541c11400c0b9041c1b41500c1c2511f01c01c403081120224819003010020500048000e101741d0b8012142c5243c5a01140d00d81601c541d12a0009203d080401e9855a04000074840e032080c1450b5541c00300b0196041c22000b404498a46d10014520b203c0441d100d00c2141241d0641a1400180c0009407441405207901a1200009051030701059101d00784c059a41a6900c0380444203000866840e42d64a040f814030b55284409000702a088017202d64080c40688580d444400a030030200d80198000700b05a04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 111914253 1250 111913003 111913019
    0xc0102070b030c0a0e0f060c0a0210051c0b04091b03230c0904020a170318030d121a0907050702011103032404090c060504170303040b06041503140106 66
    0x400d80d07100c1080c0391030600401c04010000401da864500d01c41c1046001110044c0c0040c4450300201460781d400300b004164003000500000e12007003018429035141684034030000c0c0c151007a015020411003a202440502450b508880d000302c0c0d45e0b4140600045003809a40e500e100584886030514488841100760800c2400621881c00d094041d150314181e520b550340c038901644885c08503c10030701505504011404540300c40e01c030400141044c60030900350705103d04043d51203900403940141404140f4481c480c0305d15010502d4210014140c9601c02e2400142080901030700b4200c007c01e1400300851071021007615000403d911404055070b510359500568400034101d42c1c80d04020f03034419801802080f040b4498841210800e16003946241c0307032120550006005401c94401c003d040c8004010000341c0207400101400035038800f00502d08005070074021095480c00202c1e40a02303880e5480e0089441802c1c56848100489040b0303030900041504c0b03440341c5194402800592080341c0d074540c010400d000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 111915503 1250 111914253 111914263
    0x315050114010c29010b131a090d060f020a17070305090d1233080d05030a1a28060e131d0a060c03060902030f010b09150c0c0102 57
    0x31400540541e060310072000020f242010415000f8011111003111485482d030102070441100c0441103583d03015a1544640032054005400440e9200c0e1840400301d8171444003240400000e80503c030090600d002502081405145441c055400580c0d032610015402c1141c001020300b03103501d48800ca8441002950782e45c510340010b041600705480e24051003110b0801040b4080e61100d589450040b450130f00a6090003041d407440002e05548042e030706019100480e58201c8080204048594580c2d40e0b2031081a4807000c401d00d140001420070400181c903c840ca51141c407018031058a0304001c844a00c000c5074815030035002c0038441822804495000400c1c0900300300c054000d034030f0402c034800112004501c04414a44014401c40d48911111500420481e10b02e0715203550700c4121100181141000c000401d220090240082c4c00e1400100c0ca040740e600850380154000c0c403000649030b00c2e069101285820100c6415881007000c4a11000221340702e000d0251031046402605c00c3c10700080c000b920300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 111916753 1250 111915503 111915509
    0x121815041a0f0109050717100302010f090b03010e1009050f1f14040e15010b030f0123010c06020c01021b060601030b0d03030203091509010e0105090c0f011d090103150501 75
    0x341101030802a62800c9440b4181c1142e4044501050548400000b650480d0325070700c150241c00c1c00075082059a901c00e8440310100c9000ba25403448083c0d03c00030840f02c280c001c0c011202142010801004600d544441c100e900900701c0040120843e141c1c1507040c1031320001e561104d0030303640d100140040ba1041309200c3e21045058030721404441e00c4c0900402c00c20303201c040c0d01881030b42d40303e0000ca450700c800d10a84006801c1d10301c000c1120f603150f815800c1c0e00d80084e01c10746040c041c1e0800214107200740701120130010390015824010440c50b10011681a507041500319683c1c0e03002d01a02049000034005041a2440780d40b04110320481609035a1401d1001402181054106030274424a6100c11004141107505450056a01c1d40c90151441c60552002003603801c13001014104621880706502c0550304880c650001d11054403000d90999860415150741d0354003450310b000d175001c1507005061141c10703004840641481504110006004540e09078400c2d140c41201591b084d0b801150380c4503403809 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 111918003 1250 111916753 111916793
    0x120601030e251e090e060609040b04030c140a030e0f0906090a150603021c0c0e040207140303040602090102190312021803010c030b040b0d020612181504 67
    0x794809003940d40e603807029042d81054003080c182c1c031109980c84030850a00640b11100c8036022200503070252090441e0f461050000700d52401d0a0442c2c4c00d04040f803a02d014420081c030240858940380c03203503c00d418000e0003c4080c0031540482c0000141d8103049140742064502c00b82270421100e0401030300200044c030241c5d1080c8603081c16900980d940c459540d400003000c1e18a00280c0d510a0b141c8070040c103030181c5c0010170007901080060740582c9034004041f800d49a248440481ca1260303000c500f521501e20110002c900507001d0004141040d9014140580c014005038801a00301d19031b80382150f1080c0c509464150300010143c4c06540c040003261550310324501440080000703034030010040c0f5046c076030f6221758540020342c100042c0d02000c0100011540180200710003004198040c0c0101a04554a1b0289041c88500c0842c1d1078a55003034880c0740c0e000f90419260203000c8110f02c01d110310003007600415124060102d078030440200241d4810041c102028815401e1a080c49001140c00d0000120303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 111919253 1250 111918003 111918011
    0x709052107120515040501091709180705070f050a050f0f0c060f09040212010e150d060b0d08040e040c0b07031d03070b0c0a0b010e0603060103030f050405100512060103 74
    0x44100d0018080c02210b00d41181c2c000155503528200d0f003401124410701d05072100c00b4040c0701c1400b5040d80304070200e030b03c2020308400d450b80304405801c0343e005221056174403287d40400d41c1c0d10441d4014429900c80003600d00303a85008a190b5502d160304411080984881d4888180381040040030807040300711812550042400e07081c1203c00c190350b410030707281450041002141c8070703084403085001e40d0b144d104010070964964100860080c42c182c024803074414981004004202c1790381c8081c01072510364401800e0480c0c0c0440356125040034122181078690006140051100447ca4910103040174028510741d144483c140350515401e600342540040e005044104103000c00250800d80340006007144100c00d8a00e0720007540000d0038070050703600c05280400e00017030500740c1d4000450118003092080340c82c401c140c1d8031541a01c50103c008c540d42c81d09903001c0e0005102190103413001c00314110140c90900d1030700303482d2408503005070b04800e140f1001c41e1000c10406041ca10100b182c0e40d0000003803070208 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 111920503 1250 111919253 111919309
    0x60301090b070c0c0b0f030613051302010e0d0b01030503030f0717040f06150b2511150403150501170a05070915120b010f0e0c0d0c1106070905 63
    0x5003003044050411000d1203c440e20220411200322411002000c4400c1225160340126440b40c40c0d950040310404d01c18003c00b6044c651042c03007407244078000c070702450040c2d2034410035070b0040d55002e00e600101a441030042d0842c1000582c042c42540c040c612a102440d1030b41000121070300040c1c006801070080c028042042154440d40304a00ca074080c0c1c0007161032440c2e0401e402e1050040c240240d011550041280000c9403502c4100c0c002e11152102109481094900c4404400480004480141030b504010003046192034241c0c0b003003021a902c4070728140381594a5441030140d000401440d24140d80701d80c01088000240c0f803c80307080c0c103800700140c070704d00250b40e54881d1218a140140c0003c07554a99440e0080468688010064540044100041d10103401c0201800000348552800c000e07200d04042005428040c18600401c06d0300e540300e08100c0c0380c41d03a25001e071a050540c10200a402c10008621081c1000074501038034090301c0e0194010b0814007407045200802c0070280420350070780e241e2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 111921753 1250 111920503 111920513
    0x130c0b0a080708041a15120102041809030203040806010617060301140f070207050d060504050d0c030c0f1e060b0a08012a0e030604080a09050d02010e04110903030d02090906030109 79
    0x185500819518243c031080d65540380600d0151220700300407000103003120400107020280240740100e107104a45406042c82d4259a060a074481e500503040070144580320074a103a0815040180c409120340152400c054403207504514007203090b40182d00292244c0e5984042a40944880707030002c0c4140c0080c403012402c512041b160010203800101c80000e0310002070300781031003484428060880201511100201410300c0005400d0030754060358180a40c20f8001c000034091030314001e08660640794001e4140c074076100c070b201e400700c085010350300300300c82c46482d264000e0b440c0c04503910740e4854800080c9003041c40c000e008001e042900188241d0f80b40c400780c800c403410361040c1c8440d50b0314514201a450382c010241124898049401c0d83d805203d0b4006220800007207601509403204a961040c82a40e600c00400c4500070404001030b021494484520040f030410350401e650b80d5028440c080c0ca001d0a080c0442d1a41e4400068500941d42c0130070310741d00600d4207014058100d04101c000344002c24090b02d074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 111923003 1250 111921753 111921767
    0x15250509090609060406090e0c0406080601050306014209050f0121060509161815050a0c02030d0906020705041a0d1104061203120e0d0f030b030303130c0b0a 69
    0x8a07034800c0403c100042d1059407950040b10240054000600a0340e0311080059619280444903030312441c2040008115100c00203285412070368004c00030205a440e1007850010001e070740005406101240e02d20004010020f01c59800c003540c5030b10250300140c00706030020002100303500414031030051100150041da074481d40e05c40e01d9140ca480c1041124074194000302c018103495100e190000c0c1d0a600700a0508101c020090b0303020507036140c03508111150300d401c0042180c00d000720300c100d2281032880c102030ba1040700641584e60309400c049014000c0c1c2e800080c50041d07201c144c9000183e5080d0f040c04050f1b41440024010141502d042c0000005030680c0d011140d10403441c14080c0d90b55544800274804111a403800c0c0e0800a0f02c1040340c2c5840b02c4142c41c440840c0d81c8c041c1c001c6020006040c0401070b4500c2039011454020010f0304482801c49400c075040c0b542c4214036070400d521503107005400ea03828801180200652108050460114541a88506200da01c2644440014400c001c2840d0708118 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 111924253 1250 111923003 111923011
    0x90608100503100f0b0406091e02070807080c0a170d0c08010f0b1c0603050d110f07091112010f08120406050f09061b0109050f071a03091525050909 65
    0x140400d40c540391380c541400034180c03251902c0e440350911000081d203a441e64040041e100b0842e2401d80c480b003e44508400380d10a41c0c0c4c1c020501d00c1d08000c1e480203d4024400f40545d048040e0960303d060544dd290b540000d81507461500080c0800514100c03c2204e41c401c030307102c00740d19040c0131646624000840c0d010740042e03c01c01c0c10a080c0001c1c00041c015110408891a40714148104211922400c026984030140c0520074007268411820012450300080e00380f02414280340100a0b0904140d0001d000d811910182240520244131402401178042c070380901070a02d20001c0101a450045454506100d10403d44202c650820060013240e0384441103e000c0301c1c0d07480c100355884401201003100c41c410039024059910a1441d0f10b54100810342240d030b20300340600c0403504400285080f1949074080340c82400494480107840300d005c5030b030660145502504620541e40245010040141420801c90701100895011300c20781102464080b00c00282c203d243c0303801ca0a10000c003000c80c03010310000d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 111925503 1250 111924253 111924283
    0x60f01080c010e1525030206100e1b0910020a1a270a0f15050c040807030609060e15070906020318010c11130b09060301050903090d0501060f06090608100503 69
    0x1415001c500104103040310f0424030350f40003611700000b90360b02da8030a502d1150310460050183e000400c0202281c2a140400d03108805090a41510b83c00b10741a440250101002114902804001a207699170340034092032400d19000b0704940c1d811850102050614024003000000900c400e008203524184203508a070034050103020100c003403003140c2915180400c08000c01460354007403080c04201e010301c21b0b0841c042e5400c005102035210441101a0382c0114020021154418201000401c80a8001c00102809a4000a0703800c0303c12003c103040c6030508011121420400c000e1110311540000d008008103c0d600c051030400e40d05a420820343e0f10724501d10740c10000d69101100a0116446a1204102c00140365551105900b074011011384200385525120704840400186c05041c11b008140c482e1030440055854888020100104160450000d444a668807200800c00310421007082c0080e10b02d0f82c5410b041245401401004040f0040c07119049820701c8204104030f0302c1c00113081460303507a01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 111926753 1250 111925503 111925519
    0x306060706060f06030e0c01030519020f0409050c090a060822110a0905090106080705150a140307020304051302070302070506030c0c01110403031803030c060f020c0f060f01080c010e 80
    0x606020002c1c012a40001031040342044002400c150564000100440d040c0142c680c0a804e0300019000ca40d1300301c850462420307400e42d84c0140d402a55000b05030a41032000c006040545544004080741c0c0100c40e440d65481000401c441180b0b014444c44005010514040742d4034a03201d01e1000c0c0e6070780c3c503280c024518088a0108410032100342600c011800000c0c103680c0b804d96a4065802c0075103802e4550512551070319001081d10300c0c2c0880c0c2c031429100c0c003410803102841c0c12001080c044e400323015000104105040410b80904050000794011000313a0300450715542000108409000785210b101c1105104004180000360003050604c12100220761554803680c4540032010b40748210501142076510b030105290781c030407810004e407050303e02a43e00c4524401221258001c0100e041c000500070031180c03040180006c480703801102034000840000341c108600701301d5aa1030111202c5110006030402c1d01000040240f0b803205500428480000304000e101040c00030701502c1c20045600e00a01c90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 111928003 1250 111926753 111926767
    0x3040b04050d060f05070905090c0901020a0b060303091e0910051305040203120703021e160b0a0c1a071404060c060228020303040507090c09060e0a081b09100b030606 73
    0xc135030256078804e41d000001c1c04689030079000107001d0034050145603c50741361781001c61050380101d0b040e1105041d06800a04030b070035540e210100c00d81001000c0700d505200c1040700000a0b103503040f030780d4440840540800c14003c030420421078010001042e4000b40600450100090380c0d549088161745040076000003459111400031a0030400f0300c00d10034a0f03030640040c0140070113a0011b00c040c4417217103030b062000b04042640320550300c0d50004501d400c0c0141020000784000340302c0030000d101120890610010030b00300c2d81d660b203d8492014070f05054402c254410052150f8000407552034520707400c10180e180c603003807841c050004201c2d0b5101070b0041c2d80c086807555030810be400001d40030a0443c0081c050344900880300a5587c0e00807141202c190050040001d503a20041c06071600c000c41c603840c2d4010803803c0c1300f011034100180078100c0f5840b88401100040001c401d02140b0324031000340041c0c85c03400a603602800101c0d0780c09010b6401d5101d40074410444003034514290f98000c88201c80c0103a507400c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 111929253 1250 111928003 111928013
    0x30403090f140108060301090201080612150a02190306230f03033004172d09010e03060606030403030908070503030108010902011d01020a02010807020111030a0b0103060803040b04050d 81
    0x36041e04000851140a100414116101c00615120250036038a107440c0f60354803002e05007030311101000203012600c4800454400d01c0c108811a281d00008070880b1805030001b082c01c00c05c50415203400ea110790380043c02440a00d0404040c1107401540c0c10284401480c06c1c0b0540c400300c022140002c3c18007083d2050b4203081d552480b4001802d04010202d0391240200c06400944036071071040311440404144880c00320364000c60b2414810303504005140c1841141140f2134283e40d02640c10030207195841c030081129080c0d03c07a1206010200a240c02d6228103074040050b040c9075054029910030703842041049a2980c1d0311040700d911551510300424001024541701899004050008105000100010074034590540c002c000c2c40e03000f6a1003481c23070800c90a558110314040302550b80183c020b0501100994020240301e40c0000c100d200002e00b9a04a8101901726002600da40250a1700c6801a202c60b69241c0941006000b10300055450a03181900c40c1c13500c1c1c0300d1031141500481c1c94034403206c1845 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 111930503 1250 111929253 111929267
    0x90907030c0309080403082505060f04020f03060a140127020a03060512030306150a0e09071e050706110306030703060b0402070b040609060e0f030a0c0606030c032004021e030403 78
    0x594000e209035140c50b16490010078a81148405240954280c4031081d40048e2103c80e40342001e41182c06018261071b501400c440e41c40004105076080440301c40b200c4103e4404000702846418000000551800c0794131f460300c080841070740440f1510340c0d0815150302000c02d243c0301a00e140400c03080169038001c01501176020300641d6000503030001d00400720304449140480294131408088a1002c02041c0040515006018200103400000e090302e135072a00c02e0a00705101030b00414107040c0300142c2c0e40d6040d8401300c02d5612407500710029502045038010850b0700d01401c0c1240420f69136140c00c500c1d00c0c40c04255548014400507141e15100c81e4500c01c96180ca50450700c149400621220b041d01e4542004800350080d103a044170528a410110060004040b41340b0a0b44502c07007006e1480d20030b200104035100100e90200b0780d2030581c0e402c400800103401c0300a9000071072040e00c04641c0788080e400c07901848241002078500690040044070745103116071224801c02d034240b0301c1040e02d9803141e0030304403048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 111931753 1250 111930503 111930521
    0x60f040204032301061a09190b0403110904030c02090a02071b0815100603090203071701090308070903030504030209071209080c0f0309060f0c1f06051005090907030c03 74
    0x800e00c002008820711010409041c1c81400a24181a052044154030390803626544610f0522094440300c0e03201e0002118018000a040109802480c82c4103000c0002c0024199004c40065a0b00050800800c01c11400c4101e11403230440360191203141c00e0301c01814060780440024881c80d001c90008444003502e034140e50707001d50001444105030701140900f120910060160320080e128078000660f607810001a010301c108104000401d0a86ca001c1e002e80281c204a10304980c9409910700102d1441c81010002d00d02010341c10011a4580b01c40c00c024040f400060010800c1180b200000d10201e50007108072030450743d043d0342580d125501c0303990032030b040407246404c100e886007080302c0c010910542d0310241c401b03030820500b654003080c142031950351382e8482c074680c1c10341000b81405a0010b003001c0401801c1d01038003803c150b50807209ca81c80410b021700b01a103004080c6950790b060600650500641c44500418142413035480c11005600042003108000d00400c00c05445080c20040180b090b0821045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 111933003 1250 111931753 111931759
    0xa0503031303090504230910050901050105090f0405060705071a0907090608031c1104031211070501090315050405070f06090315060b1632010b0301020a0215060f 71
    0x503800c12003a03079503400704101802c0d400a030307002401044600e410300c250368103c8003099941d14007900c40401d2164880d0000e050340464000c20302c480b564400603000311442844202c000086542c101007c0200c4010090106003c07084072104000000743c0004030f00382c00282d982000d42e100e42403840c0600b050040301c0303256580b6060718418001d90090001d00142915090801800031544942e0300507581d00509844403c105030b0844250f49010007988030301800070f10038540e6032030076440c0e4071045880200d1155050000d800d840041da5103110510024000d401d0034a0701e5004149561600c0806810b00400c1b10030b01c55840010a0401408000c90001003480500305002540d90b0a00039103400c00c0c41c4410ba40540a8000188055429104400036101c40d000201e0070a00c0401ca9840c0c1010591400c5445400c0d601c45903d03190b0b48000784c40002c004401d002c10700d0002c00460b5070f081d00c900e0794416009a00500c04260981d130007140100900b0358541c0c0b03600e61980c0740780000d0150b01407070b0f849a170 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 111934253 1250 111933003 111933007
    0x2a1605012c0d061a06161b08030313030207050f0114090a08120705070f061403040510020409020d0c0f080c09030c090403080601140301031a15030106081c030603080a110a0503 77
    0x100300031207904164620065500d242c1c524001403014090b8600c00c0e01d19942e006401041c2003070010f47d1840c40c00e42603421703051918000e5034542041501d1070303005651070868030b0301c00c07084d5204040d03041060001400090710f03940c0c0c070084000000792a1901804d5000840440403c0d030000c2034803003c1c400030007880e20004803103000340507100c1400240d00c00a02502c10f030041c0200400c1007146805075000315440f6659111b4408100a8a0342e0b8540004d08101d5581c0125280c1e80ca000c030180c0054805030200481c0180e541c04064004d038200ca00444600c4240f14032000b0000060741c200147d15400164032403040c1d0b4440c80400000d08080c000c045050344001e06001340420b155100b04d2940c0b240400384c907000d40da100d18001c0c015440c042444010b144410b0251403034801c1c454985096002814072103500325069075840007030709603007036500301071600e030304c86802840d9080f100710065502d1415414108210b0b0300f184c440c0075861103034106540c28070851040903144002c0410031110f1407504070054039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 111935503 1250 111934253 111934279
    0x9060c060a0510080c03190804030c030c05010f08060a1e080109060501090605090f130303110705060406060504020a0e240706060603050c0319112a1605012c 69
    0x40400703541c035102a003040d00c0040b4130365900040f00c0d00070050080041c1040e40c00c842003140c2003031000000f2540c443c0d06100c0000003510000c4084051445040060009802c1500040040313115003900d0381040040003d006080d00c407880480151514041441400b071044000e142c1c00c0303903183d44160040d40c0b8000c1c110701400341946c04541602d25240007800305680d00c108100850405440c3c0c10101da00e0007010400100e842d8902520082c420b08021800b89000c81d11114103800c40541070f5015009481080200001031040c0c4d0081c1004880440c181440000014480c40007000d402e402032005652001e0b0028030043c640c010081071840c55903036450107103407480181115115040102c0d00703100204075005490350075070381300d0104401e2510700d080303140c0481c5010300b905411409001d80100f0180c4c5000c0c40544010342000f00c03404030107150701d00441e075081c030f0402c80650840303d441c0c0da10418070143e0b91001318140c0302143ca0700400501001e4010182ca0402d1030001d95510040c60b4800b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 111936753 1250 111935503 111935521
    0x180f0619021e0c0102060a0e07170a02010e0108011a03040606051c060b090c030a02160b100311060a020a0b09010e010c0c02090604050405030a030e01141810150b09060c06 75
    0xb82c040104921046030010046100280d928049002c11a000d41c00020004550000640c085c1d580b14604004507280559182c2c0c1c0010801901034004030795412402c00c810a40d600310118144000302860000c900d9850702c3c18500b000d103200c80208100c030380000702060074005d81d508944007514004018848079105009030046020485200b12029820071280d8007440c03414044291284046140481c51031380c0b49880742c030080d400926801c0c2c0400100c12f40c0c0c008180303d81040c0303200b40040c034400845e41d8111f080010fa410801682030307104540801811407043d5000ca00c030f261043e80442500342945840c0400c40c09089100f12a8a466280c580c030281d64540c045480304c025030023500c1c3d0560329219941030006441d003c95000e012503104020b1480d5080c803d52180c4014001d070000014020b10401c000b000b4284151980081c4000c180081c160300c40040c40514500c551240c4100500c000340c01c04041b42999510910b00202c8010408205039142c4000700e03616111078400740c650b07503d421524 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 111938003 1250 111936753 111936763
    0xe0a05130302250e1015020309030c060d18030909151508180a061407030b010905010f0507020d1a13030804020d08040e0a0510120c0b0304140304080c01020c06180f061902 75
    0x1030406c03001840580c80c42c03283c004412500c034024090701416990100800780051940016141d40c184da070303030304198440006845210001a84299104d01c2c0c054a81008601511a141c41040300a4602401008101d8030304540c5c9920880030708101c505665111035591142e516001c1071510350040005030001c0003907650200440e5003141888035900d03124440d08038100e0380c00903080b601040070807101348442c2d0f00860781c0c0000d810051034802e190030b0041c0e0125803072078050f810071106015440e441c49543d01c00d51440d10703406a4407115404810600f030710004c0200301e0260019018043d41d082c0d10f81402012002c84010b80804200300c031260071306205100040108072951103403003c1710400820308244a040d0080c2c201d07001126500540e00700202007020307030300181c0300300c410001700f085400b4032403014000b0f4401001c80c04050038610301880006070908280c1e103d090b00c5881d0802c55001c4803082c201c842c445c200000e4410544904540c004188030f44143c502e540780280f01e05142100007a80050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 111939253 1250 111938003 111938009
    0x1602060408100903021b06030703051012050a020907030c0c0b0c0d021803060f090304090506060d0c11011413080904150f140402071214130e0a05130302250e10 70
    0xb084070901006150090f403950448001b081c0d1203001080400c030b1141c8603400c5541c05c900d100f19408101541c41098011034541184129007540004503418194641070714403135070261642c10280003078801810010210350300e01000901508000005c1601c04286405690000c3d426000031959409000000c1c0300d4070b82809100fa02c244a02c00014000d00448500b150291411000550416003001075020151200a1202d9040b19007072050b80010000750241460100b0076442d1a41c07030041255815003901c40c0000e0b0521a41035010038082030449210741c01107055044100d15407a0038400000a024000d03000030b04600b20b400a6020541180185054003150521110008003411000c2884141e010b51200038000510541c90860b010303001d004220b07280e4107905825403406041008040207400580c02c040301403074602d410005074002074491a03800804c0740301c03044036a04e01c40d60300035a11000040191207c51401008484050f0359000c0c00b07000d030151b00101207040c0303454a05403040f90403d01c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 111940503 1250 111939253 111939257
    0x207030b07030516090b03160e03060703020316030603020102030a080a1401080708070501110307030c0f0804030804050907030213140105041725060e0d03120c020723061602060408100903 82
    0x228004e04034040d00e843d40c203d90400c2d0615003503a03520096440c50000b206001c00600510041300805d542d810300405214030900c0d1401a1241000c18402034142030440a140a0610b44582030015030f8000054480c030364034a00d4004c1c20382c0e503441039070005000100404141c041c0e2510011410800c003141550550301141d045a085655801c01121040c480c0101010a600100180400b10744140284035032603010391079619804030995225041384e8070039031084c3c4030041d000c2400e0100380b03800e040301504043e443c5001e41c14400c0e079a0542240780054443e004454498810180403a40100107030303001040b80202c5001e00d08102406142c5400c075806042094915441c0b455414001141705441950820340e200f038040f4551106010080c10702c84029030902070283c1840e030852109000742c140b482d089070701806802b4070704603108600c1d07884c0d1348524200d040d409030f40d46195100c200589912010065005004807d607001050303185c8110f4000035250f0040da4080c941c09420358007e041ea01d40f20f5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 111941753 1250 111940503 111940531
    0xe030a140f0a0b0a020714060901090201020615060a0809070f030303023c03270c0316060e150702030106030c0e060603060f0f040f050106022103090703030f0207030b070305 76
    0x9030381080d0b1540c440482c0107020300c0d9514042044403506074050407581e8824002c44080780d07200c0c40c0340b9103020f108848000d41a03445030071044c210350b414844160001e8103000300546503151030000407240c0c05100a01f1080142d100000b0314070140c00c00c120401000f140c501a26a00e03100c0c10001c0c0030754451400c0d0849444a860b030b020303015015600b00100c444400700125002c680b6201114665800940307940405504d0322034544440000d40c18118191a0100003002d006a410041c982003518903400c00ca00c03010844000c0044941020035131120703140c00c44169001011459008140307001e2100b029400d50300e042c0010041011030030710300e825540903041001c0c042e601e035401c1125520040b24100c2d00408084542000d50409001c01400c03608020404101130022803024012a0000d80c0b000e0016802195150100d810400800d87c0303200f0010320452543c58445685903450303c4920000b81041940300004032458407d014401c082c6610192040103410222130040c050712094462480010f55 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 111943003 1250 111941753 111941773
    0x907120b0a030804050d05030706021308060a051012020d080d0b031c090e1e040605011401030e0a14030408030a0e0a050607050706260a0903090806040b04060504030e030a14 76
    0x800d0703a201d81142d43c800c500c0703890a81094184440000440c0e4110b03642e1105000a23400601980081d10f404000034580c0900e851030b03c040300c0d1801001070200d0301c409241000b80402c031072a4a030000141c509038031004021003128800300314202c13100407002e440414041641108508030390072490b03a40904500302c483c04400b002001a24a1215000c40c002c2200c02070200705091080704410380c859405200103400101c00c0c2000300c020042111b0444415503a8801070040b141141e24290907444280303010030040b01a0b0300038540c5da0b00c000c1e81c0504a4030f07400c9070340901c094041040b00c0240000d0419a40c5900c00800081c10340d0311200d10b01c0341b003050306400104007401c2103010360782c0b4540c01500900307520780b4210080d100025074482d54442c00c203040500307402c0c621140310300c07901031900e0150008042c2440c1c14001c02906141e0410740c4250011014070000c10103024120b908141c1012000030709403624641614030404d0303001426014010003036240c0500c0b100e40c000c8400320048009545403480c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 111944253 1250 111943003 111943009
    0x150a0c08090a0b131217100324020f0403050c0a0603110a03050901020f07050601090b030102040803180d0b04050d090602031303060b0d0506100f06030c05030402010309020102010b0907120b 83
    0x1280d284a0540c420501800410f00141a490b01300340c01314040e40c03034044261101c0d10100507000d80d41000c0741c1c86911004e0400c1c8070480b425881481071108220f418195031b82e000c88090041402220141c0c1d000800c001c0b503089d5412680c0040000c80380b140d44550300d1800c180c403002c0b1610300511900e1f114000040550180c016100c076042c4d904600392034004541c10a034000d100203090310f01659402d10071003840100c0000100b002d203000742e0003800305614105588064880f041d04213030083e40107100c01c20600c0f0380041641c2044200ea100d580d5010542401b060b10600c205001620f040d030351a00744424004080f62100c4400800c3c1d0780d01c00d880c3e4076454260307542e1040580041c0b0070360f10004100046022940091f82000b00200b81d00c900100070f450b410300d400da0a032000c1003810601d2000308654880310328540018012030605102030500201c000c1c01c00e000c020f1004e4103042c1c030340c000329007160f03c00c0d4031401842c0c600501760145810006802000102d11401207002c2902c0d1502c41a80786c0307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 111945503 1250 111944253 111944267
    0x60103060f0b010f08040c031202100605040606081308090d0308010302010f030606021b13060b04060f02121b03130b03070f020613060c090b04030f110d0b0406020f0c150a0c 76
    0x1a041e168041c40d0184ca8504440c2040001c100391040e1025110110008402141d10303603200701903a0042500d910050500002c07240507910003845140f50200c10400c494000c481250300151040f0940020440c5041c60206c5d40b0034a110540e1001314000c10b4020150005040d9041c0c1c0d000b0303600c403441c05000301c00a4080315810701824015a10038980313120640220383c1181151000588034008000c03400b0000d800342c030301c0ca800091410030003107401d0155941c81840a41c0c030703001c50f00c004d1607000740301c1d1000c01c01d922801c402103001000740600010760581c1007045610000300340303480c0041584d8621007101540c0080d10044d00007000360000c86072807403002903040e00801c012080500d585809955071002010362001070001d1244600002070700d58108000b03131000718000c00c4031801c080c0191904a40d00c000f0814036611031030b98504a880443c50b1007901e41d80c4650702c21801aa10035074145445114012113403980502d10030600340b01c1c43c0c8403110040034011040c0c000240070840319181c041c1c1d460 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 111946753 1250 111945503 111945521
    0x6050105010c0f02040e010e010207060b090606031b070f05030a0c06050a11040b13050910050a1a030402010309030e0312040e0a050c12220501090b0906100530060103060f 75
    0x2a240c441c005005441d086c0c1c0710040f140350010000a2088213071110b0303400c4ea000039005035110740d43c5402031005030410010840d0f0141c0210b50322841c500d42652005122030005a050b0301900d00803811604000038404040e0810360410300702c85d111400074500400d03940c04c1c00c00c1280d45c5810080814002e03500740c001d20b0101aa00c48000d0b00306414902c107800e42c1d0704000d0b08007203021041e1500080139101c0c0074503280500e000e0251040e480741000107001c1c185145502c95058105078110400f10f0301c4201040ea0342041d0f091030080384514841c01c4c202c2e02000002503066240c01801c2c2924401200c40000b081191080c004100542d034032002c1c178804960080310034503126001004100300207030b2055030b9a0390280c083c1b5501c88915036036112440200100b11802c50f120782d1344003121800e00c0030b1402c0c040d9101542e81c0c001c0440b440c022480f40890510351085a002d540c00303221021080100a03000d0741c2c500e141d4410511103903806005c140d41c5840a1205803046032a01d00d0f1032500001d10300401c000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 111948003 1250 111946753 111946763
    0x3060b042a080a0b040c050d0c1b12090b0313020102010b121203100f0e0a200d020a030b04091b0b0f03280905010c090506070507060509061b0a06050105010c 69
    0x128070820031090b96100401051404001c1e900d40801480340c1d075901c102081c0320301540d070712501c4048410108040741c10741c042d10030a00080c0f280d80b00d1486041d2006031645640040080c1002c4200304013640c003094640c2100101000c04070030806da040807000d4a80c8a54000d07402400790301c03102c2052040425001c9002242d035004880c420f07101021290041d42c00c03401440358000c00e40d55822a8800d81c2405810040c1c4e80c181240c2800078560440c001c0171401040c4521154150781c20189102003803007503079005090719030041000f00c41035000c1d03800509401009003051151450a00d000004d0600c504507205481e00c3c0c030003011521010610a035800c07030b101310111900c0d64031031a148032407200b0410001012040f810449880c00b01c003500414410610980010424000148014000d0101600322a0082070244042030100b8400224607040f43d4490800c140d41e6a21203010401d00d00c240c100c408030160080d1449541c0341030014500c0103040c0100c0c820000f0380d81b81c000445214240307000180c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 111949253 1250 111948003 111948071
    0x70605070b010501050306130207060506010e030c0901050f040b0a030c080f070e0601030b0f130b0906010c020105091201140906160302071a07180e1006080c0a08060105070204050103060b04 83
    0x865004134001d54101e81f0003000d211180848616030400c2ea442400e003140d0550700e60b028400b40f560030240540b9a01c13800c8000e096a1b40c5c0202c04601c094034144600ca2059580c00a070350b107035407100d074000f415243c409440e149140b0b85a04003803006619034420800349104002c900001e6607008901035054590415408499480e80d80044000d490304c1c142041d4001714003c008020742d515001410390440103a000846e0f9001041c080107000350008007039a05008449400c0401030380d0180450300e8258049071642001201c0c00c81243c014420b400c80080d0306048001880302102000407001d03c24045003c0040800c0c403070580c00c9042c1d0140d1200102007030001000f80d06034058148203164003140346d01e8908102e10500807400c105038281d92100e2207000e400c000b881001140320495502403c81400c0181d42410050184100351294084920401c1201c10100d845a0300c99400c4030680c6400420a20855860b42407450040c08075000c030920035032801c110310102c8040c0340343c000200e103c0d9071540c0d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 111950503 1250 111949253 111949259
    0xe0901052401030f020a0f090f0602070905040f020621060321180303030a02070b090d170a0216030f1b050619090507140109060e060405060a03140f09070605070b01 72
    0x14042212822025040c1512016210201d41311031003d817101141c946c1c1d03414891456200d01030000da031560889000010b404d281449529000500030048822910f00007a490760707079080414208d445070340025400301d400035000c00c411100c02c2c542e00b04003440034030081c1140c48000425903a10414003e28a900d00c0d0424900c0c0b0841c5224090003010000320144628602c41000003401c69004440c00840d156011441d0021b00c22044510750344200c021004280784c00c4180809422a00054590142030040100040b581405a0107507440e5003803034610345d902c42086250144c241c0a0003d2840000b4807210441c50104c1000c0340b100c042c26030000b015180b2500d40c0c6412020b8100110b90a551403034030780c01e00301d0010300700300001e1008101030703d5030012011111000400c82c0361190b011008010380080c400e8026071320b520440e0b00315981260752990f9114501015009050152210348007080d403101040640e0000b006014070680c01681130b5000c80784c032220b007503a80e03015040c1c1c0500006e020300018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 111951753 1250 111950503 111950551
    0x207090b0402070203061914060d0f030507050303070306090c0804030f050d090804081608030c03180a05131a060c151f0311010807030e030d0902010905030a08040e090105 75
    0x400010090720152070114a600402e141003015203043c650448120180f1201c500c035803140300010688422414202d04000c030001ea00300074403110142046010000780010940580c0403904040d034003006403a00ea15040401800811080c4528440b46080c601e514280e580b09000b07141c803565050f113800c1c10301c91a01c04100c4064200741000c4120981e00e00746100402c509001610052034000300a0003844c84544415007111200e90204840d41d100b4000ca00d0b80c1a40401500c960760260001d181a55503004006401081c0f10b81c006a00440075142d03480d2201101d802000b0081b480d080361030a801c41b21000c0c01903038414003106030b00341d40289990f901510310102c52160001c9071a8840399030342c0da5948010400c00305030392084400c03000d8070004040c507503040100c0c80e034000d0040c101003000315170030340d407240d228401e1f0040c001c00e2569070f08101f01168011810140a041e000d402c0324403d00052030b08a81c1d980c00ba000f06460b0303c040100240e038000d01409030714403070841a0407104140c403440c520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 111953003 1250 111951753 111951761
    0x90d0c02130617070f0806180111040909060b0a0b070618080a020a17070f060209030f0106060c0302100603050c01081b0703090e09010c090b0a0504030602070c032001020709 76
    0x4100ea10850003507211544100a00503440034201100c1211540a08816811300c4d0003182d0740242401c0420310810000c120380803d00d56801004407044640002d030441e03405006242d07106042c1241e8801060100b445641750b031210403502e1050504124100d01d45d4100114040350344540066020104070030340010b255a0007403080b0401210140001140c0350742d41c8481d903000400c000b4016404031102c0424450710f201d42d0f24522811014041c905901c1da164940c40c20003440c2c0103000d00f50002480500740d10200f110680c680c0c60742008124003504d0b4840142801c441c60380503001403081c3e140c6090f42c00841d2007441c3c00c41ea400401440c02207107050064540034030050021948030208103420442070134482c001c0040c940f2030b40e40e8002140c24010312189214000d00383c1c001980c90304001c4c51000d90400d0070a825110490308140e180c1d405900304a07000c1c800c1c0c1d00010300241c000f02d20b500c00c2056004440d416207105082044001d202c0e002411901c0d8014441c103401a405040d00b080010b406600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 111954253 1250 111953003 111953027
    0x1406060f071e060b1305071d0f030616110102030c04030f0201050409090501021308010207020a0e060a09110405040506060a020615061207020f0c0d020916021609150b03090d 76
    0x75000341103010160b0440004014403809036007054644800390803c1c84d0100d0400c03110f29650008126608140c2d0004010b880300400030729600c00407540d02c014a0ba19145415544071004085a1a03843d1260010a0780320440d04620301080d940c0d0a80d400c0703000c3c18025a40300f0004480c01ca1306043c6180c40b140646424410147d0500008002c081000e050b0790140c140e40d580600000b680e540003090340c0341c414400cae03035000e0000303a4818031241005070307100d015140880d255a81c40300c0342c588805002500855603035000c076012504e802c00c0f40b0b41c0d40b040b03000a0011901d04031070412140c0d40341424020541311f10102d51005800810000eaa501c18409460b080d08001524041c242118a1068002d8800940d0740c1c0c1c015030700040101c510484c0c10045d4503040001525890900700c0c00b42e01040d901d200240559071514006080d0001180c0b08000d01e4200d20707811081551a40d99440901004010041e0403c01080030544085514000b2400f01d03802001020020b14031040c031818102c4d045003c002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 111955503 1250 111954253 111954263
    0x20609060a0908120c060f13060b01090504090506061807020d03020c0106170609060109020408030f0306031204030f03020c01080106050315010c0210090f0806010303170c04050a06090503011406060f07 88
    0x28030b003c1110b040c10080d099201e41031882007981d84031040000c6240c000000c0030b4402a202800412002118291001040f5640081c3c08202000c0d844016244089540c101c6a003040c6003040e05814024000f604501038481514502803401702040c0744c0454050845000c0050b0b4000000c00078228804c0d07000b440701702d40f440000142c5607142d48c0d210000c01d00010380628a58841418809000020b201c15801045004000c52a01740ba020038141c0301d00440d1404068084040005401a10f051002c40d07007044184e281141c1d11a160310700700170f80012441d815401480f8403281081c0950040340b105040e81c103145c4500b415603880425000e80b0300040300030a41000303142100080107844038410003011030000d40314405118105200d00780c103802c040d40b0032801e03540118010804207030000391070340407038200310220b800b1951030702e1201d0154822503100907044200c900b00011501d43c001c03000400c0c0c0b10300700d000f407001b45141e03d00c05214645c00d80b141a88a00100040c0001a5000c002000014072603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 111956753 1250 111955503 111955517
    0xe1311030109020403060f0b13020708040e01030c0806130b0f0712050705181c0605060114070c0603050601020321070c05010501080f0d0504080a02090a0209100c030f0c020609060a 79
    0x2104042005400c280d200d020440c0d0007140c24010040307140034044101c0f170142c0013084090020300020302c40c86200d8441d2003000354005080c1d03003030090b00b0301120090070b000020a036141d40c0d2072900d2a030941d09449a50345034081c00c008600380c1c0c030140c000409283c1d085140c100190316185440340a84202800c070b00f00340110300c07031459808000c501620f84504125103840c0c0d140c5098940a00c42c03d404140214411002001443d16860003180031280c21074008600003000e43d00d080050714852546c01c1c00031000039012520008202401c90110280c03980c82d50280880c1d1218001640d0b280503880c0e02114401d0300c144907e61111a128119a01100b64030300a42c000015850350750840c0c0013a0000c0055821010108040d4407040001070548202441c1c050300c3e081c0b429840c2030325070f51440002072240c035180c00030503000502901500c0210000811502050284800180c11500d50b10007c0b004101039805a08405000c0d03203030191320680150080303240461030010880180d101f01d41034800c1c0000c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 111958003 1250 111956753 111956771
    0x12110304032117090f07050121020a031d071a090607060f0b0402040801050103110307030302060f070309021201050601030f02040b040512010905160e0a060510031a030610090b040b010e13 82
    0x1462a03d4040d130369550240001c050204070180c2407a11580009060205500e142d4091512803010740f041102502401a15200c12050407405400003440e14203126120341c0b452900f8030b2340490148102c640b0070022500001c10300c141c0711068001c182416500040901c10040411055005801d08045c031003030028010010324002000c03030308250080c070010b0395a20700600c00c0100380590501091021802080e55030b1641d030b03009644c2c4c40d00920131684482c100d408150300e035000350800346c10198000c02e848607264070303258494001e0a0480b0024002818400700f103080030b08510031601a1003d00200364a054100b10902844102507803440c80150b60301c541c01030208105002d91404600c50600008201e49081426050842c010302141003aa25001c0e041080f42d640e4103075400342c000c41e800c0c081030022507050075403420040400c0c90394040c01034a0810140b800350307041d0601950f410310401c10111500c80140401c07a000c1111b0f650118400b141128018a0701f10940f12120511941c0800d000740 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 111959253 1250 111958003 111958037
    0x60703050d0603200a09111902150406020909070e130903170c092b0b0c070c080c03010c020f0c09041403120414060609011e0e04121103040321 63
    0x6403552100304c203081c0101002054582000080014082810180b11035412400e00d00c0071442100f2036201e000c1064035007100c241d030017804090b0030b80301d200441c0301d00d41c41d1609003023001c0d500841929105400a074001100c0030f00480852081c020f01400c001c0c16038880100d80c6d0024128100194148058041e2864220700c05111711481400600c40582e1a504100309014039426201200c44c640380c851001460184841103401c0700d199000207804281c1e45a00070219820300c03440340041d180724816a0701007400000004c420b0701c0c80c0350503402003280c00001c8200301e807905006d01c1d0b03142a43e004100c0280042c90400031003a0094014004511441aa01d210074a1948004010008120303a42d04200034040080c00e040c24296040d0f01801103840c10740009841031805014030380d112001c035020b0b0780111100b109460007805104c00c400c0f0b01403c1c01d04212403441e004405150000d1190284d0021001e4040150b40407254010740d910000000001c04800082020444c0d90401081d159001d0b2002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 111960503 1250 111959253 111959273
    0x306020c0c12070303090b12060402030a022206082d100e040c0e010f1202010c03030b030a05060f01150507060b010201020d0903030b1305150105090307080a0b0106030b010806060703050d0603 84
    0x3110400c0141241843c42c079000c1c050fa0f120341d001d0102c0030307c1030001040b0405a09507440e0b01040859005030303285c2d207400c50300b0001d001e070301418515004c0ea01c03451401c41041440002c240e1300d140d1104901d0760b0780e5400d84090340102e0181801c0c600503468621440710071340c0012a8100d500581d05042d21078803014112402c85086505a8002d03079034040800c00412008ac02e1405410007490a000d9107003000300442c418010040c009042041c1064a08185882584103061801005059400c550440e042c03460350f6240551740c4c4814000c3c4031000040710ba20788440390386074542d5900da00d401c06c0070580301d1100801a208985056540810084159030054441d00c5544c03403203524002044c03444d8a0a0101006250200514103846c04045c847d1224100b4203007803020901346001540c400404000c00d051900d1a40401464440c1720010400c2003601d00c8444e068407940e54007000300015680045500010076521203402160401074031020a01c41c40003001d5040c00d84d580402c480d0b5aa940d0070080d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 111961753 1250 111960503 111960529
    0x31011090301020f0a090f05091303230705010f020702090708071809020307180605040515070203010606020303090f01090804030201200a1103010614061b0f0d020304030c0503030c070306020c0c 85
    0x84400017040240140c002c8904405040c0c14662403284074200004902081c4025091500b5000d2252410081620030500d4141011007a41c240d0681401801c580c0540d40042d072049900c1d501740f4103420010262407099404450f00106004619220f042c0140c0e44403401401000402040d981d01d8601c41c00d55051b114002e207042070300181d40b840c00700d5000340030203144444805502d000302d0041144903403000560303083c1c03082110031803e00100003503500054032603500000c3d055400d0500005c5d0240e004030103548200308410a60700c40240002006080300d11b071741e400a15007203041c44140095403181c10541c054200001c8581a010342e419a02c5281c1031152208644001c3e071000010024142801076600400c0c1c1140c5142240c08510f000070482c0c020481c8a41c06036900f1030860400010810803c00c0403c0c01c842500c030580d505420003500ea502502013036401007071010b80003900342800030858000781001c901401505041d5a00c00300a075004507802c0480380b05140c40b00c1559030764004001d0f42 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 111963003 1250 111961753 111961777
    0x705040b011b0b15092404021605101107051f020d1506020706110c0d020307050a06080a0c0507080304061518020c0f120708090a1208030a0b060903101109030102 71
    0x115250195203140e0b9030244003484d81c0141603c005101101038003c0c4030b090071541062105070a40c420801142c028001d40028601c00703807071202d281003446404282d5428860740100c0078007040c03041201c148268031405000820f194403017401038420b40e249543d943c003140100f400147c0360003030889205068410b80039120046020004040081c2c0390100103900040c03d00d41007407444d03050011010f81c7c807a01c9000d9214000d0340e000f0b10040840d45d05100020140c40c00031302d0100282c2c2c44c0d803001000e0138001c980b0f258207185000d045100c0c16026a0030707601c0040d030080e0340d18a9a81c0d90b07600d80c1c01900c120420311a0410b0300d0b0b100442c8a04117281c407030300048400c01d80142c0b40c0180c031a4451511a01e0b100d035800301d8207d001c0c01010b03e03000d08200c405098011100c9581c81100101051001c607855110718002c0018200c00c6040050480040d03010303c00d1000e041c400c0d00f00000400801c0e210b8800b40c2503069000001c610403068a9402194001c2c0300c103420345080c228018007103802e90340482d0300010b03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 111964253 1250 111963003 111963023
    0xa030c0603021b1917071218080105150609030c100c0b060a0308040b030702100204242a05010e030c030406110607080a0203181605030d08090705040b011b 68
    0x9412122a204445044800d60040c031403500c24a011310b400c01060180a40881c1110008002646144080b5440540d0151418524106503070700240035095444940c110100d00e250b000410103414020b040c02200028422800c40d003086080125562040140c17a80500a40c1880301c1a5580c40c10b02c6400c80300d00e03441d03c601c2e007211031802e8082c402008004501c05d0309a24810b101040c01c000039602641c1705040881d0380c039200d81606900d003e070044088424140001401706404040f003034010440c0140149000c0c1c06001080c0c1912401c00d1959031460062900c5050a0030f000560780440300f89000d01c00001e80141d20080035802d581c0244441c1d100d40c1c1c400501000229071202c0c80d40303c403c40c0c0001078409400d000f00010084600a040301030300e541c0120100b00600d2085445074402018882120750072201c0e41e850160500700c6110300b61182c0504111944080e0041d078000f4844d20011380906111030508040100820034030007440d040158000e0a40c040419151111190034040d00c8022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 111965503 1250 111964253 111964267
    0x40501020d061a030a020f04030506090c01120c080712090b0112020a050111060402060d0e06040c0e010602010c0c02040f140c031909030e010f110a03090905091501060503060a030c060302 82
    0x4410741d40968031009203c6420320200710050b286100780ca400c25030a08000d030341c840072450b0b101d55074002c0350000f40c5280541c0c1c0c180302409600107113082d0307400703420f8076042000c40001042d0003c03140e04041007804240c80c8000600142d115030009021010071420000301d001c1c00361500140c11509030003000ca00c800140c3c1c075406504d131000996009107403d113443c1d1848d4100c030345983d0f264040031b040203009120201e020344a0110642000c0301c0031464200300c80003480d00e803d0030400c00115101e080c0c4546031140021410901c18081c20b034a064070340c3c54101545840740d080c00010098001d80c0c2802c55a01c075140001d04000f9841c09016500c100070240c2c0301c1c100101d4814807040440b103030002442c80d246c400c1c00083e801c010075204621090078240400c2d142c0510548940c9540c40b100f0f40c403809000c101408064000b0202410f645171030004006035981c142a1540e03074244c0c048415504a54030004000440c440e00c01564411400390801500c1c41c3d0360707504e010303072031030325400400101e0340119440c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 111966753 1250 111965503 111965527
    0x20d030f0909240806100b0325020c1002071505070503160c06031506080a0534020f0f06010b0f0c0106090207020f092202040b0604080105010612140c0a1704050102 72
    0x3e0014100407030107072809040156140a14501c42d20411031010004400140d0b00145e100c00400328184001341c00908900d10341c4c00039201c04e02da0160710300c910000e2003c008150310024089055400a0325032060300c0800398015600ca03005281b04a0b52172104005084152140d12074402c0c1031849a488030204a080880103415120602c0c00803040ea42c040000b0062640c0c42a13a081d04111401c10001e0795407aa50003480c1c1c1c803041c548007000b5a0000b1101104925205290000c1c460026825100c26000080002d61610403d030301803150303603008500500c00307040100020134060100c010403c4c80d1100c003907019400e4034221703440b0000c41c9030702107500380950904c1c25036010f00c5c0504417030162091601000000024040602c1491030406107621101151501d44c0b080510408c0249183c3c0c655684440082c081e183c00d0003048006402c040f0491007020540c080c0d211824050042803001d47d1711081d0b42442074002c8200401045030100c5481032801482d144940a10300600c005070791400c80c4150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 111968003 1250 111966753 111966821
    0x7050601060813030e121b0307050604050d0b130c03051e06040309060f02030405130204080d02030720220501081b031002030a0905030307090801050f04020d030f0909 73
    0x401da040c801c0103010000554103040e50040002d40c1403c000005c034a4030400300e01d0a00c402610540c8134400c0c0c41c05544a00624110707414039881c114205c626581c0c541050001c5802144a02904507056460301000101c0d20120183e00c002c42c48950340d810b440c5034644e035280c0541c0342e0054a0341d8102d00c5d902290302c0150fa01402c0420300600c0203012a0905607030003000d1001c0c5114030410404807940a60040b03200348101da0040500810f10007046ca0b0011400c00294810f116a010f10722444028810042c0040284c0b81c1d0030350046555a040303142c0d40591080e08220194655102103000c000d0b00e0b2807407050000c400740403d521000140b56040c04101c81c6401c078030300010810720100e0f10350795803507541c00143c400e024041480301607140e440d41004100904503290300145240008000c11003d5544641a1011242c003d0300038001916100180b101071401130382c5c0a07410407640668400820b004103d500d10815592038210341d510b40c0d6004990403902c41d400c5900c50790031105031100c411007110382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 111969253 1250 111968003 111968009
    0xd0c1508150f1003201207020a030516020f090a09120801080d1407020a0b0d06140d02060a0e0310060611070f18060b030a0c03050f04032106091107050601 68
    0x24401d04201d10754001481c0e04515115491090400000e11480f1902c03079003145e00c14050001203007a61100301c4a00c480240c11200c440010001403c00051500e440010042007140d010f407142440c0001880128450360489481a0b801c0b54510405400a445100b2410300c41e402480002882201c0c510f0005c0007159600981070801004000610001c0d802041c0f07110044c00c0c6e402c3c642030a2454842c088040d0040e610082d500c00d242807030024600c015040104046000034104200c12520364075550101c1010000b91900013181003194001814610f004000c410954100b179403068250900091809014a4000304080d44903481000225013126044109040d400c018004c074604100e00003100b205284250108441c11072031018100600c1c6d40140094250401d00c250349140000c036403000340c5005001040040d24200005510b042540300c5c544c0500c2d41903442a58540099032101d400100352a110440523135074101c00a001009482024418000d4007070940d290f4459042032414480164 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 111970503 1250 111969253 111969271
    0x90b070314070c1e0302010e04020a18060309170403150902010203070c0305030a020f0303060306070c020a0f06020c010806010509010210021b191a040b010501140403080d0f0b0105040509010e060d0c1508 89
    0x41045c0700607a00f1881c800d04002040d5070058550b140c0c1401110030031920320780018a000440008910350354160403600b100ca01402e400c0741059483d88602c0382c28419440054003000c0d403100529465803468000b0181280148100c03410400951154407588074158000c9039107900014a400c8019014800a120414000040c1d800c0d4540f10b80400d0321080020607941c200030704180b000c1c086503101202c2c40302410048070540c038900e480e00806540c5400c0580800e011400c1c0f840068010740c410320445000e014181d010701030243c1c80c5403a00020f500243c030002103504005040c3c14107050b00b00901d03c0206c86202a0486810940c10400003601013500c00b26007905041d07040202144591429504450f0203107803c10111348410801d4010b405540c01c000e003c04400100c140f01725401d50800e41c0d5600f001e460800c2744030400b000545481c071552160f00c2d0010f103040010803680240090845d804070000c0e02000e00b50510b580d44074846411034011280c02c0f543c455507020515800042140e020000c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 111971753 1250 111970503 111970559
    0x60602070302010507060b01140d0b0301141e06040e0a050a0b0f0108030703080411060301060f0e0103150501110c04020a09030b0f011802030a0e1b091006090b070314070c 75
    0x142c000802c00d02c070300140a0b00749500c6890003d05644075800015035440311008070b43e180c202c0200300d0000742048440b118440d41c00c18200395940d000b1010107a0042901100607a00010141d501c46a18200100a15413061b42c445c1c066442714005d11413440d1091043d8044c28100b829031609141414024191141e003c00500050003030000003c1210845034050401d0711091742c69280c01c00702e0300710a0780050b8001d10040000203030207030401c00d6072144000c0b5448001618034283c004504456114480f08985005000c04100300d5004d1001340c002910b60605072150a0364000100f0143e9001010103000a01e200001700207020200c0e82050f0001142c903000000e65252a040c4007203907540f61001c81030141d000020030305051050b80300748003e92501054900803660712640ea90803003600b9802d41c2c091b044040c0010b07070500500a42000783c0c0c100392144104503082100d10060703a08800e0f0300714203002d0707080b0300d414a09290740080c20800e84183c444642d40390074030b154100c0f00d10607030380c0d0305404e400d00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 111973003 1250 111971753 111971759
    0x3071b061b0804051509040f0e0613110a060f1413090f0902030601080106090c030506031c020a0618060e060402010f030203060607020405040f020111160b07140607090906060207 78
    0x403007580780341d60303100e451404000d401803820b10022501c11580321540c403201c4003c02c000b801051501a004140c3e0440741008000d0040f1b02d45019178400034081d4829804c070600140b00d110442408200c0c090040010400c10000400419100c80441d084103002c12900305140580940c80a9003546600181009a042c56000116251048402d0080c240c11039141c92403000c005c4244d500601001c0e800804540300f95a444c2030b290f0082c0304601500440b681801d00040006000b0f001c0c16001785c00c040e0045c0046070159030841202c190021010085015078902c0001103800c1d8006e0002400161014034011042441c1a03c07c4a032600d800603420b0f0000010000980c0e04200580076009160a0159036680c824000641c0e0344102c80c4001e601a103840140400e010078034910710340d070600c00c1e240c4600e0000c10304a4195503500325200c03c101191298000e02090028002820343c1714030940c285000f80411920450910740100c9000e0700007401e1070420440b40340240294001459070340043c0140304e003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 111974253 1250 111973003 111973007
    0x2206020a0b0403140910080403030b0d0209040f030e06070b07021009112107092009030706030f020d0501030f0203120a0504051507060c0815040b010e040504020a0b04060203071b06 79
    0x144090b0030304c01d81d100c2e0124410b03052000c1303c0b1844401840e0403103c4001d0480901540810385044e00000d2800045810b02c0c2881e0000081143e0000c0c80111603540c0e60355018a5803070910b1084081015020303200e5010346030b0002600016208019034000b034600315400074604174128049190050416680a0110b601141d018070a440c081d00d00d9090100305062803038420082692003515841540000218852a5071155518411100c1542d030402c45160845105000307840d5455419001514100700742c078000d501100e0030103405c1c0c0002d0b003003c26071000032003100c409a00c141e40c0e1300d0714040a01c0c01c5190504c8144442c0d00804406030802c01600c80041c1a80607034010140101c40a440b10f00d05a1405402d42c4c001036400303007050000b00c1c10f482c0024032040c01580d01e03007070225403291a800030386028010718045030410707561442d001d00302c241080003500c4050700598004802c0c98000c541068034500620244c00107030011340e0748a006142c4560701d00484808240030906000090010607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 111975503 1250 111974253 111974273
    0x30b072109050f06070314090703050c01080a0902040f05090f15060f01020f100b0a06030204051014120103210c02060306190803041e140a0308030705040b2206020a 72
    0x240818000003040121440e04526180000c0300f400018840c2104100b445917151308070b05108200d981961040c5c1e00c61941e001d03034400150000501d543c01c00201010303d544030b0000c00380c1c0f00d031004201040c40d00158011504071007000c546090140d444004002c60300c082040b0038a00c01c00e00c0300050220304041e0003001d400000103403989114a0040c0c101d1411a842003100c10601c00d15039090341d42c0c100c6030340c101d08000c0c410002914010803000000043d6103001e40f003918101c1d0030203400180540740d080421201924550648902c040d4180301e02c00000c014085024007030340c4291401003400030605541e641c40c2c0011244007042205014243e001a1200c0040d40e41124065a034800c0d01c00306c810042e048000c1d9600080d115110124001416005441021588600100b4160350301074942442e061002071800c10a500101c1d51042080007860300310003117070f100815103131580c105a145c0c41212403d07840b40501c180c1d601885400780108a0351642600001d00b02400148040c504a60346c0e001d00c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 111976753 1250 111975503 111975557
    0x1209051909050603031c1a0a03080909280f1a060f03090a0b160305073b060d0501050f0607120c030c0f08030a15050d06050916080601030b07 62
    0x59261000f00e100c5440800c00d80e01910005441000d21541d40300c6824018044800c2d0081c0710480c1141d64441800c2030b8800c0303400e50b0b0b0407030000c52a007000c580c02e06c2f24111015180c0d455041c0e0048200c0c4d81028414407001100c0d103660b2012500130080c0110506554038002d4462007003441460b1a030b419a40d06d82111000101041100d480395201b40486042c544000030103000022040c080041c03a144110019410481f581c9042096480392a02140d50881004414274080542040e00081d01580c03150b4140d00300780c0f000106222040c6030b000c500c3e0380c0c002c05001c902050b00d80c00140410f28190f048018508801da03403840c02c11440b03071156410445032030520740c14040c0108584007850720419000d040c2e5030b084000c60b132840701186043c1083d64001c84450b240c1614006084000c40b03030340350315601212402001920f4212168803280c1c000c00c0054a100c207940318107001c1122a8910f400341d00d00a095a00103400c1542c518103164a0034980200710908101100d110030b43c1041c1c0303488a503064 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 111978003 1250 111976753 111976769
    0x6010b0903031c0b0d03111203040c053d1103180114070f0b070e01030c02031b03120103061d011104030b0901020702120601170304080303010902090d0f12090519 71
    0x250300c24032120002004c107204001d801460300404401031542002034400b20701403190850b9000d4112281c10203542c00207490047c05002d08035410060b5181c600c880114014000c100d50450b43d0344600072039039242c1032084805089071000c1e0b0f40600203400c40ca00c004a80c81c400069490312207030f02c0528004078031040e900c506218202ca03900c09078a543d83e041c1d079601a8048114121500b6908140d40703840001c030341d60f60026100b41815420f07540b09008040d08001c254006500300903a8041e03c02d08405400e00c8001248000e010381c1c0c44001da41900304d0300039405008000f03a0009080390451410b404d8070f1041ca4541e052010706108013a100040b1000c0300c1d0085800b0784c07240c407100c140c940a03101c0c1540180d0b02220010405c0704041c03010a10381d040b078810744000002800000c1c41151280204d2181c116940c000344010441105260001c1c80103100080c4114206a83c941e969120100c001c00241c421000c00c40f0404842604006450f002d03002c100d912100c1e01c400040c1030f0748018554050008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 111979253 1250 111978003 111978037
    0xf0f0d080906070f02070801151403031602043303061401061d0109090c0e0f0f0f10030e10020d06170a0f021c06050604050f0402060d0b010c080307080906010b090303 73
    0x403461740309115550140c08035600a1020384c05a0000040d008164001e00d004459192004112032a0002c1160003140c040489081040e03132540800008010001d00001c504151020402c40481815160038134103018500c05040f03d4110b0802400702d030041c42000c3d820000d444018003045810526488001d0402d070344284400c4800e00c0100c6a4007000e0380b103032190500b08203196040079004500c0c01c0041078140c0b4000c0d0644401c0e01040803200b140d030301644c0c0104400e10401598107040c903000d004840c00e8140403d02c40201100700c0c0c5024080c039096109146d011456900003001d50042500419682d1019004803000a010548030a803030040140340c00d42c25500d0004540740c0019050b1030343c0418100300f444141ca800c1c0040640000c03238409204910303240c00960b5010204401c1c9025940140a21307051114100301c02d4020282130301d84074140201820440f0020708180001c500c00c50b4580ea4103180380c201100000e2600b1410f8100c0c1d049000248000000c81e1800020b94000b0110101c2c160 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 111980503 1250 111979253 111979277
    0xf0408060115020c09191509020c10061a031506030702060906010608070f030c091e051215180a1e0209090c01141b01020a02011b0302030402060d020a02030c0f0f0d08090607 76
    0x98000e200d140a0b50103002030000d1f0000ea4020150702404003041e50100365104400c1922a20b011200f590217098540002d8400386014410003001a5038040114519244e8042103100007441e1b640084922000691081c1c0400000c2e81050040900500c00ca0070594014240f0503406400803d10180d0842016900c296100c01e203132103880e200340102600c841c012076481c43e40b1141c41180c1c030309005042c000c0f1070480310355800302d07000a070f0320f014030445444800c034a0300c40341d038030020034403e0107400100e6114158451012400c10042d0313030801c0340e2440c0540404020383c41802010a40101140c1407a04200100841a6000a5040903800502c490b250f5200c078007281c000f4405540c0c210300035096101040608a035901548043c1840c0c4901d4840300c0d140780c1c2031300120103a10040750000d401601c1441035900d200d00fa500034200301c000f103005481c20822000c200ba440c0ca079540d00c0303e100301d91259a40001d1400d040c000802903441914144c043c600d84025104d0361250041c101004000d400000c0c0307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 111981753 1250 111980503 111980551
    0x1801050402090a0c1b030e04060b0c12070c0e0c030a0b1e04020a03091410050903031302010f0c1a011401050c071a0403050d02070504180f06110f0408060115020c09 72
    0x1040000c19817102e04008041c1c2001800d00380703a02c1c00c6600461a14601181d40380311403050320b02980710003000f0700e80c5a08100000d951074004010841c4c0d41e481c6000040781d48030000320340c80e100760300580010b601e81c9409964076003a82c950458031402062000400d440040c00c484048070304840684001da61000f810078100c00500740f0300e401502070160440040d03080070300800d03110104540030340240501e0319a107070b5207a01c07440103070f5403907012050b08240c4400550113802d0042c85180c0500b00030f035210341241ca0f041ca09041c1c4002c1c0e5000da02c0040010f211180c0c1c45a050518410700307182083c100002c01c80003550321840c6009503800b01102d08090000c001981e070859000d1644401640d00c4a400315101940d52009801841c0c86a0706040d03010010901941c40d00380426041400e2103456101a101c00c0c00420060038426041d200c20860340d952414203200920041c070220b001801d9641c58008540c040032240d60401003190801402c41c0e540355a0480507542001c6201040c9800e805003a441c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 111983003 1250 111981753 111981767
    0x106020d08090708010c050c1006082e020c03090405070801120f1412120705030402012106031704050102100b0604030b09100906060302011107060f030209030c090f1801050402090a0c 80
    0x808483d60038082201d03a0346607c140a0101c0700c41c441c0844500c80003c03007669081d1225030003100341a9000340010591103900c08104800c0000c1c007001fa5a059040c042d40c0b50903648502040c0341141d2000600141c0c6041920501d41c3c01085440c01c2c550700d504044014100c2d8288000281906000c5e6030300005022000d0080001000c2007421103071005100000c0303036040d030088045d2004140f501c00c00107902c40d0083c4200ca1045a0594940b09944c90780d01003407000d03c01d20441541c4980d511180403000420301c9072101e00c540050305625031514901400285410245c41c44601114144007224200780c40c0d020903141500e910010409196983c081000d03d400c0d400c40c0b00c00703407032420110240140845030380301c007090340d0003a40c4480c0c3d00c508600380c542e6110fc1d1741c8651400500c00d01e04420342c0b10301c664007034901400000c081d40c64071151100000c00d03506c0d09541e030844514480c0d003802412001d00200000c50059000284142c0c60a9000a40441802000b11283c40e45589600c41460f03c110f00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 111984253 1250 111983003 111983009
    0x1a010b041415041403070f0302010c060c022104140103090503070809130906020405100305040c140a030b040605060405070f020c0105030a0f14160203071113020c070801020304020310050106020d080907 88
    0x612684865440c003da200c40d0714a1035200b4000c6c02161000f0854560246003030095a4060710f4900c0c6404080c1c1d13a10000300f008800400850107445080c59140c400c00b955044124580d804031501c07241003003914039010043c0c1e2203080c140341ca00300b0480c0010300084265010b007130708000050b480b00b81107030221320840728035000003140524002e40f04041090642c094001d0300c405072190b0031881604801031b4200e030320a880252207920140f5040107101200080a00c003c03c0c0a01400e10072652030b0344c4d1220a400a440840e00701e038442042103d00e04282c480e50740e004044d440c280042c91a4880043d48806070007911f0307410440000001203540c51150020503120403030000030480481c0b59003450f400c040099030844c5249034103c024004444c40001507541281e0400c4032107102014560820100d20451002241c10a809200e620040d04040c4040d600a0600c43c0c0050794038034051040609220808980c00d0b050b510f03000040c40541d50005450f405030940d8100b13200a80c8410419901d0701e121a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 111985503 1250 111984253 111984289
    0x50705030a0515011401081603200306091302010f030b0a0f0b09090c19050d1103010f030b0609010608060405090f0d0207050f0d0302060f0705040e01121a010b0414 72
    0x907001404100c00050030b40e450725100e440c07250756a603d50050444d20040303400c078940022940d00c08501010440868049107500ca070500003042d990801c0301030191595110b0380c0b501803002204016641c01d120070a10381c81505074102c44d250600300c3e80060004c1d40764502d52400c15944003090400d40e1034a050707480141c102061201c4005554500500d2161700c0320308010f0061664801181142800900fa18051814041f141da900503a901c01203815400c5081c94884c82a25400c0035142400c1c100e0045001e003440d081844140740c19420803050042000d0801401001410010001203511040c120340000b8200c40204250312204c40340c40c944002102480064041e009000340301e242c00060380b004540c010355400384200540da04100c543c18403540041c01681080703000983d6030500c0807450740d02840c103003891400c20351a0b000c000d400d02401d070014441d0141d402c1528060002e0140004140050300d018501d0742e60514000324024000e074814070384090f000103103090807682c4d02400d02c03e411107e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 111986753 1250 111985503 111985513
    0xb130609080f0309010b0f0120030702041b110309010e0d081c021b030405060301060c0f06050924070c030e0a0902030a151e0501081510020d0801080d020a0602030405070503 76
    0x408110942d50310507207003800c0940ca402c04406407030030403190038011180140c4545001c0111070746034041c400c01410f00c1a1840c002040301c071005941d00d20844001c807003007101c45241d0420503600940140701031641232038143c2c0f00313102d100e050340e038841d1054002d43e506403490342440800d440e003503043d8091900c46491044034621012078170803159021303181584107041d01c84449051146000e88078803a43c081c090b0407150400050142d1801001c003811070030f2042c0c0300f441c1080e40c16118001140c00603200c03034003190070030071400504200d07054038402681c1d8031080c0c3c400181000030b8080c0c005800481c1c020b040c0440440c2d40c8800c2c0c0d650105900080c0411032055549242000101d0b001b00409142400c4013860f0320302c08a4501d4a01500710261008104048482c0d42040b005484008000b0042c001b6160300104400298848400341481d0381c45e950000c024600c03ca81001d041c0090580024030281d0000720719060480e40041d401c1d100e5038002400698030345507030900c5404c150300c81c1c100c650075220b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 111988003 1250 111986753 111986767
    0x90201090909050c0102190812090c1005130603020c0318060c010204060c02030d09060914030a02040204030807061103070906051312030801060906020105010509070e0301090203010c11190b13060908 87
    0x1041c00413003448243c1c262641640f1039035501a0b030406a99002c3e08540040c400346503614022844035400078514400c403084010100c00044200c00c10720700711400a2804207082d041d14050603011005081c65050a50420040d5086c0d56507a026400441400440040c4600e003d521420110703240ca840210007990740d59100d4802920001400c03071b00301c0c000d1081c9079012051a00c5080d803801600d1040e5a1801043e2600d14081c107480490384100307601d40683c41050006179524030043c40207612681051b526181541040c0302201c4982c04425007011081081001c0143c2c08404101030700c04c28103011b500d84c4071510842141c2c8940b81c1000005205481e507810030300d0b40016856040b00c016a43d0f010740c2580f555001c84c00e0311070a01c151900802d108000c20304050282d00c190360491400760000507107886c60b8000a007034811001504002c40c0000503000765904050100340210141c0864903070b80c844941d40e906070350030001000c4030b100c911034200a004000e40717038002100d03130307500684060b40342e202c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 111989253 1250 111988003 111988013
    0x190e0303040b0901081f080c03120a0516032c010807020c030d0302220b071b06090e0c130b030a0b0603040b0604092108070306090b1f02010b150c010509120d090201090909 75
    0x142c423250a4800d11444060a00500844044a800421a646590410400c11030200d03044c98981c100b1020300c402442074611010b40c0d101101d0311504200e0310700038603070600030001d088074070080c02c00c0342150414140081a61800200c90b10001014030700141e0b80c0300e481d00075091401d20032952000b1700038611000240080b202d0040c0010f5400b4841c415807603034122102410342402d0344141004516990410040c3c400c006071020340c004ac040d2682031070440c032086070006202c01c0b034005881008000c42400766540061184880b201c0b02600c40d9459401c2584654040110040603140320b69111401d9204005845114480103d60079521082280440794083c003c0744d0112051800030b49010700020b0038004134020010340c05006400c0c0c1c05084120502d00181402101c1050155900d40c0281140c0340c445268211018400c20700840c0c6982c0c0b904284d40c01e561000c6c160190607403050708040e03003004440c812580c4000024100140700c60792480180e549108c3d079070048180503e04028a0b09000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 111990503 1250 111989253 111989263
    0xc08010b0108060105030f01090f09060c0804031b03170411030d080f0a02121305010b190f080c0102030a0309020f04020d09050607020d020c090615190e0303040b0901081f08 76
    0x34500762901d0030140e07141d80c011540c900049400403142c4c600c0320700402c1100704030780c003050080700052000b160300c0b000c070380b22141590100724401e80000e40120030001407540c04078106174000c40c8120040300f00760360703a02c1c000d00210082c20001d00300303400c85010400f080082038600d80460f030050195540042034020140c1914001c41d0001e00380ea10b8500080e1040320030348200c58104154140103c034944030214a200d2400b10107a040714599030303c8260729034960b515112002c0c59985022400f4200d41001d00508084007150301c00401079125502c0d100b0340d40c5e0003106440c0400d541b03140c00100b58131136000082481c035090b50095045440001c12041400142d000f00f0307515030080d01200c40075111840300300d0ba1440c0c9041c0c03803030042c0c000300700325101031070000720190f0890304c020401410300090300d1180d001c40d0b02a000b1115004003c840301101c464009200401c0320784218061805c0c14034080402c50244903800b1603d040182c00c0001618010802c00d00040140c00c86d64112103d50b1a0800c5660326 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 111991753 1250 111990503 111990521
    0xe090c030a050609010c1407031803050708010b0f0904030207031511040603020304061503030801140a08070b0304020a0602060906192903010f092012010c020c2b080904090c0801 78
    0x65400c0400c1b0b5007200340216210046892080182450100c032510b01325101d41101961414030340f54454004003150082001c2005070403003030000500c0011150800200b40e101e09100c2e030103030044208100c0840d8020841808603500810704003081004098404024810003400045802002c44c001c503440e41d250340030350300c00c1d480741e030342004501500c11011280f4011480001e00150104006120a05504c4a20060002c024081e119402e8598a44904106203504000701ea02404001c02c019490400480002014079001412207801c0c1310030401d480f000d009000c901100d03180d2141c1c00032010b448e440303404030013000c00203404490402200400c0340c40110600900c650301f4141c12013105452403240e600c55543c040303c101c001409a05c00c6c414600300c00800694008882c0e20a032500c00402e028009507001c0e550f014002d980b407030310100615aa00c114035100c0c441340300b19090f46918021101080c086030043c00c410749600c4010005405003160710b03001400c803020b1040002c0d100005400449130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 111993003 1250 111991753 111991771
    0xd05030a1d040203090709020c030706092012031213120909050c28020109021302070c06030b060d05040606050a0e010305190f08030901020f03010b0d061a040e090c030a0506 76
    0x300003580002c00c03043e80810f851000d02600041c0040240c407600d40d004004040d00780c4140c0b420f0215907190f2004a0b20800c10a40b04000782d00d00040a0310608000100c0c0ca00003101c50f030280002c850025940c90040b02559586c450b624004114540c102103014203c90354441807400811170740c1c0000070300e405618490030307400783d04010119820050003000e50b0940900d84040d002424009041c081c841070880e01000b047d075684103020000350b01d6800000700b5840e400c0901513540c000170728004241c0801988070a007003514025807035030365945440464200450020011825480e2818004020049a8441030303001c070a03420001101d041e81e58142d4100d0b40134009481081500b030410074501c4000081c0108800d010400e40c60001b0300c401e01850b000052000018100b5980c090101d0f40c540c006e8001290040002c0b40816107070b0b485028500c00f801d80788501c0a81f038440860740d541240114010054801d0075031340001c011304010408408045001002c48140e0b0119061950f00d80b0703011385074458 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 111994253 1250 111993003 111993047
    0x80a090803041208101d10080303130309090501050a09090240050c0927010b07060510061b0503070501090c150507080a110c1305090d090f05040b0d05030a 68
    0x1d03000e4014121801100c0c0380c2c0c0c452421000c10340d0701c5860800c2c00207003a44100480880301185e0a4810270285208445100c450003001256090142141181d6440003000c941000014001138603100400f0302103410109020404414510004005001c402d80b04481c3c800e156407419082110794061003104400e00d078060515a00200f10103003a40d0342120b8170889030008020000700d9003040c0c0303034451030f01034582c20000030382440c81c941c1c012900081e800503840b2000840c50030240042c510a06820030303401580700d0f04071442c100c0042c050003176210907010410900101202441014011503030040e52060003004140c0ca00d00d0b120203070f4401401041400d000d06200007801e20b01620403610090b4012400601381800b0301000c8130600c180400392100ca008542910f5815281d560780c4000b11066208003003000e141c01200d0501e00544010701104110080d881045000301c034000c200c0c00c5e20700a84006c24180d400c100814051031503030744000c0840c4000981604203aa200a58090034040c0c40c410314 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 111995503 1250 111994253 111994261
    0x9060105011107030b01120c08120d060602030a090506090f030703060e010b011d0d0204061205011b0323060a0e15030705010c0503090907110f03130b0a0f080a090803041208 76
    0x1541e4100b41d001c001d014017101c41c01444445a99078510075100c2c401c4001000c042d4480e040036092941880c181c0b0704040012420350b00d520680e0040f10054280d034070041d410300c2d507541001801c094892242c0c40c00341d14000740752540c07525070601019007003102030104e030005a52442c003000200b41c103074142803140d46406140c6070250303c0f40e00308c055103200816200c0046940c0000700528801807107804c0742d01c55911040041c1c00403070301141e10075141c00b034800007640303d041003a20515080071081c0340c42014a0079001d840700319041900300d0034040340e503041001255103800110f43c408155421140320022060300700282e0280400c14103070140f04c00e03402d032066a5a20f400540e1884018071000704a5002031105a12a0500040443e132007040391400012b62443d10103500e052444481c0c5a03030fa5604006030954007a41c81c109100001c200c1d103203165207006507640c0c0080c140c0041406079420015800e011442101060b0402d5402c0c5411900ca65900e05042c5030000840400e20b4842c2d000c510140009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 111996753 1250 111995503 111995537
    0xa1502030903040918020d0609030905040e03040303080c0405030703050703030306050f0607060506010c020618180402090c0a0201060306021803101a0112021309052e1701020702090906010501 84
    0x2990148144a00440c1018141071407180034180480404c581c01c1c6000d50300c800565240c2e0301c11f44410740a03140c00500e0380c141d81002000814030fa08024092801c091a071004400004120740869801d0705d00350a0701d4035444c55040d0148619404294140302d5010302205100010403044100c030700c291401c0002954550034040103250861034181d0200c42405120080343d0076800584e40404149402c607810412640000c2294111010810000034042380140140c14000400c4422031311641400c0140d10f8290b000801c14400246010307009100070406c048030034002d401200185074000002c1d52620840401c108941c84540e24483c46480b510796024200c9a0038403032030b800c600c2821511908007900d50015a141c0300380403a02c031211070342004000c88061800ca0306502a0a80c10400325031814000720710340e40d0500b03180408150700c02040c4c0188040142000e0401190101d040c000c201d0506503481d140280519a03000c1d410940c0401080b004440104074a810785e1000d898060303020b2800d07019 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 111998003 1250 111996753 111996757
    0x330a050f06010309050c030a031e020105090307020d021203041d0705070507030b060d06060e010305010c050f0412030c0f0b0a0f020f0d0f020c15040b0a050609041104021b0a1502 78
    0x64030380500403000858829403103038100f035000602036011907246850040100b03182945014081e00000d25014110011a04a0713145028416244c4001c0c0715a051400515407207108460b13000740308006010003078045407190344085072650403403005c0e251100c0d6a01c1680c0305006841c101000755103c0704000466642c0035070262004250460010304541e411035403280c90303401010f09140d030311054003040e00002646a010b440d001d40142001501c0325499440c1050948004009d1101441014800480007244c0358042e42c08491040780c00c07804500140c1010b440880e013003803000d0300c08001c5003401014013400d1061076008125040302044280940c1c0202000c0380613035003407200c114000300071060180c055604035041c51031413120014901502143c0140c80e00442c034180e807401c0034410b0304101c18007840d0f02a05a001c9c00300c030001c0c045881c3c000001446908010700041c104000d002c00c180440d262a0305940344801c9031440303c4e0a404c46c000d15140e54031209481201d500c00b01065480c405441030007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 111999253 1250 111998003 111998011
    0x2071a010303020607030509010f061403011103061c030e040227060f0a0e1c0b07021002040e0c0c0a080c1b120706110f07031101080a060b1b330a05 65
    0x20150641780c0312400220041c10313018200e00c180799215981c07820012074a220710300041005c40715584100e41a4018142903c2d006400011f80e007109104024050700c4880c03c40385200611080304604c1000d610b0140c07a040100c40c03132250030910100d0b420304000081141680d0080b40c2c50b0600140c88031000070041d80d84100901244059010b005208440380608000d132907244004207400b42883c8034000039008000c0c202820b5519000400600103901d406000e02910302c00c00c40410f51405040079031450441c000a0520a000b03800082d00303074030901040c88040c2000d03900202041e6208400000240e43c2d800c508800c4032480c800b442d4007569480c19020313420401c20f0b03160140c0003075840c0a1094a00d403070103034455240c41c040c1d40c41c031410a50f030a2042c90061440380c20f10f44504001d10000400c5620028480203a0501e040411f10488000c20103a9211807010803200440ca03c03e2120203003400000b96000100c400ba20850000e070030038032030780401200002241040c095580130407503070645805031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 112000503 1250 111999253 111999257
    0x30606060a0f030b060c070608090309060909060f30060919170307200d020a170702130515012607110d030903030b03120d0e0c0a0902071a010303 64
    0x81d07202418010100010080440c0c00c001a1035010300001c9041a0311000d0340c1c6400b9001030b0b005000b02030b0001201d54014400c8002581402d0991002c50428803030441c03214421020100002d6641c2c6e502c1021680501c0060a440c0860808000e903c407643c502c0545504800c2005071141940380000580c4c40c0701d40000402001060010120000c2c04c41c00c03c2401d4885c0c0e90310045610070304441c180118000ca8259680e8590300061948140c100b5200c01c41c043c0c15504040a2232031200c0d0300056410045410103c522407902ca040407404051061b02402034011108035209149016540e204511a0000105000c0022044801110402c041c072444905248005248170880003010703202e50b0303200c0098142006a0f412040a45151200c0040540d0009450b0f108060800d42e06000314070384114203030010410b0f00520b04412181780160140018038556a0a11042061081101d02c2c1e9080014103034901040d00c5003180b5000c2d41c44200300303403801c001c19890f0010b21040414910b040700e03055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 112001753 1250 112000503 112000507
    0x1020111091003020403080310050301060605030105030312071b060e06010b09030d0807210b01090b040f0b13050406030302030318060705030f1e1e0115051902030c07140f03060606 79
    0x50020407103906082d45502e01019030034080440014004802540503500700051040101d10b801d040500303403076040d046603003004814801003246403400000d03a95076100c0026541403995640d80c0c11a04010796000d20301d006001800c0d00741c240005540802c0018231540d0994070207a8a80c50304111900c109100d0310b815600007503030b400c40248a940310f035802c800e451a180e0050a00b802400200030341c03000180c00720f140d403140d4201c003540c3c210400030700410030000e0a038201850601800f4903021548100d120100c0009007a40421000c080040090500140104541a12402c1c02956504101ca030203850009030300501e21004030004086201d50402d6498a141da510f61509882c00140604034010242d03260081008000c502240b44d445441803018030240096088418040070f241070380000307490f4a08814042c0043d50000071030f0242c0e0300040503541400d010803c224518491890500c505005108011500f00d0b1b00c0446450081c070101e400c800f9425162081684400c41607130801d07804441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 112003003 1250 112001753 112001767
    0x6010903020904110d0606090506120d030b01020a06060e0f0901060f030f0311010f0f0b06070f230709020306040c020303060306010303082a0d062106020d06150f02060601020111 78
    0x71400b19107502c42d214800180748041d00402190f044500c0d11004c4076419224607041c8540c40b424030a4a03406501124000c11a002d11200c81e500c9403417480b401c1e0205622003200c114540d00030000f40610543c0302c4030400145a40d007608226540e01643d42c00d402401280c0420845c1e001400303038200303446002201c5150949103981d2140d080c141e46c003080b400c0c00010401100040030a00c91110070107940c1c4000315008003451301c0d9100320354458010a00c2890203000e400080390348485141d5070503a000c0c0c00c000d01209041141000c801e10030300e1900051299990104503825550045c40c0620b0090b5800d001441c4900c1c401da071240801c80c0e00c580c01d54800c1c130040021074811044541c1124003003000303581e906202c031750b20649428001440100d03030f00005110a5031214a1184000030020655422020080c5c00d580c1d16211f155080064205600482c90580400701c0d648960001d0125681c1005002046a40540300d0003d0340d1101015001e0312001542c03650041c080e400b65418038940c42494401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 112004253 1250 112003003 112003009
    0x1801080408030a0b0a090213380d2c12030702190305090d0c03140319030519050412080f1009150b030709030606080a0f060b010e0303131d0601090302 66
    0x44c40c008025802648a00300140490140c030080c580d06401c10b002900450809800405668405040010f09142c3e0700480c214188111050201021864645036503000425a9100500745026110b8000d07001c500c1811500e88082220611006c502c00a0700c00380030a80005034200c2c00220b816601503000111b50b50014400b03554480c2602c0e110317050aa0500c1d1020001c50030204143c2c00071552560144801d109000c240c00400000000b5400114580032400d0104901009119164810300d0340b940041540511400410000d6060035082000585410304003a4034903010b8100441c081000d00b00420b80c0d0084019075030340701d036045095034402e0600d0300d00800c00425090b40224207800c101000402c4280d032080003140552500da0751018110300310b00303220044540e564000b050035441000b03d17900080d1b0103094614400d410440c0080e42c44800001a034540b01042d5520380d02d07000010310004107001004405050b240d054017403c0a4003103805080c003900c04151452408102e004804000610b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 112005503 1250 112004253 112004261
    0x30c0504050f03151006080105030c0109180b0409150506010305010f050d14030a020105011a0702030d050c010b040501230f06070204230103050a031106070801090c0201020c121801080408030a 84
    0x2c4000c1d00311071128004003000e42c039110050703e40016401101d41c0810401d54040074090150030101d010f840502c05580000e000b450062040301e0780c01202622290114901c1c0c0c2c88000082030290080c0110561803074101d50b2600071500400c092460440807603105e51003845160b059982118a40314840c0c20601013000d44036882100311000c0c24440020580b007141400a804403c4a9800100c0c5035410100035040d45c0d00e006a220845080512450002da035002400241c00b03542c4d8209255260300307071503865000d08400003038190054140000022040c03031803030320464445d503050540c600ca03241d80c03820400000c0c0351b802e245074420428408580546001e50000c9840d00e025410590300300144040942e00041c02da01c1070303d56070040c0162000303040d04100544210b26026014100da85040c5001a142e40e0301806000310321581d031000d81c50014000d40c100c0d041d00070100c04486100c3e6540d52500708582c442001d501c80f40007500c1c840d440035409219014007c82c3d114280c14256907412164800070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 112006753 1250 112005503 112005529
    0x7020a0b0318190b1b0d111603080a18110405090307050604080c0114160c0318030c03060608011107030309110d06020a0e010e01090e100302120601090507030c050405 73
    0xc002e11070554115804100014960102040c07910444100703d0300b4001074145000701451151000e50440c11030a0003c0c804840c0c10b07950100300024544a0030044800c603001d6844151018420b10011001307054000094610030881044203001c100a80502d0503168881604001d04120951003a0041d81c03600f80c200580c007000b94412603042c0b41003a00d070146051800e0b6026140504000b444a043d03020a008444070f5071400142c0c0012404c298810308032001d148140303c0e003040080507250041520032100400450300415494087d591242009481c425451000b120302134038246002518403010f01801c1da6070b00e60044114181070940d00d0903006800000300071034a81000703103006000d075034882011004450040030016141c3c41d0110000c1d110000c103d1001c1d06000c0d01915003113150b81c0c8075820000b41d5a41d03841c802100d4a400604840591903504002d41c0a004410200419000000d03440e0403140c00040501c510340b03074407900764106c0d40b80f811440000b0340200028811428031a40501403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 112008003 1250 112006753 112006771
    0x31e020d0f0504030c11010203030f06010804030201060e01230a03050a1e05061602210a0c0602040503010504120f1b02150702030d02030406020d020f0601031b080a03030504060c030207020a0b03 85
    0x41d00c0d80200c0c455040350003c5500300c02180340d001c404014040c0000d034002889200780025480c604200443c11243e0400616141c104041c0c0030004040501c00c0d08600021709403144e0100e600d50712040030340452442600c0e080b03107400428103100b44924000c00d0103c12660850040c1c00089581d444400c0d0000c800402d00084400a507505400100b00708079113442241000104052510701c028020306020074104805000354075484150452070209046441b03640e55418045240301741c03071130080007134090742d07200039890f500c2c0204200c1404a5a03200047c60f48450b0340f2500910110360082c0e031200144031031000c034810030720100001800c20b01d0030000b042d040304030351a04000070b03540060721f881c0c50000c2d0328005810100b0708011b0a90100103002d06003030705001030043d812a02c844039594643c1440082d1180000740800d0a0400d0080d550f80d024201d0002641c505172098200138015101c02d540840303040c1e14103088082400d10a00c00e4a50301540100f80780b800354034000061000340c02c09001444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 112009253 1250 112008003 112008011
    0x60d0203031b01020a140711040e1501140109060906020a1e02030604140c0a060c120c020303130e0a0203041212110d0f0c0302090d0b0421051306031e020d 68
    0x142c502c200c0002000c4103420001517074800404000a003052a40800c052a18801380714040000b4001c0c2001d400701c01d0f00b924005008541e0b240200d25114181c91800d000807003043c00801c102c6000700c80d60401c10400e0304c465000c0341c0e4602048607840d0080c8142401a00214180710002c0c910f90b1010b1000100035144019211035a0002400c2100c1070781c003143c40c0100003962010030302090004d0101818200e40301d8812034039001000c1c020a41c0c2c0c18000300f01c45220602c503809240252400650940c018080341c2e00d0318800c01032501840d009015403503d808155000400041244c001c880c451a403050007089a56480c020035610741040c2c91802050540300d010807007106908002412210300519004640c08245001e2102141c030500003440800d40100841d81e4036440e03a00d004c03406a036000040758801e0391036007000c5500755440e850210300401103103216084143d004000c0c2043d00c1c2258003540e813260f940c0000341e04a900103000c01441c0300e601c80c070764100d981d4954090000180c810350085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 112010503 1250 112009253 112009267
    0x1021c0302041706090f0c0d060504020a09020301031b090501050a030f03020c040c030b0405010b0315060c0309031b090f0f0a0b0a0902040608040b0c040806061c1a06030f0106030b060d020303 84
    0xf00603909100c03c072600f9070303005004005000c00700704051815803c101024010514418000c100846070a09014080f203480341d010a0864a41c00c011100620306000d04644a5840307180c6907801d0046580070f10310345840900d01140010191088078100c40004003800303801451035540f80980c004442081d402d5020b007010b18980380d1110f0141240b860f40f0781d6000900020101d04000031204103800582142006008108180d4000f4081d66843c00b0b0842d0140d481e8110100c0305890342c0300382e04005405000e0066201e840102d1949807403040360046802d0b00e9242d0f1101c3c0c044009000031641c0341c490f2000203011620f00f52807507000c040181400791807640c5048e00e4070312a4044e640540c0c400740005140c141040103110107400300c241c120840c24a001e01e058908180e6a9503400060003061046800b569031403402c1c00d414055844480c1c0c0b00304080240ca000a04112403964200c0c1c0e058003a008030f071070075614100e0610800c0c09a1ba0b00141c03900841d150b18080c45018000f0307440c103c0e01031008001d24 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 112011753 1250 112010503 112010519
    0x309090c090415090e030f04051216031514040b07080924070305010e071202090d14070f0812070b060307080a06050105010f0c020f10050d060f03020405060105040501021c030204 78
    0x191080e0b403410503da00744078a098020002c490310500c0d5154690402c0c0113040e400c98925044400700c0784219005521f40407101802420010035400414181040b060000104540c0321f411406000355040f08100c7e11a55481c081d810350300c01c5030000d220501d00ca000650560103003039030b43d810940070001c0311503420304e000001030140011905c001940543d20104a14a645809090b015000100403081181041c54010740803111142000031503d40205c0c1e040303496120080e2080c0c407a504a0540040c1503410b40d0960741b0b5954030b01039501d03810b0601c100410700c44400289003210600c14440140b030603000d41c4401c070b5440009010f555150040420019100908100b404207950143d50f0000d0954174110000d49140000b604940c2031040c0980401e016030381c2c05030b081d00d05c04410384c0d5000c9181c100c200110742c14454900d02c20a03152070440c0104070061004404015a40b003620b0030007240e2600001510a070180b48289401a8805118004071903180c40900200c1100d60170094102a203800e02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 112013003 1250 112011753 112011761
    0x20f1e0411040521160302010c06090615030602090316050d02040b0301020d1b0e030d0f110a0804060309020a05040b0901060c03020a0203060106030b0108070908030306010e0f1c020111010e0309090c0904 89
    0x51030104d0700e80e01620610520074400000088000040c01c4481440d503400170300740341c280c600054449942c92082c4024011180c010300a054041c2d1081080d898603494800300a4002984c00c80c0248039115205201759644c208140a03a10010300c2003407100221b508100250080c001d010f40c05540074801003180440074040c184000b614030032a000880321030303e80284628182c0b00001e110341e0100312059140c6402c01c820641681043c500000624180c4460601d0a00d051034021b107104400900051003940c141c1c4511406c0d803080301c181e01980e586804200c191f40b040c200c01c030b43c03007410b01004104030740c007891142c00306030b1207401a5805c1d01c19540000e400c1090980c007100109499004c004017940c0d00c0301110b980311010f410103100190401c00f100e9070f40c3c00300030b100c9418040c106203412600da5944401c6404503400601c016015800b43c117000120010300c02c800ca000c176464041750747c545007040c080c801801070424021810800c001041000000002e45140c00c400c1c81000000450f0f111409 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 112014253 1250 112013003 112013029
    0x30603020303030c07021008130b15120f07080105151219110108090303090c09070e03070b0a090b070f06020a03090203010504120210091e0c080d0309020f1e04110405 73
    0x1d131140d03c3d000c042c018400d011804524030f01c02c02050b6001c01c0035195840500e5009550000340594040c7c0e035803e070000308091078040165000c000110040c03500480011016950500c21069038040f994030441a4241c0e0800d480401c2840c0c42041c85035880e003801503140110364071001c00c40c0c0c030121000041044400440400b44c801340a08908003d0b00e58108205940000404006614629141006c152541046003115202d494080041500e15105a041202501e8018151503190741d0350701024146a00c00c4000d440810034a03440041c81d91043c0007a24000c64000280025401c92070343d48000a42c410700d06041403541d241a013a000d41c409205a82c4540e21402003130000380d00e0040040e150080360500d403c03080d0f090510b0140000c070600005048554211030040801c092480c05920594054000d2101445000c940010301681034220000740c03802525040c076031907205800d0100480440c0300f5440f110701b2207854460103042170b60020100c00c46003521541400c0e21000001d40f0700c01503903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 112015503 1250 112014253 112014271
    0x702120409140708070e09180102160c060801180509012705010b0402190804060b03060915010b0f03070c0c030602040807060e0405060a0e19090b07030c0216120303060302030303 78
    0x44503800e04080341d0000981c100d4810b042190713a500d40f11000a000344590301c2c0d418000c1140c4004550b024103840e2003c0c0070f0a000e54000d41d140c0108602851105121400c155140c90342c4150005e415400b07114158145e84180c08584494100c0540c0f030400380c200501844c40c10340d070380d00400301c821039408250351890a9503d220b208900190400d01d00f5034003802032013489641b04001c0d100484402c0d442075646194a410403201a81d201c0c05c0c1500100182c80b1000e800d030007024200705842d070003ca14904c0c0c8143c0010b0042803641c07108140e45030384c0a1940004090b48042001c541594001c1c40c0040d54030744685800440551659660000da80003544040550f5001170307010300800d500400c4103812810265010009807401800048214a03648540044041101d000c03441000c03090210241c4410f200c3c0d41440844500e203000c5101c400e040b1200e0000904d05504442d8a51010800450904c500707920b0380c01150030076810705101e20520800710181a5503620020068070700f8409148505001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 112016753 1250 112015503 112015511
    0x50c03070b0a020105091c0f0c0b15090f06060403022b06050109060602031e09011e02030702010e0d170906041701090611040608011404060b0c100e0a0201020c090702120409 76
    0x2c40030190948202800b07108080d00084020700b0030300e19016010020100918001d017450391014400c0d145901014000f401e2a050101000800300700e02c0140c13501031034261262059070fa14541d415650000940310300f94800403c00c8200003501c2c1182c0c4050903c02c0300c0d50907079401800446050000c3d000d11744200c9046440340d0040140500f14890300c00208858005986031110004881c6580041d01e440c1c00c40c40308010a00c4a5280d21640b40040410f80c4c1055a60b011071316514042e50303942140c50200d002900f22404001e140c240040c0123401540d1141c00303030810010f01e1208803819042543c6a070740140c0103001c0001d0307141c045007a00003080f241d04000100e1624504061065465201019683d0345c000c1008116103607000310460b0455413141501c000f0b0122136000507000e0105940a00d0000c0c502144074142e460010a19064007407542c50201b0991200811107034541d41c403000064050b03003040c0c0c00c003100c0b41014045550b100e001441910a44080b070f6494401d65009608442d1100d80c3d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 112018003 1250 112016753 112016767
    0xa0503030c0c011b022d060f04090c030b060d0b0402091903020a06080f01140105040504060b0a0801150f030203090102130b0d050903090a05040c170c0702090114010f0804050c03070b 80
    0x468011001ca00c0845143e000042e40105d2409912961b2004401c40b0b080c02c0032400001c0b1b43c100021080b80100000d0f0348244030011110150403074000d050ba007500c0d14031481c0d10507002c0e102d0000403203005008907080c000039817294001800c17564400360708540c0030442c0000b5a03035200d00b008807070a0b0451000340c0d800d0550050002c00c402d181c11020500c004030047c410910380d8080c3d81411600c0040300e03800c16010300c10040300c540c05282e10007504241010340c04960b03056808040c0c11116500e9958031102d81ea201310301c64146000754803c002103140d40302b040041c1032003900110f9000394548005403506140030030b0040c02e92026231090010603008105003900705082d006843d0001140402541403500718030025440452a1207554440d581c7d030981300441c2e0f03000340451510341000500a030143d00c2c02005015036940140c0040b403048074241c0000c16998a41d611f64504081c040c0d41c0d0002c2026013850540300d10002034003d071100d1182440c1541c07599020002e00010701002d103800303910f07048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 112019253 1250 112018003 112018007
    0x130203011d090606030307020d0f080318102904180305030103051002040501140a17070f020c06030c0d0e030d02181804050c040c03060b040b0403030e0303071a04020a0503030c0c01 79
    0x9010b006100103412100c00d0045956001050320036581d0125038048500032945012501c018080d407006286a80100401c0758600614240420703d450801c25a50101c45010341d0b2011a4581c00361988008601c4481c800c00c3c0e015242c98034070501e030142000843d818160081e21401d0740144007180041e03130000c014070400100348810000341c29a004254103103030030400084c1c420507102d049000001c001044030140c051050000c034100100300310f5420031074104040003e00c1d801c4407801c0000580b0882d508100300e0300f80030b011241706062284203e8100510328407940c01628001d5403081480c8824494070001603910f00c000c00e0204110328030010502e40c903000307008958201c44000200075036850100310101d600486c1c102142c0390b084500082117681c08074250010001c1d5001042d101c0c00c00325000c00c83d07225200052040ea800b903200c0080040045080680e6845000c10050030050395a2021521842e0100d489400c00c5c8010498594162200c000c42c0c550380200034024103503131010243d80c0140d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 112020503 1250 112019253 112019309
    0xf090c0504200702011202070818030d090305030d0b011701080d0806090603192102070306060902041a1e0706090b010e0603030703050d06080303070c050d0507030e04050613020301 79
    0x3840210015a0465a002d003404078000ea400182c103101441101354543c841550480d00816031141010703882e4410070003406000040547c0580c0a4400ea02c0d41c042c019018440c0001102d0b44240190301d08498440c010019051070034500c1d040c840c43c0181205c89500f501d001d140a803440c0002003000002c42a40108140c0c0c0141819018140d24418492a6100458440c03400b500040d1f1480c8601c040d0700c1c1a40035150f01c00c50b4143c40d900505101c5454980c0814030600302da02450051001c45d441d0880c0408900c51407064400e2803801c04035054584440402a280940005003200750281c0461006e2855070700041c000c83e1480c0d40d88550b4001c2028040b5100c2c01b401c0e002030100708502e4110040380c1c3e2489200c40290500601082d030b28850b4509420100141102005490300c0703080c190300c054902c42c1104002c6074240994000d40c1c01c0705218005440d052a0107565000b044040c0364240701c01014050071494111400b010f4240e010319203800210300900309010024186d12813001e04000714 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 112021753 1250 112020503 112020521
    0x915052e0e0a211e0516080601060c05070e0a0b10020f030d0f091202011b030507051603050c01091b06030501030c0302190905040c1a090a06080603010f090c0504 71
    0x1111050008035940c0e207400100000340c55050f0703841d01c04808041c42d030041070500840c3c000e002c0005420003562040040c0b50009440380b10b0b908a4100144241020300280300394003034904194072903001008218030403e85d06545c14002d02c04e98102a44440c8509a0359104541e609112030722250780d0415400e108a07041d148526620180c0300741080d44400c03641340c0c4120f80c01001042d40742c0c2d81440d080301c0b80f41d0122440035404410041071244089029010300003551501c2151a01c10380076200c66400380c01018800c05141e55181c2c513148103409080a484c00241040d82000000d1003d60100c00d000d2064404440c0a20b00d0000480c002400c1ca484412868125400b0036060400410024070070051b0441a00c2d8110380d807000c1d242030900751b0b0f0000826a8805500340381803200b0312003400080c0301c030442565110309500e4101410000304103240d110f40c001c40d0b0341206501c0d5003080554490342d640394200000500101f000542c035000541501d0040d502a9002101d13000300700100d10b002c0c03245106c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 112023003 1250 112021753 112021757
    0x60501060201061a120a05060301060503150105091f03020d140f0616050f0304060f020f070c05130203060906010315081e010c09030302030703030902010e0a03080306010e090603070915052e 83
    0x203400c4421000342c080f440c0190043c1b8400d501c2d44081801035030290000d401414011b411602e600f0000c07019420111002c1c82064012403ca002250031005119207050888900040303800c809440d56003072081c006030300e40c001c0c0e0303807519000b2100c00303904418408181241f0980e8002c0006040400c3c00c5800c280301c80c0d030f42d1000d01030100844044004c0300e0f02501c0d81709400c808001030451070074803003002038411405900713401800000c8071002c02a440030070360f0590381d054880302c40074000f4000a0f01288004d0321000d42c099400e200081296100341c02240c0811681260429140e030754803001c5185c444401c025000c58104200d1070010b00e1002d20880881245a00c0d28022031442c588001e5100d10401c14003070105070b1200c40c0c400559000300210803e0300c03006850208010ba032402d1280050300207450003030001d80c0c0541280080e1a111281034017900000340034110f040d1412001ca0018050040c0c0100c3d021034861001813140c0c1d44032a071044008858149a60084040d0450f2070203041401c001c0003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 112024253 1250 112023003 112023007
    0x4050a15030b0f0f010507050a08031603180305090609150c030c010b0d0b0103080c15071e030603020f0613030206122205150601051c0213050d021503060d060501060201061a 76
    0x11030307a50f0380c54211341110800e0801d1650783c442814041d00b05240c1c0603024080c1900001805195480544540705145540e0340400503810b18641c41c0c4500014801d003d80020801e200d9503090b031074001c006001040005240d0140d4441c181c109180503088031075903103415000881c803100002001e00600710450b070700303c56405001200d80c0d501d00c0040300c1800b0250a443c0f020400b80c003941802c0091394400d4400b10b440031100d18051000900200429004441400e40d907032045142c42d00034060b100c00c1c0c940c010520140c1412442c24000b480e00158101d11048545081c00801b5071a04001083c995002005412251603d460820f41400d01c0e61001e400240d1800204d1011400c00b0480510800388821440d41948601c40101c5003402513001c481200b11040507401007203400c0742d0040c144549140c251100d055034030010050998007512010750070840c1c5442099681c403610000b198040e40040a140c3c0e503217040c0d121305013140c20981040c40541e650700c1007400000000004180fa15802c1c1c8800341c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 112025503 1250 112024253 112024279
    0xa1d1609020c030d0903020a0b01080d1e0e1c2906010504230103090b0a090c0605040501170a020f031306180f032a0b1911070f0804050a15030b 63
    0x2e5543d2180d02484c5803040d0355410003c0c20548203225031a08180c00080d11070b06961209901c3c0e483e64074480801006c10540780b464209a4051000990000025202c0003c002e4946043c4110140c2a1601c2d4030070f40710354018440044c8030680d003e00c0d488540c0c0d502d840048220070070408080c4014040905124090104022510f0403001c0c2040382500402c0d05480d50740e0960040e0041e01240030010305a41e109004c001d41c2e541d803603101a400ba4010a1030f109056510f80054405201c0d41c0070f59400150016900ea01e41c14400d4481a00081c03080f00043c50701000d141510201c0c0c00580b40e001100745100d02c8042884121f000b01103516685070024203003903201d0f603074043c104503103900c0040610500d95000c0554200020203200035512140d07a1032200491840c14104040080341e0788402d618040340c803a05203007814452103d0007288101003034503044064135205501681003200300c40c601420170012400380c4810002100030300c0d0303a200801030542c0e042d80240c16589a034203050300865400c0402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 112026753 1250 112025503 112025527
    0x3070504110304080d020415080f01060e030307080f09030109050708010606020105011d0402010c1514090c063403030225081c0b0405070801030201020607020102210a1d160902 77
    0x181d400070b038402400c580e17891074410f00d60040c0c016a4407528048402e00c582c424055000203100d440344002da8030300c88a030383e02c2d424161440066504166050340c4140a10b60004407803400400071120300040503414030010704d0001e07094403c103000469440c2c000c00c50412000da401d00840303025040a000030f01c802c2d8117140041d46110007440c80e075224600300402040c01e40e40100141c07041d0b05c0d00f001c41c3c030301c102c2d0402410344003406a40c45a02c20640710750000842e200d00125004080c4480100700d1883c0c0400d0080b01542c24044011848212440344403904080c5941000003611034800d4402584402021000302c1c00040081c0580a100c1442c050300d2000402c031030100c0da902070a81c410303004040c0d0a40580001001403005c019042803504041c403202940112040b81205c4c400d0b42116030a40c0c881c1c03800c07070907401060f503403150158007100709004011104000c141d11103440e14000036952140c560580f01119203c2c014120740e000f20341c50394a2013000300d4015024041e0382c01c0c29468207102c5100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 112028003 1250 112026753 112026757
    0x1e0c0609120201030207031710052706010e1f080a050604091110020109020a0f031415040b04020f04050a0c14041a07061e020c1605031506011e08060307050411 70
    0x8020f041540c002440020140a40c1002580001e80c1ca00016540b5166560803800c09441c0a1740e88100c54089822254181c1e0050a20382c29025442c04a001e0b26204c00541e11480644015a8803885201c000c1c200e90300c0a81004802c0106543d074a661810a581b281088540207001c0a00403810540d0507804070319a54924644624243c0b00d13400708010703400c8102d0040c182c6000095201c3c010361800603400040103030321f43c1a00c0c0290b013022186440c03c1c00055480da04400a80c80010307001c0d0009020445d0044055807060020b09032400100a010004017280c0c400c80380f0700125030707032804881c440035031058840644169000c030080c60035081c0300e0040444a40e070a00401800c0c80010740030204522504a807141121010110000c52101c0340f03543c020313403c402003003149841840c0601050060152000c0c00f2114051b0141210b0a1601c800e8203210300300800c0c803414484400907604400454036003200d6021126501c004407800c014040504000f100d60007107209904004d0140500800401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 112029253 1250 112028003 112028039
    0x603060e0f09070503010e010207060e0c0d1103011b0215060603071205061201020c0307051002130302010807020c0a08010b09090607050406050a0207080a0b041e050304170a1e0c0609 80
    0x21080325036a0012003e14000640c0c0203039815500700442096042c905402501d8494890901440700020403501e8503520045602195440303d11442000c0c04214400c01600b000c8802030004220440d003981d041c040489001441e40069000b1000089450020b020b8a600808100c1e0707601e04d9401c0183c00103080c01001c0c86046030199480e0041445a681e00072407040c00c1d80705400954450401c992103a0b26030b0800320044c0c406000b40020a03160343c3c014400ca80005507070040d03e20204d070940d001140e214400a20003005d500c200c643c0050203544042202008011290020410740b0b1000207112043d10090100c0b100e0f5030001050200d803603017000c266000da500c0c510f4510307140c0c80a05c408910303200465100c80c202d8000c41d10701e5810301a4103d13840c0c0c4658020303840c08983c80aa00003000d05000e0003200501203400601c024070a041000242007030880f520700c111482d0103e55240c084041e14281418224044419801010070809600c2c000003000c0e2405e00720901c41c5481228402061111 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 112030503 1250 112029253 112029271
    0x200103090201020c0f030a12030c0801080706120e03130306020301050a050402030921040b0c160b0c0616110709020307031b0c020f150a080402010212040f05060c07121b0603060e 78
    0x44010585c40c1c40800c62204520740200071031074003280071200a001404610020b1001944040010500f00c4000a07100d00715052070782d52a4000041052400003800c4000e10404180001c02c05906c95402d0702c0c0050010314040c5d0380059403545080300304014000c0c19480f090241c1c0c01071003004210f4202141442c2d440c108500c14602e00001c00300a100325114940040003080004600c9600e01c0400041360703109a41c0c40e200900e40a512540141001d00400c02980865400761002845c011400e030b0201648000508000580e45000201241004203640111003465804801c2046a50303050140c0401001000c4400c1c050304542800107026411410001e40510000080c0300c03213944503d00841e050302102c10403580c07551500380005007181e00039102a0b005108600d000c0d1903c903240411901160407811300802c6103841c140a00411b500321003080001c034014180d00240c14050702e5000c402c0d86216016500c8812030740b495024461829420900c1014548070092048482c51600c0070740000d514 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 112031753 1250 112030503 112030519
    0x30c0703020a0206030c0904200d0e01060b0c0114060117040303090203100504060e0f071404050c07080a020d030609152102030d020a0501050c09010207030305070c030b0103200103090201020c 84
    0x500302070346410a1844025000f0070000700f00010001d051025041c640b104503014000300240740021001c1d81c022801c804007041c010000c50a04010640c40003210ba501c40303001045881d55215a585550000b407800b07452039448200051400181d4915243c0c414000d00300b1240360320801c5c0a000c3e660030024002410b0660b10b000c01429541c0410000440c0081e10006200c140350a241a5000d080400c03403803640362081444140e0044000b068110544850902c2d407066541c602003004017500001e806010601010440c40c40802c500500905451503103400504080303c080c0b00007421941d490784083c0d440c41c50542c080100b152880f01942c221418101c042c11400300031540c151f52101c0d6414020341c184907003060049015000310b402c42c03102c0d00801c004c100d2aa601e003460700c81480703400e0149005811100d0103000182c083c201070540c00e4041d04000001c1c0d80c40f82e40e000d10bc0502070700280d0340c6012503480080309502e00c032505400bd19003880c050003414410380c0082e61355404c1041075407051440b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 112033003 1250 112031753 112031767
    0x403030923060315091608130f05010203040c1509060912140d020d030c03060503060402151c0603060c110c01081302150703170108030d0507051207030b03060106020111030c 76
    0x4440c01d034000800c0d00a1003030340e480c00c104800c03504081441032468010501c81000820300b0b80d40a00f041800c42003600c0b00a62940d80c2401c012080c1c1110800703c561254a4540c2d8010503002d1010314882c034441c01180607224200310700035805000784d0070501c2c108242c205c02800030b1907100c0c4410040740c0e104000c015010a01d03246c8034a00c03440300078080708203100352590780454580c0007401c62450942601c0030400307000e080d10101c00745c031150f0241507016402140401c0041c10451001104181809409410a81c980e0848103401c03108050107000d542e01d400382441480003d214100e106001814404146075410707114030307221044010158188540e50000a07080612414000f413015801004007e42817014544482035810003038040e40001d56039802a000f81c4403190056042e42c1c0c80d0002103003040100f103400c0f4050b0200034410405c000302031002a099030415030401d400303000c0d140c50108000007010241482c00700d059204034110380c146130560000f1410041102e0300580b08545c0d4030b5607500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 112034253 1250 112033003 112033049
    0x1c0c06021804020d05040303050c040b0f031305071517042303090d06060e0c1606050a02190806100206100302010c050114130b0703090305030a090303060e0c0a0207050604030309 78
    0x1254034110b90010700020b801c1c0c6040710720340e01a0340319074400e89040056499240085159000c1e50040c2c0c4041d00080014610302014803014550203001c0c41d041c546500d08550384d10313044c46540c2c1c1c030640503580c8034004103003859000620314103a91940c982c4031850f481e043c0c8a03001d00f903008001c4400007508401107554510710074003c555101002603d500e015a58501e0100e008100e00c1c0f02c0c8161440c0071002007003039a20040125005d0901025003c05030405c140c4070b910042401038410507005a00700641e0090305649c3c122482060300781d445448070342c90510240a0b03180d10b080650780031502310404003c800c01814007498262038080c60064099030f11031031301c5401440b43c01d000800ca0362a4a0400299080c5410032941d041c0c401c030300c0b641c55611180c0040d02500c014140c002c000c00c0003071000170074112695001c1c0c035003140031340b40103e125940c0d401c81c14605401514541e0800b4800641c0d0b55074690104000d0000384020b0f00d84925003499510000c2640700c0b01e0003004400041c0341202647c0c4e113 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 112035503 1250 112034253 112034287
    0x5160318021f080a0207030504030201050a111501030303051003120c020312040e07020d08100e090c040e010209031618020c1e0c0a060c150c05210106021c0c0602 71
    0x2039001d0a031128080c0340e0709146415044210245001a107a50f0010341e00440c64000d0302c29172585501c03481d0800d42154010760390780c3c1120390504100400d00000c1107018400f00410500c1c0201143c0001e040d50550070000c040e181c00400031040d24428603010800611138210780841d0300110301c1d104820b80405e200281c205900310403e01100c0c40d01050114940c46c902c81c00b039000718103540031120314608500064500d81c008440215080d42510300811648190f2807038030358024640b4040da0a2a03000000140456140300038010550b0750200310905941000c0007400c6540c080c803902858540d180c00070603003121081c5c4000f03810300c5401044119a40d081040341e04600495000740441840c3c4c01c000da141c1e20701d1110030042c461100e004001500b00d0080c80c90b1880d05070025031000650002400a801500f400075440042160070007554081f5881d4a10141d02c80c1c1a00442c1c00349540360041c02031519142c44103501e05482844100302c07005030014044000c280e4000300240e11591080c1c0c0403400a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 112036753 1250 112035503 112035551
    0x1e052704090b010906050a12050303010501030c050712020607110106080303060d0c031a16030b100c111003090b06030c1e0a050607050609010518120f070204240603051603 75
    0x82280440081052422178000354261003040d11032280c8035540e403000c071580c1585c490019200f900300300b00502c015442604222841d01c41c60900f5032920410360b490f8079084800c00d0100300142c1054080c0000540c1c05401300c4042d1315000000d012240c00c0c0300340c1c00c0e1039120191545210f41d041548100c20400c800802e4070045d43c202030480704401024444001c40171040711030b10180070f42c41551400d01402442440350304c940c054000c444040300c0f24000d81e07901901440c1a03841001070000307851180c1d0364101508128005d9980480e0f551200e02c1d001c5100386015181502c00e801010381070ba21038881c084885846580905150359003400c0c0d02c080b54181c61240c01c01d03500180001501000c0c404001402c41c080c1400e403001304a40da4640c4240392403800c4081402140303810411901d040c00712444040d00c488000460313014a84007032580020102c034401008400c0200104245e003012403000c0c00340400070425800e00340032902c0d00702541c0d82280020b00082e0185982c544500943c021203c16024070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 112038003 1250 112036753 112036763
    0x5070f05010905030403031205010320041b030e0717030307050f07050607050a0206070804020f01050a090b071109010b040303140706140a0209042403121b031e05270409 74
    0x501c2c1e545050481d12540980015804260f80700204480c1103014440c0b24120707078101401412a040015081c0b00703c1304001a1550b00c5912a40c103009080188082042445015100010111003c002c1541082c0707071035204040144080000c0720b4180400b00c12a90700c62100c1ca4115030b0350488031034001c818041e40c9406407403441000204032103542c210005100c0040d40c0d03001c83c3c3d102d55034107504403aa0001110029040855400300460550007003000e02446112802d04418441d1140c0c10180c0c1600452401d490409200701c401040b414201d00c4a409000d865107a58a0141581c034040c0000007103074035203040b000c2c0020b0500f0920409500c15842c03841c487e0504420307070402201070340c00f075004000001d204600e01900342c001468034041d007010b030100401d24401494a1522202030f800400380718801805848841d5140440c00130711105889403207601caa03589804100710700c6103030003081144501406010440f01542d1b80c501d092802c2189540c0c085c3d2106c0500013004640501003140000788 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 112039253 1250 112038003 112038011
    0x504050703031e021b010302040302031f11190509010903020303070c05033a11060f0108070b03040f06050402041d010608060c27030a020d0602090103060503070803040605070f0501 79
    0x1086808104035044a000707a480028110f0180300ca407860315026400d440250340801c0080c105e00c0c0e0407001c07070b0341813100504006003040d6898011a09011495202404d001c186020061104130a80701e10101038044224403410201400d5554041102c520045c3c400c0c400c011170b600503207a10580520001d1903003d801e4a0315a01c81e494440003113019405014070900449134607400342c00a103907001da41812040560745a003000700301403000c40d640f004410020840d003002184401c250401c0001d0140281650f044165850705800c94100700303d07038000403005042041484049144030003480f01031500540700140a0300c40d0302c0040d0040010b15586100e19000c804e200c9602c08040d4840b40455014406903045665805c0d60b05106105500e003003400140c4480c14001001903880040205240c05021100007032040c1e0000f41b107000b1440003c1f030b105030300059998025641402074400400040d4014201c1c903060209540d2240a18060481040b03404150a81417110003944113103100d0708100200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 112040503 1250 112039253 112039261
    0xc060f0c02060a0c02010b0d020603040f0f030507060c080c0301090e0f0d12050f01050d0f0f02090a0203220b0117030d02040e012102100305190c0f022a04090f0605 72
    0x182d100d500494000440600d411080e460090042c0120315003032030300400912540c5019802c0214a070000341056418000002c007000000b51900c00000300d4600a49036151101c0310703031610344160345651202204000000301402441110341c0c090741d0541e82072040c041050300d01801030514250401031100302e24412141c02002480d000703800304165000c80d01042c032117a039808081030f80c3d0303040030300c10a50844c2c506101031010896058109100030710401d56601000c1d4a070f000900c1c8a201030b56495001e50340002848402d030003401802071400182a0181e800d10140d845a01e003940c0c1c140711f00f149980d203036402c29030079174800d00032200311101e410702c01c5403540d4a90640141c0d0880034090990030b03220f404a0740d105001c5404200044540c020885460060900c03400c1703024080140028200b15403070740d2a0003080d00300340a48914284150740c1c050042100b0f00c0c00034644150389440810346400c5140c01906083c140d8107401940303c0039500400c525a032890320004039a042600a8120380c5000c0600c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 112041753 1250 112040503 112040507
    0xe010213030809100302031003110a0f0603050117010516121409010501060206061203090f2b0210180e09030702100207140a150c080405130209100302040806070c060f0c 74
    0x10303169030328084e035207403020b071911910076000ca01c02030724142c142c04400c40c410400544030321a580b04440019082031001651025400c10500441d080600404d44420040c0000fa000c840305c5211000c40030028401820507080c01c1481d00d0b1b80c00742500410404c4090500d10441c1a0400094420740c03403400410361a120342d000d40203000c28002e0340c1c0103020f00da000c90614a00101c02c0b10120302d8030b20141d480e0020034010004117282226000e80c0200507003c00d001e01b48031002c1d40000784203030780803101c203a8145407042001c0c0c8030181c0c0c9244203008401d400c0c91318007803020680d1000d6801c0342044c400e558442c0081c903840c3d0702aa080013940001741400e0401c00c5540402c00d1021910b803015855030340803009003000b031880c07a180034031180e5000c04200703115414800c2603103806081c00740200b946442d8845000c1404484c80040031400c2640018001039181003940300b645460655140031800e09090940c000c1d211800038101804109683d170f8450180016940042c0f540d07016180108040c0c280c117400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 112043003 1250 112041753 112041757
    0x6091b27040c02060c1c0f0203070302071a01210221100c0507020d060b0f0a0f0807140a1701020c0703061a0904170c0c09040507030b010b120a0e0102130308 69
    0x40c081e90038a45815502c90000030380a015050001e2000c0c2001d00f02c441003c541e01c03010b100c4c00905900c5509a09003401d8a1008502995480e42c4c090398802d805c3c141410380f1807814010880306901200100400b040104c030310341d01070036075042640c100c0d04035000141c0c142d0300e6400c421080394441555284000000184d140c0444840c640600c0081841c01040d80c00d4001d0380380107500802565184000201c0560103402103e800500c2c02a6103000d40e00810132004a580145030107060b80d81c004c0c04220020064040102040b411401c3c407480c0600104505407054825022030080d03891041944080a4043c0d440303642c491000c441c42c0c107960303090440180c12454610144030081c40d04d01d0303a89080400f205031103903070030451700155070b02c0c11019800c80e0742c030844c0700707814070300420703152207066910703643c03080d01403401400101202401c40c100311220741c078182c0c000482d80504100940d5612640350f542c981c4007802000000b58201d00d001e44901905c6005008464029803a001008010803800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 112044253 1250 112043003 112043077
    0xb04170706020106031a130b01230405153001051801091a07050c0a0503180d050a120c02041b0f050a0207050607020406030c06020307170306091b 64
    0x81114425a03485009038200d03040380c000604212048a4843ea40c030504009050b0001c5102541400c0c940c0310340c85140c81c1c040c0a811441c0651068007842c036000d4a55400003850790800c550070001030030324400300d07010000c0380c002e0f00d40101024000e8245c2d03461002810303103490041c80040481044800b108900038941211b2188078289820a21003100e001441000c050382e40c04001c0c0412000111400f808140c2c6c01840002041407c100d8602d44500c180151340b0964807460055884030550035404052820b2101e802d80104411100000480c00c001807201d8542c1d0040c00080f5000e452000c00c841071001c004000c0d420a00700481d141510501141c0140641d02c4c0d0b548204032082c0b4a401121103109a000210050340114000e01c924a81700c3e009150300c52008000007800c0c0e2b940c0e5281984070586a0000e000750700003080403002c0c007000541c404d50120001c40945d29500d82000010341d507007805047e200d202200c0035074900b0160650012108080c0d1030000c04400c1880c4461101c240442c00c1c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 112045503 1250 112044253 112044299
    0x403060606020106090b010806042d0605040c050a02030d020a20061509010b0427060f21080d0203132a0e040f0f03030b1e10090b0307050f040b04 64
    0x164001921850900c94800c00d888140c1da1810241c880c0c89c2040040d0204a074a42e08001026000710450982001141c1031500200804180a46050100412107070140c80081c00e0100c01c0005403e0f031503010089980424003e1001610f030b8550171021610b50a52410031a035000300807141c0715190000040300d9108003800c142000300e10302c02c0e00600040c00740078442c0f0030361594140028081c00104100310101c04921040030054038502a080d001641c1003980309001c0aa094501400310010468003190b0303401e40203012a01c405401d0341c581d0414440c650100500641c0400881d2920440c5009444036503000030340303003410038044a5501e619002039918284c05d0f40c074454000901010710300640f446550400c4040f241d6038050348683c090b00a80503c11010140e4407e0329562680e1030740c0b10216400b11440d03190070000803010602540c2480c103690f40040c4010100204044516402282c3d4012002d180003a100c0100041202c4035005d03e40240220000c0400c010807030449007404075107844400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 112046753 1250 112045503 112045511
    0x60b030c0c060714041512110a0807030b0616081b010c030b010e09010b0a090308030109050a0b01020313060e060c0118020a0e040c060c020f0301051303020f1501092004030606060201 80
    0x400054685205181e06444e251106000c2040784007141d8000d210411040d0400d08203103040d540c4248212001400d0340b80130607030b010a0355244d85600610096110860f400c0070014803d0f01d1000841900444210395500c4a03030800000801c08401f00f0b07036070304003120f4901004800c040b15850f13011300003114002000130315010701c14510750700c9608104c41001c4058440b0710705908092400e076851380300010031300c1440385000d000000a4004030003180248101c1100099a0402842c41420340b422004550304650060001015035100e02c404c00b4200c82c8030b4140355200311010300228085004221754400554a84806640003038208141d201201d8400c58400f07000b02e4440d20701240941c0103443c054000307001080180300342ca018a00161805000030611204115040c00003030a680c0106c88072030284129111800401d501009202c090800c024050f001d00c288962020411210501c01c0000e00398950791080082d51100074403c00010a000e0941c1d40c40307450f03042c54405000188103c10040d031074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 112048003 1250 112046753 112046761
    0x41d15010e090c161406070f0809030a08040219030302160503060106091802070204020301060c021302090102030a03020d020c070308040303020f030f090f03070902040906030c08010501141003060b030c0c06 90
    0x421616041c004038020000c58840c2c481c2100d024454000c074410080c1e6402075940c0c8004a006000c45030300c414843c4004103158a00800300601010500100805221010f0107110703e01ca800b10170b60700d03140940d00e0b00d20603668407400003500c454100020204100e00119000c0185a0f0110f91404051884502400a075a542c818155610804d1003036000007440b002051019280100c0582c081101800c000b44c01c00740d80d80c0000d0100d074400c2c1d1010000c268242e40b031400314102030310f880582076807140c000c604100070720b00081d49034403034080c07010304055001a40c2d010300842a4103030f408003a1b6020403105001c0d107034903207441d02d98414042903000d8414a0030400f88010000f084400161038161490309202e8038030f003800450f09099803c11344c0740c001d4200104266450341302406c000d00b503030480802c08a14500b8014180032003604800e180d81d0422005100700c000c1206840024030301500c44100500015404034020b01c45500143d45140c0000700f0b00c41001d2941d409840b143c90001c007941d0194413 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 112049253 1250 112048003 112048007
    0x1020106170a06051609060c0f050111030f06030a0809010f03020c010609050f0f1e0402030307170a030b0612150d06020409090201120c020c12010e0307060912020a0b010b0f041d1501 80
    0x710380102c40003d04111003405211702c1460744000302c1e80f0035540c602002c7c9d0180d65140c01c0d40c1d9101007805540c01e0203c00c00640b4201031842a80210080c0c0c00380030040f009840d4840f4902c500c1d04441c0c14014005540401648070398102c3d0700160410000300b00294440800801810094030350207115a040d10200e403425050419590050b40c004401c1000443da2600304039800704e0013401680d05000901c80390021950003d0100c00b01c5a20496031580c91801c00400380403902040000f03400703940305002e0103c050350400a440e030040317800e40c101501c401c204400126030404e80140200540e002040c00558500c664210080c214401d80f202d05009a09855200032034025041c1800164403600f1021064113201043c4815044240c0001c21100c0600640a140d81d01000007103455541d16415441408090952240d03c102184040d010b405025207135852032400c107004185000e8070015076044210b40318400c40d0004d10a49010703000754521540340030b05445040710100390484240c1d14042080d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 112050359 1106 112049253 112049281
    0x50d02040b1207060f02161205120706090b011d070f0e040e0f0f010c090603020c0313030b04020307050f0d0b04110d12170105130b01020106170a0605 66
    0x11300d030110003800041c604c00c07000119004510a1000300300703422180812500700910003200028182082402c04525120f10030110f10002160405c20540d40c200c1c0d0780c068003841901d1040da9a0b000c0380244200e41c4500c070320560400340c001800700b600580307807a0f01c00c80341d03490243c245620304000b04e4104d88001003044459030008108950321101040703c43d440c2c6040000910805040c0003028080310001d000b0082131580126000e03071201c00401c10f46080c90b0300c4030001c5004a40e2410924241e01e0b0603141030b4000e01444001084500745841c0e40844908058031605842d0130300c1c0c03103a5080080207003049400d200c8011680c0541c0d640d10300d00c21070310380c041c01e140c25007410495006031120705000c500b90100040c50004000d00d680d0011989074501d42c00202090000d10400100e0041007a600200022011032140b501d4840c800941c070001607110342d500700659180c0034100520b034 = true := by decide +kernel

theorem cover : BRFrame.Cov 111870503 112050359 := by
  have h0 := BRFrame.cov_init 111870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 111870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 111870503 ≤ n) (h2 : n < 112050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
