-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:24:32.719369+00:00
-- url     : https://prove2.me/submissions/13c0581e-c3bc-4d96-97be-67365a780b08

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 35791372 ≤ n < 35971228 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 35792622 1250 35791372 35791397
    0x9032c040513230c09040501090512070515270f010f0b0109150e1f0806010e060d020706090203031303031202030f01060e010c0b091609020301080703020d0f0206030403 74
    0x300c401c080c00141c809296481c03a4800038502035101c5140ca00404084078003070035019080c0f40703001e612404c150b82020600c02404100101500980640307032040301a602c01c103030031a00d861820701a01c500a48294800c0c07200565440e42c07210b080d600113600b98a0300201020440541c11028800400320340c3c80c0c1c0c08400c0220900c1001c2c406c000c4c0000c43d000301400407070014000200741e4217403030150207003181390011031089a5005900c4c2a100640192a4030210401c4140c1c42c007c4c1d1504800c004041000c6000059503580315200d0b801e1498030080c1011305007824100710000030b41090b602162400e40c1d8240d1078001d030342c0c00c00140c00280301c01040e40561a040d40342c000d0041c2c1c4803075000088680140300781f040e45014031601505441e0b030344c60800c50a0300d5081c0102e5401440c514041c05000342ca00910401c200041214180d1000291440ea815542d44145004911003486100400d40100c901071005240030018807180381d001e8900491401415000200c4036442518200c0c04102c8102c82d02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 35793872 1250 35792622 35792629
    0x180613030201021c0507021909090b071106010602030301090b0a0f030803010503100603150b0d150501050307050607050d1803050d050403020a0909050a0303020c010e1f05010b0c0d0309032c 83
    0x1441404800131507224070b1044058080c11902854000900c140000c000c000d0b201040c8072001002480804401d014220590400c039007140740940318a0005050788040d52032550300000d1030f07412140d0725402503186a2900c00c900c8010b050000986a2090388100b0008a13003500503a81400786020f49201c5a4a5160100705860400000a44070481e800e05000704003060380c0d41c0b0340000d0b0303070b99101e03020070f041d5161400600c218070799900003400001c11504102c07291800d6030020341610700640880d15508d44401c20050240120f0700002c2c0036910420040794468070512385c0c807034a400e40030007200c01550cc81d545c182c1041e581000020010340007003401c005501c0c0000860009060860080108200325110315440d01080c640180074142c00040e10402034000358400d54500c9498402d8440990822601410440c0c480301c03c9140c1600b4180042425004401182d10307503004803004142501d16000194090005410180c0520040b440b48011281a2446c4512615048031020440380040400c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 35795122 1250 35793872 35793883
    0x40f080d08040f03030902060d1a010207120807020f0609030d020f0d0302040501120b060c0706020a0203010b0f09070804030221031b04050a0306050c041a180316090218061303020102 80
    0x81401c11001c407081c400400d40c4642400c016641502e008135111580f4000305d0300718411081d00227140d038a01000c50b0581d603087c0d0540880e5031003d90035035022941d0781c80c000003000e50117600a4048101008244010324001503104e003641d0000d0b00f028240114480040d0502d11450100300c056084042200e218950521440c4841c088034101181098201030008000040c802181d03403480b42c0d50a1851115600d541c00e8030180c41c0841d04407004961030b0704000f520b51a00302c10480c0607600380b180e044040c0c0380c2a0341d03540240c00090510000e50703550907400c590300c0e040504181c055004040121400c0c5501391549000d65402d2008950380c0e04002a000d800c00c190310340091207610051005220a1391001224002c598000c074000c102070f00c1c0c00a20100034811584601080014000104c15030444031001c1c0080450413409499000c0c00d25003030544407410a081e1607480500010b0a00401d60241d0142154002e94003040461020364404102c09074031401248010a100000c10821907a0405c030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 35796372 1250 35795122 35795143
    0x2130e011a030708070903060e030c012009010503040303090203060109050612012904060807060c0201110c06030a11090a060801050a0605040503120a050f03010b0301090b0409051c020a020303040f08 87
    0x100012500d410707828072480e4000036202c40200140540460b1042e0b10503da07103005503401510401088584040555480d8052a002801d41d4203010011a85c1c2e01850ba220380c991045901c40c520f0020b41d5001110950b100400480c2410f0755106010050b07141000118080c0000d010001154180380c42000848080c01c440d10b0f0090381803101d0705030200d008008442c21410004552006081610006405001ca0340c2000049200b200790001c0c8050344504003c0b0924000e80f1410300001c40c200d20313151148914400150814420004180d06030596030201d0b0700c0c0e00f40303040c1681c20310541d100003400e03070b002e070313034048400120558010f12042ca00b1001e000000c1400782003052038285090042501c81d401c2c151913541c20440841d084004502901c00c54030510114800755a0b25a151342425130103400a019841e801843d00414034900e00f4a84030f8080c1c1c0784d070080c0050003520484000e2a0078104c80e911203c003140038560200e001600c0800c00380000e0042129001052400e0030020351501d8451030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 35797622 1250 35796372 35796389
    0x140c06250c110d06090605060406120b0106050d020c031602030f010c1b0f0b090a030e0a080c0d060f0212040506090a0305040b0f160f050d020d200109050102130e01 72
    0x504804055040a921480558000600d00103040c920b07001800c0030042c21000741070b56043c01144403c008441c0e000920501c1d0443e8204045512802584415424564010004a00140140011030285010b0003205c90024000741c41c0140038200d03a41503402941c02010b01f000000c104204528040c0704d11400c131048040208071a50320200024581c1c464000300210700091855080c00303000220400b908629040640d120b114100076440c20f941c0c211460050b00080d41c0314403800740030700e440c1d01d21008481c0140c000300f040061034008c1001e0320301501000c554050b51880c00c0c0082d11103030b0010700882d01c00b01800245620b0607080c03c2d410200010302284254104000210010781c21400380c0d01618181000c0c80d8031407a00001c0d02e2024450220103500410502e104002080781000088550030700c6a070a58584003605041070baa1041d07030fa0b41803004030302c0f04a0012000300c0c1c4601a80e85440d0090000700d00508070762162802c9034003143d02c15002c401c6410317003032018980c00a0300c1d0f8010032446 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 35798872 1250 35797622 35797681
    0x8040909030f0318150b0303130806090610050f0102070801050907051806060a0c0c030b0432030315010207031a010f0602030f0a031a031c020c040501050a1203140c06 73
    0x28450004100500001000519171a40b0b00e524032140e54010010600040c007101e0b034600001c282780814046900c21003106200b11030006201031000310300d09018072564044120301504060403c010b00040784641b41c110310842cac0000601140074042d09008a600001806a081c2402c3c103018200079a5860b0012118041d802e0156988400045490f821102d103045200340187c0c2c42d016003004883d034405850206030200b40b009001001d11480e291071000c0c204049174413103980c042003106900c42c050150641003400001c0d40f440d0b0051050118960500c180d0f104141c8035a1010410b104039200781205c1d40000d0010300c0f00d20034000e400005000341c0e0004504052601d408038406100c0e1792612001c250705d8246030b0a1010003e03a4090101034001c054800d0002801c00300c2d40e041e4520280500140f141d4030350301c40a0b0625100b0380c1d05a80c006420ba6891030b04114003441d1030342900000b1070400403084400700342c00030f03240040c106044503030303018261504180060b07046080c3c88490802101c1c0c5407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 35800122 1250 35798872 35798891
    0xa0906050a05010f1101090b01180b010c11150d020918040804260d020a020f1203040b210c0403030e0a0b09040504030e10081602070602030304030305060a0308040909030f03 76
    0x240c407014011210246400301c12000320700740864641d503c68682410350741c2004a401e082146892010b81030340d038480040c110342c180c1844102c0c08d441c0a40b072101e002c5404910b64101168240004852900024060207241c84900810800300e520044002411302d60225011800785420301950103c010401d1001541d420191a901032a100d1803040e03082c000080800c0c80c00c0d50360f40d5000342c1c5100c503040003a0b40c080941004069140e00100724124030503201d41803007540c1407130071160110f0700c82c21041c0107600305401c0c10040c0c3c0f2607900201040e44105601ca010031120319400c94900c2c494404030f007065444034a5850040c00d1880440f9030607108a003503100c04d000444881b0150748208400312404101b64850b41400e40d45d1140510020350060a00e118081002d42c0141780c59014200602104401c0c0808100490b142c05003801050b0041c1c0080000c02c0102c1d101e908265000b10b40200a8150b442c1e0729510302036140d001d035100d00161602d84190030207040d00694902040c3c0d055060a0000303106 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 35801372 1250 35800122 35800129
    0x717060109091e02190603090209060306070c030804051005090a030305010b0f030403030b2206080c03010c050901081e0109060905091b060d020702210d030905030d0b03030d0504110a090605 83
    0x2400c180f0f0054401607403001c103559444403d0414410300640080340d0340d03229080240038080d4408180d0058503400049801c5080c0040c0803031040144d0741c1c440f000f03d0180d5904407a00c1c04094001d981e41d114040c1105082c0c80107124141c05141d0f1207008011903241f514024059440581c0700041c01003050001e860841c092004681c2d12550500d0005100684030001614038181c4007141001d00010901d040d020220590020007500c003010100e58600c2c580034201402d82c0c000340303210740c0000c4090240507901d5002e104441d40050610394254403d071060f510000340610242d000400e40c039129001088034400f1481142e8100f2130401c090480b601076540001e460005044100340520300000d081102c00301d0a50648000ca5401482901103007440112040944010b214400d00c13401212301c00c0c80158024800c000080d9400409103003012200d540e250010a050120181c150108018600300d42031a03200d1144a14802d1a210343c0c151500740900614820680040070a245009410b20060b903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 35802622 1250 35801372 35801393
    0x1008060f060307180e01060e030601080d0507080f030702010507030c020a05070612020904050405030a030e070e0609060a03050303090d0305060a0b04030b0606070503040f081902060d0f020903071706010909 90
    0x22400d032201e55030303501c800038212950f02c2d4910f60719418002c4ca00700821880c181c070b083e640c100c171030aa5070701403040c848070b0416403604003e10886c12036a00106a10030340703034040e401500703001d40100d24107420b048181c0380c181c103207900898820006075554420400c1d09070300361043c610301110354402000c50f940c0c1680d03510307600c01840c043e150500400b442038100c409500e4049400000020308280000d08240c500303955a60055480035010170300b021400c440c40360000484a04441620880070030b96200e03841449036015000e800507411180684001c408640c00f0070046006651440042a450308911001803c8903400391100303100b480324040c01c01681e2081d0f4161015a9000321007412140c8420340011442c1c0315100c402042400045000a80c00428404484c1100d07024000d4800c80701c4490603000384281d444900035400042440b1881d002101c9600206c03200075003040051522a490300021329103461a40006038401400102442c007003014003030540104400300c0180100c10003075807941d500c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 35803872 1250 35802622 35802649
    0x9030a0201110322030c080c01051602010e060403030c0c06091a0c01060509070206011806031208090705042d111905070602070305040510110303130f0204061202100806 74
    0x100c0358902d5601090024002c40c1c04c603480c0400821052140c08070b04900d0032041d44010b490315806050002281580800c442c28801e41c140d442074540021402e10b00316007080c5000a904214945005440300d40715038000700051806a00c49444080c40e40c980661a03a0300f40e0001ca00300b04c9500b00c01c00079164901203841810b001c0740981ea0b12144c907900100d00401895022a070300401810500400940100c0c186059554840c00034012480541c1c85030266015480024440b030840b401031030586200d4070f1007507082a80d51040d80c42c108e40c0c1d40001012354503800c1e802768100381d40360031070006441902d07450341d69800e03100f00501815040381408099401090645c0c107040b0301820305050201e100f1821209003603841a411520b030141c80c10000c005402034090607001d05021110002c2013401000b44564417080e00000314a0f6542d0707560000407a0ba072840044440c4075503c503500005039180d01481025000c1d40400f0b84200c480c0340100712051034280d5001050195110038407510f501c070440066800c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 35805122 1250 35803872 35803877
    0x5150d0b0a110c0106060302090109090e0d030903030b04090804050f010c02090402040b0d05011e27030e0105070203010e0a0605010506040b0a08070c06140910020f0d05060409120503190209030a0201 87
    0x2240d0750202e44401846032071089029546068030101e071094060780075090002007079903110021b90301d503d40324048a603540c05801581d8004040840161300c29004041c24038420b28011880303041c0e100202e001d84101100c00c50f100070f004a0103100b2400c02c00b01c1820b03007100928044c0c10090454001c1011500003903c081d00540c1c840e0004180358a61740303006260aa4072400800c40060150301c4080040c1c40d4107100e14200382003040c04003030180310007a50038021407034039110030140f4003d980c2940d88007400100641805028028036000d80e0f42032040080c90422a005008032007540d01d010340855405070401445a0000c1c00180480e5038107006440000c0441d003411089a1242d110a0360100108000240010f00b8140c000c403a080d0461281d0b8003c5801c00101c0f1101c1c503000ca0328030b00b030707025680161140c4001489801c1c2014441d801064002402820004900340182c03601c5045111514500000c100c00005008982ca030300081100c0000001400318100911600040e4803801c40c82c101904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 35806372 1250 35805122 35805131
    0xc080109150e01051005040f060518010e0906040504051906020d060603020301150507060b040e160506160201140c0f060106020d0203070f020d170d0b0103050c0a020d05030a060b0d05150d0b0a 84
    0x1c101b4080c40031540640400240808415542d660081c015481880705801d190000611107001d940244151626244014100c100507a5907000303120050000500940301481400120307c0c40004546120241c00c1c080ca40150f501d205038818007042d0380480e07001c001090320405c0108024035504400c80d10303841c442d240040e540d42071070070148082c018021050341d1180c68003502000d200d5000440d001312030000d40c5503103880c50307070381042000d68001c01c0e14142e01c2920030b19a0000644c030804507944a080e100351003d0030550000c284602d030480c00380704502c050340004010b101458041005038900b080c103100640c030b0301080d640c0b2210819101f41c00240115402c0c4080700402840b6400d40051030304801c1c10031b4541040d100e03240007070400d0304500e5000c2498603000c00e03c00c091010403554030b949160000d2000045941c0d08a07142e0b84001e0040103216500c01000c0780c0b107101580200005950000081158208400c04480d4101c10124480c03080003102c0442000410700140190700214181c00081c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 35807622 1250 35806372 35806399
    0xb13051e030904060b0711030d12020a050f030f0603190f140309030f0304090c030506100e030a080a2d02121804110d050108211303060c080109150e0105 67
    0x81c514060003500503031050400b00c2c045000b03004003003c0e0601d039001c0d0519903007003c1c3d80c0051607219580398440d100001c0364000044039101c20b6400400a048181c0781161600303408607004540c6400c2504d49004100038074041c40540e2404010180010150041c0078003c900030765140c0101405807240280303a0300d40301202002c0501d060003983c0241c54080c041c0ea09400c0c003078800c140c0782d92050140124807490413990800491280c0b2481d44075890140407000c0c03203000301e0402c0d9414000351414650510502141e40c00090400010f421207000544904070748014500c3c070426560000c051541041c0f0720b03840b000304440c0d4000b520840c100c01144540e5170302c03d00400c0b2000b080c840d0ac0b00c0b50b50801e09100710685000c016a0003040311000091040100780d80ba200b005403103110101c0e549081813000d06800c8510071020004050014921b142c40120956070f580e11010b4901c110305000208401200420915030b05000d82c05e00780c01292034405034507081c1070300c4226004041c0580c50180241032500b6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 35808872 1250 35807622 35807683
    0x1404051608070e0a0e040f03140703020a02040222090506011403060f040b030708070e0f09210a1b06020901030537060305160f0801060e0f1315090b1305 67
    0x1034050700e1a601c07500c5d51440d090a10a4100c0c07000001100040c4420b80a9201d40388005e0030b07101400c5e415806402070700ba503602000040d41101002078140110075120b4035181c046c0d905840000c001032100480c40e880d02200242030481d2188a20f041d0f050308008004440e82c03038003032012052104990025440c0d02480100c1d1820b40b6540010030188541600803c00020b00e000c09407148810307403060700c0301e0f590700300720b0503100c4c401c190f501840f13108a84c08040010011801515440c13540c0c0c907102c0e13440d040c0002490f501625103603041d070351036a001840c901c155a15009040c1d00c011140340111445806064a50340b60000302d221881d01c00210b03003d000100901d411100c0290340010444000a0005203c2140901b4a00c1341d200b502030409400580000306010300d9003121207040c56030a0655895101100806c4002e240703030010350b00004984002580103074195442814a440069401050b10f41050034110141070b4910808030320524030300182002a41c941c00340421081c0e60841d070a00c0ca42d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 35810122 1250 35808872 35808889
    0x504090515060c010b041a01020d0f0e0d0b01050f120303060d030302070c081c0305010f170f010606091406030907030201140c061302040c0314011a12011404051608070e 74
    0x198002e50018180401e0342c1d054020703041e00301c0d0455040066036034440400e1142010f000d000c5001d030f00b0011000d001280225001001d01d5803e0600c4440041d560000601c0360303806280484108000000500085c24100008090040700ba100d98180441991941d9a20701009082c14803a03218510f504007003502c81c0d016500800d611008426440c0c1e280c1e4611529241118544410f01000e0903500c4441807103400b070941201c0d50f100d03050000e9404e10300900d081c8810040c94000300e20a85100711910b28091203010020021540e400c0c4a050400988069070042010114420442881071042d04680402c0d0481240d0342420040304461300c4d101c582c0050f004c1c0e0342c0003c17418042e0f28104092822006101480184210740800182d80780e0342c0e060b801c5030124060690442400801802030070350080c218000c07100c8031030b050350400c998440300700c41d1078909070000c010b0060a03039411140350510b4002c0076000107001c203103104007000c5210010b00f000310044c24181001000c80403840d154840b0b03d203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 35811372 1250 35810122 35810161
    0x60c03070b040602040312080f0f1b120f01090c170a0908041427180f07080a02030d0809030a1b060207060e10060b07140c030706110d0801050105040905 67
    0x55150740c941410040002c4d0000d101c20358264480d0201d448505110303d40140c4648038403501040740b51502240c1400318040200480021007001e44074540c0320148030060a240540f54242034058504055620007041043c1d000409290501c000c020703c041c2c0007080e580b442c41d55213a0700801552444161409098143d00140030104009008903041c00d041e9041503012406507403040d4054000080081902010700103181c2c00c1c00100c0c0030528103203942c008443e246549908440e014041f8403119801c0080940c007200c03a59100c03060150860900f0305c0220810760603070901207070514100381000e449100314000e15080208900d01011006100b1019010700341e0840021900d40d1954a415001001103252450062003210512a1205c0780b9004d060155409040c40d04e0800303106958920b001c20b48074150300c000d8019559416035030b4404018410082c24250b65001d203003805091500c1c14038100000810820031007600510050360400e0840c1c044413011140007a01d079a54541d4442810300782c0c803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 35812622 1250 35811372 35811383
    0x40b03090327030a0305090d061d06070516030e03010e030d090201020c04020708090d03020f070308090108091605060c010204170d080c09010801050d0503130308180a050d0618080a09031e11060c0307 87
    0x110038502d02c01510800d02c10240d2ba02003241c0d4a6107a0000a0711507001b82c9211240c00a210341250300001e126160350008560301400104580700900460390454001a44207850242e84e119660309669042259604a817401c0c2d508501d40802030300c454645100e54140d40c0d01503c0390102c0a01054403c000104120080105452038261649020071309580001c0420b40040c0904000c50102c40000c02c2c840780f820040e0381e00c00c0130b846c90322061000580003690030540c02c0d5403e1000148034005000000146400d18018000044030100c002d041414094580c48038075100f8003007032039580d8000e50658103481d402c580040c02964103203050352640c8a20b1503060368240110f0800010000d009000d03000307003400b46a4503002c1c03143c01e4050082c0285c00303108050780728179146400004104154080f58010030f9000c40c81801c41803548840314154400c40304000000c40c185000c01c02c0c002900c8480351f03402c01c070711849409035980d51240068a0404c16040b4800c0303400080542144204004a42c4000c1d4802d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 35813872 1250 35812622 35812631
    0x9100e03120d051005010e0922080c0d1b262107030606020109030206060409050c0303030408090901050a0b0a0f120f14060607080d0b010302040b03090327030a0305090d06 75
    0x8a40c2600a00340580b1901101380805002160342d40c010407500381003c01c09059044c0740d070b8030305020500000003505011000245403060102280d0100c005003d103000d010003c120b0008030200c010042c400285040106901c0c54885500003821500001d024200401070115142252080b02400348104c02c00d012400d0340e030380d110603030f98a01151414403841a68070100042036440000341d09841c0c4200000300140c1002000901d01c0c6019071110214131300420407140d050321042c000c02d142d41c0c01900c0548800c0d80104510016203043c0c40d440f40580320075a440d8016070328000e4546458041c805980091055620030072006501c40c40d041200c130401200700344003211044e004000203004240341c503540c80000e907001030300074113002040342c0000c3d5010501c9860710190310402001000d9600d5000d040540030880007801e5100000038500454688000d9031307480042c000034620075200341e0a802c050010000480d0700710742d80450b010380c2481e05420410741c4d520b0102d000900440401c0c01c020981d6290 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 35815122 1250 35813872 35813887
    0x1202100503060f0a06020d090501030614120a020405040b0a050606040e0c030901290a080c01020705011107030b0708010806090601060f0c0317090105040b0f0103050a11030114010b0d0f0209100e0312 87
    0x50381f6001c001161f207404055070340b030310700440a4510600410801ca001d603614095941401c0390030341480050803003a11034030711480d400902079400940f0240c5400100b0010300035807509a04c00d040c0c11000c2221b02e50324107482e0155a0340303002d81c001c0010200b8000880085d001410a400c450041503401c14985e01000401d0700d841c030030071188a0103030301603d006140440c12400006101040c031005070001c110051418004407094141c900c6280303145d00603944d002002817130200710103014122649403169190704040b0f02d140750050003402406903600020040000d40c0c1c1180000e41d0f00c9100d46846180310800f42025156003821100405912012104100f8803010640c080c500962045900d84855210000180002c000a02001e0000e401040384480000c803100c840707480014014001141001e51507602c00c003840000d0b808031054004c00160710500c00918890304404034003072042103007420021404241d10f2071041f8103180030300000074580074460b80c0030064042c80007000301040d42d0b281c58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 35816372 1250 35815122 35815127
    0x2070b1006030c181401051c1d0610060305061503040605070807020a0302070509190911010905010302041d04080f070c03060b0906180c1603050705071202100503060f0a06 75
    0x1000d01c90800000d00e0700740c450500e80c1c0729013141205102c4200c1210400f500f000318041110705442c44031810301c00b0400a141c0784107640c0d600e0508240340c2840000341c1440c41000030014914108042d4050340011003080613842c20110924166403044c0740c001660707038510021985103440449901e00f00c070004010482041203640007a446150700d41c0d2410700380c0e107500e8130903070ba15501c0c08001801340c0c0041d035060145051840000f5485408025030b8003485503000140400c680005005944a0740c54810307250603940c1003170406006010a28085184c90719000202c1040100301035500c01207e40d01e0049000e120411085c2c501c1c0b130742040391040c0c0c2c0e00c04034078003d01e1281e4188000c07240142840381001d0681b4000942034810040030b000d000305504052141c0d0700002c0010001004c080d000c2c0100107829240803448502c040c40780d10b03801d941d0852030a02614000e8030750b10400507101182a0440180c8070001098080189800c02c01c3e05d907140c110002c1c0e0010f4044103626000074040500040841d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 35817622 1250 35816372 35816401
    0x503031527010906120c120606030212060f0c030108100902040603020301020a0809010b01020c060f0304030c05060c0c010501090902060901050c07120602031815060d0c080105070302030f090a02010c0f020402070b 93
    0x4145000070889990b0341c0c084859051420780000c1c0c4541b041030400c02081254502040300c06202d000300003002a02c0e58006001121101c00d41c000b01e50010040000810f42c440341d00b600034403003d02460035517142030740c45607440f01181320440c1151380702e485030001c64031950482406180d00400039912170f02d0361b15005041c00e6048444604a41c00c2192884980d40003003a4403521100140c050b51416031814050892640080e00442c20400f680c04d050000c504c0510509000d000380040065807040040022825104181c0000c0c00c0d0a207029003800040e03071240200c50b600c038000c1c20030700c0e1201c032080161810514503911a40d0071510f04440b0004009a40d4011071081e00d5042c444904041c0011885640300d0603220303000740d446940c0c0302213500c514040040d008560306c80d21220000e070362114082c0e800d4403c2035070f920303001c01e4022040c4046143d10111071750f442042e001c001c0c00c0c1d00c001394000074100c401c0c0c50b0001d8440301d0b10f060200c1c15510b035074046462854000b4018802818104403400010303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 35818872 1250 35817622 35817629
    0x20105070912080708070510060e0907050415030b0c13090605010f05030717060a03020d050607030507050a080114040f020705070807140612070201090f03020c1804050303152701 78
    0x800149000c0b4104030200c100a1032141c10218032820b004080c1d4840009600045058420740314450313a07034440580c24098070010300080c0e0119000d5040100c840e900e88a107541042d442070381060407809000c42503a0b4040102da810485681d8540c4801d01000050302c640b05e06400c240b000d031840032039582c090340c108008449003030346da009041d00c21640c2103956020644d22200040c84044e0b00810704192100244c5e0459401461402d09569950018840340754109080300d040e04000200000c503a098400c4642c41003040c288070f071800721291030041040d1014043c4408020711105c2651442d22281e02030a1100c0384560b046584113818107040e03544024903c1855424840c07040e0100b000e0280240340d5071100310143c02103050640e0442c402d4070b1a68010141d908640d41e401e501d8000c110406e442d443c1c418003c0c4c0280800c03881120130703c6000d030000d41c4524401c10502d4140000690300200f141d80c41100c52407828000b0780c0c118006010340e5250a501d0484d00b84c2b07a9085e03041201c075181e02030b048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 35820122 1250 35818872 35818877
    0xc07060f080f0613090602040909030804020f030601150309050c0901031b080c01020703060b060906030f01030308061c0204230c090a0515120406060b0d0608010c08010305120a02120a02010507 84
    0x190369100103a0b4850203040380c0254121402c11041e200d06000d0350840c0207803902c5500094205520380119408545510100313800080004003844154100082c4010b4641401d0307000c1c0465604001614800310038100000c800c165544030401d0601c4018016046020381c02041b2480030350b503d003030090740b103402c0c8c500d01d26a44400c4040059800000a4641c6e480700e03041e0082d21501c5d19588070f1034010610800c206400a204002e07140b03080d035a080045100e80d032581040e648550450500401400b0024801800343c580302d4060307940e2003258110062000e40c111804600c00c003654070201c640100c148840324031032a03054240010544900080c00c2c4000c0306079840c9001030b64980400610080800045e0317240a010003008140050001020b03501500692010a0040e5a00d103000700b9980301070001c01b1980e07a5000103006084081c020b90522040728906251154196110310ba1503c50740c422024124200044100c0700034000d01c00700c40c062500140c195187d440d46000030b8080c000448401e0300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 35821372 1250 35820122 35820137
    0x30d080a0f1406010507060212010906081b0901170c130f1404020901031101110d0509011412010b0a0309050708060103031407120f1218020f0a03021e060c07060f 71
    0xc0c5028280b240106000d061200e1680e036444410041d61203070303c500000d451854003000440300c03c4990203007490081014903c001482454490414205001e000603421805082210034bd40340da5440d14450550380d039140705442d030028039106940b400d07000c4000307544c100e05000d8903030505030010760100314007600e61101801200c1b07041410314450b0f8003c0310001e40c02404580180301107108810381c003a507450181080c100907101d1000301c619000441c201c0100081000442488a5030701c21444203440a00e03401440c1030503240c03120700b501d00c07070140100768801c0c0c0045541d103903040c82a041811200d0b009015a0917117a1a40d61441d241d03242404190b000c02d80449001e5502e441c03410896410a8110210240d07c2a03281812120f801594900f00100401c10048101580c924447c60310b450049040721402e0025510511080e01007017201184a10082c84003007015840d180c4100b0264080740815468001c1c003180000c0081c080c01103800220f00c202200495180c0e004842402045d0301a1035000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 35822622 1250 35821372 35821391
    0x30105100303021b0d0b01230a03030c060905010b04090804090c02060705040603090c030b070e030f010b030c130f0504080d0b06070c030201050a030621020a090509060606031005030d080a 82
    0x4032003080e200090040c0d20081601c0381c031a0104601c0907401d040100811221601c64a84400413107007a00182c0400769101c03940003441140c80034891a00074242c071001013003440d40d10041c00c01c914490700134000b40d031114014001c0103800c1d800406010b1004008014044071406d0a42007034116000317549c1c2c45403602110904050002a0b010711440f0642d03070782c1c0e160605100c01200600401c0e101246c18004c05040400000c1030486168403800040e40c0315000c00e0300d43d800301454101d1440240340240d250050112554030007154008002c502a2404104101c262050702c6c0100070050940141504c1c2c0414031080101c0e00006180c9500190743c1406913000c0310041088902c40c42c00c005202001c1c0820410055020b030020b0034084035036007070004145a43d03012402c0b00300b0401c000c0c9104101c072014420708601c0d01c51081c00203441032010803c880c1c9041107007143c1c1c0c2e840c080c00d03841c0303d000c01100003501d400c110404100500409010f6908035901e4000290044406450f054001828069000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 35823872 1250 35822622 35822641
    0x5190e062a06040c0314120307030e15071e0e10031407031404060c030209121f020c06010e041b090b01120504050607030f06030f0f05010e06090d0e011e0806030105 72
    0x50f40120f401050680000d865640c4000345140c20b07480c50069400b503801002021360060002e54410240c684011a42c1d0207000107003820502600c1811023079160b00c40600040c03035440580d188004406104044682e1340300f0300151042a02c100d0000c0d40264042e000c8440d165050304000d000003000b019409083c0c42d00c44043d016940100c2101c8803003842180000c0c04103080d6040071072038610604005160828503004101c1520b000d201441c1d155000d04010382000c01422071620304040c81e05002c508080c45040b201c0d071514010300c03461010895000103d0184440040401b550080c1d072016600c560340e8921000001e880c03032000c00c40c0881c444904581c1016110300a40b482958080e004e4a000c1e51089420350007400744481401c0d10550f140804400110410450139400b4003448408006003460320380f01c0d080d605d4140001c0c40e40c1c0c00134000d00c44044000100c0d6070100c4a142040c00c0e03030000010049840607a045a480c00d282581000d880f07501c0c4e0090041801824168000c0c0096500c82c0c0b0f44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 35825122 1250 35823872 35823883
    0x10f030b010e0112030e060403080c06040c09020a05091509060403060b13020a080f070306080703060902120a0209010e040213050a02031006030b030c012105010b0c070501030b0105190e062a 83
    0x9030042c01c82184131080020307206070880910b03941300500e030608040c1c8a40358041303550841c2044080f1544654248030900c400d9221003001050490800c0d4601401420003c2c500c1c001d0954041c00744803240303100710031085050140c940c101e0000e030009071155601e04010000d01a143c1d0310074040e550000d03c1e05113141d10b6008940d000c081e00c0e2202525515007100c0a60031040048ca0a0708141e640d000c0030840340c0082c448180110700414011401840794010400c440544561066481c0d01401d42c400048e119450454115500301c401c110140d030701c40c008151120400701c000c03860b0b00c1c42c00342045a41031166000c0c501420300014603402260311020141c04075000484440e5041e13000300c04113025580301c0e984009019143d6000f040e41070298030002c3d8160344c42a0050380700041c010400380c1140d0320400a0b0002410246804d102200c003400c00a0540d206e003a18007202c0441801380c41e12400d004410f140000c02c0c001c3c1c1100d5450040100d03200303041c070804071524124070300c0e032035804a5050000380c5c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 35826372 1250 35825122 35825129
    0xb0102060601050a270b070c050a0e0f040f050102040603240e010b0702031f140f0c07030302160507080606190e220609030e090a020c0c04150b03010f030b010e01 71
    0x4446181c4401c03001c00365181440c00000d4100812001049113517002d5403500300740106403d00049850300194901440fa4040b1030704a1401100f11032010000300910009080e040f4011a0801c071554456003090100314000b06070140003036000150014515a260b80b0021005406071110a01e01c015441010755511180c03099085050b035190050042040d000300501c0d00c148014221030100e04011a07a13049928541401300c1c100c0d0303a980410141d000150070141d031000e0306510b070841c0f510b80540124580c2c0220300d0060101940400d029118210402c410119590460b00321040d031a5107140950f6910000c59203a40a040c0c40650208030018082c100d40a44144142744070aa640e221035641448200c0d10740e040c0b100d015420200c000c0b420030b114240050b4081d65414580c40c1c8844203012100501a155125a5204110b5984081d03000304000341c1044048401081c0903800900034000082c280d0054820101c0003c00000e00d402104282c4007168481d5041003000c1c0e90391f4950010032070b802d20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 35827622 1250 35826372 35826377
    0x3060402040b010c1a0709080f060703090609081902010c0c0b0402090403050403080d020403030306060e03190203031309020714061b030c040e01081515060904020c0102070203060f07030b0102060601 87
    0x824014546500000c00ca41d10600d01010301c0d00080c1c943d0039a84051584c0d00440f09441402c1c403410690024070310001c1d02c00c1c1070052000850b1134210300c5d039520300100503504141d9580c00c114200300160700700c0d0010680050446403160320103402c10a0304012420710310301561a103076110840a015484160040c0c0c1c0007002500d0b80d41c2d1b15001d0001182000300200d081000811000c4000742222025041803625030742c2c016260fa08500c0c0c040d0450b107858000c1c8052114000300c420460341c000800c000100e209130140701c0c1e052100c3c8046451802000003403241c900f0401e0010880303599540c05406c0003400b40400c29003007405000700a442c0c641c140c0e603200c49404202001003d441c4610019030304080e421407110314007681d44081c550920020b07006800f01c0d41200300c0ca4030000e00c0c010741d51030b00b11310722040980b01150940000b4900c0d2044400180c0190340208811034091400e45c181c9084940140a0b68414907000745540f461030740403036440c0b0100f403034000e0f5a48254400180e50b4800c0c081038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 35828872 1250 35827622 35827633
    0x91011040504021b0a05150f0c0406120608070602010b04060b03041109090a1a090d09050604060c0201090513090b0f07050313020f0d050706020c0303031504091b030c0509090c03 78
    0x5003800701030351224021448856519601c01c0c001303402000035140b854003030809440e4101c015402401a854080c180011540f07581c07090190700480c10007260101c3c0c0b81420404a82c07040c02031510042c0413546d00c005110b004040c0c00040c0c02e5019013004042e21401c460402803d91181d911511500050300d014282d11408001c5140ca0700304851803541040d05001221248011031380d13200b40c210884150102c95442440601280742810003804030107040509080320502c0c20315000c0b4445014038410b05003003020b501844c4055901601c64000a000098010503c5a05400c520400b41030240000c031140c907002400a13910b900d01d03011141c043d02e082d43da160320b5502c540e081103c005842e42c000b640d1100d0b050545001a0b92480c41600010307204034040c20f4051714006020b82081c0f81050b55a01a030000c00400c609241003600081ea684003c4030005010700716030500c3c038814540384482c2c0d074891031044404400d11200c9002d010407280f080b00d404a0301d0381d4503000c01e038888013850010354042d4440c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 35830122 1250 35828872 35828879
    0xc140312070807080d02070c03060b030102160308100e0a05010302100f0801031502190c020909010603170315060c010b03010f02040e04020f030319090305060601020f0303040813090e0609101104 85
    0x800003d160315801445403a0034180d24814110499002c840103d56586406008108102c41800f580e218024210003c45c1400542d80505000c0001e415004041119640c0010303842149040b11002800205080c0c030013619001061000038402070006911412100d42419417940c4141c0240300c1c03041103a51038909591039550b480c86115881488024425020f016009881d0708200341c803140d042203a551040340c81140d0060081e0b600010304a0401a41041403e001049002c004010180f60180038165aa0758080c3d0390b40b580403c0f102882d900c0300c000107400c0f2400030150010350907070f8001c60080183c650306ca0804022445075115031028020b4a500150261515060140c2c8188010f8280c03494049500d1541007641865040f0b44081110900c06100340309007001000e6000f2801c0c0000d00d0034541140b02941e4034080184003c100075000034528004a1420050f800140f10000c014080343c001418840c0d2107100032180c1c4004c40c070407450345034103070307101405410210002c010045140504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 35831372 1250 35830122 35830133
    0x5030f07060b0616030311030105030d050c0709060b0d0e0c0906060a020c04150f05030105070819061503020c1917160b011508070305060105040e07110601030c14031207 74
    0x803650544185540d020128810303201c00d4020f10788004000182c11119a072841c010301101c048074030310314a4280078030050001e0348000803007201170031560400c1c07a1a514142081071405403150000320740d280c1041800250000c1d01e00190a403074640c01d001703019000c116000346641d104409031050f03100d507403000420924240030b401054401124415030b01400001008682034504000503048600d80e041c80400c4440089000d06e000b602d0214001d12490034a0340c0002c000748406059040c450704a401c00044901aa91103400103200d00d91102c03054005c444405170080d0808408031205015415025049011107000c3c1321f1102d50101420414484045501203150090b82500382c6081c815543c04000c100000c0300c1500808459403050114203061200914104014200c601494204021301c4810780c0c0107003d5600303591141400800701d5031065801c40b01d42e90254048007140c0036020000c0107002403203104000f035510b100c0c84400100c8030345007410395550000e0a0b10007a05402c2c0048000101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 35832622 1250 35831372 35831377
    0x3031101200f070b0117010f0b060409050606070c030501140a090201020d050d0e0a0f06150e06040b010e09090105060a12051b030705060a1d0612040f0206130e04110d05030f 76
    0x401c0c1d02c41a80c1085010b5a81c1c2e0300001c0280c01290700c80f1100c1c8455410103d007405042605504800144070b040c000d040030800794000d0b07004240039076403030f100001d02d261910b10030781c0c0d05240c0113171b4105160355503418030034000d00301524500060001540003030401000350091082075503040e4010126031a1981040f109900722042040d1075036210904100180810040303000e2450282a02d081f9070b90140c9010ba04460300c003c43c041c0324500d40c00c010072448003282502d0394009410b503808100d0021072001298415850950035901c400d0340e000340300c650141580540d205000954034180400d40701c2081c01d1401c88445c4c0010043d034000c41c010340700802d201b586441c1c8050007034226400f0b45e440e007001940603001041882d0028803030b841ca03108050058044002409025203036a80f41040598895520350002807010b04a1800171841034115210201100d1118120b40b04034142c6035261004444818403d44060b912442c02050f14482440d01c0c0c146030a11a5102008500c1d1002144461350581c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 35833872 1250 35832622 35832637
    0xf060c0d110f0d020606130c0804030f17150301050109020405150705070b07050303070801050907090303030209030c130c030f050609010e0405030403050d050a021c0806010c020a05030d02070303110120 88
    0xc0c022481049400c81d4104080e601100c29130300541202e103404414022001c4403480010325032400e000b20311401ca03802028070380e00290903140030f031054250068240c1c1d102e1800c82c0c4001e420718007002004441180c00d80c0c80707901c11004900030f0003143da071900130070164021401341d15032000245000c00b64805451005120036881481910546070741e80c10202d205420004055800c0c2e000001003040303055008582c2405403e08a8031039609040c201c00c018001004c0703010003401d143d400038149a00d95000c010b4032043c81c0c4000c0007168080b0b650414500a4800c128101010a00300089001c28191074000d05d88908005002556542e1a040c0c3c036928801014100796101c0c0030411010000c294180710700c80b4003814a803146a5200e04221001f8544480d90718a03411010814001100e913940c4458055041842441c140001d580a80005001e41c07145a1120780d143c403a0042d61041070b0b8000c100300c01100e001791115108030035040381160980e42c048a505113140301c804d00031040b61204002038040c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 35835122 1250 35833872 35833907
    0x30409180b010602011512050d0c03170103050309040605030102070f0f02060c03030a0501140102030720010908100917070f02011d04050a0e0d020f12030a18030c020f060c0d 76
    0x201d8036207202400081e005400141d4403074402e240e0103e040702408008200711b241e2038581002030303107405888007480c0101408110161a410307040c58840d1800d2103281c0151044d039a41541e50703140c03617541e0381e2280d4080c90145013000b00c0000d9900d0107200b50340e816070300007003241400c0d00b1668810705141d0301580100c0e44544180214085000300b000654851070b180600083d081d41882c290074a0900180240380c110340c4100004400210b40d842140c0d21005600c595440b40c040210050f1a12015a0440211441050940c4410170380607041064040d01402c0c10072164444240c07004464440c500b0081d005409100c008401035105000341044480d025800414045603200040c096440a4546001c001d841d180c2c40280590180302d560150302d481c0c00200b115607244035849403120350941300003e144030044001189008660040e4040c0c801940c5028032503881458050042c3c0b44624044c0e020b59400c818050046c1400002c40383c82e400340d0001085000140b43c4112442038180419452 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 35836372 1250 35835122 35835161
    0x3030a0b01171e0a02040302011b05010b10020616020102130314070308030103050a0b06011d0108060a080706020304091512060902010c020a08010f0e0a0b072003030a0b0102010e010b03030409 84
    0x440641d514500a4042040c3c80b40782c0d1030800b10b458030303030100540b50b06030003481084200010b0b80c0184818030020a40030b0080140580c0b8201a03004045812500b50003c401c1c0080042030f541c00314178244240b01001840b20000c6810104134201c0c021107180c0c41a03855011030610205401141c1403907071310400d4044804103a1240d4a10449410a910850700707036012103201c0e4100400c0200e155800a42860b1880c0c07884050701c11100b0303005610150905001440002c00c400e51503252000700942a1042112071496450300000e43e654014461041310503c0d01c15400761900403285030f0780c04c4941c54240240c00704000d4840c880100803d80040f41031011100030100146c462200540084c940d1000000305a80710740c900500f0307610b585403604034076004039650070300042e030703c4d00103a4105201c2d15141c3c503c24150621440e20f422180898400c03844017000f00034180c5210341180d10000420380c024405041d03a40c0b08030342aa00340230065540b6410a2106200d242800c1c0d02040682100c401e4001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 35837622 1250 35836372 35836397
    0x50705030c010606090e0a0b011d040e0a030207060207140907140c0d1101110c0d05031909050703020f030604030f0f020c040906050105010e0907050a0507060f0e0a0606061103030a0b01 81
    0x103086410960007600414a0b45c0020401c240203001c4245c1d001c00c1d03102061101103e01e000092880c9401101d481e0400014984107002d80c99a52180368000303064400c441d02404c041c20701079501d01c0d140c481c20b0014402c5501c003041600c0300c0804103020501c040c01814240e11504020780d014104800902c0d0054800c1c040016035200c1005588180001c584910303021204094246080d40d5441446c215450402c004144d0302c4c00d40040c80358444451807a1064403510364000c41c202601112001e442c205007448e141c8414400085007000880303100700c44041e41c80c80706006040e21810116006004500c9000100744500d0050700c0485c6103a80c80d00c15110004450030014084038401c80040d100e0543c4d82006200c0740d6001581071000340000c079003040f070602d40a0780042061040242030720030802c0104642041000f00c5c0c200b480208501e20b0705102740d60303803100129642c005131038080d5001c0b42040b100141c03a6000343c1c0010005103c08000e985903544000005000d0004004014108140101d402c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 35838872 1250 35837622 35837647
    0x4030e06030a0c080a06030503070803060d15020301080c09070e01030c110f06010513060308070312061a030403030b0603010614070f06020f040306060915050d051203090c0108010909110105070503 86
    0x3540300d007500d40b40000b010203c4000080440c070700105081001450107000f070021820000c2960b41c0641e000300303015500d50b03804001c2049500d441d01d00034141c0520a214924103c0242c016606941181d4200c591544003441008820700c0182c0300040410411071010b03850313510130b811418400040b401d11842c03941e40026014035000b8504122451900311800600284c64800c2c5040442801c0c208240961800c0d80c132012020b10814000406000006503644c600341c100c0e80003c00180780d0103108080560149001301e0455104442c1140002d15040b40c008440c40c0c600300b900d05171049a030783c00d04500180e800b003c0d1141d010600a443d1030780d07091140d10000300507000910001c402141e59070b4403107146150107019941c05400403c40035050564540941c06031004140c11103504442106245550342021401d0460240c0203070201400001002680303c0005490240c100c0c00b070340d07100c842d0fa9031070402c0411500d80030401000b148504035110310315031040e00070700052400790007560328083c1e444160 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 35840122 1250 35838872 35838877
    0x50607111507020a05090f1f030606090614010801030b06010c0f02040c030b01020f011a090604180c05010e0906030607050f042d06030b0d12020106030503040b0c1614010804030e06 79
    0x188107000400141d14085091422158008040c113940c1c026035400e06e1b0030707a6661140000c1200e0303985180280441508100f11a2a000558000c0c0b4204186c54a81040201600705401803880048804c0c0bc00c01d6154452010581282c0d0030014031101340d00c8a0b401120110f1210000307540c4050010000c0c400369507240718020556506031030000d0707403115110019050441000c00c141050349450402d6001744000464503400c80001c8400c0301080d91000d0009008022410000d02d181d011941008200700c0400309050542e8800d0301c4403541d0901c0101044220388084842d290103801c40004a66007a0140f0060050202c0402c0881e04240e101d1030011051502e0b0690382c0c02d40c4408015a450100107010700c640034161781e18051107a001102c0110316010f11501004252115031649811410f100b9403011015641c07003816079680b259544908a21500720003040c548501600c1d0714003c44100c0901208120b5a42c82424095040144015900e0700c074003c0c015000d0260414002c08980e550400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 35841372 1250 35840122 35840149
    0x20307150606080603190f080d0c1101050903040b120403050c1903080604050402030a0f02130c08090106060507031d0a0e070c03020d020d0e0904060f0501031203050912030105060711 80
    0x1000034581e4684540100324100c00f91805000c2c0c3c10806010084452005d6040f0032250010030a44071002d4034500083c1e03e1148a0300f400d0032502e401400c00d0f441b45e02c20910b001e103d481c0b1700288079503101c03d00500c0d1644510301c03600000b090b080000c10082560800b803a42e00c1800790803ca0f0900704d0f9550101d04191001c0380c620001c49511704480c0401d5000440f42d508003805032800c1100f440d0550200780e07079a5084ca0003420301200003c8640442d41c440600120000c0c1221050240318030604001e0304c22141036883d642503500380500851060b1042c42503800068040d902d1400030903004a01c20300f403d56200b280754200800e070350b008c10580268614540110380c01d640e40050f030011410004c0c10120043e64020454001481d10b6011aa1100e000225580c04a42066064841d171405000400c117007130040c01030500f0f000002051007000146803103ca0890780b8103000035581c2c1d001054035040414900400301c40244014003941c10b09601a14030a481031580c1801401d0141c00078024800f00003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 35842622 1250 35841372 35841413
    0xa110705060a0f1a060c0c03030a0309020f12030f070305040b0a09031a0606041806050405010308040510090608161112041511030a030902030703080418050c09130c020307 75
    0x1050010044a900c40c2c03038000d4440340790810078a01300142c802404d6501c5590144903030004246022181c0b018448041c0041c070040440e0784d1440400c40103405003186042c141e2040041c01d0b104041e43c1005100083c0402014012310b2508510b09003518a980180b00c0c00d4041003820b20001ca11821080300800401d01d180e250444281c0c91441c0c0015480410a40103082904800c1400041c0e1180c90548080d6803d84099104010351854240c1c020b1460341d121030780c41803c18000006204190740100b0555006407140c00209008083c15181c01c41e030f5111328400200c55000050340d407090340401d50500d00b441c0c5171404d4a00502e400c0c503841d013455102510740c1c1e00000142000944410740541a60602d50b0a00741908144000d07c181c0324051804110249a1158400030455406000d19809181e2000301e65844540311a54080782c503569a1110101074030704000700303001c0040801598019140144061350316164a90104040c0c1064100c020a501c0107011040000c2c0c040300140c0c440301810f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 35843872 1250 35842622 35842633
    0x204080106170109030f0806060708040b0705060c070c060c1514150a0e010302130b060c0a02040f0605130c0201020d020c1f1e05060102070302040e0a05060c0406170a110705 76
    0x40c420481d001c5078060402d520340c0c5013504100000b50080100c001180c450304164140b9034804000c11001d03c01d10320014800c10000502007030f00c40352a009480054041c0040700e01564580713801042c94421640301070b0000030301d02e07030411102c3d00c01e001100340d0a07c00c1d0a50b0200c180505c544e60141ca10b00804014403036407880800c4040c8140c14980d6580030400c640020885140c1828404058018040640240e24601601c00c44900c01d81140e8110b50015161541c1d4038000aa002d44502c14410203c0c400c90400714401c9040c282030191406564004011241c008640c4079460020009041d41d0360655400380404520f0f0840d52024000703840202010344140f052104040754241441510b182d5010701e00000c0d50882424a29900103209000340001034649803000181d2400110b90b200a50082c100010300003515400b040118941d80710b5011540903851320480c03060710303000b03038015800080c00d4034070400480504000c0040c0c011100c81000102c840302030704481c00c1035000000a48103540716 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 35845122 1250 35843872 35843879
    0x3060209031c1d032a0f060c0303040311030403020f0409060b030105150307080d1b0c080313091802100c060605031006060f020708030a0f02010b09181504020a03031b05010204080106 80
    0x6a495403038803c421400343c402c10803100c5407040800b410070740805a030340405100d80d00680307440c80301d0009440000c2100c0e4881000e0490161303241d008850440000b00070440172240207400106543c10741e40d0050079042102d00302018880103103203003901980d465840b20720604164800784612401000c0d00444410140c0a05003070502d0003d41da88680700d02c0d070010b20302803000d507030000c032004000007141104070540c111800c0c03114118410b030b00034500501001aa041c035402d07003030300361908480d40d03c0320038400004825210010350080c60400b94204070030310102002d00b03110366848042584280400100e0544070800729180c4014190303103000c11030352003405103e55034001e01c561103118041e200908181f8206410180c8074003079204080b09001c6800e540c0d00d4524001e4101d42d1403268080d00d0700c1030324909042040c500c4460394004603c140650b41035000c1c40030085030390031710a17a000391540000d0f910316a01120100c1003440f000741d1140301103c034400060300a00040c0000c0c02003c001103901d906 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 35846372 1250 35845122 35845157
    0x100207090b0109030b0105010503060a0b0c01051006020f0a02060c010608010204140f0a080a08070c0b0a030902010f03020f0906030417030405030d1508060a0b060f121005040506090103060209031c 86
    0x4401e0707040c5061240e104420800207a4003001581501e400703181c4a5100d480b000041100e25101d50810040c0703000120380c2e00100181540028850b400307440d00f459070240da62000342d03202e070300c0443c2011a503041b10350300d00094101a0300400f800c01104000103481503482c50340900326041034001127118400c2d000401c21030316042a000e08020301c210b0381d44509a2801e003172150b41302c100c0400104540e070040360075800d000318111000001d060400459680d045070f254028014a04100d04030301082141a14403090781c4240700399404000845801da00c1c02400c0700c2080401c1e00010030440e00880b0821480c1c0d8036020260156004600c00e0008580791804134050a00b66030900e0400383c3c0351903e40c44100841100007410903046007031000c001880c080000c2c0403400c03510034614208100c80380041c01c0940b192601905900c141d80386207543d00d22030340f10020881601c0c800c0e80c41641c0511000014070104810764020910808018204c80d48080ca211181426075407a2200e20b0110300e400052000601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 35847622 1250 35846372 35846381
    0x20c04060509060117040302150c21010b04090e0a020a06121103040f020d4218030516060906020d18080316020f032803060303090306051510020709 65
    0xb01d81c00c040c1460310000080100490b0541c00c1c4d540600301e00070805060090121005440c1307405e1550701245411054010b140e4042740d1410240f5a85c103d0986007040c94022090503a02c43c605041d02d001c1c075103004c09002e0031f5645600c54031401083c41e52001070303031502103c4008100c1512000700340c0c00c070004110200c4043d103141d016500d03010420000064048054954843d03070484802e03001e40c03c00e042c0803036a44101855600b012200d8103d000b15595580c0403000c099002e066071901c0001c1203450141a80c0094154404183e028000000007a00510142003c81d940b21020105049142c035040c080d60380404040d910142d0020310260108240d0044000c11341446000029100c07030f40d505d00c100c80c4001808108150300c81c4900c0b00c10140709001000f110000300003200e896110302c2896882d81e6186601c51402c00007020100081355000c0c0c011802205e40680782e0040130307490358031542c001e0301d0b00408080703010f070040e140202c041d5107580140b902c1e071816900815106017409409011203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 35848872 1250 35847622 35847629
    0x1260105010501051605241603090c06030504082205010305010815040b07020a02030a0c05010206060a0806070302031003050d02060402040501050f0d021201020c03030f0f0112030516080c030a020c0406 88
    0x6904010041c0b00b66604501100d4801d008008078010301c07203560509501744460b02c0e2180600320203400701c014810a1440c0e05500400a01f4070544036154110000c0d012070311814002000d001c03107200c0c03c00c0903500981c0500e91250261800c94500008040030741284000d60141031005c6000810911855a250ac03c4502500740800140611140d100d804000080001c1c00140317562042400100d10740d02c20300c8014000313030b4060200e4014895138502303500c10001500a2070700501c071b4000010b02918021103c0d108882800010b084152192841200a941700501000c00e09421540001c00540100002c42005480342d0203004181054410407080e2801a48224400c1c190040c143c851a80d0b460003151200b98119690340b200b0849441d014068000c01445031083d02021003000240080c00810b544a40e100c80c00b5296280e0b25640415004403500401a002481c00c0c8542448104601c0106011a014002050400405100701ea1640d070085a41d01c0060300130030003034060360405000742e0018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 35850122 1250 35848872 35848949
    0x6041d0a0b04120e03060a0911060f030108010c03050f04110a0e160207090e070e1e130c05030105040308040209070903080c03040603062315160b040311010501081c0203040801020301 80
    0x1812031103130001e0782e00d2101401c6ea0600c1035803008140c042001031040402c0c4000c01602c40c6403240f100c8040340c0e020341c0091003241b00e25401e0181c032101140c407a2251522400c0c0502b0b40c25602d454540b070b02104404541c5c8916001100d11201207402c0c0d00c5201080d10a56440a145114681300c0200034140515030b071009210606020300e030304040c000445c480c4292106000c40d640320b40e0326902e005004400144c0540c043c00e080e002446010b4424000f0010083c0c040c1c3c001d108101e0340c8d101858203c034030444005d00015822070102c0c0051800010250700a0340a203030018035aa201d03280c81045030f0224800c00000d0380005000c201107a018040c040080103906100c00200c1010109480c151110000c160f1040e00f0320313120440e06a4074002601c00d0020b641c0d840304001d1905241c8a18180c209650640105590701d0800c0134545050082605a4181300040c10708004c00e0444030200d01c00c1e0b45580c0381580024480440c0a68091001e1402014804640c0b0b1400c1546052941c1f024104090902c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 35851372 1250 35850122 35850137
    0x7110405060102030405060d15030c0302010801081603080d090510020306010e1c1101050f04030f031205091c0203091309020f06030c0901210507090509090109030806041d0a0b0412 79
    0x245680c022017642c01311801514030990360f6285100d800001c24528040072980c0c640b2101c00300500c2011585001968400c0c0c83e090050790303d403d0301a03540e01e1500001c40c40140e0300501800090108000f07004091b00460700460703541803c3e03881c03604010402c0080c448586d4080f08124681d81d0000c03048204101c156050300c048a03103440c0c4041a00c2c1c0030107000d4032308141c070480804264825011034211900381c0c98cd00703403140d8484c90301c40e008491000b8185c0c0081c40849200300c200c03049110782c074040c604800044c83c2038502c0003021240c2e090180c21000650100b030146689680382d00c0c0690040c0c1c10043c01c0003400308581e10400070501010200940190750501c104242c007982c0d10101d0b587d2000909001e542e804001c4000a002e03048842c2031700c0564100014414190f812100c41c0342900c5084440741240c0c0d5512519608032050780c840500051099004903d0f1810280c0c8510807490800004170043c0d0b03003150407545000c139031010807914200301d00104400d1103100e420040750030352940b40502 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 35852622 1250 35851372 35851381
    0x82203020a02040b121009030909060b0712030f110301090c0e03030301061107030204091103061b0d05131712060103021e0904090b01090b0a0b0f0313111507110405 72
    0xa5441c100c03494000d002d40e94401c901c42c010b580f41d000c410680a890011280c0c07100e0700c1c500700406004c1d119011001f04110303007030106000d102070141805880780048260b0502009403102c1c082d80421600410916a032007403804848441b9001d030343d4035041d08000d455520752400c4850011a045c803d2000100450384813941260b54010044074112041881d102c10504850000d01c0c1c203014056000950062500c03200c81c00300130180c414011280402c8040d980d01d5038a02141c0b08013004042030000c400c1c0740c10401442c036200c450344480d47000340c4100c8102c94142207564420076420001483e0034680382000c98600c0741d0a07400d44c0c91550013072081c0780560a0052410381220440722640e84d4203403504001c94980c82940781c030b0740700c1e2560381e801c03032181820f5507501c580310401000c06480090103410707001008100e42240c80d04441d000602c10b0901443c3d65500a02e00160003c550021603c3e540343d0600c1081694070701c00c809004010f01d032070017907441030389142c1110726514030f03811240503904040800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 35853872 1250 35852622 35852627
    0x110a06030e07050a0e01030b0702150a0606020c0108040302070603020d0f090c08060c07020303041205010b042a05040312050703120c080a06051012020f0c0708030903010e060f13030e03060403082203 87
    0x21780c112688201d2013031598543d80c0050b424601400c20f980d0300d0310f04184c20003000344d0700d0780c10a500b200c90079002d940c83c1100340d000440388071200302c50290140e4410a020040b0724400d90040400312208000020001c0224188000f40d030034040e41903e09102c118014069047c0501c105a000514405060324011a03640425102e00691156180c20b036044001c0300305201c004e401004031420010801c1204100700c540024804581c0030200c02da0300e0390040b600600b54000c20455043c4d03500070030401c0c2c40100b410390480300c59120380c0b801c40420422482d1541c440c10316018201d13240b103031500e5003006468072405081c00c644090380110300c1403111000280344160424203240d01c10405110140e03540907107045c07068062003009070b080442e10660400041a200100190214410480c001c0c080e2a45012145540304029070f80e4040022102c3d0219515801c5030350745041c100d02c0b07410424605810840000c0c1089011101a0b0104000204000e1141748190101d500e05035580d9142d941c026003601d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 35855122 1250 35853872 35853899
    0x10e0c030303040525030602030f010608010501020c06090405090313090e01050c0a1b020103110d0b03010b03161707030602040806090f0111040303051c05040302030d051501050306010309110a06030e07050a 90
    0x2850b101d0302955000400c1c41d454140d1030300103940c018106540c0c9050400a440d02c9103000d00c01c0cc40003c120b080040740a42c80456403141c4284020401030910f01700c0d000f000700070080901054860320040143e8107540c1c1c0c0740c41d020780c01040c802e04005844041400c0352400d45900620002601400700305640082d6086030280650300d40004d0640040c44a03480180c1c020301c950542c410484401040701100c003001c980098a88542c00c4e002489200441ca01307042d03807002d031313a0f040c803200030000314090007144001d214454007171107500111030000399139445070012039119410124083c4c0204042141d83c00701009000e6003520b1400c020400d10081d207000101600807030000070108840042c940b9046100e4408280d00324a400030700b0442402e0520340030350350f035200074004101642400700003062801d501000e1500b443d01a100d403884d41e0b50300f00045000b008030000494031805040420a02a1110781c1c40c0006019641c4000aa0340c80c24407600740741ca40c3d03580c002c030b1264806110078000d18268994 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 35856372 1250 35855122 35855143
    0x303080106030510050402040b04051e03210d05012607060905010f0e10170a050606090904050a050a081c02090a030320010c09030606050102010e0a080c011d010e0c0303030405 77
    0x300000d00b0740701c65400d12484203181e817102d61b01c076001140100700009664014022200308840a10803c100c840413210f80781580040e02d90715400850010190031a03400c0014098003088416500e0214000703092801c65a081e00a26807000c0e84031440d0307013040c000c00c1c0c001040d40e00c20002824101c0c0f50020080400d0380074000c0c181044104d8850b50800c034040c0000d0f006403640286042c8040d8032192005018440300000f03200d41141c00c1c07003c94191816031040501600e0050301c518035012807941030200d801d07800381c0126450b00c507035420303030011810070301640301c42d03038800c1c24081d95460035240308082c48036422092000d003600c100100c100640e1140141801c5035894245509000b0603840e201d80c0316882000131120b25420241c1c40343e43d855010b10b0b58400e8031322544042203001d450b000120308a5005940e4044250302180c4240d010840320006050002d030058000301c1c240318651a03c03040c4070003020681d2802c0c1c0d1034441680501d00140b0100c4038800064004505500e081c2d11419038030980c008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 35857622 1250 35856372 35856377
    0x5041a040501051605030f010303110a1a090c011b080a0908030a02010608060a06080a02150c16080d030209010c0f0510140604050f060109031514040807060b0103020906120c0c0d020303010617010303080106 90
    0x5a00d6101c07002c18031007000300c1e5820dc44010401055100072030040300e81141c60030524041c105102c40b0715070040030f0050b161500d1964500240c0c1041e690205958001041c1c0c500f07001c013841e80024490020001010101d09032ba0011074050314205030546402800f4110600c110300703081c070a0218000000b00c207a0f2094040354501090300640500b00141d1103682c4040700c0034050306400521a15200d03800f074040301c2950302241c50800101008030200e015503004c0500040c08043e41c000032420400d42460000d02030b10540782104c450312034071000ca4141041100a0084450800a0300d05e02485640e51000000740c0182a610303110000030250a0140402400000c6c9071024030301c600c006038009100c00d8800300c250442400c1c07908041c0b40e1600402c40c21182ca9080c0090030b800ca5100e80203803110003401926460803c0d510f00e51111102e0300050100040701c00a0000c40c038488070130001c7d050302032103e4000e540e030703541040d0004040000001d164001c03c0c03001801040003a9210180c41c0c1180c1052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 35858872 1250 35857622 35857637
    0x90307030c110d030c140d0503010e040303150906050405060604080a12020304090603030e03061005030c040e0a0501020d091a010b030c0a020a05120c210d05041a040501051605030f010303 82
    0x2c0c41c0181c1c400c4042910250400c8001ea8980201508629001a03e41c0500858101d803015040341715591016045200002030301480100003046107001c00c950070600c05d040c04941c41000c140038a103070003481da00001c092910340400308240c1c100b900c03e49030040e4080e58103910709810b064081da641c1c20800c4000f840e641781001c074a1280c5200b4010f03507020303003031a1409000040d5a030500030802c0d010103004510a028017400f2948071551130122804480024014160641f00c1504010050040144480745070281a40d10303c0000c3c420310040c00200f1144100051032501030410340c01e48942180030f2a100d80e940320051042c211420b00b541d0b4055007481c94030355102c410200807810100c003e040240103104544500554204074405014549048000c07605075568804410207004c0c00600301c071040d003208204d41d8a0b200f0268100c164407a0042c40c0e452000700342c0da08903104910741110203986a03555842400300500d40707000e1034001c1034010324100b800c50510b1003483c12800e02c180320040911106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 35860122 1250 35858872 35858897
    0x1e06041203090306050405030304060e0321090f01021207110604051f0906021813090b1801023c030402060d0504030e060a02010b03010b03060f0705030705040504020408010e010b040509030703 84
    0x10b00b81d0740c000345611000901039401d161a003180e40f60020b69003191010b040241b810394006000003541c07001810248490060150750301102c58105d0007405c10059801444d4020306804001d00040c0030b0030340902024515403502c0d820081010303e452003e20710f00d81114003440082840000d03264003091203031244c84190f02070024032070014803216200601d628000f10702e02c200000c2c440f40071004a00c0030703a070010088055a032200d08903644100010441e9a1030703400310348031101c060800350404646000040c607001143c85140500341035a4802caa403031114071b1820101c0315500c600b00c0e10110b040840941142001da0014065005007110201c1140e9140001403e144c440d152805190b14058031f6280c1d509a18040203018200718880303240290b003000e07040c04450a00040032442000b50001915094541d000103d4031380e07201038a08000c01100340400306181ea03981c402000200705080c000103407110b400500c5400e5903200c60000b846a803900c001c0065207900841240c082a92502d010f05100c00c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 35861372 1250 35860122 35860127
    0x1505030f10120b0a0f0605010f110a0b1611191b090609090b09070501020d0c1713090b01030c05040909030926070909050a0209060f090a02091e06041203 67
    0x81580300160b0180180914800d0114108800d406080c0f43c900c1808004100c580da0004d8401d03c0c4505070000c1c0ca020407811f4002c0c45141001802342c60641035800801291312a02081e03082507a40404111558602c1c014507034210340c034400007580c2c0300d0240070340300c44080c640c10074860031031000f828071046084040d4070507103141200c501038040b403101001110703121480d00004100c070380812507801e03070308030701051803841e000480004841c0c05a0041c000050584000c0340d6070340c1d40349411100d203009050462050369086000c1c00803065490f40b0b4817505850031900905403014050303414141031415246202ea66881400c407810382e81844c801241c504031a1804907658041a80004c000c00b0010301d4589045c05101c1e61450420984002ca982d0315480e443c0c08400c549030000001c10319403080c4280001400d141c4009540800000c2003032101202010208141050031204c407100c4a900041500340340c40d0644078003c40000010301410380c2035100d0b011840a10403070041061452102540808042c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 35862622 1250 35861372 35861401
    0x50a030e0d060c030608070806060307170304080706030f0f09020d021215040807060b0901140d0303020c0f07080d0e090c03061c06020304051005060603070e01270806011505030f 78
    0x66015104205618000034004d00401d481e004480060240001c0020086c41c0040c065020740d0307004028102c12480c1c00c1c0e06020340c2c2c0400c9010a81c0740018880015258010310004000b4145900d0220341c5407604030800c0121380340e0085569805180642780d42c05038603080c4000e264958103031502c11998501510403841c03c0c04e803454121a00406c2010030003004040320103400c2c50b5128040a1120840c44403c100415009001e80041711112405e82c086a1902440f01d0051900904005151800720660766050540b20003220240d0780c0602c1d010400b8900400c001c01401c9000d140542c1412444400101c6d4103074003809403030740c0362404000308a50b9034440080010150024000c4100f100003840c0c040042d400484050f40c2c940142d44c08800c4018803400f6140c400c050042003645540c0e42e9400617501c50701e241c04154104442c0110302418003907001c0d60611a0a60320b8500b8840c00d180120240c034100d1b058010440680d517842041c40382a4004080d40d40040800306214083d0751074440300b02182c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 35863872 1250 35862622 35862649
    0x913031d040e0f0a05060a0203060102030d230c090310020c031c1103100f09020913090f080408010212090f030403022206060503251b0602041701020307081003050a030e 74
    0x1406419080c3c40050300000b881140340f80300c3c0060b10600d0f50303550f035001c04a02003250360320b015810403c400450b000240e842002ea00e11901f2a0044000ca140c0e551003420700704890f030207a003190000b012140f5240400200b8184900d01d0300c10342c5405601c4124a803240942000302440c04080c100b40f6100b90b8140e003001400401040455480380781102c0602681f4030a4400e8850703040d05e4071400b007000e0002e4001c40d011004040c140000c504020b005500c02441b00c110240c44100e840160803000805030f0001300f00404d4581f0025840c4c10900c00c5040c00100040d202c040142c5c450007550320003070341c00301c00d882c12660102c5143e40c10100f01c030703034030b0300f08085040000300c1540c03030640d0204450340c100000d54040c00d80b501c406484260840e00b00320880e4041080c13400460300241c0304046804400034000c001ca88592405814180e5a16854030620b100e11114400d5035004020420708650003051903a110382b040320846411461519400d4880c40c40c140043d00708819450205031a132a142c0300d000d240b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 35865122 1250 35863872 35863901
    0x11071a0c010219030b01090e0103030503040314120901020c0c030c0d020f130203070801031e020d1704090f02030429010603020a050c060411030706030c0215060a051008060913031d04 80
    0x9200050f80003401840c000e04110b012444e00c0202003501ea443c0700030a0305076070b41521920718540b500d4805649480d2801e01032446e4050401800050324290384025005000e060700158542c0c01000040d030030500001e602078020743c410115020143d5641d42610b03aa1130f015502d80c40c400201c140469900c481c555480445140000140483c03280c1c850b000604803405180024a0344808000355003594058013001395000244901d600c0201d0605004400c10303951072200186080c2e0749040c0b51095903401d20115061903070100c1000705014600d24030066840d40380c200c0e80d401503500103030000300c0041801040c04040d40485c03080c00c840d0042045400c3c0200490481303129150500e80804204089a1180d019000d84540000c0f4a8000d02680400b00c00c00c0d0082c15000f030303510068030011000206210780c411031140000410741c1718071820510004690b80e6211142c503107041841001c51029000040c1800840542d001095029a82c01141180040900b500b0302e48180050050314105444110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 35866372 1250 35865122 35865157
    0x203091309020303210c09030c01032a090306050f100b0a02070308030115030e010513020904020310110d0c090506040e06011106010807030302011503052e020a050a11071a0c0102 78
    0x113103840c642e100410b0541c002c8034078171141d03a424050394124011044820f400d54800303030001000750b004e81c110f83c00c01d00020b500a4141002070351140b180d1048007089a000c1403c081044c420300041c0c0c05400c1e4004410140d1100a0415104140c1402c01074420710880707003800f00d030700c041c2e4901c20300c000402036400080d01d80d00d030358580e0070200c13859a0401c030301008241b130700420026504043c0a030707a12a130103440c098401a88542c00340000c030078000700f040340d25014409400c2c5040490b48213100c4a11780c00e06400e44c468403505640c1c022039000410000500c00c5544080005954a40480d4140c501c035a03045115034a4180058842c1c4610075502c0900703001e000004a42900001048001c0340e000742e00a005052006201c840800202d00014041e608425501c5500c07a1460510000e03c1c0c2515104504200ca6144c0b80030880c0c01c02c54030300c4c00252001400721209980424284100c0411001503d8018600a842c1202d907051085100a581c404901085014821b40c160b440c3c9400d00c0c2c2d600b60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 35867622 1250 35866372 35866387
    0x150308031e011508090601050f0f03010906020c010507090602030c1f0b03070e0603070f030206030a0203070c1e0b09010e061612060e010905090a050703110604082506030c0203091309020303 83
    0x2400710407000c103c4006000c4000042d044480090801c0c101daa018110340350b07510950b01400380140e000c07254150950748540e800b9001850610081030b1030395a8400001f294100340f400149448401d0348500115842440070100c0500003150607600030110409a5041800004650000e007200071034271030741030007107100020700922145060391107071100b10191100d05440c3c80305908011064000a50428030600000703201441c107900464100c884c1c0d0401c42180109980c80f4070743d202c45602e1301e0729082580400c030307130401044010003078101e0f41400083c4025030242e8039665441d1303001003442d6540400395680e054042c0c0212911200904000e0051010640320b0910304e4911100b031086d40129803400c000601d20007400706512082942c820068070350280345807a00a42c04803128800c80d4481c00c04c00c4005103074a030411440b2443c001a40d482c1442507560401c581284100c1c0c0d12070780a043c101168540015404021103070081030868071516940702d4074020100804500d03400a405110004041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 35868872 1250 35867622 35867639
    0x150b1c03080a0f020a05070f05010b060408030405090112031205060109090f051b0c07030602090a05180a0507050405030c060c24091c1b0f060204091e150308031e01 72
    0x41d841000800ba080c000000c0d01c9205104910519040d000055001c0c041140020146030003400c03018010340020560100500010302d00d0f5209500040ba1640b0001e01000075040001005004220700e900d040344036111514007030483c260102d002c410b0700e40d4940024109030b00a0300c0c3c0102401e00e040d41001f100d01c0380816600142015a000e0701241852135030f24020103201821100c4c5c64130a40040c02c2042e20310741c2e500002c0d42241200c140d02c00403800c0c0c04582a1107429101130f0844000a0602c0c40381090b598242c11941c000e006c00341000001c000a015a0b02c0c0001c105055680540310990383d181181200e5081002480b2024988501c608201502c02c00c2110f0b094095103140f03050707800c0d00c405841441b00181e19120241e010811020301c0c0ca1183c1c50000c04001198003442d48020401690380e101c0e802c07070307120360004649503550300d05058045c02108100c1c0380e0500300da207041040d24421015482c1c0b1680034400100130100010004416912000050440c4404841c621a680d40c49a00c030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 35870122 1250 35868872 35868887
    0x40b0a03050d17010506210705070501110406030b010e031c1704060e0607030c1b030507050604030210110f03011a0403060c0e01080c03100510030216060e0613150b1c03 74
    0x40f94001c040480042030a1034800100c4042442c40010b442e550100c4000f480c00d040401803101e401e0001c18840c19002c2003080c05494042036545009a96032406c01d40d01601700c07042c18403801e040001e0059189100d17103000070002c900000030203c1400150709104100d0f000858011311180f00300b02481404100110764121940071401101554250395810303400700d00305c0e60306405105c00079440c100b00c1c980c0341103c0c2e040101400e020349003503403410103207484503450141d003500d003200168401c0d00039403c0406940b248d000350f030300680b400704d103003144040403050f0500040c001c0e0945006062100014900858122001542c0c407241c1030005c0e000303003c4003900140000c54400d0102c0d0080d80012083d6070b07030303804480c882c000c0d8190040342e003800e0005008621444c640040f080c9030f400c0040b200202c41e006441c0100134031920020440e050103500103418140301070072003000c40d8110b03220000001c512440d9000140110030001605090f5100003810320b00d01d600b0800640038600000d00181607000d00d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 35871372 1250 35870122 35870147
    0x4021204021f120911060c0c0a09020c03030402060a260403030c0903020102150402210705030c010201060303020d05031302040507020a020a06080108031b010b0303041212080411040b0a03050d 84
    0xb5040149050100d01e900310b03200c0401c04100180d90b07410301c012100b0482c0d002c2400c860042011441c01c240e208042011507200b2a440340140d4003495501c0e0701e03407900c1381140c800340400a4040d800d00072544130050740c0780006003009108003070205024058901c51294482039415041481100c01c80510500300654002e031810380001e402c1c003003000520390041c4090030803268107900400d080d06010b00c0c800000e42015004a0340a40350031050303144801b039980c0c603007550a20384000c0d01c40b0380e161408244c40c04002d2202e150659041640820204e03401048440e0750400794280a076072a5950440d031951240c8070300c00207621614290070700c05050b900240700318000c3d00c01c0c1c80200e500d9442d04810348802900b4440e4460b1584200803801c001c240041848100010030800407480c100040d00090541d00a500200312907094281100240300d0026400f8140f4100340c24180d03482e0a1035190903201140140e03420703001b151108100022900c0d103403e01001143c010b01035811403d08010010302d00b002c0e850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 35872622 1250 35871372 35871379
    0x1c0e192301110c011103060a031104090203030406090602150103031e050906040b0409050a060e0a0207020102070801050c1908070c020409021801091a06090f091e0408120108010b010207061209020402120402 90
    0x4031061706000b68002200e0040000920070102d203451540d0300792004903007110654119448501c01c1e030058400708043e2000e401c0c0c0761074110085081000091500c442900035071451a10b240040000c290041d01c004401c400050040310b90380301400e4103540724420000d101d50040400200020a600f407500a402640c060040038862030302c80c1c0160f001602d00038080c90f92101070b03003008074207601d0b110303030041a200b031040c019120f4481e41c82560508561084544107500700d80000c503c00380e04050407552010010358202440c007030902c01002000102c03600c0c0002c0c0160fa50707410540540d55001c00b400310146c19411024441d40e100c0515001070300c00c2034040e01000080340800c48040c541001521110403010346000340c10503140c420849038120103020554100e000c8000c01d021086110b0300284118004c1022641e514007040080ba0340b06d6050380640c1e050b0345415022401a0b034080b4242007114050300c1c140c0c01000040c080d04c0006c103481180250b0152001914104a02c0c0906107584154000c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 35873872 1250 35872622 35872631
    0xf010f0c020309100f090905090303040605060a080606011b05061f060e060706050a0605030d11060124080403020c0316080d03050606040306021e1c0e192301110c01 72
    0x12202a81c2d20b014028106a00c540d00c100404043d602c6081c9000705803010389495408540e54840b004111002a281115160000800c101c1480340900900781c0100c42901d80b8034903a40351440f16501c4640140c43c1e02d0401c41c102d201001408003045034840603c1d002015984d081c1804103440400c02484403002c08106c20443e000180d9a006540a00180001078402e51400a003039803007000402300140701c002c40c1999500081b41d25101084030341d2300440380340c588000164059962a1500744140e1045880800740c10066021245c007132400810200142800c400316120752900380e0401288103ca81d4052148080003000c08100d050b1400890340c100f801e54907034044100d0f0880560f0700407520f2940100701000704000044142d03004081d02500254060403500444040c40341581c0800da401d003610007541010750340603841d841004a0310a030303100106140075152902240c0101c1008000c1d10b22620485031181040b100035181445080c003800030010700b40045c07201403150700200140340c0b066281 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 35875122 1250 35873872 35873891
    0x310052d0f01050901140d02040908030702060f01140d02040f09140c0114130b07050a020a03060b03010b0f22060506070c03050d050307020712030c0b040b07020d0503060d03080c0c0f010f 82
    0x1401109060382c1801401b02e4180072088140003075080c001000700d0304240e071803c0ca107021440348000b542c001c95046c3c0c0038104c1420000e40002d0406010303001050f0070742d50503003070780f034269580241c00c0d101a50580b400300d540640b94144d07400030003032050058001c8103840b61540d43c40d0b1010400c658414800d0322a45440b0058104a041c3c2e40164a804100e0b4010180180301030021100a4402503120350201c0344440000d5001c07806480e00c55108660241d2074003005400d0349403c0c0521342d04420305a440c003031400c0700c203800102499000c2c22161a850402c00c1c1c8200c0013075150300444083c01001d23001d10340c0d80c407103480c240c03c0d100c3c550300c4140c0b6503003d0302113800c10782c511883c1100d028600960050400300d080100c1c0c1c1c034406159134000c40030300504005003800a403801c88120300c0b0740c0c010341c0399041501e000d03000030313051402c0f2681d040100300c010410001c203590303594031340030041313406151401596840304180c8010340306005111341c0500c2400c000c1c9d0742c1c2c4001504080003a0070840400d0014002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 35876372 1250 35875122 35875129
    0x20306040c02010213050f06040819060e0c030d03050c121509010509010608060405072c03060105040c12020906071b03031e0f11030f040303050415050403020310052d0f0105 76
    0x80c1404903442180307005c8200311900c2c2444070100c4008005010524041e500c20045181c421408003d804034803024207001c050020750320440315020b8124002d803d942d442c0ca40085e490b40488503a180c141961640418560714058040d90454500c04804405074142400344030103000e10000d4051003440c0300b000108107410b00c008558100c0d0401d8580c0f421546a410412014000050080d410010189000d101414480b401003029861410318030140c0f1010b503084c541010340c142c0141d801203040c8105006a603a010013811007034060000d0043e220903003071000a92034406e010300601565101c2c10585040c03e8100600d0781102d10a4030760104500420244034016890700e00c13000c01040e00c000385840100e001e044202d044181030380507a40f8041c1c0d401c00b124420381142d082030300080c43c007140a02041c1203907a0050340300e407a01d0401909041c40c5d40d000035a141640c40e92800495155004030b520201014101a031515038040010200c0b0103c02c1c41410a0790201c8501081c064408000100350a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 35877622 1250 35876372 35876377
    0x604150209060a0c02040207060911010305090102090604120606050a1e0906030b070c140d050403030201060504050603280204020d0c03050a0e06070e030c09070905030706020f07050103110d0f020306040c020102 92
    0x900a0304003410305400d200284d40b69502d403407041e80c1080c1c00700701d410005a81d0b449110040c2d48a203400e825411100c8000404680c0010042200c43c3e10400090203590754000039207085950a0729194101301a915000000d044d10b60702040d04400c05c81004140b8541ca2a048074504002e0805c400c0080e40c0c840990782038072810b201c0079141c0c2d0078840100b0407141c410000746040c6805800041e082400f950003076880d0151040f1400d00061b4086014001c05a0a0186100038901268248030034189400000d4a07180b60302c3c000c045001c0508a102540060010030150154005004640382e206000112000c0c050050070200000e141100060a98809106030184640d0140040403240d890507429101e032026030801341c0d03141c4545105140981e6900740040d100b41100d95900e140b1a01e002e0504d03141400079040141990002694511548070001c0c1c4038003220400d10f80410100c0064a001d00b00340b0a010f000003480d414210403c40301580b50300190b005038401c0c0d80c10080f0010007003040b8201d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 35878872 1250 35877622 35877637
    0x90304230d02091f0b03100509090c060307021612060b0603150402090103020403020603101703033306160309120c0b0304031704030918020f0313060605040e06041502 73
    0x40070716061a0050300b0303da15665030024108044003c2d0780ca00607440341444aaa900901e42144000100242d84120740c22080082c04155006601410300b5400151103500e44449130340031b070f600070001038030840c07080040400c1804000c00d00701038240c590074090403420344070a0a890040c1040881070150034a039080301d115101c0c9040c1407140e43c0c400e400b00000780d8050f02e000c0381050340034007020004d680c503480218094148a09042c450b03d260140d00c518041c40609204642c1e042441000361940a440703243c000b01960800074180d548444010360308582c52400700680007440424003a041d84803111403d6200740c0651a030040090f42c1c1c00000c031b0480c80d401c1000703250b18a40310742040100b1000c009540c0103032003410450100d484441a034806003004076010780014a2051017005075101c10b40da0618500c010700c01c1903140620006009080d0311001d0300d94103050360064000c2c801c0c0a681e42c0400301420b00240180102e82401354656624001914155a411202800c41865070098400c07105e69 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 35880122 1250 35878872 35878879
    0x1502030901030b030102040f0b120108070302210115030b071106160c230d1205070c0209090a020406140a09020712140403021309030809010902150906040b0309030423 73
    0x20038808500440103044140e410a030190f4084c40041603200382e000c04000036010102e0704548410041e155201a0031040e4012401c540140b4006e00146c5c540018686010303411034041d10261201042141c0117145045e070a01c0003032038103c400b00802c4007100e5a01d00070111307a60303294040d03281c400d82103031140b4003036514100a00c140c0b0204a01e083c0a00303204810903001c1e403190040b030120b820452180940d0324003641800d801c0102a64031560f04000d8400c1e102050440c00c03c0107140c4050060251405100060300c58210310001a01d841c6041003011110360380504280039071651468180c00002c20b16880c1c0f407050170000310100708101c46109031040340b508001c1000d9079242000c420341d115908141080000030f0100008001341c0c6940c211014450050301c0006054039060030000c04a046c0500031803a00c0c0d051100b0207000d60341d4070b0842210410442112651114080000707480781c4a654094044004003200b0400203000c08070190085907001059002804600c10401541c15a1040c070f00b0350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 35881372 1250 35880122 35880127
    0x102010b011e0201020408030703050c0d030504021503040501020918070f050f030a110403170d06051806010e01051204050f0607020a0c0909030903060f0b15090a150c0c15030501150203 81
    0xb502a84060b05210800e4140001071605849030b01032130440c1c0c01044142c000c0745c00014059409c00c0700300280701c00e104262070108103a003440e0340012039001c00854000c540f80c0000c000b0400344402981280c000000090040d44441314a402281c0651411140d0070b010400f002d002c020380c503016004403030f680c1180ba65002d1445d51038181400003020001401a80c03048240b10100000d19144411840e0362051103102e62546641c0b00a0790a480c21038028501074100003603100340401c04904009d17040740e000d00f040c01212809000498090107400019200d10702c00c17200307000034880301007048501c0c3e4004c0c02c182c0e8120398445100381d81d900030007000200389080c1c02e1010411541207a0001007400e2080c50241c1c086940ca0301c0310415100c400885a60540d0380f03004c61a502c0c83c21009034690501c0030440c05003081d00c2d034400207a010899202d1000300141d6060689072441c0314840b0800211b52003482c41d400503483e55003d204001d10315240001181c074050000c41c2c880c05400e8100c0c00300019500552 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 35882622 1250 35881372 35881397
    0xc210914010c0b0f151210051006050a0e010516060b030f0a031b050a02090a050f010501110a02010318020303040315150f0315060806160e0406050a0506070c030605040f030e0102010b01 81
    0x100300132802031a5020441c07451024160a0360352418107039803a0300300e44c000d24550301406262804c50301c0240c11b040110038201d0f820005107800030199540d503012420080074400010005071401c5c072420300f20900d546031000c107050802c04503601002040c1025003c50b0031001660b45600e94450007a000640880d007000d030081280c1c124640e100e007113188500e050380d268944607404994003140555505c000b181d111703070410003007449010704140141400d10300390f00d686032101801500c0300e0041001904041c1c8401c11f40c1c0d0205200d000644516601408031707039607140c2d2428080460504018140c883d02d040c113651050025000301c00c0c40584442a540d80c1c1c00d10314564441816020314000200311070348075040040c621105101d0740380f00b802c1c8403844580302501c80700300401044032844d4003480340b4646103060103280c075040155001c3e500159165961080c050400d8950303892951b00091450382044104400c00007401415054a0301c2601c80700c03501841c00e4010780c00e0b02d082c1d070b90031400900c4094010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 35883872 1250 35882622 35882641
    0x50604050d0b0403020705100e0f01080c0409022803020909010e090d0e010e0409050705010e0a0e0c0a0507050d02010f110306090601030b01090906140108090d08070c210914010c0b 79
    0x2d80d0440c1c42801202c8803259940040303403d01440c00d01107070100b038010302511014100300c8d012000c019030900e04141c1505e841e03079650800340603e00030420b4286e8081011170b50285040041e400807500e008822400107580c1100a000e0b5020b40907181c0078440d080c0c0002440d51500c52100d0040718404080c24000304030a400f06d400b881f0161000e41044141c0c411b000194031680300b40452580a0ba0107000010b0401d0009414407228920082c011250000200211a8010005a0400c01000c401035490354104821140c500603031760040d1281c01000091980c858056200000316603611100380302050005607481104d020803582340340c1010410700000d000b584a03500c0280e082c0c00505054070126200d60208003140e146c2c0c0c110000c100c10440c3c0103050b41d038000c0501d030f600c00c0d10400113000300c0451210050810b00701405020038400d5181c046020030480d1302c031010740d05900c00c0a03541100e6021000910140f064440d10716040d80601e603070ba615511401102c51520b17003060f420b4903581c54488a9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 35885122 1250 35883872 35883893
    0x12110a0c140604180509190803160c05030a02030307030b040b01020a02041d0a050303060405090c1c06020d050702011b020601080304030b06040603050114160e0a0b07050f010c030213050604050d 85
    0x407180e001d10b04002c040303941200000c1c04101c46900c64400206031400c900e400b0b280c00b284140c8520010001d01d40300c400581c908080381e034408510089103218410b0440140d4144040800c0240710740000301d003600c81143d000002d544140500c2d50f050001c4020032040c041258500b03080c880c01600103004800150419030803580e11000c10802e410002c001241c401420841c504d0011a9642c0001080c4481403419014142d0080100340c003403d42c0c03070150710001d01e41c0e2600c116142c50750b160400d089402e21000e6030544140c202013080c03e01c11032403d0301c4000d00800d071a18103041e0507070300c02c0200b29030148001015416100c00100861070241952140d801001c802803a2035800b545404000c40020030070701801410074012003c0406904011101c031200006c0c51030600200604080d001c00603940c0c0c0c005070021581d1503800503507240060b040c400d041c0156a61204125030030321007000e52041d40743d0300420802c14200c00700540b060300c0700c040040b2440b50780b003107551207080f00a584001c80c01c800e00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 35886372 1250 35885122 35885159
    0x6010e10060807090503070612140f06010c110d030c03200606060c1c05031008010b0108070c0f0203010c0509130209030304060e03070f0605120106030b090f07180312110a0c 76
    0x14075910301c4c0e03900d400003850300300c0e690854400230341c1004239041c40c8152402a14000800c95481030302916000044601c0010003d00290400c54480c1022080c0b01442120300000d0748007030082c5214180b2420040d11450100e10110700188042c81015800c81400d940c13000a0500c0d01c02400c1d0035111003040001c01c0c0c03c1900880c1090155a40c0c4c0201003484460741d608403600350f1511078491070140d01448041c002540100110390404002064076a40300300e290b9404521824240320010003402d1842500c441a04000e4141d8030b0f00700d407030305c2c0c294201c000b07403071660340440c0d030900810f800c400c0318010f80c0540c82540e50164800d02050100a014212041c042d610140484200541d80e44e2450142491a808840424400641010107507800e00703000f40900140c0c01e040c0800714185010070700100f0000c0003080315098a0010a400c00e11402051100824001e100ca00340d90301c9040a503459860307856100c2c0800c105441125101c2c81c0070071078140d91600058580300307541c40c10b85440c00e0b4068001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 35887622 1250 35886372 35886377
    0xc21030d020309010e120f0706050403050705030d06181406060309010e070b030718030f0303110912010b041b12020f090402030103050a060b03061012080d0c0206040506010e10060807 80
    0x112490403180e10344061071003032498000100351410880c03240c03410312070f0702100b02411a5081000c264142000c0c001c4031511390b0700c008001103507038a0f130504480314091540c0050a40c040000d617501443c4041d00310000303491584110251810b4440c004200b00d58242a0359160300e091f00300011818544000595440740c0360800214084061000d00c900344411a084020000300100a1052041d40114410803202c050304092482d20b08507181c15030f44a041c444024101034a481040340e0100c1d00c030f0150748001c01c001d03000d59030303480742d03403800394042c225009440780114a003209152400c000c1161a0148042c0c546500382549151004100698400000840d0281d0104800302c41611188000c500941c054009040a81158035020301034404d40e0176441d00c69400780e020702c092400d0608092045503040b03181d0842200e0140740c4014580a00d0580b81b01062a19070925544c80e008074025124900c140c003500c003035a0701d40103590000101941d100d20f42244d002000d12810b0300500a1300c0e001861070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 35888872 1250 35887622 35887627
    0xf143001210f08040602210304080405040207060b09190b09281503030f08090f1e0f070902040302121b120f1c030605010203040506090904020d08070812090c2103 71
    0x291601145039104c0d60001c1d006a200c9041186050380d0a540242054460034401e461410641c44600c818007450040a21403030380050100704101c0340343d210a40320000540015001d1030006543c0242010b16140a07400c24103104080c8094907004074040d00c03403204852160f0348900d800007699425103030070751031110040da00c980101051800f420200003c2d41b2a542d00800c50750080744c0100000c40241c002500703940101903901d990803000c05c035160540c101c040f8251422214000035841c000460000b40600d0180e101c001c039a141d810f8000f0420b40f0300035141d5200801d49507ca10f55a120a40084c41044840380d01d0310702245403010300f4113004070588007244c1c4010095101241030424000b181d0003a806c240d0040c1c8002600341c0034100c001c00c07013400034500389403030000402c0c003500c2542030041c03041808c98002000c5648900300e2121032900082c0c2991900040c2c580416560702c1520480103884e50140064424000000c10141c0c083c2c02408030174008a81c50980c0c5941d001d040000354450005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 35890122 1250 35888872 35888903
    0xf06050c0c0106151b0c03080c07031b05011e0507060203040611030901090b160801090203070908030a05090307140f0d030504090c0e0f0604150f14300121 68
    0x7406007602800460300f412030306944448000d094020b0100c0c140407800c070944000c4c0c006c500c00c850000200c03604011000d0381d903220180e126040c50141d410080110952005600c0001c0c014030030704080d16801c0e01c40f180600303100ea5542c034902f00c44481800003e1402c200410004450b600a55000380c030400d40032409000a031240780594000b2180c000941e90360310900c00c24081343c0d1004507005040b003d400e101002e1003e00c01480c0c02c0c0705005403000c2640002c0801c5500d445585100e009100b800e09681c2c480c501500c000305a6441544001c1c82032080d1000890612400042c5010a000c001e00f01aa0941c001c1f05100d041c0c1c01420064003400020b00c000904200d66000700500b002007540c41408010074a000c0041146840039920b002d040c040c403050141987c0c140e52200701503181c0c00c08030190f4034440f0040b5411103981c44000424000441c0701c2c1801004640d01e00c071011070b49090800c413140b49448020100c10309220320095440311005010710b045142d214141c43c41e01502c11030001d040d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 35891372 1250 35890122 35890147
    0x906150e0f060309010903030f060b0a050c070e01030503040e0901020415030e070b13030b160804030c0c0506040308030702011404050c0105070201021e030306181005010e0118180f090f06050c 84
    0xf0460b00720b609651240c0d002d0081541c18455a0007502500a04014681c1822001c080601414564005020002031a001c01d00c00402403440280b0103055060a03640e100e24003980c49400c41e01c90b031004000003101268000030113000303442c01c1c0d0326a040601070042445a04401411701015907d8941c0070301035011910411620042419036034041058034458914a05442c0d1032800521011500940703203031041c8402c6d4002c0580e50415050715260302085d500d03061589407507405a01290344000c0c0000c0000400c03085c24065803281a1030b400030408407203800040c00d00d61400700d400605913004800440e00940c0110003030500e42d070040c41119440c9801201c07900c12a641c50b461021564404000c000315403030300c4103511a000c41a00418030043c00c0c5442d07164819900360090758103001600038000b0300d40e4400d10021580300b4080758158500e59603008640c00003601005080d00b01c505181000944190034007030001e1640d0702420408058000c1c3e1a441c2c001d2001800144103240704100e407180d03091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 35892622 1250 35891372 35891377
    0x2120a050c0706080712091218090603030806010807030b010804060f0618200a080a0507120c0f020606030304062705060403110907030504050c120c060d060305070906150e0f06 77
    0xc551312802058103015070054014030900078850040d60500001d0800541400504078403000d090616807514102084e5203c032681e141d4004c1d1042c240703810b40000c1030580c80b880c5a4001c0c10b007078039406050740740c2d20000c40c103552030f07094824040788456012500180e1640c0c400c0401c0307503480000048080d151a040d9070880790042c004240c098984030091421b0003500000c2101480303140c00c251a150445d18041c00742c1600078002c01910340c1c0c440c00a4002802030035801d865004000c03080161040380d03440640310000041d000340052040c0800070b802814008200c0b4269076954035110142e50310180030310303580304020191040b1803442c1d0030001022307160302d030103000590301c00c92059180010000c103000500f18020310003803c06040c102030001042000c10f007408070580c00c0e24440c60340718154001d14035010221030555007101e4001803a26004d00c440c0d01600c25648618151100c1669518052058840301d024070a8400e9041c1c2c0002282405952502c00504014003800c18502c030240c001007254 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 35893872 1250 35892622 35892629
    0x14030c0f060105150406090902070501091502070b0a1e020c0a0507030302030a020c150702090a091506060311130e130b0708010e1e13030c080708070215090102120a050c07 75
    0x3984090018850f9150a603400854845004483d034205450a00000d0591804c0d206242c109a80042c80d9400e101d401e411440ca11608072002c2000c40342c150030044000d502c180c805035501909003000c0303021001c0c10300a0805800800305c500791011054941200258000c030700c004200c1c407400c52800d0000310140400740c020b60081c3c0141d030f00c1d416140400390070b04944011480c03040c401d03a0001506007001c3c0381a07071803140e016200300800347d55192000780104020321000d8090500100e8842c07202036160407100c00e6803080d60701400f038403020820b524402e0003400702c05181442400c40a1000328105c4d2800c0340c1c0485000301301c2020035415240c3c0222214103540303940001d001c10f40188484203e00090b6034224005159181c850108031081880c000c030f002c0c104511845412030404141882800d1201e00c898001e0723051940e94601380781c0412160702c0114228003859071544080f40b041c3d01d03070064581c03015068014001d00300800848800760f9000409480a114091181e04500341c800c1090b0000f9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 35895122 1250 35893872 35893903
    0x901200f0a0302070e0421021e0f01060e06060d02030c0d050705121602070308030a06050319060501060507110405060103020f16020108060301061406070c050904060609110301050102060414030c 85
    0x5681c0700d802d0090800b03441360405c11750011713000280000184505e4041d140c2014210700301c88200c0c49000120304010030b0f103c00007821032003070109200c20100400d08122070744040008100e0300c2d5403401420303a6a2021280168850380500172110182d1075a00210303032140c1040c001900c1d003881584072400b1500c055030002c000910100d030784e800c0c0303402d0004595041500301021544070081d440e80259101240c3c0001030040c00c000c00030504644841c0c1144001e80310083c107035a015141c48502c0d800ba01603620307040e6101e90a007000015814042c0049854032500003d1140040000b1310030301001d003030f01800c000c0c10941d003000030034055280ba03005441040944281443d000060340001080c013840500914401c0e458508204480d05103498458200d42d800d40b0001d491358a103007030a10505112f07504c03040d08150034004100c1000500d034801420760f250f000c410030998940003610710842c0403d014031030141e4060008640480d04600103014034010020440b0b15080004801d5401c00e0041c1100f03422 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 35896372 1250 35895122 35895133
    0x80a0503040210030501080d0f0e0d1a0c0c070b130e0405010b01090b0306010c02040902060c0109030801180c050a1b06020a0906110a050a0f060905031201050f0909030901200f 77
    0x4515042c2e00b40ea40f01d095516040c001c039410050500c1d01c0b9074451b1500001e21150003000705c1c142c3e000700c1c2c118200d50001024003101005504009403181c00031402034454501e9940001d8800e032500003a103810030b4800c40105030301406c110700d080c090703807205c0701e10800e0f0b030860307100040c08159000c149840fa500c81e000100e075041707205001411002c402d0308a0385040c14207004014141e40d104500d1117101e03030115808614202180040351880c4243c04880450b5402c204101d0103141c1c06c110f015040b24610091708846200550b00b010803101074050400004a081050020003403084101c0c1c4130031585a000401c0044a6070b688004a03031118182401250b07845008003c0c0c646c015000025405001c40070304042040359880e59155482c540005281c0d40b1198201c105110142e8850a4410ba11108990f5107500110030544413890900c10584a0080e02160710501e0601034040ea008818810040d824101618010750381e41c00808a0f405181e40c04105038000f1902c10458611344408030b102814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 35897622 1250 35896372 35896381
    0x606020c09040209061014070f0506150d060b19080d090509040f06020a0c05010903030603140d02060c03060f0402030c0904110c0303060f040f0504240e0307080a030603080a0503 78
    0x241080305140200d44601441d508000150315071030301d002d0344140b040704d0001d0640b402d0314060301c00b103042c12032101d8015030101e046010030040300c5010304428001e401f242d04070b60b00c9140d05170b00109461300f6180c0100c2c2e15100c0b00006810740e00500c030076100003405140d403255410b010854a100f1540701803c035611000c00d1450031604422520050082640c28850501c0d2036154515102e511fa0340080030164001a500c0c0c009118801c0045841c1c1e000000740072105c042d041c020007900d01800103690b4040603207007941080000181281d034403034040d00581010b6441d083c69103000c0e00000d01c241d0308807100c42c40f0070002c0c0e6124402507100f5141102d82c141c540110005000845040f11480c0000e05e600308030f880e40e040d10020603264425401c8600d050307600c9d009800b080c0a8255041c0c00051a824502444104142c3d00045a00e40803030074440d4000040b000c0ca0305064035144c0203450880d8104101c40741c00709440e01c0003800144440d0401103103640e9260344d0b0f500304d50300c03140c00000080d40210500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 35898872 1250 35897622 35897627
    0x140906070801080c06070210030603140102030106020105011502060f151008010e0c0f07060209150415020c010219030503090a0b1003050118030503130f0204061205010e070b04030b07031e0606 84
    0x11400b5008640080c0211004440410174510458001901c203088284003601c003a8441e400c048003070f40c0e016200190003454048418040d400a015800144d4240000402c3d20141128101866a90350703000348203648524100e0b40341c00b8805004443e01401800b00041d850321044c68842c091515030b41e8112856240c42040e08260101030720a0440f110104299124600070341d050b40d11540d040200180e694038040005440010130707655407185c829000c500003950300c1c0300c5c0d2649080394170240c081d00e0000d41314000490701c689070b01605280d031058a02c1d0341301c04a442080550b9211f580c10301110220f0656440341034448208403200b078100c1402080c00c2c02004000c3c0180c04a8000f24071040299590550b005026400014a4025041031913000e20050180080201d1105034011744200040d0792140d10511504180e0541a143d0f5828480500c809150000d04882120000c0010b0740c2041d041d607462082d1458060300100400d610340c1c1c40b498551a102101840707404036914006483c62800401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 35900122 1250 35898872 35898887
    0x150a05030a0b0c0d0603050a06020d150e070e0105070506090c01110703030905012609160f050904060c050c070b040906060f091703040806041b17030d090614090607 72
    0x14a000e0340201140000144008440a4004409461450b26001c2011242c0b00500c49544054601e10a00c6c00e240c2c00d1020300c0c0c2c01815442c56038030042c02481641e0b8607408c0410321038801c0204000d084000034480c2c52142409420480c014505240f80c20290f4071303131174036162003039a41c1e40c042d8010501c001099a00010950801041d91000d40011440c544004e040d040c1c1d50b20865041c04203c43c5138104212000c07204108100d020210140c0a003400d0000c0e5070703510750f400305402e48105440008180030ba0104203400850b41c000340000c1c410b996030340c0c41e500601144440002840802d000e03004d0040300a2101602411300e504905403102c0c0703480c00c0003082d80c01c194441024012060910456168480e00301400e413491090895552428030601615500c203d502109043c003a001c180010021020701260381400300980551030300f40c84080501c0c02184000c8900e00755441004041703101d0340c01c0d804c440340c454092040000c44855000310111880c0d01140c92b40c0b02a00107004001031981c01454 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 35901372 1250 35900122 35900129
    0x6010f08041e02061603090603060609030b04170702060304060e060f010518100801060b0306040b0a060f1805090103050606030124050637140702090c0a1106150a 71
    0x3400300c16424192182d00d031148030811407a45100c04048a1420354a94400b110b5000c0d0706440b0381c0c0b0b04105182002003550f007d50080782c00280c1041c0c0d001031420300c58804403007500e070454800982c03a00d03155100c40c12352000010604021000348481c038056030321400a1403041d030240c540170031640501000c403800c062000b401c46400001000c01444075031540f0315207000c80300400b81c0c21041911004540200460107074010b125540c2070102c0440c400558130003030350180105880501071030456500b0408503070300c030f4021040062801c00e42c40030144d2181001002c000d14000b00f41944c1a100c1c40840c070210400d80003035449511000520507607050900c10308000c00d0000520b05103c0101001c2c030104101a84a02ca104803004034180e019070092810903a80c408015850b010302d14022520143c6040c80c210305203012400c00c1003010540f01494040307401e0a81d0040c003c042d550386440c5060540d40020010034100204068628100c1100b00030003401150000030000c1480e001d1010000420203c2c4c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 35902622 1250 35901372 35901377
    0x7080601050105120402131e1409010207120f050f0a48080d05070804141504020d0809041104090f061206090201020a050a061b0c03091a0d020f0306010f 67
    0x8450710306140c00516140c0c005604a4482c0e03450130340c00b888007002e004180c09000010906c1c0700008e01d511a6a4010440c1c0c5580301c440d40400d0f62940001802c074002e001c00a4100058050550307603251155a81280041e95401c7c1907061031104001010950810410400030961402091910380494140182c00303048001000c0e8004900807207840030902e0604000403c5524023550004110307a01094480d01e4030140c400304498a042100240341c0d0b54151801e035004201c140507442d0101000c1024070075842441d006c000145c484d6400d100e2105007100c0e043d50300700c0052107414101d5a850103a048090007017580030342c5841c00c0000c403200b21200c100f5491001e9142c82c0d0108040020500300401c2d4a0b009200069540910300050341080903800000300b40313009a0302101c2c10818243e0000d40b02c3d40c032000e40d902d40c22045c10404d1301d010201c03c1c8040d011641902c4e0800c400c4401907400c40031501510401400d040c000132a490598201c0124207080580100030050b055900883c0302602c5009072 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 35903872 1250 35902622 35902627
    0x5010522020109270510060e010f0903080904090813090c0302090d061a0307090203270618010b0604030501020d05060603040b1909080f07020a0621050901180507080601050105 77
    0x25400a00f00c81c900f8822520500060f280494509a20031181046003034040c500780081d1600014050507210a4052200424020950030201d0351103040c1c4940400c3e003507114001100c4c2140c54041c15508030283c1c40d680107407120a0003002450b41c034082e00380011a200300091083c181440801a544400d042070100351040c0031002d50f17030362403c415140841e0050390000d200c80c0984a9070146100d004000e9070948620703c000104c1040b181e004501c607444900c0d8025001c0c001c00144072101120000c2c00d00c0c1940700d0004516461080780409096001345800000c00350700590100350540c20651040d50703a81d5000c07902103a803040d40e010300f80d4060011a00c280c41d6140950354101032090241040411840c0141d43c0c901400b0303290b12018445810088c0c158440310000c0d10b400196020f43d4080b401100320440c005030480c01040c00c0e06140095180c450b98450102901500808004081e90065034990b0041c40c14000002021717030246000f81d000d06170b00c60600d03107424980201a4440790402004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 35905122 1250 35903872 35903941
    0x30a150b12030a09090b030f0106030f1103010902060403080a0207050405010b04030204060f12030c06022a150f1302040603020d030507050601080303011d0c0d060807050102010b031c0e06070c03050105 88
    0x4c1080b0050741e11228001944c03140c060080380c9400b44460300003170950f05e1b1400c0442030050740750341d440030280314841000b455408501414280c510540000350005020f000a00010b640c001c043c10759810284100c41c051669031001070b042d03500c00e0f40544812000080c0c240700f541010702506010b01000e40d000c8030401d01c2c10900d2420200000c001804220a0a06050421242d44c044803a251040c8021b1502c18502980c0002100c280d491107031820b102d0511104842090142031905c5840d0076280c04e200c50352030307401007200c8812108080340d0107a9106800300040e5181528a0307106802540e606480340f681d40b03401031401030181c000240b545d01c20f10040100c039001c07006c0c94002c8016100c0a400c1c03078070340e82c00000d9140500c00a814a0031705220000c1481d40000944201721402640240004540d08041c9a2201000008074a0500c0b094203825000b0707003c2d14201e15883c00103040c6c2c514020260312a49508240394004880f165106d400348041500c4640d100407401c40b0902c13960500840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 35906372 1250 35905122 35905127
    0x3020c0c01050a0908031206041b0e06030a0e0321010614030109020f040e13051213030b0402030a050a0b040209011d04060b150406121508070b030402030a150b12030a 73
    0x8a10014a040010026407800b0f254482c0740c911006080d0070040ba030301c80c6003034285660b4030b00742280c030340d07000b07074034216680070255007450780406510280d0712071041c41c80c55901480419440103004801017525012031942140d402c00050403405081125140c0c1500d652800c985250010789c440c0041102980489074005100030440303044131a180340040c0d444150080400320340c0500d90011030b40104041c200107041d5030340080c4590300c92254086d00d49400700d103a90140701d0702480c0320881100070084428000103000050341900540020110b801e1400300340e940030b141ca0307010141122003c4a40c0180000c5050510b4514054441d5150038214086060305210140c140140007804080d2038030880311064499070721921024425042240d595510380002904150846801100c2c840c6402010810b00c122425180c00b0303505014003800c051440e0002c850b80a42014101703a90501801240c80005103099068451803150100045154010b440401c4054002e41e0b1000705c82e5002084410025907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 35907622 1250 35906372 35906383
    0x612030a050c010612050c01030608011a01030e010e07260106060e0603040606030c0b0c060c03010b0f0a030b04050f07031a0303190c0209150307090c02070b0315040609061503020c 79
    0x55140391182d00d4041031002c4034003502c0140d006422512407455041e0030300070042140d4500001c203813002c0c004583e1f603420007822201c030070881100d10104044022070035072294120030004c2030810008902c604040640c0b41c1006100d031b026000c05061444131540c21411104140901c140850080001c2e920305800681400345046003a40b080d0000000035081101e1a40004065070b00705070801041a01c80100c4451684000110f116a1154000044d005000001100d060b50300100071340d81403909941844100d82c000f81c084005154403408400080d444a1107400d1140202c903180100e1070909c410080d00700c0d4045181d801c40c000341900c1c402c041e030b00e0000c200d0f0a9500059010030b843c0042e5402202c09201c81c0c0e9000b50f00038065000e00c05503030030070341c00c0d0031003210b0880580300141ea840103540b0458410380c1003000980c02009003003080c811900b0185520030406141c10408400c1c010000741140e0030380c2c2042180310f075503a40600c5804913851407540c0e01c40440c1030071490078194400e85a0b551 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 35908872 1250 35907622 35907637
    0x1716050304021c060f0b12190c080d0905090105030105040201090510050c011107021008010305070608070309050a05010c03060504140a02030c070507080c010810211e0302060f061203 80
    0x210000010404548500d2292250007050480385104680e00d07190040103011340104282c0b01e18209500c0300d88a01e000813a11105002e504000c2c008046194006c20b858103010038161030749200c1d03003c0000e80410178801480c071143c841c0d03180150340c2d00b08820001d401c401031300807d001c0d078035240400c0b0050760072240400981300220f8042030142034009044400b44941d0746c0101c0254205001006c0e22204200070700340d02c0c0d20850f000b400341d00421504079500c46092002800b03591000e58104507c43c056a901034010b00c42e03190114159116481c2c2c107150159210007200c1581d075a00c1c6441100340e16109940140104480034001d40810764070100071200e01403c90b6149950000c00300b8441c0321240f08460700d85500a0640d1901659500115180c640c15040d4034082448600000c02c02c43c0040d110344159240341c1442103400b04103904808106004500441d6858241c402d50050400001042d01c1c07202c0c42035009203502d142510b1116103100001e000c641c010003070060302a90400001c410745200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 35910122 1250 35908872 35908877
    0x90717040302060f070806131508010207150e0303091005040302210304050d030606050a03020c010b040e0706080a090804060f02070e09030c010b030a02030601051c08130501080f0f0105010f090f06030c1716 90
    0xa8541c2707041d810514600701e9005e040650700c0051558100010341d040301e4480c40d9511b80c1041112583c8034095100d100440e014085a00020019108d816195211f580c00901030320403981c0d149a5803040e66005010320600c0300d0300f5007000c400c01041002c10082510105554a4240006071030303c0310182803401501c4c8244203043c1c020032606801c071400d61064800550007001802405041c4010a48404480c00fa6500051071000018500b00c164020700f0b016aa1204205140a15280e400c07640c070b109200c00c8000318043c400b00060081d40100c0e113503020b0000c40001c5d540d0744c02d00400c003500310382d1503000c0c00f40a90065940f040160368081091411110240c0e850380300280d0421019988065090b0001d01d90036001c03900c00814074003185001c007515820780701c3d0b5a10303807922900f600c16100102d030300282c030312410401880903501c6030415400c120f01314108a501e071a29120b11003240c525507000500043d9566079102c1080340e004c1c1c24100f590003d040d2042079030418101400400135030ba03041c20f05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 35911372 1250 35910122 35910131
    0x1b120d09080c010c0306051c0804050402030405010915020415020a050307120c210f17060f010314011205150709050d0c0308071a01090614090717040302060f07080613 73
    0x2884000400c0712440615030740200b00c1000c520304d014008005a000700d60050b143c03040d400894100c030b00929016180c1000d000383c109490442040302071340c0024000c681c0d9540324000c40300010700b14003c0c030114140024001d030711503003010720b01808500560100c0046602061407900421408030440e152550000031003901c1860b202d50079105009040c40061034032042941c400600821a003912040209030b81e55030740b04041c0e02104550300010300b40f665042e2941d110210381c0d68038006000801031801030501207140c030035a400001a80400341d211140040c01c00f4010030405c4403d0110f41c3c2ca2140a034120a500e08185400414070340c041d0050500485491412006014040700a50000d5031310440695588810349003e0800c000704140f89401ca00c01d8000200c0e4a04990080d142582d0b8030036160b00c0b0000e554400c00c0321600016049205006480c81500d9401100c040054812402500204618100b0010310140a080241030384c0400181d40180003403030b660350706411506400014040f4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 35912622 1250 35911372 35911391
    0x308090f01030b0307030303090b01091e0b0f0604030b0402040e030309070312090f090c02060c0c030a0302070614010b0304111903020f040e0d020c0a0f0302210c060f1b120d 76
    0x30b000f84142400d103036252050132000000c00d9810b82107484464032603051001166669850760b010b03107030b080c20544400c640104038140542c0c070a91141c1d141e10300080038600200600c81c08030790743d0b07800b90f0000c1c0c803505000010401582001c0c064164074100a0004610314900051503d4a0305040e0000a0004001d6910350001c28401d036000b10150154149140e11030b95909034070b00041c00800d036010054080c0500140c06031980700309a441805807800518900014260102c0080d80542d034200c560580d2407941100040748400b1160181c407800c01055900c1c10709007044042e1100040d4054454503103029200d550040851841d811240d06551000c0040304400008000e0002e11001d50740d944515140c000c5180c0d40040c03a4110800c054802203000d9441d0740a00c45a90400c0c00041d40015207003106c0c070011040c40c607101100e6141c000655810502000000d42a640588124000208046080c0541280f4040311030015142e140007000c0171910103050762000d00414821540d00d9540b1004e01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 35913872 1250 35912622 35912627
    0x11030a09030f141209030f060105061804090609050304180912030207030201020d0e0601050f04061409040c0f0e010e0a05090a03050a0e0405010e010306050106051215060c01020a11010b0a0308090f01 87
    0x402c40e645501058a541350030702c40850145401401005200744982c00c200300401c00c01240c22816600050300380307450882d12104100075015034101454009a54000340f02c040303121032140700c91062040c3c0155a07140e280c46c665500c010f5003018200b1a403483e1141c040d0028886e8a9100745e2540d8030f04001d40c5407101401c0c10b0740213000390004080d109081010911a82c200864a10305a420446542c7d200c02c45000c28442155254026401040150160100146028080f25603c00e11410710704107a51340303e501c000c504030030b03d600801444a0320401400f80303040181c681a48800c3ca21820401450107140c4541e6481030201c018050160010760030303030300c640301d6418070040e082c0c0a8401d00c0b4031753f940c100301c0b804800d0901c0250b030750500c2c2500101c0d01030f1142d0b04894040450041001083d00c604011030043d0503e100c02a60181040200800c2c400c402e00180000c01c2658030f0360309860000003442c500352210007a44501c162003500013400010442d109031501100c041e42d5201e40700c888007005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 35915122 1250 35913872 35913893
    0x6061509090f1107050601030b0106020f060f0c04031208013f2904020906040207030804030f05120114030706020f0307080f0403060528060b030a020a031103010602010c11030a09030f 80
    0x14810f80200080c4100c02e008000803804d04981c40f90181e02d00603a61a0b400300d0311030b900502c0c080900c0d0004004140c00280c41c1500c2a00100302d9aa41440c15507256110810b89040a00b0b841c0821490030040003c000071014005d00341e000780d48004500800c00c0b00c1d84003955a0000d40e5222100050004014030600030b2a0046803e07a8042c841d0a0fa00245e10104007140c040760101d00ca00e62a0000600a00f01802918921903054036106400e8840340d0741905d6002c0b40342415402c02c00240300c402d8040800040050081603001c001c01c5903001403001385401c0c400740b500844150b502044180380c50803000011502c0303ea4104038142d45070402c0e20100c00c0e00788900e17400906001d0a00e404c2c400c180140003034030b0324800c00540314961030210700c40c1d590301614614030a6030221030301400003818408158009000030301d01440e0020780070680d0b1804016640080c0c00040040c4e54032a20a501c00c2c0e04141c010b501041c0c030200450400480700c800400400316400001c2c41001008020000c0085040d01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 35916372 1250 35915122 35915141
    0x2130510091508011508060609190501030c03020306060109060206071103070f05010c17060f040b0102030702030a0c060906030b0d03030207152307080906060108070c0c08060406061509090f 83
    0x1c1440112800c0000c40240d16041c05116255480c100001d00701101c0d2901100450f002080689525034640c0100080620000c00300d624115025000414240341172241a028500c00e40480d1038480c118010305281010041c00d490610002400070710006400262156004040740f07089041c04001555190450040640c02044401c440c01500304100048d0412000404280c3d5035260700301141200306803c090646070140c0100c00820100351a00345500624154141801240d1611070707658046450003941200585040001d240180a4140c2c05240c6038018915440c0a000643d00351000600c19016540001c061540c0001d04000b0414801a204042d9038462001c1043c0b000940348540c0890b009000d460204c02240c0000b007041e13000c2c09190307000380110401840c0941c0c4a00040d500e00c20040c0c114024041540b00340000500e0107403004000c0c2c0b0104c0d010b41480d00389450a40e06441c0d050308040a680d01c6c164048420381e0703000402c40d045a800c43d9004c034403086d0035400306000b17044410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 35917622 1250 35916372 35916389
    0x180503030a0209011b0803072a05060609090706020c0906010918020a14120601030e07051512060904020d120905040e1f06050a05040b03031209071403030702130510 72
    0x4029504129a003e031400c02000c0e00c400e401c40c0d2000c10038142c00031502c3c000402c0600c0c01c0c401700391058441c60003100360030320a040c0030f010741288001840f03030760450100c1120b03207074804410490903007880c5680503040f481c00750080c451541451400b0751a01da4440015003d2003070f18000440c2a80b2030a0b41500400100c5280304e054850542ea000207503124011403c0860f240c0000340c0340d190b14040c12105002400740c090b14030340d1618401100076021103c0a2409481100d81c0802e155948500b100443c10000c900a035440c2c02d4243d45044803a002003040d846001c10340c080002503121007190385040c6502182400c2c000c0c40000c01540c0c0030080b0f400003a00189030140c881c220f2040011105103c80055001c9070180d094010401c003614503c0c06441e0b000b401c5d41000b00258105138102558808008082e03d051408030b124118284800303c60828840d4410502000019022040030028800503406503260219a030042845c850b0f100d856035010a544800240785820b4584201c406400d110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 35918872 1250 35917622 35917627
    0xd0b0f150904023013030815040b04110405040f020406020307030c0302070305060f0406050901060b0405040b0409080307081609050105030f1e07110c010801050a030303050403020a0b090106030c06030e0a0204180503 94
    0x711303581c0184030134080c4043d100310821008999000c21203090000d01990542c0c80502070740c2d0303035142c604480517120040c07504545c41c0c40b2110380580d614080d91101c4964101d1050701d03075203494100000c4d0b0366031440740700140740304006c2444034590100407501c8180d01410300e002c1d102c00614040f45003986680c8080c00b68040c0e0400c1c08101e059030350526015501a04086c415030710f0340c1c035045088030118807881c03240c190204020890f504068111708da12620060000400e1b41c400e483e5010141d104030b62600c0011025001c2003510480801c00c407450107050b140c16400c843c01c0a0028049100c090510316010b4506400180f0001241c03002c400315104a00455810f400c00d00005032100084000b0b00c1d0450040c170100034900c0d48100205412280c0040a411005146442c150024000940280c04501405550002040480030070900481c080000000c4007842d6040150601030590450780406050411181042c3c00000e0902d84085d0101c4002030701030002c190b0840c052014140003040340c00302 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 35920122 1250 35918872 35918917
    0x4080709050a0e0312011e030b09030307020111030f0f04080f0703030902010f020d120e150414010501120f020907021c05030f06010203030c1c1d030d0b0f15090402 72
    0x20381c00141c0150741d144800d02103200c040744015140d0260010982c207550381807004010b81046444210b25a5100c20909a5699140d849512001c4801c5540b07800c581e00001c01e0007141b5a0900c1030001400c43c1c602801d09506210400458400000d0500e01303e152a99020409110440701182c25511241c00354507070710902c9240150141c10950002d0f0301152000544d081e12070300225210798180050340e515240300b44010700240040c8507000078040b0074441d00202080c41c030340500c0000e0040d400745c0c5907442100c0d0070082650941d00160445c04031914000102c000251043d8044840f80354106c0700769060799102030080340ba00d05440200c16031590722044e000742c2d158000d0007e5001c1d03d00c520340f0540781e64803c001681e40c0e2100740c500d014000400c03c20911440c800301c3c0380980045039498003041c841c443d9000e000100305904040d40700e54100049030001480d2074410040044e4089d42c40050710f880e0310700041c803540740040519100460014040c08181e41e0b40d8100e840d2031401d180b449104221 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 35921372 1250 35920122 35920139
    0x70e13022d040503030405040203090f160801110415050a030e0717010e0304030f08280807030b0306010503120a0201020d0501080d0207090203060607122c040f0608060a020f040807 79
    0xc1c05074844040349408540810708900031000c0341c090b2500a0025490030f460401440003c0d84014040c00590142c12082d04000b40140000c0c0d038410304180b0000700581c1071060090850b80039404441012000708002c001c4032685a4805c180070b0003506245480e8008880c003640580307403400c2929954000d004011030301c60250440d9007a9825144004c100740d0318580d80e41581e0384503030b00001d03100514004100000600e07000c0240f5043c5c6013071014101012101e089201c00125040001c80812600700802803140d80c03522850301111700803802070115502d418046074440300c9460584020000c00180262418000d4045030b5142103900c000300469030f03558114079100c074802c002c41c1c00103000d00b48000035a20018000e032800745100a04541c42c007455aa1603103c4c826070b6034000c1041c418410100c1181643c52443c4681c408540304e1044070b40074104041008981e04025180916441e10400340011800007840d00da12200008006075560034000e042000b03402103500c030700060720400c00301151406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 35922622 1250 35921372 35921407
    0x607050114070302030a060b0309061b0d02030a050609090a02010c02060c0f0307050a050d020d080123030105040302210f0d0506041e06050a061403040605061f090e011706070e1302 79
    0x2200300d0400605231101c49000071480141d60050560340305d500426a49240340001100542700307041903038505241144900d090342c008076440c3e881c0ca95114200001401d0603d0401e80c018418030150420362103d03800071300700f20144030000e8011080880c01d610405803c10181c0d43ea0b81001007100e07140c407200d2420030b64a0b41401c20454050003030400003582c19000003000c1240c040b840c0c0b42c008160f801c0461a40071608040d961050b03c0030a80000e96640c0c0342882420b0081c2d02039805000400c541e030382003401040c240901c0700701c950401c00420401011a50607a805004a184003003410344440e000100500600310b07074842d0001058007865a0400c8030391124003160000d603091000e141c1d0365001544e4520048004407440041000091300017802c5601c211303840000240710b9104203a00c1d04510401105100095021079404041801040c082c1030415005001994480c1a046000070059803a80b030040d10740001c0c40403451100d9540d0769034106202159202100440d25503891190b14030861 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 35923872 1250 35922622 35922631
    0x804030e0a0e061002010b060307050906120a0203040c0b0306030a0f050a120203120105030703081617040b04030309090507020304030336151d2202030f0619080c060705011407030203 80
    0x135050803485900440c018051403c403510001c1956085a89454050b500369128620080c0c1c001410840f9111481c0a800e51501a41c01c00e240140c5928007450b000e5004049074203d159035090600801c4020740c0c001803480d24040d031002e4501d8200c00076142040c50001c041800908008042648440b40d65000000d000c25044603124000b42d66601c2c810300d40c5559680c04041e014100801100000c03410446001c1c030141e00c04e680503101503119481d0412150419000340b2a03c85000a0800038594000200000380481c0300041009003003400f0043d60b20b1085220040520400200da02075000c0c591450030790cc071100c100007412012504420f0481d00c01b6600030314404191001c41244d01d00c0c401c000925109861420a140007050f40c02000806511880320282481000240303403a2400c0a00195000d50708001e040080d038180041040110150980440002c0521400070440000c0004010348441c1080d1a142d55038041c5041240c09042c070051510440c0c085107041c82603070b40c1e0550086208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 35925122 1250 35923872 35923879
    0x5070207090603020a051e04060306021e040b0301030b0405070b130501110303090d0e0a0f091506081005090c0c06070f0207061d04050a02070b01030503040315060b0a0804030e0a0e06 80
    0x58035207844020084070340d140000b0b0740009505a060156043c000c8821b10120003103100350103030302d2540c1c0000b81078401c950012580360745c011400c5e003c9104090100c0d0921000d611030b250510741808426072823400705102c003034811b0440401040502406000310f401519988400c2c940d03030f10302e42800f140c480c103840c8035984c0060b402990b048070f003280100c1038900880001002c3e0010f140d9007001121010b10305104142d110b180802e0002d48145070b07141c2d480040ca2040070200b00b2881c0720003030800c800e040341c5c40300c418000c0800801483c52080c28112003600c034116094045900c1342c43c1a500c842c010342030811150303ca240180b1400507003205104000c1c102e19822201e41d10b448041c100e03003038413106140202e04030419180250328640b03600400da002d5540840103041008540b29865160001c1c3d105661a03040024240207000e040d9464480070641500c00f407103083e142604c02c080510601c1d601c0020005110003040405204550152400100925600c250354403202e100b85180d10584e1410b10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 35926372 1250 35925122 35925133
    0x601090513020118050303040e04050615030d050f07020405011e0506090a12021f120c05190305060d060e010f0f0b0f060705010212070509040e0c130e01020403060609050702 76
    0x24224228020107204010680c0401c0c00c1c50115070040d01c2052100d5062110780c00340050100e0720b920100007030f06c018490001082200d08190500608181d400f0301410305c0384001d98a0305d4003030f0320001641d0619070007910300700d41c1d200b80031211141940602d0200030b40c4503045c8800010702d801520b100300f0280a002039141c170032507034400c10081c0602c6044071aa4211004142c20407503e401d0070703d00c00c251b600242030310204e40d031145403440c0c044402e03400e54408100001e4451050103600d00c1443d042c01c004d42040c614021802040400721040f45d540c130000c2644071700001e0000e440703901a00d01c180364000e800307224a910010410380039111004240c01050325080003108990703658054042c2c2458060901e003400b428281c01d04c110380d070120300f00740c90540d002c20860f15549101550144540c1440d65820744409168007048103540d20f6124481c0c041e03101e281c031044140e81d1204800e014540ca1940014040c0c0c9081100780640141c0d0720140400e07103070005c0040c0020071a04400d12855081e400c1c1c81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 35927622 1250 35926372 35926379
    0x307050403141b040f02090d050102040303110703020d060b030a021008011e0308030105040c0c140a0b010e10050103020a030b0a080102040618120803060103020909070f0201050702011404080a0e090f0402030601 92
    0x81c0c1e942555003c20441546540b440d08490910b9806461615a2124050700d420412001f1450341c0010030401c91740c0da035000808200381a0710591b000c101c02183d03009404007510b59000520343d00108200900b45a60344d030213910903a9000c01c2807540040d07015190440030100c400010705100002d12449000c8580c01b9521950000220308603010380b54071906442c256403c100a02000f400c011b1039010a014081203010046004100c0c07054481900381c004062418540c40d00000d44401a8007288815042109121079184000e803688140d40c82071030010707128003200c8003c40c060203040001c00d820030b83c0a4008188030700e041d0000d009440c0c1d02c1e26400002c0030403400300b841e03070101803103007466103010b444103000040c22150085800c08030500d405401c103890440024101d80c41600e21002081101c400325100c1a0203000300e40d031000c0030303000800900803180c0b503412200701c0050000b40390352000900e444441d40030b8030b10102c0c4140040c102402c94503040000300444070040d9802c1c1e100703109400c0000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 35928872 1250 35927622 35927663
    0x8070206010b21060114070507060e0d02061e0409090b0906060f0d060903031b02010b03060a0204050a0e0a0e01060b2d09040b040609050925050105040513020f0307050403 75
    0x32460580c1003c2441003454140e6000b9456441c098103481c1008081e81103102e0703070700d80c0034094400d550040c0068000c240c03030060060f0403184c03010b091500840c0403006007000360740c81c0d00541c0d1480400908180440700c0360501d80c0030901c01c540114502d20b00c0c0040c59010300a054007030764400e1590600f00c68158032180d00308100b01400c00d202c5907020300d46102c898001002a000f48280354460f0030089801c1201190607224250b0007a400c00c0180e41d1504600300c00e2604001880c0c021510081c01c51070981401c0118002d1041c42c0500660100783e40c02041400b8040d07880300c002c00743c83c50f008000e81c9442d12081513035613101c003a4642c070081078071381c1070701d550301800e021011b140c084800a075161280c1c00040c013000d0b104025031594016620310001411740070a001d01482001490302403d182204a41c1100c00c04850710b90b441c1003040250414003559070841c08a42c246d890441c1c1c000d28120380031401c03001a00c1030340c0c80d250342e043c4040280149540c000c070140042c0c03442401c00d1008501b904981 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 35930122 1250 35928872 35928877
    0x5060d080f0a020106030204020d1a010e1c0302120c0115061701090f0e061006090906030b0106051c090503040e07050c0a020402160c0b04050906090912030a06031208070206010b 78
    0x50051202008002001e21460000b00419070860001060b41a969000101241c0116146540c11900d40090760041c000c0204843d130f0804090038a030600b004448081000e0b14024000d90040c3c0000401550502d402001360742c1c001d0b10044081540c450701c41c02a180a0001c0042d43c18400030300540100b1041d01030541c807400c4001d07c1c018241a40c0c40e001c254800f605c262140c8180440d42c40050407082d000034071039a48606032022401604520741000201119030319804803040d14600f40007400050080c0c2c600d1030456010749801519400c50030014000080001500c0802c00d00d0a07407000200000032020b003040707880105811546944100c0c094400c0e20540380d41100e5900401900c0c00145030a601620305511421300c00444040140d94078000b4003000c0e00309035030100c0c0c0030904108501d01181c0c501e40c000001e650180d881e06040000c0b550340c40701d048500c41070300804000200301c0c4425501204c000c58001071a19442c00c9690f0303010f0304000c4151044d030f0042c0555400452002802c404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 35931372 1250 35930122 35930149
    0x1080405030d110c161401020d12050c0909130b0601030204032102030d1415010306030203061503031c0e010c02011a0d1403071406010807240c0b070309020102010506 73
    0x9546805100e041d8a0000e0076160000312100000344529134424a0070403421080007a0040003401c4a401c200c07042c0319140304041001e0455204a000300d215644c4134201c01ca52400c1c10318045140d4451480f0000b4034003456608070341042000d410008014a44c446444005004506d030103031640b20b1900441c264401d074080034204860f09198012031290300080483c1901e85c91055038144800e030300c03152083c0d564903c16030380d00400c0d00083c401d0104020f0303100c106000c024241040094650b9011a8a51a00800e01c0c5c9131101218100740301502c052044803100041080c00919074069440c410b0020000c00d9a0708200d58605181080a40d00510594401e04581521592104201c1c01005820309040314205c40d00d5118000c40040d86100700041c0c072449114041c1d400712b01c201103050a260100580c0318002c0cd41c0310f606e0411a00e40012107a815003030108031000c401c199104000e49620840c0356000f48181c8068013000101949541316040301c902c00d0b402440726445e0f0204100d66100d00c0c48 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 35932622 1250 35931372 35931383
    0x3020d080c03042f0418050601080d02060105060d0905030a09030b0901050c04090b0105090a0305061b040b090d05030c1f060e040215070507030b0103050d1205040507050f150301030f0302010b010804 87
    0x1c0100880c0d2001c09034145443c2c42012156082c1208080400d06441e07072104031540c4440b41030b46c0402000307014008a27025003504401084425610b12000b540c607c810f00c90940185400136000c01c0c501010b03041a1941d80e000310450b541c1e0307002140010140c00c101c1c801500c08812280201d2640344040c09040e0080106034803407414213040540e207400500c0d40c2100303d418800c0403c501c041035156091040004d502480181c09a07190a102440b07848101400320304031040208820b12074410f41d241581c000780c20a03102841030b0398041c81d0036869482640080f28a070f204e011400080080e680c901c250004042d01801c1c844c00342c4d65504404050026a030003540701740c4011003800c41d01a032030050504580950100c0b119566203854401070000d0a800998468020003c0046401d400910ba080010b100701d82c10080b0340f03456140d5030340b03502d0f403405580e1041401e001024003a80c0c502c00320001c05c140f061242aa0f950396480c00c0d1094078031950086000d9420000e0241813036000b01c0e4018481c94015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 35933872 1250 35932622 35932643
    0x3030907060f0e1f030b0d0c1401050a020703080a12020d09050709020903070504150b07110315090a0b040501020c03040603020c01050a14010e0a02040306110c0c03190305090d0f03020d080c0304 85
    0x103e00c604a005200c4c00c01000b01036540038441d400b5a2442a11012140540e04483d407182c02c00f1103081120100610b2141407010030406c0302c0d01c19a000400c042103a410012150f202d908002c41110600040000e2946250000ca60f820180e07840c1c1d0710211001d07216200712240c5613a10036010050b405100306442d4107070002a801c101ca81001d4105000c0034541c010204507058564500039140d80040030281c07820b4040d035440e03d840d82800c0200094030714900c18500e1240c504911021b5807034109a80051050b07084101080800c002501911400001c0e0b5040e6900c591f2140c030014001e41041040510075820040810329080a51007240091a421211141c485c0c0c00c04030030038511030020303107004a1541d08100c0003000ca50345100d04800802540020740e55821b0316610340b803030030b10284c00c464400d4118058032000c01e40003440d00981e4030384c1400d2241d26408034000107804d030070740b010001d04030b45104180760701016400306200381d0102554407818031a0b00c40d000c2e00b00c42c40c04125001401c0c00e480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 35935122 1250 35933872 35933899
    0x1b081005090a020403020901030506040c0e010b0405190801062c060603070f050d060308070204050702070b0901110c0907020304030b07020c030703060506030a02040905011b020c0a0509071103030907060f0e 90
    0x1480030750b607010861103009858107982e81d0210f42103110992090702c06030400300c02c0c8010090350440103070003000090140c04143d41040b80e841c0c586e10451141074415111214070303d141c400c54415610080003107100800c20345a40d088018030707030940c544800c00381c4141c80381c602c1261000d0310f003014042e0078050720340360171951144d10654111750010941810b12000b40000251100f5600600c0043c2d48500119034441d10f4901c140419100060070b1340d805d542040340144684d002c6c55066903000f2100b440c040c914003805140c1c1d941424040d03405c1d070360080b030490200110150000028002c0301e20034010314500d981c84c030001301d84502c44141d02d260b06401c80c51040000c1030316a00070359003103200203043e5000f0b5449540010100d070042281103843e039440394141d291121103801140c00e082001d00251608c217040d20006002c1303002c14021a480303682080041120b052081090102c45404001280e50700d0418142280d981c031514032940001984151646c5101480b80000c00c9440d000940f10680b030008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 35936372 1250 35935122 35935129
    0x501020f0105090712020111060108012c0c01030213030807051b12030f030c0c0d020d0e01021b061303050f0f0c010c02012309040903090503011406090103030e0f060307031b081005 79
    0x4403105d040c2e04010340381e00b0b2035044d0007007400001c2c000c060800001401030565004a100143c12589442441042458201a001011031415070b025424a07006a5a064804d90b907211101642c001801c08200810f4402c10050f000800070f14285410450780c40c81c1107518200160b424100380040042c0d0001e200c0400304040800180d074002003101580390030002c04034042854070800c9603018005038008541c5102440c0c01c40c4109804050a00c05442e100c031605d603081c8041d214410035640174100000701d180a400302c00d5142c3c800f4607441002d9840301c1d50098049552a100c0c0d0f03008903414012401c0c5008258002c0382820741003a4180c44960807102c44a81c42c40d1315205a40004507082c104000c1c8021035503451265234407842c0701e80c03070b089400c905110a0600319142090640c0b903001d002010b00c001c9540e1075984904503a41451b110f4211541c0202040381c804c80741d0440b94000e10084280b08482e174058002c0300000710b10040c00d410116030b0f40c81c02c8581c0e01042c1c8844410002c03c080038400b504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 35937622 1250 35936372 35936399
    0x613150207150c02040609021306110a08041d01060822050a121107090606270b0301030c03050d0e10030902060702060409020306120102040b04090b04240501020f01050907 75
    0x80034015105565610300c0818550110311004800094414403490218074161040001a0081c441c0031410914100ea481003000c07002c0c045c041c2401f00c10058042000c2040041030702c0507034444952900c1e1369130350401240000e44403a9225582034142e0000c1a00c81c802c0d00068850500480e485490b80070040d03c00f200340c0c0b0000021f40e003d0041c105490045400c00710381c20703842c055540d03a1f00e5201407900710350341c107103078190708850139240c100502004000d40c40381c0f060340010b0b40310200d180305e01f00c14400c042c0301c50200d52141d0607805d40400000244002d290410003224000c005440000103030704001c4a01c00c02e483d02c20741c1e00414008640041d284039a000e6240d540c4050300f0749103408c1640d000102c0039007040d1701c00d800d0207400000304203c0d400d0000080368081d0a2000a500301030405100d03028034017684c05a01c8007070b99103032441402030f034860f0400351121030507100040212011007081580f0f07032202e0241c940580310354000316030784400501c180c522500100d4042c001481c02c1000002562 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 35938872 1250 35937622 35937659
    0x16080706140108030a0306060206011d073006050103231503030f03011409040302030d020d02070f0506071407170a05120f04030212070809040b12030d0b0f0613 70
    0x9591415900d00752506490328038080c1c40810011034a034051003d00800380c03041604500115002080100502e5103054060760300c0d59048480d0071034030344e660f9000b00c07420b0850441e16034801444c201c0740a10380c25184440a0f01c40c880c2807050081e40d880f000150107540500c4140840704104140c41c030f500300d422603034a40d040101c48501c10102c03032080001900d550007035102c1c03c030151000401040030300340400c00e1b0301c40c0ba20103807400341c5685010b8a019490307000b00100c41d525550009055811014603604980003180d01200f00708010402d030401e641e0390041203504502240100090240490081041c0d6a206a100344d41081840444900c030180d5004404514103010f400d10010001c084074000061040d94015070311401485c050900904d40b903961643c130f081814081001001058019048440209060f6804200c1d00031000102c0d2282c05111b445507014000890380024490850b0010045103a00311030400710b40b4480d5003045818803820303ca4131203810018100300301c2100f1866418080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 35940122 1250 35938872 35938883
    0x10c03030b010203040b0d060e0a060806070c051615020c03010b0d06180204090b10120812090a05031306020c0316060f030905030304031e0908070501050d0207080c0102040f0902160807 81
    0x4083d91010040407c2d00480702c0301c45900d1300c0305c50034020888420401075205c103010100b03210f8130b807401ea00940c50328400341030b0700108154020844244a01007055400d1000c0049407520019a1141003400d100c80d2603020400500420b500c0302c1051030140512481420000c0c40c0c0c289810003640da40d40245070001c050080300c0d0107440904c0141e92070344144030b452800fa940c459402c1c44c180409080c14002500030080101603001c8180215206200355003442200b01c0098406444640e110b601d031030325500000f01544400031340b40c2d2807400d10f0080300d81190302c7e079000c9030b003428911000c00d030300e80c00200750300e4400030002d003c200011445440b50704c031841c1c01c4e401d0020301200d80303440311400d41c0d0040f123040d0302280084040801d01c4482e03600c80d01e000455440c00801309410b006206889a80034491a4108100815560000c0e1010307412100701d5a0b1101d031041c1c1d15030a11419038040c0d0098403e07440c40820b207030000034001d0308500848010564042c000752031400700c0d40e907031039079500a14000d864 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 35941372 1250 35940122 35940127
    0x506010801060c03030e0a080c0708030412060f0f1104140619030c0c08040e0f070503060307140609090a05011703030103050c010f110102070b01050901080c0306060405070c02101814010c03030b010203 88
    0x1e0384031090115a47e00303030064440f1a6200040d01c4860700e460341a40c024190b0394010002040003041e800b10120020341d007c000070a0010800055101810b001080403851624010b000c5254240c441d004200300c45084089042201d584410446140540581041d24486440905204600c40e6100700c110b50b150b405c00c07040c149450f0304ca960440d0843c0d0041c10a5003003100c1844880000c079404140c2c4041c841c0351107461842c004020079200c8220b44906001141c1042101c1074030b030307501b2042c3c40350070340060b0a0320194a004850000545420f01c903400080c03e00c5450200c201e4000b00841e4162600a801441d0f216984030045039058804411a81081040304035103c1021080c001001624000d06903040076506010401c48550300692100d0741c07035130103600003007565200421f00c164040412a400203407031740d805c00c06a8140d60812002984105110000c14804c1e4000134041c00b0882100b4100c0280d54403a0300a950300041582114081003480203a00006482a04007410780720042c0705690 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 35942622 1250 35941372 35941391
    0xf01021209010c0b0a020c07151d04110d02031506030903070b1003020904030305060112061a0d06120302030711090403080f04020a08010e0a031d01050306010c0f0819020c01030506010801060c0303 86
    0x30144d00070344030103114030740001d00880100010441180070700350a28402c0c03484c5071150b102600700d80c540003013411b8030303200c000e0045441da483c0e502c02e41c8948490a5095901c1b00427600b800d000f980308442c014640d04024000030503d080400649201d54580070095140c41c0300ea03110365102c0c103030003002420700d00d40c0c0b1040800140c075040c100c035005920a0b1400305003402d0110001d031518405058a0010030301c0c04204005400f00281150045281c01c1e10f0155a000c0c1512105c02408040c2c110350480c04001a8000801d540000104800360007a08541d12000c0c145040154424042d40c020300042c20200125907200c0f900c07108030350402e2000704104151680c0b00c040300d01b0f4801908617440560845d40a8005050b001f058040c183c0203403036003181040c1000c0e80068464040500314038104201c0d41c8541040001c190192580141c21401c0c050302d6280001041c840061040080740050180501032002035009004150103450140c5840d01f1580c01e08104480703041040b1420b0381019281e14046 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 35943872 1250 35942622 35942633
    0x30414010c0305040308090a0b1602030403060e0604031206030f03050c19060e0f01050108030d0e0307060204090b0a0803070f03050c01090b0103050a0218090a061505040507030f0b0f01021209010c 86
    0x1040c212640e403400300d044d1620b0b05010342803c40040c019122504000700086c0000c1d40c02d04201d070301800801d49140165042c8108910b50700880d00b00412462074200d80b20400e00d00001c40c0f0b8850740c4240d60f041a410300d803020b45000d951284c0b100800c031500d0301150070700007401031020784444400710085411659442040c42c1003070304a2032003650502c0c5d030350101d181007900a011404010301c00c500280184e514001d000c66413407140b00103801c9115030320803500c0c0e401481031040f50f040d1608a00b065443c0c6451710109001440300358407052003410030800019201401005a44150b60031000101d071400c2c01d40c1b030984141d44031100803055956241d00c401c0005204000843c081c4bc02840104800d0140c1e2040c0903d40c0c80c00302e1801002401b0904004941000140070740300c00b40e11070004200184a904107009000641d040315900900301400c0040503581940000d401060700c0105201c2034843d04140407207141e00c3d078244d90042e000301074620300d0100d00000800e10200107240801446545450304d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 35945122 1250 35943872 35943881
    0x30b06030a15021606020d1e020c0703140c100306060207050f0d03081906080309030f06010e041104060f060c0201031406060403030e0604050303030c030f09070605040e040c0e1305011a1503041401 86
    0x80c2d47d100e41d4416280d540000030040320013680405040452603c421074020300e541d05d08501c402400d00c01803c0605954480a006100555001600700e1404030000c14024007e8903860003420010710650074000307524a0a010340e07c0782c1c944040d0a881060087c0e40381101c418000612480580c1214292400004141d1288600034a1413402641c0c07290441c10070107040c001025144c0003198840c0b8018411503404210070341d00558085100350010139000301007405800c0e240c5c4100c03c510500030b40055241e030000d50002e1741c0c0d8800d9804001000121601d41c2d500201524640d0f0048018082440024000d2070100074101c0300400260400703554500291460b802265440340f814000300a2100d50345003140c05640003c0240040d1100c03c0c10f020000300300380128031840110f00c105038041000d000050106c03002500c0403160324049860a9041420702c8039451108541d1903190412030304136802d0b02d6814400444008052040000c21100000c580d0b03040540103860500603400c2040f44103400341f04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 35946372 1250 35945122 35945137
    0x6030a08040b180904020f010503090f060a0b032104230d08130b040e0c030411030d0905011805090c1b0a0c050a0b07030f030f09080310030b06030a1502160602 70
    0x40b050740d404400303c400003001d101031a40341c0100c0d100030600006a13207031444a280c0c4c0600f847c2c00d03603e83c1e640e000168500042000e02c5141d0f8010074081c040418266004100c0d20710050f0221020041d121010010a180083c0a141d000c40180800e0154600c1c03103800850041041b88168543da501400060360086150710440c2c0c6100f00103241d0742d450440900e180010091761000600300b600e4a607014410101c0240700c86e2140c0d40c00000541081040c3c14101680301010301110fa409150140180c4554050f00515002c00c2c04441c0c005801c0c040004400266000a42000c0854440980c4000250088001b4a10810a5101c0060784120401c080e5400501034401414002c0c1f6100900115641503040300300443c0d005c208640209800c50354610700e00e4510b01d0001144800c03120604000c08598600802e910310000030b10071003400e20201113050b24081c0b04140443c2d101c18081665480954000800e80304e244001e43d821104c1d40c1e8080e001000d81d00c40b20110814040e83c0380d00c202e034410039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 35947622 1250 35946372 35946389
    0x5150408030c0f07080a03020d030b041d0a0506093c03160c0609060e210f06160309020306010314010f051609061b02040e0109061401061803030801060806030a0804 72
    0x86240d610f001013000010000d10340480582442d81007614025221031040e8010303018503498079060f00490321680d01210400e00d0010011000d50712000c411501c03004105400d50380f40c40b0710b6021909104010401e042d0481c035400000146961010300d0b05006011203400b5501020f24007104948440c00740020400c42003c0d24a89031120f80c549800917682001e40c110904220709100c0a0050a40ac422083c6030103030202c1e03800541c881c550840c11115004c40c04032a14a000c0d03001d45607280310380011000c2c01510103078411041600c4441c0210111147d20308080e6047e0310502c01040403d40000341011448480e41c004500501da401d002c006640c000d4a00211081d0390004842c0d009500c681c502d4060085480c0195881103421010040b0030f0b417102c006441503170b54242c030b82500802540b010120070741c01070040c0900003c034280701794400c0d824424540841c018011140c4018103420108040d6a450346400d0010303400c11004a8413264002c1c0309607094420b40110401040c00800584010501d21 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 35948872 1250 35947622 35947633
    0x6030b0d20091f06020a03091707030c1806050f030a030c0302010e0109030c02041d0705010f0302090d06090b0702120a0302030402040e0601030c0609080a05071208070b041511090a05150408030c 85
    0x1c010310fa5803007010350010007190414101d16001952002810b812540c1c0304180b40003d10181881c2c50a10451b6440200305642d61080020801950208801c1a044c1c4620410045581c0d100780000c1559020001b83d05400401c2d030740002038091850402803502900c00007900c2d11050528070300b100c898100035404112450b404004514060082880365143c50070124403191500140c40d83d07515160180506009105280d941c80d64840d07810780e0401c1000910903c0000d0359401e01100512042e04142e5106020720000388489000140c0803407451003a1001d10b0ac3d000300118101c00a4002800403079100f41c69141100d0001020460325000e54014440444580d01e0004007428400c510352000c0f030a80c000401c94008140040380800c00c89031745910070f072031400c2d40d0707d00601d03144106000180800c011000384400d0100c1035041000c2c0c01c2c210340c400c00c001da01034042c4181c6030007424540b0750303c04c0100c9001d210310705011110205182c48070031014100350303c0f00041d9045421220b044a20365125 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 35950122 1250 35948872 35948911
    0x1140f030a0b1011120c03070506011e050a060c0312060e07031d0c0a03140715020c0f0a0e06130f1a030714240405040e03030f0106030b0d2009 63
    0x7036070030300c3c851540c5052103410040c1c0f600c01503403581505680d104c2a42000325003a0400041481141c3c03059920070180d5039079684807000c0f6803800081a40c5030082030035010340402c2c241003003541231003903402c42d444480c592401e60b41d040380c450a143d030082001c9520703601e000500145d1461614041c1503541c0340401c03000d44200611949a101001c0350049900103140c618407038880040d042e055039006202c4011808071405100d2600341309510100c0d21950829103044126030220f14000310400495801c40030b0f1141c0c208004604219010300c0180e0500c48021444134641511244000c20b0001d00c0425014004920202160511040000c8071b2009202d606583d11f803e101c0780018209008290f013030299800041003004500c2c0d01d0000b00c021480d071f00c032020b00b0920000e80c0e00900c0c008205101c0300051064403900da40003034503c4403030002070344000f140d214002c0c01000103030b44014080980f00c2259494140c442c90300800d10401a03200a1088a9103803681010a03214129900003c180a151b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 35951372 1250 35950122 35950129
    0x4050705090f03060c090103050604020903060c040303030c1706040c17180601080a1110020715030e1c1d060706090503040501110105040b0103030e03031201030302070f050409080901140f030a0b 85
    0x14502d4042d10940008041090ba0800c10055440c585400e180010b01560741d500400c0003480388024166040c801c0e40c0c02c000c0c02c5000b900003401500d03c0f1b40d6042c00a03440110041d6030740008185050f041440e05000501541455445910f5035550341ca012010400e0341540c10100c1001503441401a20307180001800102e0108201030040030800003c009020068907121403600990700058801d00822405070980c81c400c10440d00501100540c6440201660501070001e0001c40300401c81c50180d15001c131049106180401c030134100c0780c1c49800c00201c1a410003e1038a00c0031809036885103040c80b44202080e014410301d030071588910006c40d95942441c0002d0700d0a418132010f1030032070303050500300f00028041248450440344e050803c441c40c0c406d002d0000b8114060100d0581c10180702c10000000d0542c0050f100003100c4a520714425100d450384248025143d00c04405480004c0400461000d5407040c0d094000d805000180d203400c040425a42d40c03142c2c1d0007903507050700040d102c60b011005841c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 35952622 1250 35951372 35951389
    0x3170106020c031e03030402280909020f01020c0906060a0302130b04080715090306090206040b13030201031104030203070b0901030209030f01090201020c0109051806030c0303070c03120212030a0b0604050405070509 94
    0x2044020b4008003080b14204d40d549200043c0020b001d518030360411016140c05490000391001c010101001c120303140c290120081260700c1050f48604501b090f00940c650010940c005518406082e0744401e035100c0c400d00c0031030350240700e42c14101030342044000d503401c04c21070b40000a80791141800c0d40d0369203402e1400f40341413100d400c00345200030303101c0302800d000f904011810112030340480d0216280c1190b0000918a010380e911041540d80c000038540000303051404042d080e28400d89040040303507902c100c0750030b55001e103000c020f4056000560038005d484403080036200501051602502d040740e00302c0802e04122290079005d0b4241e465800c490115a014004000010000e20702a228149010009059100c24101d2411400344890100d8900c3c0c80034455085a480080d049a590304550728104001440d288001d40301918040040c0300501c0c030116000040d400d9100d0100d0440e243d280360070000303141044109510620401c400242601c940c00380c140b01c1c03c40b42d11b030315444041107000c1c080c091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 35953872 1250 35952622 35952643
    0x506041202070b04140411040605071a061e0406120302030301030606060e01090b070309091a01170609010e09070807150f090e2403030706020c0d020c0102060f0403170106020c03 78
    0x40d00304000a02c1104030f401d041e00e0444d0074844076070030f50b030b4180004200103000192101464203000100410500d0b00a801000c5061255000000803400b040b50580c0021003078038802d0b84082420b00c403402410781c00e0342100e80720310001d00003d000d0750313503c2c105202e01f29514011000f6130004801007040c0581c1d4032800d13004014608000640304038541c0020249403090003004400c0d54041117032000d140c480c81e00c60003d418200c0e170800041030859503040c0080000549180001c40084c4107030807038448891034a0180d0809002c505450f400c1962042c0380c0000100414520720642c10002210f074010000c0300010403c01c120008171040f140002880c0c2e00c0408a50000d10410040800c1120407c3c2c000302d91000d45030200c3e02d8440d4200201071041c0b03054484041d4503100201d00502440103c3e401045d292401d002221904c140081d81030f615800301042142c05601300f9400550000100c1010951040c03191809d20010b14103507990b030741044400c1c0c0000005a200b00c0418809080406c01e04014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 35955122 1250 35953872 35953877
    0x2b0e06190f091e05010c08120106090f0b07020604030b0613050a02040306060509090d03020307120e010c030b0a230d12020604120212040510051201030f060515010e0904081605060412 80
    0x2d542c07021030b80f04640e8080b84645810861442c6030704081c0002c080549500c480401c00c0031085507510700c0c00034984055401142100350700b5900004180d03004008582d41d680e07000e000c250a1910b103031900d580d1910001d1110f600400403460b40c1d1920780c2c40c0e104051240d02c04510050710349056051001c101e821035085030b0700400040c001d00080304000248205070500914002d030b40c1c1d0b91041c0d401c481401211199011203410031195001d2120190080751001940380d07400c0000c4280d01042000154492140410b0b0141901c110409a401c504070728030080360140400c00c41c84420396800c001100b69102c0c2a0068019601380f00c00c1041c009900403000c50b061000f4101501c0200441506104610841c1e03c500d818500301c00241e0f00034010380e050140c6542c074503440c540c0c1d82d08000c0510b0f100900700712600b501e407c0c0040c00758154450110039810060359000e809a10010900c108414090801d03203a400d002d1001c00c014000119800801c10302c030303a0203040b40c0d0a103451300100b500c000c031003100203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 35956372 1250 35955122 35955149
    0xf030804150311030604050703061505030a0e030403021807090302090103061a03030a092c0c0a030c02030711130b1c02011107051005070602040b0a050c2b0e06190f09 73
    0x3c06410001900d4105408840000c3c5a40320344000f43d00508031503000344c2103000034158001003203401001661140e07401c0d41c0148000100b4402d02912840341b400002e52100d9101900082c0703203110451941c1c45842c83c00c3c135030540360704d0f038001074460a026802101c80c03540b00e00c13000c0000c020810040090500580081d4109810840064010040c074007984882103444000c8414519914482880e503664050b0307941e40d6420030031200c2010368010002000030078104040508814800012141c40540005144508280400c108140e900354444c12210b03090310751800710305035901c0b0a0f801819407194080e80351905420b2001604404a0004800c907030b8011320410040c40d01d94655161440e14585001959a03c140c03034450b00a010fa5084020500408180c250360380d9040301c020860111141c04039920500d1400d0f10360811041300c40301020501001c2159003100e401400318040c4180b00814980c103102203c0e41078071000f54000842400911281120b510058002009a02500e5807182041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 35957622 1250 35956372 35956391
    0xb030c090a02090d081605070b04080303010303030c020a0606060809070609030f06021b160f12030e0108100305060a0c030509070b0403030507030903020414100f1802070201090f0308041503 83
    0x80d4820300080c05000240e80001c2e015000781d9626090f42c6500b580411a19210749101a401407804e0642d00d0441c0c4074410803001144400044007598203c54030b400041d0315503801c43d0303022000346c5030300d40d510310652040e0120040081c40600501014042540c3c131400740307191400180e441c25115034800302c140301c42c4040038000b24189001c2418203a80003103001d65500c0d007005028031484030396001c840050080410f00c0c05824600f5030701c9021140f2048440c0301094580c008080c1d864400d0800030013081a9026005095016480c1541d0180022044003011303a0340303465207801c1c024222644143c556882c6a201d0076541c0511803541c000d040b200c000e0016600742020700c005485140809014407101090403000c00d4492400c04014650190051114030000d656031010041d09441280d800890720b54007013030303035100710384024116940140c61000800e0b54000035070007076112040c103a0401c404410041075405003540007600131031003158883c1c0d03110320b805040700c451048280c00307008240c140700080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 35958872 1250 35957622 35957629
    0x3020c0f061207021632030c0d052103090f0106030f0305030a020f0c060a0c020c0a0506031b0307020a11091e09010b130e0610060203070f0309050310020a030b030c 72
    0x120703001203031404210321548540310b0907441c0c00745c50041800a0104403034003080030901d02c100e14024000e050705c0940d42049070244000d811800454076600340e030140a12426502d45400700d28007250050040d0341c4120f20781070400040f40050160400814000010700030b10300410043c403410110b20500810445040d644c0d100c5583c81020b002070100b000200c0458901d180e50390449001c0e080080079241c0e00c41050380010345444044401c0c1c002c1c689490320a030b2410380086040c0080c40401040100f14900f03020420076035410142500442c461f4000303035400c002c2c0c0200d000b14000c50440d00104906031080c64404440c0d4085d0000c58040c01c070b007100740800b881d0444c00801c141e0205040c800060b6417454600c9006004c42c003001680074001361441c000100e969480703100724007560000e98046549100e01d4411b001194405e00c00107038000c210000100d041e0800c850710652091400036544c940da00c1c00245004c4444c641030042a43c00070740c11540680500c513100c3e00000960140ca0000e1303c00000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 35960122 1250 35958872 35958877
    0x20a0b0c0405062209020d0f150810090609020d031808150a0f14010e06011103030603120c030705010608100f0507020a02040c0e04020f0d060501050304080307050d2703020c0f06 78
    0x100346428046007030703640c030090034013042c010b03158545d01191511281000d680103003855140700e0680701c0c03516400130301010000e050b2005461803c4010402c0e02600b091603401412281020389503550f42d002800016924071030b95028542c02070b50f031050183c6c9000d40011001d00b095100072140d50000340440b100310311020045034003421310302d00041c0d4406089031841c0500400a08400c0900c1b00c2c0c00089004507843e04001e004010a90ba03c1d05e00d005124012542da120540d08240e01d0b60107042c0d0741c1c643c0c140c584c0041186980c0764043d6030612006030b0f600c90950b101c41d0407103040c0d80c2000088501c040340c030b0f110f12000448001720501c80c6081640c00030352031320100c2030003900072900c03091a19142802601110245500680308554401440600850580001c00c2d00441c0317030b050a1002419601c03940903240500d800150061441d01e41d007005407002e520260344050001c0e11801c40c100d44986502448a608102c0a1a8400100ea0780f0b0000d060040740c408140c441c00000412140a8035002c06 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 35961372 1250 35960122 35960137
    0xa030305060a0305010504050f1b010801030f0222020901020d0e0d021002071508010f0501020706020303010b0715060b090310051003060e10020408030415030902011b061407020a0b0c040506 83
    0x10001a5034640741d01080381c04059400203081c1e903080500740000c00c503001403104401304010301501d00701b44141c1d4810b600412005032580c0000e00c5800144049964004e030001f059100400d540903244149410024120002c071140740a154082021a0b4550301405200d0840f4030318a040700054142c200000c00142c4060b0000e4020f841c580000c0907564000c002c3d000145c00505513120108118200080186109001d038030142029101d0015465000252030700680d415900598216824005182c0c00340c0c1040000ba1603000d40f108500070b2010340c40c1700300f1024213100b15007039a640308200c0070705107006052041c240082e40f401041149181703c941c42001601d0740068007080301c2d07420700b01851514004400341c00f41d884c070018001844070000401401252040b40d0400703048249100d040d800c666803a40003901280d94414507061000d52005484241441540e000034540705000c0c1d0303400508821260382003d81e01a2112105004124880e25404102d100c8400d1401c1d0800340481d5141c0500007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 35962622 1250 35961372 35961377
    0x110304080903010b09010f06090905011505030403030b1e120a0302030a0e060405100801031a09030711030313030c0f0506030103110409141501061d0a06050a02120d0203070201060b0a020a03 83
    0x92a820035030302900b1002c01c25000174106031095840b41141c1d0700c11401e51068801050300c0080004c0d080d962030086a040301c07920b4680c0b44180b41c2c80e803015121588000d0045080550700d184040040c0e880d0907012144100c0c10503144250107200003800500c0b00d00c01e180030400d034000408040000d600200b01c035008011480d2086001c0007a8000c55414021070f0050341e4448003c07681d42910310350202e00181242d000720714041e801c22048640704481002500d607a03419070020001e90000c43d01406249000d00c0019013140d14011035000c0c100d0b48c22a01d42c0007110207018a1104104800400030044050a400c41d111031955140d41d684001d07419500030203034010b80d290b909220034030808500c100e49a0800c207040d91005580200d1900708060702340640e00224400702d01c9c0c450b031842c0744440c440c245c0300080d15003000b603070a01c00141c0c0c0f03641004090600b18821080440100c0c2c4080380a00040d070440d000141c3c80e814404c00127420341d030854115045803202440b2100d0344590000d40d0409054050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 35963872 1250 35962622 35962627
    0x110901061706010e04061701021908071409060409050a061505120a0504050a020901120506010603091104090510020f0409060501030b061b0304030209070203180303130e0a1b02030a1211030408 84
    0x1c50205d4003a042e0b6500020219640ba02d00520f1613006400a06416100750030aa440350310007101520030746416280c120005503140b014101585a8600800c0c01d07440c002e08690800390b840c03e105081d10012554042c0d55500e41000b00942c4496642ea400341c1481418070b0342c2804002170b9920345181c03000300420110750721240030409105080c88244403ca80180c2011007668481d603d900c0003040c00303101100c0b2403041100000f00307517100f44644400d45a1141c400d00b41c2c416008c0400028006002c010b4401d80901c4400444407825840182182400c41d5071154030340380740900c040101c030340c1544014141030801030107401640d80d400440304201c200c05012145005805100e81c65801980c000a401c2501003041c464001c1c1c0010140442c0d1b0500d5102038480b00e514000d00d52280500607034aa00e00030490802e2091610030740c006540320207200070004507001504407005120301c100210801603007000034402865948220100c0c21204240c80602054484501040c1d241c80010000740c01030002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 35965122 1250 35963872 35963897
    0x1020307230c01020406091404140a0203151c060f06050306130807171b0723010311040f0e0f0903040b0304021306180c030e07150203070501060311090106170601 71
    0x2560944100e510054004c40d11603440e80301c050081c003080d00491b500c51048c0c122003041c0307280038001c40050904204104005850306d02101001e90805400d58040c2080c484d081281c607110b11400300000080c118001c041101e540c2050400c9514a49a04180c241048002c0c442901c1c001038003508800e403e1701068096a003401c150b0010300030031000070020300e9480a0007202004e1400906444840110456070481c020310f4000c0c0d9031182440342c480c220f204000c60300c01d40e07100c0210b200c41150040c100814018604516580c40d540b06030000c03105842000390901032044d68804241c1d10a0351009401014289101c140d07540303004030700c6000046100080042d0864031140301e06100240840fa0900031607844100004030240d002c0840d000c00d9240c032039211102d40c4640500c1d002400d68001426010b418101d003245040c054111480c2944000c100000000b0424070480004501a0840002629801c07080202180e0180d001e0400c0200003030303c40061007201e5480d1070b00400242000c14035a0719 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 35966372 1250 35965122 35965187
    0x51608040c05150c0f03030114030c0d020603060a030807120305061215101206060303030507020a020609041a03060a021801051c0509010b0d050c0301060e010e01060c020102031204050d09050301020307 88
    0x3513035803202c0c5030380203256009540c0640000034506035000b44040c21401e01c0420240b507a1006000c0000c2c0d842000840d1300400340c01e00000854010710040c20707600b0195140d031a00e0440f544111412a40105006018161b03143c0c140310707550300120100c541d40401d80d1134030a195601e0b41d282c400d19000217401c0000c501045102c0201e60004c0007840404088030285040c950000e00040c030060340400d09280009246600c040b560040169004243c581032125800070f00004021401040c6050912503401000700d81d802c10030584614240c07000540d6134500138040c82c81c0a01902c030801c0c144842800aa80010701104800d1a02215440700051580d143c46109000d024a08803c0fa0060140414101440303c0032554898584007500244081170ba036035108111079109120f800d410b031450300d00500040340300348104140c55005104403420041c2c13400d144843d144041d24122820390002d41c0c0b03c0000c54102210030000c0c94200c00850940c900000060141c600c030000881c034079286021046c00810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 35967622 1250 35966372 35966377
    0xc03070504030f030206060307060504051e04060b04030f1401060b07120c08031009060803040303051204030201111204030815031b0d0605090303011e080a080a0c0213051608040c0515 80
    0x16080f0704005a400c0580c01e010307403109800d0701c0044c0a4040d81030081015402030048408a841c083c04c03909070305070030580b9072004090f0500c501da030040c0c8030080003c0000608004d400518020150310201076002c2c6401d006013150000b40c6402c50341400c104118144a40040d248070681200203c44108001c3c43c040710903000c6004024071307941c40032081c0604094880c50200544209070300400c000e54035500110b039640110b10000740020410050b85c464800c0010146411a2180c000892520746002d086540d81e084001c40902c0b8111590800061540c44070030250007a100e401c0624407840054040703900d801604040c02244081a031300041b440e110b486000c0182134000004005034146070808a841c0d500038841c070345411000c81a4800c801e0001c0724403074111003000000300b008504603038401624cc0c009a0844041c00a4aa41140540c5580804a0401642a03c0090140703090820222580c00a0a0300810401c21004100000c2d50445900054440c210349540f244104410030380441e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 35968872 1250 35967622 35967629
    0xc011b061806020a120b0a0b070302120a0f0e0405040f080c070e0c03160212040303140d0f050105010207090b030705060d1e0519110d0e0705042301050d0b0c03070504 73
    0x1841003036441018440a0b90213403d144030507a40d0301048280307501c0384030255010a00c039070303900525240c8200124080c030030050101d076110f401655040d44c803c40040d0744c0380e042180320030081000340040ca001c081e030080e94400c405130f048404001e9400e154481c051580c076010002407850400080441d10f441c42009028010904e00710301e0b01041c03403c00e20460664200b03541c4442d080501c8407a4032001400811803507141000c00810508052a640302266009c100242d0030498030020000980c5541e418026051803125803200170425500d04400246030808550142c0c11061501e41c121303d5075900803a8085c00c1310411100541c81d03002509058008220541c2488070080a42030344400c00c0109400c218130a1401e145500014030712802c100050f0780c40c915518500040405c00182000c840d076111611912000c02142e203000c0e01c420100d412a0080ca000e03071102151040707030400550a1145075400f4040942e00558000c20990316101140c2020704103689041c130107c0050b9003503101e10f040d60000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 35970122 1250 35968872 35968901
    0x60c11010606110c0406030312051005091602061b040303030b0a05060c1e060708070305100b0a090e1602030a200703030c0506090105010f0b070201030219110f0c011b06 74
    0x10b96918805018541500c2c100c1c0024081d102d1001514501032003a41c04494140e00c82d410449120544030004000040440c51041e07040e59003c1032070740300c03003145910510107061201c5290740102d1300030380790510060030030310b0413090510f1a80101d624a010384003100e500d42004a419076050300003480c240d55a40103160070032008920034420100005d000c0c441084013011030b51240f4201c00d0883c2e1034040c2151740c040032800b01c0f80880c1040d4800d922030707036202e4031920b0558072958580352041d4003035000500f00000101442000d1000301c1440e03401a400960600e050000c0f4000400301944a01400e91358800780300e8803904084450300754251406045e000c130303400e5034a4140c032454082d261a0300600c1c00e42d490701c40c18000a0a070a414442c69042c0c40140302c2090413a80f0b00170900f1195030041d20100d04254003441a40c3c020790002101c0481d001881d2104005221105102403400c0d00100341c0400c036906c441100340d0700366003254030204907000c0c410340d0451341e0340ca500707000001d0200000e02009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 35971228 1106 35970122 35970131
    0x2010e1003020c0a12090803041508070c08070308040303050705030f0f0601030b0a08060129090409061107120915020c0603072006010302100318060c1101 68
    0x866030000c0c40c000d4600201c0c1212141848a110002c581c42800d0a24629040b81c00186600107003128000441c2031038a810a0740c0599252075810b0401e0088c580d020507081480f990190f40300a4002e240d00e41d070307903000f40790003802c1e80b034111011350010b841c29000c51032282c4900c08403070084810403000130840c0c445455088100350050700301d03810b1540e6840080180c5d1501108040248013400c0541102e614001a408504000d07021011038070320103800e800740c018804000e07a00e9225040d075001601c01e071030b850100d000305500040021501030224a410070004c04580114407054296524440c203503a41481480301d031123448814015820018a0035980d043c650050b50380880545000d60000c6201150185c0341109070520300d0040e0004c1006005600f0243c00ca103410b0b410078a000c104441d5855803240410340030450082140d5100c2900351a05440b800b8039402c0151804000c12 = true := by decide +kernel

theorem cover : BRFrame.Cov 35791372 35971228 := by
  have h0 := BRFrame.cov_init 35791372
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35791372 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 35791372 ≤ n) (h2 : n < 35971228) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
