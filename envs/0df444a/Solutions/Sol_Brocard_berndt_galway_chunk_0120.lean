-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:56:33.315719+00:00
-- url     : https://prove2.me/submissions/558e70c9-1952-418c-b702-0ca1a1ae29f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 21402883 ≤ n < 21582740 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 21404133 1250 21402883 21402893
    0x190f12170702010603110613031509050307110901080607081603020f0a0c0b150a260a0b0103111f0c050f07080106090614150307090906080a1203020a0e0d 68
    0x400103020040c0c240a0100038460341d042d405201600d100b1601000720f640b500b03043c4103c501503414010341e001007a01043c40816905401c0c045100b000342d20205180000da91010300310b0700701900449004500740701c02e4482c0d203003130f509050242c40d01000034800e034585448002c041101c00351440c0100c0300a018601c0d070303283c80f0f07804840140c2c0d001070b8260b9448040c44c200820304a04100d05540d1000c000e0082195610310360b03580403000c0f000600b2400043c2c1000b01200c0340030310070180112070307a83d0240328000a00041c095150341034002e040c484250f6240d8101030f003400c0c00620306184a1b00c0314880c0e454449802d030500350f02d0310260380340110150600d40340144c41d110110400101610480c4000600341c001504200b00b50f4200d01828840070390b403408480031078000c2c40c16640d80084810b00d0320b01c040d04c1c00006954400c3e12444c00164140d60382520b0310455800b500724611603000b00c0d00040074050134100d0b00c0043e100c50b00e000c502e0a06070402c0100160b50340007007284580000c200d5801800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 21405383 1250 21404133 21404147
    0x9031409040908040b0c0717031e07020a0b03041707032015090c0f0303070330050114040e0f0d0e01020109060e06100b0a02070e04021309110102190f12 67
    0x80d4041c803402e07590341d00c505e1400341c0b0740c11450003410540f14010021034030100107400c3d007034110f440130010340c240221744c075210300006900c0c0c40c0041c424605001d0f45000d45e84040035440200b0003486000da403070270b09050803a1542d14805211318080020030039200065070001000c080c0d05400f082941245030b40d04400c500300564514807416000015080c490140804507907181c0407102164411130001081c02416124012031001402250400d81c0c080c004034182000c00c51444000050a891008a400d43e54200c2d0020b8000001410056040c9411070038507104852601c0f0210005048412009003515500c191039030505080000241e0008240d0b4001d403c003043e4160700a105001101001314400d5689204071880e40501c4011400010341c0c241c8441128918140c940c094405e80f41011102d00010b030020340220780107080808002c200c40f12501c201000d1b20311030f024900034050b0420009203000121000c0342e080e40801e011202c0020321084c40c4203038880d40252440445020410103075494 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 21406633 1250 21405383 21405401
    0x60702120a1b140306010b040303030506011e030c030b1e040b04020f0301030f0302160b030610120212040b100501050315010c0f0c08150601020303040609020402090a090e0607030903140904 83
    0x900c500b940c5405080d000340c0320210555440d1074810005021541c01c1594904081c0314018100c1e00401051000c0383c403d802c2180e0144040c1041201100800c041c40401c0042030710301400603544046000d03e96505001d0341888030012503000002041c0c82c8420310440001c0c3c05c00510071075071042d07201d440da107494050b12a901c0c3d1450a0346c0e200e607541d00b0200304290450b0411001800b0740e1415030149038188a0074401c8e06d0100350321070b00b1542da503418403080c1540302d9015018410341c0f00550f5400c13610750000b042c00e121010a40140d5040500d045540428007070314407030001209210034030a41e40c0c000b0590ba0301900c1c8085810040100f0380c0103880400e08020098940110401c0040a03c240c480112040b0344911088070060f10001d22003801100c0141d40090040e0000c00128012444a030021401c0600003000185000da0880010b025601d590340014000e649071441a0f003500b00520019500083c20b0800784050f034266034005015005600000103502e10124140d4415159a0300c04a04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 21407883 1250 21406633 21406643
    0x2030705042306040504210c060203010305030904050a060501050703030203150303280302070f080a020f0102160c05030106030f0308041a010306050610020f06010b07061808130b09060702120a 84
    0x900346040c005a000c010098030b4400000500004969107007003a01c60307648a1504a0600c3d00c101200039000381d401c00425401200700100d2000480200f0158401580203500c148021a0384010703110a002c1600d1000b000341040ea86842401c12841e6080030442c2c0c10640e242c44c0050750b03599441c0d01c1020212100b0072054244c0300100301c00003440b0844009041c40410300b074581000c1c40e07101c4003c6041e4814680010301d05144607004800040c6142c000d8001e00c02c071b500688403070b078024240e0b0b1822608103403a800300d50a07462421406214840111001400c015002801a030341180c4500703845480f0b0003401801c2052200005051020065800d203030300c195000340030141d503502e05240c0301500381500c20912902d00d82c030f600c01225000040031000c1144410181c68207a1a01801003626046040141d81003511800d900b10030f031110907a41031920b84924101c03500d400070004801e01c3c0584030380020f03004e40d100b00042c0c10303150313142d005039000300d941100d26a20705001c014141d8200130342c119000b01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 21409133 1250 21407883 21407891
    0x2040305031c02070f020d05010b030f0619050405120318030301080309040612050c09070e040501080703060509030a020316020103060509190c17040204021605030d020a090506030105060a0c0203070504 88
    0x40000200092070b0350800d544021a00c02d511045003000ca04c1990030041450003405500c00041c00d01501d0900001e02034000000c0410000c00440d003084c418041c8000319030804001c22004416402c07103c50b24803020390041005240503959140e80350594001e0340000000403000810340503002c1900002c5500001c1903a0702c9513940e407003081c1c0d2034002d4000780c1d10a030309200300821400070490241803456002001404507621a1051080c500c20103401f0404000c03c0001d013046035100c0b40aa02c0c002c2415000608a040c43c0d13041510031a44040c149420300d4004004643c0030540c00010341d1913035000c800c200701c01e0b50603910041e40186102d40c8102d802c509103404000d5603003050340d41d404001c0525007040c09000181d89085031300c00300f00c3c0007800071401440045000f40c1004d501811015881040c00c5180e0019902d9040c034641201c001da441c020303000558030b016688e00c10074a170000c25090740c4c424159414a00002d2190103031903114020006900020400e56808011000043c040640204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 21410383 1250 21409133 21409139
    0x3030503090105010b09010503040201030c090f03030c05010c02011811030703061e0b01140a0c0206070816030e01030b130509160801060e0603060103030e060a0306030602120906070e0310020a020304090204 90
    0x581560412144600c180d4a07003000000c0840244089402c19403050b900d070307881e50307a03190b005500800801141208200740e40e50045028411503000001a6001e81c4402103580c59a24105007034410b50340c0c0110459041800c0c0d5410700384041c1c0444c00c0c107584407204040e0b40042c1d0300481d241c5040c580c005003071103091040c1a0403601070485203a0323603c01e80d14414840d440c500001545e2240844516150300b440030000c1c2c1c10340a00c1000020000c51008080072326121141c1c443ca2590b410460b0000a03101c80e111a000c01c040c4c1104020b0107102e001c0c00d0034040d4a0b40704c00051010080d0107540c601d256241c50004129071804d0201100e40e800d40e414200c03515460f601c0207802018503002c1c1e041040054004100c541c034000648a040340d60650381c13920441038040601004d900218092801d040c2c4440e40030002175101e00140214041c100c0a032826880c2c1000a1803800101625200900a800040641545020071a05000c030000743c070241e5508091f010480c618440d507840030740d01c02e1003c5004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 21411633 1250 21410383 21410387
    0x30b060313030e010309080901140702060a02010c170603030406080703090506010807051306150c0206041203030f05010504090b22051501080c0108100312050906030f01080d1107050411070206040303 87
    0x24007819020340d03520f0320b00c10003000040d4100d658065001e0861b110900501440350701c2a900005e0801018190a003004082e902042d45034215007124000f50f5142c50409000070742c0844c000c10088030b000b030200041c0c00e104001c65140d01c20381c000da40c01c000d95034002851040c0683c1250088075440800c0f503100d5a1b58602c015298041e5000d181d104018220032070001080901903801554403500000c00e030100e180509a9541d01030783d03c12600508203110010300408000320a0740361a000380c60204d0000400904034040710700c142c108520407440c1c0002500440c20740d4000f194000314000b080c09500308882450000c0c0503150304002c0c0b1b10f20a0a040d000745446413041d2038105c0304030504841040143c1e40040d141b4400850780d2b00034410a55504001062590044600254490900f58600406080030034220f61085440b07100000c503038001040303011005c2040020122403880c0905c642070b614021039031130340c3c202d03c034a91180c0d031912050001c410f00c003402c607a15207900070800d0342d5680c2d40e4540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 21412883 1250 21411633 21411661
    0x3080a091e031106070b0105190b0a03020301080709050f07080612070315050105150f0a0905040c020318010e0616050c03160806130f060e010e07080304030b010b0c0d0c03030b0603 79
    0x100300c07004007007500d107605903080c003001744c40c41a5401003050b40380d0781c03c140510060b114801642c0000c001011000190350704010020708501000b80d230302684c2e030740c10071400b01c0c07501c13019074091a9041d10340401c000c001120b820616030000c0903854030008544603940081c400740342d0401040520b000d0950700104000e40600c0c403600450340010203010603130740d983c01c2080a00707000c40c0b5010601000c11940590324400002410b00c4812820460b110b19121008901103a03c0308560300056400051407035101e21040c051b41c01c10729024070b0041c602006403c0410094060083d21601200031501280f04211083c0a80e03981c8407006000c40700c4a220700d00070309070108824403c0031814050040812443c180b941c03452281c41e5080300f61b60303410310742a541e4071000f414130000c00040b55580f480d440c094035100748141402401c83d10015610380703040d070401e84640384040e0f10400c0e00c9441040032083c828404646000383c40940d041c102030049141c05c1c160042e00e00c040189501100c0041040303005564081c0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 21414133 1250 21412883 21412889
    0x603010e25080601050d020105160b0c0301180506060a0513080a08030105150f030c03060f0a08011a01030605030a0f020a210309120b0f06060c0105040b01080f07060903080a091e 78
    0x4a01c0081d207590340303400d5032030b00d00a010ba690881081c04a120241d409040100507101d1011250040c142041d120341da0407120582c3d034400d0080c40000100450b421008441c02805002c22080195041680004405104d07014000c010700c100802c3c1c0791000c00050f55608005c0c21740b40b00340c0752888900c1c40d06a10551007401214420003101030291101c007160340664140d0703107100980d075240d03403201081407505810080c00950f110700b40308021203458940c9985000101002c00c0003082d80651010a81101241d801d47c8504240c603002041240b90341c0054010036058012801c840b03400042e00108150702d025401ca0b802c0c0d5040003002e42491071401900344a202d0195071030824294482401a41d20a8400c1c0c018040d4001e50010424400c40400a1500507400400391850420742012203429201c003110291070401c400e00c01000380c000c041c090402c003a0308100c0a05601c42c1049000390982c0010300016003503000110b960000d0078060139003c0d02401c200c484e852850501c2202d40d80384440140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 21415383 1250 21414133 21414193
    0x612070e01080313060503010e01061d1002010c02010b030a020f09071416050601060302071a070219050708010b0102070b0403030806040605180a0b22020d020702040501060818070b0406080603010e 86
    0x86002500310306c203030180da040e540900c5da8211542d00c0e0581c2100d902c1110324290a01901850780103081e641c9060700049450400c1d000400d050310010001b038212042d0900590103500042c00320f40050381e51196072241c100084604030f080c1e8840d104211403950a24000020b00340002444501d0174180050030402c491042d0308460441e0b0321400308070268000c024005100c0c07818511440f40c010000007207180e0042561040740d5295101500080f40001056010390f800e410a40040c0522030007800745a485040c20300003000c00b285410000b05e0b2500c02d61002400300140500411055035a9400c80c40090000170100e890481c51041005001c82c4150f41c207401482c980700000d8081c0c10054000c8003000c03280d15000c42080c40c6001500c01a60010f091034074003541c200b2070000103036640d105090203862507a0310b4000c1c600d448182d06000c803000030081089540155070030402d03502d4110445040d00e485203000112501c81c4004039016014210003e1403e000707032007008440103400f40b0003402c207101d41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 21416633 1250 21415383 21415417
    0x8060906010e1006120902040e061005090a0b0102150406143103051902010b1201090203100209131e0c03020d0b0103020405030607031e0509030405011707080612070e010803 76
    0x407443e00742100445106800100d100c034504041c1c4500c503644140c1100e03001400206002c0c04601241e8200502107400e81e0f01110407820900450030b20b010346030744c41820000100207a0810600103903542901c098a0648401e841d40000c1c2080500e411070001914140d00c0c0780141e05083d02034098510907a0010703c4076010290456140c80c07882507040c400303143c264a41520700204100841c142412003410441551b4840d08082c1c07482d21450b4204258114060001518041da032040504144a040000c0c1d0b40c240140103440341a13568440b8209403010310f000016a01030b001c02408007946040004540b5030b80341c9000d490382d554141d0000c01c00d04524140030807502131070400641c128000d0b0b0241a82550081c40007a200a010f03900854020a142000b40040401c4050490a4440884010700180c07c0802d003040a56003000c1b50741c00d80d620840d100d0541d031401290040403424010892442011104400c40c8091800e0240c90007a003e840008066580c44500060366035004030a50a903070340d91 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 21417883 1250 21416633 21416641
    0x606070212010920091005040c0201061a040306050606040f051011030c070504050907061e0306050307030305040e010609030f0b06130903091d040c061116090902010e03030a020c150408060906010e 86
    0x1164a801c2d2113640131011b42c1084a051006220041c41000c40300010356680e41008600034800108030a85080306d1050140e40e581140384c5030050310303000751015000f810280414051b003600c8601d41410f480c0706079800d07540d1541146085070b0b40800c442c104a03860000003544550140f010440a068441c01e0b1001d11031902c40c0707071405940c0d002c82d101e802c0000d0b020341600403103008044107684d018400c0b07280c04182c1c03030384540001c3e05100d00b5034011000b00342d0000c0c0810005618142003401414141424085546036454001d005158008024a40070901000850a070346100700101d070070081c0780d0108020b05041c07402402c0400280070300f03100c451440381d80070760b061000c0d81e000b445203a000c101042e02526010058809180e54210700d00a80250910703910b004074520000030003489054000703d040c44d941e00001d0b1440c1103070484203001e81c1040081140e0150001181e5140d5481a030344003c22544844140401c6d0265030008011405484284240020000b600c0b0341079606000405032a030315 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 21419133 1250 21417883 21417889
    0xa1e110f0601050d0201050918010b1207181203030908030c07050105090a051e1f140912090d0c030c0303090602240403050307020307050d030614060903060606070212010920 76
    0x1400f4428543d10403050695100154400c9016126958001c0c205210340310fa0704068141c601c000b600030448102021400d2281403a00050319030704044141004105004000c2d000407000c00c05008103c440045007542004040c82580045d6000740c00420300d503203e0812031702d01b003c1039000700c1c01030f92550b00380302c0031030b840040200c0e40c0e060942d44200144095100b25820803115260640035006c54003076140342c1901e080c41c60b206541d4002c809607000a0104201400504000300130300180c06642c01221903c1c6241d08980c2111650f41c402c80301112030300654603088084800542000f4a180c1000f00004105500070030950195110ba40070f8541c02d600c00d0040224000c500d4007074540c0300c540080400c0c0424003075001982c01c844580f05a0345080016207490389040c00041c20707500000e07643d010400440c2044842625410401c80d056441d0091500001707660f0000640701a00c6028000346160855540800d0401c1e40e4102710024401440541407207401011030741141c5011a981c41d900c44501c0c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 21420383 1250 21419133 21419143
    0xf05030f0321130501090303090309140d030305090309030f03030405061f0303080402060f0304030f090902040605030f0a1d01020a03110301080a0b0c04051801030204060f0506030a020a1e110f 84
    0x103050b40d400720002503140c2c003099401900036203d40080300b151403402000c90400c3c0113042c0f10a000380c42c0410259000c0ca0010b0080300190710180a45841c002c000e8201d40d10010100c10352901445e0102e22925002800e034294452140041da0511611082d00222200030002d544150301030015179142c2e5032612060074a040c68072a44114840040006000190064028070703001400688181d0819045100e007106d250f00a4038290003048442a01c10400c60f07100403000041c0c00e00700415405c0a2030400d01502c0d60001402c0394111000100c0000c01c552140c3d4010140560b282e81035040d508401c11b1183d00035071105c040103000a0804410130101e07076050040728100c030744010040c03240c0580e0b600c0d02468500302804980e0611000c01c4005910707520100c40c55500340c030710340d12a0307030b2541346204102c01c4418070740c0005102c0c04600020455591400e040d6a0322812841c40940d40e01d000002c21136000c41900703544980501d40408140c41075502074828801408a23808442c0b0401001e03650319920 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 21421633 1250 21420383 21420397
    0x60106050f040b130504021812010c0e010c14071707050102150c07020d05030a030f051e0601050d1b030902100809101503050a03050306031c09030605150a0f05030f03 73
    0x2200d00300010040d1069140090808510207112104d00c545c8070800642030780e004503943c0418104101002c100f42c6000e000c0d2502000300d0034001c11094030f08080c00f0b854021120b03519814409100c41003c21300590f00d01c10603003203041e9400c0d160f810b42c50b50656208086071b082d0803c0340744034003003000ca80c1c1e500004a0096132125403003094056a01e03051468816401808103d81100c3d00b181c010000031020405480d14140f2500c0c0421610f00303e400300411540020328403020703460030440d00e001007a141e80d1031f10740201007844c0541d0785854000780b03c8003800c2c0e02607103401c00b00401000d01005036810b0b8840319555100700c404004440b21054215150b007001e85154045400c03040e0148501c4c200c0d43d001032441d00c0003d040c0180156039840d41800c0030700114094001c07400000400945140900c01007400f0717801b001050800100600c001011140703076020042950742d450000c075801a4580c83c1e07403102c0c0100180381080c22511902003200d001784074441c1c680a445090528462000701000b40c840c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 21422883 1250 21421633 21421657
    0x6071b151e020a050109140d0302070218060114040e071209030206060f030106091103070318150527070501090b0c0c040c1b06090515060904030c0c0b0a08040506010605 74
    0x2154004200300c41c48107507000900c5040d4803405078810002413080c0540c40303466008151100c1c1c81400121400c0c1009105480b010805104020160040c2d60304244040c0d8010f403503112048a50b41d410062312695001079581c52008408100040e09015005403d446103510351b0b102050044507040c3c0e00162104020000c0140e00148001451400c0002d2680e03102c0b88002e0020480d02e40c1d42c0040c0044400c1c40d031102401110003c1041200c58250103a0042040d00413100e020444694076010307940c8181d802600113403170300c0c2d00205039040030032100c0000700045402c2010622003440a80c580d501d00900c0f45a001c0341900200144520402c000d0322083c0000902030440500e07003401700401820070403404000e0000e00c3c4c03981640a4000d0b64076400d15442141c00081c0d40344d9030b0401c02c0c41c00c40500c0ca080310307004614080000540319440200e80044c0c2c1820440d1920b01c6500e4245201c0f0f003a03400055445c0c0300450180c1c1c01541c84464075020303a0050060301d0306a600c4807411a850310907c50b400320 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 21424133 1250 21422883 21422897
    0x3020c09060f12030409060b0c0705010915051612020c0306060306150f031005090604060b0a030309060521090d0306080c060703080a060503011a01020115060e06071106071b15 77
    0x201c0c10a007803d000e2080600040d2441c00b6100d03e00d0500700d51554100141804010a060401d540308002610181800742020000d0925000c014a56503c070050060100b14022030342d000c210441c02030590885034014054105a811500000d55580011407807074072902c60400862551b08000c20324500074114200e0603462040d50006005c884062111115090302c81d601c00010390f02290303c500c0340545221000b40005040c0f6041c840207541c2c048071620300c511002c4c50308200098103c3c4942c01250b4041c24450b858025008940b02001c8150050b110000d440c2401c000e511074010902070107003501074504200143d101c0749007607500c2807051074445d0810400c00c101000b10380151000c0794090901c84000c103415803210f0201c2d0a403103400e140c08180c2618a03203034100b95a02030040320350300810400d8088a0918001c2d00422028200d1602805243c00041c84810b0007050803180211640c0981140da481c0960b20340341c288500402d2090310110030344000410440f890a030309042044056a601e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 21425383 1250 21424133 21424159
    0x14060306010605070807080307030b0909030c070e0403180b0307110106030f030507210804060501150c021e03070e0a060f060e01120605130609060603020703050f0705031204060903020c0906 83
    0xa40c00f5403001d441030702c17400740c10b1004100103180500114815455940c000c100e4161900910041d6040902a00320981042c880c000c02c00100149a10444d0594009090720341c455040985810380010328006030555202c5000c030b008015800114010400c6030344100f800002492806e080f40c585000003801c8044160071040400d20a80207000c0715400b603140c503c44201d170013814201d2001a50000c10120b0060400c0000b80000d034410300307004105840b0282d040003110640181001c01c0d502c0000e22030700d050001c1c0c0c0300e00e10116801022114000e03044a240e540c6850701b42c2139a040482c0c04000b1241004408101c03561411000011540b00c0d4941040e0107269000641c0c0708082e00d10b840f850940c0c0c42e10001742c03030354403010461964005d50100180039402d1600071425550325401c00c03c04c1c10300400242c4000f1354424201c1d6112113000389043e446564514156080d4440c000000300074803480c0c001c0c001400300f190300003404584030341c08540115152205002e10b5400440f0060340c084401450300c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 21426633 1250 21425383 21425387
    0x102070c030206030c0c0f060a140403020c010804060f060803041401050903030d0207050109061a041505010c02010c32060f061309020102071a04050108060901120813050310020a03140603060106 85
    0x5141c00c040c1008000e41040c50300c15030300b4600a94561f150140782d00c00400d000c3d00d000680721f101c1030095002d0207410185070988001e503580092000d010304106c0d5480c00101441130540c041c84000d402d1580910201350f035540084d60300d40050003540d100307580e194940c1c1c0303440d80548202e4409060103000b640c1041e02c0320116000a41001c9401c0d5441d5490700030b080c0010385a8414514072080c505803a116500c02141404203c0d0041980d280d40b690071a50701740100d0780c128075080e41160b03092a1803c070b0a0513500d0a007124100c0702d800c0c0e0b2448500d0200001d2030255044580d40d4111600d4102c42040d80e52070310b010740d4a2020340346c0c1c58100c0c80a084907150001d154104185240c01801161100c669841441c0d0764601031070b100740982e22001c40c00344603540e03201d40c0042c1c11079000c0354140415410300980d60aa4192210014004800000c851200310300c0304411600801d0000c040d2041000040d0b4039002a41c051034070078002034170388100051110000b49199024560140c02000300303038201402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 21427883 1250 21426633 21426637
    0x501031a040c030501060b0406080a14011202030102070209040f170f0306040c030221060a050301050105130c0c05070602060f0105010309030c11010c08030915010b031e070903050a03020606030705030102070c030206 94
    0x1081d03402406041c0b0100c04030f0405d002d448002d2031038250550765a032628600504d203800c003030b10310381d4290300f0042c003050780b000f175101040c0c191000c404c0c1c2c01248400520008c0e00900c540b0700000e402002c110108014801c450080b01c46240c09140c1041e92410300c6c00b00440c01d803060710030315081c1400601c0421800d04081d8408042c0a095041c011700d09200e07808014114200b00d001c000e007a0840c401001114203200c01010002c010130303002070010354104000a04412082c28200d13140d0380e80e600046040302d10039000c0c0e20905030080291408191102c000135100d900444000c40300003588400040c1c0c030b500ca4411200701d075405a680c98101941959510351290864140904020b501c80090000c50203000c01140207450a0f401080b417441c05d040c8000014905034400d0781940414000c000c010707040d1301e80c070720151840c1055007401c654489030156040002904041c0562240941190805400003041d502480c0200c1c119614981e0394401c040c00d038462000d008060a013810002c00c014100040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 21429133 1250 21427883 21427891
    0x20409060903180806070f0507050318040f0b09010308070203070b0d0f0c081608070302040503011e050a060f090b0303040e040b0405060603160605250803070801120b040f020102010f0f060303120501031a 89
    0x40c08c03501d001d0140c1c80303642c5581c014a5411044010a28515000746080c2c0b041100d02004503105112000c1d24000041001c40c0501c00a04000d200107504011540c003440288050041c3c0209162194a0198040c00916400e241c4040713891a08255007542d5005e407040c50b10a0038503c102e419128104035045451120107001802815001c0c03101142c6a07038280a8020f44030b100460496440000201396000e0b110054a0050980d00e000000e0201003100548102a91442c00010504c06c40000100340346100310350101d0b0300441d10380180f0003000002e2160500444c0210100c40003a226982003586030745070001c130301000082c00c1c10304204550040020b455042c200615009224828000b0441005c040b00e90469080400008100c1519009501203000d0070800c81181c070115115603c40c4c019440107440038083d008000c4080f000c5a2003500f1003025101100024040f0000c0c000d81030003d007210780011008500d004a121004000314468a0304a0f50481e80312480888603880301c1600004c050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 21430383 1250 21429133 21429137
    0x118020f04030f0c05150d05100b041208040b04090207060b030d020d230307080103031209030509120109060608060a0e010e0c040b01020307290c070c03030e0d020409060903180806070f 81
    0x100005819611210150080300c103183c6c00c00e6445018850040c21900d004100d50221503020380140100505501998282e404001c01204500c48074182118940107507881741181c80c0000030041707003000c0310346c01500e00144150310a015004501e400c151b00c807202e0441c0c030f00050744000c0b0400c10320b500c01d5140420f07034071036400800860300310f1035011140d42d03204540041c00b05a01d600100101913000c0d48107540e2402e00d80017000103040581e4002d1452240d00f0b0481d10510441600441150080d445007040641c060700410100b0794402d83c04d51507003030841e02c1540c15403a281c400000340c04103020f0300080303040c0640988007561400003004010141000040d045101c113003c4000001c00503030303d081035040e000e40741308180340c1d869005c0c01e14094010000e1000200c20311001d40041c0350050708030280c0b43d060902e40e20003034805000c82c07040d00c1e5105002e5405420b1002144c04d00080b54000d6402d20301a50b00c40c50442ca0602484105110f50303c20010f581c4d01410019401501c52005100041158 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 21431633 1250 21430383 21430403
    0xe060703080a110c0f0c010908060705042c07020c03060c040311130b060c030306040501050a120311030d060b041418010608130602030106020f0d0306060e06030c0c0105010e0118020f04030f 83
    0x112002d161003405c2011032480e074020201d80040c1d6803c200c046008204030001007607249400700c4021705c00c3c0960321928202c0c0101400d00d189281000001a007501d403141412446031a01030002580d030b107980300001d80280100d40100e044942d00808807400c8c2c0b030704442800700285d843c000340300000c0c2c107200384248540e5603621000d24554581c0c005140c07019140d8025a20303410103504000860360103901991090441d4a01000481c0c0240c0050811981608152596524001007103045100d011b52203d812440d240b004241484104050400d80d40381c2030f8840080c1c43e002c801e0014009601c4040c00071881326000411480d2302c540e1075142d0084544080303041585241c7d4503141070360003e030043c4000d42c1140304000c0ca1600c081068000e44900c91409018042c60b01d1000b03005c400d0901c40c554000c1c040040051030703110b801000c86441d07c03035a900801c45903035211400303c0d9180c400c3c041c5071640c1140641c8580004403c0c001d82c0c10032401114014549072540d6610314089640e520121094500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 21432883 1250 21431633 21431647
    0x60102030912101806060803030f0403120b0306100e010e090304170a0f0f020102010e0a0308070309050307020901030b0601080c19050306011b050f0c0a030b010b0c15160e060703080a11 81
    0x6180a02e0340400b40301240c4410030113142c9041d8095441c9900081c88690042c404c00210085283c406600150903050188002031816110005800c1c5850344940620880f001c0c00020405040c01c3c2088580070f4000a00d01c0c2d032540c018021036001035a03150316035442404240051001380c0000004203040e8802c0700c50050341e568400080013940a4246d0b01030210341c07002029560280112141804494041e0010303120541c2c011302040d2001e04400109a0ba0b26205810804200708849103903400a00500c00b0703681da850240e120110071203145000a100303502042d4034200308070954407034442901540d110140a01c100f01d800750001812141002002c61010328100000c1e286000340c0741c0100080c215200c101281140341c03103089525070b402030000c55400c20106035941c80846c159413600c1c100700c0d92a60b0711000700b454880c0c140382c8505454500c40030f02c0791050101300d800c54560140e465a00104001c201000031030300448401034041200d080024900c02c40f5613204000510f8281c81c4070f810414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 21434133 1250 21432883 21432913
    0x12020708060403050417030901170703140c030405070e1e0a02070f0b0709120206040e04060b060a090806010603021c05100f0f0e0603031606090201020a17031e060102030912 76
    0xd082d601a40800e50005081c85048000d1084040182c2c40d140158a08101000028a45081c00c4200307026405640003050505120ba0085d10341e940e2001036940250908803203184695000340c600b02c0701c92140c3c1e00001f07000060314041610400d010300a21100030f20030380c08a107207000014403004009508000c04d40006502c10f04000f4050300070048118989055040980220526003009504040079940c09006a840c1e604603815102c9200150314991124900540903120080d400303039106d00080741854007140d01544c418111040101105c01c2640d8510050782207106081c00e14121040f200d0010303240318003a0700403d402c610500a410000b42d07880c8a00b10045007030f90030520300c0b4101803204000b00040944083c0e00402d08030080c0d440c003003004e8030450841c82d1410700108050703100c040b0001907a00a21004405541090095446a0b030441061300d0a610032038070014401070400501d801e010741e00c2c0b0510720940042c0c00851500140d00100030412001a5031001244109140c3d1103c101c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 21435383 1250 21434133 21434143
    0x40b0411090115030b03010614010c230a050d030c08060d02011e02070905060301061401080a02040506070308040213060609180204181e090206040608090f0607020f070509010803030412020708 84
    0x300750f0031070100402460700d8000301500e400c170b2001ca01c00c0e03040c48020701c1411144825500021401d00384000c5080c00ca1410801210703885200a43d0601003100c80074a020003c1503070105541700d038007510380d4000328082c2a42250745d00c0328444001403800000446904140000c404901e005041201e44850800403031300400c4180b548150041c1c001082c01c0041000a002e0030b034000c0404c034000d0180038182000488941e07402c0d001241004003213400f051000e95554110340c05014064401c668403071040c280a016244240c401324001c816519503030101010900c00c0c1001e50300c0b2a40c425251501d481911030515164204c3c8110b0300740d0800002420215800d80d0b80016803208201003410318038000004083d1160741b1240711003a0404150701d0042e030300c0c48125411b9800d0f9003030440c01511403a4a980c60b04140d60100e451501c107003001d00c500250005460150880d0320404c44c0c2c440d540303231005e01c09000703020308c0784080a0b4000d1000c41c000691000544034056214412100125a10300d0158a08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 21436633 1250 21435383 21435389
    0x3120c031407120e0303061008181204060905010309020307090f0e01060312090b0f0d020a1403040605040b09010b0a0302090402030a200907030606050901111906050a0b0109050306040b04110901 85
    0x440c21003402c40e0003c203918002d48140d0381d49980070b5411807034214045110343c40098007260400c00c070b480009090522080902e0742c0943c03014112020141480c180c480d0342c0d030150040c0004619005400101e0b0b40c824000c8407502c0c3c0e800360141ca1120715004ca100c1c082c0c030f005403030303c6940ca07100c0748a00d100100034802c000046010f20702c5a0140000704030082d00310b60031508040341000081000f40341040803c002c940c3d10b105058401a03542020003001c40c0e07084c85605e042000d4000010501007031014030f8200b0381c011070040003050615200c404119088038a1001441c0d005505064200302614107491019405400501540e005202940d80c2001020740b00801805d41985d6100c190140c2c1818081a070703100046060412000341440c801030324a0050101413410003070740001a8070003400030712060704602041d403018045210f4a00c1d04c0009007004448a070728080c50945900c0c140d610402640080340c001502908046c3c5943c1c5922019100c018400d813000c26400410a040d6290511400d0007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 21437883 1250 21436633 21436637
    0x90e0102030609060d0302030a080402010c0b1f060516150f1d01050a0212010b070201090f0906090f02040308030711070806040b0a050f010506030604021b0109050a0c06030903120c031407 82
    0x3503440c0c0b46040211a60300902241e004800c0004044c0010707800004441c4030242d5401d00c1c030313001d98a91004032101103440300b000301076070202d41c240012001c0911540d441c106501c0c4600740030903281c07601240d060169500c00c1c40030440400315803020810400c4c0040310740c0302980010500a003400090000d440f0080e010a070010300040422268002c01c1c4101174100340342c1c210562902040d45076071009500103000c2c1c0d114081c80050440c007160b00507810782d0003d0003a000080010b5070b0f201c4800004000920400c071619080c81080d0018500078401c5509880d40600715030b0540e218000e0803a604041e8000c122024426000c0119504030108600c0c0d11480c4581c0d0091814030f8001d02c40003d541d0040c12008028a0400051150703a4445081d40d0307000c601070720010780321080b00c1038031058040c20702c021080c203502c2c180d08402800b0b000b24846000c0742c000d405d2103030480e036646002c50440c2d410304809000109001c5104100d500c2c281c00c044001c1145140c08580f002088600c1400b4040c25940040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 21439133 1250 21437883 21437887
    0x106080d0207060206010f3b040b091006030804061103040b0c16080d0c030302030618150909030309030409150302090f090d02070b030c2a010606020c04060602190c090e0102 76
    0x45a20b134104411400f500c072107010004002c1ca8802c9018001600c07100381030140703040448604903850103401c1400b24103421062114181000e003491001c00105540100e03c1e0b0007250b0718042240c0840c010711088a41c01201103180524160b000c844202e640343d00d10380c03036000402c00040c0910940c000f810300d01031120050110004503070814200d0007030545c010203940e008500c461482a820404450b51660942405a0780741e444100241030601a0703000060804440310070311108001c01d03801014070301400d990488107501e41603070b229503034003048900e140e0071b900800c4244091401e0390840d01704652180002c06c0802c0d180d50000f00071440031280b600150020504000d04018100082509149980082c04400742042e0840c00f10744030081030620b040c1d10000306000003111030024602440c0c0d030742d840c10b00c079071400000860103450a482500d00512605001d80c040349024800c9c00d0498030141c004250120243c02d101c000d9240585003582c070403030030080c0041d00300b055000e03405d0b1756005d4800050b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 21440383 1250 21439133 21439139
    0x90a060501090603110d0b040209030d020a110604050a060e04060b0a05030601020c06040b07080f07080304050f060108010b0d0f051c030c09080604020904020909010204050303161208040203120901020106080d0207 93
    0x5001c0b500950084003010304021041628480402c204e903220b118a820200c0c11118040104010f031140f007200640510072482c40c25240c642c0030482c0050709100702e100710408200841082000d001d20f00807203500c0707128410108492800f800c100b09410314041c0c00071401681d5280784404c150045074450021900c00400c2243c250f0f03050041070301c0c04104881250070541007a010320381030300a40d80c004000b00380000d0890310540d010400c1da440680d1022006580345090b1400980b22071064103208018071915001250703654060007201c0508101605000c0f20b4001038803403c4e840080450255100d0007125800700d03c08082c44801554280307191004904412840c50050041d0001d900010454101c8014080140c0c0c618030042c2d003103601100c900c500d41c2c49007106a8020321440d4003155040c840040c0410b07a03c400305600c078954900410740f2510700062038070252103502c000c4500950581241c4005020710000101a0102e002c0601c000903025841d280d0700b0741307010860100d080259100d16410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 21441633 1250 21440383 21440387
    0x90503040e16090605040909050f0d090e1303020d050711090c0405030d02010b100c05071d0a050105180c0d0608060405060901290d0303020f1306020714010512090a02090a060501 78
    0x750b050800c55150003c9080d00d02a0024603d000d05c3c0514005541c4420310b540a000c4104410b4034408504030960348418201c3c20094a440c1c002e12541702e8201040001881c0c0150003103d101480e42c154001e01401010100101e0300e42d48441000c564142c0158012030b01a101c07051010f218001c0c145209a840f4203000c101417034802000d0b0007004581c10700200d80e00c20388902504940303d0ba040c0c1441e000c110601e00d401c90411826800400b80d0488980a0030080002c41042c0341c0107540d03110042181d82d07240c3d030601803182031128004d125805803d0100c0d0300d07820808024100d0844000000580c680c5400f40c9030300b0310741c00f41d03802c6d41e09501040a2000c1e414080c410100c4245000d907011b0503400070420300c50517034105003107040d05c030741e41d0000a00181406501190354414000c0c03d0103070b07180385584480500d201039010f0000103201f0010f01140c00860000c03004083c40050b105c076418601106c07103101c1c840c000204242e0f5107000d501d00303c0e80141c0381d55080341c0c00b03400c4610001c40c5050a100c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 21442883 1250 21441633 21441661
    0x20f03070f0204020f0a0c151a150c060c070210050406171815060906040606080a0504060204090204030303090506090721020d0f030203030403020d09050a0b0d090210030b012c090703090503040e 85
    0x50407881d10300d8170111015020a02721403407201502550440c0840c0300556070480ca0740101040d10070140100b1081002e04044d0700003e001e250310031184240b030580030301021100c90195003c0d410115140d484483d0105440a0005502560107544405040a10b036100340c04e001036a1075086082860906005041c40c1002c00164082c03020b0302d003000081d00d4001c2c0201499000350640e50f0701a0303108046814403500e50102c5001e8021414203642d5207035079140090003030000f00700c02e8a84e40604004925100d81c00325540c0200c0c2d2072903140301c03401428042a40b051035070140040b03a100c40c0b03000720000081c0e101501555a64000c0e0003441d124a803900340a801e00000107040810490f9518060211355210303880b15068a480a40d600c7e140d6680c00e410b20005d00300c0000181d030100841403019184d41e459000a15100b03c03c1c0d031148502c1501e940141601c032800b0100c601400c0801b01e080c00302d81044e520003036014005e4940401c040082e40c035a6400c41d07100ea041410080c00c0a0b041200e00e91000603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 21444133 1250 21442883 21442913
    0x30605040504020603040803090a0204061d090609061b0702040c05070c06030203160e03010e060406150501020307020f010503220c030204050f09150907030804090501050a06020f03070f0204020f0a0c 87
    0x14040c0202e20301035001907414440240028039014010001c500c0f02d82d0200302c00a80c440d8054400c000d00303074448050201401c0242030021056040320001501400d002c20301a004086c0b850007024281c072107074031041c03400b6031000480e91100720600510340982d4403070042c14511211606c4950740d9911030300740075122400e00d07044101818010010310141541d14004003c03a4061403170b14103418030a541c0020b002d0060700c1d0392000d052055406100501015610510f01c1d01d4010040c4a0a180e0310b0b001642c8034040d460b00694481100d1001102c0d075402440115803003d074104031010264282c3c0d0b01028508800002600c065400120620071400d1910489401c548001c001340d005140410001782ea0b4180107481c1c0420b00b40c04030218004a41c20000070010350f90007500140c4850711081e015004020901c6901d1003200f500300d0000700c40b4008182c01d1951028440903615044d0746031100709801c0240d05080740c2040d42013203403003042c00603100640030303400040e524121400c6a6040c0001c00c030b03035018 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 21445383 1250 21444133 21444139
    0x40905100803070c0902280f08090706050304060525020109110603040b040f080903150a06060806060304080a0e040e030702010201141504050c0c0106030c080d03090c05010c060603050f030a030605 86
    0x200c3e0003265a019441e41190302d00c680250380d4000148140805c81c1c3c820444003a165080c000d40d4001680015040c80e90001c550b4490b83d6652b00d48d2081541d540482c41450081941003010074045101a045258012603501c8141e043c0c0b1014041d90000720402c1503c2d40060f59105114001c1000314410312804d803204030340207230450825444400b04000c020b0001420b00c07074103404030000c02c40a9030075240004401400c1d1a9003110a280c0024400e104640341185945405404204903010320415402014040c0c01d581c01c6503540d50341c4040740d5002c4400c0710144800003112440c0740d910b6006a4406480c004095616100c02d4800682552504c40d603171420280b01c40c00308180a681006d400907031a004450124664071054114600da1190f0f2800300241d500b0078030080180710f0000105d100b250005001c0303415580c589a4120119481d107000103007001d007080740030085584a41c0c0c0020901d401540006080fa80d01e41d01c0600e030031180002480c0640001c6500c00c019a010f1003150700408080d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 21446633 1250 21445383 21445387
    0x412030b010e06130503010c0306090509030307050a0503100506030117010c020604120c020d08030405010501050a1d0a09050c120105071404031101030c05160803041103030903120c0102070602040905100803 90
    0x3510010b8100350202558502401002c100c038100e8000c020800c90040c800070f0b0017041984641e01c0700074050b100078004c04180606000105408800c0003048a00c591030301daa80f40c0c1880c2c0304180172102c590010304072460300c0741e000a020503282e1b00c0800943c000c2c224840554001154a0041c0e420355401ca00d400d015500001d08001c00308103164141011542c40e0f1503c101041c2c100c1c800214030152081e00500f294901008100c1000015440719043e150120f45030804942c0d9060805030814004c6000d020b060b4807100420209201608801c0c080c52081c41921054149480031481a01c001a41801240e4650f41031110098204401204840012485034a05401c6440300741134040c50305009810156a0b03542c0200013841074050328408580b0042c450380c80701031402c09401d0b82d04265000d6910007407003034114496107000003c640d222134024001d459a82d5100c0031001407a000380196800c0b0b95003c00c08500040c0c0541300410140030310401c0056503060888208000d4119504900815401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 21447883 1250 21446633 21446651
    0x60a090c1d01050420070c030c0506040324020702061204030306290a050c030409020d05060402090306060d21090e060111100209010c0b0c07030305060604060912020d020a0e041203 79
    0x700e106840d06451040e42c000c20081303a0041c45000c034001000c4065000c0d440814400100051200b07018212801149000c4249446104020503803080348001080300f180303409404190201a06500c0183e40129401410220540c010500030360284030160307869040d410810040540601c220009029115940000e130b281c1c070b1b0b00142c4d0005804015803500240410030010580c400d10455550005080659445540d0360040301c000c0c1d08a4450090340504140002e001800c061007070f110781d9000100103060903115142400555049200b040e1400c0707c1011480341500001d41340c2c0b846118003136aa2103c003034641200002558006080141000000a8034184c00318000603040c0b11901d120000607954a01600141c981640c0c0002c02130081001500b003140c510010b00140a03228001e4030144841c0d42c1c0d00b8100004c504c00c6d405450b0214200f10400d10455800ca16600303409480504080400c0c01c3c5600000c2c0514103651000100ca110502000b04000b0f401340f01000600311800c00b4441c603e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 21449133 1250 21447883 21447929
    0x11030903070807053d020f070204020a03060905010f03230616050d0903030e0105130203030d02070303091b150201020a080c030403260601020c01180e18060a090c 71
    0xc01c66602505403000490448140107090200c0c00000403120036088801e4600088520303409070402d04400b07001c9440300503981581c214000c4030b01034008401414508070300d582c20440207420210050007096604c00300420050302c1c0b07200300d5000e0010003441400407882c5140c00f80004500805070203210584290b1038140800001d41a41c0140c211070501024031554141201c0d0350080c203003c2c8010324186178141050542582c86080e0070340703221000f48566590302c907000b03e81d80407107400250141d00400c03441c85007200640c05800514800d1a020454000c241c80c0c1d803840c814203041022818043d860300f00504000c5041c000301140c1d540c0000e50411003c0c0001808980c402051780d004040000006020540300796154000c0d80034403903602806610890322444007a1080b18400d0140c481c0c0c111aa00d00d41c014070a141029207024a480c111604000108101c0303000604640c2c1c9404040000310842d460030701610384a140326003000601900c0b1030809405a001907800030500300068107110214030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 21450383 1250 21449133 21449137
    0x90e01150b0702010507050a1a0105090f01090c0903050a0b10051e010503041403120610051201090f090b01060c020406051e12190506090d111c020709050a020304050111030903 77
    0x400c1e0755600742d120100c1d8001070b580343c4602c07000202503010f0343d03854104001030025520401c1424902c01c00541c1e80710b07420701c0301305041691004507010f039040040040e0502070700b200d0305000f86e6140591226a80703035282c03880c10b4419901156054072682c1002104204006103400400040303071041c1c0000481000004003070380404a01c1e04000001001a09010030f1070340307081c17184010404803592041c0404e1250103032101070310784030301c1170040720100700c2c016106200b40e441104051001034040e03441d000114004090b1040014620340d16022480085a090f1031480d0080c5140c1d00d0344000c441c00343c0704000450f03545030400c0e07100f0100f0312506c2c9180341e010030751000e4200c3d05444032620100c0b00d0005610f0304001c56101640c610100f2425020054003054080c090b0100004944454030315034000e85003a81000390346241a8045503842c0c4140f000b0070f108284038622401640c507025159071018040d1142182d104050507000020320080110034402c03459415070552a140c15400d08089075078881c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 21451633 1250 21450383 21450389
    0xf19020a09050402010c020a0b03060a05030303060a061b02030303040c0602060714090105031902030109090209090f0a0312060e010603020301060e0a06080105011101110a020114070305010305100e0f0105010807090e0115 96
    0x301c1e540d04005030459028802585135660001c1840d01c4459503030103a10025403040b149903001c3e001003440090039060000c26207000d106d00a0000e10102d0420008603000070600d0990b1b451034004a10f1074001d61070078002940624060322618600c2420401c01900c2c000c2c0240c1140304000c0c0a0a03080c405500d0901560042c44003440e00c0c07540e03034a0702101a8104a003482440850910001c00082c0466a640c000001144281c03a1100c06561300d01400340c46080f00b59030704120780c2103841030310300003441f84030b6a1201c5180501e00050b4103441d0302800246490036044200440d074008014003403035030070046214190f14104c2c2c1c03401885003820300061803040c062150a06018007000c002207058001e40164402000070000355454041c0100001e01800006000b241022040c1d000716030403611900400d13041c0c3e82c1080081080007400c00c048030007049044001402c50107800b0b0f54581e080000e0044600802c5164020804a414808400e0448109400441080e17141054100f0410a40074580d000c0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 21452883 1250 21451633 21451649
    0x215030108070306020a0509040f06080c0103050f010b030618010303030b0109080a03020c010503090f0102070f03090f140d0309050301050f06090a0c0804060b0103140408040807090c050306090603010b0a03050f19020a 95
    0x3e07814600d00a0383c048c0107000004e40d00608003502d0b2040d81c1229809107040319020300441d266202c074180150222103056411040403041000184882c0c2c20070b60040d078002c007000d40712010b90800c845460003910310a800c110000780c5c4854000b03929690010964000d44426400780c4042a540d65029680f4034500043c103040c4000400040d00a21090101c1004410181d000b036580c3d400514045010101740300045000c251042c42c040ba070543c10380c8210f0140d4030004240000e4006000822090862a0604404111344d002c8041125182070103a00c0c000c01c04d2511880540c1019410801d5070f15005000071441e61420b980c0d08103440d0712208044c4c01c65000f02000842041c000d004a004c0c1200305404a28140f00718180000c00c00544010003c49840b03800f650112512500c01c6030a40303000c44058800202e0900203d8120701d454049590414802000059808080d001052029061b40d0040d1201c0e0444010b01013860760500100daa06d14178031900503001389507580020703400e90890081c444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 21454133 1250 21452883 21452887
    0x14121204121b03030e0c040213050a060e0105030c09040605060c0a11040209030d0509030a06050106050705010e0703020f120c0a08030d05130308040807050f010204120501180c090b06040b0a0903021503010807030602 94
    0x14010780c06d018007110078030080c20541d40c0da43e60101c0d9826107091482000c0c024140d140001a4041c03003055080c003950703416510b0502e146c0b12016491115001222582e40c0155145000240c42d903500005014200d40003014008400d0726041903e107400810a0302402030b0b0040049800d60b64001c5000512040c0a0918a840f07116050119140c002c1e00ca80082150745010f001082c0584c208020b40600d910407002484210120b0011b10b40303589161000075000544414510341900d4000b09103110510000c0465071210f03000c000280c201586a481101c15400010360903074250600c0c0280d560051050321140c0d4080d801d954001c060101c02032000d810080046407490402006100324081200107000075519031f03440e0550107200c0340000340115159031074644688e07500340f40c04040c40095034010f01d2010309913161644500160040840c507030f902c007900f0000415056a03c00c06086403c94a41d10b0b000e25504600c1482160034000d0861400f1000c1840100728400b800034001d010b07298840009a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 21455383 1250 21454133 21454151
    0x112050a050d030b03060108010225140d030203070e0406030506070c0c03140309040f0507020604080f09090c030a050106080421031d15100602070314121204121b0303 73
    0x6041140e5031400a10714090084004502607241d0480f00b018242201520241c0c4d82e034145541c200d224403c1c0180442400703d8451010040300c144031316005001310a00ca0085051292190509184200c1040443d40c00310901030000c4e404800301c800400309941c10020141991580e17660b61600900b59801c000c84120b4001c1000105503641000b542e10184017100716418102180e06d030381224402d540a0307072402a000e41c8030f5440b03020311350042c400750300940f40545032a140d01e92282d00c803124140f500442084481c001d0f840d600c10741e07445103481007056a200c3c20069405000d03902c040c0e01920400c40c3c800c082c0000b00303040e012020307a052010314003003864a04e150410b030042c0ca40014100703c45d804c0703c0890640c4000201e00b4825091902c45007000b242c2d514540c0340f01c24200ca018520050344812024400903502200000c200036180003244c02102e2074640d00a007690018078120800110141448200030300c031254078480800034180b50000010f6402c4030780b4030307480020001e020991914285 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 21456633 1250 21455383 21455393
    0x207170d06030f0503071505040b060f0604080f0c040b03010b010f030f090204050705030603010c0207060504030201140c030304050304030312090305070b06040608030c07030209010b070c1712040303080a050f0108060112 96
    0xd000b1540300e0960018007985081490320381d08080c105445030f80d07000901180c01c2000d0b201315032049510869880302a2501e200380400401da8413500c542106042101040c422000c1040e582034101a0005048c014841c0081c0801d640e03501e22440e000380c0c107058903026a030780c0003040c2e030f2408074540c6000a00d8a06603000240030300720300b15011350040d01e000c0c140154a0b92080041d031041e81c1c254024042003c030000100e0f0340b10384600c12480050300a020920056200b00c0580c0e181c0c3c40c02d90205820040400d0a6074210b90066504880a5000040800400d60418614655003004000c10411004940c41c090002d00c9480e5001300f400d0102e100080d8147d58a61060340038288090451361141d14400285030341d8000f902059108207002000020400881000c580c000e5070f00500f49a684d925101260300c5111010318812158015410325040c100d2011015000440c0a6510351000e400d2002d90a02161400f03001c583c0325500f8400103000b1024002240d42c11101d42064503071003015a4100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 21457883 1250 21456633 21456641
    0x61203090806070203092209060603021806060a0302070305040f0b0c28080706090f0b10140d030e0d170301030b0603060417090105040b0310050301060b070506040201030b0f1002010c030506040207170d 88
    0x501c1031230000b01e001840340c9544024140c034400d0301c58103511024404e21482d0000d0807510594000c004200500b1180e00c45c0d0050038610b4880e082143c2044e48552500da450302c60754005070101c080100710450b90340320401c071418809804660f01e212000307601e034081d92400200c0d41d010340007000002e0341030104440f551000c441030b80c0041d4241d980b05124170b444000d049040d14031032000319a40c400881c6494075004221518030001300305044140159805460480245803410f0b8043c001c10021000b10f440b0792030f00d1385d403201596191a965815494200492003024104500a502050401c000240c41c8a18280c0124111503440d848448000048a192103290441d0101c010f010050001a031229051442500d0040f002806000d8448810300614091032401600d036500550208026502a5000c04105500600146a20b000000c081401142c000b9038080040c1e40d40e80000c0642c990521840d904030f2800c035819440c083c01da44031400310000c142100c2140c0c0f074000a400c229480e01e548 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 21459133 1250 21457883 21457939
    0x4020d05011a01022a120a020a0824010602031c0b060c070305010605010206060121022502031c020307060b0406030c0b1909180b040b0406120309080607020309 70
    0x10090242d2900c0180301480e80d10a0000700e0302502c01d0a4454407046018070070040d40c158030070011030784a403412042041c421a261403026140c040e280807440075031a00c4072400041d1400d200105a0b19101d18412000d00114420000024031420b0051086030b9000c0300721010790600d00350400369401380c10070500080c506600c10a43c89800021004100b400200c2c00804407800340e8000c00a003a07841c0010b82c1c441d40111112400210642400240080c80f8044402c0081040e640181015140390540c010820003400d005c142540442c1c0c220308500d03003006070201c0fa140000b80403c00a08104c80a5a83e00407090006c0406840701c10024150722240c0c0070720019600144100440ea5032000c40395038540c4010345e0354520a07640f020300c01304540103090200131240d01c000c480c40003000c80103442d4018110300c0802a4001e89039000c1d007680e03941c2d6000e07860207041420309035190684130f468058803d205550240f900d0b5041003041203c4541c010041c0c814511083d00d803036030f00455400714180781e404640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 21460383 1250 21459133 21459143
    0xf050603090f010509102f0c030d09030503090c030a030519020c031002030708070906020a02010c06020d050406020a02010e0109020307090e030c01020a0503060a080a0c150c0503030f0a0b0105040e010501050304020d 94
    0x138040141c2c9060025403004030000b400001c020b03030400400340141c41c0d55a52080b2030140c80310b41d40c900c060803000008190040143c82964140269155240b098030348904090700080c002000b889045031080c460a41a40740450040001842c50394010f80140100d50b401c0c11106040070400d900702d40244000340486030f00600f1703070f26008014550400250425600400000d02080016408501603080c18042e2500340d002481c50341056401120b500c500b254003160210340a000d40303035403a1030900505001d5071086c000540c41d4036544034000e0854065000343c1e401e581c1082d00c070328096140800c20720107440502c5000700d05100b0f01c500d080d180d8072032180d04200540c4006503030b000148e844000f4501500d4100c941402256135400025035a000040000d800840c1c410070800000f11074000745607003031500d420030100d0380385c0c2601d8550864004036149010b070002c06d01040503a1b602ca214401c0c800d0401d00300181082d09002040e0356207103050040506000000020405554a0650703c0789080d600c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 21461633 1250 21460383 21460391
    0x302011202040b0f0309060f040503031b0d020a020714010e1513080a060b03120c030a110705030f0105010503070506130b090319031e020d1407140303070504030317010f050603090f01 80
    0x3d09031248544e001b100c014407640114800b1034103c0e10b0302c0301d40c1c0d4020307a080701c029419919810b99000da20780c1070554405072142c0410698140100a001030582d00310103401038030700705140c07080d1300be1985155070610b81044500d495040160b990101034900e880f5141e0209a11423900c028010348404807900800301034810300c4811001c02a081d044109510410303416140c2d6140d8042815100d4066080407004a8000307000d46502c452207201300c100c00d0383c41c2e801240c403d00d594901103030500684140481140c0d440790014071460900b00030704401048242c030001e01e0060b0350142000442c40d10301401c0c020000018440090340d60030004820a818160b00200ca2800c0a2402509003a081c03a403611820042852848009002042c3d07045100031a0f2508082208265005a42c030b50022a0466260035088410415103008101440c407644041d140c542d5207608504000e42030901d40b403449070490101900500400803080c03400d108480e400e6a5586e00d94a8510a00b03003051180c3c40e00700440e42c64 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 21462883 1250 21461633 21461647
    0x90a0501050d150b0d08130e0705030403080a15091401080703020307030b0a0f02160510090206030114060403060609060611030c0304090c0e090c04050f01090e0c0703021e01051005010c0308010302011202040b 91
    0x2010010180b50843c0c0c0320218003181d0348c0c64001e413036007802c03034041021a000f40300180210b8090301c84030380d200d144858001190504c004141d07208990580182990a076140311080340f00c285141464050108034000f80b0f407240c0707543d00003130340d500f9240001460301800d0000714903001202d8010030f103590300c048425911024008201c560800028100b59503520071141881e5548100e80b042600c01900079107081d203035030700300004042c40340e100021854002c1020000000495510310500e8090040f40402161987c80d02000070000490012100340d00d0704104401c10014200100321400c403042d0050205201e1140482640c2d168072001040e5000040d060800c401340401074000d10944034211180d90720040e250004403184215802210780d01501c40010551721400a0050624a48a84119410346c82003a5400543c001c1280c0701401c13503034451040c4a5041c0e46507060902400b420310f451503d101180d11300400c240340611000e41480264180c00170401c80540469010309141c04d4280d41d5081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 21464133 1250 21462883 21462893
    0x7080601030f0204110a0e06090f0409050105061f080f0c0405130c0f09080604020409050c0a0f05150a020316050c06130306180b0a02090303070b070c02090a0501050d150b0d 76
    0x1c10030b0482c820351601c1c0f40e0401c680c401406440c034405895951090108500702441400d40c03140c1600e0f0303802001080b4103d905c1d6124081c90a82910580000c2600e090410512020120a5120312065a041c062005100d64400150703a4061441038042d022511a034403050310700d104a8110341e820103460001030310b01446a0f00000311810b400c3c1c0e501c1940c001306080844025444e80a420800e03005400400c02501d82600711401003802042030b0f80c080e000d5040022590900350b0300100b0850b800070010000c0340360440d210b00301e248c0441030340740c40d011054000a4030783c070a509072511020b89015110f4103010003000028065500580101c1e915134041801c8010800c0d540320031160282850031400455030381c440d920307000903072105240c14113859451114001c4c1d084403401940521040c003010006ca002100c030540110305c1c50b1603005102d03403030b40107120402d140108050000d0341000c004000d10b8a61316041000c0e1600108107000354002c103d040c601074604501c1081e0300204444048003808 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 21465383 1250 21464133 21464153
    0x708090109031703150906030c120102040906120606060305190510080d020f06010b07120f031b1d01030c0206070507030c050601060201060512010509030405010c0602070b0c0c07050102010b0a05060703020708060103 94
    0x50030340d10710340541178100410480142c008480054050300700401c8154a8207250100122025954001500706078079201c1c03010456020780d1003e0b004951591028042c004103200c4c900c050000c600d000e01162400800d05050443d8281035896455900c00002e02d208062040d841c0207481224144c0d06000c807180e0f8000d40e90fa000008984240c02844000910301152030111180654450000c1080f05a114015640c000c207501c000010316803504800c25200c50b80ca840061200f519450300b5040000740304001580704122003a4605161500c00355810301034000034602e6009000d8030b00250b4500f410310301181c0c48a0808030041c40d912881002240103501074010b1000c0e94030a46103043d00c0945031100a003a10829a0310503803c0c1c004200c148003035440b50514503a00750250501500d440c2059a40702c5800604031078900703400001194041590343d0520035480280001d01c02803001150003400505250440e1045900c01c0400041182c101402401040c0c01000d504098a5641d0780da410446102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 21466633 1250 21465383 21465391
    0x2070f0b090c01110703060b01021c080a0c08101a09090108150906040308130201030615081503010b01050f0d090b07020307020a0905010b0d090c0b07030e0a05030609030708090109031703 82
    0xb4010745902510ba03501c1585542d11a2040e0301c0140315052a50300d841000300503031403842d41180101c0d01401e003034810440000d402c0d808550754040003031a00350f92410440c1c038083c45c800100140401804044101c110b008829a1003038101240d504860407403184007446008000ea811000351400024a01008507000c09c07038100b00321400c421540c500816940302c900c2207400902042c4007201080e200041d02200c00c0700c00c2d00c10705001410740d40310480c080940e42e0710b40170407002403a11010000c054180d0341c03829202241c150000e0001c245e403100060031070b000386402000c7c44000451048a40b0525400401401d504007600d1425030034107880003500daa0050100307a00490b5003070303400606d071a03640c445c0c00e040b80d40e0040301a00700100300500502a04e48100c3c1503d81e5914000041482542d900080c45621310135213545223000c0ca02002c1c0490000030303610080c445e0304540100708903404040100c031480e40e4020f02043c1e9800350b110040c3d03484000c80e000a045040c0641d001007180b00d00d1b07002507001d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 21467883 1250 21466633 21466651
    0x904090c05030c0303030403020a240608010c0f0207050a2903040503070605090601050a0302060a0c050304080d0e0303130e040c08010c050315030a0305090105180402070c0e010b040f0b090402070f0b 87
    0x10107089024135940740b1060714000c00603800000b07a080414129060304c00510010b43c4403920014044100409a810135041411141d640c0c00c00c00d0002504100003441000ca980080c4c95030b0362074080001e80414141c410700b020080b0320500b2444000d00d0b482c0711b0000c800c4000305542c4a003802c1c14000e56a0308640300c22580399203003002007080c600300040c115040f140d00400c42c000841c11030b42440b45541005400c04180243c5400315000200c040c8041d102a1a1001c001d010100c40b5840c000e00d00007072110094000e8000f0001200f03626a500b001c2d005940b80702c2089040d9132568507004522960303d41c049041540780c441c4418459501500860103204100c50b00c902401c0040209a100c3c50342d00c10040219004002e911001c0d401500948032441c080e0f85000f1807510b6070804101681c1c040e413411141c0f442c44240c10b200c2034000ca850725014084100c542424281440c40781c600c1c00d4054050700700c010002141110b180d0f43c468048900c110ba02080c082e0440b2035500e040611080c050701c2100b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 21469133 1250 21467883 21467893
    0x1151416151803050c030d0f0b010905060301230102070801060e07030f0507090515070204090c03030818070303030908070609200102030903030f030702070503150a110a120b03030904090c0503 84
    0x40c0c03107001c0c0d0300003040954401c0b03801840654003034038a80e00c2443d2049803400203100c107005079616841400707000e035150000130455008020005103061450b8020500c210300030f00062100301c1d100c0f03020280d42e0300240310b00c0b12000f01c100011703803804695030301450706503082c0b14004c54107424400ad02401240c0e961018400d1a02c0010301005503941100d0a00008442c010104990b1604021508007408100707801442c00c0781d50303000f04094a4030460305032803040c0801c0d0304004040e440040d06070b0040c641598a004010b103c118a81c0ba800039201c06801c050701c8210140030721400901700c0d00303071507803003c1c1c104442c1c0001e1030030030044070302c020018143c1845540080c04d41d500100885284031002400345240446e40d00c01140341d6000a04002d08500c52408042060341301084000c03040245400325019030718245041c0019100f0f000b0309414015010700403281c003680c10403840d030440c85101602281700103600300842d25500409650651040c10440310205010b03040e40b5841c16501e00360700340da03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 21470383 1250 21469133 21469163
    0xb010e01030207020d03080a060902070507230d15060b180f04050606040902160203120c0d0903020f22020a0e03010e0d0c020d03050904020a0914090403020601151416 73
    0x140403405510806500140445d06080000f031040030440da0012058900055031501c0e04c040d04200d0b0460041201e99502010003404440c203411860f10640c0e06455214400182920115003042c0c40003900500322078500b03c1040308001680c0102015110345511284c45030281000000c05841500c81d01d03010300c04040982400f42014018140310b940f025041a283c14641466140203622000d003448001b03803040c4001006179014003006031071303802c001e5005440350110261a400d02414a60040c00e02c100c8900410040c1c035000680c1c1e1840340c0454000c03034051344001f10018100d00b01d5524a091a200003400c4600719000249408641400d5008208443c8060070340b40d81c1d90101102c06c1e02003030040c8014001854207224100311f15109203000d40c14040401d01050582c0c200e240d07910040b5128100c00d010010781595500300c03441c406c80d80320302641402e4502039110281800b90000700400314040456480c02000d83d9083c443c02c81021950f40c445400c0380b02c40010f12914121800301d000701401b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 21471633 1250 21470383 21470387
    0x3030c080a05151c0515010303091401020703020103020d021201080d090f050312090312030106050d0b10080601050c0703021c03030506010c17072301050603100c0203070b06060403080309010b010e01 87
    0x16100d9040c81d030704420700d03400344010000c1002109030391400c0d1401300d010b0180000c10611242d85100c0001100007840e50551601410460013900520300710f403005d5111408036a80050000112034080c00d0060f512184d2080101c064803840228042c40b082000000404040c0000c0d81c0c644000940d580052a980700d01e040c005008141c42000c0e4035601070000200e10305c0e0b04000802c2001c8008049982c0d03000c1c16461401c00b90400da11213000301d44045050b548803100c034098020707041811180710106400c1c2460160100401a081c14100700000c40e13620b071818010404000070b16001010001c0484004c0011040d0954402c411070009062401041895001d0700b540d5401aa02c4200004540074110342480140c0005c01c055402d07500d0851500c440030b03140350648a28500030800801c5600e0144181450a820f044102031594503040401081070f5002c401d4900803940b03c3e43d000344a845410000c3c1d80c5004c0d41d0005001401c000003808084101580310040c020001c0e2a0b80c40304100b44001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 21472883 1250 21471633 21471641
    0x8010302040f0b0f10020f06070503060102010b060a02030d050c04090609020318010903020a0807050106210b070207050f0f0607120203030708090c06030f060d060c02030408161a0304080702030a03030c080a 90
    0x85180c2044694002d11414541400f020545c03040c00e1040350300105100c10594980182611280c020480000c00d00c1441d590a0044400c0494142c1e0031510300186004001c1d50f03441040700529060f9912000701d00515060000c0303400074400e041080c0702d0580c0b1850701400039401034400707020a68114100c007600d8031040c000d0700541901900542120251074403840f1540d84848801c940039540c503280404c00039408c42d0b411070001c6003c8900b04c04107580d40303801c48412030003418400c107551211713a04108036500c803085502c6c030000a403a02c40c01403001c0004100b40b809803c03030040c00076008580c1055a143c0c0000618450901a52285ca10b41c45000300d060701e59110f00a00c0380c1201c0304000050f500d40f5907411890304500003030480c01e14262241c550100702c0e2080001d40300140c000040c20442c00d0820081d00307800546104000101c50715100d0115000301d86881c90b40404035000c80010103101001050300d000680180545003580381031305d00280201030850042020551303002c0826540b22040c85 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 21474133 1250 21472883 21472901
    0x2502010206040b040503040e16110c0307151403070509030d0e0612070c0506091609020f0405040c05070f151d0a02010e03100f0c140703080f06060405030a0308010302040f 75
    0x5031080c2d40300e03501c0e904402c2d080100251080d100c204000102d00c0b20400321284100b54104517080311110300d1100904042070302440708000d5109a5a0510030f5401080308022201c041d4801d21300010039034015210100140000e00ca5110302004100700b00e034022005060030391048080c1d5040081003241640e034040c4042c507403500400c05004402104842907103141d040100c0d41003060340104a07560710351825504071420032091b0441c500703541c07040e290340e02c2c50005003c4c110300c1942032614488108c00c2c24001d42c880e59100d240c54516100410703010301d08590049811460080c8443d22500b4503908061400c10001c0c1d900d450680000e0040390505008005a104034000d0b005500141d00110f4640b44074002c52545402a1058001ca070081807081a80c8100040c034003007040030810700050844494080d0303640549600700800300c00a03900861099204803540051846511100007080880c0629082140c06100b11103070a0280350700705903210304a074400c407000d00c00410040104029900c00d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 21475383 1250 21474133 21474137
    0x6140411030108030703050d09080d090201030507110c04020a180902070c090504030c060b031f0b040b01080f070f0c080a030209130b0d060203060d050304030b0f0708041e0c0504050903250201 84
    0x110607480028410b00c001e100300382c1c074008c0214580701a034603422856803210b4000d680703c942d594184011035030540501030344480310307041428104000562a41d2a000d03d9071407030f4403480e40025607803c1603020701c0140090901041610050689038400c20000b58803040301074070400ca450b0400201c40c0000c3c005c10f8400e6500d0b5440310500c0803555240c0d0301400500b030314281d050058160a03046034864480d87d50b104102c2a8002c544004182c040c001151012003607a41080300341410004e203040c80c2030b071141c0c000c8924505101c42e2143d00c00200c1d01c00490040060281c0350000d142c01c803156240e00944002807040783da10040204015428045403000c0250640001c031500040d80420b2030380d8051980b00c007000e0400755148009607191400c0d40d0180c0c004a4401289000348003002d520703800d070194080c1c0b5500b091840c40c1025241e0346050210306140d180c00031a50824102086200d054400c020100908103200a0078400c1906403203070484c46a0030626030409018a102403500031803000156010707 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 21476633 1250 21475383 21475387
    0x801090308040c0e0601050409180503130f0b0901080601050309070806010e04030809011b030b04060e010b1b010c050313080910091a0906070303051305030a0504090c020604020f0f03100614041103010803 89
    0x40071181d409481500c224004144ac88440c920210344280020032000b043c0d8008802441d040107903000f010ba800350810154141300380620320050341c00100ca241c0042e42402d20907260355903015401c0c03400810b41c10110741800740c01b00015032001208080d6004a1003905c9100d0340c2d54840b68402e00325105400900c00c0140061390401406000f42e12038817411502502c0410050b440307010084103260280d0000920b00070024014181086201d04a041480140024000c5400074480113180e03000141a45042881c1d80060030200446c00301103582c041005080c00c55001040540907003800605d101d12401d15508080c1070000b80041001c8858000c0020071036030800b146624200c004200042c0062114001480c003940481d6042028244034555561000d03034903410807403220191107110726a9001d642c000c80906c0016075404800050803042540c00c0c0d401300c024000080c1c98555410400b159140c80d022000c60860a0401040741c044030a0b00c041c85070000d0038004410038402485064025013007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 21477883 1250 21476633 21476639
    0x309170c060c1504050f0c1504210605090c030601080304030201120b0a12050f15010302030a0210030b0a030c03050c09010612020f0706060801020a030f0204150507020301060801090308040c0e06010504 88
    0x807003000b900302c00c4002e104460028290501d454800b400c10380f420f41e513070b502c0b1000c2181000700c100300d11051008140c0b08007012200c1040001c110780241d000715410104545100001400c52040d94040300c2d820410501045c1048400c564517a03005a040c940240035131400420302103400030440c3c08695044e501c00b6810910103c3c140004c0081440e80d50380710450000c000b5403003802840102c50907000314040c00c0d0228030804120701d0401c29040404a4405c3c0704010009a5804152007031080d4042c2c42c0f43d0000d0312244011401081487d035102d80c0f10003c0c80e404418058200346a0003901d1107001140c02041ca041c0c10068692400d10984d40001c0c480041c4036a920314036005020405a40c05080d030402d401e40d039503071040e59660740041c00560340c0416001c03a1150f16016001d011804801e007146003e061120405244001030460000d00c04e0005004045403800d48c012001489e505000b00030220380c9181c01400c40005a40a0301c8902050303501060820701c1d1036655000d20816140c2d2490320389 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 21479133 1250 21477883 21477889
    0x40b0609090d080402030a0507060f081018090203010908030a0606090503011401030219050301050a02180d020a050f12030403030807020f060601020a0308070302070b0109020a11030f03010e04020303041508040309170c 95
    0x44002c2041b60140916000711000070000c0091401a00450711100420042c584000301454402001100c40d01c241190403c00807840c401e1100ca00c15011402041c200c2590011a0244c4103098000b80040000820071220714078940c0003006842c5180d44031307010140c1e11000c050a0312014000507205900ea40700400042c40c0c20850b40c0c1031800c65196402c03000e0b643e0030000342103d000f1610241442e8000071b50700003110000800135200381f422070380858800c9898003c9000f250142c0a02070188500c0d07462a00207a80d04030703d081803031181c0d00c1144d41c1c1741c0e141e14004240e01e006486980142c89000c24400c46148003040052142106a00528419030f045d10308076040400074040302d003415404c010010200d82205c0d10f50307010b4110320002594130005c82000820b990a54541a540b40d0018001d01654014407011241101c080031841006600d42d03000007811885607503c00b20a021900030658074842d00f002c0524465070103074807143c2120b0383e42c5240b00845150b402401045400078003406449207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 21480383 1250 21479133 21479147
    0x402150304020d05060f04120203070302070e0703020d0f0902010207051503130314030f040b01051e0603090304120f0201091a0307032f0d060b0f03130f0b0f040b0609090d 75
    0x1070b0005200307092031907180d1581c50425606481000e4404605410042800715500b040b07008484140700452a207005034400035181c0203240500401400ba2401103264a03100c1d4042c1c640940e0005420011500c191240900400c02407030100d016001c4c560f00001c01d07180c80e01c9402042403c002c18540786a4030703d0b0203001300c0341600740100c05105202445400400b00e683c059403291a402c1094096801c05041c00f0b544039005a1020b441840900b040c1c01140c214400c0d58108210151515502d940300e4440307030307821801250490704428500c2040c4400344241c07000c607124424001c0e250544a140c07525840002020700703803c0811160340030400700d409544282d00c000d660442d00100110014030b4045071004004080e0204080e180c408a83c2210310001c1d440f40034010071401d0308592030324204850801103030200610025031400e000d1800c105011046c02c181c00610b0b03000810301c41d20324004003059940c02007680e00303844a82c5004002000b0f4107141c50b00354000d0071504010003807400d07054002c403907403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 21481633 1250 21480383 21480391
    0x706020304050109080f03060901050910051903021f030b040207020a0e04020d08210a060501020717030c0d0801080c04090209010504020d0e06010803070b0a0c050d0903030209091501020d0804021503 87
    0x40e40d40d034500311005c1580c0c04003a08803030711030000a5507a0b082080070010f03c4801038100c075108415040034000381d410400c466030704648040e50325140e00e18404161101e641c2c100c0c1c4c40a500207090241a0030741911040315030392516010349041004400e05002d2004038000c600000750000001c070701c1800140b8082c40a164070900c001c10b841c105081139607a60029400801d60003942807d1250072100141c02d13541e4896104003402004c110382843c1c200001d40e21040c0e44200c0e201c0c1c0c1c5c0d01a19600c41440140201d4ac0304013180e000302c1d00c5110781c003031005201c1e600c2442454103030302500440c0c031907900d4207020701090582c000b014841940d0a140400000303500c00816080d4250b0f0710880104111000d0104034002e0007403a01a5440301d40e2810010755418008214205051404c003110200c0d40d00300701038654140d110800020100d005103001e4009204114256600025440420560400e440c20a82d200c01c02030f420350356082e0b07169074192050401070300d0003503100c0c0c4001c2e032012908290a001e076500c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 21482883 1250 21481633 21481643
    0x70e0409021005090a050607050d0c08070f050a0b070203130e340809190b04030e1809010606050a02030706090203010b2107050603010e040204050601140a0801030501060f06050706020304 82
    0x1403481180d0018401c0c402c200402030200b079010440304a40c0c40c0401c00440107260655029203021401d40c1e41c587c55032040701000080c0950f011003041070162250030b942c12154011909202080303e420203598402c41d15108645003400c2c0400104080c0c404815a00310401000b01b01c6003090900b201c5160400d00100761003195a950404000400080003140b2861000c81c8a12860013081e10002402c1c00402800c80c21641c0c45004001ca81141082c1580411904007400c0215a1190300d4211240200b0a030041d6004020350700740c01406404001d0329001d400441d00030803140d0b98a0805403600e020710314108002d40c2083c0000d0001c0740f11504110501c51004000098140503440011900400e505151000b0030b8000c001344c645810400c4284040c00f002c0b521142075616007505c070012801d0052000303015540750307000706ea03030b136401040d80e6002a4840c81d020f80c0c0752098040028000b000034442590650300303090002407800e030703016450300648050703503903007445d101003900d562003e940702900440c1c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 21484133 1250 21482883 21482891
    0x4020c0d0c150c0e03010e01140c07060902040203090c030c030f07050d0602040b03011818120c050a02060315010917060c0a050c0a0c030b07030b060417210a0207060c0209070e04 78
    0x8040b0003d102e000c11003034513a1140c0003164007030130506003102c649040d01e061b035070b03d00304c94182d00c03d58a0b042e05a21086c19a4082d81c0c9051900c0e1a074040c03d80c0c03010003908680048144102e17108089080400544260304503500300c40c4402c20160b0360040b020605176603410000c0b0600460501409100301c45004040140c94282d0707521040c03002e0b078000d03800800302c8071002151000b00c0e81c45003c0c410844010310713101c03441000680c851540c502c04051120f0b0500c0014401c83c41040000d1001c55040c0d50010185038a9280c0702c0c4155200c1c5200e403105d40d00165024001080c00e41102e40003182c01d8080d503004200d02c1d91381c642d0001199000300c3d84c000c107100080c06605141d0604000c2500154410440741a04615600d0440d2042401812200c00e060601c0c0da4031075a602da9105481c100e8900d88941240e03c900440d40600b000700164420000c0700445810f07408031050b04008200d11005942210640c0e40d1b0703440d04407030240581500070b510030101d1010030086031040c40e20f681c1d03040004000003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 21485383 1250 21484133 21484163
    0x2010f091a0c1c03050601120903090902030405100903090501030b0306010803030103060507050712020a230606010518060d060509061f080a0e030a0206040308010816030212030403020603090601050a0504020c0d0c 93
    0x4400803207059202c00081d07140c1701044250b5920800244030310384125020321180c0b10b6030380c0c0600461105e01601038001d078080006070911404100d007a4500703405207000c01022040e41801400c00c03c41f4002c0d180800e00b018841c14140c140020b1860490b820306000e50304603407c5595030009004042e254104001d800c0c44403101190213540c0310f240c034000c1600240180b0942e454082d00c01d00300503410200014214182d40d441020200b24154000002d01c1c103e5902e40c0701031012094040762000f65a002075000c140c40a454540b40c5c042015a60101c400300c0d41540c0d030a04000ca56104405c03d1000c2d40200300d00d4021040c09180c00315044480702c4004038981c004080c2c95440c4d0340060300c0c1180164040d400344800e06800c000c01c940540b940350080c01001507200b0704000409010301c002405038482000641681d0070501c10740740030715401448540e80b41049518240c0e505428000c26100e9581d00e98000356501d410f00c2115400c0304090003500f2882114401078400280d032079000e6410301c3c81036480c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 21486633 1250 21485383 21485413
    0x120d0b06030709090b01030606021c020106080f0709140910020d06090519060501020712080c1504120e090609010b070507030203030d0c020105010e0601051c0609020f0702010f091a0c 80
    0x1e548161150780c1c070107071501e18205040d0240c51500012a0601d8507104080c002203901103208031401e400c2340a141e2201c41080400ca00402c00c990105030039000e21005802480d00c041780c00e00c110f80d5030090902c00d08010040c3c0300c001c148203454410740d07980312810302c540e19202134020b000b00016904000903060ba03284224402c4e20400c0b05d080040300c1e50006030b081c04081034800d00700a00001c3c030040010300d04080e04084030b4001194054048070b8041a407622800c000c1042040c2c1100e40c00d080d402e00c1c1032501c2c10f1007038007500000c9003001c1041d108151059040c2040c525216041c001e25508140e40f8002920301c003a440034800b40d400b4018030b0301c003101607181000103000c02085940001503601c4900b100034210350043e002801c00e0307180711040c4a01c1c0d80e03100c000e60303158180b403410a0101400017003444004002075071182e4001400800c5881d9400321003009132034100d0007070700c0389000a407500000f1204be1200703002d100480040040003c2d16900403401400c00b9250300011a16076040034401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 21487883 1250 21486633 21486637
    0x14060f0f100e3610110405030a032303160e1305010e0604060801090b0c0a0c0506091e060912030903040e15010306060c0308040201080c04051305010e011502120d0b06 73
    0x6803040080341c441004002c00d0510007150f50310700500049400c803000300200d986034107148460900e2940c07a07002d0745406015038402c9070001c0000400300c94165005107800b800240500c01c4804201703011755420310066589208980c494882c0411a03034501001400a035038242e1000311050708104403c201500c005110311a040c042c007030040e0280b44600d4000100029100d660b00a651680d040c003040c8030009043e0040250007504a041c210340380d1350b600c0400c8600751a1400043c12500c64001030014040b0b020031150112280e8a851200e02c0d40001c150a9a94030b050356000f0ed580c0c0b251851861a60308030002e140c000441105036464250394040f020303501d0070151642400e10090710340d944250368141c440d600042102e41402074a0800586020b8080207000748043d05024607480042e009500400480307001c0c1c4002003c206101fa060b188803c0142000d005810014980303400204094141d464100b11a0f00329600420000d09001c1d8442520f400c90041c0b011019100c440d0341400d540c41c480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 21489133 1250 21487883 21487891
    0x1502040e07120c0c0201080c03130503040e0f1506030601031509020a020c03060a0510030609080702090408070317010f090b0a0504021b1b0f040e0f07060c14060f0f100e 74
    0x10320200d25421049a150440d83c0701d150f001e081c08008101c220050340c00c220026031241200b02050b40b00d941e440503622001110000090190000080105a821264540300e0103086410a800e070341d40c0d81d01c3c0e003101505203007086440d4890b100380300050980d0300c070f601319819070b81030204200c0b00c0a80d140b003900241d0304808881c5c00503030440050180c03241000c004c810390098400009000c1c0381001c115181c1c0303015031400040c140c25141c4100c8000e1110980481d41f00c951b002c0c2c0012900d107080d060042c201e8200250440000300c80c81d00398090500740810260584840380704039013a291500d11103500400b010101075401029001c00001c460303a40f407014110005403000c04842c410404400c990400306040c403a0110445052181050b689070004814503043c0700307450000316000c10710307586440c0002c01940140b4505c6503a10200b1a541c0c000142004c091150419001d600a5242c0c03181e00c5e00e808880207600d420300000003920716007009220a0300301030b50040405000352191880700803038004072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 21490383 1250 21489133 21489137
    0x1d0a05030f25050d0212010e0709020d0b0d051905010902060a020a03020d0302030903160201030902040f0b01030606030212040b04020604080d0e10030b0306010302090703060803040f08010c08070c1502040e07 91
    0xc5402c121058050381000d14a00c0c1241d040c1205003040d0018607480c4160201074082c0441c40b50316034440100b503121000300b40c0d080c412590b07840d6413101c020002c2d52000404ad1505401e001c0c50b04540d041418002d499140e1000c041d00405040407101c4522418040003501d0135901e49010f10f0250311000000c043c1000c03194040c00a05140e0304002c0d00e0080f010700349804141c13042040024040c40441610704c03a410007080105c880f500b600040300a060740420180d803241c54550000c064880680c42500101004e890a001c03266685900b60124001e0065480c00d0f84018000500000d0301810410b034403610080030745003400d864080a03440d0182001f49400440d032817400c14038283ca020440c01c64910b00510702885418001004240c4642040c13200034029642440455080f0b4000d41129024180400c122521180e030b440d901401140c192180e41c0300795103008a0442c400c0e2091041c2d41c8150100d0b21031190241895403414881c400001005074421f6003848046075042140c40c0f181e001d40324503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 21491633 1250 21490383 21490393
    0x40305010207031806020c0103091401050a0603060f0624050c06070302090406141819020a03020d0f051b09010527030c01090f0501050c0a08030405060118050103031d0a05030f 77
    0x501c1c014040003030031030b004c90307080118040400c15160f0001d1b03000c04900e020b20700841d44c07c2d4540f0340065044100a1480d103207501300700401011080325803000044074000e00080c010340758030f9611641120914000c0c242d045400394020f81201075011241041c80d2041d00d8034038030b4684890002c50800505503042c200294001551002b1480c2a00520000e40541614080310380740c90320004402e0b03500301030000c0380e0b80d001d1030001d100f03034070251822a1046144142507590f480c000d00c0c002e000390f0200711a442e11501d0a00d40c404851454170405216840c0c1052030b039289001140d0205041c4c200003d118100103042007882082200009043d400c02c00ca101c8208412009104050900d4460a48181000f212030000c000401c884000082103403028200a030fa0303845140591400d002030f03024060314100b00001400200980007034001c0c12200402d00140103c00c408042c10123644081c0b201500040701209004031354422042c0050754030300000d00143c0305903600e101003410300010a40380d034800c0d084 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 21492883 1250 21491633 21491647
    0x21b01050603060c0d150b22080313030206070602071b05030f0604020f0409022d01090801091205032a03090d0201021207080915090601050109080d08070318080403050102 75
    0x24010150031075030890161015280040c0d4580303290142095002d48240c880c02e855040d40c019a0408025180c00700040340d82e081c1040055032440e04907808454000710380b0500050900c404400e8441155901c0d50007003040303255400704003541d0841c000a840c119801c000400c00100d82d0043d1003a99010740c0c40a1121511341707001c01d41003030400390f110b039100e400c58420000140e030741114003104142c040b180003070354855074004600394001c2800315095150400682d03d6130708081c40301e0030380c0e51076090b41d401c60002d03210a1600d0076a014070780c2c005c10854290a2407011107000b640690383c0000c01c0c00c4110b007540d400718850700c62210300c0081c0e071011540c00000c0c0310003850240000303540384189000035480d00a401d540302d05002d00007800c28082142140229890340e00500c004c0340c0e0544100c40c44526401c2c40744015480e8239080c41494042090004000350110000c54044400390300c503100d0302c400d90b403804000d501038051a00450711160081284000080d40c1d83e0240001d075005a00060300e400c0b07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 21494133 1250 21492883 21492937
    0x5071205070e0c030f04060c09051503150303040803070303020d0b1306080c04110403020904050a050d08070e01030e061b0c07090b0f030304080601060c110901030312060b0c0d1b020402 81
    0x2800f51016940800410822001d414030100d03450b00302e58803420014020701959011130742e0710b8181e00400e07803003510303003da54014220400155000d550b221003008552405241019564401d521580840303400510481000c42e001c0c0d40540a0325544800200710f441d60b28001400240040340b100b9085035564400f070001036420042c481d0000b07801e03a010006c11801c00b0450b2094026032000a100e00c0000d00090200a028080442c0159001040b1030310500080070241c800e500446005000900c0d4005c10016580710b40100318200040d00080e00c0c6540361303100040402c001c003d050ba110ba200030400b9031034a1008120030b00082800300e10024141000300c0c06c02c00414484c2c04960700c682d00920090002d89004296981107a41741e00b0811804182450207504d0002a04441580b200d08007000000307142d007000079410707180a4810100001c5840303203100718944c00340c1440301d000e40d03000c5c08040305014016140c44c0048056007600038500034203940000c0a0368030540f82c3c10111160590030342040b80e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 21495383 1250 21494133 21494159
    0x303050a0213030b0903040f03080a0f030504120309020d02031006140f060306090a0603060207030801051903030e0607020a03060216021302040308120604020903011d0c09040804050603040507120507 87
    0x251000c06500c0c22409000c00d034808041c40c080909890416804208084e10410413500207017800c19035445125900e040641c0150030401806021680000e40084003922034410340b40701742e901181e0406400a6800110002c0c0041d0400300c0e04860740da00c011015a408000840240515000c0805e45d035040c00900100151800b05881c020300d0300300c20001207980c0b00b10680303600000c01c0d580114540e03201daa0580c041c119582c000f605552000600000385544a24a141132700d0058418842014248107403404c0d20f6114440074001800c0106000880c2c0380010041c01c00500040c02d4950342a11394440c80c040782c0c0a07200c00d00082110304949000c40c244403d5448000074189400c50410340b450311011407601c030700030261260642e02e20018180b96200da0540700c100702c01400801480800411040e031a00850241d8540b5100320f030001503d515091131310605c2550b201080f14149032a0806010168102401c215520700034040301040040032082c0c0b04080c107016000505500e440c11103608480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 21496633 1250 21495383 21495391
    0xa0c0906060c0c090b0d0804030f17090d150209120d081006090501030f020c0d020a0201110a0309090c0201180b070906050c1b030f01110403020301050705040e13020f0603090a030305 80
    0x4400c1c2c08071404003240002a2030012907624402c040749540c03070800018400800b40034000e022240105000c820300c40b10074a081c0140e80b203175101e491184c1440e00302c4120380c0544001f981d0320544460042001405a88405c103c07107100d45000b40c01d00d4002c1e40065140ba2014010542c0e9512400c058002598010b6415800120f04508004c999041000c01840c060080c00348505040d1180c0910340e0a41c642d5048414900d00d2802361186100c0d0164000c0d2075180100042c1c6c00a1050310b140c4001e500b003c900300080540c075031500c040c1146003421540c06003100800800c150f543c1d541003c030407481881da150740800d00c142d500c0d207100c0c50f041c03001800b12204c075040301c0200038041c0010302d00d44900081c000000d840080e0301107a490401c01c002450200c0f01e4034210403079420440b0446907214114040c00c10b0341e10840c0248500e0303998076412a0140690b01c14000d002ca4540045200e502141401c4880503001620004c0c210080e0710100d442a4825140a8003550000142c1414154544a22600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 21497883 1250 21496633 21496637
    0x200403050a02040c0807020d03180b0f10050604060f0309080705010e0601030303050903131e090609020c0c06160b04150203040b04030f020f070911090d05010b01120b011b02030f0a0c090606 83
    0x16505040311b00a560310300c03a000520502d603440e0640c031000030100800d002c44c194041c0d081403051805007480480902c044e2040c0c4d01000800d80c0200d02450444203842c00da03001d035a40c0108070560b1140440203030641791340542e9244020801800425028050740300002401802409503500d503207401421510020f25020140d0424007071916546000b1300444120f580c942d01526500700908450b00c00010560f0003900000d251000c000780010b41900588501c101c1e8070b09813040c00121906008961244c64401c00c03800000d03a01510003d649084043d400902413411110340c41052005d11040346c0c41542c0c10340d080318440d000c000400d5170040402c02d1914042c4090035055040c9802c0f2956102c16004030310380b103500c0c0c0340b0154054032a001514030100f0010000484640f4a05219000304140313450240065140079884403107420380d0003403103c0142d040e0f49000841b188c62150312407040ca040740c00c9038503005001c07095896100421222070924010320b640341c80185440004000c8448990100301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 21499133 1250 21497883 21497897
    0xe0f09060406050c09090907060905120319050f0a021e0d020604020f01030e1e01060e190b0406080a03110105090a0305090f0a030b090a050606010804080d200403050a02040c 76
    0x400200200380300360800d40c0850049800d4407200350070019806036980194100d0921000c0081081000a0500031204c40307840da1034440e602c42c410300c4901c1c00c5040c0e800f802c641c41002401c00313002c5503921800c015511450300c2030604c280040c8913038065104070740117001648281e041418245811070110329207001c0c10000c061201640d5400794445500500181c4035850110b03c0c00b105902a070441591504408256030040c201807154a03a2607161071011a099840c1980c040303002407a20f220705000b01c0c0b003080c0c044481202030261401a04801c542940c0242c0c44840001d00c201b030401154180600c43d880709221040c0d544404d60031540000d04004045d8844a403007404a6041400c450041000342d0750701c2206490f540100303136003420740d5000a0076000b401702041800d400107d5440e801c50303c11404e036107607926200011680384c03500359805400300c030b07003042081d1080800368000c05440040500020742c1c1404003012205507006548152200c1d00707c000420110719061140b801036010300d0170720171 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 21500383 1250 21499133 21499141
    0x1030309050306013606050a0306050a0b10080c0d15140301140105010e010c060204050306010305030705060106020a03120509010b0307090606020c091e0901020903010c090e0709030b070f0903020d03090e0f 90
    0x79131210b0311000840c0300d00c45c819940d00e036007a00d600f00d1009420302800c07600f281c2d42c0da46042401400f0031581c008046140c071342d0380c1455203040d1100340f820000c250740d52407141d100c04115464641c4000540c00030607039203000c0703244d07032924801207070340144800f540000c50241014145825164002c409007003008082c0f0041c042c6a8016941c00b05a05007031904c0b11b640c00c00c0d440c080001f840f0346d03003080e40c1c54481c000000040040010041c00b903d84190241d90050343e031031000f0703030f40e643c035042c00140807698030550300d481d40c2d04503031210b0351054000001103252078401c1d01007800e00515800c90740085880b16800e0012640402c850b800e81041540c00b14068902000078803524190000c0300703c0829058404141160803d4041c1c2e00ca40c80020000c20510f00d81d050090001600d92244040c4010460000317841039001d174a041048070340254200440380d8a40b803040394510385174484e000c180724a8070000710158844101402c0c00030710a49681c1e10143c00d0412540580303200604c5840250042c0d8100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 21501633 1250 21500383 21500429
    0x203060609040302191415100e190c02010b0d0c0501030e06060904081c05010905060a0e042307171e030301030f0f03030f020c01050a0507030e0316030504050303030103030905030601 80
    0x61400d80307010a050710b007240a240a04582901586e03450081c8200703004070040c0c1c0300442c0254026210040c05400e03680d540e15005a80e85070454a100725a140b0300c1e402d2010485507001020ba59801c1d20001030106051000a801c031101101c00b9120303000c0842040c0074035605440740d1290381344860000c045a140500c00501b0b802c0c0001e20050010b50b001c901d101c900c58480c03804c1d020721a038007807083c0525071716890950001d05c0100d9113544145800e00700003c00c491114026406590096100e0b04c10103402851404c001d060403818903002d00c264080090310018220551503003040c484054084070803c00e100203403443c0d9a21105000340c004000400005d00b080300020740e500d070300c41b909484100d0f05080560044c1032107901205042c0c000a0f0701d271250003041d4007082c4030307192441d02080300e40c64881e02141194660040c5884030f070b00401502030044043c81d5503914051003071412a29240d2940081313030442e002039104038040b400586003031140b460b003807107520701400c1c071000304c42088410503440b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 21502883 1250 21501633 21501643
    0x20705040b1e0609031e0c0f04090308040b04081606141f030b1b03070f12110d05060307090c1106070f080703020a03110c0708070f0510082508040203060609040302 72
    0x40e552040c1030002d10700409417401e00850040316200d0980590700c0e100084195200d402100351a440f400f007800d505019440d042c8120b403091a0566240509035845a481c55101d20016005071500303041400490b403021081c4ca03c58000074890840441d06624019800011020240808202c00019030007940b000002c80c80742011207810030030040303603a25900782154000d144c00c00c070300c20700362800001c219949402c00801c16004075150b03156080d03019001280d0b42100e9a280503c5803481c410003141180051942045411050080c1501c00c4581d49460380c10407601107641540214150180c4a4400700303041c4162907016a0500f845c1d0002000d040005044400043c54402450350110f81402990300c640d0200108040b401d180c143d0324280b5000e555540e031164803410099201c0e041c0301103203080d61440c0d80c00c01c0b510068400d4070003180d000310039124070000405078034400c40c0b42c09400322903d0342c0a40c1801c5610081c1c8035284542440d005160a083c0d0040c0414003462a400621001a5000035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 21504133 1250 21502883 21502939
    0x30303070f05070f030c02011205010b04060509030102090d0303050f07021203060d1410022502030318060f070c06090501081003060e12040b0a09050a120b0406060312020705040b 78
    0x103405500d0300000e07201501c56005044000e002203010010040815822240d00c0100380c1c000d0300c7e81d6000f281010b07090300c280c8409010b80042c50724180010000ca60181c805040342c2d000050025040c21103210100b0740c000c04c0c014081e000a81c564003030041c000f010803540c82d08054a031000c0c200301007202840040b9880041c0c0064002c0e0806141401070117011022030b01140c00c0041178910b07a480c80f800c00d80c01381d0042c0301d0300c109010310300703140400000518400c00b030910781c0900614100b0360018642400e8000c80140290071920410001c3c84400c000c0f001401968443c03540360021078180100100707547c2d4550485814000302c07500384841d5070412070541c01102d9001801241214001c248541440d61202881c048000701003008921a80c083d00038201d9241c1c2c80d650f100426648504101ca0800184201180d0000f01452240480d54030049503078414000d41010844075600d039586980c41d11598001303001600301c0e44013070101d0719090180a52480044450041000c0060994042015400303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 21505383 1250 21504133 21504137
    0x409060b0f121003121808010b0a030b04030306050a170c0a030201120c0908030708030f090705091b281d030d0507230601080f0304030803061003140a0207030e03070503030307 77
    0x40000e1090108003e0140c040e540c0001001a6480c40c810090542c0508003034040740c804a065021418920520031610844d100400050b100b9142d03444140a40102420960170151200c4021517a6142c0a0004000700451981c0580c0a4900e801107810070381c0454441b1b10984070100c0c1000980e900440208001c1c0318410001004851200241c84194082d404801140804501d10041c07080905c007a500c140d104890409560750b50b20318103901e81c08a4011550712412080c0803030448082da115003880c160189095910307103001c4410751808030f4101c0300030f8140c0942006030303209801d50062003006900e14580e660816100c0c01000a03440e01940d0455208116002c00e03083c0600022080d858200d80d060b40c80030b4504a1006401c0d1b0b02c0350780900a0080910034941c4130300e540480001145c0440b03400c440030505644808040100300301d86020340904064a404404c03451103800d1006c01e0203061007203001a600c02403841d002c0d0100c42c0740c10300b061182d048500204404d0318044102c0f5840b418034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 21506633 1250 21505383 21505417
    0x130506090109081e070e0103050a0803070e0a0e0103051605061804110408060f090c090105040506190b0c070f0e15010c060f020301050913032f010509030409060b0f 72
    0x1203001207490101507441005984500000b480721101040403408541006400390380d00c03151500d26180c2c03402da0038407008125901013070f1410081038512020f142c00048501d8102100130401c03000401c981c100d608004101071450004104001040000c504081000b414503d01c403890040060502e0007591003084480c10720104017022035940ba0b105411030b5900f41c41c0076840703a84a0010a03030315101110703010321a40100c0007003903286100144080b881c0c400104001a1030782024148005031501408881d040030038004401c0b80c0100c0f61610720085c0100c00e80c041c6c0c075409a0b5000070306d44038a540c000c4401c440b840d0014031041c40c092854690184001d0820007004500c44012200e4030100c0c0000360903249000b500c1c09035102c070b41d001103040f20021503011080781c5451440034580c1100341070040101d0b039a107408200c0744502803442180309282e00320340700000301521760403829250101c600003081d41001505000d89c4a4506c0307050041c10710a10b4039410507001004040051181030200c0741a0001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 21507883 1250 21506633 21506647
    0x1030903080a0f11070c03030206010e04110411070203030a0c06050c040602060115020a0503070c05010e150901030903030b030328020f0d0320040801050f0f13020103092d0c0b130506 80
    0x4590416460990822912540d07641d01e406e01c100e1800340303804110014007070311000041c050010120a40920303081070241c07030404000e130100402000d010348514044002030001d2030159405102030700c4168043c0d25050a4403a00340740c81c03022103500820400031075105100501c0000d500068141c15500110001001c004050a00f07030f1502c01e2140c0d00401c1444001400d80800400d01d04403000c0f1082038a461101c80050130070010303140603003d2085031400060060107070703e41c0700360003002d13002d0301900300040c60806050200c1e0466000c0e407030300e0640310140e1040c8902c6c004415418041c607906440034000440d040c5d0307620782c0c40d0081d01000c0d6082684810f846c000c40d01c400d11403e2401010120000d40c1c0e25940c00c5124040d00c811100710005074034000c00207008204a090403482120718050600400e0782c940e005400030000c0c85000e40710081407409544a01c046600398540d4010042d402ca101c1c01010302d00200c4055454102c101c0500ac24049001c0b00016102d0300e0090b00d008031021612003203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 21509133 1250 21507883 21507911
    0xa0b0405010b100906080c03040f08130e010b2106010804170f0301030309090b0102011b0c0f050115051903120806060d05010902040612090203100209060d0f021801030903080a 77
    0x2c02450703201c0d408402e5049114203d0340000503a012102c440e15020074a5a843c040c000540c0400c071400b515007080e2200c010700145507680201031908889008501007070320742d691403001c45001d130440c40040b80b00050354091400e040003044440340d100d403d56103241c5081000200494409040201119000c48608841840038020f5030483c90600202549a40e0b48e0b04000f445440d4038421014007924004c41d01f11107500c180a90035190a0600c00b015214008241c112482040c0309401d450311140d12200b580041c2003800307000c058020035268230383c0203410981048414111000742d806082103001c800c100180d03400c030100449280303900b80100107aa03902c020510a220380980340c16002c0c9040004100003406a000c5c1c4190b0b84941d135402c01c00518401e58000726040030340040d500d07510400041c0c240050f260014450714002401603414a40100202e10a440d03410803071041180e0003155202400c0a510301c25080c688092a0511001d80f0390f8801900408001d0a1009140e4481c0880c0070058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 21510383 1250 21509133 21509141
    0x70207090e060105150a1403070207140d0b071b080c0102030411010c0c030303020906070b090109030f090605030a0207061103040302060f060a031109060a0f060c120e031b010207030c031104060b0a020a0b040501 92
    0x40703009000c10b9891409d50310003920b454a501450844040072080100d0070300781180400e1059034024904038032519280002d45035000f0001900012500c54440b2100207a0550040c0c40800c604400142c0c407400d042c0752068101070b5414029040005070740070b0030007141c1d01100b03c5044a03018100103030340d1400540814001d204030400901002c858109000200905510840525000b0b58030162000d41106086031640098842c42002410500118100503000e03030061400d02c1c4101c9000485040004030417110750030132070302500075803c6001001103500d449100319070f02c13000c104d0320000d2450071591002d18500102506c64054a01d01d80066000c0d1101003070b1300c0140c0300000031300a0741c5a417817000600601c44504112003d0034804800ca40040c0500c08000c541c0300024040d00035101c403001c156090789040804c050451042080c0000802c5ea0901110003860164110b450001880001d10054800079480f40c0e040c4041000005541380e40410040c8074194441d1a0709550388072410b1542c054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 21511633 1250 21510383 21510407
    0x1020705031b030d020f120601050306010504031e050a03080a060603021c02070c050303040b090301150807180908030708090c0f030c040207061b0507050708160510050d05070207090e060105150a 85
    0x14174400503400c1c585400c5c0740c018100d4040e030b0a984c0d0840da5103030b0004480074007058074001d02150302803000340002442c0d80005800520300d000c00705655596900c950b450109a001700b5400705d0f4050701031092080590059901070013050806503d007185d9041c0e107481a0004519240e402c0b0b81c045000e43c100a201e9135410001e040003021661182d8503000d10703903402d034010001ca034401d41c6405030343d6414501c005281c1c01201c01030300161000314a020304403400016004120000566280242d80000c3c0e5204042c0d4000d030100d659444040c43c04007541d600d40682c1d116814030800910031940b51aa6001440602540050742c0241e11072080389440400f61072a41c515210120b02d80d8030105420b035112014001460180c005c0b41d000550760180d050701c8060410300c04410140b064000c2c000c074213000d41c2c0d0302c54480c40b92800b140b811010850340401c031101a1110b00050b00f0492040064692500408040d0072144000d443c640d45008001001c170311041303108031504240841c04e0280240038052450070707 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 21512883 1250 21511633 21511657
    0x61006080c0c100b03100603080405010e03160816091a0105090103090503040e0f0f0408070b060d051921020304120f050a03050903010606050301030809010c060b0a091d01020705031b03 81
    0x14083e443d04501000e00281c60358a4003034464660390f421645998051141169005100c561400e070420b8011148120a40980c907098403a1100040840b2400250071005044a901900da83c06900c580d06848158960000100d035082411094041c505250001d60400d02402e00d07940e00c00302000181d01600e104034010b48140404240040d4480b014258031b44905008000c2d140c00782e0703811260101c289001e4402030840002844460000380d40c41d5030b201c2c0c101c18024252049541c441c2c0d03d0030701d040d0288002d8041e480808404a04001c0c0416240c1d001c80705901e5001401c850710031000755a8007451061003820315104210703c7c00d00980c0d590100c116a013000036501780c0c0c0780c9403d024149500040e03215001c0d40c60305200140c03d81c8a0015281a258842d03006490301d1a0f2800444031030301c11040036a003c1d0355601340c09240303a8401d0700701130042810000100340ad801d20180d040071070004120201107070b40100008030019001108031050441d2908004841181074040303245180514081c03200c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 21514133 1250 21512883 21512893
    0x1121a030f030d0501060f020703110609090112030e041a010507020a1a0414010507080403030e12061501020f0a050a0b100b040b040503010507090303080a11070b040308060909061006080c0c 83
    0x2660901c00300050001d02c298280c180f0007039030398040031a607051a0102c99001030304044414800134406002d1011001300003028035050030010b0340040c005030800e034020b0805a51501c11002096000400c00d5070205003150100500b2881e4510404001804032016041010004e207400842d6256803840014001c401400941140f105200801c140c1c020b014800082c5619901500d00e0b62140e000c542c003e035408000541000d14542d030a4038a101080e1556500003c007a0000d60456001c1140c0c51003105001d1035106802d04134000a41020800c4183c0280ea8010701c01a00204100069112145602283c0500d040c1d41e10451901c6d119019040400c40300307000640010440c94030300240081d036400700c008004079140c00c00c0644d40d0140500c0300601107803000000580c2c0c004503904c441d500a0340c0840f160714003055a502c0003001241242d08030080b85400c0e051206070304080c41a82d80c4402c600340281030790305120340303280a8410f141c8504000c2011030400980144901004d46001e6054070007116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 21515383 1250 21514133 21514153
    0xf130f060501080a020c0d03020c030c10050117070803040303140403050f030a030e1b010311090a090609110a05070f022106181605040b010509221a01121a03 69
    0x4054042489041c2c001250200414101c90041c8210340100c540c2e100181281c29a180702980a034000240c01d07081d9000038030404080560604c0321104001100d54006000c0d81082d1a000d440644400b62482c03d500c000c01c284950031000045078183d0790141000c1750325807858140c1059522450b08024400c1c0a02500c85601c0f10001000d042c0c01402600c090104a00d00c1580580d20748480c0ca02d980755007041607198480c0e5022394080340214005803911490160300d400421031040560340130b80c07075040d903614003042074810328072400518030f0384103240520f0300b1711010300144580220403000e88034159003200c450465172010b04810700a440340c0ca0495544600806154a40b0022140c2c15070014142c00000210b10300843c0c040c00303c1e5607400c4d20684407401c20303003030000802c0003ca13005d052040800003203041d0340d6403c07407026041a040008810706030200c0d00c04400c1d151212801c401402402ca90000c5a81c5c0101511050307258141c6c2c0011100b1914944c01e86001ea6180f800d90180582d0b0450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 21516633 1250 21515383 21515411
    0x604150b04030c03050c09040b07141902030309161802030a0605090412020105070306060504180f06170d1407021c060e031b0a020108010b0c03040302060f0403020301050f04110f13 79
    0x8242140d01450550300040304907014032a41d039004440c0103000e4003052700001c00e0280a0301c40c581c03c8000c8185081e040c03501d482c8100d460450701543d9500541d2020040103403234a0200090a010366415007003203101441e2080740600300510140710500550044005a1540402e038441001008014850116410b01c1d05109078601d041d003510304015400c0200040015009005041c01c03aa040e648003031078503107840d18443c0300140ca10180c071003054079510110184900fa01840c809806007644101d030700c2c007041d0304191501440d417290b41c051000c2801d03040d0501c03405c4c1003503c0401d60152007515184000000240c0316042e1002c0040420b4941000e130b10000c54004080c1542c82c0752188114003201c03840920603500c02c0c040c0002800202d42c60014000490300e200034000b00301c00c1301c049a08054407a800940c04c0c0d00100f581a0704250042410415441c003401200e400449107607140c0501e04081d00e401100c0802080300c10b0288402064111140d00c0c1d5010b40e075040e5107a07803400c10160303010f1054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 21517883 1250 21516633 21516653
    0x2130b07020f030c130e15070504050a0e0f16030f060e01050406050d0b04021009080703060c08160c12091208030604051e01060e0d08030403020c01120c080604150b0403 74
    0x503801800d0b0804035a1160a00040c155080500140400e2074250490b0900d80508001d5404454038000c5949400c01c04048220890240e00f690301d401362518105401e00c804005254040c611400c4801c0503c4040c00a11001640040ca640d2040c91030044408054000e42808170180307048501d81070300003400c0004d22060754181d170012a01840740c960340d60308002c0c0d00d041551019251110a0000c42c00614120b001380646140700e04010000c00d948000d11401c002c0c140c1d0040c4e5101c1d03180c3c8002c08036681d1101440d035024142030342540007078084410040040b44902c3c4010403005050b142003000e00d02a08003040240074802c0301c900410b80a04c1c003960950008d0321503038029030074070000c40c44985101c021030f2940a000c07000c11010fa882c0c4001200c0407002c24402a800031140401900869800401103200c2c130f00035001001a003448000040035280705501d00303026503107414500b5280381d500985403500941d0403200481c000d01c241003400c10308119030f40000564440041c1c004100801d40710 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 21519133 1250 21517883 21517897
    0xa080103021201090206032d010b071a01030809010c03020c060a0302070501050903040b120402060913050907050a180209040b0402071a06010e09010b1b060a09050c0607030912030302130b 82
    0x42e550100e4609500e0440c03d036140380c0740095008405100048224085202c050035107007103000780340880e1024480d04041100203030030014404200040c1e4009102000718005c8052282d004a406e2a61541d16050424010345080f01d04014000502c40c080c18802c0020100c1403c000f010681d5458034800040d000750300c03009040b03407035509100000384058808407d5900300c2d551482418030341052050480c2c03c550004200704d0f4010828044200b513070311a000400401010340c140061103042c00302c140e030303d0500c1e0307940309911410007800240010118811145000f0452070800b41c4c0307a5800800081c0039201c1d010085402c1480802c1100620403041001981c000e14151041c0d202d4540a00460b1103912104a8030740020003400108443e046100c001d15140399440c40c40324460f2400140035040c00401d8900c96003643c0c9454000041c0401409003d061600c111901440c0071a15071300a41044101d00c902a03540711040d01e10014503029404488d4524900035001e500152240300e04916500100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 21520383 1250 21519133 21519139
    0x90c040e011b050d0e01060b07020f040603150b04140405250302060f03040303020d05040620030402090403270602010c030501080309010e0f0105070203010501090b010f020a21050403080a08010302 86
    0x140140e4540d11041c415a1403410b001003001400781c0804209a82941c0045045240c1e203a90785a825445d060130b204030380c0500740302d00f030f07856864850f4010081003060395010b5910542c6004000c10000d00d1600300610700f100c10740800314051845900041c01480125202e01c0d004510340c041200b00013011a2040c0000c0c0b1100d24000c0d96192414040c0140040f404020b4000108010100f0050800720182d54400e00c20b18000d45850110a4054241c0e441550200c0704c11351180d11690302143c44d40203044010160082d080d085240540010b40142030241016040c0160400d42d8412000450750343c081040c042c0002d00007950352200c00900a00c03603090314a00103440c080006c20301400100803144100c105940340e10400a030f079020444e015144c54645414010200200401038400303002d054001c0840d5400020041080c1c8005000448113010000c00c54000005600001e001d007851032200040030140c6102810110005450a01c902d030005404880007103503a251407940b080032036050324425 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 21521633 1250 21520383 21520391
    0x15040b04050d14040b0f0c0a0c030b06030c01090e0402030102091203030121150c030e1005040b010519090c02030906070506100e0c09040b030309040501060f11060705040506070609020405090c04 85
    0x410300031189000c40a2015001c600100002c1100e625240043d01101d81050212490889047c007020314006445908a03004151403504006101c003880016601190a40141002103524400240075030500d019410f01c01e0120310104007551002d5064075444031000c2c02c10005c0d1080c2165480c2d0342d4000340304200c03115402c02c03070b281c0d601c07282e80250f2000c1030ba20034070070f401d0f604002c8981c07005020740034a03035010150384031101e6907540000c0021418190300000001501d060a06041d410442c1c160844e50041090f5803030f1050b50142c03040540110380040340b00150b12224444120300f0b45c440e40d0401540090003044d00e000340031003c50124050403006040703511072680d442c60312400c620212151145002e050001102c1820542c01c20030380404005c099900d440c45c43c80010b0222502030b04a840002c0395a40c080380340e1500810045071401c1e40500602981c43c01c018000c00c80c0c41035024150040a01180150800085400494010758010000e00083c98a513100303560310200b00c40c0c014815820 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 21522883 1250 21521633 21521653
    0x905070804060b01030b0f13150609090608011a010503090c06030103060501090c030b061b03040306020301080f0d030e0316060b040e010c021212010608040305040f081605030609100e15040b0405 85
    0x1748150046c0395800380c82a1640f20505041082440800103052030342511400910401c2c9640035100c000b40c42c030b91b11484040d609040d00d8070308558854001454580c908900400707561000d0039102c900010900c2c1c426035958450155034140f0308090555600400302200101c1048803d80103181a120340c54000c0000788a220030450681e48100c0d60f144c0c110b04108045258105007040101c070f94840c08007101d20341035036503440104a920990205505070060100ca100100d0140210a03241d041d5190510110040d40309280d103c0c4251280158400c0d0050b80c400304125040d040b280360b44100070030401c881c060441d0b05078068034801d8030b604014003403407407020b2000000b1000c0d240e40000b10700d003008043e820305e142503441c01409007058080c0078081c4400114011072900c4580909100350161104800715481003141e1032454020601c2900101e0400070754020008400c82000c101c0f040118103203611140c030a0030200c4007510341da000412503007000180103c10760203e000d18458011500340d801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 21524133 1250 21522883 21522887
    0x30207091505041b09050f0f130b04060b0a050316110a0c0305060106170105090a0b090108010e060604062106020904020d05061c030203032d270c030718060905070804060b01 76
    0x1001000304c00318001d12424440340c24418080b004075038000d041c1c01c0c144900782c400603c0c0000d8015400704d486d51200301d90151070402c1d0203464010544521480d0502e035603810080e046010040c000d18092481d280c05083c12403040c99818244403042e01901ca03880b0480c18201d40082c0c050100790740b42c5c030800000140d440e00c214003a884420180142c00d81d542d0030301c4100807078110064442441e15444249030b07a400d90710b6020f4140280b4540340000354075040711440c00d003000340003071543d07118515100040021103ca607060300e110741c022445241d003a80c030790704d00340f0000c0c061152202e07081480483c0801c0c1d030303150607071180340035080c21200701300030b00da038841000031055409000074016001480400c0d04801d00107400c0194880070b0b520341440d03610851000c030416804403040d11109580b0311300055007145003541003842202c0ca2010b044c480c24408042540e614840c401d02c0d500c211303030381003032010440141d03c2203000e451121018405400c0c42c0c517005020030307010340d002c2d50b4141c5800e610301c0c039540c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 21525383 1250 21524133 21524171
    0x2160501020f07030b06041119020c01080601080609060a09050115080a02040807030f2409020108060d020109050d0501020c01020c0a051b0d06090615030b070912080306090403020709150504 83
    0x300c0700d40d005001d03c60540c0d8558640d41c2d0050f2049420030b03142d120200101c0c0c9241c7c0940701003400c07044032810984642200901c0d100206156070b0510040c00c0034010a0307644450002d5012006591080381929000040342c42070516a0111048506c0c2c2000403402c2403a9484902a074031069a4903440394607500c17130785000c034030491003078440303980c0600020000510364401d1682010f000d55074130b528440c034201400b496010b40d5101140c200b0303520b038207120440da08401f40541190b0700ba54004a0028113078006085d4050034042c0d18810756681d5010000c05ca000d4045607180c01c0c0c0d5000030b41d1202c20000c500780e9100040142100c00b401641280ca5142001b0404000c2c1c1c0c07400102500354065464403040024a00050140c1d2010307150314080724095400420031004600c18018180c19181904000380035240a4004019421040640c40b0100e6050002d40b9044401100c040e41e0540711460140e192802641c0150050350501ea0385140d080c00240e0310b40112102901e00340844104001581000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 21526633 1250 21525383 21525403
    0xf110d03110d02070807140a03050102070c0f0605030610031109030f06010e0702030c060a020f0c030712030605060a080105151201080d021e0a031107081204030501230a0203061801060216050102 85
    0x80c0c2c4680c501f08144a07510944000c0400f0142c40107000c61340303c0e1102400da900c060400e039505901401c042020701b8800c4c0098004107030610f4180e04606000001804800c0118000800c054450043c0c81603042c3c10750480b140040d00030304403006880911005a1992001d100c3c0050000c021800525014008003c2318552080d00c0b01801769556503c4460000f9001400805294101481901c645810030002070840038003689415008158004008081c1c899542015000701c0007880012300386508410300a042d0f850450b0002611406e1860504460007060401280c8102c260000a030f120303004074448019101550994400038600d03801103046101400b001e480da5072141e00c030140805e01c01c1480d150010314400545001c1c6550f19425454040500d0440c800c203000088c0420400c4800d1080401e140b00f0740f035100301902c150380c1180b201c4540007001040300380e030008001a0035541d001c500c621100440b5150f41250351315050002e54480003035400d400b50720102c8802150382e41c000512400c003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 21527883 1250 21526633 21526649
    0xb0f0301030308130b010303030b120102090105090f13051003030806030304050a150309150b280b070f0c0905040b060108060f04150e1609060f08040f110d03110d0207 73
    0x14592841d0b0b0100d4161030010300d000704043d00d80044000041c10108454001c0d0300a59001c14401036903410040c142200e0403000c44c0700c0e0720401c00310507540d820400384c807502003044a00c000a00e003402d000c5101000180c9100e00560718110401c040d0352004402c81d010f0702d00a50781c200450381c41205040da0703842540109607210b80142800c00c01d594014503040000319076807a0214001d106a0781e00380b40e0740e032041e2040541c10380b00d003003000c1135003000300541c5025070b07041580c015140bd83d00c0c0020295601800703000c0314050005241d01c244074240b41048205544a005020b42c40c1c3d6605075500103040c1554100da040c07400300003164403503110f103070068004c19000303001c029030310341c2042040010803107403200b100351403c070010001d8404c040760321142c8152800030202c001e40c0c080340001021034080b80c100200b8030000d09821112141e0101c1c1c0d11303500c50b50000d142c4030014110308000f52884001800d1a0740940000c20306000c05a2100085c0200d011550031a0103042c07038a00c0c00c0e03032074003414010320744 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 21529133 1250 21527883 21527887
    0x10e01120212010b0301051005010221041202010903080301060804020901050d02030d1115010f08010e120a0f030b0316030204050709050315060111030c0a0c050402071203110d0e0f01060b0f 83
    0x101501d8502e0805842c503580074000104044803d000c80d00351038045030580005044104100415601401040c0c8001002030100050703000504901c44c180c0550b01824610341d01d00aa680c0442e401020100091508080c40513280d603918200140600d200300e604900500b06d00c000003e4604144c8443d41c80c25a000700074000404100c5011200300a608014040c60310409044207217100984458074041e1083c00004d503106400d1506a03800d5031150034209009511444800203030100250655010b0742c414940b2200c00718168900714054443c60750f805600d401403451345410312800801c6c15046a10a840070b00c499603076900c0542d4410f2441c0b103111340580108850b15510650303111a294440c405041a0314000f00d421465031840c0c01c4500005020380c814600c15051204409001008100440b0150301d4001c072a6540354000c003110001c2d00c00c2c141c03500c1035000c8540307400013a13408000c010441000214020080140d8505004007510402d51805030003017988501c0c00200c03091504c032118898 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 21530383 1250 21529133 21529169
    0x90606110a02011d0409030201050a0507020321040309030c0b1e0a090b0d020f0304052b0c0201030203040c0905100302010806180402100302040801110a0206091614030f1002040608010e01 82
    0x340e4507090007013803640e101e2100d109034100c035619172240742c12140c00303a4000140e5207000c65461089030000340045065601c14800c004030524542040702c04c803050780c0d00c00e072081d840300d19090341e14506640000b020054002808103d00c2800800707465080702c2494950182c800007480755625200302001c2034002081c00000b805444c10322002400c6411002800525090121035069a940c1003a141150660000c0a0102a03000c030f0022404600285003004849060041b2000c0c081554580c8005c0c18150040000750501c01c101c00d007400106101601882a45810804052480614001240401c01c07040c04541e16040c060410f40078121907100807615500c8039020042c0300c4289180c03007400c0640800c00400c480031300303002d129140d080c10100f40e501c0b001542000b905103940140b0340d00b01684100b5284000c0c00ca0b07601080f046807001c43c2e50f01c01c1020000c001c28104426094a0b41c507030720884000840660341507000303108440c8203603181d4200741d0321201c450348002c00c20701c1140780c014a900d00007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 21531633 1250 21530383 21530387
    0x60a0b090409020a241101050112021e0909030a181214070308040b0301090f0b030a06050603010e15010312090b0703030209010e040e01050f011502071401020a020303070804090606110a0201 83
    0x10310a90f000615058490796500c0300c4402c400003451406490040c050750707590b407668001504426508441000780160340c108802c855440c00e00382c0019125a01e2101c105160007031440340011441006404501507260100d00e45550303a024004840024000c034010038902c4030001d0090081d160780002c0140e0b89520354031040c80b0818104403d010501544e10b00000240c0300d040200000c002004032070f920f030340c900343d4944210307424034005110b81c50a18859004664011407039039405940940c0c009000d0725040042030050500303000000355441544120070103590101b440c14100d0b07100c3d0f103600c3c0072444054400c45c0e50350304078810211203940611110001a009030080d00100d001031500c880130114070000a02610160071040509940d1142404801c00441a00707038054070124011001c01900c00a000356910068414840c0343c2c15540c44441480c5c0c401d1118004182c0c004044980761419030410040560191081c0425030386040c00c00150140110701d20200400d0002c06444410020303001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 21532883 1250 21531633 21531641
    0x40303090e090f030d050108011107080a110f0703050307020a06030b0102060129070f060c020309010903060b060702090c0424050a080901060f0602030703140306091603090203030711010206060a0b0904 88
    0xc0344000b40107611004920f16401c001804010160741c401146552400c0407803400c58040c2c1c00c00240d01c620400c08000404c810340c00f01c440b40000c5243c450028021840502c0c2016048449070300107009201d0000180070b4000091f010f000d0003103c40c2d4200c1a600d00c000d4049421400301140075800800042200000c1103480e13220b0880d10311400007103150300c10449101c992009800306c071007401241100e014090760344a03020b0318030302a00041d403500c201c140c0080c104040900c0014140f580310b0000c026151102d40030358850740e50213002d1310118104254011410b400c1401885000c10160b840d18001e4a2038000601a1801580b03a0707a203007440503d800c980907000180a84025074039150002030309240080141e0041c48154061038603400c0c6d070b14006144601c28046c035051000184288005552034020642c1c0004a02011a01c4080064000d0303001e01030031a00650306020101e544018404039413689403264000364207030b40c0c0f80eaa4500401c94080d00b0b5001c1c60702020401e010b480100d04103540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 21534133 1250 21532883 21532891
    0x6050a0501081f03080a030510060203030c0903070801020d05041208011a03040303090512190503011a07031206080622030c14070503030f04060f1106040303201201060e010302040303090e 82
    0x1500c951880b0040ca0300040041c03264130489511a000034162101581442540c2d00020340c010f0f0001800e14015009581e800050108540b01a000413030042c240d804106071001814690025501c9810055101c07008000c200c070305542c00e540101a01110510030065039040e140306c013400c4082240c40c00a02d04098000400860070b1550f503100d11008103c0c10000c0302105041841c0c820742c1c41c80c1590b6640360300b0724140050300078424288010700220044614060151214558240d03e8078220704088458003e08050640040c1c41c01d000410003440102e03801d03206100500c1a480e080c00a44400c00c4e01e4008900040c1c00210031886100006000c40000020207030180100c4541c42d440c1c500090543e0320040c04c1c0321100c04c0000f0f08110072034007ca00b42081041604010404001d14001540c550b80d009100800305952010000001d80464480f44c42002c660484d01e92500340c01c00c400000c0400a0148a000c03070351700300340782105610038000c541c10713250315a031510b001f41e103890091007400300003030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 21535383 1250 21534133 21534151
    0x1e08070506160b04060e0303150a05030a03050316030617010e01200d05040203031c060518010302012003070602160c290d02070803040c0e07080c180a030b0118050a06050a050108 78
    0x103540c40d06d12002000518041c468501a941808107200200f048020940d441203020740c002c501c48001094018003501d5210f00918814581040201001c07401030800390030140307000c0d00c185400340840d4030544c09580750b500290000c102c42072802088814a110a9039182504c1380d040006203885456500718940107803010f002c0b0b80c101003251501b00391404401418440300c07595007c0c100003d240c001d0800d0b052560040c0040300c0b55045030002421203400c4400100121021001e50040040400440c2c92558010408548a88401c80e0101200050030340603070384411040d2010840542501d03019464290428a5a1101346840d9014210f42c11905114821950074040345000c558180019842607120307150110f6031605180610b84e26100c0a0a500b042041070401c00401c1c03011501142c2c840914904040a01c010520001358420005d410040c10b4100e2600002108141d101c1d0500c44a841400f00348600c1d5505666401200e40c00c1c4203040e401940ca8100708403c0d4003400c40c90750411815 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 21536633 1250 21535383 21535391
    0x403030f0e030118050105010506070203060f04030e09040b01080d0201110a03180b09070501020d0203090102060112140f100e03130504021c0903170601020f0a02090a061e08070506160b0406 83
    0x300002e42100c01082c0145400902060301c0c02c2001000c0c452a4090001200c1c0c4500b070285940120b5643d0384018010700c20101c110000c141890302070f003000c200091001b407413020649001e1401320101c031421322458215200d441200d100650060090f80d605800405c807460900d14040422030107480e40800140c00c071840c1004400100700c3d000a07080c0701d49030003130041440700e1034000024600100c0d413400d0402c40d0014000840b0983c2d002c2003290440e4410007040c0c1e6100000c1c24000c085940301c070940c0c2194450100c0098040c800411800582d81080c10b040080368000e04403c6d40342e100d03941e403441503000b40c01000e120f0341c94150701608000345198458403189080c048110100d50700319105402180300b81414010512070300054035072102080c40540000301c078a40da2240d5441120390028800c6a8100000b00010300f1a0712040003004240030448420300502c0c001302440c40140241000342c020b600d03000c665420301d2802c40b010300d00e0750790140d542455240c032044d11548018004035011511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 21537883 1250 21536633 21536657
    0x140c03060c0a12050103062003070c1b08010203090105010806010b04050303031602010603171201050f0607061e240801050708010608090c0a0e06120705060a03050402030f01060803030703050109020f0403030f 91
    0xa0702c84e883c06540704003400110140003034603c411400b042e2101c0c072280c410400070003459507031102503040c0c640e07480404000503000030070390000d0741080354020340e0a40d0b10200030442100b905401890484050f0410341d040e81e601c589a0791098070503406138940650040010134207a0008401c072038282d005e64400018025240d030b807010500700c24020110b10540001c6034040200d65880d0a00e801044111010800e0b981e01c0400f0038103600502c40007a003080c2d90f07a01d540c4074101c1c9508007030700303013451500d0100580c80d081014640d004074018102c0c08005820840030504282c14401d4034010200c548441b40303d0303132034007000b203901000080c919092030003885240306158444003102c1e005402da00c03011400c1c600c6c1c0b1109101883c3c0310050400d2082d40950410002c070f8580c00c003150541615840d022503555281d0011910f000190008140c5c290b00e0a000051480300101c05140038203003640d81071069036030354161102640581c1c2004d00301403030b082004200003800b403e40c0c490410b0450402c0d40d04142 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 21539133 1250 21537883 21537917
    0x206030411060f03150607020a05010309060902120307050105010503011a10050d090c06081b0405060a0c020a0303020604050d0306080714130c081519090e0304090c0309140c03060c0a 80
    0x3908039a012240c04402d1217090000c0d420811a1140207650442c20201e550700001c031600b84a204580c181951140b00c8001e0000b02d800000c809500540014007480010781d00550720f41c4040d000703803419403800c0c001140918044c0200ba00d05000c0c01c0f003041591005004015111035110704032000c2c8101000402103c1c4a1307030080c00e403240e003c0c2500c08009032400798090810400240046055041700c00507004d00780940e03040d41d003030b13800c1660310f00d03144d64400c0c1003550b0b071100d1040d0295008280d2840001055400129607100390301c02c0c402da4681c1f18114000384c0c152001800307042c9094014030400d0007049800a81d00000c44001070400000032242c3c0d42c03031422102c0010500700007420140801240c2800b0030103049081c80203542c1d00c803c0241003a0442904003040c01119815030302c64460100810080058030040e0100032010800f54112803030242c01484c4030603044a9131100c010200038000360204003000a04009000352020781c0d1103072a040303a1035100101d500240b2801c01c0611102c08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 21540383 1250 21539133 21539137
    0xb1c11011b080306040c050909010b09010201020403080c03250c050d02010c0b13110a031104090311070801020406080a0506010210050901240801050a020910030c0c0f0605160206070c020603041106 86
    0x640602c4490b0356038100324061206840e2800e50003130038000200000d680b1a01c0760421181100d0310041529128010076004034064801c0e6400640640c04c0420f0070140d8110110040c01d404109001c003640c1608041c0e4884010444401c0c081e0600b008804100080c5c1080604103002c60f105142c041c3c804c04180da00c00010725001d4801880c1721500c080c05000304200020190700341c2d2411604155010b1a556610400303045011801d4015a11401c103c400c1602840c0051901981042030f50201071300c412280d03000350401d100c0c030000203075680c021074860300342c030b1054500072701040e405403540750888070b0400060000a418003410350360762000741000f1001c802c4041c1d5024400c405000301c052902080c1800c0da01c0103070800448a10401c907210f156540d90440e02080b282504002c690344c4203e403400e448600c5210805441e17100c0910b060001c01002c3d5001e144030b181e000f080c410030b4030412070040b6a030300700485010001c41e080180ca030015107401c4000c0d65006200d0b0115280f201501c0010540316 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 21541633 1250 21540383 21540437
    0x112020c010c0917030a0c080c0102040602030d06090b011202090a090c02010e1b010e011206030503030112120f0813020607080a0302070203100b0f010c080d060303020f010b1c1101 79
    0x2036503460403031152655100c1802001000c04c042084580480c4003a201c1d00c0b071240090a406019000e68194200030200041c4d07215000d181d1300031500c41d59501c40103074980c0d0001c0d42d80c0c20104d00e0a00c2c0403400a0451140c400b54260603136a0900080750102110029803105903010b0b4000e010103400030310310186001d24280d020b07071a40080b401402c010421071074400c2240b0b6009803041034400441850b64062150741120609113000a100610015464001e00d459000070341107000010000c14100504000d1a00d064410005401d112495040c00c442030311310a043c4030700140c2c40034003003042140c0051013a00701c1800205094680b0205039150340441c3d0018640c40081380e0042510b0301035240c2807202d2aa02c011643c000d008c0682e0000008074071310480c0e45040d060140c000312490900c582c0c3c805440100c4d100304002c004860300c03810042d5039604581040e1400d5801c09000b2212400d1200800e421140780c165440c0d159001540e5000c9005403803c0414104640940c5c0080020f42c1d0708046069 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 21542883 1250 21541633 21541657
    0x3010b040c090f060309050a03030203250201090c080d09151b0c03140a08070303050a0b120f011d03030103110d0506042a05030c090402040612050106180b060406030209011202 77
    0x2e003480c0c0700c4000c02c1e80380a98061020702d41b03800c46840c007007000032035100040d552515005070740f561f135913017195520601071000101d0755030104443c5108940562107198440c0c01410710701c20342c139030794120b10b6640c00c2c020b182c480c0081c500e010100500c540d0800e12880c000400d0400c8809907070540c1c40885000a003c034141c4800e40c9001c01001884003540d40c0b0003e0b100c40b0406006501290744403401140b0800e2070040800d517840380041d644038a00c2d4801c02130614000e06003115048070380c03580c0e943c62068200ca80340c59441d09002c01410045c9901c011300d181c403408041c43c10f503031842c0c80d9112078490920f5502e4004008840340c800248042c8002442244941400107900c0d1040d041151030400d06c015288500c03015030424001a58005580040e95a04a8580c1c1c4580d0b80c1d480030801800c000da01107000b49007045801c45c00c000043d009501620b450a0003021b03941000d500c01d5042e40c5545201903003181c03003080300b80083d074400c2d00140743c80d80060401580d1700c2c02c0380e0700e0141240c0c0302c1c288110ba = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 21544133 1250 21542883 21542897
    0x2030c01150f0501050903030a0806180f04060e0102090f0d0206040b030c03090705010903110409020a090c0c0213050402101101141302090f0606031314030d05071709030304080903010b040c 83
    0x3282e50034800c40040506400c1c42c11608151105022030340d07a218401001c028002250005550307a40c544400d801c0000c0c2601d0a003a15080510010301c05100680d000c980560801d1850085454140300f0789501d28001841403801d5a040b005104030706001c100180c1e08800108001704022554600071401091040419592407a2085400d0308180c2c65801103410040300c1d42081010806c844020348881c4011100000c2c41d20b11480040c40b04a40b0741e00481e011414489201c100329080490b4a5405000b590610200c4e18218100d000302d40c4112002507014000184002d0058442d00c0401071107900f0b0800098503030302c0c80c581c1c0034181d14211124030b802d02c055800d000c1181006c481c1e2582007043c42d400400c150404030002003582c040240001d166407010511001481808800d244001101c0401d40741d85100c000c481c94050403044400401240020762500000015021400d110ba240383c0082e504546480d51000c40503485040129411341d215441c030f040b159100e2240803002d00c940d4981d0f0ce = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 21545383 1250 21544133 21544139
    0x6120c0602010603030801170a050f0105060f04200906040e010308040f06030e0706050c0a0c140405091902131e0f050601020a030c060c0306030f05100f0203060102150702030c0115 79
    0x1061605401250459062035400c000080c1c01902160649036000d260040100448130100d19104010b04003400c103100c0e07074910b2040890f0651202e4060602070b548502e040040e8401c0c0001e481210310b40303072002c48c011003008621541180c06080303402401080a4034081d81d80340300041c1c0c4003007a00b05a900f603800050400801c400300088800402260078180000c0740d090030041d4403042d2611450b410b004d800a03c09031025007c3c80544a030703903400b8215103140da0300d81e0500c4c584204404040d6008a00c1c1c80049010014002101c8908041180300000082c941d6807d000034948031040d104541501c030211000c0c440d5001090791b02c825490a40000d03c070405000f04019102c010705264155001541e40b1030100342d0202c910206c0c20b400a2012902d10a111401c034014041980301401040604400008000f0041804041d502c4200c4040c88480d4440d03030f1000480c4001e0f21740358050b07840f504080341c025850104256104806005590911105111040c01d540d072002e560300340b44101030350074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 21546633 1250 21545383 21545393
    0xd0303060501031b0804030c0305042d12050307031103090d05060403030506192303030a0906020105060303040617090708030c07060908071203050c0a051006031a15040b03010f0612 79
    0x8030404144a011342003101181400034040c2c01d005000981040014402181814011000c0324020300140d68a408080003441c030180ca090004001c01c00a000700c0c140010340107030064104080380742c01001842c034141d5182d80960f12041d0302c2000312804d0005002440c11039560042d05210700340108054000e520305071034000d044900c0240202c2c840c4540b030344106841e04030791007140141c5411076000c04e515141d400c0c441c48031a02c07030b14285506110004400719515030049014007100e002e0340081c041d60300d4031800c2584078040c50142000041c507400c240201e160124801541006c1c10341c003502d400a448103156400d5921041072030040b03074040c103404c100c0a036115942800400c000005445600d05280d110198400c90f8903026040241c0801d80723009128050042844c8207600404030350007608e2011540010b02460310065030b0b01a007101c1d039001402030b55112580f00c3d040b4802c0c1c60b00d12103034400c02c00000344a8910807641540da41c0144460010262050f40c02804121441200c1000c03a4900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 21547883 1250 21546633 21546641
    0x6020a030e1605040c0302070501050c0c06010b04050108040f15060f0f0906030b040201030b01111015080303070905010f020309090f0103050609030c0c091302060a030f0e12030f0709050d030306050103 88
    0x18000032580000e160b400d500d410102180203540044501090000e1a43c0b0300300c000c0c1c00380a4000d4901c0d4605418490f41c0c41c00c1d0002060345c01c40180c29951a80c0e6a1100d03001d65001e1403041c9408034a01800040c0040c6411490040d203a2080421441070742c10100000e00319459600410a11000c6d40e0060290300c950350107000042a0399601841810f04503622041c450f0000b520080c1030585492407c2c0f1542c0c003680007078481c50819821030b44c0303101d03003162448094051184600b003400090b040103d600c1e1404004c491142190352100d0100901c1c2c0303001180e81071860744040f0210b010500c5000100e44e40d91007118017412111050030115411810000c0c03c1100281014501d944100b16843c1e242c0f001045c00400b82a0456040c5035030f42d10032400238801d2503507180007903020074006032a00f1100d8040c0e001800c64a00c4c80800c01404020005465840c481106040c0030b060091000518909000003150f901c04400d240100265582c4c1c0c01045004068010480200c1d858a800b84919645842 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 21549133 1250 21547883 21547901
    0x702010f06050d02040b0f0d060902040b10020303040b0907150306050306100f181107030201050a0c082e0503011d100501030209040305030601030e030408010e0c06071a070306030b0406020a03 84
    0x104a00c9252200081034900421002800b6981b40c0d801490070350f444103c0c022180034085e05424441015152403c001c04503013404901c1203142641508090900100081a135891900294a551510b444265505100600d000203030710035081c0100310220030720400b95003d1203645002c0b40b0941418101410104018400c00c45075a0005041140c010a80301e24802c84410340d08402c42404031003902d0000e0f080007560320356000c100007241010541d0550026104080b0707407004114480380c5c00421121604144c51815580b0300340b07400c064a956040107952103800c007840d003450300d0a9507040480e01392602c4562603180362140565440f11032009014402300303985079080400041d810341d40054070b40c200103000a0100080800020400d90203a0310070152200782c04226500c071952080858080c0186041031501030160740d01042040c1844010b40700c405ea800a5802c04452082c41034480540e4020812010035841f040000701103030180460030b00640c041e900240e584c4030607000243c05c3d11030000b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 21550383 1250 21549133 21549161
    0x60203130b0f0a051303020307030b010e090d020309010e0a03020a031202120304021305060301020d06030501020a020d05130302040c14070501060e1524040b0f03012c01030210120c08070201 83
    0x145090680c00c01c400c44002c0200d07030130302c25201c40a42c40004220314064000070740601c10341c403010040c0b0441490380c40c12517881036182c1000c0e9a44103202a250700800c114100542d10512a40840350302800980c564214080e045110f801d6481c1c00054508a041d0700c2a030720400c18404040d4101d5047c032143c05041200e06030300c2d20710b05143c3d011440745c1d1318141905603d9075550002c02d01c00e42d42074040b2403ca0701e01010602400b510f9003800d600039400014000003503c03034000213000040c0550290741c41d50039487c000b080114599024403000e040003551001c00c1044403004103000074001c0011f0003096004400002d1028200114019001c0e4041c00e45850301e010201c40ea0f41a03a01d846004810021461180110303c03040e51074111680a070341c202d0b0700400000b04402c90226800c1010714101c0d260350124542c40309083c8e0204499207280104e100d4189212001400542800318200b641e0390001c0c41c0091201c9605100301c0100e50031600b410700010382c690140f00c500b0f982409194a4660b00e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 21551633 1250 21550383 21550387
    0x7080103030210020304060b121605040603080316030e0307030c03080f16030e0309031510320112050f04030905040507052b0c050703120203010e070509030a0c060203130b 75
    0x68a010390350b6150000f48000403900040001c0410a603600010740c809009030100300e43c2035200d096103803103900000c510710303009101102c000340c07500e068060001100e0f04404040d1440c0c4031440c0100c0e05540381d0039a541803644901104201e00d80400061010a00a82e43d1744441000d40c90010a40c64020300100c010131030020901c0034820500d49a51300400c03040c2000a00c18203030348082411405900610741d07250095983e811480303102039130351510a40c00c0d41d1821794503588134021610480384081d100c5007100400709214048080300c86900c032011b01d050402a803852500d19100080d00c6007296002e42c0c0c001018140710803d6003001c2d964000d41341c1224180a507103407081c00280b15020703405022240c442079403401001c0814458440e4072805140c513080c080b454204078090f000d43e00030035085000404c82c9050784900005031003601e0507079010310031380103a54496840480301c03901b01400320740d4180030303410314640018805a405001015a60051600c070000542c000403100e040f680310100034481 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 21552883 1250 21551633 21551639
    0xd140c0301091505090c0a060f030b090702030403080705031204060b040b010c020603071b050109060b01110706050403060c1b06061505040305060c07050703060507020102310e180312040b070801 85
    0x10706900414000f200c10b070300045541e1a242c149140007800b409090700f10642031340100300341c0d034044620f44e9840d01a032824800915180180141072030212141001600188014000a00c407d0000d1080f5801002200d080a07400c06400c48a658140c40413290655181da55807450b040c036001d0509400d4090801808039103640e004605507100081c014001c0140c80f49d080041c024141400340030b01c0e070b0058004c00c40304260f1716014008240c04c103203c0340464078480c482e0000400005115003550b90b1035442500f442d186a4400003d86400102242440b0f441800c451442200e2050340303e100e8050b80c0c01186642c9807017008410f41e11060f10807800c0040400c800e101084001542c40d40220b114008190b40b00c03042c0c2445e80c1010440c0e00010200341c01e0500b8000c445905401178901d921000d01c03407120b6003400081401700313080300f842c41c184e803800c10740d20401c103914108201640c42015100c1c01c0001c0390750390146900355803102d60751000740785041040c0018800c00c00200355112031942018103103541 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 21554133 1250 21552883 21552893
    0x10020606130f02070b04120e0603010807091104030503180123250503072901060f030b031002070507091505090f07020a140d080906060a0b090f0d140c030109 69
    0x8414403494801c5521150712281c20030095049031350305a04407018112906007403a040304084d001c640b1440010f40301065a44440c9803000460b412134600f000141955407034012076a0180180805070030716841d0038007001001c00c50a000400300100084020b0b9070200300000003614421402a440012030540c842d00310f8508030b40c4003113030b240041c2c00c50a404062040d880c0d0b404180c05c002c50007410ba01000c101441001100c0782c009074250441c60940038110b82c1d0155501d2280030074810314000a60401110701490f019505c40155800e003e030030343d0303d880101d00341d40050b680015020ac030395922294003048034400d988540c012118114074113401482c946000602100006010440700e01e41107000301c0c00c07a600030400940c030740b03600034070400c011444000010b440b4095149941c0100b00280d0000d10035020128000344109001802120320b24240004400d140e0800003906400201c1892895040d94441d40e558148074426180850201040c602c0c071401c01042c904014020380c102040ca9000030f03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 21555383 1250 21554133 21554149
    0x501080d09060c1511030414060403080121080f0d060b0705070b0a030906051005010e030601081207060609050109060302120604080702010c02060d06081e06061807140a0306030210020606 82
    0x620245408402500076040a8008240310399100d403071180345c054034145000f018000380d0f10960180c14000c46241000d612203407240400c844c001c0c001840c0c0c200600c610a4847d48845030103c4000141d13815400302d55030600c00c1d90001201601d00200071481c10700103040e5015020151070346000690030600180c2d51282d40352268016603032500c101040c81c400f941e11980c403080c1003a401c10800d20140c00c0000a00640a181d8000c203800a62185084150390500082990480f41698001d1139114040388200c00c03180c000040c103d6403180c4a503c001410074450145601824803400c0000c0e80034614410480240b001002d0710301c5030b4000e5004c00000c120100b06884086c1d4080c2031001c80452188002a100d01c02c1000403a41145080710104003080d0001e40103000a0501e2205c4203d030f240d00160765174074441200c1c8035a000e04180314400c10925214034403030308106982894821401b0784000d0118580191006100207075032590b040040d40390440050368008003d0029040700e081400c0890b180b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 21556633 1250 21555383 21555389
    0x50d0c03081b030403030e010e04021206040c050904060e180d080a1a04051315020f0306151204030c030207090b06030402011d030d030204080d050f071103070e0405010c030501080d09 80
    0x504800315940c0600640c8201c0d0b400000d8508081d20343d02d41e01c0c0d2401900408012200320f00281995908440b1414a44210382038000e08070000741c0c142d5242000c11000d00054005402000030a10602d4490b171500d0064001514024103020007920b0601c2031803450000c1036020f0781c140e83c05824202b0303005070401c4c1c0c0c1c1a040b80045001141c0b12451040d49100f0311500d00703806070483d01c1c101c01c2009210035606800c90760f520418484054207017032100407003680100080745450312000c0012908601d8527071081c052600d03480400500304007c0d403100e1aa5480100c07000e40120362480c165504059041c4015009481c0028081201c1104207012804074040201b00a06001e91621a020300e40078500c01050b400100904490b989409010018040e41003403081d601c0d5845500580c0107064040d10550b1000002c041c08582008041e80380c2214032a00118403075054020218042b6403482c40e44065031040340180300104400c400c0301401422594142e106c240190030008a00e440c0381d510040200031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 21557883 1250 21556633 21556643
    0x1209060702060c2512110d050f0a03050a06050301090507030302060604061208070314030702100e06040503120a0e01020a110f010501150507050309060409090302060708040c091d0a0302070f050d0c03 87
    0x3011200d00c2d040c2c110204c10f01c3c0d000c1c04180740c26011640d1107a20007110001009000d066402c0e42e032441500703441d14090481100a200c0c814008455024425808035a00100f094804074034541c0d2840402d0844440401c10740760b9400802e000d009051b010000310b9040b903000e071070401503d803405181407070480c01910020100c10000548001780b5105d03503a0702c04805203141c070403503882c1030210b030295070359100301c803078544507030030141402c1c854807020600d01d1086030804059843c24075194001110214024500b48116541d03046a01c4283c10074806441c0042e915141c55044c1c80c2042c03001c500d0104a803003484020303811f00740140321203450308070320740c0410845003841d9494951a01d445402c5000305040c003604268086000100460305411600915002c2c0d000d0b5800ca880300d110445003502c0407a0040c001400e4103c0401481d140c607400308403a20781c070212289035141e20600b400d00780030300d001c0c094005a1200d181400a1445c200c0300c0c8005040032184000501015038402c14403030a00d11024003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 21559133 1250 21557883 21557917
    0x3030306090a0207020907030c090b0c06060d050a05012301080a030e060306040204170c010f050a0e01140c0a0f050105060a080c04020c0c06030103060f050c03010303020c1909021209060702060c 85
    0x480c20a26405680b16542d006286e00104d00c1c0c5440b000700103240540720180021720b440c070000740340d600c00c508469803803049101505140d03a4100c1440a0060294012509071103030380c1d00d920104a003031007202a640e46200450313510751606140c0962000c41038000c145c55800c110004000250007101d103d003600d03c2030321032603102d80d80d00300020002d018940c080080700d010002216100e85000c0b820515450003622051901a030820007140c103402080f0680000c1441403c4a191541c0039260f04245086d0030b081e034618060340780c81114203129115501f05c7c1c14010303400f580000c102081c00303000d0b4450800e91344006401d2034010f445641e01d0040c1e176501c0c095540001e02442802003031080503848603010701041c2d52540c0d0707031610310300031301941004104003403500c0c0105210502c2c40089a040b071343c25a000f482d0001c065001c1003005048600070b41d030099400e000018101d40c5c180060400f200e2613200b40e82040c644041d20a05041005003003108541242d02001198135442d4142c0303580d149100541c030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 21560383 1250 21559133 21559141
    0x120406050705090409030201020d1406010c03050d09060608030a020c0102030a0504050415030203070602030706050901060e0a02130f06020102090109050d030504031506030519110102070b04090b0d060603030206011d060303030609 100
    0x60b030903205500c0000d8109080c80c40e04418540c05400074020000b940c4c204120340c1106021924001c401038510f68005007280e100c0d4404240710f1009010703521400003002032844165a50801200d02c03641c0702e4402c0382c101013400c00141e501488014410b41e02030003c0d520f4400e00d00c3c001422841036001e207520a580d03800200004403140f0f00c120001d5a8050120b80130582c41c1c58029649030400381c4119221b909000000c0d070903800c1802614121a60b40c24287d6203070301d803485400060b40258040311016038200900180442c00c0d1200d110080809400042c1d03500c0b106000140200201d0f04100c0c041c1a22040d80000658032204031000c59401158000040b000602c10318098511640090414404e071184900381e18800c110300856207100d54031800d000d070520001a61500c15038401c0404200301400200b00c048810b8015441f0103d00801841c0401d80a40d244421142cac140c2090f00140d014400500c03010101d10500704031840c0c100440b030707064508080001c0c0c0e2840001c0101d03010300c0064000c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 21561633 1250 21560383 21560387
    0x6100212220b03090622030801050d080d090309050103060801110d0e0f070303120c030507120e010b06040e01030b010806090a0f020a0b18090105151801110304150e061204060507 78
    0x118010b400b0100c0055503e0070803681e0140d40d140e081d0f03a0303241220946141c2842408607006003840307856064841e00b001e60310309400c019030810a814191640001004054030500c060f21440c40104c4c07007902c0f0404002c0c00d06c0001000c46407985c00c5158030703a2519806400803030f000d0b0240c030380c044c8079010b02140350001d02c11641c1c101f81c1c4801080c4c2e041d20451001004054108142040c2d4003521b002c1081308036030300c00080341581c00595055022481034480000700e104036400008450f14103100100d0b0394041080462510760103070703015103001000c150043c0304011289250300e00515143d4010440741c2011007541d5140e40580600420f204550b46104d0b045481d80c0d41448000c08403075042d540c442c170801d180c421100000d0900ba84c0300d40d05400003c500c51629008100c1d245100c3c004213400c213401c51098604240460410b030b4103100c5104558482541b08000034000b4002580400c001c03142c0c041d5002d880c030069400002d11407601402080848440941410f502c030703402c000b02190075200d600701 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 21562883 1250 21561633 21561697
    0x305100b030a021311030106052214040b030102090d0506060a09061a03040510060605070b061c0209060a05102a0305190e040e03180901120312111206100212 69
    0x172403268048080000286550840050201401001520003141d007025404e8074541940f40525120303882e019019800c02d04080e4400b901c03186010703000510303101004c0c00240700c1e0381c1060300440740c0d507210700c08004103414521000401899000c2c01800550b007012014010740341300c41401003402c01c0202c0020140b080400c0800c0a0a000100c200440c40d221032005055034001c1070150b40c91a030ae100840d540381080c040c05540070002c0e0783e00c900e101c0b032647e0800486c008007805890b440a40a040411380b55100000840c3e84001034807990801c0e00401a56108404081c44c1d2070340d00381003d03204c040401e03003003000c4428a0b001c2c55600c8850071072a800648a401c000c440c0282c11603d88a000c00c100707100003000b000700401d501060301200220170108a41c480c006d0003480004918241c40200090150410411500c810038011aa020784081c1248044d049040c0e504803458448090120307a0504191210000c56941301414203c1005869110548200070403e01046280c00ba045403a202010b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 21564133 1250 21562883 21562901
    0x803100911090910080615060c0d03021c0513030c0f05071e0e010b0f090a030b0a0207020f030d0804110d0f080406090f08060601050a030603080703020105010305100b030a0213 77
    0x404100d144241548000c1c81e420600440d07025080d0b01010622100d54100408201d640b030340000c015a903a9520034400c0122440603007504003509101e0810090300500080c00300203c1664016120445211101c01c2000b4410300b0b41041407400c5e00f0f010604550000d154812501070425501c1c0101c14504580031441841024040d4060705001146804240100030291200803002e480c0d1207440d5590030028100a224990b41e440c400c100304805400120080c08000400808400c4010381d0303510303406001c0c031080300e0866699900080b00b400b1460041c015556412003900140440700b8000e038041e12103200504040c242510a41d8001c40341c4d914005182d441940c040131648048070107150858150b0094000d920100350717290780c045440c00140030301c0030440e80030900401031034075080010748241d844402c0590030581c95038008000704030904c0041c038100f44684c1c00020150315605041e81000d5070701c100000040c2c1000c10040d0b0a0f5000140482142c3c0c049072440c1c5540100800d10f00240182c80c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 21565383 1250 21564133 21564149
    0x30304020103020f0424090f050102061f0506040810050a0204032a050d0605014403040b07050a03020705040b060f0c1905060403110a080a0503060d0203010609020405150301060507080310 82
    0x10554070380d10812442c400b200b94041d04c44481f42074031f84000440c00365060003000e0059100e03200107440c0701442d040da0700d03a01032840c03405414540c440d004030382580d0164002c1e04440d03000c000e241e80b107000c1602c29107602030045c0c0c6045003400d0465030b942030b01025100345001464000242802e07580d010003d000d004250003003101004000502d4000d0242000b4882c0466030a09840294007080620741d4540f00b5101c030b00c0714035102086104094003000333405010004584030500010034a041032100038050036000340028013204055140003440d0010582010b80943e007800a1a4801d031034160685840c00e0001b10f549849081c3c4056007886c14243c00e20640c1c1511007050054248000803c0c640e0040307000b551003080a2091800c030343d54035030728010002e284903c10040c40c01c25a200714091901308800500400b400307001a00000d0944d80781d42c100004240d4009420495440c000c0131400e100030307485c20070604540c54800003803c9405048405021070f01d00000140702c0c40c402c40c4010003d030040c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 21566633 1250 21565383 21565409
    0x712050316031109131103071115041101050a020a08070303020706050a060303020c040b040b09010905011502010b010806010c020d02090103050d0207050312030c070201050d1104090b040b101110020309030a0e010c05030304020103020f04 103
    0x148c0000f80014a506085511ba02030300c1d030f41545006210741154442c940004054105550403401119a42d114504407021405464882000111058002c00c0054080c1ea00561680f009007803040448102030080300a051a0220400010b078011482400d04403084038001085505900461301404407482480d600c0340080002240b4480c0c103030300c22410f0300c0004003034201c05009000280e00707e03141c8031110b90100ea80030001070610340c80f4100f0110642c0c40a085504441000c0c2e01190030300001307800c12030b2180c111070724220000e0790420070107000385000c400a0140c541d200ca9841c58510000c0d10383c0c24403000003e450002d590040003120000786460804002040d440c0710030881e036800501074101280e0402c201c1d0840c52409019900711217000810180d803411141d4000d0741c0d10302403101c0f80e00c803d00501860b158104214805140301b0442e20010750360703406804400622500c0a440c0309810300c1040850100810000026680e0140c0c1c2800c005a94004000c01103a040c000c641c088104c11070f003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 21567883 1250 21566633 21566641
    0xb0106080a180615050102072102120105090a020114090a090509120c0a05010f0204030b07030902040e030a030b1305090303071b2414090d0806060712050316031109131103 75
    0x41c0740c0c013240c0641c000548071040661680012621130b81c052191020702100d03040c0d4001162076103200988543e200510f20060249030303129190075503030100c402c1446a004103203000c05550b0082002c906010281d80060b2401013808000f40f40355410740204542d099890000807011613040001d1141d840103d0840340c0c69800252010756904034240e805c0710a54240361035102c0090b540c0c000c3e01c0581340c0c85405021542d17180c0324210014100d400e42030b680140c4414684140100c2800240140043c40d82d012480209450510203105010441d5000f01c03441d080c00c0140d84680803040e80e0f00101d0030b14240c0c081c9052421207200581802c030000e80048098192036002c0071a03080d142c0401500c0312000c4c0f101c0c928100204a5440080701d03075866580202540d040309a115017221980248018001d500382541c5444045416000c2e020000c08104004284000c6054001900c1c0c0d00f0031280c501404101d000940100b26401001502c4e8052280380d00b480003119a150005040725220b09503154a0b854 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 21569133 1250 21567883 21567893
    0x150919080a0e04020306100309020a030c09020403020a080303060108160c05010c09080118020303031b0d180506130c05090c0c010c0306090e070e1b07050a0b07090504090b0106080a18 80
    0x31050a10901040c40d0058110080c03c090003034034842c0f8801400c0104103032071058107502811743c1e66412a4051011440031000500011503500501011440181c8890652041c00100c144c01d401064a50780180304004c09603900128280c0d01c0b0f000c58002c0c08094910010607034001c0c603010f00081982d401c240007213107a6603000281c00704640540700284890244880b12070300d0040d03c2400070390542c00c104005072001c1c850360703400c1080160301034107103103031188030040b44084070051946030000140b904509018004104030254104003288107a01c0c1c00c0c45a59243c11003641d0b280300c0c081c007039100c0000050034688000b058622305501800240410184400010300828040c002d403500a0703e04800c400c600d40d400603e45007170320701191010f801502c5400007805182c1c00c200e42c2c052461010040d03280002c0d4140300039107165101d1a07031510103042280000e443c070500c3d904200d000314a42104107004c9a60b03100d84604442141c00d140f150f50710f40800d1200039040300d04840585001e103142030000c000d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 21570383 1250 21569133 21569137
    0xd050a0602030a09021f200307140a02030c0111030304060902040b040e0105041704030c090207140d030b1e06030601080603010617160603020301060c0602130f0b0c0d0f0215091908 79
    0x1a1080b124018030001d601c0244041c0039440c080b000009009900750212500003800304207400c7c04031011241009160342c1c0d10804c00440e92407020040e00f00300d15940c21810304104c0c03401c1e002000d007001c140f40b20001035201c1d40c0e0b01008201500e901c0d01c2c0c480900540d256a40044072100b4094403d02c10b0004414840c0d020385010b0754200c40c039041900f41800b43e001c0240559041d294440480d604503494402514040e4028400a036412103040c0b503008004241080203040c5c640c040d4801007440c44640c02040824a490041d40940313401c0044202100c2d602c3c4421a0741c0007409080c42e0b602d645410700407a004000f6500000100030030300c0d0b40a441c80f00001403540808260380d104080c1c25881d241c0840c00e0340000e11031100030030420000900081d003907401400c05105e86050056a40d03a031172495030000d0205901004440c0c00008010081110911010810281e070f03003002802c10210303036002561030681c0a40140d800d0204004150407103824000314100007045130a100798214103061000c05c039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 21571633 1250 21570383 21570401
    0xb060103180b1602030306012007050306040c090c0f0507020d060b060c0102041e08060118020f031924061b020604060806030d0c030203092704050102041401020604080304020d050a0602030a 83
    0x41c003103041003d21034030000482e0302c5290103a6490034030010040048040300c01c0b00216542a004900300801c0f6910108072480c403403070107440da003907025242880c1601252410a4080d0030000020f010369040d507040402c6070446a03040e00c2c103040800304d0f824184000c01009201990040c400503010007859415006041034404450208504a4294695040500691142c2c42554021800400190641c14541960b2281d91313040549041046003140400313030300885148090070b407010900705e003620881c41640c03040288503000241c0f21046102c21000f040e41845000104400d07908500d590306000243c000320103501404243d1541c4e00c03000041e003020070031907600d03000348191400390003403e100c4c0c4042c1e0402a00758000d1494085031405000060b030007841c020f1759844201e00c804600301e09944031180700714001e400041e02c540c01e203c410f00c080f8801e8804541194031840622021801e00c1c400c40303800c55411140e0740c22021076071070940e0400101c0040a44124170202c02c0102d40709880c3c2001000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 21572883 1250 21571633 21571651
    0x4180b01090c09210f0c0f03110306090606060a020309030102030405010b011e0503070c020a03120906030507020102090f130b150405040513080a030903020f120d050708130b060103180b 81
    0x20030700900c0403c45801c40144100d00400403420b000803906100140315489460043c0d020703821404070b03522680c5884d042580100007040c80c0304001c1041c880c1429440f210b60b23400300e02801c2207090000c41a0b81d1031001070507c03880f80c90001074501c0071a008100322600b0b02000340080d5280e140c00d05145008040381d666490200788106845d0001041c050000300c2d04042a0700c90a05540780c100f0b013101e5811239184c080f0b030407000106020012034074015640c540c2c1c80070b5a403040a01c0c1d003004401010356402a02000c11b5a0040c4401913080d40d030f814180340744090964501602221010021b4090458000714980000c108650310544030310410050040d40d4043d0b4090145031180304007181c4240342c4800c0544a000c09110000d401803107a0001c40c030681c001d02c11a0081d103165100f90303061030300c1044418180c0800040c01540007080c0e0146d15444101d50404007082cbc80e084505500f0300342c49a070300500d0f0842c608002521a8060b9220706021200c094000801e4a01468051188041a070320510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 21574133 1250 21572883 21572891
    0x603061406151e04030209040501200a0c030e0d060203010b0310060806010c0201051b1207020a140a05010c031202071203050901060f12060e10020310080c0901031104180b0109 77
    0x1200c0d0400101d000001e440300c094003407404411000700c2003a143c10740c003d580d42010030400040941c1d241c8413064052802000005100420082005256210480190030095061140d0102e590300a50000c440c82d40509103030a180d62807400144288000c0d0100501940c800710002c681040c4a40107188100a05c41009801036114001680d2091084402500280800c04040015417240010700f04821641401045c6d8800740760981d030800315140d00030400b04101098400a40c9807e01c124802462000c13a498201d9400c100030440403a004d02605043c00504c5003a01e0426126020354103048440c41c10442d29003442c1d160000040c01e49459000009003050f020400c1e401c0184a00800c40741005841c500b0310b1b1070400c400c8140020603c045d1511503444000c56140c92080c0149504031080c18001a501d151541014024031102c3c0c0004105920a04a8851684405468a0540382c10411205c410300c002e81c0040d01510108a2180b0340007008003c07581040f412212440c140c44103024140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 21575383 1250 21574133 21574141
    0xa05060705030903030106260910060b0304020a06110708060c0306010305090303060f040b010203041e030204141b090411070b04030306050d080405060903030906040803070213020313060c02030d06030614 89
    0x3500380c00b003612142519001000100f14090103099080d1015207481d0b6030602c62000c806180c000ca0340204d41300d890f00d4005103041c01080a041c890390f809424a00401c0342141420303000710715891500d02400c0180220032501030695001040000d005141c044100c406030300e480c01000c4d619030415100540464140000300300c071880003000f80c0740300302000307040c05200c02c1c109400c000c068004110b0b02070540c042000007144111003254520901000c10070340d03607612460361050008440350b00b04440d0184136040103110a00d0307c0c3c07083e004503122800e501c441d00e819141c03000030000c218101d82c9079481c00740001e0083c208542070034054400c074001d440030080c1a60b1101404000300040e2001440c041c8100400d000030301d4244060051241d000e012a4200342c0d4882c041016a8002e4011440651020070198114500900360102c64030010006600b0340c2851656401c0100f2001700040031651210070440c0350034400c01c25140e5440606209121041d0f490a00074001d10803c0d418602c010030703410000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 21576633 1250 21575383 21575387
    0x117100203010e0417040801020d02090307060203030601050f130902030403020f011b0509040e10020c07180c0e04021c0f020a09080601060c03230a0e0f04050c040603110f04080a050607 81
    0x502e0403209180210110b0756900d41d1440c500c0490040070b42c40301007082c040803441b12824806440d0701c01e145100140e40d1440c103002c051403e03045034400c1d02154001c100b0020b1a99000702a5103010006c150781d0741c3c0300c4e621350340b245420850a411000d0401e20205c204014198005aa51444130f4000001c001c2d00e130b103007140e10542913242078498022450800c81d0780c205003015402520342076080c405a030381410840c40390005903031041c00744100d141e004220911821000000441c1c0307020070000c00300402d640004005d0480d40c03100900c40c0c442c50340803a201030160002c03088a403060817051004c102c194070310340e1940f009400074496000050312134400454402000144c0318140d80d0b2644a900100609980440380c103040c2e2030780012845e9021f000d8140300c04010000c1d21340c0030160340700c50b241d020031f55061041c84020040000d1041c1e00f001c1c103204c14070808004a03406d45005140204600c40920b643c8000c610844000c03407030345980090300140411010840e044164842c200b560010b440b03520302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 21577883 1250 21576633 21576637
    0xb010608160801150c0210020705030f010204050306010506180907030f060605090d021c0b040c14031902041104030f080c010b06030f06010309020a0305010207060b1201020a050f0304030c020901171002 88
    0x744808605114014400010805034640040070300b450800e201d6400c55010820786150305803144096072062806000d0307442c0500040c22a0f0320240000c5041030314000c00250781d44010310038240651000540d6403001d1001083c0b420710a1400741420b80c190030403120040050400100fa0300340c803481c01002040b00e41c8114226100550001c1c000d0b281024950200100045021481c4481c2128446210001808030030f0342c40c8070340e005002d02e038005442e0506420511180c240d0341446500a550404c4405044070542001c051f0151400140004203d030801014880c80d00040c040003850713001107080040500041042c111901c0c0240461a4040103001701350005841c9100c01d00d50610004001d0751003075012001042c001460046030719500c0d100c25089034801da0003a0381407034580c0464074035418040d00b62420b00200d400210320b00203021800400e80e018490031100340c04000004602414031801e0200304440d0004e00030002541e480344010702100b40780d51146c40ca40580282b0844201d00c1c2e1007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 21579133 1250 21577883 21577921
    0x8030f0105100c080708030c040302030604030c06050f090a1401110c0109050d02010519050403020109080a0e030c0603010b0a0815040e061006090f0302010e041e0603031b1e0f0602070b010608 84
    0x1881e05d007800f916035078052903074100500d6558400018040080582c1d010845540201d000391190b00c0e5207078150500c9002e454008002c00b01d280761002c140610403030000f95040c001900003c940b410750180315011405002402e90058096070f01080d504240d07034066000100c80b5100c1c0d400c482020318855010703400d0742c0e0700f202c090074440282c501e050707103004080d00a0342d0310911a100001d201003159480500d103800061211002607001e0301103120900302001007408098088a00c01c3c2950b14100c040503140c411640ca02c410400308101060580c1d404460090300448000d105119082d0030003e000e9480d401142c440b0303125078980307500150603400b0740000d0050741d0003507001c000300354110307001074658808000210741c00c42d03a948590000090403410350514036000e05000b1400a2860400030001190580e410b84000c114014200002d01c1280c2c1c50315982e801118004501142030415200307112108001421050002500e00100031181003218141d0321580c850400c0c6032901952120400c0c029030f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 21580383 1250 21579133 21579143
    0x10501180801050c0d050a2007060e0105010306020c0d080105090a090201180b0304030906090303090608091e0d03060602011b030b011101050108010501060807030c140d060503010e010f0c020307050606100c08030f0105100c 97
    0x2400240304d0004030005100309e0b80510004644814407203500c5003110f00907402680d10b10380c0070640294403c070901c06c0c001400b5041c6044000b0354107100009000410280100c0049913070b4504203021a40900c000401c0d40e11001140c1080710344e1118403940c40d0380300b20303011070003d98025400308105000300c0002059907010350310302c01c50340d082c5042070369041c80280c01d0f4111403058220102030003019078841ea00c440b081d07074081c000450843c94040d040d203115030050401c0d6410030f0003c1d45d0000e500300340c0c206203840350302d0081a120036a10040c1d070310016141c82c880d2503500301400400c030a14150030441c101c41c840d50f201102c564591408a0071a0100c510100004260300400d15149207031030f000d030a0b401c07001c54000450076540e10001e030848003107007603c6056135101c05940066039640e203e2601c1d404c000780061490b0810f0f0356240c50301c5090090200e4881d844400c0c164503090710400d101412161f001c42031503501d003404100c540001009100c1e16200c1e180b948107640700240704070f41e10410300303a00c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 21581633 1250 21580383 21580421
    0x2030a0e060f0103020d11040903020a02030706050a08150a080607081501050c060a110f0d06080d0c02030a1202030d02030106080907090c020706031e02040605071e020603010501180801050c0d050a 86
    0x41d03081005146c1140307002d49001d0180c854a8000303503503610a26003424441d80040484c914248140740c1041f000341c0c080d0b024481d040c040002a40c1d045201c0c140c0c02103040b00c50890034448180050055840ba8011000a2149500b00000c658001c80d2090003500e92540c2c10405601900045543d44100380c0d40c081031b078000c01c01080d030300c4049130400002446080001e07070a00540c01403428480e0424140c0401ca00d844240410440781c00b484481c00082c4a03150103682c120164000c6541c511003010004c003001100c00301075620601c00e0040e030b2a15100040b0a41d82c95950303a01c0282100010340d004003650248410000320130001d071107000b01c21170468000c1c00025140041c1980104420302480d21508154050100326000ca440100084d0185071180c6844681605100071200800101c403021017600031808009680c1e2003003a2411282d01340f902e00840c510904026520a4499005c04400e41c01e00781403120300c01c5048082c11501c4802c1e1001c12099030f4406400303040c2c603000c60000d100701c2c0e00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 21582740 1107 21581633 21581639
    0x6130e01080705030307020d0c0302090117010b0111061302220509070602030a0c061a0405010603050108010e03180111160603020a1106040c0b0c0a02090a02030a0e060f01 75
    0x90000003809101c3c10400480d070b680c46604400b0340300d1281c2a8400d81084400c10300b45015540c007901c84922545c0d0b4414030b15100c9011880c600c8a5400e2207001d41055104a50201d9503c01580c010803082d100d5003030848a9070000c0c07e00340d07001740a40ca02480ca00101ea403940d603c06e201c10000041600d08228041e0a05c1440d0300154110340042191580c903035440b8402081681d0407e80000b540c0490a5209141c0489041019003190900700001001c60701a400a4100c5007081e0081c00342a4000110684a219600000604c549200c0c002d5543e54441d2030300d000166a03110459078150b10100c5006072110319540f00000094001510b0303008203034084002c4c1c0c2c0304104c00c001014903042c00d6035061212a03d50080100d00700c07002c80c003c44d07040001c00545540700d40291058010381460b001900c0030754411203800c29194148096040807020008290744101c0c84c001501442e41d003 = true := by decide +kernel

theorem cover : BRFrame.Cov 21402883 21582740 := by
  have h0 := BRFrame.cov_init 21402883
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 21402883 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 21402883 ≤ n) (h2 : n < 21582740) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
