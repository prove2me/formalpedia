-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:35:51.656349+00:00
-- url     : https://prove2.me/submissions/2dc443c5-570d-42b2-8e7a-f0eb559d4a88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 9892093 ≤ n < 10071949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 9893343 1250 9892093 9892121
    0x5060109080a0c03141b0f0a031502030a0507020d0f05071703180606030102040b07020f0607080c030702090703050609040b07020f010906061a0c0304030803070c020918010c2c03010f 80
    0x40f005000f04100c0400100c6403080c810024544402040c2c0481008030780b88507224000c9a4080350035801c1e56170011000c00540d0000492644030f28108080c202039030007180c200c88450f00b000081401c1d0f5200145241640344d40380c0e10207140101507075017100c6030b50244009480d110115408804000722200045001e8203440080c2460f44e43c0d0401d249080c65002840d4a01c42c0c0d20500007080084000c0d82101d100320303070444522124030320840009038640200d89000e0306011001c608003005580000c001c0c000346000700c94100003580c0b144011010f8990403030b007494006507502c020070009a00c1041c0c8036040030306401550a61038104001d00e007120071101040d9210760701d448081001415014a0140c80015101c840d490100040d041d00e90b00d208520009008d0313003000001894070b520910ad1491055070007450052107041800c1040024171a4140300c007480d501e44180391414502845940c004130710403040d1590981e042c1c0340422198040190f115800d035480340780071401d01810340700300055040c5035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 9894593 1250 9893343 9893363
    0xc0507030905010809100f02040b04151403060d0b060f03030310030b010b030402010c1e02030307080d1a0f040209040b030706030903110307030e060702041811120102030f070305060109080a 83
    0x1810001e1801d034103640141d0501c900d4109200d420040413509100b01e811035200070543c688900041e2000b841142c1c84010b0b900c0010602080c5078201d6920300040198569841d8018035501000c10a00e101c1540c0c41540051100106d0b070000e5810101c169000400070140d5202e502c4180110381580e00884000240400c60881801000380202142d809040c6c0800320340c0c2140303845d6001802c0d245400c80094912001c0c04035044074850080e910b41c4602e44c4c042d00b504c1c0c03a8107907440e100078a500304491002c016818030503808110303132048401603504030005001800e5480c0c0c001c02e0100951084440c190440e480318000d408607201040704500410313156a00007001031960500030070311402c03e6841e000e0343d0010001000425030110034a569020304550181d61070740a440060001c0c8220304a4036045a00317545c809042c4991a090a002d03600c05540c40310880c00003616080c202e00c402c0741e11244018000300480c4140e07102c3e40c85182d20403010704211228039114a1071500c1d1a4403194115401940 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 9895843 1250 9894593 9894607
    0x9021906090f0609030f020603090f070602060a050a05060307150c0f05060610020303070203090108070e1009080607020c0904060504030306050a0305070501030b01030216020d020310020a09030501140402090a0510090c05 96
    0x46080c100203054a10b4903007401d41c251b0f0303120702c2c42903079190f07001c2e00c187e50101c081782440409101c290b80380006602104c070039642d1740d000603449090413284540c21519000024480c1c450901815218050003409440e8079420010f1189115910444450811142945241c00a8800384403c043e00380554000e02d0030b413800200b00480180a45180c500f10b40060042c000002e40000641d92080d07400d007810a059aa510011141c809440648590002000c01a140c0c0ca94000e60f040050340c40074800e94a00d0f07543c0e80006d0780c1d54072801c803c03c0e0b00031b0303038400c000b40201d506a8842a0854483d10303011038940d40d42c0c400991035240540040d00d1680000b041081030390717014400c0820701602030a003541000c0600001d050490b81c810f4000e03018501c00b80101003155000e01c400c0301602c004140840d00c40071540c40040c00710303886000c1121070390f19000100035501d2141400c24800c5500800d0b0407883c1d640c861605028100c00360035070001707020540c00421b031045035002e0b0703010b403408070303958191503a01d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 9897093 1250 9895843 9895859
    0x415110913060b0706050601030f0c08070206090303090d0809030702040c0207090b0901050904030305090a08030709050a05030106150f0311030403030506010e1909020703020a14030c060117060a0902190609 90
    0x1007402a41e20880e14250040010b1120042a00d2015400503c0051709650300001070f000b429460507030001c075a2070b09024507000707900000004e01810b81c41d801c441e89555400c00303841d960f2000b6114400d160380500154144030f40701e07507641540300c00420103480c1812007035400314040d100120300701d0f80940c021100074810f0f280e0070302c01c20303000721801c4a843d0880d505d0003001c1001c0714806040901015207a0740000c0d4240401c00000b00c10035846006941d503803401860043c500060380c01114818005440009900c4c50140600c505a619074080804990b0022000792006100a4001006c3c540c89214075602d28a4160246220398025100460300e442c000d4001000c1c0700030403100910408101150402c40358101340140d09650b202000180d8030300e0035050907441c1c140c08500003454103034554180c2400d00c5c0b003c80501108404481141d00301c0c0d8a982d95207001e171941442c00d00d15648444005034151b807590b080743e01304038000347c000d00c2c0810030341c3e0702c040801021750000300100320034980801c4005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 9898343 1250 9897093 9897109
    0xc130c0309050d081609060c02040e01020717040501030608030f0327010905010f050105030d0c0305090a081006031415040803070909050f0103021c0201051e0f03090c030d0c03020d030504151109 85
    0x40152401006d9a4106080034200e0030900e4000303070080d41e86500c0e001e100c0a0941c1160202500400107260001c01041d10a6150384180038040c0000e0810200150035280002a2910300f401c41d000241980e40b621100407040d1145a8162944201040b00e5001c003082072003081c0b0b18600600020445141000c0d00c001581c0041e417100340a07a10074031f03116000c0b56000c0c0300c018005130305180040d42c0e60300c0742c800a070741d00d20607801514450082d0104058901902d070f110004807480b45445200c1ca030348820105854141084e000c00340301108100042c0010b50745801036034083d41d61700f0b04a042d07c0c0c584040d48100c0d20225050540b0284200c018029460019020000101004021040b00456500091250084400f032440c0e680d55500b5907860315606805491510030480307100703510381c81c1c510030f603941d28500d008000d8040d0103070060700340c0c042e4483c8142c4e50421fa015002480412084c6200300d0040c04000d106a4210f218180d01420105031400b51041c0b2001e140c03d40e584440c440c02c1082003107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 9899593 1250 9898343 9898381
    0xa050601050307120f020f0c06011a03040803040f030309081218030a020c190e0907030c1d070f090302041104030506011706070c0309080307080d0c020c130c0309050d08 74
    0x20000500811460710751085015990800c0b000010841008401c4c00101078011078800c047c2c041004280c0c00302c00302d000101903040f10000b1020002c0000503060780d60552009550203040b05504100140220311040c84a6445500c1303403030005115455521900c3d01a004540f541008408ad02d0a1150405d40030451021040018018503d090080c0c44065502c0300b410b5501c2d4016800b100c04100c0344024691414018080d12400294600c0c002c03413860b444010900044491020100010521b51040d0f4001c54091682c207810300710b59260310b01d041d80d40c5070b050071010041110288001c40180c8441c001c20b07440a030300b8000c1c02c1c0c41e5811031030411b0078102c05810804d001c1014149000115400107203494101c0118205080c0e41a07172400c04840c003980ca50003000003803000056110800003000001c10324800d410600300888060020304a071595040603580d64030468100443e5161200ba500c040c030203041d5410b00040785c00140d940e00c2c5c1029076542c14800814109410801ca0354020581c82c146 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 9900843 1250 9899593 9899597
    0x904080702030c010f0e0d02060c120406080901090b0103021507020a080102030601030c0503040b06060c1507021018020901090b0a030605161803080706020d0f020c010e0c0a030f0b1302090406050a050601 89
    0x700c544611004004403824030949201f80003071400c100643d220b01d401c03a0001c100c00c400761034014140e0100d000440d0b21900c039010018140c24000359030070034188202550554005006145c503440c1d40c0810440d11009076000f1529002000b244005a64403c00d40700206018000940c5038030300070b40003404840c483d1044c803084c04020010000050291401d4907400b20701110f526449205001d0709034a0f1031041c40d000319018075040d09102055070000752600e030500e82c0840030f01c032250b0300000055601001c0603009401161050041c4035001d90303900700187c43c0001501620b0f00c9543ca803580f505452007034031052886c80107404c1c603d501c3e5600140c25145032012001a0a0103440d50344e840220b4461460007606403980450b000c80710908941140310032400303c00d0159124586811810b0007015090a106030074450714401700c0c540c2c188032042004880d00084c404034030018a84480014100041c5010f072403002c1e4034058030050742c03401c880d50b01850080d90005010300c0c040c0400400c4079000751100781 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 9902093 1250 9900843 9900857
    0x5030a0f1101050405150c0309060328060303050d0905030c030706020d06091506050702040f050403022b0c030309050106120f0506010603090b06040b010e09010b07030e040c09050118050904080702030c01 89
    0x1b61600d1410b80180c00640d4400c50b606d0011050103401c42c000e24024503030004000041c0041c0741d10044640700030b810440050403425030104080003c4900d45e01c40100840d41c2803000c074003c4c00302a030200c80c4550040c07007a2403070414140411820b540c000c1c00112140b03a40410940000d20a61180002a01062600308950001584203400464182c40b5500801000040600440d00e46030800300c2c0002d0782c80740c10700540c200340c58065102d5104041880006580801303489285c00320b90082080c1c0300141d100d64075040c049440031030244c03a2424050358590340b01c00d800180d00210380e4203410f00a0080d05100c00483c2503252060a00340f0680c086800c16041c90020000314115600340341d0442011980025000c50100050314413000c0402840d0740a40ba140c000501c8884030301c0107100e690711a07a41c60204010920400003200c8800c0d4128001440c196420700040d4080d50418005180301c048914000343d98600043c030041d0203d4080b94603203070204e82c060850070f04100b85818881e090230151 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 9903343 1250 9902093 9902099
    0xe0a05090c0d0605040203070809010b0a140d03020102040b030a050603100b01050301060804060b040c05180d0804090915020a02030a090501030b090a0c0509041a030d11060c090a05030a0f11010504 86
    0x645114005449640060070001d20400b8810050340450020302c0d01400654481c54004000342058004503a60300c4a075017800101680f610707194108600355406403230503143c144180003d00906004200086055640c20400451880c0040d0003071807040d14000c0c0c01007210725021050501303103c90a4102000b0a080c190032100503038201c400d0b241507030110300e0f206000d5a101c1c01c4c00300141c03100d0700826400500d451203d803006a0b21200410314007880040301c1c0c50810030b203010701c5610314982c10090402101400140150702e42c40d0030420040740104911a903154076485c1c90800c13607000e1107045001d42d0000414040c482c0c1c02c655039100622003401d041107050b000d20040307400c240005003100b050700c2d510119140264060f4042c2d07584454050020000355407880b480c0742c86c0141070075149110b48030301504400851311502030000c50821a4002e000d2503228503c41c0b410980014005652080e01c3c6c001c04142c548007003200c80c9040f8000c03003480c5030003c45400c0c046004881e54800504000d010070040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 9904593 1250 9903343 9903349
    0xa030c06090806040c05100e100206060913030206040605040501090b0106020303040b0a02030105100c08131e0f060c03050309150702030d051006090e040204090618110f011d030a0b0a0c0e0a05 84
    0x104046481c261540087d110180310202c5a0945440d880c0703a000542c620034505250f40000d2581c464007080c1c8003100c4940381c00d1542e540c0d03140160340c000c0040e8008400030380001c038160003060f00144951300100e14280503036138004101c44241c00c10302c0141e0011003040203008a8003030640c1c0011076800b0862465040c0000305864800c0c020411043c001440c581c00d080010305021541d00400d040705105030182c07280c20030085d01108640d07803005055803020115a148008480300d003100c0c090780f906400b240385680c003595036810090004c1076a000d25901202c0c0664954002846000035030302035684c503201780d07544d0012a2800b8100c5506c609202505000080e08048528181d41c1c1c0c030801680c880d0b4580c8006030280c06a010014501800e01c2100c41e01e41468200700444c03141700c0d00b084d0900c0c0d80140b003032180c183c1003410040e00250b5040c410071040c0d035501c881c0301502e20000d419a4850803054840349955a03098030b05440c0d2030755800d00240401d03403140600140f460101c8100350034510303240c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 9905843 1250 9904593 9904613
    0x30a050a06050f0d1b1401030e06060102070501120e0114040b09070303080601030e032a0d02010b09060603040302030d09050d0e01021207080a090f09050115050702090406020d0b0a030c0609080604 86
    0x3d50262101c440c1d82c50501408540c0b1490f0f0344426044083e03070719101e07001d445001c801c0c11030a03070100b4104507012008080110320385100349810b0b0b00521010b072501004440380d80d04940c46001c0030307540d803a074150021001e0181e1120309205500081a606013231074a2231303602030f00030880080c80e000480e0600019034090110780d04060700740307004541080051082803c42c4140c0c8503208072011601c0b1846900301c00c0c9502c00c6540e0000d82e0030340c0c4100108800982c240d504150000341d0009941c0c00103000c2c0e1820704040c54100e4001c0c811a0b04003501c000d1808103c800e01c07603040d00c40d9800b807880101025405141100100380a202038030198500750314100c51405984001407051001041000c4110310504c51302d80181116141010f6482d0742c0d2117040001e020a01a1a001d8010219081c821038058011a4403055015202d10220703507883e00e803a0001d402ca03c50b03c040c00d03602c8402c600d12595030900303158050740c010302c1041c1c5a0362401c10090100c0303180f41d01104658115904000c04607803c100f0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 9907093 1250 9905843 9905869
    0x7050103020306060c010504050604050f060106140706060315050103060507030e060a091b030c15050301080a0f02131103061c0209040b0403090b0d02130501030b24070204050408030a050a0605 84
    0x80c0580c494440304001600e5005580400b0303029840d01c400c00003800800250180118002c0060f90f840c6220700550907260750003400760030081900c120032a01207194907401416524095080050241d44907501c900310003154464400700141ca4000500900086200c1e140d08007040f03060422800304900c2c1a00e882c1c40c001001c240f000c0d542c0b11500d4062140010300b003c00000000002d0040d0303074491030520380141c1140130784054203501c40a415200d034003403400c484c1a200050010104e80d8126a203411a44510100880e048940070310f042034100028000d50200c0e06400e01c01540b2850484140300301d801244582e01c09504c840440c01c0056114555866003090708042c070076a20366694141924424095448503086180009600c40701005a50142c4450703403601d00745d004000e40e42c07801181501c0038500d00b43d900400915658007034850054a8130080880b58440f28200074003600081c0441704219416038018000004002a071a6288200da50110420004106803420940841c1b05408030382 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 9908343 1250 9907093 9907097
    0x20901090513090203070b0d050702280c05040c030603060e150f0703110307030b03060f011a09010905030706080118021305011416051c09140105030619090c140c070501 74
    0xc2d030490b400002508420320f1036801904451314560f580d505541c880e4011240070030811718080202c8c281c0d520105524440301da80071400503180801241c01140343e00704050845008840b000b00042c2d0f80c4680c091004403003081d4600160b51032a5061501c261098000108030541003620290b80b100c400c00c09040e00f14280701030405207680c61405c03d90080c603001c50010b001c030402004008810340d2542081442c0f04003541681c0352510740b01c4c402d154003003007030196800c1c0b4801c0f0081c48544601440c0036015407101490865501a92400401d0525a142d0880c40001d0320610041c060360103140d2000d0165031241404628000320f0b00c40c0140f0a43d15070203164100114030035603030034020840095030040c0215038180c0b503503110540f4000d40e851501e032106c0d45035000f48040380349001c0d00648030b40c0c08603a1002000002c0b000d10038011035150340001d000b942d206051640c1da440030b5208400751009407900c0b4030b0004e5200c03480030000d00803440700e0020321019041006840d0512001007200c1040381c8080c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 9909593 1250 9908343 9908359
    0x1060b090a09090f0606030c05130207020108060103020c0a0807050a14030f0409020d0902180a05070e010816090b03070503070810080316080405030307150b04020918070302070b07030b0f040209010905 88
    0x340c0381c940c00c2c2c02d9072104017a00241c201a80401445260801182200e1003120342074210183d5503405001ea0207420301c0603011444040001d10b440d40aa0000d0220011100c190384003003041e9a60b140842e007041c0c1c41560f0715407044030a04100a1071031403004041e1b04000c01036040c410b000c0d904480600c00c1c2e000f080180d68011446814912240d0030482c40f9540c01017001c0e2441030302410030f814409040368021459030074903011901d00c2e4020303030180b01c4800040e5070300100760351007280140400d0060700c02801000a1041c1c002190101034020714001c42e1103955150766420102c0004010740300107000ba410382c0c0703e41b04040194040000881d10241d400254003400491203040009080c0510fa00540d01070000140020070031040560318428442a607004000d0014001e0900c8101d004000301650005e030000542240408406030095024404d45030140c5015295942c4003c5200d040d40d02202103071722440a540c5901c0c08a110421074072099408600b030400c4140004c0c861515032149174003641032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 9910843 1250 9909593 9909611
    0x80a1a01050d0813091a0102010c0f0c080f0d050705120108070f030b0601090306020a02010e0106091a0d060905010c0e030d0c0302190201090e090d080a050105010507110103020c06010f060201060b090a09 89
    0x1314032010004081e215420407031120802250b4030354448043c0c41900552034400a00b40309405402100701c4000642c2c1c60807420384150340c47e031405038031495046200d000140710050420341d007805090300c40c000d50358800740c40c2ca84541c88021000010307005070001d80c10250f414002045146c203d4821250400840101c0d40c03900300041c0d60350703002c0f50806040c1d0307400001c2042c82d543d01508968007945c070b007100030000180e5030a443d00858003000c5690055104050300d03491140703041c88c04000c5044c02004002840e011030b40c2c8460031210482c08003000b0540c000c0c0100154074081c00508040556800c11500c1842c0a540007074403247c2c82e914400075850000448001c1d64860f4040070080d00c0c004004002e941010603600340e42d8070071341c041e40001840840000e007000311a4011103040300c006840d0a420441c03d43d661284041c241c000f03440c1095800c0c0b086020382e05c8200002402440d03d802e55245542c10040000d0950f10543c0160f2007103a000c0149141c65281d04804208031000f40e0400a00d12070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 9912093 1250 9910843 9910867
    0x403080a0b12060106110a02030c061c0203010905060a08060403020d0809030405060705070e100f0b0d02070506101703040303090b070203030418020c010b0108040b0703091407080a1a01050d08 84
    0x98801d1081d0004050803504540c064001080c0741030302d145440e808815018012190782e1034403500d0340203401da0484c58240781175040c034101a18110005510540c007400038031081300101d0b08242e10001c11291204284203d50800140b200d010786840c4019203c0351405031000fa43e2800314510030010081a180001c000010134001d9501401008241790303a5283d10781401a60b070410750041d0226440a90302103101b100401b50500f04440c064120142000e1408809160a4202d020343c14032a035003c00c908400580203120051050207095112202071b0300b411000100080c0040740450f141e40b04100a002003030b0820314001c03c0fa4241c1c940655185850b20120381940203035805103c1101c24084450084003013a00500310401142008104404c00c85004540140060714081d142440b0040895190b40c480d801207a40c0754066000c12208403505c11285103007101c2c90f801003006401c4120141b0030040d160f804407002d803075400c11250165060200084410b803040c90020302e14400020b11020140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 9913343 1250 9912093 9912101
    0x90412030e12030103200102060711030403021002060f0c18060c01020c07030b01140d0c0504021308060109060e090705100804060b04051e0703052701020f0406031415090403080a 78
    0xc80400c00342c89a14042c80884256034000b030000701c8007030f05100b4907402d000070814070340c0b01e030501c0c1640208010389a0350f406584400d038000c196000c42c002080040301588a51104c00c0c011a010340c02060b07146083c0c0058125404003910000c04c40c0000c00c103074030f440402c590000150090848003c1c7d42c9903a103400242c0244106010307400c0a0043c5500081800300021a143c100e5815048a4484246203010080c01e940307840380c001c181a400c00420320140c20142d01900c0d66580c9c01c00005c4c0c5140d22807240d140f13040000d83c4199010b980750502404800c066400040e0070080b0343c00285021810100040d45409541981008103e072100005051040300c1e0080c20715440044e20030822070400340131914407850004400050004003a02085016100c1e1090343d104034a1949501001c0440c444400908a040304d6280c03010342d000e0003900503091105009200605c0745443c0010718a10101e170300c001c8100e00034500492411f40040001d0345883d0700100c80d41c815813601d040d020613034807401034400034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 9914593 1250 9913343 9913361
    0x50f01052502090a0b01080a050c160501050907060518091009060311010e0904050a12050403080c0105010906050907050d021b0a0302010c1209030c0213060509040602130f030209041203 81
    0x698481c00e41800354041c41c5141d80601d4001d482c0c0115903601e0000450a9800155840d0b00040c0000c0004603652440e0384101e030010406000306c1d140c0b094944181007558000c590582d220b075500e400303200302c0308810030116006107024101075081041c29000c0c119001c030f0304000d40703000da455080020465121680b469029100f45001049050b4881c20101016038142c01d11f41e0114080300c11580043c5440003403144116440002000f50081564684109541500200092000911000c1f0004520a010303200c2901d81c03074000a100c1d03140c00501015162503500c114042d00c00c603c01d208040b94048110380d200c0c1c3c070303d01d00580c2d140d0b0001c20075030719240d12695a00042c010703041c2c4201007580c1900310907002c1e0b01341c2e926030081700c082c0e48003401202c45903800100810070100d06c3c0d0006040c100307401340700248200300c000b985666440100d10b01c003204480846041c0e500041d0b1030700744010380d180980900020024100c9603030456012508914010f0800307000590740000a480355886034002460b2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 9915843 1250 9914593 9914617
    0x30b0607030302070614010e040f02010219030e0f0603040c06030c050f03070806010e0301050108030405041a0a0303020604060c080105010c14011b0504030501060506030c160c1a04060e09040309050f0105 89
    0x140d940c66080080c02508011000c50b00305042580c075880c0210140105810303a02c3e103c0c02d00103103031155541e050040d10768510803030641c007075075807900080c442d0344421000090203500c3d14104000b018003002050304401c5196441918203005100124400c03008a00680c0c01c0e60500041c0d0108006080d60315006440c510703005400700004100740340d5440008240039030400e0700c072950002203210425003a50000d0050000951040c00200005d07e400d4001d400c0030080003c0540350351200703402007409203283c0d03001900946e0054041c001006018482c0f07060401c030b2454440d560754107040000b000c030800041c0140003103043c488403441000e02035220704a000500200031884407030815000e80190046d00c81036407070b035103170000c001114102842103074421801c00310b2040c5441c0b550800e40b4602521048181c400841001011a5822882510741800b010001c0e100303848518000c1c000b0100e101421000f4029441401801700103034000070014142c0d1011070340d02071017482800049a8600983c080940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 9917093 1250 9915843 9915847
    0x130c051005090102010c090e060f120601080c030f0d17091005010f050406050105040305030304020d05031c05040b01090e0606010311091504060306080304030c050d060b040f05060306060f060d020a030b06 89
    0x38045030094020704501d0004e07002488400c80070b203410349142d40b9a01c904001d050078100010103034039207201c4144550380e004000c0000c0200c2a00c5180c0380c81401d812240c0560305c141100b065601d410016406032a40d60001401c0300400040c0c028070f40d610081d069401c0000d100046180301f142805088500714003400b0070001580d40d1414040c01e03030000d200b00d9001b41c2c6040390200d4254402d008450607241c100b40114a16180d0303038280480070308080410f9507240000c0c803841c1c1040340c10a62a0100c1c01e6001c80100b010308260a0004030608103030b001590651814000d0700c0c0542001c13030481da0140003400e002401c03d1508941500d03900c07a19144947c0f0049502441010b40c207500007a00564a00f550100060703070f1030b001566980c0c03040d800007900d45040c1800c1041589031441e045510b04c3d11900001c152000381c40082000c4d555811104030303107103884004004150034200308480d84102d00b210080b0042882074041900d42c0b003a441603903805d60300000c0400c1024000e400004460001401e00c039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 9918343 1250 9917093 9917119
    0x2010c02030a120e121209010e030a030302030f10150e03070f0e010306051005061804060f090506030c0306070c02010e0a05090405060405010c09050a0501030504051002040b04060207090c08130c05 86
    0x103d04188511204001c9401e600711240b03182840d82c1307043c94901496008001e21459070400f610290042c4800d6170400401401702c008585041c0f0208912500c40d46001d616410124240302c3c071608000d200441c40d08000c1c0701040007000c1c051314841900024280804443c0d0f152000c681010295040300754059054080068400c00c584001c134122070092400f0003040c1c894007860076840c8060b1040a1303010605000e08001003650345602c5d040103c1c01400000c0d001d0f601e841c00c184446940d1710a8448960741c504000301c5082c1406a40d41c282821400b0305483e02c1c06082c0500342c500c4030a00641081007450b9402003075200c103031001d0003070302000705040c81c10701e42441d110b96a6101110708450035403d08543c074000e24091030001080d00e0f0010520916281000011001483e00070f2040d941c034404c55000c1410030a492008101404d03414500641d55400c080005e8542015940a400040d00d0a644100510340c0300310003a070050f00f1440d090b42010818141680795030015041140d21900c400807079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 9919593 1250 9918343 9918353
    0x806011e0c050f0604020f01080c040807090603061a010503070509030304030b0103052b0e0103020a02010b09040c05040c0e060d200c0a0b060105071203020a0302070f08070501320402010c02030a 85
    0x803030709580701d4000c44600c024880d0510392107070825900250042d005818031b0b1540c1d806002555030003c80028201e040503643c1010340d00d00030b0f0540c0012021341d5940420702c2401401d02486000b03000050000c000324159000082c85888020070795400c0010102d034000752550240125070003541c03c01d45045143d6183d040050303d500d41e128115205009951003602c041c0718070100712030b003825262035842a507600e200040d00658000c2604404555981e64222007035500c0120f0a07001d03038054961040c0080c2080240000c41d94585110801c1c00b07200240307054079035100e00c129240b0807028840840c592a4107000582d0411591b030b0301204070040890f003e15100c0c00015400030042c015002c1d40c0703c94951500644252282240290040e03240b58240450305000c0d80080406100c00d14005160000b192074042240000050407143c0c40307000151042841001d005030011801d0145403001403a0800680c0b06090100220821100351101c0002e0150789c0030348048400caa802a0a40c0e8030703040350703140c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 9920843 1250 9919593 9919607
    0xb04050114090a030e060d0b03060702100507090b0702040903030b060a0c02040606080403020312040512040f03050d0503010b07060b15030a0c09080c0102190f02040204082b050a0806011e 82
    0x1545200000007030010b058a0b0000507003d00d101d401d602c40c010036030760142c1400601c5d4840e14103040040d84880e004460741e00e0030401144540d6007680500000d200b13040d071070401e598004d4404010000402000d102800080040300c0c112a8101c800088910251a06902170441d194003294403ca0100f500284030340c00406e1703507032103d10032a410812192540f40c142c403052401c2e50058010b82c0240060444101124481d641140c0500111215010001011141980650404041d034bd558040410070454204056043e100007420701509640c1040161071103400b92482c06071405464155520340c0e9200e00c01a450055503140010355686054214600a44042e50450000036066940060f503074602003001030200f841680901001c2500803151402003031504030030b4800f6442d000c183d800582c2c0c1c520040c4010150138014100403000d000c681c221031414035000d51424829294220308036035201c0100d940c0030640e030401c82025101c500040360005420070f4401940c2030b45200d50104203401c641 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 9922093 1250 9920843 9920861
    0x10c0801170304030b010303030203042105090a090c0203070320011a130b09010b18040f06030c14010804140102070606080c100e03030405010f022811040203041203020c0a0b040501 79
    0x154031040d6a000036594034422840040e05d080149001880082e100e90002c1da0824002c121800501c080c5009508288808103003d401161000511001c203042188144004109002d010008001400f17006501c0f481200e4004003080005d82400120240d8980b22005041c4000020060b428081800c0100e81080b80350680c403440303804c201d202c1d8440a50140729940380d000780c0f5010b9142d01e095140c40041e0064641d42c813502d40e81655040e03550302d80f4850810454a03605010800c40c0c0f81d0306080703840003080d0300803415801e40780480c000300d130340c001c0103140c1c1140e0300428804811070406c2c803032802400340040051142c3c0c2000e0001a0710100080d511504400454800f4240b4001080c10780c3c0400c4885000f0740c054106000810056003d88845800e0780850300640d01000e102125904600c0701024040c2800701640071804144032405680c0a10725000380c800f14a0360030140c94981d54a2100301d80c200406400144020700000c080c040861956400800c09509042a107040d40c060078603c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 9923343 1250 9922093 9922109
    0x2090a080f06010e0906060a030611040302040f02130806090c010e04060b0a030c020c0102030c1e0111070b01090f0c0503130213060e011401020c010504030f022e020c0102060709050d14010c0801 85
    0xf0b40403035417451001c11307a54029400141203100c82d61442c1e84603000380180343c0500c0150320b0f0500000015880d40c0c01041410303111007600582d40d10b502c65140110030341c140c1101c0ca00341c1c410010030800070400100708022090909001036588000e20008028000c5178220141c100c4010409190461b007507041900341071007a40a0301e112a012000490340ca00400410814583c01180c0346546071509841703081900c4555400498500000c084603540c50f0b0009508481500602004109002d100c1c0f10340c0b0401d101500050101c80a41c0000400b540005007046606483c01e2140c4011540c448860050080782d0358403d11000b07030342e4900c003040d6007400d10442c0c01c0e050176907660300342e298800b00d260749402030140c4035a4201400e6483c0c14072031040b90402282c00c80340b1900c054480010402406070746998214100c43d141c07440701802820701003009903070350640d0300c50010700c0b08468001081d54255001a84c00142142d25420300b0307188076141c0d82c3d1903155035190481a580a07a40300140c04d050b18014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 9924593 1250 9923343 9923369
    0x9030c050607110709050405030903030a0f080c07030c12020a021e03070b0c06041509051902010201140405060601030f0f05010806010312080c030c030c0904050109061805060d030302090a080f0601 86
    0x11610a0302c0315400341c0c3c0ca94455800506080c0245c4890350b0005411a004608603800d00d00746802292459001c3c100308008114044190320650b4bc0c40b2100e143d2004104102a0a0401995000d0408020240000c0c4150003000d8011603061003000501c5540350010320140000c5421040c10000ba5070a409442c0240115000403c00f01c244800329094140c00000903c455031321a1030300300050300a0346404040544070450603003c00e4041020f902d0f002c01200300032002402501c000b908507051a10030760503030000b00c010000821000b0a17480d0740008203080200f0044103100c05040102840894040c16030301d404000b0030000340c00190075041c2d0f0700c81e03801212504c000403c141c803a040c4c00c803480f4005020800024103401da01e04043c64110f85207011050519055a0005040c4d079801d80120034899904d903820425400c0030100325000c0c0c0c3c12487c0411050820381c0100c1c000f40e4101801405040e000601c1c41c0f607a480300140d40c03008040c05000c2c2d81380c15080303601c4140c13915070a12898010480b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 9925843 1250 9924593 9924601
    0x60801080f03070f06020a14030103080a110a03090513020918101a04230d0605090c0607020906060708040e09060406050c0909060f0a090f0203090d090602060f060307030609030c0506 80
    0x304452081d900300b0003100c07210b68540ea40c40003961100c0d140703802300507a4a000f44091f40c010800340d070280d40300d6040b003074488603021001000b0a0071a00c003140542d04c15501000480c0d0071203842010b40b00207036440003071206000803c1d030281c420f0707100b050380044c0c224005103c14044070201038007865025201d4200c5070350310b102d021410300d2204c01a04030001c042000304403801d0088408a144070500c02100c0322011400001036284520800c186c412507210400c21410a04c18403810400040450301582041815004540141802811280141030008144042c41030752030550b0300401c1d244050b201d280c0761040030151140390a80e41150018203040c0442e0180090405480300081c02420800c00e903a5140c00f0890758800e421401c5801100d210030210340745507540100000d14400110140e0369040c44241c0728901801c19100d1400c210081c02d041c06242d50110341d281d0031049400c410001502c0d4130000034200500b69100525851501180d1020160031485216000e0300030002e440241da030f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 9927093 1250 9925843 9925873
    0x1080307080d0c02071802070507050102120a080a0905010c0203130902040e07030203060111011802030601080f1504050313030b060f0d05100e0304080a0c080d110a0305070203030d0606080108 84
    0x3010401000c4034010700010350721a8a640c041000e180461040310703503440d60b071012244864901c2c900c0d64001600054048244402008040c0c0105000e20007080807605a1030009018000c00701c0310420040171102080d046105600094040f5801070020000b5003140d25010b5500e6200c0c2c0d13444405647c4c1d4060000355240107100f80c030201c1c0c003103481101556840c1d6604074000c3d4001031109040c040c8100780301c034111000340706031000c4030328128101450b08180d0040502d4084140d00070000c903800341032080e050000110320f8508846280c1c66401d01500c640c070746103065010700304811018407043c0300f0020070701c01c071074000c18042d50054944011000d4418140224203400480260040d44108104120480c00d5445003a81074084c030b05403418581c450381d00300c3c01d0408408060701c0030009484144940642803100585c2d03043d00342841d80300b050106020903210706136410042d041c03000101d505400c0d0340b810f1044940712030b0400410403103292251405451a0700a00980c04148100b00c61000410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 9928343 1250 9927093 9927097
    0x8010603050702070e0408120903130504090218060604030b07080f0108010c020a1e0c08010209010806030d020606060a03020403050f0a0510060602032d0705060609060a2702131805010803 82
    0xc560f80c2c040c0c82e42d2810015400c1ca03120f0702070022a00341d0820415003924031f610005a60080140c9006156201c1e009a50042500030581001c0d124500d4200301c2c0f00140e84d0b508040c1680150720628032102e580300400980c850050383c3c00a07189805860800009981c0103100b2882101f000a0b50740ca1030340c0302d105860072601250115400340e0b02c990a0080032481c1e08805100b040c40d00e003003211011201c3e81c2c0f0102c0307185655200508503074001c0780213041580c0101e04541d0140303083d002004030f40002e40e002561010041c0c18a80904000541440c0e06442901150007460300700d030032605050030303a4120595a49010205403598006d92800d4440583c441c098407088400c5e0f64000c50030030f241c84005d400341c070782e54042c0c0754901400024580d5544001c0000791502c640030708090900340c5400f17020b118003180001c1800e07103c2d04c1410001e220300500c20801c0c09615074006402d507040b510140300d00009100d900b01d003484040ca118000507052050340c210400070070100d4014005643d0300c500b07860f40c034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 9929593 1250 9928343 9928351
    0x5030c0a080a0f060807030c0611060103060203060301020d0e0a030206090106060905040f06050a0602031305091303050a0207050307080f0f120301061107050415030b070c03051911061003030801060305 88
    0x420010004103803014450410540c02c00d1001800244914402c0e04141c101d0300203a0041c0084e80201c003042040c0032919210380003d24860404108482045201584842050000400f52580071010840c503031000d42c15201e480c220b0000c100600701a000c8803540c1c0d9003a0110440051080a0005080d40011300611003250820703200d036001c4a040500b0000a0880010307000002640d80030001201c2d584c03513003c1d00c01040302e034024545d1808501d81c0d000c820040e50704104e001d02921030500c04a825800211411540c041c41c0c155150350013100100e0501e40c641d40074960501ca05a00860003090108005107401890f0301190940c403540700e0102c1d2035802d4041c0003003990130140010030000d80071b84070040b2160b4201041e54140c6031183d0008088403641c0020b4003400c07100a005104122164407140c1e0401070f2410900444241594010540d1041184003c41c410001c02d444000c140903100d401e051325004800c0c0c03078645c40d0103020040003160900c4282d0020b4600400029498082d10405000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 9930843 1250 9929593 9929611
    0x4020f1e010f0c21080c0a05030109020901031b02030a030b040905070e19020a03020a090b0712030b0d021c050606090f010306150506070501060303020606031f090c0509040f02040c0503 81
    0x180c0c0250010740352031411440900c02d10a0950680e000102058074020000d1094008609461a2480010491100203020604107001045494481c0b078011003681c0c110341d0701c10009a40d92120b000101c0180c46040c0c07648480c0740107658a100d8540d008000341c0800e002c96070703003000200c2140082006071100601c01500e56001043c06000d08000380f5070307566201803c00c039012421981d408909081307a10282d80080000c2e400304080140c81c0c0d0100c0060f0052010303900c00c0d810280f403600c07904107480b900c2104205169641c40648003540f600d021400319540c00405114411004003507420340302c2404081201d00303002c1d800008080d49000403a05000c1c54a00c901c500840c0e007181d603254000c000303280d04c200301880080c00c00112a51a54001d0104074400c1002040781440c40c94007910340f540c060540d6100c0c0d00420580e1011206140100d2603517084034001240c1c85000c2c9c200380400420070342250b40c20810b01003c00c42882034001b42c8408940c03003a91b0030004040e20701421101da000659401034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 9932093 1250 9930843 9930889
    0x30b01030f060b030c030a020c03041d0f04030203120405011107030206010302091023040204030b0103210504050d020618030601060809060a050402010813021206180106080f0705010f030212040b04020f 88
    0xb0034005c00c90103994030406012005151021200406c0e10310b801caa40080450000b07400242202e00380c0c5201144c102c0850050100342c2d051a5030080e480f0300440c008920442140340000382480303000d41002045480d540110b030341e641190700b8000e40b03a00c400d000c1a80a80181d001040c3c09240e4041c0000c00c907000d8680c8801c811020050f03040100092500c16640715409110100124415a030700500030f511441d090030104046c1803c4281c540f44104000051110a000810140d00c50107540c00200740c0c1201c0a55869415803400c0340304404511b1501e4251051034004079420b6000a5080d000d404010211b07103151341c44d01d0440b403d43c1d01c11a0300a0001e1140b00c00706d00c01801040020489902c02003040b60207403030584189141440c1210700380e45d007185902c1a615410700a2140340080e119030000b5041d180b0b20100c505544180c07910401c0d040043d03488051500030b209a041e11a141e000e54588441d6003058100b101c00e5280075141030744116802500c4003624a800403210400040c4485c4100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 9933343 1250 9932093 9932101
    0x304050d03030f02030a050105040b0111070b0c1006090b0a0b04051c0503070605070206060a05030106030c03020105130f0906030b0106170406050601050c0a06060611030c0703170f0703030b01030f060b03 89
    0x4082200c05140403410b064403495803080311561400a940300c0d02c181200041d41350726200400c000c0c0e94030010014144088507980b41104d800101314802920084851203507140043d2103120f2908601c10008052140b500401040c584810341100f0307002c0710304903282544c3c5521880100441e114178401c3c00c1e403101565010b0200000d160f0413000604d400303030b070130b41707041401a40f038090030b484084440d040103802100400c44645448901c1d403000e0001607008200d51415030390f560011413803d00011381404000318107101c0140100d04001c0103032507030f242c201100d81d54594400d0089c2113680401c0300c14002074000071035503e1003184001c6201c0034129030480d090701c69440c4c01c001010080c040c0c5040110030040b02c2040b0900b045141017030303481032000007191440c0c00f600034040e0310009103400e50758004110340e00518200040b40c800342c82d0071000100740c0008000d40c040bc0e0344509000c1040c0d003000400c1c01028140c0543c003034031074540b00b078800340100d084000113030f41110400d000790480b0a200388080303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 9934593 1250 9933343 9933349
    0x3010b041203030905160306050a140c03090309150d11090f0409020609040c05030103050705040b0607030305070c1202030c01050f09030d020702060d05040c06020c01020102030f0a05060a030210020d031b02030405 93
    0x907801603001e41400207000e161521024240440c448565040400c0c0260401c100042072144a034000c080c218100800900d1300c028203800c03d4041e044414504000c00401e210300403d00484a00007001806a8200b40a202954589403c280b0514428907c0c1081082e0b0390709503031007207644196004041501c805400c104000007000900c00c2039030068811310402e41c4030b4845104118004044e0b0310f8094481d80b46160a40c07411225400050140d0f041c1105d54156403614000e480b8401d5143c2000f240c0707560b4170001150688440383c3c01030001c2529210781d466640c5c0200051060700c1c8840d00034019955100700590341c2034001d031030b0602a54030401c244070f08080283d016203200c501c020040b910702124240d000c015102c003507406803a451706804041082c543c0400080041507c02c1c0001e6042d480c14090800e031095004104420194407500011300c2940ca2100c0d14000e164000c050203695242494020f41e20316149181001084c6454581350790715007130541c850b0a011895005600d81070404083c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 9935843 1250 9934593 9934619
    0x9140108161209060204080c0a09140403080a020f04060c0b090c01050f0a0201060503011d0607030c0503060409140a0501020d06060507020303030103030e120a06020d0606050313020402031e100302010f0503010b04 93
    0x4648101d03550f5030480c0010b03010b03000078001010f40500408140c01e894003002404000796129020705407521504844252001c1c542c154001d4150170a07400c80d0f81d80c2c241010107446021081c3c0410a000100070586039000005c03400c0749806009950901d5550b408500d95039180d007000302c1e0215030700340b103130748601d00d034520040400110b5840003140140e501c00109082d101c0400c16906c0900040c60455848242080b034150300011a00e010f0003100040c40d400782c070622026002e04c0c080c80e150364800082c4031020448031540c140c200d044421a260b07a05000d07000f504403c0080030503a05154000031100d100d48140da1100707800602451540c0d01e5a5003e537142002305417503980010001084101a00d42440000d0419028072000f60356210781d00c00003400c48400340c0042040c000c0c1442030200c0b00040d41c502e44180c0d907040e5001079580d15041d001800700001e140c40038041d802020100040807a61103a22000c4901c01e0b21124000b101003542980c40780000d0291500f0020140810008003a403094 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 9937093 1250 9935843 9935867
    0x602040f05181f03050601030f030f021902040207020a05060313050601140102030f09030c0901060201090605070c0f021005090406180506030c0d0b04030c0c0602010203090f071206050c190914010816 87
    0x44504074484c0e803541d8081c10850260b000380c07114900d550441043c1500300314007030942403041c0302908103240843d080c044021456032000c0e0049502007009011900c1d00410751001d404000c180c2501c91602c0070802e005100e920000302c070240a034500002e17081c02040110208007105030060750034078000002c612040d0f0004912198907200320514610a5110000c100340a89002e0f40003058034481420500c05942016020908002240440802089a544458090030350460b1480807001c0400070031102d60050568603176005141c03000000b5804140025200685041041407100b6070ba01c10402d9241ca21280e480c603041400034070701100068108030841c1d4410b00c28144540c44000e191216001a65650072400250394000706111162504100045c0c0c00011200181000d50910342c082c00c1100080c140141040d48a10101d40d4005000066a83c0c405409100030101661104028039441c0c5901c500b42e80c6016030294011303554400c1100074424280284050f580c01150b100131a001d0354095 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 9938343 1250 9937093 9937141
    0x3040302060f1306080907050306070e0d05010b061306030e01020a0c080f1215090f060a090b0f120106060f05030603060f060409050114100b1809060612040602040f0518 74
    0x10f0701490752100303041e8024042c0342e900c0d480b242c940340c58201d10b40803050700124071039445a0108030210f03500c1204805610700560322000002110b2410034090a1010322950b48208082a43c0f008a007103c1c1c0100e0440f081035030184001e20010400500f01e207d0b110080002440c21011000441c0401000749480010f03100054a0120611030302450b9481c20703203890141c599005012140c910306a1665034204d100c43c1444044ea00308500007880c644c640b88120303950207031118155140b81e900c48403110307580032018202c2e129001900510500a0249026000c00305000c4c4048000d000c0c400e10030303240724540240040426803100914820030f0000204401d510640ba141d01c1c80000d4401c1c0900101c85103403514800301801c08100003d40c541580e0001c0607203074001d011030320100d01603014078940e5820503100d184042e00c400c408030f02e90b4031622885482003540d20044c8400c0107030b6a80140f048a4850300310080d2691503004110b40c001071401040c0741010b110021452000c000440c1c604694081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 9939593 1250 9938343 9938347
    0x50901020f060708010302040c030e1e0c0a0306090b0c040308090603280e0705030a0201080105040902030c030d0e0f010306080303040201031a181b03090604030809070902041814070203040302060f 86
    0x600012803811400300d0f91040041d43ca5001001181054099240d2110b0366060600003440704da02c0003583c0e2428080200941c1842c0240400720036010f2143c203010f40c0000d0000c2551640301e0a00c10081e1a43e020b04a070100c003043e000030441c00110b000d84060300c2d80700e40741500c4c04203d18100205500094808094980c041c24542208464451003001451444a011445181041540303040c52856400a8081c0d00060382160041c3c0c1c0c803d1001c0d0540b00c0c00c990004001800e03001191070120b0b00d42c52681c051060b40d03159035001c0d4014283c40b002441c2111808000b9400030011800d0b82c1c4588a26507869000f44080380040d030280e041032518010050100028155a00c005840a0862910800d800034460b06000e000a014091388000c4808015a20328600b00504043e5603030a00520207400c02c121500816400f200070302a140080c1003110007903440741d440340071010f0108010f140c4a60054906182d8185c286000c400f80d03807064080f50065420726165400303010a940c400114141c10081c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 9940843 1250 9939593 9939613
    0x20409020309010903080601030203060604030b130f030210050c0906030f0a091205090406090908070210030b0a230306090d0c0204020c010f0501050111010504120c05010207020d05030a02010c1403040305090102 92
    0x100e00c051489080700100200e0070302664100600700c0315000e0035481c1058010000c00c449600d6401c104e03003c880d40203481c1d01443e80c0c0c81c14280e242003e034050051031100d806a9038000c0c55070018002d00c1c04034103040c0811050700ca001c0e80e0b40395441403882d0700344c00c030405200150658181e200c040d030780440641c0c408500303e45103680d400d485110303a042603004190081056111760815101e02c1d005807408840c00c0048204540b82c5e9091802054002071081100070980403d440c407980110705070004c00b510481c440c2d91107010700808a450ba41c2d80304880c400d0740e0315801040c580000c110380030303010407005000d0b6200881d0088130610203122090f03800540030000c00062000900c100942c00d000c031180001c035941030000042c01c0c4100d02090440a0f81064180800309010040e080041748540c00c14820070005881c1190290003820301c041d41c0410f00c00c0e042014000c002c00207041a1400750300030411310304a9001500c0140408000c41c5e86250b081c4001400640602c004003441c400500403a01d500380 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 9942093 1250 9940843 9940859
    0x402090402010804051c050a020708030f04090c0c06050103080304200108061002070e090309040501050607120804020f0612181504080c010908040b040f0605090315060609030f0a14060c0a0f02010204 87
    0x3c52100360001100007423070307413040e81c1e05010400180c180f1001440c034086040361900d5040c0107600422206c640d48003120030b04c0e180102c0c0e401e41c0032a803148041c8402d40e564105015150000c0b542503c0900d40d641c1d0318400d2201611034003c0b160816103036041140c5030007044c004500e0308400c6450951050340700120b858451880c015108040c9400110380e2000b84a05200aa0700e06a0155010700d4043c0800800542e40c09083d44800a0914280105036524000100d04d0300c600d060490f0011800640140800044140c2c0d40c480c1c1c140d0a01013414030880701420744d503800500b146290101a686c04a0000703500540289010b1002038000f0403402411b44450307800c3d030b0050f4000c42d694100050308000d015134100e8100300621490819905001d01c1d240400e454106000344400002c8420b00012440ea541c101074030032841000e402c03a040c0d4031844c2600ca07601d4655400c1514280340d04190100c445000040d281d1103504410078160800c51148001d0313072102e00c034610810955400b4080868201 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 9943343 1250 9942093 9942133
    0x20405060c01060801180302030f0a0e0a06020d030b01053a05070c052b0f020709020307030204030c0f05010507030503070903050d080103060c08010501080c0703030f060b03011706040209040201080405 88
    0x1110703800020003a00d402005403c5807501001c401c0030001104d848800300e07401105403102e03100c2c4000c040e940c1c0c8400040c100c807148958014241e0042000c2000320303038580e0019144442103802c0e28200076210301d5900640e0381e801111900c0341030000c8a03e80c0720100b801d03062581074010aa80e905048507411a1004082d03800c100c1e05900018014a1720400f405020040002c01c8940d10410e0306111056400106642d13000b81850300a000c8075500c0e04e140c080c420040c0400401d0403540440d22030a00c030000902942c400d00c000ea4602c071401c1c4000c502985000708401c00c88005071034261409101c1da409848a800081c294018040026000070201e081403101407854241960707003101c998110f00d403d6044640b00d6501508002070b020050001780d070400c0305540c00810f404200c0751511128a0100c0c0544580c00f02103082e24241400001c98040ca1409141030f10100e80e00b01d58807200c2600c0860b0361350f5089401070760001141010901550141c07240d560031600580c251080402082103080544e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 9944593 1250 9943343 9943357
    0xf0409110618031009050303040605060d0f03050a030b060f0a03051b03070309120c020a030b06121203010312020a03020c0f2b020103050105030703052a0a1205100209011707020102040506 82
    0x1803050380c1c020302d08501e4184401c250303144140c84100001c8007151141940d0380001003004010f2a9036102080781035072000400c01509038030401b9070304000000e2034001d00d05c4c2c04c4079000d00042400c1200395801441c103031064820123036000c903046007407070000c42088005d8000070b0812281c0b581d2541020550080980045200d041a0f407404160415189402c45211141441c020104030a141c004001680c440900c2c0d81206d81014a0501c036444072030018440c404480d140d0105403184041002d484143da601442c1224001c01c003400d542d1018000681c0c071040b12140081c0160010a24440750303180040846d40c505101410710a00c404110b0447d0b580583e40c91a00c00d982c420030030300d98086681c58002c0902400068014204c0603140d0341d22103a88407084002000586580540120000c4544400c1c001c5060000c1c2104145540e8128503810301000550aa03603501a10180c0f20b9400348038003ca80001c001a901c08003480f0049002c0e54040c08044c25a200b1075400304030001d01c3e59110f4000c2e141c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 9945843 1250 9944593 9944617
    0xa02090f03030c03031e011211010e060a08061002010e070e190204030b06190503030a050f090307030b010e0a0204060806040c030902032d0106030305220302090703061e050f04091106 80
    0x52400d0a5a031484a00074000700764000c2c1d1b41e03000061241000b482210b805065102072451100b07100303440185e0713092000e0b030341a9401c490b0100780e840c01c0a90001c0100c0c081d070016116601c0624034544104e00f030758890356003044280e1000c041000364100f1202c0040d840810b6900f00040403010308625405d80c0d01551003601c403201c2c440d05001e00d61400c024601c0c081070300e44d00c42803526807400300401d803a4042c1610110601c0740100f8000e0030000c21800320b038842c000090a46031402c0e201c0c6080580124203020304c1c800500c0c00b1000405d80729003482114151507154031103543e10307a141002c1001403c06141c03500101a195100c0c2e00040e02e0406c09030f51a4069051003001c00240c1c22f04202d15211a688c050100c1e80c10300c0d8080001c240c000003102e84018a0034081c03103010040d11104580c0b812075600c002e40002e805001c100780c07164140d02c030005a92580740c01115500350410703c0a0900781c9405100c0d8407404045140e429843c0c035912913109544540901440c402c641800034846401064007400b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 9947093 1250 9945843 9945847
    0x501030b0f100e01050409080705030409020304050d030501060905060304020d240b0f060304060b0d0b07021501050111121c0e010c020f07030b011e03020d0c051507020105030a02090f03030c03 84
    0xd28807800030119511801c0042c100d00c0c01890302181c8002c0680600c42c07180982e5540d040c403014445820f044582c2140c000045950f035543e200141e40c025881210300340c0346801074a086170740080c401d000e0389040380c0701a960505054241340400000b54405007040303030b00001c1c0d40c2c2020f00054000c90703802082c2c1035818019100c5010f040310703c0103981c88900782c14854140310b110b46035140d4920742680c0d005a0081000510710000c20085034540d894440e0250090844004006100c0d6000402c0e10300302210800f001c3c1903907078500056440001a54591600d41c20100c4540c05030383c1751380b0240c03007020007544900000d100f03500305403000c6880c00140c6111a0751a5940c22400d070703404001d404a0803e4510080c80d1161a58542070160300040c0500c960301c28a400390b00c041c041c80c44510728069900181100144001c0d40b908617080d642074440d06005490042251400c1c4004900f41c070400d136010b0b1110b41c95941c40d100030710020360001e81b54551001140124205c15141040030781040501180155 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 9948343 1250 9947093 9947101
    0x91b06090503010903051e070f05030a0e0402070b0a0e01060f0b0c1c020607110c090a090218090d08060d170304060608120406050c071701090204050f04020109060c030c060501030b 79
    0x6180d0019604080e002c0c0c3e0415903640c000030791000894101200313090543c0c2458100549510b50b511903031a0203004000d1070709031041031201c040001d02000c1084e4540161036403180c0d080c401640156200500181c3c3c218002032000211074202d00f480019150000840c25102d0340b0b41007038503030550400c0b114034102003014000008104001c50401002100511041e0007881000f5a500b0000b0244e0040080c01c072002c215000080122403048880103200004038500402550001c14001d03500780d10a900b082d5602244080416025001c2c100000c0a04a40440000261600180540702c00d400021540658005c150054100003400f4901c5500903903034181801c01d48151411a00b248855401503109a0210083c0708211404ca500380e003080c6456589003281c450031b00c007040e441810305104c0701d0280700074180706500c803021462080b14100b1482e11540c54a034808101124000d021450313861003400a14003641c4501c210038400e181160101c401a0380315826250300f80c0c000c44100c000c0741e0907c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 9949593 1250 9948343 9948347
    0x102030a020403061a0f101205010603020c2418070302091f170c09040303141503010c03050c04050402030c0712020304060801050d02030d1103070f05070501080c030408070213091b06 80
    0x48070701405c508462070f84200e12800039145041d906051840303507009098002440c2c0c01081184119040410b00700629030755204046d001e9171201180e084280101c51000600d0981c144004270410203400e060f00c41507503200403404c12444501650071162154110001c0143d441d0028180300314902514480c080407490108280b10702c090300b00408444540c0041c843c100b50004d484110304c5c02c1100d405d8101c1d1114202070b0002c14412021941c03c480b40c1c01004078090401c00f90b0380441800703500030081c2082020703080b811100c080c1c40943c011901088100180c0c60650051608164013000703483c07404440e6602e820000c80390644003809a00301080420103d078020900600410b015038050500031059030020362103011007103810b414800403050703d0b98000740800030303900f42c150f004005140300c03c02030900304c0e5031741464421103000a032450000364150302c8000c2500c0c000c59000030400d060410031340c00c0042c5800840880200c1c66552900030003c03078001c45107412454080049207841e1030a0201c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 9950843 1250 9949593 9949601
    0x100303030e0303011401030914010504030f02060c040e060f010201150e01030c0b0301080307060c09080f030c0606010201090210031802040906020903011b020a060b0a030503040e0117070b030103060207140102030a02040306 97
    0x40c00410b40061004000c4412001c0412035101004d00e40003511b000c843c0342030804e0324058521380c0c28079840d01d0100020140c000710040c0b01502981c00300c40b82e40d552650010800c1c4618021084a25690340c0420300702d003003420704164900414000030989030b0845401040406080d03219413691000640108140f00e1262481009082e0324003d051035581400c000035500e2242000082c4116640d9914082c80c502c250b002070050051355047e01c0b0640200030141da0380790000300f4103901601504000c01c1d0749600500c01c51203006da0160030f50b260364051180507402064030407002c0c0d030076100140c100c900682d03691044a0442d80329100058981c89a01f0515085400003420449900900f49032601802d400103074450302e580e0302410114090022001041103041207070300c020b0940c400810045800305e003407020700d41601c076001d10f207a2541e014004044d80d650b18034400ca5000314401c200500204010380c00400050b4080c1e11034070022266503070030710308990085490915066011400344100030705402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 9952093 1250 9950843 9950861
    0xd030b03030f070201201c02010e070e06120c0405040303060801201902070308030903070209070203040f0303030c03020c0706080108010c030b090a0507020a080d090c060c050c06090112020310030303 87
    0x550401040714412100c0b0702c00c850b8040c0c1486403c41e003031b00e500b100e1245603403510005981a00c0c0500f00c810120041e42074085250300c099404c00e240610594000107a6400301c60511064034043d45034102171000c24040b41444a215014101500d0450b483d1030007141c0c0101d01c0703941c000071202d142030b00c15030844111300ca2000342e800e8072542c27241000e1404010360360580d02c0e1486170766850b00d816078241c1c6044140d600c0104000d6011042040300780700400641009402aa203d540301e0350b80c2d0804030703220302c80e9016000c020b103100f11040c03010a110f9841001c110549040c0149011800072101c0d207080b0311503004000160307010005001c1c0c203500380a10062a0210305041c0b103540c00110005281441c024551001d45550741c0004030924420401c101500740c120103115590480304484002030084140141c0306c1400d0740e040061014031030103925a03617a41040190034002160001c1140c2984400354035410811071040190285055100444c080c070b809110a00034186545406015038200399 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 9953343 1250 9952093 9952099
    0x80601050a0e070206040204020d02070204060b030402031608031218060a05070306091116031803120f110c04240f05040e0a020306010e0703020712020303040201110706020a141e0d030b 81
    0xc148080113030000340c030703d401c564100c40250721003001c3c0114a00a0040141c0070b9809803d04c2000070300c1e55100c00045008074021380a0310308007902a40002c80c40c01091150307480f1544200a000910510050050380000c110340482d000700f103a10341202d203400f009450750202c1959480500c004590148211801000188000e03c405041c500e1882518016904002ca540c4142900002010320468550541540c80c42119103202c0c0c0301e043c9a000d0800141c410070200d00d0410103201400d0040c9020074010041200400e20f1300511814040940443c40c2000d00003001402c05130a1004c6480340a0068426080348291051900c0c0411050f25891841400d164201d03041600c050f89001c144107040d01c1d84152220200c0c1c4034041c045000f4865004040e00d54050014032138125079000c0000c600441c003da96580c0300d5a00c9a807803940340c4c1c216203d88400342c0e100384070083c00510842d600f03807005580ca2060756070b040300c0c12285444107901d00380b4048a64100481d11840c1039050302c1510703043c220503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 9954593 1250 9953343 9953369
    0x8190807021207060f020301030302070602250909020301090204020c0d0206010b0702010801030314160b010501020618030a0c02010509100c021c0302030901032d150506090306040305030619080601050a 88
    0x200300180d01d80c804000b40d00886200014482e09000868102d142d013101d40050445d0782c0d42e500e040080d150300e500d001d08001800754400000d41003521018145d549003070503500d6952103142c0003d14004165450303080340c1554036000302401580d507500c0504588860103000d400021000b030790003810800305800c1000c1410080c4804800360740c3c4081c02905403981070506d00003c2d00500800c1c40b0500810a41c0c0300401d20b001e42ea00d040045400d030103812128280c00b2140c0c5521001c500c525500020b5011020302d82c0203101c882c500030700c07814100c030103140181000761030000903201040c281115001103201082058000c2405c5041601c2190b43c000c4140c0f0308000c5561003075500a44030300c1000301860405840d800b070300c0c855640c0143c8a075141500243d02c0a00540450b00800c0035240d188000c004d040394034040041c0c6801c2c41c800319034425800402400090361155800d41e5180c101170001900648a1000e01c1000c0b04075600440240ca11000104140d41c586410000414100e801c40241c0b0070031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 9955843 1250 9954593 9954601
    0x604180f02121608030406170403021c030204090f02040e060303030c0a18120501050106030b0301090209010506030403200a2003060411150d050a0b03120d0e010603020409081908 78
    0xc608910300416811610700c04145064226a4074041c114065050b190f00703840d100082c91200000100308a5100e03403901241c90041c0d00d80351851031002c89010700541c03c0300c0311b82a81c60300700d402d41185440d0340741401814203803038100b40000c03114030364208001e0603400101401801104015103a00c090200c0081d80745103464207030008135028486003c0d003840006107429441200c601d10303000160212070f02c1134648002500f0582d020741003c1c86060007080c80c0c01c05506560806014040842e900906801650b900c1c0c001840941d40c0014015000c105600e2340340c40c90000d041c1c07030b40a13100c5800002801c80d00c20382c0c1001ca5480304e02e48007006100049209207412600e0101e01154400e0308400c0c000c80c013200d0340c804207040300c1100c104440700c054001112212155154801c1c0c2c00380481c0364040180c440c0304024903680311030004110034140018400159440c0664112100f4058908001700d1110303035a502042c281c5540b50f100319130107480403898042901e200c45001ca4403008900c0c1115003410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 9957093 1250 9955843 9955853
    0xd05090c0a0b030702070e0408070b010e01060c0318030614040c0501091d090f010204090c110d02030412060b0307060507030305100f0902070305040e090c030d090b030705071b0608060418 82
    0x540b44070702d02d000000400018041030082c0b11550003406003841c2503143e89843e142424a5500c5020300311031740084400041806040c00b610603040c0c42e6079844008000010343c505540c100490403d910b440004580c002c00080c034140107034040a8800c5000d50b40606061034014803240c0c094010700d0400000702020800c48508100800032074220340d400d124151075100c141410300e10180d0704180c5e0340d07000040004500c4500e50041f10044201e41d0b1b00d1142c2c1d940c0c0740e80e068071490115030a800581c0140400d2200ba00e542035241401441030f0b0000600107030030341c042801e00340c3d81c2e070140020920100e80d42d000d1541600916074484070011146200500703007010b506070007540e40503540500d5404a480000c25014400711750251514092400191901c0c3c0c194555030040f84000d20b000740110c800183c9c425000310b40500540f60001500d60560740d03050b13000c444030f40045500369482c0303800100e5007400f482035000b550f029000543c0d0388400d074a000c1d420b01040d9458030751256413030034a401c0b410011035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 9958343 1250 9957093 9957109
    0x3022d030d0b030a020406030803010f0801020310030212030c060c03010f08030a17060105072f0603071407030302040b0c01060504061205060c18100305061008040305120a02160501020d05090c 84
    0x4aa84440001d0504440c00400e04d00001c124009410514000011050080701001707181225003500c5036908403a110080e580c01d0b80020345252a60030400d6209000514050360011081207140003103c0c10907540c0c888491030110151584c03d0b00030310003c0180403840c1070317a0359200a40401d0006502d06194060010840f120054400c0c0c0b40d9103d40b40412000e82c401c00403a03a01a4100d0304000c042c59230211010280d1403950680e504000c139441940b1410b0034500140c1b0704c150b400703461f403104513140840050242d501c120812420580e007003001240220410002e0022403800700d00006a01c0c3c01c103418002150f2085d00040070100000200340c0c00550300041c001e03402500c81d03604680303680004181c1c85004400040a5030300a09216202c841c441e410750185110741001c07500305042600c00c0c8829100c100050354041c0009004000e0709d180542c2d0100c90a421500c030000061900002600b0b64800d0300d1100070480d4070382d4000610700c0e00c07180c071401842c2c1c01ca409640035100c0440000c1c0054044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 9959593 1250 9958343 9958357
    0x901030b0f090f0a08030604050601080c070b15040504061407020102041a0c070812070303050c04050d02040b010c060e0a020103111602120703050105150301050f0912091c03022d03 79
    0xd001070000041d2404014083c1000440304071044400740301540ca814080da810440f0108d004501d413900203807140d0300c40d060403802500301d000801e14018141d19406c0700316900900450050f0a9144a820561194403455200d01e01039280000c030075641c424040340c98075020300081c0442e130041c0824011100c000c0e00c9802c003407400d102030310b994817002c42445092100d2584150080d0040d441040c0001464100400c0c038a0300c01d03681000559200c085802041c010350160b41c0d00100c0d00b6031850700505140e4005880c0800505005105418035aa94001e80c0c044215840a0350000922101103581600038034901009540e909400c18031542c000071035011103401c01030b20800b11005684e84800f0305210000203150000000d00503864032030342c4070a00f52462010b5070b0003580f0b010002400000100006030040d910540988100d000c3c2c070705038604c15040b1003c200d40c0301c00500b42140440150000030094181701360040d112620000c40680c420710b200b249040e0720303c0440d0101086406010003141c403c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 9960843 1250 9959593 9959611
    0x70201140c04290301030501151205030711120f0d110703050a120c0602040603021c02090a0308030c04050303071203051003050601031203110a0e0a0501030c050d0209010c02190501020c0901030b 85
    0x400007000100f001c2180000400b865000004004000d2040c190414201105102c407285503499842c081101d810050a0018006030018843c10700080e408510b2000c10b020000c02001030580400400c90400c0103100b840401d5602c4041001c3c1819004800b4403440000e00028010035495922503989519060390000c1011072200c202400c89030181c041e00d0941a0018011500e07680c8440020b40258000715081050b02d094220244440d0700a0003242d0035480054082e0a8551442e030340d4400c5604080e20340303080080c003400702180f140c60070000f81ca4803a014446010000f0702c0000080c044a90190060120640d43d1005202003080098140d0445c3e52100314041842c00c40001100100202000000c01600c0001d080700a550301c48240480c01004843c2d815103140d0342c40c019400c6460000d540e1020031810301070702d48600e0321940500750031141070400124060069000440790350890040030074240f000e120501895034100000c200741c40042d40d4040465045d0b480392842200004e1100e81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 9962093 1250 9960843 9960869
    0x40b1807020307050307030c0b0a020307050a0e03030d0c1710030512070206040909030c02030f0606010f0c02040b040c05030f090a0b04020609030f031c050624030403020c0a090203070201140c04 85
    0x1a14501c00c02c21140aaa001401d583d00d442d5203240003007103004000d9083c0c417100350020115801000d240300720390060005440316440e040b01c0c0c150581c3c1d000e41d07511074554580014032054428800700d028840c8140c1c0c060303440d1520640b038415030161100c2c01418061100d44039600a10003d00b0000c1d40101018a12050790b8840d8958400a00d0358802d41d0040c0143d01d0409101d001019044030070071a15a208509450300e64a24200c0c9a40e5840e00300e500030300046003541814441d074080d105030400c403400504080b5030260000c0100c2c007503c801c440340800180c1c0020402000494503454070b500942d610300582096107507602c2d4240003030f6015001a00c00c1c03c0014441030700d640c0420851b0902d402036401d490301c0c0c0c00c013494a03072203041da00d41c80342402d14102800215a45821818035189400c040c030304101c4d1511001c60f02030a034000420480541c81400d603032110a2340e6040ca5003000b0000d46a006d40e4a00d0407403c000c0c259002c1000c21125000c40c50180401207070000195020758020b258149 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 9963343 1250 9962093 9962101
    0xc08030a02040f0909060c020c0f100519050309070f0602030703030b030f01110306010905040b06030103081b0f01061401030c12050c040e09030a02010506010c08040306020d1d0706030605040b18 85
    0x300c02403155600411541c0d4102c40c0006907141290400c246560284c0f41c1080405c09903003050340c5410f50741e0b072001d030301681a40752503051349051291424284850300c2c040342061440e55003203241e0304494100c000420340100030010303021800c012002c05404c650440c11b0b035003484c1280196403405031030300082c10b15460340210355a07600d00700403844ea2008004000e01000d04011940d801c564801d547d500d0008002c92008503142c1010f004100391030f24080c010500c0c50b86140c842101316000741c07180051001c1c0718056980c00b21400c0080381ca403540d0310000001c6641c600700400c6800748651a402c0d05240c145840d481c101d40e003003040e92001c01c0030080089865512410281111311550f04500402e0504030140010410000007516600e400d030380080003981c88800055503810444140203102001c200002e200091498015064168a807070b4041551049004018014500000c80c1d850980c0002d00410009a040c025000244826142040f01800d5040400c0e8907410698030003d80501d594041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 9964593 1250 9963343 9963361
    0x2040633080604090809091e06030106030c12110d08030a0510060f0f0201020c0a0b06190e0403050a02070e01080f06100501020d05090a050604030507181b08040507090c0e03070f060c0803 82
    0x3039031340b03503002440b00887c0c0c80c1130752862088007401031200000c01110b40000380c090905200b0700301941e402c60700b004011480d05c201c034041200c0c000c104a034020304a001d41d644948424104542c560b228440f000d48a02d0270002020032154000c0114174104800030742042107a402044540040c2841e00c1c00841854411800741d003e845140e075140880d00c0ba10840100b03110081503454000c510171580840584d541c84184030f400d00150143d90310118400e4041000240550300600341c006150055030061540e80b5020a00300000342d21054a035007041d03024002807402484107030742c8180d4110189001d10305210000f50395881114003501403060024840d540c59580001e854018000140390076520754503031030b000361908002c0c840c00d40d480d18400014841c240080c01540030f01c80201507981059250074a084402e01030181c4103440a0044040100d4400160b01407a495083e0030745500004a2a0405051030f08401340e00a03600003c0420041c00007583c030215041e0240c0c0c2080c1c1240e100d0301c030b038040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 9965843 1250 9964593 9964597
    0xb06030a0c08010207020109080303010602060106121401030b04140d0203091011010203010902040509010e130809060c060a05160c0203060a0b01021606030b01030b0d020a06030e0109020406330806040908 89
    0x8041c051903021030002512590540042180c607100b0380c1c90117603565580381001d5680c0000c0c090300000d43c0080c4010300c0028810130482074001403243c00070070901c8042e400c3ea104000d081e0020f43d403100c1c501d402c100500c41000d81405000074024020701c1420145100292030f406440c0351b0030f200c1c0c040b04042c985c031584030350300400303210444200131035032540e4442c484c8d80254018480c40e03000c0c14042000180e0b0000c4261054456400e0f070500910040c12943c603036070b680c1d1050060503400a01800b10440e161000c0003030a2140d40d50fa200003071181484d80b4030201d040d0588201c01c0401021105540050303e001c11a00d4002c1e510700c03400320300c840c00080144c0c10800e401c075008041ea100c2c04400500f00703134107400800303c0b007000b030b20304000224a0505112000c00d20081c0a504007942010070070491744039a0044146407921400041c2d520b141d42d0029040c0c2e00c070b0340d200c070704d2050a41c85440e480302903030101c05a03030740c0180b04030b884850b042001c00b8100d40001000980b04960b184004014484c41d801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 9967093 1250 9965843 9965863
    0x703020609030a0b01080a05010e03040b0d021b0604030e030c040b180703060b0c07030c0603020906070209040203160807050a09020a08010317040302040e030309010c0e010c0b1b07080315010302160b0603 89
    0x8241c442c0d031760b15410100d5440c60a907606449660805940c100203000100c2190150303403541d10a5441e00031058904c3c0040c0d0322209064100c00f030355080041a0315001c0c440f15000328401e56a05080c020014101860b040080310503130702c10391400506003080c0e5210f03040b8142c0301c01e078081865070f2a40e03051400e03801444140d101020680d00014203c0b90844d0106049080d2407086040c40035140e02c40c6c030220101c1c022070303c0085d00808204800c00140c600702d00c085038001d100600b11172018405200b03019111290760711800059002e041d0078042d5107403446011001e081001021400c140d03074910b00034101c180c1072101400050002000501e190f0110046902640c0c01400a014440d071610741c250b5258030131a11034201e5407a0140300880a03103d103901c543e00d000c0c1651000c0d5005a03540304c5149001010300138001c0c0510440d4681c4143c441130001d000403038000c640490312880c015104000f440c04141200341014410010b183d03d90b03031401c41c0900120380240300c800055a901c0080380c6040c2440c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 9968343 1250 9967093 9967103
    0xc0d03030f090204110a03060801090c0504020c0c0a06021e06060a0b30041e0203060a0209130903030504020a0905090318060c060108010e070905010f0611030d0204060801051e01020703020609030a 86
    0x40b8400c980d021750300003400345812070341e010000c2e165200001422502c40550040c151100d0010401452030150041c00005000340c080c1c4000c9000b40e0005a02c2c1c6513203034001c20150b04070080000201d564007448082d240c0010010340b03440e02d00500026885030703241c054000f0842d00458250605041d01e0400181d0f143c2c0a400707204003840762008001c441204940071203600f01034601070400074400e0400658426400350060046448021003031000c0d4001d05281504585d00403401c510409841c0a04c0010340d0103a10006941d04190050105608143d00069141d90516041c4035940318000211a081c0140b15020f8208001c0c240000d0000d00c01c40c0030405451003050000b00301008194000107140b140e981c01c03100290b65400ca808190b880912480400441c1c1c100c04102c2c10f401010b4080d0051308010079289400b40e0040c07034030126080364000c80c0000302030000500403804c100e40300030414072a1544031001c04140a00003542e0340d0950100034060000402c0181e5252810042d075540580e2103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 9969593 1250 9968343 9968351
    0x30304120804090f020306040b0102030717030a110f0d0501080f07030f020103060308070605070206090115121a0a0c080604060b07020f0a09020d0b030d0504050108040314070b07020c040b030c0d03030f090204 91
    0x11365102000703900150740140c03050340703848000c2c4401e42c000412910010742c000540d2486c011251400c10f8160001811400301644500040e4881060302c402800e040f20b195503a03070b031500720441201c0100e40050700190720a5000002c510795140001401c0b4046960001b08283c0036020f40c4012005020b10b03500c0206038480c040b0303000c01045000e0704058801d6041754200d50065030b0f11420f007803e81d00da1054070f8040b050000000e000d43c8415610b40d4080500803441c40c078007070b07000780d600e01034480d804c445505100b0380e1002c040018a50000207283c00c11000c82c0d090000d03070300744540d0303061611807100004c4c481d01c0c01e54030001107130312800d0703001c80240558201151240c0c04003200d40083d000780030000c0c1c468040c500403d91a10300a8040c0c0f13040c0d41069440b540309545035641903541500d00040020840c0c0180050800550b0003400340c1d11035003031035000d003022000d00c8051005460000248510a0b001900484001e1f100c0512111000c2e405150200390710b0890040c1e035008000e4400c0c007070b400c0390030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 9970843 1250 9969593 9969611
    0x1a0f16030b09010303120c02030a0c020d020a1d070207050609060301140103091407061407051504050c03010207140c04050108060c070c0b0409150806040203030403030e01021606021f060503030412080409 89
    0x710755142d1b00120140c00380301d90400c41070126100d210b10344024000c250305840390300250400c603002002a61024000c40b100d10789840c40e6410208a004181c103e441e1b8000412280a505024103c02824191203260420441500050f0b176800305004e10340c2090b01071034044205a2007a080040042e400c0b400d80007400d0554404d664945089015074030105008100420b16401c9400481e404190018054a0142d1403800c84407040354014005868911541c00b1038840360744c00784000c1264500c00d1254000b45061190020309041c04000d01780d00c070b1481d00004100100d40410b2080d404540c1e071420543d90383d00380ca829405860182c0000711041d40101c3c0101c0c8042c4150701403400c0c1c1300d4403d0149002681c0b4041c66565020803280250035400074441000081d0088644038046401401644c0303a80c03425152401034805142d1154006a03c418800c00300d040010013038a8602c481807005104160815005c00ea6074469807181c10440300c40ba011403c144400d80c0280c07009003080440030300840c06 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 9972093 1250 9970843 9970847
    0x11060d0b0a0801150807030807020f0112020f030a0b010f0c0209060a090608010e06130317060a03020402070b0a0c030207030c02091308030f15010e03060402010804081608071a0f16030b09010303 85
    0x1312407210506941e079206001c03c945200189082c1101d81c0610b4030751074001d01da4240899035036040121414032054602c40c3c100040c0500150141ca10211a883c1e00ca1500c03448641c140c2d01c900141c107050042c0d810f1183c406950100150a45540668541400e501c80301c0100b0180354890b1b00c44252a03180c00307000b103604201900080c1500f140ea0342200e11580b46c040203070350040e40029004000c98440c41c2c6590700038008411413544508003c0004105590701d4010500f66800300d0011680019038104001600c0039610a41c4010fa00340d140442c1403014a07036025000000d04580039118503051000528161007584191100c580d200070050340303901303142c072000407040c0c0d055070503075012001c0451880c1d865208203e01141508002c004182c00d80716600151641000900103944900d420031100452199540001c81d10600c150002ca91b101000c3c00e00d0011400d0074000324502903c170406000004c6c040c0b0580603004580000d040c100e8803544002500204401010700382c0001c80c21000005041e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 9973343 1250 9972093 9972101
    0x4080d0504090507051204060b0102010204120503070501060f0b040b03060301020c1e33040c03080c0a0b06030a020904031101020405040c09061701051309020111072c0411060d0b0a0801 81
    0x41c00b104414419501e03400d40c141d0701c50081d40010401c914040740043d01040003600044014001800014905615006000489060054281e0741c0303510014242082100034421600100040e0100c0c1c040c1508024034034650784500d00c2040803511010002c030340360713980a604584c00070390418221401c0300c1d1030071031468140785150720400050246603944800340c82a140146c0003025034555103403074210809040785848001401c03d5800188030f90020000a0600c001001c110344800010003c00925140440641c0c100610150094101c01469030040c4c46200c01aa08658903003021400720749a0fa9055009010741e610255005040480c1c03042d07510b0b002402c0c503050300e14032381d140b542c50070641d22210307400d50080c42402c3c0c1202d9207507060703038100c55164415400c2910500d0102c1c0c54004c805c1c00030b0f14051a50708000b080e03128404d000c00003490030b180122a0511503a401001c6407130152144c0049031200c2800d032340070383c00005084011181540c40340c2c0443c100144040308054668510500038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 9974593 1250 9973343 9973349
    0xb031014011802030c0702120f060c0301050307080106030804050607020d08070809010f05030702060103080d0609140711060108030406030908090301090f0501270213020c0303010b0a08070302092404080d0504 91
    0x4061800102c8071a040c050007103030305c20083e80000c80d14003001d076401d101061400c2c88002c065806500c82c46000c000c0c041c004c7c6070142103051000340c0c0301d50629040500b0b0040c0c592017013116a02d40001040040c40a200341c1d001c469044070419210900c5001041d01c42a03c141c00811100c000a010001c012070203015041d580003c0e40c03804643e020000d0f064582e0300c016200c801c0540c0c010001040020718500040c45944211207001c144035039074003502d0303040d21a141c0364010505080d00410940315400706000040c0c0c682c3c2401406107501d410952500c03407080340038039400c00d038031880c101090141c8502129030b407034400340c000c0041900c0340c28111140150044120355039401e19110824100541401c2c0780e4941d4030003646000c40c1c005500b044010721114000008154082c80011140701040c07014500806591928950300d03401038000500740d400040c07040c0c1c180751040c00312036101c0e159600d4160340301020740e504104041000c2c100b1596030045900c0014244203455440c00c070b450b4400080c200f2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 9975843 1250 9974593 9974609
    0x161203030501060c0f120203090a031406060a030c0b092202030a0e070803040b03060a0909050f0d020102030c0d0b0f060f041703040605070209071b03050307020f010507120b03101401 80
    0x1181d80b200f03800c442e082c20f20300c005401d003000a06400e0208516001c4e408054860b0300441c0d151506400100300400c426501c25901044003440c03110079144240245079010700110380c0385950b9419640c07680303481c0b40382e4050001c0000003c2442c0209407141d42050211107417105c110040600b0b2000c01c440030f584101c83c1c03d8145410042c0250b00050001954070076910008061403c00341004c04c07030340c2c1c140c000514840d40b00002200014084501b842415003060241c8040c01c400c07040103001600e060880082c2c881103a104108000b50140c06005a90000b854068081811650180007403c4000103415040d401040012500b244c0281c08001304201c64405400e0300c243c10751420744a80307a00551041d90b0205004101c000010300d400740e08140e0003003481c10190ba40340031404c4994001300341c0a60840c04103600106020320680c0400c0b80740c8030041194001e0119103030503900140001c450a040c0f81c01c0316211424104555824014001da80e9400ca000304400354229107400b00c600d10038402c0c594 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 9977093 1250 9975843 9975851
    0xc050a1502220602030307032a020303041403030103030e090606071a07020c09010506040303081306020403060f0501080c0a0e1806040507050a060c0308040b0a180303050702010c050705071716120303 87
    0xc0550500b00b076120031540107070040c60540c0d0f18040150701604540c48040c04188500321020310604800502c5a080071042d40255183d14003850311646110503c01c0c01c9a0796030007400100002584030030f03101c160480680e030709107003a00d4200210701980240d001c010081a5440c0409100300c0d00714495520500b441e07405c41c0c0303c442c5001c050090f500f00a00481350003440400080c408203000d0503050790440301c5000c07024180da07256100c0d6070032a00603400072111161074128400c4802d600e801028007411544001c0d004c0361121400044072a5007501c248840001d0031320000c0c0814818003052003c10203600c00781c816500d41840d020340c440a090050501c41c6040c21008640203101d95140d1001c1a0300d6181e0f1302113038807140c95032544618028005006280c07141080d45c003240d9440e40c6030310080d01c0f0341c80c0424141890617002c1d00b5203021035054820060f0a0012a000c03820004a0104540402c4079020320703407a9203201603081040c40c9030600e035400342c280c0001482c421868000ca2810b03019a070204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 9978343 1250 9977093 9977137
    0x160b0106030905030306040218031006051306080c1302130308030a0e0102030105060304030e0a05060703050c011d0c04090c050306010e1005030a1101050d06050910050103050c070209070c050a1502 86
    0x58116046180b024249600610004141b03080c503030b0003400c1c580700d40c5d01c19200d0012401c0010340b0b04140d00e18a980320380d407520300030807803400c021604100281d06041d00784030342c60500301c6003039548a803540c68a118082400300c4141400541c0d040740c1d2030003200c061100b0350680745c3c1070801a503842a62444075041c50300c0306400720018180f01742c0f8142c83e8010809883d5848680302110030740794500440b5031081d08500d0008080d5114401000c0786031090702c40c0c03070b100d088040b80c8a08495017411052004183c890103401504030100da5440500000c40700050400c80c14200200c444034983c0041d0740510031f401c000708840311075001262140c0c505170200c08140d9222000e040d100d207031464004003030721008060301d07a82d5070055020b40500d410400b4001000303651000010305001c429a40202c5000d110300052282c2c2d641801455840002e840540d450300384641c0c0411081540203000001f08018030343c03034400304002400144251034110310000d11400baa950900300942c0490600710f001280340d40c0407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 9979593 1250 9978343 9978347
    0x13020906100c02060c01140112111f050d020705010501080f0f070312080a0f0c090f0e0114040b010203160303020306040c0e010206011e0302060c03030106020d052b0f02160b0106 78
    0x141c1c51115038541e004024140d00b0300c201a007280450646554030b49903955030141e500c0c1c000c940240b25034840c2852600450800016190035460176a000d60003500b11b07030b1650354400d556012210750a01e04165a540600f061400a0003034a80081042d401c00000103451000003480054100710310381903400398145e0600d0113640d01100e220050482c0c003903000720000d050160320595840f0200640100780b006010100c07204658107001030901007003800c0d80601681e50b00000100107013915606015255060001d0000d034250031201952050751500c0450b00164401d000b5a000720b0781300301410303943c10001c0c070380034029400444100c0d00407454054564046c610403000c1030b601c8070068000c4c0115900b051004600703115901982035021042e0f580c0000180ca400000f4414a900c5002854a95040040c02810202d24080500410205002203001e0084114520070441160100d00500505260ac01c0001d0510304202c154410b1000c81e0302202c4000101071901098070450201c00142c1e268942 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 9980843 1250 9979593 9979609
    0xf060f03030a0c12030b0405040c03200d021e0a170105060405150d0611070302010203010e01050103020306100507050106030804080307050c04020c0d0309080f040609080c01030b06030402101713020906 88
    0x2000010700d003109840c01013201d00f000305100f18050324010800e030342c226022a0560700c05507000c0f200802208410006d111204500a80e14218282103030003105107400001c5500c444402c1c040d204805107207001d85420b20680700440041c40c0900040c1440b640c0b90401a1000800f445003a5a9400c1200090081c0b50a12480d446004501002040c1405c403e040c010460080001140e01c20380e150141c49440000303001506206100e540050395a41c18401c501c50b0601040e480346040c10f005100748141603035001c07070a1300d80306010300d00715483c0d200781d040150140034507500185c201c0e6400100030498560200c000c0c040280540101c502d00d42c40941072008921502048100725009020201c140c00e100342c1011031914011078402c0d0400340640c04d5185198000c0d0b1004c00480c020590030030584006000380c0d08461001d00b410040742e110240421524031009000034805c502000c0e01d0b00944c2d01801d5900024031240303a403280c50780342001c0d0002e00d40990010a0b03110f884007200103642c0e0f1821401c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 9982093 1250 9980843 9980857
    0x10f06020309010f0503360705030106050a03081305060414030114010e0c0d0615032a0228050106090b011715040506011205040b15030a051507090e0f060f0303 70
    0x5a0345402d1320260104444a07000038110807200980d20382856141c01c0c006000d07404032502c1d82d40c21100c5050080d011403819280d58030035400ad905050003080746958035124a4201c9400800d0f0564a020a220850f41c5001c642c200c01c0d840b5902081c040b41503a0310700710400090340b00707400801811249540344c5803000c074240302d001c8030381000c500002d054001c42409803800160000c1c0100f030f01511000c101411384641741204001030350340c0658a188070075060240504c505842c620908c8030007500c8000392511100d4120030380642050090490f00a420308070f100310f00790031100070852207440d40c030355001900503945042e002808820100082c0540d140090f402042603000001e285003a103024040503240040c842410b002c010106040c00311410301425200e18815940018285000540b1a10129000c00b50034000e034049050000041c2c2c0000c0d080300b00341003406404036141e0f030704082103842c0010b98011480c60802803044c0564040c14940030780c01820b0441d2128048290300e0b09050703890003112 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 9983343 1250 9982093 9982097
    0x5250b0106020610170307050604060e0c0904080f03220b0f010803090d0204090204021201090203070201060b090d03080402030709020a0302030a0b04090302070b0a0c1a04050d0207081e01020d0e06010f0602030901 93
    0xc1000f802c04c0b942a1580c82400e40300071b1305d04001d201c2d00c3c1c250804604640544001c0e4a50814180c185401d001c003844407081122444090706240e01d42d07075080d00071007045001380b41000000c21038032401d001c40c0d02c0303e80c40800991140d03002c1518045600d00c0060310200c500c8120140045100c035800310503105000305c0a04840c00000154007004090300c3e401c0c801303076001682004400700f00010a102c0754082c051281016903a42001c20f4000e0859040e94025207131081c09200e11090f07541c0f03801d194803071640c2500d850750035500c4600000381042c08550003001424800501d1061036901034001d140300ea104000108070707402c0d08405201c259030240344001d005030450f071018008000b0030300c0a01340c0c40e05646059880c5c4207241c1ea80b010181485a09d80041c03480b82800c21080040401c00081080000d10240c0b000c1e41c43e1806442c1c0d20300724150f50703d4081140002a69482009605450307901c000300600303000e4801e4081d07100b9116603081c01440910110510007181d0176000000b00c40da0140e060f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 9984593 1250 9983343 9983371
    0x201020c0108060f010507150e070e0703050c070f031205190506030705060406110106080304090203010e0a0605030303060f1f0e011701081908091207050a09060e010308090105250b01060206 83
    0x2001106d05a0143d04125458144200480c00a06d95813003610540d44600005207a40d9050030b502da101002c0062032038080500700710800041ca030100c0182c41000394041d04000c048581031074152198460a060240c10078900801c000d079a03c1c9511410100d060303000d90400840d200e650034541c070307011123018654104900300010081c15208800304030041c4084000060019243c041e09400c55001d40d00900381e10303070080018040b1038115039145410039403482d400c029551601f00400e0b140c1c00001d05040c03151008484625007601c440130507801d80e40000e08000c90134080d001001e003451400c02002d6000811280606070340501011100c0d060301d0919006203566001300b081401c4501c034000c0212a01c290503c000c01c00c507160348140c013080500c210050208581003001340200940903611801105051800030481d94050820a90551350001036a90380c03201684016a214820754200400e42003030122022905030140d41030048c0709200c1c1d02d003c01301da661406c1c103e80d1280e054800e00c0c481060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 9985843 1250 9984593 9984619
    0x1050606071b0e0405070f080c0a06030c0315031a0117030702040902010c06050907081204050108010b0a090f08060108010c03020a02060f061306080a0606050409030804060506040207020d06090201020c010806 91
    0x41c80000018002c001000c0007060361030b40048403030b60f20306a0f411200c0d60300940c403d01c10107102e802d0000240000c100140240b8101c54001030741c402c010311804040c503039a00c021002c00c2d0b201e0b80040885c1442480c820240c90b030b4034904000e0305013540b18840070340b848102c008281458141d81803420000c0840013141000307416000c1000900e0743e44001ca0511294030580784c00200c40d8014244940b5410014100c200e14184120742000385035140141d10038000c20090000d6a0007a410340d06440041c0b9171a51601403500061b54401c3c5a85c06c0000c5100c200140050545400542035040e00d41d07960080c0019200c10b501a000e9003c0c1c5480c41d0050703001030000940b0500301c040100e52002c0c000300190085400c0b034691101702c03903550300104072680040d41e08034103010f01405018000e040c20307039080018905544006141c400d018100500503a240c0003c0344955070356070141c40295400520840740d41d14076150800041294400c124007501500205038000c0d0b010b081030030b214040103054a180146 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 9987093 1250 9985843 9985853
    0xc1201030b0a1409060403170c0a080901020409090b041101081003110301140901090201020c10020705060c0f030f0405040e120f090303070f0b18011506030902030f0a061a030105060607 81
    0xe0002c20440341e19a503803010840040e444184213004040900141000f400c0c01e0800030440c000400648107140b0f2010f092058601d0700c003003100c01c046003d2a01806075110320b044240a441550701510071181000c08440030f001040c0c08550082c1d207d40f1040c85d007143c481006483d04039044441d080840044101080895000e918111304c207803000700000383e02499041f6071030501000752050105c40c1e64840782c0a08550301049407803a01181101c00030340104c98840300955400d26800341d10300441e4041120211850100306141c00385e024142601c3c1c540c412203406030100d80143c4150b510903800c000c0150f41d02c000104035618120007a00a2611344889400c518460390f00c04040544c0500c010480300002c0b614419030384d80c40303501c20802000c90382003d032070b807001c4c1900300e00d00501107903d1b20302030075100403402680c10100c6200c0e00700880ea4800c10700000f03041030030180c0c0340b45050084280600400607550320141400003901c0d031407010290024245801c0711002c607401c41d0414410000403011503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 9988343 1250 9987093 9987113
    0x130e150402010c02040b040902040504060b0a08011103070f0912050319030b03060402040203130204020c010507111c0e130e0d14040807030b040512070503070506012103030c020f031309050c120103 86
    0xc1000b50010408a00344e9020402f10b0706c2c00c031130a0b03c80700d81c1c035616001e13145800c020710001403246c4802031200340d80c0c19141c049244000b500e804148013400150404050180134500e0080c0410b02004c429607240342080b0ba1641d004042c4e007050601e141c5039210071180079101d48103200d1005001401c8550360359081c80020351001c0c0001e000070560240303000040c0d43e10b000406c2c2c081c450a00104882c01c003003201805145100058440613040091050861400b02c0d00403d000c2c40c2601d000314850070701a000c41e145111011a48191504000c00100d2240300003641701a108401c0e40e510034461008a10001280558000e040007900101c80403c0803454005105410500500070384003003540c9032a0112440d406100c08032010382001c6510300074414140007490040400310a0001e98200c0103031001101c55000c10010f06155403003401543c042c1c4204800e540440388401100d0703455080c091f42c0b034001e2043e882984492410140018900c100c0b40c4282c3e1013404000e10003004d1039003140e44428070f003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 9989593 1250 9988343 9988361
    0x70506032a04051e030d14030403030b0402120702010e0d030c02030f030603010204121a060307061205040c0509070e031c0c1202030706050703021b0c010e010c11130e150402010c0204 80
    0x41d200900c0042a0b0340d8030030440d04442490840d140c211182d103481410b080040f00e2030300a007072000346a0614500420141103c0d40168189000640c41c01550001402402044a0007003070030348a03410881200d030150f0102d030040d00c2d158100c688074910001c0403800e40f030020401800680043c46218603c5c10004007440d0000700c01000035081c19150484c2e0070340400c0d40201603501c20100c14030b120649280c1d504850700003d065000d40022400d24501800c10f44003900e140124580c3c480010f4180007040e06500b018010080c194039107820310b0b02004015008400c00c081c800c0c010700d42079011610800003080040500c6403a04107808130281c5078a0100411100008190f0004005410000d14107115040c4140b0305901c1c0140c40d101d0b00d0514030710404150703a080d410350b4840651603c1c10ba030420035600558000741b92105214402c0d142c03112050884816107038100900b0182512841650703000f0f0b00700b0490800413215103805100500c0400102910040d0200f5000000c01015051582203407d032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 9990843 1250 9989593 9989671
    0xc0201050706020304030905010f0201021303030503042a06031a030a03051b070f1a09030a060f0608030c0d02010510150f1e0f02010b06040f0b07030e100504030507050603 75
    0xc101082c0c0303034441a6801182c1c210700140c201d0000f4000356070066030840846295100071406e1116009200c1410b80403400040c0500c00c0100c0040c0c10000040140d61080c2c18003010482000602d200c00b060045181c090000405d0500c00d80d00c91042442800f9000394200500614082403140c50958a951203c404143d446044610001402c4410032900c002090103c5101012600d000c210754840c130400282207100c030300100319001266400080d24a0013940021000400f00380c01901d0000078441a40050321502011540140007000494400580c0c1141e400a209030343c1c0308070ba003078000f41d900d00400401c000f000c0b41d00c0701801e00ca4070360200070001a0500e9616480300e4a1403140e5400c840c8001400a0b080d0403071804800d80c2809410b090040c151802d5080a0800100130341091040c09500066480820030700c040c140301d0060b9000701d00e80548804200c100c1100000c2042e885400b0548052041e01d9002800713050481c1201d1040300a00c815910040d00c01d289800700d102c050351050b030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 9992093 1250 9990843 9990847
    0xc06060907020f0d020a020a060c050c1e10050d1401060f0807020109020a17100204081b0a03060501030c0f0b0403030c06020a09180606020c0405010303021c02030f0f040e06030c0307060c020105 85
    0x3502c030b0303010400000300d405a17030000d14028505104004d113428039500081d00700040300c001c42000440019038007181101c02c99a0300b160311040e010041d01c10340c2c9141203a17440040c003010400d070300390004c00801104042d0310042c0000a101800000c101c0340a10512001400d0614082c45162082c80c0c85074110103248000314103007446400040301540e00340c00204048071540041202c1c00800c129411583e6035500d82903003454607009400f030701c038401d0780150844411f940b07852505030380d00c80c14800c0c05036601139400c0001d542c503410481c2e041c0364503014003108111222000308040650f03074155001c9960542c1c511030320110640e50075020350031110a903414445010004180303041e0b02c0305444014081a2400501146130180c02484c0c51803180c811400740b4500360050002c80e501281c0c1041d1160030504e070a84103140040201c2ca503201d1880c6007000071601203401101c5030342420050086546000000c14640c17146030400d0780f10315084400c43d074564890802081207902034100900d0003070050500c94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 9993343 1250 9992093 9992113
    0x70c050301020a0e09070903030207120201090e010806010302100e1c0f060603060b01032007030809030c0106030606030c05040c0e12011103041118040f11040f09050d030c03020c0606090702 83
    0x3400e903001210f242000c03614001400c0e1312414503c88099000945107803614a5500e1034601a46075a01c5003d440b0f518001298a0341c02d6900030b11008008082008850134950f0750cc4100c1601d803e002e0200301d110b0302c1c030b519080341054420b60305215a000018443d8002d00c540c09010340600000c0740c01120071428188142011030414031507000218007400000c0b62841d0a10001000c0b1040314100ca641444103600384400344102070140c0f90000d600d801c2c46541070b11000c605510f58002e01100443c15030800902000f00801074001e1401c0343d11546400d08103036200c000b080f00fa681e02c0c1548030005100c000c1c0c03e0f201c61400030201652007481000004403581e200d150081c0660041310243d84542620f08020a0f41c180548442c180420305000080c0c181055600d41e003a805181e50060300d080ca00f40710190159440303600c08901104451000c02030107a2070702e8402d407a090f8010400e40424601f40c10707032091500900880d4800d00d079507000780c00e03107039107800401c4101180981154214483c0880307030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 9994593 1250 9993343 9993349
    0x1309050f07031704080709050703020c0703030207060201051008061302060f040306060f0501031808030901060b0d090302010507030501060f0309050c0d0f05010b0f0a03061e050106050c10020703050403020105070c05 94
    0x25812848030001030a00e00e4254100390403829942e2042c1140c0c440100001c00c400c583c041000345c1174903801e54000c281921140c000300c02a0080300c0070307242c00e4014110000201500007402d202107410b075030000c0c410ad03601c8400c13088032807a44c8d01c5010281d030460000221050307807035203112482e9032005043c3c0d030034805184140c140075007242d0011130701c040d81e83c2070030301020000681110043c04240783c203110175100f40d42030300e8816070300c0c4200502140011012401884080d088400909a06140301d030715400004c8100c03010348481c40f070640140d407a003004581c0152180c082c1034166212615962440d0b54030362000c400170282c0941c2643e4034020320f080c07902203076104030b0a0f26070107015440c0402e014245080031421550000d001d588101c444040813606500c40f031042008691f0450000506082d0113180084203403080303e54060b43d145444008500c803500240540301c0e00303842d4002c4511b60240014030b04102c0c8a401e0000c0e002c24400d010810056224100800d0040d21801c0c8140b00f00b0380d21804 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 9995843 1250 9994593 9994603
    0x160804060f060603020d1d0a0308090705060f03060108060102070803040b0703140c0102130b0304022407020d20010905060304080a090807031a1315020f0c0303010f060207060504060806130905 84
    0x1001001940010302620301c000e06e070180e981c0c4012036100b80e20009003414007a0303071b1300c03170b41d2603402170510200c00005a2815800e100110003080040c1881c0d5888041024285c4036520071501140411160307408141ca40d40f0024450342501c0708080113600c0c3c1420074071340c4e01194010400c101d0030071a500007002c0071104140c0c06000f0328520740e00003585904c0d031503d10110b034010a03004028034800500410001d661416100003403c042c6c890700217003d0810034142c1c90584038010001e500421154140410844010940b07143c101c0703041100034840103203c0044418042c2d5102d02680407400b807000c20081101c02d002481903507010b060480a040d80e0700801401c00045034010380302801c0c0004282e42c103400e102c01700c0307512940d02c04680100c143c0c2965a14580c101691852240580c04600315511200c0790088800d40080801142e80b207607590401600d503076685004030401030003041c600246180c054801c0d14140d0300c181d10707980c0c0e86d42c0c1c0e00407d000340854060388459007561294407080102c0d000b400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 9997093 1250 9995843 9995849
    0x2030708030c07080d08060f0604150e0f030304030b0c03070905030f0304060807090302030d0809030409020d0213170601171908030f011a040501180803041805060108160804060f06 79
    0x61900d03480c2003680302d400d2155030b5010a84c03a81001e0b00c1021745d50392000c8625401607084814082042d810000b08041d030107203803c040c03c85005203000d80741c103a810003255000e07e60f007213030010103c0d0122018103440e401036100090003e01101c0c04240c8880e240c0380515407100e01031400b04801540c0e000047e28108041001d270b65140c000040c288800345d07111300c205d41e000d0b54a0412000c650700d581c0c08030b980d54000602c0341c001c000201001c211541801d000311802409841070075501c0f40c0710711801c035009600010705000381040204000a44400042010600c0401040900102d07881e2880f901c1c0c650074034080c0c150450003440c0145600c05004d6a602c02c0f441c1c040c03d13020746c4928000285502c40c83c8180c004c460741e5000720060b8594881e5103022070301601d80a01e0304101c1c0c038900802e050208080350700001060300001c031300170450304e1601c2900c0d07080c2c480c0c20805001c0d90f01c44600640301c04109842c4c0c900302c5c102590030303441c06602442d0045d4015105240c009441501c0002c48421619550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 9998343 1250 9997093 9997109
    0xa0602160501060e01030c051002010b030d02010605010921080a0302090603070507110102070e01060f02030c03040e04031209080304060207020102190311100516080705040803030108061b0909060616020307 90
    0x6100c0d001880707000d1044001422001d80200043d506607201d00209031540c0c86040d110740002022000b54034401c0d08400c05035903024040b030380a44003a50002c2c0c0a020b036405514002145280e0014240c0825682c820f264003031010902030015980d00c2b20309655110a0300201410707000c000c0150180c660713000944c03042d5460b40e200d903144c0c0c04515200301101c040021503411544180400c0c0b00d00000440f5060440720581045000342400c5581a4114083c6104100450001260000e44150041c0495100314172942d04c41c5011405000a5421500b107a03a000c4c040020a1000500088055000b03050396401401152002c05049181030741420444104900044400c4c503482e075104004c210301103101c441e004081c4841c0c40e007480f000d441d40c145104944104101c41c0080f51689002c1c500316000b034003120b429a40d503580c49a840594601e82510902126000210107403548000300094943d01c0400401038081c40d01e030744040004a030860f4056107500d00000c00554010398041203064010901d40b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 9999593 1250 9998343 9998377
    0x50d120504030812041e0b0f06030f07090219050a090506031306020c0d02012706090201230301140d05030a03051504020a0c0203010b0901051804050a08030a0207021e0a060309050a0602 81
    0x10740b6111600c5400044100401b1204211000000b10800c0501d6030000c40c20110650030303a0780c0e50001e860040c1d00c089464160040343c4001c51000101c0c1c0041c03c020b002540302d000c0d044207140d01144e0074496502d03101c0001c1c00700c503000c3c0140c0c40d00c1002140c20050300300e08104485d040351240c9040360300204556031544d0090804180c030310740a026404a090300e0380700340c41c2c0d54042c3c40440c03005100711110003081c05942e98450001c680c044c0034564400d6202a21445a4504440c01c0403a60751003806140f0407094a0074880034140f50280001c08031aa10130b01030350601210701800d90141c00d01400c80c49004040100407580e5444038409400c07800000c0d031701c000551816005050844503880c4442d80128100d800502c1261100001c04a581c03011500c0d1580990742c50038480d051232058072000b8002d0600000b440b000741665005408844c0c021192200c40b1405078660100c84ac280e10b131110b4008031445000c01156009611036000b850181d01960503501182d640c450032a4880b001c0c2c2040c0e2505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 10000843 1250 9999593 9999601
    0x90614070201020909060307050a030206030405010f020a050304110904170d0f0c0201061e0803040512100504030903110a0e0109090c1e0e09010e0303010b0306030307141f06050d120504030812 84
    0x40c45c96a40018054010308a56828400401c1ea401c4070340c00060f025890000204040010035440b02c084d16000c6c6a085440e080c5402009210748e1007510290348103407100c5c030381030403030f140417004240160351000c500c94480340b0301322015003140c02907202001c509a0f80c9041000b141c0c0d4900036410000340030750001a0090130541041d22440182d00c3c0f07400b84011880042c820b51100004560540f841151950091032942e00c5082c0741c260750100a107034003400c0c13805000c00c05801000500540e4420300500395480461014000401c3c5244070703d070003c62046004110040640d80100d5042d8000d11035400140d480742d035140d00d81140310302d0b07080b004990000e01b000b040e117005140c1c0c2c0d08500c82030002d02c144038980c104281e03640818000c01092240000202d20f09039800c00c2104c0c2d6840d408802154081c00449046844a10b6041c6580c403459011a030400315260b184181c41c2901e00040c05a521040982c0324203864802c2c50f60590107110703040001001013101c000c05061080b9418010000901d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 10002093 1250 10000843 10000849
    0x1508030316050301030c05010516150906050a0c02060103030305060109170303070e15070809011101050a09050609010b0901120305120f06040c030203040201022a0607060e1608030a030906140702010209 88
    0x84101c0a200c01c00c1010320040c00040e1407144100c00310f8009107040c42d11000942a2660001414640180b50224080c0c1e4070300c3d59a11904041d0429010b10410841d554441d81e80f14251201c4d03841020050f0050001800064040c0c3e0003e50000018584480c0060300d40300144a11501c16514050951010041102480e80700225020080c01941c0c0103500001c1c140c160451070141940041280c5800b007203611f9aa40310f0100f40d01c0c007801d100000d000c00d00b040385c10b01000340a00441a241402102d000800c0100f05001d03070003803410041e1074540710340e207442140c80c14034444420440070400c04000c5130f4040b4961002c043d0040310550612902406c0480c01c010480303680b101d80344203050041c010400944e80204400b01e15000c1c00c9003950700c1010569481000010407a88141d0040010403400306002c03859010002207180790040f06c480c203d120b5440c0041309807501c11007406600810868500520030782010302100d101c1c0201041c50b000c042c4d20b6401c1030404403041001070b035001c41c0140e103520b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 10003343 1250 10002093 10002121
    0xb16020306071e0f05070c03060b100311070f06020c01090c0807150806060702030703060608010f20030103020d0c050904080901031409070501030c020319080412020309011b02010315080303 83
    0x12465040540d0400148143c00d16481c210b0120b41050000015004143d03e0041c421a40300e164041046008280c81c0c1c50180001c1c00c8c010000360140e0301038510343d4906402881100b00440066022a04042c09660307520040d443c10701e000c0781c05035024000c13405982c40034040c55503124400c1200510381070504a00d42d1400030306500107140c001b9260b1004d01109d800980e0960480d8080d030f40e6664642c2e02c2e001003860202c1c15031000b440380e460008005040300741980001c1007000c508a041c044022208500c41003501074042c518013059080004000600c0c0c903182b5543c8592041b01159501e50f92030f03001070101a02201e00784d0302c44200054683d0b0b2581e00d44070b403205110042000d42c42c0b070f0500d001825981c030883c0c02803606059890b4403081d005070080040d901200911082c000d910720620400901f044000d82e804c480350600304888400480c0003100f40c3c0c00c1d400060f5105220074040b140341d8401d0001070081030f41895521540c0d2942054940c90400261030080021966414181c075100c0890f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 10004593 1250 10003343 10003351
    0x2906070c0308090108070c08070b04080909010612060602031206090402010c050109060c030513030e1c08040b091503041703060a0e16020c01090302030309090408090d060906050109060608060907090b16020306 91
    0x803105140c2103002502c880151080540c00c02a0100240c0c0c90707233494102403080710100c661114203000001200b0343d03c00e89049100d050000280442c0e81d0340ca8bc16680e90081035151142111580000343c41c0741801625198000d00525007400190032941b01e89084401c1c031002610b1040c1c440400c01d0742d850b018051180c01801040c590b00190580e0b40380107010203086810306100790002d0480d40d191049135020740c07045680020501e640d0325034507090146281e00c07900303200380620400300d60701c002e40c007004050b64821034100e0002140f4018104030b440a99000802c1c1507400380e04214042a1009c2c012641881640d548030407e038880b0030300c880a45444034404e0b2181c100a1220018401030f1004020340717040103800c1d2418034003500c1e10b10300500035009600d40fa0b034000b068041d50400703004168000181040c0240c004000d43d0f602c0354411020307140c01c0c1c02210041402c9201244460500c182d40315400b081e01e2818004540d01c0d804080307215841448094418010a00040300358034003030001e1504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 10005843 1250 10004593 10004597
    0x506010c0203100915020c0a02090a05010308030a0b0a0e010605070b0a020310050405060604030f080706050705040f05010c0c0e0112060b0301020c1203090114010e09010b042906070c030809010807 86
    0x240940315030019548401074a9100071140d120b0340e0b04010041901805180c0d000b00a50964480f840c00a1860f0b843d4042c080c1a403041010102003802c6a09030300c0380307605a80c0c0000d401407942d44c88040840c0035000c5201e010307810002515001030210101c480c20345c003904007070b59059900d10141c10028520030020b0000c082d258410001d001c4100c00c1e405001045030015a400704541c0d84010000d901b500403a0f01c082c141c801140105001c10031080300801401e88a04000c00180e1140c9004480078000c0740901e5118442c080d1040c005507004544800c880c40c0b0581e02c2d00c001944450003804103c00c02c7c9d0200071400074103c0c0c55010041c4601680600e110141e00031418010543e1001e5030383c4200000d02c054030900040881c42d804829041250032040f81d503902415540d503040c41307480801081320010555403030300308500014175090082c09061466030300e0b541104480142d5443d903c1d0308030440d0320b502c4801080304800254241c01e0132401140214076683c0c50710000c400160102c0c40043c03840b42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 10007093 1250 10005843 10005857
    0x80106021c02030d0f1107080a02190506060d0f060c03050a0b1203040306020c120a0e040609091101052101080a0302070605031b03070507060f0501060f020a0213020a0203070804150201050601 84
    0xa0701507000081c0c40c1004003809000c1500b11201202c1c0004003070b10b003201082c00c000080c0d17a00a00096800401c1d042c02c483c4d088614000d07a03040805081a5528402170141e0030100c0400c10030b00d030108034080814080e410810442c030b050365580c0105c61f1952111700100b52102c0070844065081e10403000440030555542a0307040e0b954448035101c1c8100c2c0030080c0388580c0810418800801040b001d018400c9018945980e0098070f540035091f603402141d5140304900381800403807140010700030905100c0e8481e009001107180c05005561541000803881c4004100f85084841010369210301d80c000d0413054003800f074200440c2802410100300740c01c0f0360107000c002c0040c01120399002d20300700c0340010700d01403268481d201d1103002c55041c0b0603c07401030582d81c20450b83c2105c0c0700d203039031109040f1101600d074100c48150a6200341d8444c501420041d500016440e00c04c11300c038101d5002400098100c0c41964a030802c240d50f0003a03d03030059081140c3c62960042c40340c8000360241724103904841d003400c21070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 10008343 1250 10007093 10007143
    0x219090503060a02070c090e0109080d02090a150c0609050316140601081c050702010e0a090e010f0b06070201030b031e0f010b01021605120703020915090606030403020a02012105040308010602 84
    0x1800d110092051f5035600e9039036040c11198180c00e40c440c50001c0e50043c4d0041c1d0780c000c00010003029410604202d03114154035400014600c24480950f05000029160320300d03003221640780c9200810140105440d680010042d407001204101121402e0a20508841e40301c003141d076100c0d82c548641604901c05d56802081691450f0039819500b08042c1100d240c095a41e020501c012150501801d505035002a00720801007035a41a507080802c04500401c0200031171110139544400b074405180c0810b412020401410b005544260000ca5101c0009012030344080604880d00805040c04078886034550440c0142d0314140400f8011010201e400f48010080801e40d4201007040e007545200e0b55108135148030840b00788000031f2102000443c1c00424140303282c40c2000c1c511200414130940541300b00c0d500c1000685603e004402e41e0b0103160564000d14401050b41c0c019521032149501600c8503501000603102c0130740c19030041c14404e5200b41c1c0c03421986d514040010b0301e002000d280ca000928a0303207690b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 10009593 1250 10008343 10008353
    0x40503121c020a0503010302121203060d020604030f05010207140c030303010504091401060906060906020a08041203120e030a0314040213021e0c0a03090e09030301030b0a0219090503060a0207 84
    0x1284a41a034200309554910040c00d003484504440c034002007407540041100e03158581c201001c1e5049030300030740f10700c3d902e04e6000811070f85440645690694101c0d060012584604215404101c450300c05019645865120b840d40c0c15100160700046a15a40005071141008040000000c01047c400010003080201000090300ca000500a460103256520030b2281400000010796404040d890300805c4440e0b2030300c1c1081c000c2d007070500407170001c649950000552180300080c003030612078000c41a6400c01e82864403020b464230140d1815400c0002e0303600750310740305031a078455010700450800086598081454000d010b0f00e558140003a82c40d0711725010000940c60b030380d02042030403201c602c0040c0e0b00c407682c03100b070201c010318a21144642c0034003284040f4408000600912030701e000341c482c080329a40d58900030111600803200390026402c14001000003920561402c4d07000450703042d0145c24820003100042c030704204100000f00007414075404101a050510859800030303100340003075240020b41d84803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 10010843 1250 10009593 10009603
    0x90b0a020c0a09051e0f010b030c040e04030c020406060f020c12070315090b060a06080604050405070b07050303090105010b03070507120903060e060601030501140315090c030607050a02011803090b1803060109061a040503 96
    0xd50148c904000002500400100c0072180500f443c0401c4880d00d0a0600700104040f81441089002d68038160001c1400d9011b0021080e07112500e07802010034491490602618200c025582c1c02d491092100110010305408504009882c078040002007440303042c20310b41c10200e006000603004002c8541c00340889035120312155481402500d01140c60f44451074281e260007a55880702a0102d800304403941004000310095014110000090003e0b903219140400c03644001c0e240c107004a01d003041801c00099481c20f50003201e014604103a01c00710354a45804060328440d1804841b50340285042020568140c8a128094505418001c000810780401300e5a0b80c0184280e1754107080340c000c006401080b0030440c04102000103001e4600d14140603030b0141c20b03904080303140740155003000780a11150031110b01d01d141c940c1d0903a03200e016180ca00003181506600004600c2e90304843d0042000881d1010003100d4001c20710700e4030010f00c1c00e1400f18801601240442e0501c105502040200030304c0d900024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 10012093 1250 10010843 10010849
    0x80c030a020c0f030301090b03060114090f070302040f06171303050912070b0a0e01090806090a080d0e1203011a03060a030809010c06090515070302030403090b0a020c0a09051e0f01 79
    0x40142e42e10040407115140001e0380c440410540f200000100d0ba081c2590021b05104000b6811100c0c00d0341c07501121a0f0243c1d503000042d401c608803c00081100720310409403030300100701e4100180b81c651900b40084604449801c044041458905184400c1c0303540c10400750303c0600c440b01103601180d9594014600e1141000321441928080d0032180f1070b050901a50006006842041d5034911302c0c0d40002c0c02260301034014078045200d080e40001c1c0107001203202c910462111005d05902ca1f180e035141d07a05d0390030100c0001200c03a62030081c00c600c52003c020004030614031284158032989001c04120311410801c0c0c45102e10034040c010700c10907482c0c2401c403030292580948595150f420701c8004990f15046410090302c0d440c00c02d10481c0070711502140c10352031040042803402c40c9039615031040c1c09a12003510020000b51150f8020044880000040c005590a610643ea1a15540e01c001500c80c1926003101d000651b43d402030191440514144580f1303008a00f55138001c91911034120001000144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 10013343 1250 10012093 10012111
    0x10e070e13020f160204062403020d11030405150105220504060b0d060f0605010302030402010503070c02190e01080c030106080a03081009050903070203010b010806030a15090c06020a060c080c03 85
    0x1414030000c00c5460301503443d0000002e40503a101c422015081041200c1c0c090241d016500e044c50220741c180003558400d81c450340c0c40a510800390b40101e403c40003580104400c0300443c1d1b0300e603419030040c07098000850065008100810f40180e1200d040c0c1102181030b40000d110700000320841c96a02d08181c0c440c50300c11608400002e8594076801d2620250140380d03040fa030300c40c1c00042c0030420098540c3c040d05418404140c2081140d8407400150102d10060314064003180c400e100180046120700d9020030300d02d10180159401802406842d0081c07075554001541c0d40e9103d000610294504001c3c03022010b0088000b4000c0300d2030240c41e1515000c1c0c0d01e00250421812000084042c050010072038002c05e29a44104045d1134009011926a04401c10492027035080c0620300310958030994105000c0e240040c040d0401a5041ea0f8140000100b00c1c4c4445c4020744990303243e40450307d2080084000c003030903005446413203046e01d028000c07108800c003102e081c42000e8043c054084010b10540f41d002c045a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 10014593 1250 10013343 10013359
    0x801050115110709110a02010506010309080301030204020306040f11040305010e0c06030412021908030618190b01020109080406030b030610030309060806010c0f0305090a090501050306040f0309090c02060708010e070e 95
    0x810b0142030146607005040710500344018000800501801800c0c00c40a5034003c0105454100044041c1c40a0751006480050144018005403515070b00641d081a002003001886070444903500b41500c001380f51000c1e401201190804c00d01000b0702034207401400f00f00180000e1004000014658040075002130854048000340c981007d00810108078501c104411044848103280703003c136810380c412101035004032840e000e106c405060010710340d401002c0a418450690801140f5032005200300500b1034115074035000c04d00c1c0030442442c000c1c0b02400107950042074074003006050620b462005007559061410f051010400b007a0310000c1d0106484081c5410152500d807640100c0d884800c910016005829804c170b035004050b048001882403a60940e44500b0481d9258200411036109100c1d064254019000007000100c43c2d100e5a2003003446410041001900c600b00d60b02101c0045500d00e0160303101c3d9050229a58101420b540100341c003005120740751821000c002c0040c0400d5600320300460322 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 10015843 1250 10014593 10014617
    0xb06040806070f1106091606030519020a02030909010e041110020309010c0c0302030114060901090b0f090703140f06010e0a050d030e060c01020d02070c0b09060711040f0204080102090a0801050115 86
    0xc5203102e44001c0a804c011540c0e170f810078030342c01503c4d64400e4060700504e01c14041e001800300d0080c02014803404018056466078450f4020366070196209074021011400f003003011345420364407041c00601800501c406100c141c5440d00d8541c41c452440016940314a1803040304a4107698000100c8074528000e02e052080d600283c03814524041103900020b41c1542814514000082c0c01c00ca6030b44144821a03205401d643e1f613000807000c0f5904107001030f810018400408001d4281243d8450300000c1c0d519000400c1c204070880b407028580e0694101ca044246003050118569001c000c2030f03c000d40489020100c1440c201c009138945020380401000e2090081c0044400d0ba034110a95010102080082d55a520a0304848000358424482203c180480e4000452100143c01c140e910f00c6101404061404042da10340900c5c0480c0030b0121a80140c07a003c00c840409901d0024000505804001507203d00b0204100040c940032504000e20b2603150070010082c2c00e0490b030400070203d10130b0502846050b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 10017093 1250 10015843 10015847
    0x12020103110f070302011a010212032512060605030c09010309061d1e010203040506060d1b09020a11010b0307060c02030a0b0903041a1204060e01020c160503010b06040806070f 77
    0x110780d480c07980c40c1140128041c142c50450000801c08244a40c1c004c0103800c1880801504001881d0102801a0f2180082c3c801081041c0000c3d90041d60f00d900452402c0000d0500c009010740d4441e5240006400c40050710800c1e2050203800083e05c081d00f4405c3c1580f621220702e0b000c7e4024840028100b54070366052000b0f200e9035034000001a10701d40358040f1040401c0008541d40c201e81c2c4030315001a00800032005040006200352401036900a0180400e603c8400410448a40c0c1900c1504e124010b0b900d00b050403245c88112030014040b2110140e2a03c0c10818050411141c0f0501d4042d41d90400311005810742d00441c060040c0ca030141005820f002c41400420318001c90380000a0562001e401404010180000680104c48948240211201440e043d50407180030384485ca021b60311407800420300158090700301a2924001e0400107040c1941c1c9400280307001c604050741460701180a6081c040c40c1002e00031045011000d42d4524540b52401c843c465880038001d180c0c400700b1403001c4000e40c60794 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 10018343 1250 10017093 10017101
    0x6120109140114130224130b040501020c010c08030103060e07090615030b01020102130302010503130f06020c0609070303080106050f0c060a0605030f0d140904060b0408100518060a05070306050d030905030f0106050a12020103 98
    0x540281f40044800d0f4a403052070742c00798414000d01c1c1c054864500180f10300e600c41c00c1d00b031034050781c0900c6a86c1144d2850340c860f00030385168120050f050082001c04103a60300c4c9889104007c14190311030700b04400986074090308542504080b02e0459004224104442c0c000ca09000300b1a58280381956507581c40e4082c40982c0640244020b00b62084070440809201098018001240d580c00c107031113a6840e00c08401d40d45003010310000f004038203c100108099401800540030009600c000c00703240900a82c1d60504081c01225030f80021a542c907002c3c8400c1c141040100041014400140000500400007401200903c071120000500005110f4065210381c0c01c4400281003810100d0f03141c03078036441c0498480b0762001025610034604800201c2d4003010808484800d2407060181c54103031505c044400240070300901c1c0c0b800341a00c901000030540c135080100100c1d0b50283d502d4812007403c1c40205801c102000d1030940c80b80c0e0400d2414070440d80e8000d0720704211444e80902d01d414130399502c01078004d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 10019593 1250 10018343 10018357
    0x9070f09050d0308010305070902070c030b04081303031805040509071a1207020d080901050601080601030e010902100f110303090316050708030307120b0108090606120109140114130224 81
    0x20403180d6290b04140d08207810b00c1c10b89108000780d0b05042d0b11b90114a040b07004200c4090107611410706d042000ca0400d600142e001401125841e140142908880d106102940e104500140e60420000000d4045d43c0020000d08401c580a000d01c1c02e142201c0d44e6200014001c9920032006402404a060310f40411124031520345d101030b0072145040d10000c1d440b44a968401c00118000d000054020481840341d0351003003805850300e40d0141c8030a40114010134514038000d81c0fa40d699101c003000359440345004079641c803096440d2215542240b41c018a9091030700d2b2010f100b58400d1051100b815004010358818101e800500340c141c000c5805c3c228a00580303680030312042d010000a2001c120b40c81041c400e0807503143c2809010310b4800c40c0045410309021184803902e41c00913800f00e00d0b103143c20b074481035a844c41139001040c24070141c0c0700c00c01c00042c04140e640700c503959409c2c4149a0406018a2030740310800c90407400c448149600030940d10b030200700030b5814126018000c004000001130580d549 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 10020843 1250 10019593 10019599
    0x15010e030a03050a02100603020d0b180106081b06130506090a090c020102041403060405070e091e03090907020607020309060a030e0f0703030305010503072304090b07030204060306060e09070f0905 86
    0x10800741400c0260541e88801d441c2001801142c038803001207040f50145104032940601108040e1046071183c608100340581a81040d41c640031600c540001d0900504014110500142c0814003403000107450740380c0c442c103a640c050301c0b0038001c1442001051502030101e43c02514290307034276401d07900012012505a04080a1103181849800b4050b0b0b055010b0000c0c1d82c81056040c1c540e00030300c410150f0300c1100301da0041c1035621941c028040d0b1000c00d0b04542d08040c0307120481d1044442400c3d810222142c1c00c104085c60390011500d11800c1c680b0004494000f06a40050403070f5091400d0300940700d100307400f0102e0148500207403210a8034803aa000d604035100e05c1080d1205d4070031085005480700e01c54030064002a08000002c5a98039001c10240c088a562400f50089500400004c51070034542107015075125649000c1c041c0130441c02d0740e00e1441403141360b40050784c40e8240200541220099007250741001203d140b0307103240d41c4403001840e400420904045400d0740c1b03c2d25007158500e46a80005170 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 10022093 1250 10020843 10020853
    0x6030a0203030406080105090c030114120c0d030c0b010515040b03090c120c010210020f0901030b04060f0609080609120d0f06030804060201020a0219030509010809030403020405010b0c010c030b010815010e03 91
    0x70300d545d07000c00310038181c0f8403c4401c6442a101c51141c405d0740c2c04203000c0e610550003096034400d090300c4c0c1424000007150081c004da075440c034440c200045204041c501c040d800f04031b042e9001c000304114a0502da02403d82210760108104500400000c140564000e4648040001005c12410102005030782040310000300011880c40e080b0304d001e42c68111400e15280584210000d04101600324020307166203001c1c50083d01d05101600300118050102d4409444d081a95802e000c62001c0e03000100b840504026100c00c3c2c4a145072103900d51510000402e4010103401c20001100611488400c940244901d1040840c00c03d401d00b42880c010206544010300c4c251000a0014001d80c040d00039044031000c58080d41c407098440e62405a40140c00000200020401c00c8260303000d40c018010301e90401401c0044906282d280d07400324040314400c0c0c0000401391320116180000e00b0090240d0034030050a8070701440401016070010b42800806480e0b000284a000040700007a407062200e03450745038000301100c3d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 10023343 1250 10022093 10022099
    0x50409020a1e0806031c030204091802030d0201050402090408030408090307081b01080f0406050903041e03020a0602030a08060603090a06050a020405040c0513060e01050409090b0106020105100e040b06030a02030304 94
    0x1400d41e5801903041c401d4402860704000506010f800b90740d200303140c09405400c9180c12510b8108024408031800003d140d0b080c0404030799104070780b0840750001c01480f142c4559110174010035142c42c8540300401c085a04100c00c000042c0c5030b2640740c0c0d42040d40f0180381c81c1c80c1c8d100c030311b0701c07584c2d40c0181301542d505441101e01c0081c060000140001c49000040312200c2a0420b43c001142c00e000200d2b6003007801c2101b8004140014600d0b070189a02003071120541e0704282e1140000c40d40342841020a1004064940d014001d62030310001071070040026000840c94950418005405414010300c454032079500400000d40e220400d104030750701280d0020b8100a03504c0c0443c0b04900039045400750500551600d0754220003540110111032009011402a2680f40e00d410011100c0f07098407108181000014400047c101d201030160300742342da21480b000c41081d818040b0080c00c5400052240e60b6002c001941008000c55104000ba00550480c0e1407540965601c800f29141c031114180094051100107800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 10024593 1250 10023343 10023347
    0x302060d05010f050a03080403080c0f0d020304080106090b01020604020f03010b0d0f120201060303050d0504110913060b0103020306060f0f0f040e04150504020609040504050a14070501030506190312050409020a 92
    0xca07050300d07400b0341d0301c1c540c83d901c80040c00304200b503600005086040c108010310208050801034081140c190b03007104c0b00c0b81d801c45072160501000103544405a0302c041070a0091040a000e040c028184450042012281c1c81000039031343d030700c0540064024118010500741ca601c00303410001c0044400b0301b0242c520700a034985912501403460007600c032001540080030b2081e20600a45080700d0f0140d48250400d404101c49400601c0d000d001156100f03e40110070a147d1246c21000d071040c403280702c900149000c2e80c10010141e03640745036030741e04040c410000c0004079030b81c01d0280c81092600f91300f819220311003051200018440c41800c00d80103131002c90700003411255150944c2c0725500c1220048bc049003034941070340981c0c00c00c0c1c0380290301020a000010080c20306a00c101e60050040c412904001d1554443d481441042c8281e0101908401c500344004e58050007010b0b0003803001c1d50860340c3c04100107940480d800c19800000c2ca03415221400c459036074442c00a90f03000d4184004219680c2c4034107040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 10025843 1250 10024593 10024601
    0x15020412050115030f08030915010306020a02010b04090201080703110f0412021201020703050f07080909090708010e060f040305030910141005010309020f2812050705030a03051606060302060d 84
    0x104640760740c284004071819003582018401102e03400081e0000100e440d40e61404540c0009058004600c21b5009147e221442c1e00c03991802036018160050359400390040080c25524086a558065818041c403100181d074080b01140c2c2c8036205140006201c240032808940c42e02c100c0c040700e40c81d5400840c5c00b107284000c0c00c0602c80d41901c201d5a001100b62044041401c0c0c1c0140c04001d008030b001401070720503241ca4840100542807003081d0b0f440c580182000064001d210503140c0c1450384c0d000820030b10107407030309204449580c0c200d04020181c5242c11802c0040a0304024801002c010780031011528220040014141c000b00d846070503c80c0f10003c80160b0b03458102259104803000e120040003c141d4000c0c4144001da903000b5040500c8a4286028000d02c6460040d0301038002c80c503400c1b0350050b4a091042480588000000c11001c80e000e03040c520b01e00103990b00003038030940101c1031100c00250000116164072000c60042940300c00c041c1003903401400e41e58806504040c0005140b480c507a02a40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 10027093 1250 10025843 10025879
    0x504050114040507080f060f040b03150108010b1c020d050a0206070f0c0603060b0a03050907170709050114060403140312070809060115020a060b0406050301020a05040905060427150204 81
    0x2e01041680e0710070300d040301c0e40082074030540c0e0000b0500c40442c03050b040c100303145100000c5c083c0c00444c81d4010300020a10344090b607171040c404c84d0700c50700050020350000c1c0102900341d50700700e81d00e612030407005244101c0f1a140d40f034000e114401031400841044010b0041e00740041e0000d19640d1102d555060524101b03180000403108040001408030312140a440340340103954035415241e0800745640382c240c000380409020341c50315100303100c0001805140705110511028808001c0d100306850410040d05550040c0c000c142070302c00001c050841516583d055408580e000740c0e1300e21000200c8140342c1c3c218840d01609240250700c2e5001c100d041d5400400050003503506d20100c03102030380d035100c034808158000c21503d00140c0081441d500814420b401042c1c1c0e400008000107174855603040081c1c00c9900440404000c5140403508000781d490030711403990b00610944040c49040e18099000161101511000e508515014400f109200f40e80000d1440c3d0600160f007150fa9580380ea00e80241150740d14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 10028343 1250 10027093 10027099
    0x3050f0606040c090302040e0c1005070605060604030b0f0403050408160e070905060f090f040e010507090f05090a020711040501030b060f03070b04060f021002030403050423100e06040504050114 85
    0x40210702281042d2140c240700724081e40d96024401c0c15036007008050081000050080d124452a0070384558510041c00c02e0080951600c0b0743ea16107074602003080e40c40013031a080c07043d1800e00c0f0400106112a44440d44141500d0401136030f5543c1c0d140039281030060790071158091007400d942a00e807400841881069039402e410540b80e07690b85150854010002e4010300e5007002c014000003101144190151030385400091070a41c1e5048190042011200c00d4452141140e4441d8241302c00d60b5000031086000e0310455288540c45402c0c42d010400080e4043d12861800e81d002030325000340305442c0649100a00020414000b030b59603402c1054007560304dd5030306403148a05544511044c5800a0b800081340d00403803184d418680307071103c15a041e10041d6400390a41c0583d140159019210f4401144224460344404c0d071200d00708117800c45206440084e1030134188000000341c140c0da9803422132001080141c0b038520f00d2a00c00d000072551350300450340a030f9081402c2100210b014041840407101c541c03019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 10029593 1250 10028343 10028353
    0x40c0302040b0616080a170405060403140c0a08030a0902090901090b0a150306050606040302060705010c12020f09040504020a05040e0f010b01051e09032103040215090f060904060f03050f 82
    0x200030040d091140d10b8010131402c4e100c649560000d42034001800d68801035007020012a00150100c007025074040720200d549402c41d404100800d07400600b1003190620207800a400d2040e103c840c40e654102c001c40c0a0495000400024201800c40d000b40c850158080e19107070550801d02c00a9019080c1c0c500105c92504929000540e00070f90361160154040103d0303550f220031451522618001e00010781455041501080301002580b03800b80180002031107080000b800c43d10500c002402d01e01001c0e01050880c1c01000100500e181490603140340180c12034000800380c48903c00034190941e10350100d0f802506107401c504a0210100c0d1101d516102c040080c80403001d983c0c011038451059201c41041e20030072000d4004511742100142020308005401c9802c0c6001c50301240d01c5c140001811070106030000004c003c210305044032401c01c5400e6a40c541405d04008000003020700180850305801802d001c1610900b40e9141d800c808003c0400c0d181c80503145449040180c0c64211000c2c18a1031840380c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 10030843 1250 10029593 10029611
    0xf02010c02031e0903010f020708041a040b071209090c020a03030609180b0a02070f120f0c0506060607050703080c03040512070503070e07020f0d0905010f0302122805040c030204 78
    0x8401c64002e8003420030f65035901000c02d41003e10380d400101502d9091343d0381d202d00b030741c2a44007440180b42150107803030026107403490320400040303140c189032442403c0402407008100d8221030307009031192658000701014840f10456011103501316a5400b1502141c10484400c1540d500840c600729110702070340d030034000740351180c1039501502d2031680a900505180c01d0445c010942030b82d82249c1044100c44007502d13019192311001e0902125080940b008401d0900401219030000c20030b4503446880d0030810f40b4891035480c4c40e912070000400d6130b80948800144541005000e0007020040d40d401114507850740d27080841d0340e039a0380050050a0003a601d8080e84589032600107040c604031200200100119401e0200312020881e0140885003944a041c2046400382800d01002c14a400e0701e03a164003500e840c0c240014a2a2491400ca6091510401801c00e4a0714288602d541c01481c4c290302d00c1440c1c410b5086511124070490342040b080c3d192200f4002081a6500c0c00030450b0b008803018050082 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 10032093 1250 10030843 10030847
    0xe100f030203070306020a020a1506050901060e030615010c020909010b0f01090b1c060b0c2506080c13080d0203090310050702031206040609020a021e01050601120207081303030f02010c 81
    0x255000196150303002030b10420001348140c0081603c84e105d0300c16109050100c0d50f4240d8602c000c0c2c0c00c900d0546466600c14041402d01102d603500402c0513161440d00d079203405020070740f525000341080b0802c000d0110f00d55100d900030603940080690107804100b8500d86004070500038406091043e126001c1c8044092903076100744250000d540c84900414074184015040b200da0000d03030501188900d48603103000407020298000350101282c2100900002000c021880f99003007240f1103899421040741c4410322803550b00c02082d40d40010b4100140e5502d8035601102004a00385610548152140500d02102d03103a01201401042c4400e508580308040012180000c1d02ca0480751040143d0013404800349010a0124154010002920010746542c4442220f42a030b4481c1c400000540d01c0414900c1c02084410f600c28840b50301f08008202c0c508010f00020a001102c1c9621050380390081140c0c13041c4104441155091002d070741c124054560740349009003804c541c0c000581c001d5460f200740c3c0c0342128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 10033343 1250 10032093 10032119
    0x90f0506030f0c030601090f0902090a1a0405040207050f07080706140403030f05070f021203090901050d080403030c1506030c0302010206090d080a1d0105010303050702150c0312040501090209010e10 87
    0x20202c5800d0307555150303148083d003504014080c86c10041d80d09000108030940182c03440c0500040300300581c0d03a8400b80d01b880040e240552040381c50054039001c01035090b0180042d101640c404980140e501e0602c0d040a500e0300c07115000034112402030b2540000c5442c03000a0280c100d425645409207242820b100c2c61206001c0c502c40500440c01941241c80c1c010f200308010700a443c41201e01e084c03240090b8011450720301514120308866400091400078615207504000c2c01058119209c82c0820807030354818072280242e204c0101481185d8819004102d40c45841c44403074801c41d0010880941d890030f0811513110181700c2039001d40958000725000c0d00000c1450110003000e0b4407262116103904420400030407495011082489111849020003182801501d000b51300034bd0794140c54418500401520700421110004001e00422004c2c902c01c0001c0251481141c0b4000e1120b8a60740724105940940b1020100941c80503908001140107081e01408902401e10180396444c404d84804808000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 10034593 1250 10033343 10033351
    0xc08010c080115171501030b0604080d0e0a030506040803040303050604050f0105120f150108010605090403020a060f0b0301020a08090c030106030203030304060908090907091404020a1b21090f050603 87
    0x10340041c0042c0711020f1064880102143c2c1d0380380c103201c450720800444030f00c0013055030061400445400c901c065980d150040040d810401c948041c5028600345c510340c0c1e01c8000d03801040c02d210001e80a210943e807241010002550004142c0303950340f8041c94a4251b03544120307011000b003450500850741a0405100309841150a2000751215034200410806062a11403000e110792040725404800c0d1340e018000c40c40c0d00c002030035040343c0b1541420005420b4540d2504454020b205000030440403075800107040c401283c10a00001c2e00812801c2d04002a0030909503254040d8000612100e500c1e0340800200d200340c514409460310b083c13802d02054240ca0081c07102a40c990b0081c000301d40032410340d40c0031409403446507075042e1514034804080380e4a5402102c011011983d0a403042108140f2421070f0ba65100e0f04480840c80c0140e00c410140405d00d8448450071003c8401c40e6940800502401c016501c00c80c0402d804034156040702d00608440103401040c1e251400040d000940c3d091000990f030103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 10035843 1250 10034593 10034597
    0x703020c0a11150a030509060105030d080f0c070c0311180c040b0f09030a0302150f010b071101020109020910090e060402030d0503040c03020904060212070e030709090204020d02040b03040c08010c 86
    0x1400e0311500c46981c401201009154815400c0d405510b00d112500000d052a84d056140800c4524007032001c02e0901e50160f0043c1d0083c0c008102c122991640521030340e501501042414410741c5400c02c4142c031034040c004e03000b410004025008400c1c0a0900c1d40309100580440fa0b200a0071a1100c64030090301042d5400005148107006c2405460141e80180c0480381803107895908241d20440001d25050000b0819400758120b440503090702e51f5954555544600840c2c021785480d4500320a00b1010301c51141c010b03046c02081d241100c03007a8405e410000c6119001007075600307a401c004502c540d510710144501e00690740340c4a0001c0e011040070425078452138006000e0f0080400c1c0480a40749039000500844000e0800c4c03401100603642e83c5000f5000b0b90040d03e0040e103e11036101034106800025148806010808040002a1380c000034200241c4561100102e4003035843e1010502038021603083c0c545050003c903001c030b005140600958807460048171113920540c0d035034801c5030032030f020980c40d180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 10037093 1250 10035843 10035853
    0x1b031e0201060f091d06041208090d0906080c190305090c010206100909080c030a020109111903020112021201080309040b0a030b040605180a050105070f0203040b04090c0207080d0302030105090703020c 88
    0x646000ea1748414294100d2136445440c0c82c03d801c0500381010001c440864280d240c0b40124284d5030b50140d02e85034440640760040181040314100078000e85a10f100303040802c0740920006410750303002c0c2d080d96505080c0d01500c030106201d00030082c02900c0c0c211904d07500381c810142c0c0c1c482998800110140905a40c07050052111305014541000d40001c01040ea4456401c000c081f80d034250800040c00441c40f20f60000420320300c5840c0220310794144400207880b8003d240d10344002031003520440b0007100c0e42424900502040145001c0103406102d04000e100c4242e20f00006040f0404802044a843e0440d000c0000783c500700204541c119071800058004010362000900083d02c590000c0c1d04269001d031140f4080041148441c174080c0b0528045034035946a00610072850381101400c81e21558074000b540c2000d04004c0e007195a03003d28802d03140100c3d16001e40303100d040d0007402041d01900c01c0c10150380c0011801c1d840a03029600070320485005002c4000011100c5100707200340c40c02d076400000a40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 10038343 1250 10037093 10037099
    0x50a0e06030a06080607050306010905040203040b060d14070311030607080106080403050a1206030807020a080c2b0b01060c051005010501050406030b01020c040f0605010201050105180103030f1b031e0201060f 91
    0x800a41c00080014000580c2e555001c80c8603d4208989403056075150344403030b0313030b85000c00004115051982c030850085006005100004440840681d40000d041e11203100d0b503a070a06113039041a600030011407140c0604000801481001d0002400c1c2c0714050302211030302e031a01c80040361164005d1142d40005106800810006407041d0300034402d8141525103c51075030385036010f901c12143c9551040711315950020ba64001c50070150346c03401c000c0c43c00a015113903401e800b4002c00d41090040401042c80405110311010508640f10b0011440b1b400a01d00201503031070b9035000e0102c10018800b56560b01c038000d04206012590b000d014140e41c410ba5840342003a14012040e0054103c1855050640c0903802d102c0340940c651f442955505401110701140043c54500003a00711501a00118094808030260014490f9110704990441317a00d86811807000810310342c21500d20030f402c520060709500d1510074009241d0321440d010240003403030074841d2820100400c00e900729501785c400c900e42e040d8000020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 10039593 1250 10038343 10038349
    0x106020606100909110a020c010201090308010b0f07080c0303090f0d090302060a110109051b0103090b0117030c01020c070905010506090108010311030a05030f0408070f080c0d03030e030a0c12050a0e 87
    0x102c4414803941c20009411a101c4980c2d405075440396103c16100b20010802c220240d504002c2507400d4035081c0001c000020480d01c0051850005001d0b4a054050009507241425965400c0f03600d55030700500c825884100c0503505035160351007520124098861401d0901150401103000c5040002d6910b510840901c0c55084c00031a400205004061100105034121444800c2c0544104944150f000d0200c01c04004000000c98040c400340c42e0400d0700d070002c6800041c1c112049079040d1f580c00a551020f10508613109031442c4202d811080f415400030954590180000a000c815980c07c0702041c0701c50703038a90040c070005002d07441610340043e50010041011034a00c0700b13007001070742c000380035078000c80d96540f15940380d0303884000709100c046000a4100035481040c0200e0b0080c1803407010302172040c0d141403c120395400601d02020303c100c01402c0038004146c0207a100b0034550222400750ba03101c26140c14050680e0b0b01d007100a980b4641c40441010109102d8001c03920894030607201c0544600c491418 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 10040843 1250 10039593 10039609
    0x1030b061201120204020405091905070509090a090807020d14060105010305040b04031107120f060b04020702100819110703030c0e01171302030604050304060e06041d060103110415020c090106020606 87
    0x2a038000b43d003008086004c0d21400709c814070603034090000700394203011000800c086640003441c075020404c1c140605041075540000b05500001c0304400421008600c1c10103c00c00c0c07003140300095201c911104088100230b40301000c3c20a8101c09000d5554580c1c0c3c500c0154240ca000711002422700e0740c1000001c0c0041d001c0c1c1c103000c218010600441e0002c940320100003a0b45501c164040d100d80c1e52180307464080003942d009007880f10b078064400794200801c0d41d020421031048000d605043c0034410340061003050502c003120001c00d0420000b44200d07813441007480d2171580035020560000f420b0013101048280202c0d0744000310300b410795541c2e0b200d9080c0c2e2860055040c000d410454480710b12041400540e4003088814000d90142015680e1945001c801800c0f05124003032150040009000c1048200b90003100c15107100e445c3d0045801560f191001240184400c80d406508448040350101e2004003507414000030744d4541d0201ca0b0700c0030420040007000e600c06d2140100517800040040d16900f002d0302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 10042093 1250 10040843 10040879
    0x50313050a0c090b041a0108010b1b010204090219090f0b0c03040302030105070906081503030a1101020d0603060b040c0c0503030112170a020109031209151508010e010b01030b061201 80
    0x56555144540c1d50302c00d00c03801964000181c554569031036a0862505100da0000300b403030000f0204040650000181400f901445a440c440c0008264209100642c0c8128442e140f0400c00071965039031030b000890001d4000c3d07684400740c0102d032021078800c2c3e4020000031090781c800180700b0b0401c6152003103401c1d2544c40200c07600c101d40414840000182c80034040d80740541455211035100c0c50030010001c221610051951030340090300d104040d2180c07004000c80d07000743c001d40b0b000307155529150340d05030192040c0e241d040b21862404c00004203009590b4841030300032404550074400198000422640c441c101d0344007030302ea40c10400c010060b544070200042e00b424450150075408121043c50552140c019014500c0545d46900c1c861080542c800c000020150090408002c801140e031640f4421000042e644000c50b99210f485c100014041040c440040103a00b0080c400840b000c004240030b02152900c0070f010030704000b500705041ca0030300d0507070f0400000310566030310503071a141c10500c1c246400700c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 10043343 1250 10042093 10042103
    0x20a0918020903010f05010302040b0a181d0a03030504030305060a08030906070204110708030702010c050f030402010809070902040311030705040b0d0f1109040308040b060a1208030604062d0602010903050313 91
    0x420b0340c03240c40030f0045c91450310380e9840c00039007580b650040c070041d10001c0c2c04403886035407848070034000da2642e401e08130384a44000300000b99a1050880140410030103451001e0140b05581400e0304266058000501c03640c030075601030026459500c2844069030b110b000b401a150004c2c04003d8141c1481c1c0060300c0103600040000c98007000b03040c02c01241d0303400303600c3c02d51340c0c13080000411102540900600008908501e425481c10300303451040cbc2074600024200a04001c4080301107804032108101207005061007083c215a143c1e078900d04005200030f0704800500178010200000b0301c070b00c1d042c824480303808405840090f2860360780e40c41001d82501d00904603500005211100c5941e2030703050205100da0701c00d86403955907003810704203c44802c000074032a078820341c00038100f440340c013140751400c500c0799501c00c45040c0c40c0d8640c7c43c00030380a0311090300b008141880c0e40c8031a1103a5074480c0f401d15090800e45014040d0941c84c1c4104a00b66840e080e03001c0d002c61020004542240041e01380d030702040303000d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 10044593 1250 10043343 10043347
    0x60c06060e0408070c0807030c0905130203060907060201110301050105120903070c060c0201080a0504050d030207110d030305180a110907050d0c020601260a0f020105070b01030b0f010801020a091802 87
    0x11501d04921440540e0b0030f848140300455200d040190756a914000303001070318002c01080b840c541e0f4920380c5403080d00403002042d40303c40100f11000a080c4500d06010742c000c06842c07080c90b160303200c5540c5034151b110b2100190b013000c07070500d0b00c000e14204490590b84182d40303044ca08030102c0c1c0f44914110300a00001a144001c00000300403419039200b14018100b03030707940c0701d032441014000104001d0025240005080c03825062100140001a9000305030f5001c0c140541c43d0211410b0640004090042450700a09010300c890f080587c13682c8501c1c8124004d41c03243d04908a4002500d540301e0706058020007034071070003407030001616060f6180e0b07174004138502d442450f0592505194040d580289481d9000d41d0112005103c100c1500c0696100c0d01444058420b171101c0303601c91182e959485071405048881210b186505592040c0c08488000e9000f1078281c40c0e650f980d1810b803150384403c8607058000d01c40040045443c0ca0306008a621900c0b850f50754020b041c1c242070036007212001000098844943c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 10045843 1250 10044593 10044599
    0x10090c0b030c0a08010605030702071514070615120803040221011506021207020a050d03050903030403050606030607050703080402090604020c011812020109170c0109060e06070e0a050604060c0606 86
    0x380400a42c86098003014040e224001c982c400f8010030010b81241e0306100084c0200300036150700007142c404a0f0881c50090f14540201c101c1682c1072901c5130819440c12800082d4801400a903402c460956034001e807103103001e683e5403010382c58480704240c0000c0c07030040100042000361170280d030003080001d65084185a1007410840b0603084404010b4444980f1003801030410901d0340510001780382441036114607140511542c000b9401c4411805450310500c140408181410f11940c1503440c0c01c0c0700130301229503441c1c4a080c02562140e04950041c424414030000826180c4901e0a039003881ea455160416240c1390740d401c00040840c0240542d402550034000c4540424003401125669410b084441320000000d041c83c204103001e030400d010543e81000554000032300c400803141c0c212100d000c60252224004120346016002d03d01000d80781504240c10a540c00101203140e0380145950b896103100c54100a0510200311440e1146503070250040c0020414280960500312402e031003050001400c0d51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 10047093 1250 10045843 10045859
    0xc090e0c040903020105040302061015030203090a050109030914011b030302090f030601060c151506050d0f020a050a030506040b0906060d060e040803070f0201050603030306040c0c02040f05090706050301050310090c 94
    0x100708810b43c0140c6d103d40900003895014040603400000002100054a04058100d001501400c4c48101016400800601c800b581032010000e01030b03008000380b00c1c50001c1e0500911f20b06281c01025006409003181079541d6004540007501c2d104a1500b40d226428a510190b0003500605819a08031001004061761a40c0500c007860180034940c442c920031459030305200703003009181c039152869030786051a2240507040c440942c204580c4545813040d518148181c0f0708010344240200e291546001081840c00540c0140107070107070100ca55010040e0340d48140c20031054a40c00c8190640142e13410012030b00300e0508c84000e0036501810340012503011794651842c10020300c21582540d961300d01000b408642030b44401c410801006c144001d1001d8203200001948078440900180e100d1540c42c1030000070306006030783d0081403503002001000b0010500715400c014220440d8050b84500411a01060f068000c1c015a81603600207030080242c0c140d0914000c00401c403842c003c1d030740140e0343e080001d000d007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 10048343 1250 10047093 10047101
    0xe030714010c0207080303040203030d090f0503030a02040e070c0b010504020a050c120d050f0912090409050303090d0e030d0507080306032803020d0305090319090515040e060d0c090e0c04 82
    0x2461000000e4880510b20009080001607008508030707070000c10900c0003695000060b50b0b03070214150701c00180340500745003910090b040450010500d000100c20811203c25540c00380c070450350b1030000b20b83c043e641d005040740c0c16442504011b00e1616040c00511941c100366002c0c0c00d400406080c028a00225540c40c07a10340041c55000000403074000a50b00500d011600500380c0103d8036000604803410705441054903034200b0012000c0141c400316103020706540703c1d04035441d11a00300043d00c7c0d40f400d1415610380ca0b59050108040881c041174030b09240d13130500055449a4507500c2e9209410480350b5558102580d202510442d814031030b651498080e5811004003150b06442d200c0700890781c881d079140203400c10115000f1b04c41403514210400003a15004011215200c48060410481020481058403403d80c1c580001da0005818510340a190034600c0090003900c00500300040b065032054208004058a5403008020104a03042000441c0c060380000180c2030b80c11003500c1c031400500012408503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 10049593 1250 10048343 10048373
    0x60203120709080f010501081501031e02030c060711010f1806080406060e090604031b08030f07090e09070317040f180209041811030703030f0c03110f060f0106020a03120e0307 77
    0x1303655150b0040154190810103103041d4989032070820750b15891500c039080d0080c910040901e00e0440b08050034110340d014002900d044400401c40303a02c0700c03800e062518203a503001030200d020500c0c40e0505a080d034007600a00e20340c00b04180920011500b05202110f451802800444d8816151030300450201113400c000f40c801da01d594018250ba1803d4140144a0f8200811800c81001420309034408030304030208072507112002c40140c050544580c01c1c1160504065800441e202c1c0f040014028481b20100319942224001c83c00c0040792042000300e404075114a00c9404002205000104007000094401400c154500e9a0041c14900b070340b4007180a40d02c01c24103056842e109000300c0340030010350301c405e8652600c041e401000d6460039070750050714011400b0600424403074010a8501018401e01c104909240107230705445004554110b43d540e1340c002900c0004405284800102c0e40a00c00210b9100b8650150748260800c01100c502c00010019016858224041081141c5c0418803420101406c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 10050843 1250 10049593 10049623
    0x402040b0c0d0c02010806090c09090a0506030f0615120f0d05040303090605070b0601110f0a050307030305070f0210090606050d03020706030b0102030405091605040305060a09020109050a06020312070908 89
    0x51909020304040c100b155001d0750100b0311030412410b00c00360742c0c80310210f98489000d0b6000ca5158440016509c05401080b18441d8400e82e00e0040010854244d0005405050250110303010302d50340c0f0300e04985940b01101c0448580b030414060600c00d2824000ea04003103141c0c00300344c9425044076000d285c2400380648800d0045107002604100b0541d105c21407030010811850498103000c1c480e075400300e030030001801e240e0402400d0702031120395050600114004850100845e04000d85502c0e2a0791290001001036010030b18080008501303034011000c0d000701305542d41c05441c0340ca01c96100b10002300080c200c15500d150b03171f591010485072508000307581e2050103a0001c0c800700d0300e424402000d40d01c410b019a81190024442041151250200f00390005030a0110151795030880c18112254055980050101c2c0306074402d0014000503540f004207454000e030381d403580964491090040740d292074800c0c800107030300400c002002c80581c00c5002c1d030066001e25125419642e5404003e190060004000c45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 10052093 1250 10050843 10050847
    0x914093c010603110a1101020405030d02060f0105040e060103150204051002060405070906120201110a06051008010501060305160e01110706030e0f010c0507030503090316060e0607020105060a06030b010e0402040b 93
    0x101a104440303036401041c15140921610200f1010108140100710101c0e05000e00018800700c0108290155009014041e045501d10543c60030025595901907a00480030140d120022403142042e00031180b000345408014080b0b07920350303070340c512212300c0b04500040000e03030a00000c44c0315a01c1c80e800c070b806007989034010b150750309050504031304100c403030741c0f02c08040342c40c1c040c3c208501c43d04030411148294090800d29000c0081c11403441c18041c190b80003d108500d010104001007040c01401820b440d4080001c1000d80e80390b810549c100d450950341d016030b021007a0100d00c10300380b003801124400c02041c9030440e100e13401c83c007041c0e00e0014a5001100440d444505101c0d050f0302c200004130ba00d80b0311500074018000c806070050031911031040c024040240000001d090100204212028513400e005400c41740e102a0514500031b180b01c0e80219404d000d440c0c04600c400d8814040c4500850004110210180c60800300360001d2110070b039102d05002c41d5200f990580c0da1244080d0004020b201130850b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 10053343 1250 10052093 10052191
    0x1030308150108061e060d0c0203030415021e0304150905030912010902090105010f1701030809010807030902011d04090803090705011404060f1407080a020d0201060501091409 77
    0x2181a10a04041d103040110f52010421940c1d10368111000300482d45404205035071007600410098413400e090340306464248040c4848155001000703620460082d003142035000c414901d00d4003a48160558034480c0d03201800c014401043d02402590424403e140c80c4480041c03034005041540d21903101a85d16404c00b003400340c00c0303050803545180d5002510340208442000b130f070300052140d8030600500e41000040d490588a02e806020005080c1d82061100d207010341c0c1d20b15041030340780d104940702400140c44401140015001c0d00880030038550503146c20020101d8402c04c41c0032041c038004082e03405a03c4031040310104500d40002e501800c2400045d00600342000f00142c54400ca40c030002c90014400c04c4100840c507844400030302e0700c001c18500341c20070380004003580e541030146540290083c0c01c0003035514051a0001290032901038544c009121443c1e40d83e005407501c80a510170b141c0346504054540d00f0510301070011681c402000c1030f04d8207070302d03078103403102d03889010761aa41c030311001b107a84100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 10054593 1250 10053343 10053361
    0x7060f0507030605030c01021504060b030604050c010201060f0503060406110f04030b0a06051804060b01140d020a03050f0106020d030504020612040b040302010b0d0c1202130507030c110c0904080a0302040e01030308 94
    0x81c41c040d0001707400501c4039008000000750b8800f40c6903030b1001800e0700b0700086000c00c00140c0040c1e200602c020700300c800385d080c941441078a500906140901541ca850400540d01035248504011142c0003000303800c10369102d40f6201c01030403600f800300b005001c08121220a04440f000688007950080302800c08070f180520b0f20004841c1203402c03582c030071964a02003ca164001c40031030342d400b0b944004045481c040202c016580c114982842c414200d03c080b600c4102d01100d540940324401c51036806200c0c903110f0103203040e1320b05002c0c02080016080500024141c60003604000d4110b440030b0b111b2840e10034898108649140d084e54125210000390051206165090042c89285131341203c0c0107941b801c02d03a691560031181c80c899070f5070384148509c07468199038400102a4000103249008d11452a014000030700412503c50000c0100302c6a0300340d400c01400010b5810007500005e0408111622580c46005680c4c1181c1d08500405808010206882c115450490f0080d44030303440c2c280d03040c00c1007025 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 10055843 1250 10054593 10054601
    0x90114041512060302041e0b040c0509190b03180d0503070c0b0402010203120916060507050a1103100e010902040507051903020307030b06040e010614070812070507060f050703 77
    0x5244015006000a0200c0951440100c0c00d40c060303820641d103880e1070680310001900007903102035802450042d4103095503180441001261075415001c210840c448230130002160302603110030700010002e1024504505284020503406900c8250610780300c5e070303034034225852607108648030300b0040b000b0250000031510070081c2128810040c24040d0551905910042110001a00190610000c500843c040d640203104541b01000009010f00b082c4c90080c491559580b10a1407a0400382003540000400c00d200b40242e076140780d4000041d08900d210340c4c5030040d0791070000b04100d52500560707040310305038800d034454a186d040c80c01e8000f00300c48007103004000c01c03035400800c564207010041150000f2400c00a2220340e2802e42c41c1001600c0b512510012802492602007503600b110000070003040602c0c04c4003442c0d0403034400c2c0e514122130745585180c1c440c1c0350041403070041a8500501250380a83c90100c4496803000840c9030440c145210768807150207403480074016550b80395840c020b200b0325a44c5405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 10057093 1250 10055843 10055867
    0xc091e01020607211d0307060905070515030609090c0d030804060507091202090405030409020f04210302060f040f02060403060e0607030b061e07020301090302072c010b0d0905030f0901 81
    0x20090f51203103490844201e5140c04141e51310384a84c0c0c914102c0304481d0a1420107402c600b0441c00c40344c071a41c0f01d04d080720080c03810740025569442803100002d5a4540807003500710f00c0103030280c80b908540718102801042072001c1c3c582d030018000e106182615480e04000112668065a00d8200604080c1041d2045130701c003901442c00c000307060314240400d18200b0001c800e41541511609080d03074840c18824118000c5800030008240005011399062204002070826103009002243c2c0a16891902c980580040c0b5001009a008000010384002804c0d501301e6000303004003041d1401c810942c1c00138016a0194004a03042542c0b040b0600c4c0d00700c0c003004075607403102c0d040c101001140601c10010b085401445605841c04c291500e110744500d8107601942c00a0703038094000c6c0300d24607080c82d010352078043c9030254000d16640025400c4500400a41c0d0789d040442c1d2511005640c4d08103081424603520840c01400d440352941844800560200f00402d043c044c000380c1c1c2a10741c03016600060100403554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 10058343 1250 10057093 10057097
    0xd080a051303090302100207080106060f030b0d110d0c0909080a030506010206040c1403010b06040306020301030218010302100309050a050a05060105030f03030c04060507031101050103030504060e04020c0c090c091e01020607 98
    0x150450300000d403c08000f5060320b804480092440c1e00108040345044403940000030039508103c0001440c036044940402d4403a1fa681b4140078445200041c410142c07080800640b1720458042060582d04100c1240600d040c02041180f070700d20746400c8480c00b274900301c2004950441000030345001541e4140305072a00300c5003d10240400d420b0a480710907111b00203010381c09031242c0c3c038003804843d50303003d50000001660140010703842d0399890518000035002484280e001d110070412840b43c03403101a030403d0580f68014001001c000d60070500f01d0092280410407207941c4100c2d8a0000030070343c20004030f00c0d154442c000601c204d41c100b80c245420501c980f02c080c4025841807041c04140500081601c050300e8a41c9805a10395941d41002c4614806020710b90009519000c0003006042d400340c010310590b0354645035140601000c0c42400100e102e1800d01c01050380012004500394030b4043e59181d008400e680d060307800e016600e00001c584c9588510900c0300002c2d0284140b0b10303540c040c041194803003003034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 10059593 1250 10058343 10058371
    0x10b03040c08010b01170703061d041b031709040603060e0703020f01020f030d0c090e0901050a05060612070c03031b0302040e090303041e050115060e0f0603090d0c02040603050d080a05 81
    0x3402c0086c0c0f00c0d80c45184d00f4206900141d001825040c400d5000400400c1501c0220769078000400440200a01c10340c4c0c01e0365130414101d12403034034117004604201200c0d44517600039800d61100450681507044041040c1c3e100352101c1c00000072856038010009000680380180480520b0742c07040044441650400754150b42059082036004030000c000ea5940f141810b1000c1003080400400b2190f05c040e507007210480022400a0140854055002c94840c0f10720310300822282d180c1c4c0c02004454010702c01d0340c40b13494038000001520544945806c405040c0321b400c0208680c6054880700070039140d2540c00c080003e40c0424100a4804075001c0f494010341c5260256140d81003680310502005000b10703007240c070400220080740412200b588800617091a0304000109942c4070000109806c8024040503c5040601c130a510b00e45090400c582c06121120002c6c03d4244040a090b5007001480c04241c0e4400d1795a007001020800c06e0020380107800499032002d6042c548002c07104126040a00804502d500e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 10060843 1250 10059593 10059611
    0x10b0a02191101030b010906050d020304020307090e1e0c0607060b01020a060204060c050c0901050303120c071b0302030c0a0605160201120608010b1e0612041b140102010e01021c020703050c0303010b03040c0801 92
    0x20300b10b403560202b6400242c1d407913485002180c60700306c142d44042d070681e1605042d04410200801c0308100c0a00c0a540f074140c80444004159039141110b80c000d034000d40070403240001511980c0003591415060041d01e40700b2886032126012a000b5034400c4000c0344001c41c0400c03c000d001e0103400301c400004c440e003000b40d504080104e9580d00031482c811052040000100301070035081c00650b154907901500c0e1420b030f140307002145021002d072440128001c1c8102007280c1320f04e16081041209642e007550764141829028240707141e89000c0c410050303052240d0451481800070003405030101a00c40c9a002041d050f50340da042c0300810150301031440486040c00b6447d410b90b5505802c4030712800200300d0110054666003404285440c010345991000500e811000805003074900c8038801496090300204200c103007031048a402c3c0d1049502030880c03084402c84185c60400c0c0ca90103407004a0103803400383e00301104140414950f50080c1c201ea10a010701008010402503842c103800050308001000f40b00441c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 10062093 1250 10060843 10060847
    0x201060e1b03040309180609060504050f07030b0a03050303010906060801052409060903030a02010501031b06020601050607050f0706020a0c091112040204110403060902040606020a0803010b0a02191101030b010906 93
    0x28003036580310581c24000011909051151070124040c0c404403c110a544095035200b9000303002500c5170031640e80c1410b0000566191a00c22140f0403030801440a00e03642da06001140140050060184c1c41451004c000c400b01c2d0003040514068410f003000041d4203414800054480041640828480e0540710269406c802c601c4203040da000514801c1d95445100f030740c1c0050340342d0084c928100d803d844085200440e5542c1500400d04880c0603100003200c0300605210344040038424050031003d03030300071801041281854401850001d0040043d40c0480088244840c24900e503076000d02e005038401c11484080c014640000c00042030564010003210a000c0080c108038003c603200e400d402042c1100007030030740d01d55070444c1402c5581071641c90740d03660302c902e01000107144117441a80910f00e022408501c046c00003400c1d00d0070399003215540742581c0c0303045ea6812050340255185400c500645d4030545251418440800e0b6175882080040880c1090030001002c951340591858104a005031041140035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 10063343 1250 10062093 10062121
    0x606030106021b010c0204020d0b040f050c040b0d090506011d060a0315020901090504020c0703110901060e100203040f0f0602010f05190b030c030a08040e07030504050c040c020a050a050d0201060e 86
    0xe2001403030340001c880703c50069484044400c400b94004c5d000040801014405074031030a0407000842e010000c0e00200d40284d42111303411540000a1070f0100003d014a40c00d680c054000b155184002041c110196910241082c3d4281d0026003d1180450502d9886071255446036018100b6940400301e0ba14588400c008182c2039000003e9507940001c25408992248048402504014109658401c455079401d540d5000520040d1541c00c0c3c1504006e8103881e020314018102c6059503210614420300c40100061001c1e206030400640c881000000f400308880000700e0000c0c0302030003409041a26112020303003500c03544a81c0325101f510744001c0186244240c8218540103212080010b4042c503904080785c07600e034001188a0345842652402d01c10000f4107801030050300c807142c1d010046034503000702c260207881042e540144103800000b411392a0707040540c091004e4840c607104031042803040c0d0303c4460800342c5c046020f1756660042e51600341d050b502401118002c00090742004024076001c580c001d009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 10064593 1250 10063343 10063363
    0x7031104090506010c0609030f020c030a020307050f0a0f0b0a0e01050c0604030e04090b09010501050a0503070b0406080a020909070216120209060d050102040e0a0209010207150e0d0302011806020909060603010602 93
    0x80d558980205206901c6a01840b000e591b00c82d0b010401441c441c14040c0c52a4601100400144100c40c9440310380d00700466140c600580c060000d0824a00b84010420100c1c812801d80385c10000764580003c0314841c00744500b004119805203581c0c2c0c0d07010703640b00420882100800906110b0700b040340c0d06408100155076503010b074062410400302d419071400100a41a0b0f045e01504600035181070001482041d0301450403950101c45450685a4a03800c1c59155400351240b00045241880208074403805088016800741c3c206100600d8040c0340c03070004101d40300c2610601e006070f00900070301c1c48248240410720081c1601d20220b039083c50b03a41d4001400c8290060043d406070b10011000d808010094040e03070301074a01c0e03c4151a1614084003c507000350400e100d428010b1245030b0001500d901c8001c20307003802481542d00c440344800c50764103000440b03071140b90840840d940e840307007600381842400e04050711501c910710160395a45000104450160054050f6129000420042282c1c50700001c6100c48 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 10065843 1250 10064593 10064609
    0x203060d0303050a020d060f080601080d051207020c09040302100506040515040b040e060408030f010e0606040b07031106010609050405180c1201090f080a1d0a05120304120807050607031104 83
    0x440d581d0b80c100602038007070070aa811b80c0e5800d1000109550842e209107034140c0d8072190407280d85d61790b52112195640d41100f813403800701c0c5013001746861001c03421003038903800010b0380100c50345424000042400007104031802d800603044a4031450320050f10707000d240e802c01000c070380038066030500002c000c886002c4141c19030b00c075607502d100c0010583c80d01d030441c803c4c020a45080d07440340e10b460f0400310701e954000c4650050a81c2031340002f040f0b107064401d4081c0078460241245003883d0911040c1140c640c8a0030098080c0b2524210840c8101810008180a03285036960f00d0911846d001c144015200c01800c0c0c1c112420041c0d06903540b1040c00600000600c1080301c9034085141d40c140b281b40100b45100c00988840b004400d1007091084d050000d000c000d2403070303940e4802081c0365403081c0b8201c542c80b00400c1d8000c200482c03c0220b8602071403501c1001030181d054a140a550302d0018a2103091404201c92044011a80300c0a108042c8002c82d807001580c10300340700c002901000c0070386d01c2c0710380c2c014440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 10067093 1250 10065843 10065851
    0xb01030308061e1518060307021507020106080628060b0c0f15060405190905030702010924081009051312080712020a090801050709030b0c09010206010e15030a0303020901030f0203060d0303 83
    0x300d00c42c0302c0245003050100c0031b4402592410481002521480c1c0307055482080c1000101041e41c81e0303c14861502110000340c0901035a403140f01c00c88900c0660070800c4000414103400c00140b41000e0700c40c44004110680f900c0f607441c082e8101c61030a080b4007100280a54110b056031582c1c0030927094859512010450780040d0a90380c034038440d6100c244400c21400350a1030002005c04014000005203801e6000b41c032a110403580d40d429503030395618024ac0d04800e0403c1e84582c3c0440c03074000d44003943c1220408442d80c6416440e0480f04084a004444155445c209c2006110501507005059444288a440c0c001c450b40781c00d03800505091075603084070000903800180010418410031024000e0541c0000030700090811640041c600d1000340401c2e5007000348540411050210340e0111030700c00d08103030041c183c90380c030346406d0540c010001071065040320580042103030b86903814446514210300c40c1d04c0044e10307100040c00060031140d600903018001c900c10000e100c0e06588400e2854805a4145004a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 10068343 1250 10067093 10067107
    0x60e0a020309011d0304050a05060c0c04090201051905041e060801061d060304080c010b0102071202040509010615050301060f020615040c12150306140411011404030b01030308061e15 80
    0x1c3e004001601c0d58086124000300c140010b820084010022640c04940d00c0c540036851ba01040002d20612441c041c40354007240544003035082c541c12800c82c0c207005040c4141000c181500c404d014442c0c2d10303207844c00981e000900380300c40b8490203043c82d610b114030340d0020005404c21302c0181c843c45042c09100c0c14072005020303000c2c1500d0010300a034a0500080c149030b80700c0c1403d01e0214103e0704040080850365081c0304002c1855440016482c08542c0085855000160142c0030b00c4010540600940010754880760302084000c90010404200002659819640c0d032500c04000c3c110500c0c0103440003190040024002c5050300a860b007154818204d4000540c0243c0c408240c070003140214403c0545418071011039160849240c05108481c000d280510440041518164040c0c408480c020680c80e20104188001d52051030407660300d41c1c203600e07240c0c6003944944504e80d1442c030903070048000540800c10000c1c1030a02540781c00020703c1500c02c2010300060b00000500914103c4415840d400c4003060103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 10069593 1250 10068343 10068361
    0x1050a0e091f02090f0f0603070c02030c040204060f02070611030f1b100c1106040c090504030507051218030a0c150302041d07080606030412050a0c050d03060501080109060e0a0203 79
    0x80c1c40e1128450000b02c081c09450503aa4010350030030030700b0030b1080d00130400403816800d00e80d4819548a0004103d00c0c9180c0e030345d010a0702d00804102069070588141290310115448501c0200080e0605446012140100380c1000740f5241050b04200c00b00a44248040061400007094412212009c140c440d10395507542c401c3d9510341c4c001000d0340703181e10404078840310200041c0d1051031100078695600c40f64224541006558000a407401030519105040c00c02c500756081d4402504039200e843d0051500b03003542ca03000d2829940f2200b0300000840041c100ea01907840364026000c840b01500034102294560700c449003190814031400c2d028502070910305000724440c0c0d0444000c0d25214a00307529100d03000b9a0300003e5039040398031700c001c111040c0114441f0b280038406d803803149038089030f8143c0100a4031802c84154010881210501800703c8220f00052014441c4c0440900c00f694001440c030701e0310700014040300e4103074080c032005032412030300b03103c490885400c051b80420040340150756905c4880e0b917 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 10070843 1250 10069593 10069603
    0x607030b0d02030a0b2d04080703020a0b0705030a0b01030b06090f040b0d0503041404020309190303020d050112030e1005090f0f030102040807060e0301061202011b0b1009110301050a0e09 82
    0x1c0d81801341020901c200a040a00c6501468035011021101c1402d0040740e440402c40850140003541c420000400080c400700080961078030a02c103481e102c080641d078820180384140d070034801048c408410040b00099501c10155041c900746400d01100000e1408900b80e0710544030b9880c0910307404110b00d50603844c0c0d60001080d981c00502510f42c1309009091058880d00039004040c0750b98501001d00406190a00a81b4041c90300c0300003038081d048038580200601d04501c0c000303c1c04c0c10b4003070007010030800a52003054020080280080c1c0722080b00d1800409112115030401c0c480d82c100d205c2060540d43c0641510a0303510142c4462612885080020308107240e4440030ba58990700016020608041c0030030703003504591007521703100c2221801e20201401d032900d5010744000700e40aa2482e00140d03118003230841400050419030302e89082581c0354200884022540c0c03e02c03445950030304016090b110b106d640c0e0070820308000309086504100000c0e00c401c0303440c45850600b0b4510004a04e500c40c003882 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 10071949 1106 10070843 10070869
    0x30b040504021c050705100c0308100b0904020c030915070308070809030f09061b030408070501050705120a050c0a050601030b06030a05070603020d0e030403060b1f020607030b 77
    0xd40c001400c2d1042d03c01d4901c1c1c0700d4500001001e03142d5554031780501e10744c0d0761001c4030041d0350b04015208800103040383c0305640304504200041400c41c405d407412100100d80140c1c0c0c99940008161440c000d88021942c001c06410015642011040080426a110313440c3c5054940e01c042080c1d5024800f1034428210f500204403103400030200310002c00070414001d040c2070904d40414554214038050407804100e56000040500c000c100410015008010929242d4a4a0060b41d14551075403091a2040c00b408d44c04900b201d02240180140c505280d110700031036140d5107403800c1003030742c62000f032005440c942003082c0441e40700e0401243c548a40c47d0000c00030000ca40c6403210440c001d501200c41750609907a500c40d0812054018801000114011080410110514410440e150003000ea446030030140d41c560100c65150080703812644201c050800040300312a00000c80d615401d000 = true := by decide +kernel

theorem cover : BRFrame.Cov 9892093 10071949 := by
  have h0 := BRFrame.cov_init 9892093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9892093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 9892093 ≤ n) (h2 : n < 10071949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
