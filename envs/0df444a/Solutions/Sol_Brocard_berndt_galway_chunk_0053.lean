-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:34:35.143901+00:00
-- url     : https://prove2.me/submissions/c27d6d79-8ca4-4b90-92e5-2f5005d70ad4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 9352525 ≤ n < 9532381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 9353775 1250 9352525 9352531
    0x40302010e040203090a0b07090f08060105150a0302070512030a36020102010906021201050a08070b0f030601020f070308031f0302030a0209190c090911030603060619050a030b0f070503 81
    0x603640c140014082002e00002c1c1d04080c02c2c00d0454800e8500103000181000c040702d10a01c820780d256540d903442c0a007455044240c13a400008281c001000502468903001100c0344812045010156504059070b0218020310803000040d2260081c02d03210908100d1120045002d5441c191041c03004400280c00d10b040d10282e4244201440382c0041c4401407490b00c2403c0c1e0911728014000080c05d40c1c07240d02c880d0b080c1d034494000d100154030080700500c503a1500b16407460280c030300d4400610407a41070041820017445500d02160b000c1c140400001c17810380c420440349400d8007550b810340d00f03415540c0ca01100c080d042928030086011901400c0c14219a6103000c2c00203c0b43c000b00201103600480d02400490075007d4900082190926604100310341d15008404241d100b507030701d000d103240c80e0040707400454203440d503500c803422820000e00c101c980c0d000450b15000042110008403107040d442496003016040c1d0300507604010000f40000502880302e9000780f0511070850f82070401d41e1030100c1241c05100071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 9355025 1250 9353775 9353777
    0x30c020c1806060706021603020715020304030201080c04120506060103050c090310020307051605030d1104050d0219150509100c0503070609020319140c1504050103051b04030305040905010b04030201 87
    0x1010412480c100c4280c0c0341c03a0420b40c0034007070a00d81201c5450354002d030780c002802c21322070007940030201041550400401004251030001c8010b007400202e8000e441c2c0c8201c1c40083e04106c881c2001c115034450340e9040302c1c02040d03c8640355141840d149801c2d6118070742111060701181c60840020014080c2000311683d13460014007510340e405200ca01300d0029040a80b0b44000c000007406214040c001280060513490300500040da1122a44114407040d1580626001c8141d0b100380010890760700c400a0694009504485810701c00c9001c40c00e401e40c9000e80c0e400301c200c51002c0f5010442294001000b0040c119003590f07141c610031303800002941c0d241c04c00400103202e50f00400a081c0414981c0d40039007031945c8020241c403203c1041101030341076401c41e08816140c0ea07242e85c8098500480400103000d8214041d1203200b00f900000030010014000d9225990506840b040005d1801d004409000c0c03480b60070000c044d0b01d603070300ea0a00401c036410a000d88090103182100204815800f041230b1401c8030380c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 9356275 1250 9355025 9355039
    0xa11030714030a0902060a02160b07110402030402010c05010203010f030201080108010e0c1027090e0c090718080d0f0801080105010b0304030c02030f0a11040f02090603040f0311030307080106030c020c 88
    0x4000d9000003503070b1005149505403581e8480d8040165501030051400c0980c0d5030052141100564070030744461601c2d80b000c503080c04100040f1000a1201c42c0b0911401c80440d40180c49617654001a02c115180100003841540300000106201d98001100c1082d41d000fa40c07000d02a03a258030015003264280080f4039841ea0140f102507500345005800c00e04424031034030f00809200040001d640410718801c1c882c20450400c19820b002281d4644544030301c158921000704840055440070819030000581560200505420100248100326600300f008188860807101c85078900c080c010a031500790300c0c80c03000154070301000090864050051505941010300d00514580300d5070380c142c0d08030014a00c12601170042c42c1982e0100300051100c00301090203025242041070300301c2c003003000b242d81e5480a40728085c8103004079105c2e41c44683c00c0e030350b2041d40480c1c3d41000c02803509041c0c40101072802c0741003007480000108504541d000007000d0494085880c00d00442c0c124140c2079072110005001c007900105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 9357525 1250 9356275 9356297
    0x405130b0a02030a140c04031e0804090204050907020a120305060a0b19080916120c0b0d05010503010f0603030c060f060b0c010c02010c0c0803130312060902070506010608010e0112060204051003050a110307 90
    0x40b02c244c11444050b0249c640782940ea0a035a00e06154000c0c1e405560000d80c085010425401e1a08000e40e020b90a44081d001d8411155034441c00403031200c00041c00c00d0350302c2000400c161104a160406804104121510b4923a0002c0040c00c00c0050201d100000e0740c0e0401041025030001101e600701c0e14502d640132081410b108829120803111002034545207041000040d00100100003841d088900d2140803e980d0304020a140c25542d039000b41080e0146000c801300082940704049005480d800303c008039000d00e02d419603e001d427845400410258100240010481d5415440300d403111001da0001c1c4410030140c48241c1d0f12040a180c0501840701c00c10001d407001841c80c0e1080300582c42800c02c0d00d02e20742031102440440d0300300c0d00044044c950010307030081800010400c0038010850f51509091030344c18050a1180209c3c103100b00046025803091410420001c0d070191405000c010701101d0900100a1005010300320585030380c90400e04e002d5074079080b40005001c40e0b224241030b840d1125036031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 9358775 1250 9357525 9357533
    0x106120213080d020607020f030409020702130507080703050901020306010906081f060512010b03010503070513021204030c060506151801020a050a03020102070b010801060303020c0405130b0a02030a140c0403 91
    0x210014814524150300308200c081250380c1da400c08001d002072100800144440000180c41c0040103000c03034040d9842003c442105034000022101900d12010003d82c0340c010710310100d8601741a002008040710708000070001c6003039104400520858443d03809001a84071945054200d00c4203139180b03800518405002d2215034004c4003440e8021a21451580108402d4807120076101d0361604a080041c43c0050040e2100868112070341c09444004001c0b442c2d5403510700026038660146c8a01c0d40103402500d4502260945a41a00c00181d09052480300515252400810039900700c101111481d03d0b000210b581e03400e00440300c40080160700c181c070f8907010303807a6490000801ca11101e14118410803d01c100010014844400158403940002da01c2c1c260078a041c01d20300005070400c241c036078500001080403990000c0e180c0b02030241910009026110312040424215204802602880110003070009140c0140d00941c0300703610908041040f01403140b03404845040540d251074017440c0601c410300102e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 9360025 1250 9358775 9358787
    0x31020102031e0c0105040b0612060f060d0309030c141813060b060408010906090b07080403020d050a09080105100e01050a0303050301150203160b100501140d050a0204080a080705010609020c060106 86
    0x7012001c0e85541400d10581603e800d40e601114101d444c198034400f4003600d4200a60380d400003920740400385c6260b1800c15612010968010308280c4591040c8000400307040c001c0e840003003d0740e003060411014a494141c0540704202c2090b105004001c01c1e103000400d80020322071207005242020b4455020026900c1c4d90010b00000c44080b0b500c44401c11001521510912451001c03d1180388040760110303c500b012102414028034000522070ba0303400300000641e000c20103d002a5980c1415038460158020486010300581c00412241d0310f0503052203451030444424404403224400c140c03003d40e80321018000e21010601c8001d010a10070f00c01442101100c017411030340d1084600c11641002c0a10440304507103603800c10241c91155020f82030010081c0a800c440010b03120a003800e46000902490000b0140318256020b2111075540000c124003180301d070112001006079908941c000241400e25000691065004541075803800b00000342030401c1d4029148908805000741015130b18201d019604 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 9361275 1250 9360025 9360067
    0xc011d10020c100309021305070c08030910050403020606031002040501050403030e060d02070c0311031209100903170c01150506040506030703091703070f02010b0901140d08033102010203 82
    0x6602900b9040246600c1c0d1403141845038016541c04075001d480e9005000300c6100000c10b0750103403802c0104224400b5000751081d010660300a030304568a40c2d5403040a81081d82001310800309031b007040248014554002030340e41c0607080c00c40c2520300b0064100288400c03840781d0320405001c204240010800b0a0182c1142844800d01030700d15894031085500e5072040303030b01000d001c0b1001014601c06005004484413550143c0e81c061f00100030880d034040c070f03814540c0200300340d45109680d500c034001160b62080c401100110b9211740002c1042c9252000c0c0341050f00b00c280400059880c012140c5c2c4c8506840d03101d141241c0010780818070702420301c0c040c000d00707a00003403440d0b081c50b07100d50025001502030001b8540c0c072012041c110381c40382002d10005051710381c0548090704580c18a070107002c640da124028981101c0381444071800ba42d1260010652158050354040d1920b00007101300403d01c1d10b09141c00c070340c0c4d481c1c00390802c116151080481c2039103904048080d005903c2440b605101c003008540c400c003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 9362525 1250 9361275 9361277
    0x60717060f040f0f1b03060b03040609060902030d0206061201050c040306020705030c070605040501030c03020a0e0405181603060522030f110f0106030302061e130809030d020705030c011d10 83
    0xda071184458404280c0302815410752000366201103403d010045c240301e401e40c4240d140344c1400360f0341c070700141113865010150014120581d290309000c100586688140348441e40134059480061142d070001c0c0d1211803c03540b55000704030407000d910341d680045c0b081c94441c3c58030707140355410103045846802c002e400ca148125418401088000209402001124000c003a913568640d0b0b210301703060004091721140511031080c14014000c0048980d042710f4416520310099a0025060f5542d040100b2600051001590340c0e0203000524010504145640c1d800d4030f0107040c0500c0a03840b0418094008040b00b40c04240c00307441410726a001030f10070140f00300815804d1804940960385640c80d10b003400308488805050740e542d0503081081607018050180c2c000f0810b420007580c0d02d0300d03044002c800308004145070f441c640c002449008011802091f81c0c04440050304030340c0b40e2149014080d40c0c403c01c502820384030388140200e1000940c800c0101c1480310313415030300c5604c07902c1c006424805401d07078403541c9070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 9363775 1250 9362525 9362531
    0x31302030c18060a090b01081308041203030203010302030c010c031b0302120f0309100c02030a03020702040f090503040608010905060607030e010e03010c020d0305090c0901030f03031806050103020102060717060f04 94
    0x1208560b5800c100c0c040000c41190003480d2802c011080064040d21030340217400640c00e0020060541ea00040d4540d840102c00310100d0900383e01d40f405542d00d200710707081111954015149402895410340c080c0d810f803882601225894800f10006440280d029003006002034100700302c0000c0351003641409a00148a40101c4010a0790156406540e8100c5080701e80307503030004402c01043c440d041114001c20195040100400d2920710f00007500e070712440100d04103040d00000c25030210b45480d03108010001350880c0802c822041c0b07140140e1260b00500c140d0000034954000802c000c80240b05481c040c040050030700b071a0400c0b076034099585014400da900d06108501e8200c1004e521300303024200800c0d080768080c01c906075074aa4090304864001e4040b40a0fa80640e9005020b81c44a0854038107413500029414005001c6213412400340c805040003225094104284204110541d004035043c2c80c401d07000e0f01c1740c82d500c1c03240484100c180c88a1500020320200301141d4181054025100c09260286c004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 9365025 1250 9363775 9363793
    0x1060504020703030509160609050103020f19020d0f020c0a120501020d050a0c02011503050601030305090a080a0809100e1011010905031209060105011716110d0206060103050903090603130203 84
    0x50102d801004060b400f00c1c3d1220100304400324180012a04030030858650101039043c001d00504090043c09400d0615900080343d07121083e030a0b040c3c402000034195001409841308200039200d005c070043c0540800e41070300510410310f0020600d11080d03030f0060800500300d07140c0071000104004109060312075550030000c00406103a24010380c4c0c0b24411505000c1004144140000d0031104640020342840c00040418000648046a1281106c2d0145800b40c0c17a040700c000018032441d92640004070500c03c00300294100203100e0701900001d001100d0100040b1800d020980794155940c4a00b5407007008500c1c0504568015a4505250500d4000000e248105d583d03680e03146d43c0c003144c410440b1a001200308070040030104202800b4090130318000484501e117a0f044405044081c241090210103200c0443c038580c41500c580403119040c004a0302c8050310800e000e51503101c1036030100d00207420180040c60811000049034000b0780c000d81039520b59510400d803852800e10800741245c1c98025140300b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 9366275 1250 9365025 9365029
    0x5030a0c020f010203040302090c0c1603060905120f160303150e0604050c09010c031b02130203060102010b04020c0714060f0301060504140306040b060108091501090204060e04021e0705010605 84
    0x18052404040e00c0d6480040160300400c4040c04620180e00d0440d402004180b0041e02c41c41342d529000150a0f04c00c90f1640074440182d13040100200c4010301c41c140a81e00041481160740142800c1801002651884150016450000d20404010a40f800d00802c1a0040340c840801c4100040b4003034070f0000307030110038140c0c00c003103c0016070301c41c81540020405000c07103481c00d4450a5040081d002d5241d00d0611b805001030070301444050040c0c10b1050542000403030452107200800b0380c1303a000f4185020224400700d07100c004c3d001036548030300561910343e60300d010381006e00c2140c00100005004102c10b901d40b003802c003500f800500c40950000814000b44000c00d4820010350702a12050f143d0907103940c01e05040b00903c000e40e171140c1d4406d600040034070000ca40031000780b9400800c02e10b80341841d6610700c0c40e05031030300b0003c003408405520749e003000003540d00555001c1c0090b9411555200d2011001404210a0780180d0003180c151040709030140841610f004000d01c206841030001141841e51900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 9367525 1250 9366275 9366277
    0x90b0a0908100608070e0106090e041401050708071d0105030a0b0111030703020601030302120708040506030c091e0102072304021303150603060623040c0203070506130c0b190c0309030503 82
    0x10142080d107403280c0302404402d80c00d220175400341204800904640d1303d8035800900354103042c4900e04100202c0c1300481d083c0140085a80e103e520003600a02c590305041800502c902000c0350070000003400c0141c840f5414440078454200000142d640a003940c8410116400504003444114140554410100d2a2103008d001601c20075009801a11a03503245090290605a4248001003411010000700c0002294a010381d41640d0054039140e8690fa5105504011480340f05062a0300001000d44148900201c1104508004d001c1c3e0954102c01d07503621006280e800f244c16046000c90503910b9174034280c20258058001164101d008110040c0c2e6621618003d1003030b0b07041c885885841d000244140445401040001d03e203402c0104054072150780c2814100035040d400074443c03616044007404051007001078400454202068039100c0c02c10f80906865060700400c2107861005010000450202000030b540742d401c0d0481300807140c8205020101c0d00c0309d2551408809110084002001150f4200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 9368775 1250 9367525 9367543
    0x51b06071e0318050703050f0307031b030302040b070c0f06020a0305090d0c05090a050105010e010e06070b0a0b060a0203040503100605090f070315171b01090302060706060801110d050f0403090b0a0908 88
    0x84d01400c411400c604116081601e5680d00100503032041012000280d4401c000c1c54440401c2e003042c0c070f12240d00c2d1404030064482d56215100d0343c031010803050300380800e0400c20b100700caa07815401000c041d500d48060b61134250a0b04003801244046c0014116401c0a402d0030024030310032200d000c01c8940b01c1c0002811541d00b91400e04600c2d81d181c0041c0a01d58002c421451951409d0900c21002e0388070000251030740c415007074024468800c0d5804a00383c90195003015000c2c04005082648442c8041c000039905e404c0392064034864407640d0301c4094103410510414083e107001030441180e650302e0200034500303120060014020543d8501c0075195803078181c51000054a001d0303a032181c1400c15404554541440d000396885e000c4410b0b03c0d1a405a0f80200070304045903416500981c917408141400c1c40206807a510800065083c1500e5102030500344000304510000280200300f103032a59080305980382030450300100803407440c140a01c040d90044010304208410b500d070090072076849004540c10b1424007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 9370025 1250 9368775 9368783
    0xf0c0c03030309070f05010801050603190902130c1202030603030702010f02030903061302030c0102011e0b040209030304090506120109020105030c03090309040603080a0909021e070201020f0706051b06071e0318 92
    0x1c820722115170031003880c1c00240000d00c2d01c1c65440d410314000071980d100242a0807000702c42d03186403180d2054140c2011405a400903e44214291a0380300000a00300840e0040c0003d6062440110400e03914800d403405600040c0045040000550040d510080c0e107283c80810344c0700074800800c8580e81041140d101d94074019102d85c025640d80706251503c0b041c0c844041c150790600380b04094101c00118400b882d05425030004c42c0d00c240500124009106514900e0340500000501050350301c0f194104a0148100703850703410700d29000c014080d0894181c00741c003d00003102040856404848a406903810451080550346008450b00005045035104e0703004030368a031070218000d6461a00500800000c000065040d4502850203210f20b18280415011007003003d00400c4840a691003040740440105c01d54040b101d080d91582e4000c0c00c0ca42100c1c801207a1140307a0000f02512402c0030480c540070700d030f40c0c0e161502c8418803c55441000c0140c0d150b0001099601d00c0c03201c25610000111904950017 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 9371275 1250 9370025 9370033
    0x150103050307060f05040209040303110c010204090509120c030a05071e050f010c0302090a031e05191104020405010e010309060b0301060611010612020907050a1704051509060105060f0c0c03030309 86
    0x1d07900c0c003c01501c00110340e40e02418500790402015032591110154016418034000a4504003034007446c0c494081c0201112840d0300c0070402003400328865111501a030810002c4844044903401c00c06c00500c12000710344090b820611007200c2c0d03580541c0c00703403141e248039a101e019105140c409001c0c0c01c5244007010356103070303101802401c0c40200c01e20801110709840c1c81c065103800509000714030b1150f1140701c001e010408600d484214040c10041c014181c0303074004251240c40020a0040c3c0c0007420782d00b800e40311310706150402c0300c1d42d2800f0300c02c030b50440c0c030181c5502880c81d0040c0019001041821020b076821600d8030400103081e40d00307114140c040e2840d5140c40081c40c2c0c04941c0c00d400c42c2d0b2950403034032526848800c1c00c030260b59640c4035142d00030740e940750103039031030808001c111000d1116140620400714000184810044081074641120030915400f001035512204c480c1c0d6a00c00c01e1041640048040102c28800700343c1900900e504d045100c01c40d40e140728980c000c81c1c9140e0045403c0007040d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 9372525 1250 9371275 9371287
    0x3051e0a0f03110c07050105030a0b060a0206010f050414010909030c0203100204031b030c0e090a050703080405011106070912110d080309100b030c0103050601020a1704180504050d08091501030503 86
    0x1d050b2080f03410f5100741085079400c200001d401c01d03a0b50f4003580102c078144200400090301e84a9a0341003581810800b4110a488424200c4040e68554081c0150381003401102d0001c60681130038460b85c41081650741c42001c1691030a1503410051505030700a0301004181021078015883c10020004007012005005a941e03186081c50700b007141ca1f008074490100e40c84101000031502d880d08001c2503818428a00c142c54507280982403411801c52801495401919000403d1240400181c801c444086e220f1441e4180100d9810b0380b00c00c412211030010031030600c0d080c0995079158801c3e4540620840002c0707042c14904000800961017020304503001500017040021100042c0010818800c1d00b020900c60440304500107500e070120260703c241019610f900180d0300d41c0c401c00c281c1910760740095820098024200c900104c9a02c240159485029005048800000b0340d00c1078621454211014100ca1560340000300c6088001904800141c031914000406a42c84820040e00031840340004503a40c0c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 9373775 1250 9372525 9372527
    0x7060e07141507030f0c0b07030507030b0603040c03030e03010905030c0c040b0102071505030a09020d1a0108070b03041202011409010902090a0218090702100f0515031903051e0a0f 79
    0x120810341c072802220a2403500d1088040903055500641d85414a2039250400700c004585482480c00040c0c104144107003031104032a05580980d02502c0b8030395091000d410030205000c800c1c03005641c010513403013030400b003040402d10540319400d00000050001c11500c603591155131443d0400d4918014941102c00d104541d4601351040202244082c000707490079914140d00c1c0c0200c459199540418414000009500110154041e04a0690050196101607858100614000d800604182640c02e0207030002c0746d80900020200110b6048601c000e243d81d0300da0781c07040e0100c102d4550103010343d92109540c01c5041c2111085500c20a5400d000060242c0640100314030404c0240c00091514810021a1201325940c0054070001c40196201281500c1c0c4120407841c040d40710807901c510f00d1500d04059100a016003145004a4060341080c0d05040240201501c034412104c00484441a007910348000038051000b800584200044400c1c140d41c442e03851803100e0380070b81611700000f24003001a5401c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 9375025 1250 9373775 9373799
    0x10501051008070206150a09020c010209040510050f0112150b0c061b04060f020a0b0705070b01050f0612040f0804060507140703050c04090507030c03050f060a090506061507060e07 79
    0x10762070034075151016040005001e5114030000d84900103131481e448030808036844200364840180303000b200c11036952002030080750007500421400c070710541c140760103d1000075240b4500015140020502c0d00c2c1c84101c68010b4680c0610543d2200b815a21801c040b003915550140c03100c0104107500100e580c1d42100700340f4a0400c2002082e01803100d241d00041413032400240c05a9050750f84906081e40000c504650980c9031480100703000b043c0320303501000c004d01180e1000182c20740c6841182c00031001c0e600d4008010b602c009030910316030050002e1115002202c2807140558026000c0d01c10324031614240d0729076440a130b20a8122401083c00040c50000300225040d1b21402e0408072400740c01503501b1740e5a029160319030019072a01c80e07900d92545600b400742c2071180100441e801910320304010707503030316080f51a0b4600b9400101c5038025040061203580301802803d0781ca59020010340440e0343c40c1d204010380c00d140080c407403051001c28041d207000100c051041364031070355200c0d00818100745040341340181 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 9376275 1250 9375025 9375049
    0x20a08010312030204141002150a0b0307050a05130203060d0501021603081302010801090c0e0a03050c0f06120c03070c020d0605060907020c0105030406020c1207060603020405010b07050a02130216030201050105 92
    0xb014410813080000042c0c0e0042113046c440100e03820019080307020401c0707203000d558a1010020351444810300100b410140d02c4080c1d015810340686081d255560708110b007040d0940b10326900420003160b0f401c14401d040d8001d66212030001d1402c40044407035180d0a00f280c02000e038021107403240322414020715800801c00d6502400f4060804030b940000e9000800c42c003018881c0c416910f44850ba01002c003800f42c0392400c0c100c1005460342000c1e964070300706250765003501550035001c1c2c601f1205101403030800104031400c204100d900840a03441c0c076101d0302034503440244030320208003040d0000c00041e564541a680e11a004440105150030000204804094060302200665000c0741040c01181d8211056035030094002200607194004207601d2802d0086a1302c841900c0364000840e0810000d4a030310020036240241d404006aa80362243d46800c0c4c460380001600b90392013070385042d00616100295007820107400002504080804485a0380130b60701b0700c0210f0150f5110001809141800e0818980d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 9377525 1250 9376275 9376277
    0x1a0a020f07121d13050901020915030105040606020d052502220c02030301080c12210d050c1c18020a080109021e0109030b04080c060f01080606010c020603130f0501020a08010312 78
    0x107441030b0303180019040d10707020184541245d0301c070710014403030b40c41c04e40c1940c8444802500008403e01c842151800c16842401001d100d42d21b0b01001140480c4005081c0e144c00025454140c0b40159035803200d0100c80d11410182107041d0f1492000700142c88180354000c83d240084100c1c0b030107035000c030500025a600c0888440841d8001e000400600b4000a00d641c81c041c01501c0c0510607907038249805d410500d00030190002d240c0c1f075124201c071144602c4010b0164002d0000200120348580511462900c107400d0312a46010507070f603642583e64032503403103080f10504480c0603100141080c0d0116004400e190b10004559544e002d02c04198284a181e400c01d80704a248014074001105001030020925800090416030302c110004042140710400c4414002c41001141e070545048458032225010901403504540a0170703010070165406100c040019990083c056030840e55001e40e08480c010140000782e0b1039100319991800410070a1005028942e440d41c2c4000c110360640c24040d40503654200e2004c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 9378775 1250 9377525 9377567
    0x5120c030717030f04030b0402030d020a0206030c0309011407030b0f010503010f0902030c040b03040b06120a030207180609020403050a0309050604140f0409020925020a1a0a020f0712 80
    0x4081690082101c0e41503801054a100070007240d004001c0c81c40c001c010785240254000030300403003844135104035030703220f01d00c01c400b120313010541024201d031603201d9040d0080d0000807d1000ca50291a440041c540c403c07110400040c0c01c510030030100740c01d40c00641c1c903600400e42e01c00c2e08150604190f0b00a0071011401c2c24003501d50b52500490b1151010a446615403040d400300c089403440c2100303022200204140f1440350b03100c3c10725050181c690881529010311a0700c001c00c100d54085008195643c1943d055009082894607028000703115919503201d0200d1030783d075290702281c2c010451001c3c001550052000705501d40e080e15002c0c0c10031126412491059038144010401c442c0b00840c2d000e190b0b0030543d2001d41800200700030030081c01000d0303002541b01180208014000301c110f2402c3c3c0e0074038101044003024409007942aa1105401e101c064045141e1140d00c0141202e1105165004800050014904284801c5401c01c13070300300880c21078540c2c0c52282c8292045500110b00040b52445407209 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 9380025 1250 9378775 9378793
    0x7020d05090a030204090f0b1806060406080a1511040902030108010c05070c0909020d020402030c0a030b060306060403140c04020a08070801050a14100e040f06030b090109020d0b040606030c0902040512 88
    0x40380b0501d14400203224580342e140c843c04015506291001d107a41c4500d4107101e81c1446d012003401e21511907130382e900b03a00c01c0c503002940300e00c0c260140108031260300f0041d103041105a1500700300045501e0a1103a001d031950140c164518401004000600420f00e005840e541000780c0b1600b510508104002080340c1808010085003c8103500c004944009200044410031480401c8484c1110307000a03500c40d101004010311480c0f4907000b0449510075036400c0120604800c104100c500058500c0e5030480f000340f0041c0002844410074400e41c141a60440705104058000541a44c0c400b81c49440040e10003014440e4898000c011140904401c845500080d41400c0200201d0900300580501c0b070f070b00e01040306404030b014070790340c4c3d007514070140c0b003030062540304c18082e405010944400c4031075072094000285045418030810051543c010400080080f80f62207a8000c0207014009850069a80da00000001c484100440040050400241e10b03546004100002001c1000c08405582c21020704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 9381275 1250 9380025 9380029
    0x501020309010f0905040204030c0e0709030b0c07021507050109020907020a05030f0a2619060807030b0601120f050f0105010203070c2303060907091506050301060c1a070807020d0509 80
    0x151501d40340207203040050200d80f0310701203500c00040d41c40039402510004000c030520605201d04c07000d40305034404150b4240c807139910845160405120290105074400c3c041105a41c21702c0c0101840741c001004c004041e000d070b0000c1199030740314030412260303030b075642c20400c085003003d5503416030101041c0040c08504a25444840e03c1c0c1c800d01824100c03203580001c070b4203402f9000d410015410004202c1c0841c008003130341d131581d41e20401a600c005841c03205403000f1110b10b506004020540310a0380291030020f1869555030b02962002c4d0903981445894055520006610f00c01c1c442c11000f240d4000c28a400e1440c9031210200e0181c00c9241150810014000820120016541111000034401d00b0f032215510490482d29440072045501d40102c40600140f140c00181000c10303200c0c10714040200003038840551040305c50500c0384a02085081c0010001039000b1042c11107450b000307040c90070030800500b0401c15810401c41d0044003190b00f480520288650400c0380040c002030b44e080280c508500480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 9382525 1250 9381275 9381277
    0x301110a0f030203130f0303050a0e0a0804031401061208040f0501030504050a020d05070504020f1801030b010909090213020f120709141212030f07020f03072406080303010b18040605010203 83
    0x1d81c140c1499000000329600122204408000c0e581001008401c11483e01d8003d0107000c00391031890901d400c01c2c09120b0110b9000c2420780002e584400780610307040c650307a078080100c0d4043c00211b046550711341c00001e0f0360004d000b9071003846108040b07a40e610fa0904801d03d0410f8120f8001c541094a03107010000061000110010081d404848480b200f034250b2411918000c05d0381c0100d0381050021840d0481e0b024000c0c05455041260b005407608007011000450403183c80c4007126000440e269030420011605074021180140040e00940019039030704031020980c0c0c000007001c8840d0600080240090580840041d049529860614500f41c98034039412403c20006283c0c520a0f8080e8105041204003000240000441c0c2c01d015912490400b614491003002101d098015001d01060300e0500312010040310103884e401000108820400b10f000c5451f109090f0165104580d42d13074000c6188103041010718000d100481005a40b4121103100000307082843c150381c0d000310b04005060080d0780e000300c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 9383775 1250 9382525 9382547
    0x403060207020301060305031801020f0a1716080a0c021309080406030b030312090105061906081b120906070306140901030602131502060402040c02030a080c09030a020a0b0301050301110a 82
    0x110003686494003400040c0c01418140e00c014000d1200080d001c420341a211040c940ba90300907020b580419401220b0540c41d1000307058028441a88015100d8580380b0020107460907410034080410404211b0b40d5520103580505d200d4008030f08415481e00440c0341c55030300f44100c0600d80314140041e26056403494075a00480c000c500c2855101d040c12441500e0820030307280c0c000c15002c050708207820325102060082c0130581d4041d00414200c080b80088280901014040300d090369144521603a510074540d50f030346103481e22031403401c0080207100407000401b81038600940000001e0605810b2114003e001c84420f5132100640940b00c0208062503078070310b0f1406044a40001025a0b601c208202c10440c80c1c03880d40085120020a032444868240d00049c002e105031300c00c0e1400c0150042d20382042e66240240816080010444000140380c9240c000240548130005004c55005030540d5000944085507508906030240c00800100300c40d1609007c0c50400d90300e04a1010302c0d00140d4000108140010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 9385025 1250 9383775 9383783
    0xb0901090c03080f0702060f0301031106030702070509070e100206090607031e0b040b030708010f0b2b0302070906060c060605010305101e03060f0203040b010509090a0303090602041a07030201050703020a050403 92
    0x10948542a00115017210210385c1d0050005230b40300d072101840b05c440e400a010030741c2e05550341c07a47c81907030303085c0002201e01850380c940041070a10b10300b0007003041542c401032074441080f006808044051300c40c0c41845403a4100d41d0098841c03813600f01541494800010b01030004c0504202916004511040f48620313280d400501c0031a060182501083c0506030382c0941e81d4141c850844001513408040d0300004140c40d03404414050180403404102140c502800e194001d480c6005920340b920440059241c8094800d00590303941541d0703410724204640056019001054066003d401000401c2c0305a10261500b4202040941003907014840c00101d64041d801103c410040c200d454241d5a4080720029039000c04148111240e030030b200d00103034009403000c03102c1c6080c1400204080c500314448a1055500030700074542c0c0b00098408030050b05081406503100c036070801010520002e1140c80441c0d15030581045692030b9414a4001d003182c030000c110908040c130501060300c01943c010100c400304d03500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 9386275 1250 9385025 9385027
    0x40609031403090a0806040302061e0c07060f020c01060501090b0408150c0c01020706140a050105031f06030f03020a1505060306011802190e0a0909050303040b09070e04050102070b0901090c0308 85
    0x100d074845480d5120396100c0c20343c00010b039000041c143e00000744040c882e030710960a5401a4440300e0880e05032482600b54100c050507800300041311092207801500c200d5000364404200e07000d00ca01c0601c120780c090090801103035103906042c4559600004144010403003400f229103010b00d0410925201c070a1000181c01d818030b440c01254a039072040c81645c1e00e40080000071903540c4c50500c4c00000408916984a80191a071000078111100074410181229405000b81040f00c260031103001c50341c0794542d80d010220f5a91100800800c0010403100c506074425002480c1448803400c2c02d0003a01e03003508420407854188010080540c601050710b90454071724181203081c60302c004c403014019005601d10f40060b507107942c420103056507105030034440390750094500c43d405a85411440c0d0648543c55006003a44d8001c101050000d034010391402e90000c02c003000d98019585888405884500540382640c45030740115869041c004c07500c2146400811b4407000f0800c0c45140c8e07807880c2a00d4081d10000e020710394 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 9387525 1250 9386275 9386303
    0xa0504050403090e070302040e0105030c0901060305180709050108010b121207020a090507081006050a020a0803100f030302060405010518060a1a030106090204030c15050d0c02010207020d0f050c010504060903 91
    0x4043c01620000d0304004903280c00c50b281c15100107000750441d129a980c442401c1000090f54103020030000000240075201c1800750707091007415405000050721100c2c4442d1420703800749800c0c0c41805600d0250110340c03030100d17036549408200c03821b5441000c40c41e81b10b1096204a860220400591402001c0b00c00c090541c0310b074102d0000440c40b68081d80014452801c110030000c000354088511740c42043c0b82e000b14425603440b90ec1c1101c50780110800c440c0940d02c4142c0030400320f200c80018503401b1018282c2540051384400c14900305405542c01140503902030720074041088028080d0640c170100049003c0070900c441e800c000c1d900d003406007203180440d584505030022355401803034210f0310a4002d402403010541d07512004d0700941c041e00c819a140302d4018404908148850484603065030143d50703103410900c11090060043c569011958195907007000410300580324450f500011500600700e00c0b604041d681006410840b84003001810003404100900c10243c2004039001074940002003640021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 9388775 1250 9387525 9387527
    0x3070e0a0f0e0a03080703150504051009060602030a030b030303040309050105130e070f02010e06010506030601052104060605130c050307030b0409050609030a1d010903200d06150b090a0504050403 86
    0x348207081c507140300c1d04149107000000000035031400fa81d44640d9a40c0507a0351103081c1101142c40311000c01070401c4004804200a280541003e60800070015290203d6640c8245c43d508581117684890003681000c100210880d030548a0420b01c081c0c03d80c080d62551400307030740060840203507004480c140711000c2810901c5d4040d044026010388a40d081507a1141492031019210282038103070040150700f003080c0f40101d50380c040703111812184003404450641d100c840040d00e207504a074a0340d40c034011194003c0e20000c906041002d0069000d90000280b8034104018080c1996081032241c4245081000040301c00d0740c0b003412203601050070b10b40080c07212680340010300038080340c0001805034441c0c4c106221203200080020004070000c0d443d00c40740e804105005085e01c440c004a0140413641a417010000306d90031404000e8550003443c0c10800800e8400c0c0014200340c040740d01a01c403240e5800e80e46036034440249a030303000780019050b0360b414011103400203040c11380e5502800d0f00030f640741d1012030105 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 9390025 1250 9388775 9388781
    0x9010804060219050d0b013207240b01020c09040602030c070c030602030a15030803010504050c0408010e070501020c0109050906060a0203040308030406020309060105060f1803070b04030c08061503070e0a 89
    0x214102841d41140d05040007402800d0345c00c90140c105485152400b12141580038516030100d07013042c243c01c0c0c0e501c3c61070450100b5039604c500628122a1000308a54000201601015411004100840d100a080d10121041183c04180320030741554400121150140d44221810364000c4d4401b00143c0c0d41da466043c0150b00e401210401030041c0990305012041100f250050340c0304410401c2c00b0403030138008156802d440f40241c8006444440100010f1285081c00e410080d070200321218a07914050362010b80d00d0848864a40d5007006400226050140390b0781401040300d11202480d00803910707400c02c1c1c00a4500798020704030601c50140058806903042c028801d5400854104c11300036107138034103801c102000c1d40c021078803440b01c2d00501c40041114600701080d283d502c048181014100b184c1c0d00caa4039511210602203c7e803501c5a0f001c001800c044a80003030001e14480c0701c0e07000456103015800b0345001c00280040c0c00310410518104159180010b441c0b04861403240308143e03d449130b640075002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 9391275 1250 9390025 9390037
    0xd05070506130309211401060b0301090903020717100e0c060f160804030b040605010b16020105030402040e070b0a0305060d02100807050904060b090909060402010905040c120906050f0c0f090108040602 88
    0x10403810501c4400884d51500c401600103002e0322403140030031b0ba1481d41500321244c40c0aa010b03034000a00c0140140c42456000c2000e00f44a80100c84000b9103521442a00318200e864001c865401008041802a1140104030489940f0b4009154800040002401e24021845040c811580c045642118080c1800c00302d5100764209003810b0361551a41070204c10000125021780b03091f800c002c00041e060303800030121012034a4405c000480192240e0045031190f1022344142c0c0d11039210a02161081d03021f004440041c10200c03001c654418022401a082c1c1d07200501c0b01d84a980c81d0917100003d0b0300e841c0241081141c00e031510392810340c1c03150400e0700c2031700825114a810600d401004100c062000000705401c04086451000654542142c15650001210028001181640204820305054010115808650400141400f080c0078110b04030340c010740c1e040ea80306454038207001c040c0c5619240ba81e04003030985602803406000b209810034501c00c1a00241c104407032032002078144501a410356107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 9392525 1250 9391275 9391289
    0x180a0605070203130e0103030512060d02090a05070f020c130203040309170703021c0c150516050d030c080708041205040305010e0c040b01031e020a0509030303100303020d05070506130309 82
    0x81d0600c804003c1d56500109180c0c0c416a0b40e502000c03d051021a03074050403240e1658a0078601081800d807541d0441018086540000b1a0000ca0300140d07a00000d6600c180517a41c00080d032450030002c020000340030510b5000075034102403038201080d00d65503040c4080c0d9809030720241c0c0d00e498a203030807107180420364041041c0d00100c484003490000301041003004c603402111140340d01c4540312030040b5480003142000300401028502008400e06014005981d0082802c1c41c904000a05101c4031008021440859060b0004094a26255010300c580361520b42c4510380b411140c5091803002d4220f07080030f44064513002c20b0320040210700f84a1002c036406141c0c400000e0242c0f042e45a011503490010000107403040e07040c181d80911a5219104000040170351100d4031a40c8851005010025800180110200301041280b1401a00e00304011805210b0800581c1c000624505000b4200141d0b000c8000410500300603100c08144009059904498800c0c1b1000c8100a241380550b070b5480a60f009207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 9393775 1250 9392525 9392531
    0x40507020c0a1d15011808030306130c0f03091b03032a050d0302070c170a03020c0405090a1514040807030207060212090108061201050702010204140a0803190903020a17010f05060108180a06 83
    0x7c90b0004001c0b015600a41c015100502d0450002c2403032010782d884d8010300380024140300c80209505110b40c110034a50f50081000002482e1194180c80600850780c0083c0d0108a103004aa00e42d0780101000c070170715981c4046210b51000d00c95440c0ca89a1000c2c564040c10035802284800902035105207220042c0021a401d007440c0e500c0d08645c0351281080354094005d0f028880c41c800c3d07682881e0081130701c901030500240c1843c038050b81e195100b0504030078ae000d8120380c0e24544650f00100011459005600901300c498507803a0783d1600a15294094001c80c045400c4410480300804000e806e4078480002402c0890882e51204041180d118860803481041d40c04d0000b0302042680650080040c0c07126010340d0741c1524201e406008010542e442040e2280c1d00c100580c01c3c0d0700c000e5850191001c005403400208266903a0006419500d280d0030103011801940e404541944091140300300c0e040d82c14405002d68505100080c081072801403a16a243c0078a5244081c5289d060102d11100c0e90702450030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 9395025 1250 9393775 9393779
    0x308070c05010e0114070206060102011a0411040801020703020c091f09050601050d1b11030408070605030c0c0d0305060103050124080603010e06010906080705030708030406140405040507020c0a1d150118 89
    0x2500c0c960025031b080070250140c103000c142031354818045d070480710ac480c00c1304548050782103061100a280c40f000404004000b4800400c404a0038002030044900071b50080c81c071032020b1000c0000055024003101c2800100c2a04c502e002041d8a40510885403a81c1001071a40d68990058030940300f100c070924105850001101c80264407041188441f800341e50750341d51060300480e400c90762441580550b03940d5901180c0304000040c410401580d121460351003050820440c040458500b14802d03591a020035190800c11841d0b50b8103100f100e0040840c009030000700c00890315131258060010f2110002c00c1182c50010300700f80c60035003101d806101c400080b07410541c0d4510740031000b0000e40c05120500e00440c4000501450002860416924000003a40c80c0600c1e00e08107a50698452401d03c110000501001510f503a81e8800c2c588143c400b07801a20710141c03900104007000060350015800000c012030086050b2540d80340700c0d03521610551100c0200340c0070030700503124412032612110b20748850040c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 9396275 1250 9395025 9395051
    0x4030602120a06050a12060207030207080607030c0215070507020909190b041e020310050709031401150503011a0d0c050402030103120201050901020a080f100e010b0a0e0405040308070c05010e01 85
    0x40074802c00e1116401c112440d10385040100002d0f01c1d11036148846010100b04000c155250300500040d4400d00407100940c3e62122500d05100c002c540c08004259540c0c1a003121540610074140f91400d069100c1134a8a00700001800c0da0149200103405421107000142c5410000c1203200c0c06124003400c0340c448091149010715071000e088804490140200d40301c4c4806005040c140441207074001e0241405940a01c0c90000403d4010511000c00c1030f442ea00002003036040d1010494805030400100e00700001521040c0018001d600841c0aa85040e80c0004c86500024222403e0740c42100d2052240c40282417803a0301d02443c0c0c01296110740300100000c10004150b101c9141c0e046190024487c40d62502450741c01c030702901c00d5100c08030f544840003807981808101a82d521039141c40d920480c6035190b0881c500e212809800021051a00155002449800004a260f40c000440b800d02c140d02d017995008005c500042c0c082d00074440b142d00c110341007103002e4101e82d14800324034008101001c03524003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 9397525 1250 9396275 9396307
    0x290109060602070e0103020f060c0c06030705040801150b0d0f090606060504031209030b010303110f010501060305060f12070501030b0d06090303290102070b0903160e01060807020d080a1104030602 86
    0x1007040094800c50340001480c0810700900343c100c0f0380041c02c152000b0f8414082c004541d010005100d06802441c04109099aa0354042c600800407580c900d6212410070b84550f0031122070180880303440815203402c0082e240c0000458407121020300380411010105500c240107005540401040c0608000c80892840ea01401400441e4001d8121401e148000002030b00c8003c214000540903a01c3c1c40c005202280c000c035a0001d1161507041100c00c2080707001242401c4400c280c020380c3c0040d4803082071110b18605551140f4440308121584980c1b40c00c1545840e41e03c1e1b030644100307418180c490b085d8103a03030307a00c8142c040c080c1c3d900100b0500409050303245c014014403682506520314101c500480791441c0070038184109445040c0c00400b4000e0501c4081c00d07ca0b0008128254544519506d05600b03000b0820042c00a1602e40c40e480c101d5410117001811180c03006100200319800361900b8402030b60301c0a00e85030083e00e00c040002e07543c006410098058443d0b504041c06880c0009101076150001312 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 9398775 1250 9397525 9397529
    0x3021201091704030c0501030b010c0813060212090609090702070302090903030601030c030207020906010804080d09060b120303100b030a090b15010e040510030201080603010f0c18050f06040329010906 88
    0x42c406a100d40340391078240000c0d01503800041c049107001e040602042d4000c1c0d026100c0140b050505081d40062555000c89a0344001e03074649002050400070071009404201c09410380420642ca00d0400d0b0500010074070310f0081050252107000030a0101e2010b83c000c0c000f58000d1900902100d02900d000e201d96a980d9100380c0c0d600e40042d117010400302d040c900c244250f036246a070007040d80d00c854950030011200260064130a0f00c41c10020040316040315020320502c07040782e10883c0c0c0814810035420810800c0d28070711941000300c0d0000c01c01c00c142e0107103411074201030b548141100d03a102c1d101c1c02e00070f10040182c044014021211003003031243c5040754411300e4540c014266a903641620001007400252042a10038001d8100d0707030340301800198045c1d4071259010301d001e0000104a007005400310300b5652201101c101040b05181091841d050031296440503003025554880c1802101002c9038040c03182c0d00c0050034030892155000303800e5030340442c2d04521813114003c460b0b40b540c60b0500d400060010b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 9400025 1250 9398775 9398783
    0x70507030b01050a030305040b22140306010e01030b01032d06140a060311010c0501090507060305061f0507121101060305030d0e06060306060607140601060c020907020f0604020f0a0302120109 84
    0x100c00081d4a00d13044c0503a8082d2503240c0d45160615213001110324040c0c001046c56050040c41a5094418400c001d020b10002d104105c45200e5a80d100f40c18141442e106030090f40d102a83d4000620218860300304140c11240c0c44405220414120700d844541c84540301d011485800d103207a400340c10f002180d005010040d107607072643c03c080d4803400c80840884a103440010000008051510070360f6019a8115401c180a20004100c418066903802c2c1000081d81004012950350301c1449036900302115086082d0111314004000482601009025409040002800c00307462801e11a20140b01790204481c2044800082c0300b015168601240c49ea0882424034003003a19040d1901a04030000600602445000c0d0240c03149840314000e0001952201a0541d58101096900c50054004000d00ca000340071070b0b6146d5407895518410082d0504014000400315800030004c3c81c0341041c0450348542080c4d0464241d0405188000401c0d009074090384040e6101c5c02c903400113040c1c0e42064004036810f6100d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 9401275 1250 9400025 9400043
    0x40b12010f060c050a0314090d0503030108070501020a030207050d020d05030a0801050301050a09030c11060403050d020604110a0e0a1a04060305010207210203030a05040503190c030e040605130f09050307050703 92
    0x4a4008848030a1100e002801545c07058000d10301003801103046032483e0100c0c001e014a4180c1c04008500000f114200444981d440080100006001809240090f00092000d0403a0340e2207500c0003565910603028140c4180e0801d45550115501d820803080e986500c0001e0300d0300c0c3d0360755020207000d540703007441000d00a50030f00000810344c440c0c500c00c5500059141d15174001030003003600c5000075545042011b40d04604200720110114004100c00c4402224035401840240341510b030068070400e0b8992200e0045007541c81c1805040c10154103280e120300c45080000d048640300140d006000d8010101039046440c207000030040c4403040d0010328120b405003110781c003014048030050317280c0c00c003050845005070000c0c40482c0700260b441d045150058003030030403641031205e0341e008564640c407021802001320344000071160800d134014030040c1c228081114200459486c0c800440c89203551030190201c07859031640b86000103401c07940700000b003e0b0064200d0b5251501c45c90550765401c41d0b4013080d142c4e50300f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 9402525 1250 9401275 9401279
    0x903070501030e100203060d060e061510050313050109020a060c030809060c04060c06020d0c050d1401080705010e01050f071a011a07031d190f0b1815040b12010f 71
    0x4024000c840e44030903654000c20810811004c0c2d10b00a4201500b16a4071100004280000c1004d070300400040d00c500402070121407c00070306580607100304030b001074011852140e105000c150424180c80d80160805803400881440e864560700600b00078000035130190070761a01003446940507292034840341c403036140c15020b0384594220356610541100d442081e0300d0304000070301416114180c0f0042c4107100d0310700541803082659a60b02a20120100c09001641c0401c2450f1000390501441e2002108515095242d5050442041d01c0310103500816051208404131410316912440031948564110b209068840e62240f41c10365103819210200d0f00000c00307034000441c0b250100c802284900e42c840c0c07c2c00d031606655580590703640350381700941c2e8010442c03500da0321000c0e1200b41100d141074212200c4d90b26131034180041c100d0052203603000a00c5a41e8140401d490410080440c090043d000f03d4a0704029580881101d03003e200307079044103e4206001c52061001c0000307504490695084da00c10b280e640e9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 9403775 1250 9402525 9402527
    0x10e01020403050604021c0c0e22020904020603070903061401080d05030c0d150b0315010216050a050d06150801020702040c0507020108040f031b0b10060207050a090507020a0c03080903070501 84
    0x406680000b43c041d8102c01c02080051410712003a121042c11903440c401c0c6054a41c54101d240041c680c80f000504038800308010307840781c81c244000c0c548041106ca1000701c84654003c10300441000307000031300032240000810080b0380604048401117601601c00d1003000c05850030305400f46000e01c01c80000c2c1c42408840c00d1454000c1055034840c0502940143c14400440b001402401d00d03e54490403500c800c00b008101e0103042d50003148140714140e540702c07544c06420002031800c0780c10100740010440b101014401617841100d01c4c411585c04585031100c2102900b03015004180a8440900d040f451400014075185c0c19005050315900840e02040b09909030f20f42600c0500c0b40c050000c4c002144600020000383c40d40c09041c031110b010385805107507091801c000c0198040341c144117441c40c44104041004815541007204003400341c80c40500840c5160001040200304640541d540654a940003c0c40051003088007100039038102c080c8106055880c03e0001c42a4003038507142c0d000b405003000c00304d815 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 9405025 1250 9403775 9403777
    0xd0f08090624060a0e0909030a0f080601050d06090203060a15020a0803090313031a1005010e01030c0314011716031205031506040902070302010f0c02030406030b010903150b090703050702150405030d1d010e0102 92
    0x124009d610f40b040f0140511404032114070004200d6410b000040c494444030140c24481c0714061700c0d4130741006aa83c24175804020000d02a907000c501700905001048441c107501241e01c44560364455000c1c0d03100d4035034002981c11401084611000c0c10007941001040c07107500c0e00840692060005034071080e0302d810882c0c0500d4440d600801e800710f44004412403c552090b8040030320710340140b90001d8601d484d00300d00ca2000e0302c02c2c2c2c000200e0510200c00010100018814510b180180c601c03100741303107403a660300da1011041a42101c4144136007c4009640220f000f20940b05200c03000700110365942e01d030301c10080250403240b800d800640c40e00c803080a0440092240b0700b6110251b8004500346071512000320050408003041c2e41c104104854000005030304c001c903400080a000801003041015402030060f210401084401014107040600c14080e40218481c1020360148030600402e55890812600d1441184106000549020700300103580003019541110003440400900070b94070b540b80d4803400d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 9406275 1250 9405025 9405037
    0x1b011202030105010905010c05010f0509030a0e040501030f03080903070503030103150c020c030606040c02010e010609021e070c030605070903050307060606080106020307080301090506010c02030f0d0f08090624060a0e090903 98
    0x461800b03174051189602955400803840d10490020401030f0041c40100c058640c296070036a050f500201c2c50421f0150400c5030000100801c2c3d80030481136145403038224400d10015006010b220300348011070320090f000d1003102c40d040d030400100c036030741d50b920b107480c1a03101c0342c403982402c080c0d00c0c2000800001d0700c041186402070200070014101d86e00c80b1400c100c000c000c05884601559660100c40c1c150310000c0c00784030000c1100010040c0c9540010b85100200500d0f0344600720310303041c1040000f0000e0302c801c6455085d40d42041c0c00054542c2d40800036600e8030071540001d07000b07110106044017008815001203055071155650b02c0c00d90390f0f031403100303990303902400c60000c2441c02c080c00103001d040030507481560f01c410145801c0c0ca05101d50380109040c00381c041e10440c0c0940021200790340c251741051506211350090718114101c7c1c6411705c407140d22240c000c2d2000e042ca100102070302c2c42040c12500b6010b0207c00003070026035100c800764406481094440c03169030180304564005102e1001c04004d85076 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 9407525 1250 9406275 9406277
    0x503120609040b15040204090903050c07060509060415020304030816021206070e0111010b0a060c06050105010503040804050f0f06040b0a08010e040201020a03081003060f0b040e010e1c03020c1b01120203010501 92
    0x503561a40c1103240d2041c07000c44131031a0015824000001c0e001c84a010301002c1c140170342c440c00e54905461060a040104640000d828401c0c1000710101d0b58680c1d40880f011101d101d80b80800c91580100101e041d403040b540064140003010520548446d5241d180c042c0d001e108035001442e20024245098845808881080224020f0300206086500554103001c040701120300000307450945100040545045800c104001040041c80004002c0340e803040501404090800c1800d40c0303420758422030588a54001c45001d02d0880401000035110f020307520250440c012f00d90350300d5503100d0ac90b21013a50040240072000a14000c000101d070a4080c010368040c94043c0e018103403845613518142c4841304094440c07030305c50121840c00400301e9080d214100d0311514555001c141c0b00081e204001c143d4240c003032840d2159150648d00d91270804005070342110240000c40241080400007030030b400901130701444103041d0050340c10510008440c03003040360015009813240b908103120170002c80304070f00090103414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 9408775 1250 9407525 9407543
    0xd0914010905151e0a08040302100b0303030103080a052a0114011406031b07030206180309030703030e03100207050a0303140f060d06180506060a0b0a0e0f03031303050312060904 78
    0x140c920542c00e00200080d000c2d130f40460b5003d03003401202d020540d1000707108030001003003007051008240c1c1c1800b580303a0340034804005000240060f80029181e01c418840248088400507030311032024090010340d9040c1c8000c80c00da03d0100c1100304c51307059035403003155504001d500c0d258140f00308500305000c29040c0d845940c3d001c900200c1d04418402e141d400501106400342070001c1c046010702059000302461072280d4058080ca05040141a130303c0c0d42071007800803454000384a40155518009a0f090840380c1500e844148c41020b680402c0c1050712400721117880d00c0c0001429000c1c4500001c05460203071281d0343c108015805c0642c80c10407c02d095940071034002d03040c00411078070b103004120072003094060328001483d07010701c008a03c4540c0d4490000c50341e94001c2e8080040e1868078004801c000c201920309035241591418000b414100c4020403280705800e28211403d40c2d4a040050b10400c0d81c0701144080d40750b80300e040c00750f517981000c0c5c61518640300c49000a201410080d41c00c50041c3d61085100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 9410025 1250 9408775 9408799
    0x207050402070f050a11030c0411121503030a0206160201020301051008070212030114100305060307030f080904060611010c09050d0303090213020313020922230d0914010905 76
    0x1010b0740c02200280d5400980c0800d6001051081c04500500c6202c0d2003480b031035000710400d0505200e41a11440e1040345407102098400c54890110354000360490703440303500f40d5594a0100720150580c580c1d15014800400c6d42c2c400b1540000b02d89020310039841844000c0c1c503801c0d008900b41e10090180f01d820001c14071040c3d0080c0d002e0750703d02d504013482d030043d2081c00c680842d0310742c1d0326082640000d04554111064910303d00300020010b010385100c1c9030a00280c500300c07010070b070346441c1480000c0040c85000301c1001482251019560030290080c410b02c501e580d682c6005104001e00629000203520700569200058003664485040f00e401520080500c4980d807804e80041a070b0410a0360001a0418008000ca8031480214414a01c10522003c42c0c01540140110306000800c490702c00903407842400841c00b6061810701505a111243e10305812004441c038650001c000c00525040c450280d06010b044e40003440d103030903520041050009020349100449403001144286034100c5807880311 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 9411275 1250 9410025 9410029
    0x1060207030b07090504090807060e0706080c0903071707030201020706020a020901090f09050a03050406180e060d020d0b090105060f040207030806010503060a0f030503030f1308030c030709241e020705 88
    0x2da0760300042c941403d40d803040e9148003040548512502c1110040d03400580b075810006180b0032600199102401030a19504251015212480180003000040d001042202c60f581c5d0400c5910042c00b03040043c0a44401a00c050940d28449030100324003500a0040c00b10384a0305c00a0702e84121500100310b0a05a41303484d140d01c0c010002440403416054503298008041081045080c10b49842036640c01c1c0d4907881c2c08030041214004e00d0085204484104007000791520018826801c5001107542602e208400c5c4002803903190030705d8009240c40e018000304986c060040d440f0610401d401d0b642441d081e011042000100d1080f20f8006004c504014007244540d489040690351101001e04500c000a40741c0050300f5100c51503500407078070350340000b04000740000040b0f006500540c01c5c800025809075070359100003481c04001c0c0001881a4040000f0303400c1442540180c000304841d00d582056a808103c10310000e41c000000000840d559803040a12000d00080d00542542c0c541e018003055810401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 9412525 1250 9411275 9411293
    0x3040503070f0201030b091003030f090501090314190605090d050a05071113090803100603020a02030a080408040b0304110f0604060c02062805030106020f0c090705030402040603121808060106020703 87
    0x500fa4109039a60380140300d152981c800c1345000300507100140010707070318620300200105006503041007048a2820108600d90b00000c0700c400352640309401d000020f10750303013540f4900403888001d00c228a6041009809000d803651241d8001e44252040c1d0b214901d0328182031300c682c440ca0f21204001941049814086609510940d012500040405500280704007044003a600f0544080c6d843e488004184010140881520002410107050550500d282044065203d0007030185610510182d08009020011400e00322409080407900342503d07400c1909086840d805044115800f0f90740d44442c100d083d15088042e503080f9400c1da41c40c00c040e810316070300b4042c540e0400d20b12401b000904844c43ca0011078050003580d1103441d15540d179a1258946400203141c8106040d62000540184002c08403030b44424039082d9000d0001c0c200305940c0d03143c80c40070130000c0a81d580007516060310822030032500703544020200a4580000000d0000c140c540160a0b00c520080c803814015a101150810006400107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 9413775 1250 9412525 9412553
    0x10e010501080411030c060a0302220332030403030309050d180501030e0102070605090c1008040b060105070503070b09060a0605040203090601030f15050108031902010218120102040504020d06090e030304050307 92
    0x5c0c080c3c03101c0e07103a100007048072904200b00440107c1d0300400d140e1807810000740050302d1341400d042400d030001c2c515250910f0744405c40d04141c0e550603185101c40c0346450f119160141480610f002c40e0380e91a81d030b050080080060440449190080031400c00034140301b1035085807910419040f41d0859840e00006400801e0070750a07150081d502400200b02080303252045901c21030007400a0060411079400b04142007585d07508401c14444050180070109032010021503106100b820480c0c4d8809460070054078600500c6001082c8a100d4810400b1a62001c150a40180740148040c0181c0e0348900410040c1e0004a50341405a1300c28001003000c907503c0f00300148031034055918004142200700c0c00b40c040c6c0c1c000740c001c000e245e03000040120031100ca00041c2c048800540c030003141400d5003003045c0b404101100d00c01501c51802d030380a0460290b03081d0b044800030b0100810442d6140907081484000d40114400c9030342c80c6d03241c9050040341c2d03440071048034800e903800006149000740598807510850008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 9415025 1250 9413775 9413779
    0x905042c070b0414030105010503061006080c0d05101701020a020a0209060a030c03060207030e0a0509070e030106081009020f0102060408070308041a01120b0105040c0c0303050405160303090608010e010501080411 93
    0x1003000003500010a401040a440d41c4113901e000902003100345030940300d040c0e200d00c2c003d51040e0700b0401c03800f00800b01c0e10141da0551134000300c20303210500c130360400d03000d19009503428a103442c007880311042005146a00325280e0403c08018000c2c0305510500b00d00070308400c5030150300519003c80c01031030725100d450707400340c0d000348540714042d02c0b611603107050b001c5504103d4010382d0000b0b0300c03003d0580100442817461403c50380f8415403824000401c0c2070190240c071203030600c40109070043c007507038080d0000406442040100c81ca0048801043c401130011030714141d005130782003c078642d200d500c04070303600e8072803600580d004d4a003e225540494010000030300951300c1045c3e42c0307a030407105182c1d50002030003010742c921803080c0d00b40345090403203940e01c040e40700b548a03d140c101d59440e81c135040103000c038941e9058200010107540324100749090a0f8810448030070060a104d0200815400c03070500400c0d51425034607009180c0c1c0300e44103241c01e41c00030700603036021a41e51030014002420341090020300f0080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 9416275 1250 9415025 9415033
    0x4020403050d05030702010b0411190e030303241827030301030309050405240607260c060106020105090c130e010f020d0b0604031707020d05030313030905042c 70
    0xe66210030b410015060a0100007410001c2030141c0d02d90f09010302d0115a1003110308001d85090000d02844501c21003040e91603540195081c04021806555110442203014094130341e24505200c01150318844040300d49071242c82540c2002030b0f0300385400c4580c5402c06400c100ba9450700c0380e0304644c0355030150001e1080e07103c20104a64010350800c0c006503000b184a911014015414442044261003005000c0403220070400d0500c141c00c3c07025502d5030003040d010350f07030300da07a030130450a00071850459003120264800c04140b548810141d11001410243c1c0f0301300c150343c1e4590f240c00081f800d0368400c0d141d803441035000705442c800354504583d40204032003411000145240250703900b607082d81c082548046100d980402c400c1048141400307071010710a8116501d030302c0c160131942c81440600c8824603c42c0e200c0004038000d070841d210640d0303080c0555048007c0306d0300c03450080760041a000c5645030840c00540e0281c1b0010307030fa007418080d00240c40c204602131010444851020285852703462004102441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 9417525 1250 9416275 9416279
    0x2706050907080d020601050103050121020105030709030606080c0f030f0a080a050706050a06030309051203030c03040f02120a0c051f030c0201020919031208040804030609060902090708040309080309010903030e040204 95
    0xc0c20071943d403100045401820456140c0000942100d06c141d005980000c9454103020b5407058807010808540e9090804586945aa60049a4061981d040180034034a81074000c40e460b0800a1840c44030442140c80e400d00c40c10602c240742c0c070760b4041ca1f52125642c1c0507001c15000641a40094100785150b89800c0c4d0906005072144000c0e24005c1d100001055507844c1c061060550140c2c1550241405903030448081804900e0f455617880014607900c41d5190100104041042064075142d0b2560001c061038103503210f0003a800d41390403205808541000c80848005054100100c40429030409101198501c080114040c3d001d000c0c09080d07c070842d5030170084240c1503902c2124604510661280b0300700c80d036056103082d042241c0c1e02c191b41c2c1c4c20702080e00300300000100b64000f20b0701640c0d4010004141202c052400b48050111343da4000d40c01002542003120156000e00a01e21650083e5668580c5550324040c903622440382c5c94070300d0b00084041c0310500109005000131480881e001e400185416 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 9418775 1250 9417525 9417539
    0x203100c0311120402010809030307230c01020c030315041a0409020f0a060e15030c031b04030f060b090709060e010521010303020123060a05010c050a0212010204092706050907 77
    0x343c0072403880803040700b10205100541d40e2081c0605d503c1907040d00118958188400064246d04140000034501c01e034001c480b203050034281c000d031800394101000954031017018082c01a142d030821140140703814801003442702d075460030707014901001c00c008007002c00c000c10240512000d4001484186e822a01e2840088619120f6807001d000a040ca07607141d0b822103c100f010489140b06015101701805d0041c000d03c01c5401694040320f030021000d5207059060504610b5514043c0a10340c000303050718801002d6034052003c00e0f00081c440c181c044034001001c0c0c3c0c4001007903070b0b019130074050040041c070308000c0552154012802094017801c5c0c1180d440c0510503110060f440620b0903002140142d460f98845440c920170b1001164103229103e0f9020300c1498200040361410f4164800d60b8100300d5100029814003005024520301c503a0080c01e02d41005000d0001309020f50b2140c440c0310026860202c81003407400b00f01e180e0b80d10030350720b40082d4800300b81e031529501c2c080c00c40640820950700a0440028150b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 9420025 1250 9418775 9418777
    0xa0207030e030d030c12020c0705010e03100c050d06050103020c07170102040306020408010b0405090607020a03030c0905030a0f0203070603090f11030f030304030e0301180807060c0212070506040b0105010c0203100c0311 96
    0xc41c032554042010010254001c20000d1011b220b000991300601940200c51800305140303059070807c0c680b150700c54050300e0003e8035011300501c1d43c200ca240b84c000011043c5031300500914405000040c10704c00f05980f400118220320900441c071856400c5900140401c884610503140f103495100c0000d402e203603c17501c51004a030f100764003807500c90b9903034a00305c0600d08050003560342c0094500090240c5203045d00010351241d20450005003015a5a90340c400f0b0390340610031000c0584030160498203400030320f02e0f00390b8013000410800d9110380300b90721001039030b584070340200741001e50700c0182d80001e021690380b00076020071881181c40d4180111400c04403411001c00241d40718a007e952030b04001580300701854215400d0110820076502c1c1160700c0310101d54004100c98030380d40e01c5840001c030044105012400c10035408010b040600c4000344034000d10030000b541c40e025900550800d0007a0740c1e036a006503a0807030051802909a04698032024850005038001008651182030200707821100e50780c00c5030070b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 9421275 1250 9420025 9420043
    0xf041a0a0b10030524030d05090a090903020c1513030318030803040b040b010812070b060411040807031505090d0c0602120f07081605090d03090305060108061f0b030a0207030e03 78
    0x83e40d1001004600c04011301c82d60800b01707038000080348809544000c241c65403405440e12003402030000d01c8445070b0b2a0110300c94024140c04108100c0d010852030029141e50b50310010318850301e42091401843c906040441e4540c0250740d002906851540e6410343c0c0142c80f8003807004130010344401c00000300f40b855005502c51849110070703021624051910240c20301d07041c1c0040480e50700103100c850000c1041e01c2190711a42d0440d426000d5907460b03500040140c000450701460044010900003030039400042c1200a480c400e4114568000b0030240d40021940125440c05503984811120741100d40690307550080d0034002c4d03902615094031600e04210f034503025210307540143c60b00030401c15001e82c0050303819003209400710002416050850018442d001e99884c2c030b032080481c42240c50802d07000e003d0071002503a000082e01d000b0341c0e44002d800e440d01e20840b40080000e494440c4940b41c0100100c2100603103505403c07890840c3c07144840c0c200290030040c070031801d10190000c0210595010004924 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 9422525 1250 9421275 9421277
    0x40f0608060603070b04060206010605090d060c11010b1507060e071703190f17090a050105090a05010b01020601030302060415090213060302040c030b030303010b0c01020f030405060105090f041a0a0b10 88
    0x440e41851403d141c0343c464540e001c500041c4040c00140b10b10b40e030100700d05046170714525009481d13941c485c0000d4081d54002134028a22031030306165000950300440075035070f190a650000c00072114104180220002c070007000c203540020400c800c0c0001459940800c02d0303400010101c410b1903890f0031007482c005001c0c0344606402c2e0320225180743e00802111050102030210300d0458030311205c0b0003024013005000013040f150800e03e040010b09044081042043c010741103030082c0950f090240541d9201c241c0701c0f800380d07401e500380141c4a940e075000007040c80c100ca5043e40201020307661601c0d1442c00d215200310511180f5242c1c0354001c0541d03a0786020b0100f0000c18600001c03028a14030400089030480720329a000e040c24151000191794022081e04d04440590684684d08c40d118441c040c020720842c900902e8440e004402e1106106d40000c03090b06a0780103654141c417545810348080000042110001c16800c02c09070348003009031065108a800000d210070100741d4220000001e40082007141d0303200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 9423775 1250 9422525 9422533
    0x403140307060f0605060304061a03030d02040e060603010302130c020a15050906010807080304090902060f030117010b0315160215011503050c0c0d0810030209010b0a0f02010c020714040f0608 84
    0x2080c0b06192107034250301c1e8101c030800c000081c51311001c1146804002c0c0702404291380c070340d0641d0f1520602003a07228050710040541c1d6841c80781d40c00680017034000e030058450344186500001c807682840000caa0682c1e40080c0350820f4107840e251401c02800b01c4401d55011030103224681e200241c0f26070b0300510b4110184002254501c1d02540f05803070030340142d0107006160320240003082902008000c0720162005003001042d1815640003141051007003625042c0070350b400000000c0e90520303181c00000f0300c1d0030b803500a1110900b0b410405984807241050400d003401c2c0400445c103d9540a620584010941c0c01615a030b045111152021044260f01481510709030b82545a03080303900d0300c1000d50001c00d00328400e080c10803076216a035880040c400f41a06101402d00032030145180300304908015907005000482a40e140c200083c0c2c0e0760000d030003480c082289103000f61001030041c0a40c185101c05075006000703c91805091849894031840c1c09500a41e46a0090410b40154020840a880044014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 9425025 1250 9423775 9423787
    0x816030e03061015110601030309180504030e040b0301090203010911010f02070b03040b220326040b0609070c050102030a050601090f080c01031505060c060a05060a1d0702010204031403 81
    0x2a16100103104000c1c40398205400300a98640c18400100a80780e0618070302540200c455401c0e1400c5201c40803116180c49080000410542d00c0001ca8040d039000e4030700003504901c1c03e40300e5801e841059800a020610b00c9034400c4040c1041e5000100c40c0c04007d0000c00d481240343c0100303003103880d044801c0c0c80403103508083c00c415503001000b07074804110318402041107615080c501c401070b0001520041c9481203400100391808a002c3d60300340860840d40b42c4000c01812441c004d00101c1030741c0990034406d1182d802016882d94550074651040e9005803000381669240d008008100c00700600e0081807200d03a05003080410720900c09540b040805180c000f419081103400900b652600d588039002c00c042c1e940050000640206201020400030300340440c0391940b4041c5000e0360307040740d04881c0e0444004101008026000070b0124001d41c40c1d10030410a13a05c0d40030500c0a500264002c2c01c80c212040718000403031004103410300c0ea00c9812072000500f459100d41d51050740440380c00c028607a40d840032a032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 9426275 1250 9425025 9425027
    0x906090203010b0a14040507031b08010f05010525082208060109020f04090902030c0607051506060a0207060c08090307080d08060a050d0b06150408030c240c0c030403081603 76
    0x9040070543c000c8454101d2203140205015500c8195141240981e803500040341d00d4a0081d0011180640103d800460f00d122100c0005c06009091050302111850180c0001c0e80c2c1d405141200d40c2d0000e0301c0c424400340f0395007000310b400605101100b03d170421400c1020452500001510120340f44070600f0710750383d42c2d15050400b450424180c00489100c0c0c4100001440c80c49000119811038408102c0070800d10040d00000e414501100c06054001a00240d03403c20420046002845281481508000340e1550810302000f80500984200941d00002e414042e041c081e40c00b0351405407080c0c1d001031500801c4008242040516484424254400211100d07000d4000c10f10319030101c01034626510003031400c00085c0740e0346150900600104510300c082010ba8480e030910526948141c48826038442d510340c2040c1e5254080d0b04020b40394012614000c1100c6074020a0000c2804040304024031611070302e1101c40c141e442703400500170034801080300000003250742000d8503c0b001e50740700000001400d030074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 9427525 1250 9426275 9426281
    0x40608030313021003060302060f09091509010b0912010f09030818060402040e03160c050102070603050405120307050c0d0302040306050a020c06071101020c06150102010c14090607030c0204090609020301 89
    0x4204265041401002445088007404282481d011220104a280085800c1d4010009030300b010350048070000c0c400081c044400020138640200341d03010062a03540441040f40ba64070b06032540c0e4030140c42750040003800880405040c490750014070070018185032441080c21030301c0c1084442d501c1a20345080c00c060540201d101c5500a075038001010284541c0486581c4401008000a12496803202c0c1070610a0003001641c02000010b0340e032460000460400c07194081542c46654014803c202d03020172224031a02455008581c420010b120000d51b400c40f04400da00001c04640c1080750078400c0c140202810801c0d070140d80c641e91030040c1d540f415400c0c8002515002481032403202c3c0108410714484500003246940025127140c0003094192a010050181c450340241c1c658600ca120140b1003814100d07204680030b2070b001d80080016054008050380c041c0c49581c4070348100c0d4014040305c0c5282c20900018107141d8403925020a84402c03990015042f00d8020310300340c4149595030355000c11410244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 9428775 1250 9427525 9427529
    0xe1e0601091a130e04060504050606030a020607060506030c0603040602041401110c010f030b0303070809100206010509040803040f080a020a0302010609050907030f020d0b090a050706141b10020f090406 88
    0xc03905210041c20154844030001050107001c6201100007000b14402020300b0301440a880030130703d02a89030416040c80b00280c1401e49003900c1d05e01030300c8086400c601e000181c10300c40030703030181c8501e040c00303125281c01c4000c02008100326018021592111040e07614100250300c9144200c00c010303192800e040c04035142501c9604641d0501c02c62070b00303400980303c00045980b2200c3c02443c00707061011600030100e0161410020054140c40302080c40c0080001c0c1101508003c402174034038201c06c54940608036520b181c03c2c800d25403c140a00e01250108005000840d80107010f841407400b20072442c2d9030720440350b000c443c6000040e0080c6904a04240d420301a203c010100c0344000c2c0018202505002e40382c80391840b0042040c841e40711150215140c00c400e840010ba0402c076280041e15100c2503082d1241d0301000c0803203480c0242c2c00003007600c9005901996082c80c0001c03013203013022280744180c0c03403651300600c10503803500c181131556804a01c1c90000b0301079031804040303e030303251a030300703002d02c401c6c0d603030507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 9430025 1250 9428775 9428777
    0x40302061b0306060f031305030a030603060506040614130e060a0603120216170a02030a050303040c0b030c09010c050c0a0b09030f0601080307060207240204030b060d0b0c130e1e0601 80
    0x80083c40182d07079880d41505c01d1030200c101003c0d900e48030701c00c420041003102003004046000c0071801810040c5c050344000112401074405002640d42c000410040b255a809070206e10a002d5034217035000e0500d00380c00c3c4030766903074643d0020340d001841d15814640101100da1400664540a00348100301c840a20702c9031a01450005000322200b400503500a40b0b2a070003500310f0000b0307054048405800400010600e540c000c1c2c00d682c9499200c0c00c10301c0c1c4a900880e8244c460201172180010102000b004680c4600392004845044c42417202c011280214500c006850a00c034041c030355000b0f580c0d502d0080b801081301040c92913a400b00300e024581800c5507502c030402141c00010042060700c49c00300444a2680d4030620040e40c81600c0e18103420211901c551502840f18000c4085584842c5e5900030300070b83e4010821708407596584800c000c0019111100104008214000b089014640d00007500c840f0a002401c6003c5640b84e41820482c44d00844020441a9103401030090081c4c0c041b0605401c2102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 9431275 1250 9430025 9430027
    0x150b04090201090603050c0d020415031514040b0f03060a05010e0711190303020403050708010905070f080307030804020f1507021009051f02010b040e0a0302070915120c0509040302061b 81
    0x3840d00060f102042d2480f4240615444800188501321540c0c01c0300c862000a00d021512503407215a120312030100d25007040040307841c1c00040e054000300c0c640c0100440384444a10206010b514092101a002403036866810000c4101000e18999041c00068800e0080100000d000d40c0f401c09502003c1c0c2b4040d102074140000120b55464100303001c11087c003040d072540441d600f01c0031545000c40081c401d0707070300181280c00341c80380119030280107400c40c50000b40260202c03005c698a40840b040500503030303c41c24001d64410012100002d0290a03407a501500040070101c1c1e0f2a4002c0c00700e140c851516400c0d2a08010000d616003c40c6010030031042d5640f0315103800e404060030140843c0b202c00b02c0546503030418641d0f003404400036200750402e5a41003400746c014044080d130800f070a980da0094040031005402040d90129400c2c515105010030f406c101c04080b60458500b410014044071002015100e61520745400300b40c540380c0c0500030780600d200e0340c01400e6500d06005408039500c051482000c410b48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 9432525 1250 9431275 9431291
    0x40b040203060a060804080702060703080f07020d0503070e03070b04060302130e011a0318011109040516050a0e030f010204030803090f0a0305030c0a0c0507090f0c02010b1503070912150b04 83
    0x222260003805445541c14240f12517212400c041f5568091440d00962005001442504140d0310000c070314000c000c080405082070b102c2e41030a0b42c9614003803170510005801440028000380c0700f900301028515019083d10451030f201c0715119010341c01a007065001c40d40001f28019680d10300761090b0000c00d180d01010310171703504041003081f034800e01d0381801070360306008070200f003001078580d14200040d12100002c022091075008040d42d19000ac0007490b104a2a01c000180042c441200388805070601ea49c4e05454554428000d80e6010307070140542e0b4241c03144812070002204d0910061001d54020000207480386090801e0b5482e040d8a1050030030700d034000c1103100c400690001c042d2034002c0c1c41c1d2125103840b64031240c011621b884482c00c0c0640948614038001404154a030700120b0003800c0d244080c46045140c600c00e0303099481c480c0006411100907004c1340000c0b2064000b65800c44054034100502c10380e540c10014020003040e000360740300140e203840401d0103c254407d1030219401a0f405001c098 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 9433775 1250 9432525 9432529
    0x306080307030305180709140601080709050616080f0d150f031113020a0305070206090a020f090c090607080901080a05132d0302060103060b0604080307031404030f060b040b04020306 80
    0x20280c20001020703d03483e40045420000d0303184d00c40604403400d908407140956521661030103048003440d0300425022100105503a54401c4241360300c150701c1501e0741d0a01500d04020300881e90700150303640c009400406010800990036a00502d55582c49214050702e50035140d5020003100c2c1c010001709126a0401300c00c114150101c00c8000c200ca402c4242511241c003a8000314100c401c0b111001103c00e44001416075210740c25a029601554555080301d40555407070300b0240d5a0340710100040d62080196090310547e141000c440c40c1d1242100034a603061000e00b0001c141c154020400450301d25101050340012035130f000594a512501203d1305219500f45608420b0a0b4903410300050720011503030480300700c4d0015181010702c001c0c181a014a80c02c0c407040c207009440ba0750a010071580f5906182e8003c0144c548001620309031261000039601d0300c9482c0d5826100000000360042401e1414000000407920081c030510f030550290300041440d048510801c03040b80c540d031400c103226038414010f0020319 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 9435025 1250 9433775 9433777
    0x60307061209060609050702032a150c0705060103030503010e0c0307050a0309020103090203060c1c06030503030c0c0106030b0a0911090106050a030c02070530030304080901360602070603060803 85
    0x4103070488000148070071103041c44005481e6540020800c141030200b40107002c2e5000001740082c6001415180072400204210f01039801c940182c10001d62001c000d0142510004840c690883c080002c10f0b45489241d0791140d06110003640243e02140001c401000b00c20188524607034050208030b44646580392100014000380200c848090415648075400c20440e4020f610600e021342c8c004040b6803c0b407600e080981c0407a40021028145082000d094581034403c0340100340c142c175805006581140e4800030882c1054002a0310030a072592500780001c0424028038007503005031030f80c500c08a00403070301f41001803000000100160082000031f00420007158400165080d00356a45404a856541c1d24012031600c03a507a0400c030350040c013100c0c1013002058042c013010a0462101d0354450000c0b05407465503281e000031180981448420043c840256105560070740c652100b02800d503000d000f2074444c3c1210b241c3d140c00040c0c10341c4490401031000310f4040003588002c0c0704610b414000d0f41d0031b01500b240c40b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 9436275 1250 9435025 9435047
    0x20f03030907060c0213050a0605010e03030903030f0c07150507030318020906060a02070f0803070209071701050402030406020c0d03060e0115170c07021008010e0a0504200f030f011406030706 84
    0x20000308024113011941c0d0301c0c00b41080e078118148103100303c0c18652013000081c2010302c91507010808251090425080120a0342d000907001000340d414901c1e0050094101e5005400c03441290042410100d000408880c20401e0b10010342d44854487d0b005140c060100d8413420388408516007806001d07401a40e400d10760603800340d0141c074643c0d1214140b440903850800c094101140c412103215001c94110700000c050102a802100c100c040da40b1510011765031500d0161944e08140101c0f0300600080c20140c004581040c840c0100500e04148082c2d214200110341d5110b00009032914002c00c500d1001c00c0c0f400e405840c150902010300c4520b180b02521203c010340180800a101000003501624941c2c09da441c2d2f181c016005501d08801d00c20010103140c001d0040880c01c0500c0000725a8014181c803c640c4605e03800542c00705900101d611890070f155111500c5540a49024181102a1801c1c040000c545451800105000178000c04040860f400200481c0c000d03403206004210b480da005010b402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 9437525 1250 9436275 9436277
    0x50604062d080a03050c0105010603020c0307060911130e06010503010e0a0308100e01060908060106050301030f03210f020d1109010e100513060e01020c0301090b010605090604030204110406020f0303090706 90
    0x1802030a9501030704808856400049603014002e800d4090540000041441c00880c00082060743e8950606030304a02914030080040e43c820300c20036001a00300d50254029601a20005002d01c0034500000d1a40804950421030280c0384e201512584608010240c09061b08600074002000b107a10281d40e15012000c0190400000b00c022801e64608080854049c101000d1480c42640e140d2201410000944c81940c07914800e00c000024221320a02c19a410f0340d900106540c54500c20313413401c80c4d49040f4500000d8652007160503003c5902c1e6940300d83c071184001d0843c05a1559083c4000030308950840350440f1800b9410000d80764203a03801001102180303011268030b9062852070804032030500504640650405c181c00780031807081d410000004050030242c1c00c540020842d00300341403d841641c0300c000c0c0004201c50050000601030405003008003000f03800c090400340c3d241c002034162140300104180c0018001800e1100c19414045d110454181100442c0346040078880343d540e400a500c1554 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 9438775 1250 9437525 9437579
    0xc0c010e010b0f0d0f02040203010902030609130201020a0b0411030a0c08010c031109121507050706180b040b0c090d111008010b0301060c060b131b1106011202010203070206130905060406 82
    0x313082100180000021640140c421501c9603118000030000b5401610103510601d0b5420016025a40e040201508503a040c0e010301000c10260781c800714510000790040345c5000c00480b215405ea01d041200e80442d900030b00001c04218600450a400c40d601d000701d06040601301031401d1900216801201d9103402c0959046110f4012503d4142c01d048600000c2c00b6042592418020500d034085c000e85501c5000707a03030401c60101c00010114014210241c014030030f015090000e0085801c240708541c1c0f01c036030103c1045c07414400500242c54114006401c65680d050440103880c2c500b8400404040042c3e2400c1ca12519410858860780c28081449083c080000c01e5030404200050b0303401200c8010006000c0009611011460070040c0610444024800740b01d400b010903250300c16104014aa200840640b80c90f034281419000d01140001050741503120400c01d010041c0c8822008142e40d0a904040da601581064540c000366980545811b01c11414801c00f8401038032000a480056000e1981103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 9440025 1250 9438775 9438799
    0x10c05070807020301110706020d0f0501080a3011010f02040605070f05010f060801020a020d031506030e030705070303080907050102010603021309020a08030d0204050306060d0c12030311030c0c010e010b0f 90
    0x203015144980c00d901c01b0b00d00118941040043c04d4000c1c210140240c2030034055001d80c07620070022650709104418069001002a1000c60304045459100b0702a00c1608003d0007080b020040002901e40404000200c101010780c00680b801e1040c1d40c0701025000c0c0561410380340c81c0c0f004055009582c0060841d0314404c580320200002540845052003078600140310090b5a6400107000b508114040c20141c0100016040e2846c841c0c0f04110040303a0762000150b155090480440041c00d1502c074000c072902c010000c0ca0046541085120b00039031190ba00c451081c0b50061405003001040c1e071015040d68180b160900042c2d9625500d4400c1254040380084e00804c00d0000800721060b5510181450000003060100188103400900640700258100c036440e0b1134890030710441d502e00c610007405600280d901840403032506c628041c012402441c02240d01468042c0b414110390060300c0305841c0701c20005000c03203070443c00e0081c6c90701c02c41c0040003007040305507a001084003801c6590030144102144004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 9441275 1250 9440025 9440029
    0x6031602010b1003090201080a0605060d0e0118080403020109080f0d0e061b01052205030d0e100204090b090c0a0e010e010201060b030906041103060103050a030804080c0a0506010512010c0507080702 87
    0x407008100801c140f038a049400005002440c900000741e00060800d00012440178007402103500700c1b04c016240c03501e001f5940c019103005011214055080355252503040420395416030420034502e00845045075110714600c005400c0d040d0304d91090440d908120031000c15182c0101e031010b05d14030a41088030105c06900c00081d10b600c500014940c104009070b0034920b01d081c056100a200304040c15500c5c034800d0340500e56900b61246080024000c1e03008004600d4031030302c1e641194452980c207504131000804090f50040a03a00281c00003180c056403200384428614016501a40064203000d480349000c100680091212240b401c50b00d05002411170f00200e264403d5000500514140b40030a0702c03401d040c0a480e485940a4500f81c412041614915900d4540410940d040340e038010000d0001d9410b644c0c040e100b8010040058518071014050750300310000a2142405052248000d00b481c4d6050804018880102c4039187d94103a1400b80701c007a03140e8103c0200c60b8115040904280c41d610b003880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 9442525 1250 9441275 9441281
    0x109030b0406050106090b0f0415020c09041101080109020702130903050c010608030310050a050102030324090c07120815010818030c0313050102060c030105130608030c0a0c080604020603160201 85
    0x10004001200000800060100c5940f00d2410395886640700c4408968134801910300380940350070050f10050400041010034030000b80b400300350b02c3d14016030f81401050400a011407504079400c1d5940341e150003d0130031541e48501c0841c05030a1142003103080801c50703004900e84c3c405410116000390b58509240742410300420a80307624101d040001d018064964440b26140d03001030ba4561010110640041a54600303182104260342d0181c4c01181541c0c4c0349050030000c281400903402c500440c038540f000c0d49455196029101c5ca075113018150b0317244d91616001c135040c0f80c0403101000304400070b010320040340c100c0c048444c400c000900c1c00030f461761103240c02d218a00a0f0120341c2c0300c1520000900720003c1070044003402e240c0c0b6400441042240da60001a43c458008458080f030500302000140458a05504010034260903080700080c038507211103602e032941d4403083c8000d299600503813548040115481c0064090308107a0050324090402d40d000c58001d000242c0b00500e69903405c0b00c1c4815aa200b54 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 9443775 1250 9442525 9442529
    0x12030905040c11030c030405150301120b0705040308040b0405010e0904050705100210050403030501031202010c02100513060504110f0301060b0315030f01050709060f110705040b060906030109060f060c0305090607020109 96
    0x84240c90341c5844c040310080c1d80c1d40c0948211070044000983c039203000508101624102d413330841402c0400703849540d80c108032000003400f86c01441404d11000c030204242c4d0010b00040e0640d00b0196981d1402d2070001340400340104d000b107100e100154100400100082082d00442d0350a03a00d25400004a0304140d05203d00800315407542807820040205150f0b1680142d41200c0c041c01040e4048682280d08a00f6505d81d01d403100c01591140c40c10002d900b90560285a2000b1500d4032591a08443d076141001d5903000c0d1001d0f64980c05110000c0d0052401007001400c61904400801c00315281016064582c00010107c0030003001000c0362000b50b803010300c0400403440d4010000c200300e180c43c81002d443c100c0366000342c2c0001110101c85280181c000c0ba01900010900380007003061034903040c1040080c18021100d01e802c414280310410300f41d201d14002e1030180039aa080420454200b406008003e10198020001c0201c0707030703a24002103a001000c0f50f460045c103503540d0303640704414001610744038566 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 9445025 1250 9443775 9443807
    0x309150c06020a0201090b0a09030e0612040201140403020306040b09190f060f06050603070f080f071d01111603111503040303020d020f040e04110306100504050912030705040f12030905040c 83
    0x2e00030000c11942e00e500c00e04840d0310036241c3e2f200a0402905001041c0035005200658100007404500990b018503c4174041e100d41d81c0b41d203407074a074913076021a0915809403400c0311811511400e0219815041c040c2910014586100c40038030210360300c80c1c2c01400c048440c050f04180e41c2d4490701d030407142103400c40300c0500005000319a4908182100a01d120282c030b500b000061758840106031001043c0c0261070103484a0f44d24005e1489190b01c00702e41003c80c0484545c14003008003000203c021091001282074166403030402c3d803080c81c60802e07055920314040002e100e4040d2584c402d4a0800210551341c0080e010b20300141c940c0c0381e804c2100001e00c9030511061a141d000b01c2d00180081113221402e104d24441d100c0c0d1000310381c1007400d0650301c64007516100d81c1c81441502c1031000d4205580810b9012000404545102d544200e400c002580140c8074140040e00004051046400369404503004051860741c010354030002e46c5000b4420100d80c010340303214540b0348403042d444500c41e01d0402c0c440d10b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 9446275 1250 9445025 9445043
    0x3903010603061e050708010302090609070c0605100e09010219080a06080106180f0507020606040b0d140c0a06020d050301091d15060301060b030105030d0c17160309150c06020a020109 80
    0x4000a8035291400811810703d0b070750b003000d0008032114404c600f05030403030307502400c1080745403240d02c02c00c489400d0051803802003052060b040008201140580b90248c00f0068010f8006802d00c03145104002001740310444980c0104181084190300030070562382c1c40340c3d91401a4840c0c0750031000b200a005c1e154080c180035802c0c04008907030074040c1b4400040100c0c1003142048195802d0300b0320015104101e9001026800480c001109403d10384c004480c5000300420070040c450503603a52040c4504001280b02c425030040e01440c1e150b042541610000e0600d81c001002d49460018000300948814007070180c0d0300f512400f0800c03081083c110204100b503503c1d003d40c0d00d07041d42c3c0200220f8941088440c0381c4690309010001403154074000880741683c00207000b400308000140015103c410b8000c40899541e003401040c802e4450261018040241815052080c000380d1818010300b0541d09030044400483e00000e0034003000e42000d0080e450583c006005030b1201511030080e0300504403000050300442c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 9447525 1250 9446275 9446291
    0x70b04060201050609011e06050306040902150a0206060901030b0c0a210b01021002040605040302041a10020109020102010b040b01050304031409060c030904060b040605120c0706020f070203390301060306 89
    0x10701904403c0c0300e01010340307641d40030b81c2ea905106180aa042220403031600c16020003403141c10320800095a001401a0000c42c604409601054076503400c000410030848001c80c03005800c0c2d505010841e04401c00319842d83e403a5046858903208400c02410080b1109000120080780c1c601030720800001c80038503a184074020303021514010213400040c403950300602038031508204800c083c1c400c1e1001c0e1811985e803142064119070920005025000c6800d0342100101040303030465440e8004111000425800071413400c01c50300c006402d440c1419440340c070690802891f816641da100d03040d40d0380b0581520b0603600a50f07138080c00d5103030b07442008030091704144001843e0b07400600010080440c42010349082040710b40d13802e620501170286000318030000300200075441555400182d40f542021207480301e40d140c80d090395620012130748000384660b003101011842c04258941400007030001082d8102c0d2070840b0007090014031201418215100e074660100c200311074561425408032010350341c44201042002c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 9448775 1250 9447525 9447527
    0x807050105060f031204090209040204030506011214010506130b010e1009081501050a03080a02070504021602030d0207050108070c0303090f051c0e010e0103050a020d05040b0a0b0613030b0405070b0406 88
    0x2200e1950240b407952251010900b40005d0790300000360200c101c2c504007807c150001020350702c4950300c0b640c025028400800820014030826000341543c004c2d50340c0c064410b00c0c0991049080204074152a494001080700c9038842c0b800100032684042c60004042d2200c1c001a0b6640083d00103142e000b0b1622804d4504030780d005a140c1e800d880141c41120390b00d08002140301c0034000c0900400360462610142040003031009005046609000d0066038022626500845d04a03000316400000c002041e14802303055040a005a05000d40707207102400206090900103056002c2c09001c880c00c0000501e142c2080c98800d41c00212407551111102c041c01c200780c10055641c80040c60702c48600d0004100d0140c40d18082c40c81f8000c042e5040c0c58540381052088010760003060b008012101040c0c0802807058145800e20441d44154481c2d10345269506041604104032540940180c1c090002003144100c4141d030f03205181c04407580079410410940c2c070761401e90f00b86065980041e022f0a00410046001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 9450025 1250 9448775 9448781
    0x609030901020c030a0c030305070c0b0d020403062a1101020706050906070305100806010605070303110a02010c0807020102130506030709030b0a0501031a010b120a06050a030c0305060703050108030a0f030908070501 94
    0x120030240e084600c0714026070700b01070b10340801c1d035030041040d00c4030041000001d000364003400c3c940c2c0c000c03228018090754548008150344c1c04001ca2040c00c0d81c0c0040d0a000700320300391043e6060b2454660482000800f0030881d03d00c0e000c4a0403480003440030603003804840707140035011500c40a502c61410b20142c2030101c070065a8500a45d41500401d050100003800001c02100d640704940450004100503441d2031020b071041c8c0e10541e0190201a218504142201d110303d0082641c0700c042e60001501d109030600040c690304003d00a6821640108990030144001c06107100564000300d404960781d85a0480940e60030b9400d520040c800d4031140c04014a6203980d40c400303412030303008201130300c0840090000748089400074094050b05040c144014008220100b81065100d840c8000c00141c15458000240040d0b013207520495440700050818020401c0074012150482200d0400f44010350412031400d449005200c0600100641105040c00f00c500ca500100354036508604203550b42c500320b060007406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 9451275 1250 9450025 9450037
    0x506040f0e130c03060e03040905010303020a020103051005030d050c010b0406030311010e06040f06020d15080d1206060f110c090406020910020f0c0411090a080c010813020105030c0d020705060903 86
    0xa003001d4040060340d20a040a60b81412680c000c20303081034282940e540f48020410200c1e207005501c014000458601214455503001c4d5004c1e8006250f1000c0b2440018103640307000f0644c14911550101c1080789031030008a0043c500480c0c00c05548548041c8056801030000001e0789034824105140001456040b10340d01c442000f1040c000d0043c006444982541c810090b54010103140c1c00c562a040403504d240e029154141c800240400c0440d94200c0040400c01d5070303000f556094000740715406000c1c4d003094010420480380c000c180047c501d0040007030040c4001c02c03180c00a00032010103803000c103801030200001d003074002801d02d54981843d040c180000d40120071041c5c002e00316402c148803c0f9000103213200c00c010800c00140301c1c44000f4801c0c08003802d0610000700f00141c0501c52100c0380c0c0c3d84c144011004e030940384003e040490600c00010541c2001510310895201d410a0010140c0d03480412698003040601c1100e555a0342080f5400c0244210031014155005050900c50381c880d022000b032a0f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 9452525 1250 9451275 9451289
    0x40e2125031707050a0305060d0507090507030605010e0904080f12090102041401020313091503020301090f1101050c0601061808011b02010b060c030414030102070212060702100507021509070506040f 87
    0xd080c2d03162541220142c03060700c9580224405001040c49207200e41c0220750700004c00b1b48410f03e0b405141c0c0e51a403402601e03400940d6015110380c100306903242c1c10700c20740c0010542441c01c041e83c100d00b400442c200030005007000e0886480040e215401c00454812a90405400e00c00b00c03c0520344613182c28001c2d0002d01980b64102800080203020350b100005032a040100002141c143c01e1404003820000c080701c1e9000d00d03900a001c007000026a400380b04442c1c042d401072800c110080880d181c040045112100320398140070702400f402c80c46d6080082c420f4151070b120b003000d840d2410800d95050700354409520038001c6600300350814140758030312142e5400c259415002031087c3c0c8541c10801900b40a02c206852550340203100c100400702c02c80c0c0c0707040d8805c0005000189030203d5034021a240207900600c0403100d922920a0005456040203000d004003184e5100b0049403d09030002525098882c00100d07034000c1400224840c070509100590080800420b5180e80d07680d11545088005c01500c00c0d48 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 9453775 1250 9452525 9452537
    0x10b0a0b04030b010b04061e030e01020f03010f0504050c0703052b09050706050306060901051c05011d0a09030e3c150a080408030a0b04090303020d0b040e212503 71
    0x2020009182903070242c1f4021388504640005400b051805885004068810580c8a0b18014040070080c4020900d0864400e040e550f03940c10224003801261041e40028003c5c0e280c40300f0001311100140c2130718100c580c5440c0c400c1d980d01d00f14503802c00680d01881180030410036002440c2c11902d050b031110100074400d000360b891943e078414054846010881c0e4658100c0d400300822140c562003030f4003c1c0500101c1c601410034800445403850100c4100360041e078140c104c0c07640c0c101ea440050161b0382e40d10500d0343d10305200c1e43c00b90380d40042400303080d03d035414040d158030507594048240d0b00311400380700c034510892030f0700100d01410b00c11010904807200300e015140e400e0030140503e008078200c07070400758191600c4440782c895648080560f80700038044035000b50740c0d16425845540c3d40c007a000816029940158581140c502c5030f03400c691078564028410342c40c2022000c000e034404114091001519021160055614008040140f00707010403030b01c03402040104020304a48600720409968002c0c0d80e04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 9455025 1250 9453775 9453779
    0x9011202030c0d030207090f0e010f060e090606130903050c120306040606020601030209070f0210090c09061202180c160f030206070203030f0a0504020a030b0405010501030b060303070f1103010b0a0b04030b01 91
    0x4005443c1c84460b010300144c10040d02440f480b801908401404049440c00055100d00002540c1c211524440c2413044181c0300c1c001000310014410001d60006030120241c03110381080c0c00010004144d40c031030000e055840b1050700c410f15001c0d00607101001400f9041d19070203d40401140302643c002c4070f0103031180d4500302001c10b81c1c2c0c4c030020b0800d040e2940500288403988a81000b55510110a84084110710070340e01500c0201d00360380510007245211719038054949060448881c1079841c035070091404c24018000c0a00943e03104064003a00d81e0054a450f09545c0b11200c041d581382c41150307000d140b4041d8400c10202000401d10302c10740014000d5095604589412004a032139101c2a1100d480e011035801c080b80e644400f981c041e90300b0031300c0180320a4200d40e580e41d42105041e822a0b05543c581d42d43d0b030041081c4192030710702a030b1001080300614540b88813581c440c0305070b1501040140041d80c03885602001910254040404070000402918006584190344009236025020440e41c02c1c2e2a5000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 9456275 1250 9455025 9455029
    0x50a0609060f06020303060d05011b0c05120306101809020f070b070302070b010614040e0106121d15220804180209090402060a02010f06090f0e070602060f0903040509011202030c 78
    0xa006030340030f503400782d803642d140c040030024030400201007640c09558801c0a407188105c14211010b5180d81034941000c8011a401e00317504100d500007052000d200c00b082001031a90390140d00080c030b0f401d64100100241a401524008561207421a040c1680300103045d001e0544000050640180302d010340200a6a030752700218140d009480000385000c00c1080180000c6005078030742c040001d030811450303003080d5640711200d160400a03444400404c508507000a480c10700e80c0680103207001a401e500000c10312001c81503940d0f100c20300c3e8203c044015a00440e085c120020a04d8881c110118801824a461424010841d0f4414402c104468215408040f1803071384500980b001440001d103c420251703125000e000d8280d2241c510078085540c1c4020450f0f07402490310800d00038115402000030750482025150301240c101416000d13940d485410104540e580c0001c02e69440714000181c111170f610750300f492525601681d04041d030300c810040004140000c86240c13000040d80210111070300b081010302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 9457525 1250 9456275 9456299
    0x50118050a020a0507021512070f030e0703081b011e02031603050112030f0302090a06030501080c060301030503040506070305070803010803250c05060a0219260301060914060c01050a060906 83
    0x82c500c004c60410300c550409442c0c019000c591000f242c0481c2482c2402e00c454902460b0412540034000c20007400364200356981c540f107230040440d00840200311550841d00d0f48a400e006042c01c05e200340746c1c120100303140c14400303401c50320710060a07012303100f41c07103804060300e40c0a90800c5a8981c2109140d00b041100d1a102e402182d0403101139820100c00110952802c90740344c90a10110018190204041420b9840d00502100100b42c01e56002030194142880c4a007000300049032117100764000d000600c04160007008030703411500100c0c1c0c0f0654410f8245800c1c2c60714001c1600c0584440c1c004400004c00303c1d404001030400c00000c6000e4041050120405107400905c08000b0b00911218071080c892400e010009011061a9004481803500c0f0280c0c40383e010329031a40e0884440089050380074400741841d20750050f2224403d03a041c110b6041801c000c01c00020f9104030303814040c20451415040d183c0100303d41055840034000e020300d00e02541064003804003441141011494a50300142200b4469 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 9458775 1250 9457525 9457537
    0x5060d06170d05160602120406090501110c030d050402010c051b040b06040617060402040909110405090703170304081209011a03010b0607030302030a0605031e010e0706091215050118050a02 83
    0x140f03e95003048400c456801c4540d0718580c0480301958200290014444081e1055104030b20400700801c0c0180d85107803250946403078101000b81582c081c080e0b80214000442910382540f03c6c00300002d0141c0c2c89000495240b09007050203085030040400c00b405026100300d80c0c0540040554090040c05410740c2402040d104031321803000010306589040e0300101d14140310701d0b00003030020000b50a05171628041c1c400ca0f8519141141c0150020210745150704040c001c4a90020006c0c000d012000d2840d12038104a000c5040500302c0320070000006030401140a054a0300082c21503605480c910742803900702d000b480f480b41700d00c000c2880d25110301d045d40390500072801d80b40800750016040810710394007039000c0e41010b4500700c0c1154071080085640c0e00c04102480c502a0002c645c91200a256401e9034212603160813010416004802c0a001040d00702c1d0003c070869640030300c0300c0c4140d210f50400c900b010070342c008001c0e865402c00d4000a91583c41c5036a410518032248401c111545a107650001240301d84 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 9460025 1250 9458775 9458777
    0xc07060f0522030203030d020706060f0305070e0711030a0801030302060f010b09060d090501020708120f0108071a120106050d0f02090307060c0309030b070306090b0609031c0905060d06170d 83
    0x1041000c049261400c0c049280310100b088011182d902d0754002811750b000603011203d0941d0110f020403d0041c2402040e0041001c3c3c0d040c0b00c0d80504645503951154000e0081907110101d10000c90100f620a807a0f092110035180141c0e600c030314110a00603c03d20082c8416001840707071a0100700a8103110100ca41207502411000d45800807074003d0098030740024018800e545d43c0c0d40b0800d00032400a00040c041280700e031168540d502e107800021b400100c0d0141c2148600c10b08540107111071800015144103642c0c88800141144401c1085d058035032140d49510181d0100940c00000e03140e4003c0003414400b8403085007401307000d80700f282020890203101e0346103506601a1508011040c00b980c04407034a41d0085c54030619454581d100d440d0f0091064a162001913903490341003001424500c61420078020841d03005190a5080d0002540c9407903034481e4601d042510b03088000c003140600710b50002031038050901d54850b601c0e400c0d41802400c041c41034401607080580c07581d000c140c002c20030000245507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 9461275 1250 9460025 9460027
    0x2090105180402090709050306090102090306070207030b1306020f18030c0402070b0402060c01060f0e0103050d03050606070201030506060c010e0f01050f010f0b030403020106180e1204052b06020307050c07060f05 93
    0xc0f07408002d40d0b2007000e031120051040c2d244020410380c80071300445201d03500000000d03030381c0d19a1406145c94418010540c004542094109200061a00312a1034100111403c04100103009043c4040240b05001d4840c17064240002c000601c0000e10500b020b040d18101d00351500003484100380016407040c2c0303000071300e11100c4000260041c9042009452071031504000000c00a0310344010032800d11403908502c0c505201e0000400403c8001c100800403203e5616040c449e42c20450013051007805100c200905040c5c84800041d11520342500780d80310006501d00278230000c1080d440b00d5449101c2c40403040c0c1e055091100241d0f180c014040f0081c100d800d10071412100e10f25110300c1c01281e4201500803404c554940400060741403220740480c0070251205c2000581d2524082d00500d0302c038640c00981c2050005100030812030340d41c0303405044d400e03070f4900002d1140742d40c62041c5901c40c482680018100d51010040c0003c4962143c050010340f40414100c40050382c0b00c40e01a20400b4200c2003003400078070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 9462525 1250 9461275 9461281
    0xe0901060503100902030c0708070c03110102030415030b01020a0c06030b01030b060306060f0a020c0a03030e1e01210b03010203010b07020316031509030309050706081e010b0d02031b04080601030209010518 90
    0x1031640155840390b00c1d18145410b00c4650303918042d0030362242b02c0558001d9078010046c018014000b0b629031004400b400111301d0a4a804040074603101980c005a0505aa4915901090b4003e01c4191600c036801082e06030002e07203918000d801480251400e074006481c02081040300d0030010212401018010b0400d401d11010700c205c814a03620030707141c900450280ca6001d0856850712500300e4055841703900c403002d0907055001485400c40230781d84a620020301c4200304840e21b0741c01010640c10103500039043c607035065180c4041c001a01c4d01d21500ca4042d07100100004004078806e01902203a07100314103071210780001203a5120942c0c80c50001030030f00c0340510303401c000203412907200c00354540c420b040100d00071815403103403814500d060f40b0032400b145401042020440d86040c003c031150540040048035035051442c29815400760f00e003501c004603400004a44408500c080f501b1505040103115981c0b0ba4469070843e40b80c80d000c1c44128066421407002091034644220a16800c4004803028085c40d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 9463775 1250 9462525 9462539
    0xa0c120e03090f0a090204030302150603010b0a03081b030d060f05012a0c0801090b040201020106081203040b0405030412060222050d1502040503030f0c06090a0206030103030f0306150e090106050310 87
    0x6000f01a2940c0085800f000003034580345400944000c5020383c015100500c0080200e0180181c01404944a6454105100855620845090140c0e904606401d13220192103900d10f441007240c0141041910000ca5035014409450700300400341c41c0d4804925040a641d0401507410030001c407044080c01c800264554005908842a41d803110700a85c030710a2000c1d030314078900d400c40360012400c3d1062900c00d000c00043d941c0901401004203028070081885520040f500071440c000034100410300600d035000726090190820940d40030780101c14091881000c51b1074180000c0d801501c0f44a060200c20301d001041c0f041c0c40a485044550240c1440315a001d107230398510480c1c114104602602d0b500b0b11000c11191401c102804100380316000d000c0d0f44040c0d102107640703801402003a540281e4408a601c0005894410a5034112581420505426a8070754400e03006003e042e0042506698507080311784170190300650000442d403040d604c05405980b80d210442d018803048505500401d203401d4100655 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 9465025 1250 9463775 9463789
    0x103080a0f030617061008030406020304061b0b09030403050f010209060711180106091403030702030a0201110109120f1d031e070506070501061a0a0206070309021201050a0c120e0309 80
    0x14209520380003412070b8813420b0301401c50310300c10980b140c1c0d64081400c100400c00100d034110701070204000114105881c3c101c0c02580da1240740070310b0013000019950241451042140200042c1c4d200d400d481c050b1416045aa507682c00500c0159000d1180503a0010714030410300c2210502500940340c145450f4058980401040180c0341c070582043d4400c030300d00d88840c0c529140a01802c00b565030300386a14903005000450402d030a800c01d102e504104440d500580d03000a0440c000d0f542800e10f0244e0b10040043e00307004003120040a03100e01c1042207a041101d51100140c4014802c0313449200d0000580c1d0138140c07401e0b0311080e1498041e80101010700740704010080f000c421940b0070040307410454441b40414456045804200c805a44695040c409498484240d0152501d588000744c10050f1701400290b4405016104009143d55031092000b5900e401c1007110604040ca002409a03082c003640c20401003d2810700c050000d00c449034020403255a50154101e0a070086009608252140c4208016 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 9466275 1250 9465025 9465047
    0x30905120f010e01020901090b03010e04020f12030307020c1807021510050a1706010806070c02090c0c06040318050105070201020703080f09130603030801060c0b04060f1e050612060103080a 83
    0x4144a6000310024400c424015500340340d075078000150306c490414002402d40491900036400d03502081c4018000141c0000801d544150100c0b5608200f000000110308600d02840030300714075020010030091450340004920302c009806941c100f038001d010f4047c1d80c08004054034001e006030424002d0249007024040a40d4003d80c040a8100038907075035000052040106510642e01c6401100e8000e248440c2481401d004040004c046c040c2e600d0030a1000b4a80000850001c0c896884c000c0860342c40607505007a18104860079048820b40d0a290501815005031031011f100d500c450701030701182d254810000c0d43c6140c2c1e0706800030120281075a81d090032540024981014050043c02000758503501e1581e010308501514600003813481c11820000c14690051300300a050015501e52000024a40d2146a9125401007400603180c9500c8403450302500641003000d03818050804014034216a50748042d0280c60125850303482180060b440980303503542440058101d08091142d04003031801101590a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 9467525 1250 9466275 9466309
    0x2060316030617060a0c03020406080403050703030605040212090d0e0102100b120d0518040501030804051e04020310050102070909030203120417120f070c050d1d04020c0a05060a09030905 82
    0x190141c1c0f500c80f4503100c040000003000d01507000d14240004001e16204206120803a440d003549843c1c10404043c01c880b0024000900b0070400107900c0d010f042c400d40c070100c054074004009660398113a50750b698542280c1941d100c40796006a40e200d1180c00e00410000d0a201410380103000032044404091004280e07032800150861034410f118083e44505200741d0001a25076241c00d901c4410407491507c16000070586c80340a81e14020042c00031038294010340d821104121400c181d10100c420321300102213810381c2c03401d40050001c003e204022130040c501d002502e40a0b402c5a040c40d6580c0f0b29441541d01544d00030300944c1040201000c0d8061440280d54804d00401c01808000c8500c00341d03440325840400034000c80501e4400740400c1012150b042c070b8102d1103074503041613030344426107405498802c2c000300344c0d090100d100c4100ca80300c104a01c100d00d0654004000310749031480c014501d41c03104540c0d03008a505008000025002a42c644514400c0ca47c00d60348002030641800300740140c0c80b804440103a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 9468775 1250 9467525 9467531
    0x60c03090307060507140607050403080318070305010e0d08010f09110c0d020105040b06010503070207090b03070504060b03041205040f06030b010311070f29130311060106020312060d0206031603 85
    0x890a601c0812814004000301d5403100e903940c009052a41c0c0c13201c500552816280c000b2401d00c4030859000e41602c1c02d6035080303503030319590351a03d8003030b4200c20b1041a4119468000c200000052040c103622800400700304400341c2c0c9001c46021030850308428240104021124014000e010030181756204a80702e001800030f6618042d05550740b10310309000e0084500050703441d1001c01040146111003290400c01c00e007000c2d800d50401c000c02030344031106401402c0d40c81d903903042d011216a03401c008880040801034001c0048545802c10541590300480d01030300c2c601c41c1d8416055041e80b0600846040720321010f80050b40b541400001c501904843d0395290400d500d0f013141d404404040e20003081030300d201d4889129005454500819000310185001c10440747c00481c00440c044164602c1d03903c1754052500e804400503d250580303682c10592911f0803944204400444c0540d00003008020740340d498200c0d1003251703072084100a4510b41c402002500810148041128182901d145e0504020141004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 9470025 1250 9468775 9468787
    0x201081501052d0d0e0c01050406020a0204090507180207050d0206010305030d3801030605060913090507031209060806041107060902010309061802010305090601080c060703030204090606050309010e0601030c05060c03 95
    0x54002c94101013142c01040b50b03200302c0c01662400c1040000c040d00320a007849414549030680194580541072006030140d9250303c0301d0310400c00c0074451500904441148103000c0408014000000d401007081210a880f6060036000214000140c1e40e040b2a40b000040d4030b8070b43c12540400140486464507111001c54506940d14640005009034129510064000d41e1240d1a0300050550b402a030059000f6101040010702c1d82d290840c01c86961a03030040045145000391410a140078a240d0010301652240c0c0c210038181036100d128030040b2100e540c0c483e0041d891311420001112140505c0f402c0c00d58003007003094005003098002091a50050500080d001c00340c2e1554030540780c007000202181920f98845500b15a0103128040c0c0003020400142459030510003160b41c0c40000c244002d01c54440410154201b40c403036012200a0517086506102d010f54070b86014203190804e4550300070550804110110849002a003103040701d40082c2c1000c9903500d41030600205a204660712003143c0401c000c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 9471275 1250 9470025 9470107
    0x20903030409021c1e020901020309090c04050312040f03230d020606010f0e03060f04140307030f0f02060907060503090111030103050a0201080c04140105030c070203010e0a020108150105 82
    0x900010603040b003015035102c1010214181c4100700f01c2800d000303a842d149081061500c44480b000c0050041c400041e6110080c00041c2d255016011043d1760080b41d00b02008203c80940c00039004a60042e000c50b07900110503002c42c07900d80103a0040703454280c890a002c20103c0d081c10850094504144000c030040801d449400b42810881035840003d40e2200d01401001e50f4090305651031f030700d10361501035100206080080e8a070704010f08440f40c0d545600000c1000e00404881038010700001e041142d40c2c9640031326001c2e1910f03442c694a44003080f070411840c490035002040d0340788941201406810340c142800e006075115000503240c038441c0e40d82c4012014003407081800850103075000b04010103c04103540300040190400400780c24803a0b500703000801140f2100b1041004180c0c0900b01b044c3c50f6030340c0240061480c090034101070b50540c2400c603010315200000c15606400d6000782c0c0e40e1103035070740c0310711031014103441c501c1407240014406c00919180081c0e483c452003180a0300d01e800d412502c80000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 9472525 1250 9471275 9471277
    0x3170d0e0a06060312050405150a0e09040c0317030c1603020705030102040303030e01110a0f030b0117070e03010507030b150304050109060501080709060501030c120f0e010c0e0111060405060103030c030302090303 93
    0x81c04841c50b6a80704414030521084040440e04c840c4140381261400f4201804941217042c20090444e0051012400907031681c0641d0103040406c10241c1440c80c2c600e000e0034450040a41d611092b81c0c0c10b200c0c1707076050728a891601d003260320440021143c00c0c908408416040141c40312200283c0441c0a603010200e040e81d001e0000380020341c0243c1e4086168048070030301e6400c46402d80034400c0d95034030030400d4405240d0031205c0d100d4004c226040001d143c0360b600006940c0d10b14496601d0400c10340c01e00070808100d81100090001240a800030092540da40030141c0858499883c0c8a80c02032040028188401d0242e0046a000d4400e60001ca65484035940b0304050f11401c1c0c1091035181c2128000b4401003d8034400c0b00018a82441d080c00515002203010341102c2903101c0e00109161544420b07422200941c021180d1400c0b9031000300450104824018070410b4144859400203805504100301c403040040c20700c0c015034003c0d01910480c0d19541e0146c80307001c0c2d0800c1c101c09141d0203020401c400d9400380 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 9473775 1250 9472525 9472543
    0x5010b04020d02070605010509090604030f02010207080a050403061406060d0903030b06070303090201020d02120307030903170108011d0c090a02130e13060c03020a02060123060d020c01060b030103170d0e 89
    0x880c0540c13290010b14180081e1041604040c0c01424110100015403000040320364105406040500709040984002c0707019100d0034a0140c41c0f4000001c12101ea190b003c00104220b9005500c104030541c800701035001c2e1440282c580c29803000c01407041d050300300504d41c02001c1441c400e0400048001103131000c00c40d00e81003000305402185e51050307920150358041c030a03807081c1d9286101401803407840c5070b03444c0442e0002a046a08050340c80c0d03903410415020ba100f80311080c2c10710550512a6a4074202076010b00707803060040300c0c403c0102e040d169a071400005c0034407840d0802008122117599500c0c0b01002900038030703e03249002e100d1960010b642e400c2c3d1000d080c0140096903450a0040c0d050070f05209881c0e103000c824040500c10401486503075400b2852605691300c0b04000c0642c216449118807541e00d560000760790060f030000790542c00e260340c4da000340850780c1608000d020b00d960710503800006010903c8050542daa4105011403a048104010082c280428a000070341e072011520702c516050440d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 9475025 1250 9473775 9473797
    0x602030717010f050307050d0506131109040605060406050f030604080906070803010603060e0f0108060f0601032c010606020109170f0d05010e0907080d1209060b100203180f01140705010b0402 84
    0x2040044c01107040c01c0c0b110034003038801039030f081082c0c10190396000e07a1194000c000c030f01801c503500708020800484100c58200f40030020000640c906050038140002c1c28141c5103148924517002c800070f03450502c03407000311968000034050f010aa0319603c45006a074060344000364008070070000300c0e0004502c2005140a414640e80005204e401c10b060301c0e14044000d800500070844400042142c0c039000625143c0c0010030604072100f9484420041e00034010a012001000000c042020f02071200300b000f20744c0c912440710080c00105d80c0c07480103a007241c14a00c1c0142c101e1000f0170a5400d405449401008880100d54100d86043e0040341120304845003038010307081e01103480c002d1000360b078800c0002901910500c1c2c080e1014044030702c00034207031091280181c1ea105403030b00c0f401000d100c0a40c0c000c0c44070800c05419441c0040700309600a40b03c0c0d01a581500c024005414403005504100040340c6a02006850b00300161107581c0c0a901240c02c8848211225925948422000e84441c0040c0000c5408 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 9476275 1250 9475025 9475049
    0x213080102070f060b060405130b03010b03060114190608010b030403020c1314060f01050306041d0a0305070b0702060f06040e0f0a03030e0c04051608060d08070b0f06010509010903060203071701 85
    0x2985484e01c00e41e008a400c4921955041c8410700640c0d84908d034a0388038580c1c01c0740000c2c1ca500d60a0101c0d0141203c0c0c0d200035070600544e00000b41c4d02854511244080600b141c100902e94102e01c688400790f5614014900004c0840d001881009a50001145c0040c060700480310400d1810300003a18070401c12400111180c0caa40c441c000511001c800560090412100e84090946d4140020414040100220320640d128290700256902500003915000a4032041d5900c000c0507041c080e1041c1d00860b01118402440000101414408200b10b8011660058030455540301c0608207c0a051203030701020ba58021840781d011104010400c58400c58840c1c2c6012901c008810301950500c040c1111241c099402d01c0100110210f400c03a0b580c0c454402802e10701201d4640c8000304040218810004280340e80c002251424499006801c0e4424024134400c1e0a1703664030140112554011041007a01085001c0700501c0020055000703154841c1036817034900312048000b12000d400480a0f8002120034030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 9477525 1250 9476275 9476303
    0x141e130f0501120c02120d09020303040308030601170103050a1106190906030e070303050306040f0b0603090f01150b0a20030703030b030c03030a1403070309021305090c03060606040306021308010207 87
    0x42c004100e5072183d1062182041092000b03400a510b8004610300ca0b80610300025403101d0340701950317005129240e0081c00312500c03191680b404c0801540705498450114245415200d060381400d00031074180d0743c0c440007600c0182085d5560203030203c12090519800b1000f444a4070001c900c19132952046c1030aa43d58074107807458000c004d001c940a440145200350004003003440803d405c102100d03045201550000b03a207005582e5511300034403c0d240c603243d10800000601c400a1800101a4a1016040020440554501110031380903055205501640f1000d012072100b1034010740d1500a0030001d1202c3d031440448105625055900034002100032075913414202c1d4007400c082080c0341c580070080e4020762900d920b000e000b800300280c5a40781401414001300042416201e41c0150744000c2c4d0242c9580c85003640d421100b8003501e81150014400e110f200e0191015140c0020700b00d000d202c0c0946450b06d02410f64540780003075404040d420440140000d40050f100200740700900d8128001d0300010b281070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 9478775 1250 9477525 9477527
    0x10020a0305040309090c050f031305030f070c08011b0e0102070317071b0501050f0f0c01050403030b0306070206070e0616020a150f03020702130b040b04050907080d141e130f0501 78
    0x2e004c030342040d904c5a14000c0000815900b1004440076820a5900030f900c83e41e038241948141c01e00c00000400b0340c0004942180c2c92002940a081100d101d0000c0c580020385800d291800c8a4401d00280c40c1c075803420242c2201d00740101d0241c14648010b02c140e42c040d079201d8a54444840c0c49a450185c5035100181208c203010b03079002d0303042e0422200240c20041501d02000200340740074860546d5005100000c1c0b018654002000322404251645c000384002c0c81e02d802d010300184400c0400034040d0007000006981e4030710108140303200340d6103130300c1d807101504480d020312041ba04050074880741f28100300c51101c0543e80d003420340d00041000101180041030010b0004050001000302001810700601c58800144e640030440e86110000702c1001070000550740c0020040c060084815802c989040300b4410140008030740e070002c1e502e2040486d1825480304030122049007900000e40d00c1d1960900045101e1303002d0b40d00800348002c2d500b400c14103051200650424044155024035110100d5010400042d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 9480025 1250 9478775 9478787
    0x120405070501021203090601060806031011070c05040203040f060f0f02070803070905030706020c04110f071101020111090d0204110c16060206060907050d0b03100f020706050c0403080f07020310020a03050403 91
    0xa02c007138264114101600a00c0e52480180518404e206281c00002c0c46924100300065003240f000303070300f440362181411029989038054107040c2e40007006160003140604080c022207024650000e4101e05004071511100300402004020717508158481800d03910590690010744000c80c06082d8140e5a410803c40140c00c00c0000c0d400107002c0e81290301c003009626008102943c09203000d840c0032401f00284041d0034550301c41e0020340100c902c404211072003884001880d41914540c00c2c0c000300300031043c0c002c004049005060b0020350003000d2040f60001410140c204803800c101000449040140e000760756030900544001da0b42820340605000c000c50369040048a81120782a60b0030216410804001040d510441c0140094192950070b201c80d991403c1000c0351103044401c00820414400780d0082000e0340c420502500c403103040c440420030350b04121040307030216a44420501c1c54a0234008880b449a00500c2e002c0c0d82c1801911000b40d00d06045000416084003280e0300020781e40b80c54600940b003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 9481275 1250 9480025 9480043
    0x2010203060f09061005030408120f060a060201180807020303040308070b04110109060f18031407080606040605010203090907090b070c23030303060f060409090501020a091508040b060612040507050102 88
    0x442c0c800c3c40180100c586410003e41c10320380c0c192504a5036592182070580b0301e8401c0c4400780c0c00e10f90b86203040101c1c460307001e540c4600440003142da05c0703140c0365a044200c2c04d807030709851007050944040040800040f0400001c08103544040c09903400c1a5407610780c90781c40d40242100740d0301210070808100401c40716446035040f0300000d080c00110786040040003400911a601040c0c00d000c541c00d132850040c0c1405411000642e13200400c034070392140b039031030b41900c440c040e10840e05184a00700200c4c00603e03081c0121001d0f24070690040d4149440c1108000300201d003d8040b80520500840110f41070180c0001030909c907015803907260701c140c504640e014045112010002801c1c00c00000d03000d0954000c011260460821146610421140c100107400c501c5254050741d04145010300707120400c03134190058103103130ba0b00f51207540c071856480a0b01401c8941030b02e05000000d41f22030000c0d00150750901d03000c1d04001c01401007414403a000c040002d4500742543d06813a15030289104105a44e4100310380301e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 9482525 1250 9481275 9481279
    0x11101020c0c010c08090406090e07140603060603101809030809161e0503010e061f0308031f050d03090801050705070b040b0402030114010e040210080c0d1d0d02010203060f 76
    0x228115201109a40760040c500b072481c100901e4240d0350b401d00403510196844148001e200308855a51a015070f40203081ca890418a14000c48000092048103502140c0300710070302919580c610790301c0d901005860f91000b40800d0a01c2224840864000208814080030031103804001540c403000e0b003009044498020400e0030b195200504500321441803148840c11200c0c2c1d0091980d02608045400304550f40c0c1d50002901503180c400040258140021000c4c021031010148031640341ca102e804010320b0300740780000b03002d07210f040000c2481001000d081c1c11490032121000c000d0a0703243e00002d2407074690800300341c1c00500c0c10203003486040802e00c1155085001c81c01c000e03141c0801581e0306d54010a0003071000e040111088009819501d0a409c080c07200410f01c1d004920a60f181c90501018000c103480c1030303001c3c04280c2481000d00d40103007001401245080c03401030801c0c0c4801e943e0006000d02603a0000404e40c240b40c280c0c0460000c010340e0008010036000980c0b01d242c090140400c040b0000940b41c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 9483775 1250 9482525 9482527
    0x50a080408070905061e060c0a0b04020f03060c1804090807030807030e06070f050903070909120305062209030c06020a050a03180201080402010507082104031106070207060509180a05040201110102 86
    0x15504c51154000590010001b0980c0048400c0000c0c410700800d44441c0e160700451407110108658a40c641c1d1040b4403c8403280170081541040c16510030b422580300305040810004645d1141d607041d41c0551031500140b001c2038280d11640e460003a5004450110007056049080c009095018001c000c1d082c131040e0001c003010b02d001a001002080741003066014840005814030240e10284500c4000d07200c602400d019141091a000314060110312007480043d28080c08a680c1d0310700015422030345000c000c0c03400d2501c0c05444440c0c1c0180b810010450130302040507040c0d80020000d001070f103240b02050b2203041e02d40140d001c01a060b9a0070300400f00400030120000c800503070704498202d8000760203181254440140c1d180c00004d61040400140f07580b400c0242d0a03581648500325036101e03030300c2075444682c08812072803a6603440c2400d582c11409030300004811b1010300d11400217403440300d80c000d14401c0e0119407420000c1c0e81a10603074410091036107904c00c00055507006142c80e2020b8183c54021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 9485025 1250 9483775 9483781
    0x90902010f08041e110406060903050d020303040c0506030901020714061006020601030203030a180305010e0d03140610030c0314010e01030b07110d0e1f03060f081603020f0409050a080408070905 85
    0xc4d0080f00d4240703090710070042c421207080144145501c40c0d894100000d003003080200d88460000e0700880e420702c400c03070709449255564a81c40b480813040c1d030b001e00da01018280606c0d0501c2c0800a00f40c00084c42100c5640d803c1c4211000315525403017003040241c40070050011070801c1400510750341e4145e04540150741c406801000103171400030850700071501078500501401c4142d80002404c45107584042c140758205056209080004184034012403500e41b0100000c1550700cc0c411100c19089071207030350040c1103421004006000707410420003007006280004440b9a2000c01d040080d0007a0001910158144010f1040240340b49030300740c11117001c0c03d009903c015114a095599100c480c2c8a50801203ca41000e909486003105000d04040c10303d04050104510305e00240140b02a10420441420070840081c0014010440201250078502141d080505580034400c061480001103500903035031314058001706206102e0b075421b0a00c50698075a03140d250098951406a0741e80160400a14000078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 9486275 1250 9485025 9485033
    0x40b07050c0c040b0a03020306040302030a230d0e030405060c0303040506010501020a05060a0b03030d110c0606011e080402120304060c060b0108060a03020d0507030b0a0c0908010902100c050106080304090902010f0804 95
    0x1c0b01e41c1c05001203402040c10303071080340425460744003640000d405101d24414082015000300141031000c3c0c05a1b201c0240f4140700d131841c415001c9034a15038908001c104104200d1055a400c03003140b2011940840e0300c0d0694400c04074080d94054194118a40c00101c144402c0080a200352b41c0100024801010a404c480d15941d442e144082c02910046540352030000b6162030904c291040c120b5441030070040201508002c1603680d00c4202e0b20212806003000207002903000300c400c40c0c903070060710040a0403140c0c10300d1706880d09032000d44140c0c6d21495040c42600c0301182040280042d140c00d9440f0220b40800b840c0440a64000e2044581840701c403030100710b4a44c079000101403c0300e404a944007040d11690034641d040038200c0d08054035800d00c2008211091405030408140d805040d5141940203139941186801c8070114803000703501021001061064500c02c11443c401e00d07002d20000035100f40d4540c3c1c002c0c5150b1003a0320441030f090321032814009540e0860031218080180b030808800b02d1801d696 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 9487525 1250 9486275 9486283
    0xb1309060504150e090c040c03060501020f0601060906050c0a02030a03030c0f1106070503040206070f06050106110604080d0e031b100e0d0f03020307110a080304021f050304020f0402070218040b07050c 88
    0x1d103004d800743d034500250f201d003030401080101081c00780c010855050b441a0050107440303180240c2d0302512401500142c04c0b880020164126000f580e510b05080b81840c108444540c410880300700c95114882c24680540d4050041c40d507c1c6e4482d071000200691200005001c484040c4480024400030203640d034607080c004562294005042e00d4055900d5442d4400554180521900034001da001071403e481027190b242d1000e41030f00e100d61284100624079501d881d82c0e517841190014004a0f0a000346440c444054000e42c92100e03600040e2410300d034140300702c40801c609254407210164400072101011112303520440129004200260102545220014050500c450362420405900200240e081c03403042841c2c0c0044001c80c000da928400160401524580080e50164403940036010200f0040401e41c200c86aa02070b6520b6650640d40c40c2d800f085107003201d08400070b400603001c000d090f0050f80e911350024080e08503100d40c8000f6041900300b110003a10024280c006104042040f0080044002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 9488775 1250 9487525 9487529
    0x703030509220504050a020901050301090804051c05060a0f0b01090503030306010f09090c11010c05040602060f06010c0c08030703090501030e07050d15020f030403030f09020a030204050403090b130906050415 91
    0x70b80c12481001d140d411030100c0a00300450401c11902e48003d00c010054040740543c2c68500884402c2e90136600d036000c050032a282001c1c020903800d8200401c20050030a5071140036418110b10f005012601c050b10740358101042120b42d40369480e80c038104010280c086105c2c08211400a20303010480c541450040780c0d80744005045103050001d0700c1c6800039058441c030410703806005030a03014092491403034405810100400080324076035081c14400d220103440384007510301f215140c3e8000c10341611404001c40d607850340039010504208680b541500815070449600005000b144005d540d00e114609000389194001c1e00031504240c2491003881d00c03010000782c104280e41040300c06003c8078801c1e14084202c42c1c818105040e006002149200d010035200000c0d511072406510300740720807011446002d04540f0f010310002c0d400982c0d90810310240c10941c0c041c2da0702138482e00703003c0c00c41903e03007118081640014840305211940075100744444c9229008150003840141c5042c00038003071505003015140958 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 9490025 1250 9488775 9488779
    0xc022109011d040b060c0a03020709021204030809030702031606080901090503030a0f021303030201020a110102070507061412010e061806060702040b0105040e24010e10030c0e1306090c020703030509 87
    0x5011800390580d00c681c004c1001020042290340c2e0b61440030020b0b0b80f550140b08050b80540569400090b8814a90003214903400e5032030203008072551a5031307056070032080c05840100180320500040340141c4003003100b1460051141c40240e00340f807515030b00420240000348102ca0b564101109140064400030603603410540908000c1050480802007400901812481d0342c2000340310cc030000240f6806500828444600d50703284030509890100031401d0b4840c4407401070a0f54841c8078104400341c459a1801410804600c00929040c400e55003100b10900070f81140b20380e070052405000c3c039458110b904001d500b800c00008401031400c10005403880c051010068040d40d05c0300c0045416a01c22002c0b1809400c2610800b222410175018890228a103000031558444102c400800b242d07008280210441000a102c007060300d400d604203c0152015042c45018443d03131103015001d90361215110320500c001010001045d40c6084035550584512100034406c1d0b400c0181c0a1000c42d9004085031420141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 9491275 1250 9490025 9490067
    0x10c020a09050c0d0f02030105040c05120403050f09030102031503060603070807140111300304020607060f0f0f020705010606140a11070512010f050709060e0d080c010c02210901 78
    0xb070f01440950f24410181c00307818551a103d40e140103c41c40f54091816510b083e11704101000f90031009480901ca410031780000307603101c0e40000300002d00c02d00c010070009401e00c0f81fa5007085000d4020900f660010385505090a0040340c0c00f0519003800c100d620f40c0480f00b10f005103034003032514070903030389564050098601e103a000c60340035081a4012a0400080303110b030400c0f10010f4041005200382c5001c1140e0b0714481d0b0910840300b217240e20501065178000c5800804c01c03403800085030713140310041c0008203c3c1401c0545a640388002501e180c0700d145000388400c1c0300960355001901e021821110550802800c0c41702801032882e1400c111010340d0141d40243c14407000400402d1101072030844107070300540c5d01c040815a002c400ca8819086a1030421802e441030020f500d60600075a10f49a040c0a040c00081da1a0700c8134800c0d1038100040d101290081032542e01d40030020300e502d804d5444161801c4050b9020940b9195202d00d9034600d001c881400c61000e40c141800480000c120301d00b03a4449030400e8607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 9492525 1250 9491275 9491281
    0x13020609041d1507050414090a0b040204080a0605010509010308070219050a03080c0d03060b0f0a031103040804030203071a0702040203070201180c0609050301090f0f03050708040e0f06010c020a0905 87
    0x1c40b039200720500e6004590840c1c1000b48a240181d030380944041c40071003100c2c80c0021849980c060030507603003591400c0300141941d4101206100860b10010001070903c1e07194110864552100d1000b0400b6040000180291030100e0910805a032410307802913002c6c81c000c00c01040440c03190029903070459411101c0409513001482d6401e103409103900600d500045001000082142000c010060142e00e0410b40d081c05000d10010ba08840c400d1103806010032081040c0442114550010719100710ba904000600101d040d0303154420340c0040301c2c1240c0c0e644000806000303516040024be402031140c804840302e140f00140389910381c0d0241c18802402281c010021072440c900079048180701c2c4040122001305500141401c03040095203101e03c4002c180c580c100800c00c0c0c103060280d650901c0d0400c0c060441a200e95a031090300422100086d0104035044c0480e60004000b400108000c02e4220041d17055030805096804600e28044c1c01c15043c4200ba28060006850301413085044419050700010160307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 9493775 1250 9492525 9492529
    0xa020a0b1b01020301060507140105060a06140c070b041403030304080702060f1605100b042d1103010602030403020405150904060b0301020409090b04120804030914030a080a020f0c01030513020609 86
    0x15041c040c0a81e0603500100000c200a036020029101c8a800f0741801406444407011031400c8070f8007940c40e150850590a41404403902078054020805031500c0c0061600201d00e001500344500703a0000b07030003000c0008041082c50300f0b20440e40c00c3d01e00101d004c2c40c5941030130396400500c0d00c0340c0c10001340600c102062490510354103070152480c825080c0c86455004c6980d06c0e02030780b241e030408418010181317803401202840c10188100050012181d15404100301502c407401304800d20550707900e031016146c4002003035080251000e10b0007092290003e40d00c7e203003107104100540c3da009201800c03a0102c02c90104c21643d40e076151541203608624001078641043c0c0200f4064492500014551420150701108204558003414412409913500070f170220154102103c202d90140c40c0607001845035001400800d9580f9540f071084d000040031660a05e1003980e8841e080c0e0846044400980c000901e011a03401e0141701281d895002417800700030600d41820604610040d00c07501a00030761022030715868607 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 9495025 1250 9493775 9493807
    0x910090c030206030109050709080102031005010e0402160305030708090c0a050d030c0501050705070204050a02030f070f09050904120f0201090206180102010b04060b07051002030403090311130501060e0a06020a020a0b 95
    0x10750780141050f6603c0d07840740c601e60040d01068680c000000e44107040040c3c00340061082e01d020310f500c6c030390104100c1e14020045aa40e0301e55520594019400c2042ea80d0040208079603c0c86684240c8980e40c5a2900742d10240003414010101c09158100c1c050783c040e07680c5e945d59614180c0d40308550403040c4c030f8010b042c02c13907600c24001d4005020b50301e05810b21908031b1b0041e010302000c91088070280b00c3e0303a6550b241c03030084c1d000c1030f1011034250001e400800d400ba400b1b00003d4803080d5a07807900c031040540c1c8100017024514180d800707455100c80c00040545596200e00c59a840300a580001d1110602a038042000f510038074584580c42c0c2030401020b03030642e10030341090144010081c170a100d050345034810102c01e0303804900100da8601c11800e40940640320380c0262840380da01034a52148003483c50302d980b15000c00341e01e50742e035000c964680005a00e401038414240a13210542c1c0340d41501c02d140040c0851042c11b90000410344d44a40c42180c01603848201c6242510f90041240751180c2070011340c1e14078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 9496275 1250 9495025 9495029
    0x50714010608010501081209030d050702030a0807061d0c0d0818030609010b0f0919050a0914060403020f030405030709021b07080d0306050418060902030f011a0f06030910090c 77
    0x22942411030001c0e900c00d0540259060311070b20070036548501d5500d10034040301d2103500c581030380680128202201d514042c1d0701502140e40064192002c5240d10b40d1040b203103a01480c405c590260f5501d00c00501d00c03074160014900300302041d00402120107410000358072401c00c18401800084d0010b40038447d810340b01c800040c8200f01808840c40c0b4281100041c1c0600900e10526000b8508281c00c200580307002c0402c0340c001c100380c900500e0601100480b420141c40000c0030018915183c0d40c4100002d69115055401401d181c0c02400c05d40c10079290007810164a200007500c194401d100a100d40d96010130000200ca43d01c40c0d005a07074420300d0351070f841d2840b00700c424561180900000014500000710b00c2d240d1941c4290b0301000b03900d8403141000101e403000b0b080d2442c02c02988001ea030014249903c1500d40340e000400310b0f245500f280c0c4100c0e095403aa481c0c1c0310300c41d01104540c0354a9007003e004e22100c41c44102c581c1e50a40c036150b020b40e50b680c8220203000d1942070311204d2800130301c110303501c4284c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 9497525 1250 9496275 9496313
    0x4080c010c0206010302091f06030c020c0d060209030f07150804060e070806010303030606031b0e210a0b0a0c02060f10090212010e060a080706050a090905090106030b13050a02010507 80
    0x24110010350040c3d00d0300424030051b4002d40200000075940300c0c80d250003611039600440c00346501410144214004c0074141c0c42c0c2025840390341c11881290390780c0701da880c580922074032001d40e5800404080c1410107001078859075041c2c3c0400c50505c80507144511403a4a22000c1c03820003419030b80c07818240c0140070780c0300118645000303460010540c288046103650680e0300a0718140802035a50104408488460b4844a04100e150fa500300000f0712506030705000200041c006680c221782504034080c1207142444003282580059140710800c2003000d9010350088035840100182d0f40c459101175201c8100a06040c035800d400f03030000d00054658210380d00038081c143d00c21074546903003060400c407c040c02c1c0150710460041c071300020014500008140709540141000d083d900e4508107040d03d01e038104103880c0c001c0c426440070206002d0842c6c4682c0340304c1c0da001c10010507031714994100900c0d10311024001e400500c04102ca20300201703800040740c100e415428600036131707107003450f0803c0c8841c90a0f60180c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 9498775 1250 9497525 9497531
    0xf090d060b0a1d06010507140106080304060909061d04020303071e0b01120203120a02030408010e0a03140f030408030c09090901090209060409031b060225060609020a02100504080c01 80
    0x26080c0112948039119070641501c94030365260b101e400308404a020f02d25050086141000000c41651064019103030192241031410b421081280340c003402d403102c0380c0080300d09a10106040241c0c03503020395840d004018000c01000241d04101202c03c0d0000119104080da485a00c003007001c40d10104200c0d00e4094000710080c504070002203111004500c3c042c01660400d940d400003081048043e0701c1c0549940d070041c0200700454a038603040c80260081c0402c101503000900000840c2c43d0280210003a0810000142c9001e030800d00d8043d00c00d20800300c0034048481c0600149807040e00c1c01c3c003240c0e0800e4000311400e80b01d540310700d40301c00d0b0fa1140742e5420b03422a2545050010300401500310300c552034800c6850800b04d80d616001d000450307a4564020300000e00c621044401501c1c2084150304060140f0710152038021442224040c010b800e008030003521940c140002c0a001e070074030400c006002e42c1e24041d846c02d02040310003540c030724a1648842700c00d6912004581004407000c100e500c0216100028 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 9500025 1250 9498775 9498799
    0x810020915030a1b030509030313051c0302040810020418090213060311030f0c0f090907050a03081803070302090609100305060106030b010e0f010206010b0705030717030103140c090703020f09 84
    0x6101410741130690302051100c507003281044034000d004041c03240c40c07848029802d59840030101354403041601000ea50a001d01e0b05240c90766518000c01c10300c0070415440141c6e58900d0b000c141840c00300e501c7e81c070740015407050006004400300d00c6600d038070007018003401007000280c600024604401c10040468950f00e003010000400024030a5034120310000c4050314a404d84951141752207480c1803880580c058448907403d11681340c01040c1503080034940e000c88200031303140c40121b0002c01e490782017612900c0c00464018100c080e04440c005501d4010780140581c0c51031540858500900a444103118a9042c1d00040b00700781414030190040d90444e04032160746d652028003070000c2c542030040314002103000f0b00582083c1402d880e90300d111101a40100a540e02c1c00b242c0c5080c41d0040c40c4102e4850000300400000301d8030b50f002e100d02d0301ca420324940350780b0b500d14508280044d4a0b455020724a402c400c84034411542d0b60b01141c1c1d0b01400030300300580c0d146440b200c00e081c03520901034241d50000301d6540c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 9501275 1250 9500025 9500041
    0x8070309080307030306080c0906060d020a020309040507020606030f0703050a03080603010207020a0303030c030b091003080c120d06050906041b0f111005060909070b04030303020906041d040308010f081002091503 93
    0x22032002c83c0e5a160070b58285034403490509c80300b0030080f0b502c29002801040143d0f1140c02c01d5000344540e03480c42c81aa42842005800030342600c00a44110340160320003003e20010b0720f07051240942c60040310000b000c0b00c61951743d80e152175901610740034060141110014245071403e40441d410035500038103000303500340c4070701d0007900810704041000006071901d11019010f0030300e804000d01940d0ba881c140c04403e841e42ea134000b000ea010742ca00f84224018250318007403000c240c00203410501510480410003a0a08041c4058858010030b92841181003c541740c1d9a16200140d40085500924001c15100301319070069841c00d009080e075040b6442641d0700b00f02c011005a06c03880c00b4050840d4808526110040b003950380c1c03059800740c904182c80030401000000e001c1ea00038049001c02038552403e055507a070802009810410f004001c0c079107680708200801d0341c461026400343c191500822003030b42c1000c0c0c4c0c1755610031501c00010315842d03000034011306660311030404045a1030078042e41e40c1d4030b00c0d124038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 9502525 1250 9501275 9501281
    0x30b04030809070b04030f02190302090901050403030c030b010503060d020f0a17070501020a0b010e0a0605120c13150e0a06030506010f030c0806010e070813020303030106031e090b0103080703090803070303 90
    0x10910b03094014031034003042c13042e02101181c0c2100c0d000b501c0740c105031215400300b103804c4001d0310b000415040381c40400001038a07100e540e00c0c85030000340c00006451030141005401d45003803082c0d03401058a00f40041031031baa080010741b500544191820410354155101290a0407100d101c4154400b0903400c000510f00440e54078200c4000b40d00c800e950f0319541d0380c001a0794410208100410101c2e15400501040302000801540211b170b600c1d0100d001580c440118003c403180341e010311990f421201c0d0341401420044482401c0c0d0036401010414550110014420000b45020f4a40740b1a13414002c500010115000301014580100c1520101c4d40d40d403451f07182410007488120340280a24400043e2480c0c0450340070304840c0ea0800c40340640da51a8011609150001c1c500e01a01420400131000742e1001c0024502a241640300000c2c1043c80c1e44400b0586511403001091440c204081280016100704410741100d5200203c0b64541d01c4500d42a540b904454014040e103100100c2c02c42c05040e4150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 9503775 1250 9502525 9502531
    0x4051804020d21021b010c0b09160e040b0f010b04050402090301020d062405040303080604020703030e0109060203060411030408040e07091203080711160b0901110106090905010c050c06070513030b040308 89
    0x40c007203c2c0010741e145ca0a042d180b100341c6903103011403500401140803a1170025410350001003c025104100110a4a003594105070f810640070040480204400c00c080d035140fa6422010181000425600d003920b03091943c8a40c0c02018062500032503200101c0c0c0b000d4056038150f0301e40d028140301040c0c070b404141441c1654500c100c5c071007012140d40c10502c580250100c4040d00e4150b034030462503584240c1800003950040b00110101a40c03031128482d8000280f08200d0f12a1240304003590768102001007109030340b120380c82c4501d02e003030420920000400200480b02110514036070441c50b6542c00d2019a003540c4194003020107007520550b500205036025551030711505090321907400d5505d00d800c8541c2e072605555403200c050f240c40741e024003000200601501219005144c4203c15403407284c699030944500d6444241c10a80f103010041c2041030030f00610010000600d406410680750868a554500d000340c280014060000307400c80d0108921000c1901071a08a80c1c0c13400c880c00d0518005000450807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 9505025 1250 9503775 9503777
    0x9060c0d02150708060108060a0b070c08070b0a091202010504050607030302040503060f04020d02090603120c06060f040504030504030602090415030506041419080f040f030f030e0102010204051804020d21 89
    0x209400c1d45030a841500468055000f036030303440740f003a0755082c010358020001a00391075120754000b80003d03041d070865008085086c41001c000450524041c4040e03c0c1c504a41c210110302d0f04184000c40c0c02e254000c20700400c0355841d1018081d07064550006032043e10031034003c0c54100400203609418150550028000c80c0d8040d0308540080d6070314480800194803c4d90000d5001841100510152070508a40d85c0c003c2c0b0300a0035240c0318a05500340d01d5460344244520a650303003003c410007500e841c100f00f04040074041500c0c00d1000e031802d603500600b5440b46002c01450306501203041c010940343c0303901aa001c00c01d43c03803213501401c0c2c0707a08107543e070755000701d40c104e0306600c880170312900321500070600862a02c000290403820800d1607a88444642040514101e00da105100000b80202d00d12521001117010790780c61200800705042c0244079044052a0700e056a004000800c444d4a0b4407020302891010f14507014a192202e01c0020448004050003400c0b61090b107079180e0b42503080d40d00c020882d0300c031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 9506275 1250 9505025 9505033
    0x80403030e0a152601060c05070b03010e0f09030708040902041403150c0d0902030610080d0302040605040302040903020109020301090305090a1706040201030e070803070303060306110c070306020c0309060c0d02 92
    0x8484104000d000c0c86024000341c0e4901d80318040d04143c0160007480b0a1358070020750826600c080c01e000b100ca110240d02220001e20041c4075642032180601000c0050030040e00b07500e19541c1018a003d141e18805004014000308400001741800001d00c00d48403402c0c0e000700103955983d80c62880c64040c0d0424021703600b01d015442d8062482e40f800054003225110340302d20a800c1661626100c0080b5080010549081601d0f104c81e0030069909100d034503c1204290050b60180d81003401d04d924111030040c40000b410301c100320a10030310b900324007603504880c0e0458000c00c41c0340891404a02500154900a4046d802c00b5507090415400002034031032011305407500d0035080d40c0c071010866241d0000c2178010740c5030031034408200594869040000e01c10903140c00ca0348407590303030f0710081e05d10b80c0031312416070010b543c031003061003042a02c2c003030394400c4030782ea151440c2808c045c6030701030303442d1a0140320003402c007a800030304508444400d105a4000314001496140c0724062400d290f611901000009001400b0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 9507525 1250 9506275 9506297
    0x7051314040c02030702011706040204120b0a0c0c03090302090c0d0f05010503100b010c08030c1303050309040b09010b0a0c14030703210c08011202011b03050d060b040b180402040803040308040303 86
    0x22001045d1403155405949000118403c45ea008025603030241c12030340c01c1902048007165040311b20381e000c146503100f0f040744511441d140740c01104680d0510801010481468220320100781d000320800709580d01140da0854688880f42141e026200d00e40f80c0100c007508000b0303107091824099201e681290b00580030384061130302c003810f40d10448003050926170100d07807220500c001058a200180d64092441c0d91420301d07241c01085ca0400600469108850580c80014461400d080c140100e0103074031400d403480001d95040001c41c0348030317011300c484e0181040a5074041000f40030181c0d40c0c81b0004203054040d01d50f40d242e281001003036a030794117001540c508852240314101d80a82d2103050700700c0340e00750b8903250b440c2d00302408401400716507030069041203121082c41101e95040750801e000d407807003a00d03600e075100c5e0304030090b1054880c51761001101a0041c00100280e4046030220303010076042404020091034501d001030000e014070340080b1964800481d012040103035810042064034000d440e1404144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 9508775 1250 9507525 9507527
    0xb0601050a02030f0702030102090a030f06060b0324030109061508120a1b051c050403050f06010302030c0402070201020118050307031701050d0602070f0609080a03110c07030b07051314040c 83
    0x44200703102035006038000c00250f040011808043d0844030310013000586410341d41000590f5103081038006580142e80d06030601c04100d4a481960010050700101034114601104440704901d0300ca4261403041c4081c0081c4c551680d800c1d80403560043c0d00801c2013242040e0751410500081e018000e426140c8651078030380344408028800d80d01460b15968842c0480744181141c01858581800e01b00d4079803081ca04040c8440c000080c000c245610960f070760a45035480d50030070a140028400415009030030107001400583c4000c02c0b4160900c03010303034025035510380c42d1004034010308203181e0000000d00d10103441c904001001c4007d10002c0e001e40c0e100c1100046001c20340071501001e00c130707590f0b100454802c5131002072056000340240e140035407100c0d001c04600d600c51070195040f1100072112000009804201d5980500c1276000301050003a0080c00d00c0380103581a5a6030069000181004c118100003998282c443d10440b0003c81900400f03000281d645c41c50040c2000640180d41c3c27080741001000e0040b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 9510025 1250 9508775 9508777
    0x20c01120203040b04110612070c03091409010e100302090408120f01060e0d060e030d0b040509071202060c120a09080114040503030f07090b130503060601030501030206030c0c0109020901120b060105 87
    0x1554200c212100280c85d2661004084110002d00540029003031020104665110030382c50703c42ca40c0f80e00c0b88078a11546280007820403040380c004070324400102000050300d494100f2a035040d40c0c1d070008241059201c44000032600f015a60000b5404000182004100b01528000d000e403202a5102e24289803904000080303400c1d42401120001950050b0240d01841d0010074124514094140010702100100b900c60030355004020b82d0b0300c0c4035200c644400d0346081511803181d100c22040042c0c1441810041011000a05000003070300c43e14001c1511080b841c02880015100c00185403c075030f0360001310700040c00c8070402d842807141d15486d16044406241c070000800f441554048003a510395074524034003969500003c0d00c0075081104141d4042035900481000f010680c2c45015540125494007040620b40040201018101401c14004100688030403060302d81000c04040015125554103210740c1c018442201c02170344c0800340718000101740900007507144249010300c16180c0c051f5985001035801e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 9511275 1250 9510025 9510031
    0x70923010602060a0207080405091e0901020a090b0c03040504060e0a06080a03080402130e03030106021b030f0d050a030906020301030b010305011b0503240402030901020307080a0c0e01050a0c05070303020c01120203 94
    0x5a080280021150070f06603000708206c51043e03000d2401c154503100443c43d8803000300d505032800d640382c201c292540500002d9440e0b20190f840002c0d89408480040182910040c0c4525030504c680414200d10404081c0281c902402010b841000104d90315440d62801d00c50940e800400646400004121060041801d0004c0c84d0035031600d400540321a4240884d1080181c2415111a41c861144640d174409000941c001c02c0d00764000c00b0a007000103480c018143c581c3e041d21344079502c042561000b40d00041000c803450b0099061181d210141c444040d0701030040d1000c014003140c07001001000b00541a014503050ba4044c1008200f045090509540c521b25036142100100700144009000d840940c03220302d0034400f0030118004440100380109050781c009031095485c0da50003008004038103074460743d500e131f01410a2400b0300c034100c41500c0c06804a40003203c4941003100000b59a281580a145400041d0f84d0140c2150490ba40c3ca0a00a45468041900b20300084262a45954200c07080c002e480c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 9512525 1250 9511275 9511277
    0x3040c09060f06050f09120c1002010b1f02070e04030c060506060a08010504020d0e010207110f03031c020a0311070b090d0c05100b180103030207081005040812060102010209030709230106 82
    0x1402d0341025401da41c142c2105508501220701000b10302c00584852199440030340c4218014580800b98508001142c2101103114046a1401001844907035a0007959000710b10240e000c00380c4100501030132420100076401204501c162380e8180002c0650101d0502e0303465009080400040d03c610082014500c15030711402c0000c2c942c04018019841c1541c0188002018001d0008540c4152011a0b0070380c0c01049042c5c6504c0070381400c0c2049420074040448140d41d0403005945052001281003001301720142150b5200b80d804503002c01c80c24003a9004004c0040b0300182c4946552140c03900000000040701c081ca454085c800035440583e0040302662a801d030b108014180010344140380f240186154080d469100552410b400f00140903406254081c501950252541c181040f40c0c0c24602804d0b407001c408554548000c0101003802c101c01d0340d00109440000c00000c1d114403004034003a002d041e0015515008074980000da081040c1c1c01001c005040303914a42c0c0c40112800072242c20300c02481440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 9513775 1250 9512525 9512549
    0x50c070e24040f0c050c010b01080609040f0201031404060203070e010311040e0408070c080a030905011d0d02030c04020408010c0e0a0b090d06090803130302010e070f060e010512090303040c0906 85
    0x1d029140c644192800410000c0c000041011401003407000b5182c0d41e01c808404110005928007050000707004028110000313091000080c01d184000c070303030195401080038018a0710150b011003168400e401c50407407601c0ca604280d007142490b040403002944280c03401c00104802190a00c51035000303000d41c4c1055007207010000d007000c0c90a83c4450b07a9000080045990f00000c020714000605071050007005030404600a0201a0262402030110354141d0410b81c1800030009915400c1e54250f0a6625031180944440c0d450300d80c83d1021030303c1c0c6242c01503840d520a00220b0089220b2a05600510b040c2c2c140d80c0c1c2e0261900210400d0202d014190300800700264020810844103081440092103d01d10031603000030f00690f140ca03044000e81044d141551040e9810401c030f014181d09004000001e00c1c0a40a04851850042144141c1085104210a100100000c02c1e060383c0510103075200c2c0a81da8040c08000c1c42c040303001603166481103d007121161082c0c0000b042040f9240b03d0035058442041000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 9515025 1250 9513775 9513811
    0x510030201080c13090603050705090c0403110402070206210a0b09040b010618030602040f032013050a090602041403070602070f0e06040b120604060b0402070c05060702040207050706050c070e 84
    0x3e41d0142d000d411078100308207000e43d00040e044020f214a900a502a0300034151742810141041900c0c20090168452030b0814001400422108400d15049100c11640182c1d51421071020131141d008282412900036031400c2690303178441803c2e8034203105c1c00d4030600800c00c13008220300700046080162000792544224000520510307001c0c0c85104106058101006612075403070741c0b9003050703a0054204016503170b44e000d0704100f0015041c80d85203040c4d9120190900c0c6200c220007003006804110304041e8038503221404540c9881c441d6000548141d040801595101e840e9410302e01080801d0303075001c2c00ba108040f80010000d1000c9441800d0320380401240b54401d14100c09006c002101400145c1e00603607d0b0f021038040da0340d80c0e040c42901d8003148054800ba10742814604129040e400801d4080c45c01000b1174400605021082420b03580c08035141c40d1185100d0010900134058800010880c0c82030030b0010800d590000060b040d01ea0800302201c03a036a480380e1807252f40303003420b8440001e40e0b51103080c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 9516275 1250 9515025 9515041
    0xc0a1205151003020703090b0322080906041202120607020a0b06010219050c0f010e0a03020402030a0e1203090111070c030807060f020f0c12030105010f0c06090807030302090103051003020108 84
    0x65500310760034031607044070a8030080008468030640e80769080400d80c00503503141015000000100108140d00c1021b0030340c5898007044036a41e002c040b03040c0380b0300581d212190410424800ba00c50003e005000c0c6500c0c0c58944036002c04500c5800800d0b40b03d10304001c101214804c0000b43e035489166284e0252030007425070340d1038040c95240502901d040d030041019012903a940b04850b621050300420050080b01001c03418010300c000d503442428104a00d500380c0684d00e403507085482040703c0d4192070050382d9a0302c210040005202050b03420300c8501454031200305940450020b14012009400200300b20008420110802d21940400811b1082804d0b030800c04501054090040a80980c1000c07460704224104c01040303034440a01c10110880105809038100c008005d0704143c1035070420803e00d1075041c200040e001d9102c0766503010410102a1550080080a400411101f5400600f498070340080f0b15010f40a5004174a0060009141c100001c1036849100c44c0c500880fa01a103400c8a41d49405803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 9517525 1250 9516275 9516281
    0x907020a050604030302041d09030f0d0e070603020705060717010e060409140f0712050616021203070203030117010c0e0906030a05070f030b010b030c0406180302030607170c0a12 78
    0x4054150301941248038042042032000c2c43c40345100e990016074a034100040411054884c070714100c1041c030080c08101000c01d000088921381030204e0711031615001d201b140e8001510000d5074884a1380581c8800203503042e0181c015040080c1b04034285c600070341d58040b04032001556941007a148038102d4004010f203907042e840c0140c02503800b8002150000d030790b84920700740d145040620328040d8030040c151030301142e0a010000242c5003016840f550500152501c1d56a141d02030321455590051400e484006802004150511031030560a20b490740b800b00381c00b03502ca8109210700205111300f803202c00d8020b0010310943c404030507075840c0e000d074414aa40510111220040449802d4419100390300007113001040391070020b007072025a6805e41341c11072900840011060703101100041c070900911070320b940b00b101039030b05480880c5401440c80c40d1145464080c80300c0e6500c00b0350940107a10174056082e50040000c202445940c00d04015500c42640c08180c91007158070450011f01c042c4005000080160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 9518775 1250 9517525 9517531
    0x250308090411070b0403030b041122080d02030307031b05030a05101805090d0908150405010204030c0e09160b0403020910080106080303071814090907091104030203010f0908040509 79
    0x1070710001c0c8048484503038244651000700162010400d680400042603854020341e0100b84080d035081c0603090020340625682c0c0511652581d0131071010311245100c1d220495400000d00d40c03402210500c0603070240203512640141d4a00300042d00b4a010424032501481000241020700e0380c80b145150758080202006180240041141e043e11070800201405104034070341080c000346000003081c1c201503d2191030210300e80e54410070f102c205c0301c1c208020b100120305d0100c011001140c0714041d50791880c0140c0240b065420050038a01c101001080400c40703405441e02c10035640003210300d48034100c3e00da0400b064540c41201c294200400090006040c01d1410b140c0054550041c0f044e030ad5190440301c0d0a64000c0d400c01600e0742c1c404410040d0059125418200d0303821100c02d624000e509040d403400500e0700034076080740661191400715100c100c041100e18000c00c103000040141c1e22902c181101260720a10090f8802d60a1130250099003c1c0c07842201c0078981c1c42150145000c0ca020700b8004044002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 9520025 1250 9518775 9518779
    0x7030b01120e0d020106050f0604170c0904290f06060a030207050607050703090b030c07060902190608010501020d02010e06070c03090e040b04021201090203250f030501020c25030809 80
    0x20704480851428a80038488000200001410810b450240001d00b11071445e401548a80210400b0070b00c0ea0b1110700445043d0350092081c5909442d101810a144c00024010342e80c2188a800400051100f5044102095850a10850742c80c0c0000000c2c1070341404250b8002681d45980d0b0041401c40c50080014210842e4905000d0b08201d404e40b40e036810a101203a50b00301280000520004244c2d200c000d01c009440004040b07400e5060090030652175019a0200424407552080d000056684a55010700080e520301c118041e00c40c0c860500610421003846154090701c211401556000d0042c0141d09115680000411942e59420400c840d01c9020240550900c102d280700803c5011714012107034411809441014280d0a00b841030040d4500f98621500c0e403645480091001030754003003612008480450035188109e81d1001408012103140c0d407104940d4029120000204401034000e071a1140c040020b4904c402d0042400b403d01c4401000d0041c0301d001184800d00003d04458042c203030711400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 9521275 1250 9520025 9520037
    0xc020606010807090305030c010204050301050705070c06050304031101020c1e0c03060402091f06050705070b0301060206040213020d0609090204060609031502030a0b0901060c0b15011205041109190605010203070b07030b01 97
    0x5d2500d07050b00310b9001c00302041e61a50001420320050600340915038100105103440340c0390110603100c41c1c0407002a070089004200e0b000003c501031610038564503100700700d484021943e60010a40e619564500e0b24800400c16424480e40204520003007006201e40d01d015025041c2c43d0b82d00c0d0700b08500404000c2c103031409081101003d42c001e4030a91400c1010f0109902d030f19548001358106540f50021a078410100881d0800c014800b03aa8013154a60300598180c40c98101d80d184610480068020072031030003205d516000001480742a00d400042e2454000c1e1010408151204402c03210100c445c00f015215400400c40c68400b2216540150707405044c020f00064042c0f640701c00034106010aa1018000614109400c000c0c40402400c441d00200007030742503420410100c0001e4404600100040a8503940c1c1c000202441001041517007102401402800c03039180502e0001e06550580c000b0707144040c40c1c200c000c40c1c1c550000040380c00c02a080145403520b41c0e0303101d8045001d8010b80e102c0e0b50401c90 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 9522525 1250 9521275 9521279
    0xf0306040e0303040302060906090703030e0603150310061a0703080601050a020703170c0607020615011b0f08030115020712060203040609020909030a0212090a060f05120103060c0f02010c02060601080709 89
    0x740501c003860080c1d1003640a8540c074144449400c1c0340c000050408507864120b503000b000001d070000e0b801c0340007c1c03050f110f898a1b0307500d81e0185110001a00d801d640c00d802020640e620001c102c2e40010f05817182e010080303006800b4900094010f0066001c01804100c001021540c5c2e5800351010340300840152044a05294903990744a01b1315004128003890030388045030901c1000007d1040d190301c0825480100141e20301500c0485005080d0361701241400003801e56070425001c2a11885941504104a01d00c44105885c04e803241e82c0c000d03c21101007039100c02c0c0300360306903201080010481c1e9036080d0f28070800c8200d8803141c00039400604102c2d1080d40d0343c2da80c0b40c0182c881001203441080203c0c0555200c1220080190910b41e510350800c9046100300010030003640c90b08070349070644040c2c0c540014014290b00003500c8034070070b0900a444404460000008011070707a00316420050b0160f5a8032101c000001050b0f0985814070282d5000da0400e400103030039540b0030340317580350311240b60301d80005119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 9523775 1250 9522525 9522551
    0xc0a111201140f060108040f02010e0a030c1e0e07020c040b0d02120f070503010e0717010e0601090902040606030506130c090b130509090d0c06020a020102041a03070807050f0f030604 80
    0x840d0b096004030400600010800e0034400b00e4010b13030b40310302d0030700f030481a038076159071001c0f10032180c2c4500a050150001400810351503070316500b40599845200c0c071030060703154000c0e0101c15000a128445030758601001162501503080c02078003501c5a6002048000009000c11014000b146280ca40201c0311602e03800c01360342d4030030000d6001c44100015012040c226554235081c01c410f90007145c001ea040140196120500090f9141150088100e060304107003c500280d000d803003111020405445240e00101d141d44c0298440182244200e504104540da10300065081d90740856481c1d500c104d42d241002c90460854201c4070100c40903240040c1615207039040380120340c0000c24809c1c0d80e003803441c00c00e11a03414041003c0341c01601c4000288814044401c0050102010101c000c0c903564003c0323201907065000350141c5014040c05070103a050103030110803c8810340c008590390b2000030050800b00d00780b41d0155086910010b64801311500d0140800800411644040c100d290460b50b5000a14864 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 9525025 1250 9523775 9523781
    0xa0605070c02010e09090d03050c0405180f1006050a0c0f05060a0b03100506150a021603030c12030603020109090908040902030103060606091502030301090515030a03090611030c0a111201 82
    0x904280c1e1035001d11049103000041400401c007004c6401008050107120714000d000415042c0400c1520307020815a0b61254005418051584401d070400e00d21420740c68916100800b440c482e2011800495042d030361140c507507403440b81c0c074810710f0003003481001b4188109100350002c5c1c0d10180035201d00000c8003084d940700c03881e0a4040312100d81180d660048440d25140901402c000280d84a5051110f42002c00c001045c04003041800c2c1c15900000560410180c000d00218a48404041099107096501d09001c1c0400021080450394210140c2c62030900c9030280c8520029640c060f075607500000c0c200f0b43da1030010154a082a10a400305000010b4450000d00045010b50321440012039035601d8584041c1c000d400e1074025640c5040841030b09804a039002017902d0445d002d0620206464544102000d003490403402200d40502a00202c2c10078590441400b00840d84a507850713001030b000d41800c0640780c0c0a090120b0b20380b504980406c10200c0c2035900c0d01c2000c008010203003000980494989421 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 9526275 1250 9525025 9525031
    0x20d05100204060207060c0507060302090a120b04030e0907080406110f03090106140a0605030f0612030a030c09050a030812060f0a0807031203020723011b020a05060c040e01090c020a0605 82
    0x49070340010303061007210b0b414060000200f489082040c228103886c0c0c2c905844414078021901010f90110301010155680c80000c8011300c01c80d08000c1d0402d0030f608210341c00f00f408442c15030109440c030340a44080c1c103041c204640f01d8000740d590b0b0601d64486a90388005002c52800d42d29000305d00b404086000040c450046003c2c1751503100003c0c03980d00d88074903074bc009010352a03103071701c0b80305024010400710f2703003103c1182e0340700e40600c0000c0d0b000e94559002910400061101c00c0d158400402d0441410b601079000c0d414084054481c0800c055a850801c8805144c0d03020013060040c00740040e120f501c09048260381c1108008090340b001d800040042120506103a200404540c0004802c000348080041c1400c80e0f242c03a4601075140842540340c00c8021a907840604100b80002030282203c0c0d8000c2d402802d060070324024482507542480d100030351347c1050500643e514000ea40c0031800c014070f0b90040740c044500e010300341c074070a82c6003031154801041043c0942095004603000c4000180305031291030700c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 9527525 1250 9526275 9526303
    0x7030f12020c07170f0601120609080f040b030f01080601080a060b040902180a050702070308040303080402010917010209130e07060c03020c04020310060e0f060414010509030703030f02060c07020f060304020d05 92
    0x80340070304d0034142c0b850000103c500070f0043e008031005100030a0000e800c0c2c48081c1c1c1103100031a41c0d0a40381782540f81c6104504011046007004207000c0340e200702c210011401a404104009956600c5030388194032440b0a114400165100301c8204002601d41e802ca040c02880050001840c5815030700421040b0415060710003000e00390100f040030f4030b0410712034580c004030340f0320007410035500316030322401c0f54803407400f000d403e00c00c05030700080c11a1311902d0080080c1a08800025000c0044c043d2503010f074008031010b500c500d00c3c030a06a403140100741f02c0d003482c2800c184000c003103041c84c00c401566100321242083e03003140200507500800d62200d00045000d420494841c1030518a00507004044092078081c0c1445640004e1003e801e669440c4141c4080c1d0320500700c2954440070180040c0c410384105175405405000f816400005d00d5002903030038500103c0ba400303498842d0b841d0302540a1912801e0030080d031200502c40800c000f424107001459000d440070b03140700c04000c0c40351500d5280a0003080c1c0b00b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 9528775 1250 9527525 9527549
    0x20d030206040b07090f18020c0a030201021903052707080619110306030d111e030d060b03040b0103150b06070b040c0f0b0f07030309020d050703021507030f12020c07 73
    0x10401030303007051a42c0d04c84184d00d004d40b44a8101107507a0515a003521900c50651458001085410095030468584168900071a00f12840918029010350006040c03281104010042181c01078064081c0c0c0303104154007508860165410817101d189847d20000c89042803050403400f05e610364040000390b00a1b18800e41ca2100104105800000e46042c240803e22011050092000340e0310002407141120050782032030002000c102600fa440d0460b660b50703620212800c19a40d141a104c040024070f52020540000e00800e41c440410490368842901d00400c0c20a601d001000451070290031300781d0701c0104a4000c0764984544c0300248080c1c02c400000e031620a042d10900c0100a020381d0800d0007040581144c40c00d8504d40900711002d400f54400b00c0000410000303040d010503110b68454030003a41d008201046002007801d0060369100c681c04101d000f400760096082d0032840901c10b0f10b501d2a416603800040103111401101c5588100389014001034007444402070905040c00b00c03101500c690200c0e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 9530025 1250 9528775 9528781
    0x15040209070f0507030e0123070506070903021008091203010305030a030e06070c02040513080304030906110111030a09030306031403070213090f0f05030c06240108190b0607020d030206 81
    0x104160390040d000790140b00100c0540140990000141c482c3d05030076081441c0201c501c5070040e948111228800b0105064a0310220341c003e80314030240001c54001c1c400c132079542e0b0390302d0700c141c17018801800080e601c4504912803c0c0d065100300d1a142d4881d04030310640e034003110403202031400c2d07800070b0b001100c040d0000720f0003040d69030b40352090190380f01d248402000ca40c10103001c058200030a01202074043d5440742c000030461000c03145102591580000c84980da031410b8100242075038901d000b58030004051031564560404140640c01000042e4000a840d60301c0f40340b040703001081030400c120281500c6072030000c0403076190025119100400030196942d04103507c100004060300d03028509005142100d0074010a84151407140d50355488100c202c40140d03581060b510394015032200500794801e14040045401c01302d04a941a288103110340c0042181b40001903606003421208000001c0c4e8188685080c000075401142040401900991800c0c24903008201524420801a00541e0180c014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 9531275 1250 9530025 9530029
    0x60a050915040801181707060e03030c0c0706080705030705031f0306020306040617060703020919060306060f03020c060f060f03010f020403020901080a08070f060f0905070806090c0306010b070c08150402 89
    0x5041021926405c1e6540e40c51005c2c0c2c1c600d110340d94101c4c80c014081502007034400822249501054031443d244085949a18141c50041210fa100800c00012401014400a1814095500b450082802d52161400c0d56101107081740d8507040241300e009104440e43c203041012001145181c0510b001d42c10250344c07407400c08203000540301c0c00e600c61030408000300242c844288000c207a146d04605285000360350381410200050000c1204801d040242e4410040005d07200d8044d40b0010481e40141c8a002d02d040d1528002d8040f4080c0c0440008560008000a075001101c01101540203400900070030001c0469030100f402c5070701a8039440500303540064148103500c0c1c102c01442c01071050500501c0e2184d2140d890090b00d0048050060100d43c00070f54003070400c000c0b50020070101503400381c2048041480d081c425598917882c418000c40f4003500d40402d4940b0300201d80302d07007260005401001107074a4000144134a0744907220a480d544000800030642c08424810307a180c543d41341448503074905003801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 9532381 1106 9531275 9531281
    0x310050c130e0103020301050c12040204050c0c01090c08071205030f07020d0209090606150301150513030501020a02030a030f050f070c02040609020307020f060105040603020603010302060a050915040801 89
    0x4120742d8203540034141240e008500030f00031511003001c210884d06c1580401001c0b0107801c40000c0140c10a90001d540081140c50020314103001643c402c0c0c03c450366450b04407105188400104400002005440301a04907401c040d0b0b4000002da07180b035560f2080d00e00c0d607403001c54040b40460a655031081403000031038028110350002d10300480265260b27102111401d2142c11a442100080c4810005903810384030200c010f60350000b1101001e844075040200751881c3c80782180d00100c0050001c0c00503040281154001755220120010064180d60b80ba6040054151621040242020740140540d4011226040c80c01900015002160140c4002e80107075603010b0000040c05401a4001090314500f46910199a461790f22002044241d89407480042c0d4008400d100510241c50124020200ca046a05100c0c4c41c14240001007405040c00185001181002140410031220280 = true := by decide +kernel

theorem cover : BRFrame.Cov 9352525 9532381 := by
  have h0 := BRFrame.cov_init 9352525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9352525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 9352525 ≤ n) (h2 : n < 9532381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
