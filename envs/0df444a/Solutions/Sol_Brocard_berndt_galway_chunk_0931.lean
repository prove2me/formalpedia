-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0931
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:02:36.715882+00:00
-- url     : https://prove2.me/submissions/b0d91c63-51a0-4b8b-80b0-4758ba73f47e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 167266187 ≤ n < 167446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 167267437 1250 167266187 167266193
    0x5010f030b04020d1a040f050d1e03090804080d030204030b0901020408150718030c080d1403071107030f080d060603020a0c021905060c0312070906020c130b0d050703110d0807 77
    0x1007500d102d4800c1020410352010300c0504220400119025110484a404031f00e0411178180404401c80e5164107080e02400e1a88020101d0240348800c01000d041e6903c1c05070043c00b0344902030758020110502100d13050f04024400170040d4025200480e004440740f00890f201150600981d000d071401a0010003106100700a10300f003013040500940d091201d08080b10440d1340625a003440554020b0140b1300c01035181c010300501d8580c62104280400841c00303503414440c510300d0102e9400c41c040d4030f4401c101151001c0c5580c01d204466000404880100120364104199400039012446184504200c6035544039416030a034890307680074100090403905514014a0140503c08035411070203c20024561580045813081e403101c0142c64055102260000c00c0a450f0024154012180c0c40c01c0070210785401e402950f903ca15510540c8601d8070f126507811414819070000e145810f00404418034054141080b81e2605641d00040e03640d0344040c48034421070308010034603501a41d400782c441442c2600c552 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 167268687 1250 167267437 167267449
    0x50303060f01031e24080a1401111b0c0a0806190e030403030503040c15140a031811040e0c01170606040306050f010e100f17070305030a050d05010f030b0402 69
    0x107a809040c1542d0b581d2181c003801441d400280d00210554000030b44404100c06100201c41d90480d4480700c031080c0000380207200002c500d141d52540d200d058034070220b00b20700c0418050214020500074800300801e01503100245200800e01d0f10b00080150b40380c100b122303402d03c1002121800307144950b610010100700c4003802c10714824520b000400d4001032540081d01618196842a48140c0006502200b40b20500400204100c0241014000d041c83e0001d204000b6103600511810001c10f0600416184a014000c5c1c03c45680d4107800d20b100200d1036032900e45500300d900701090a07070046181c922010f0313516500140d003980502d8140c641803244d1050207011510040e00501c003a4211606002c000001006400341c02c0c011060301107500059810304131411f10002d00204001c030100021103003041800c00100e01041500e901645001c1c00c8940710001070310303018840c2e100500314480002c0b1032200c21751000c040c00d081c69126009010503680c03007800704660b140c540400317880384400c1c1000c41c005261039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 167269937 1250 167268687 167268709
    0xa0b0112060b0307260105010e040b04050a050d2007140d020315010603020903060c07030c0b0402040914210f0f0c07030804030b01050f0108130212070e25050705030306 74
    0x50101042d00324030607000c030b400e080203980403d4140c1045000c0080f020f02d4920103a0041c1181c0000700304c9589400c4400751584000751014020758485400304050000a202e21000d03c2d8110003259600c46940304010007140308000190b1031503007542043c280851012806c2800c845c0386d070030710306010f04124080002414001c40102d90610682c250482c04c90840207049000b400540c40040e02c400c0001c013410300300701c0700074007140000c881000f100c800640c100d01c490001d40c0c0c2103505843c450742c0b01d101041c0180413030000505014843c503400d1214980000e4103011110100c1b010180381e01d80540c1902060080c0282d040303003407200340086024010b015001d428100c80d144111640d0303641c0c0303480d0b00265070700c00d400940740807101c00014025030600e03034001a28001c081c600606030703140110703640c1800040700d807000b40b0402c543c00003004101c104120700f0000e00303c040c0003041c0b84c3c00d09143e00d01c0010540c9040007045000d001140e00e01d14002c6003a6007109030803078081c61543c0e9802c230800c05242c0350 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 167271187 1250 167269937 167269943
    0xc050f01050403150501061e080f0414010515011d03070b0c01020912010b01030507080c12100510020a1109041a0603071809031805060403021519090e06030a0b0112 72
    0x40c0702c004003040b581600482811141c9400161550412600828426019945a024240e15104010407680c000150359209000703d076022001d407200d1030003120035000310005680541c00c21091090460240500c800504401d80301e980d03130711020f810040305081900415980c150070241f010403080c101c8000400c031400340d10000502e44004a8000794282e0902d04484816a669101c901d0403940c140c461540c015003142440b45051a02c40710b051024428900340b80013501a4502040c01079040c80a240302906008180c5144008103100c02565021900402c0d5482d00034101c032441e480c1001181540500d4000144c1110b1020800400a40b000f01400d100d0301441603000016420718103501030411510a44000f15103000d83c2d003001010083d84405248024502e45400c1005076201c104a4044907815250594040d5000c1904002400b440d95400c40e40d400030f01e045189285d100c2c555405850300301c0c1c140100358a42c141415503e80c13982d107006007901c1208005101c02642e444120114600c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 167272437 1250 167271187 167271197
    0x3020c0a0f030519080c0307030c090f14130221090c10050a17060321090a030602070507080109260904060303050306030c040b28080109050307140a0c050f01 69
    0xd20364900214084016065000401c04285000018482c440030300225200f4039120005040c507250440091102500ca003090555842001d82620300561100008092800e005000560b48214400303980d0540f0801030f2151a20081241c1481c00510a4440004444c5115440603885e54900f43c0ca110380506602d1861181544406480c0d0310040700800c16140340d0703100c0d0348492480d42c0191404450094002c24150142e0400826880000d4000100035859a11b101302c7c025100c50407100c0c1c03080c01100c5810901081010007400b8032500102000e07841401200c0c2c8055990000300d00302c03400a0002003598614042c1804412030f8400a00c0d860320300b0052161405071010002401c85441c2c2d40210041000802000040c0c502030081483c0960103039028081615280b001410300d40205501c0007030000002c900003c00c130a0f0461400c05000700710001c204014a900709645d49070400c10f4103c035000300e01c44022820117800b00369038000d10f520280500200d810001000040e20f420103070301c1c0c1048 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 167273687 1250 167272437 167272453
    0x130917090301180c05330a030c020613390611030406081b09040c0206010302030610080703080a0e0d050106090f090b06040b030c0a0e15010507030f030510090606020105180105060105040603020c 85
    0x81846d00811504101700060742d07030754100142d0b02074150f410303c0c888074041d17400010402aa40b10740c03910004500c1c0c3d00c940e035480c0c0300c0349603410302c4031051020141c48440003c0802404c811421541c0a805656640c0c40b9540311480c0052456501d04c5a07000f21800500e0f40c602168800c3c4120806030140b4900301400e904014440c0041800c4842c1d980b044401070340904010000e505041c402940c118480c1d07202051401d00b04100b41e580c800c068800201100000903640c0c030507a21170205c0c075440c0d1000400c1d640002619082c400d020b07113050301940a0a42c6001d040b5881d103c043c0c4103404c0711550007080c90038280d81d2501003000502e1042550703501806140159100f40d596002c2e174001401013200524000c1c1090068120716986988101703040c044104504808250400e1042d40300324402c5c6400300381e95840c4c440d8910140c549901c40107803942817220108041e83c064000b00d20800306280d001811292002c0b50901361032056501a0102d9802c0205000740341c4650010188441b481d401c5480c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 167274937 1250 167273687 167273749
    0x12071b030204020f0910050405150903011407110709150311010905092d060901050d08040302310605061c020c07080109150e060105130917090301180c05 67
    0x60b03803000e95003240b10b00300000d01c5c1250340340100c0090b0f803c0b43e081c0b800c00d003402e041070041002e032055021501140360300403900207284d5809412050710f00103142010307591828094405043e1690000304c019083c014040b0100340740b0b00c3d13440743c1d10b0454014040040032519640f14a90710660116071941080215000800c60f904da20700c14034050100042040d1900994540c07010130354184216212480d502c003024015580e8802c128181901e000702d45806004406141602803403240741d0001703400c0508007500c10728407818030410694000c5041c00b80b04030480c020420804542242c001e1b541d1060342404000c01d01c0710508220016002c00d50001850508000307403107403601015610940c81603460320040003c2040c429503c200030715925400388003185074006100d40b14441402428007800b102d0202c100c1c00f82168101d0300d1001e4000d0403660120400140a000b1a401141941d00a60900070300b81c040d6403000d1a824600c6411041c4440a5070410381000000c3d02c040c041c24101540d001c0d41a03045c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 167276187 1250 167274937 167274941
    0x50a0f090309080705010311180a090c0203030f060f01021515040603080c0d080c04031e060f0e06010506070305040504021b0d0201060501030f0209180a02130f05040e12071b030204 79
    0x301030300079119819854070b040901c51510560340c205134101800c145401c0d4019090a064400c4114000e04080e84005900042020488c80d58011a501410721080c0421513030048010b50103801d80d103071900410f9450000b400304d03802440900c140107030301c104a14100318442c0c0c1c0c0c0300c98012000e03210300c0d40368400030300005050700c07807680043c0d406810010340803000520401c150000030005050513085850310309142140c602803880090f041200c0c1e200c101e0402d006015486280a0f400751042049541200051005182500300e081c2a44181f500200305440c03e0300a5800150345661810301e01803e0201f4003003e50880c01c0c88105002003008408080b40d0203205c00b030310f20ba05541c0001146407500000500380c41c58080510030f0280b04000c80c4c0388640741c4841e2803230440320b00030000a183c0c861101c00d8000740700f8000d0080004903912400b01c0d64494564841040303c17421101031290381d0003604600e443d40f001450041c1001810011040000c450118158000721008415000d8542d6030b000b00741 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 167277437 1250 167276187 167276201
    0x40309120605100515120406060e04050a021002030310090b030f01061d0c070305030c03040c050402040b07030215011d040f15020a02100b090a1802040908270310050a0f 74
    0x207049880b101040f402c2d464028095008140496415070021001c100c01074152080424030b070341009280000a06202240d00910001d2040201354a500c1ca810f040c42c60325418850012031064611030040302806100205683c01000c400c540280641d20301004036000304801c10358940c1502070081c08888088080c450100144014002009902d90411703d135424040300801d2041c8010341404901c01083d03004040d6036101d103000446680d02c0e19a030078421240e05266101035407007400050007003501c1c45650301418000f80300703408650003101c0308800d0b00c05000090050006441d840400381284002d00c0c440580c00c1401102d51070307250502a1555100c0c1404030b03911249080d00068000b802076030400528031503010040003040384081400c00260007210107015908015103800440c0c945030b03410703421b15001a42c005c008100c040f80500d0002800d03080710b1452616031042e000400c05140c4012035070b04201030b00a01810310141d070a0307070300340080c40302800f096503a41d6151820001090130f841200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 167278687 1250 167277437 167277443
    0x50a050d0609060e0c01080f0106050f0306040b030a081c02030402100e060c240606070b0a050a0b04020c0d0e0a031716050a030c0b0703020906040b0912060a140609041a04030912 78
    0x817000541000000d070003a800581440042d204507401041007503802020b5450f8503101d254040e03900d488840000c2c001d400d812030619814058084c03000204034403e0018018403503680c80c80980042500c03007810823030004440203904524800a00d0101520401800382c4400008107100d00308900045003914081446450241c80c0c00e0f0415070202d0158485041a4041c2c0116401d070300e444107594a840d5498406054280c07050b4540011030280c2200d034010642600b4060400c6495402c6601a5a078484144d10001d02240c0b0098400e40d480c10100b003046d0560384c020308400501e20b40028061490f0b88085090314241d03a090303111100140b4140006288079003707546a96651500f030400b0302e00071101030b03c204281881007009502c29112681910102d40a8480c42038449211401041c0461034014140f80740d40111001c00030800b4495010841078214400d12005541d2844203000c1902000d45025083c0304078442c03c03411000344583e12950041c801e2602583d170a654400c1e9440d0180b01c80021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 167279937 1250 167278687 167278693
    0x60c030f0408010209041d0c010f0203041208130f080303011505040b072a050307030f0203030d02030115031803050f0313120c0213050105060304020d08130f05040c09050a050d0609060e 81
    0x1016442c084c041c401315044021fa5006140a90008003940c450a4070140d5051140c03144c0d21104180c000d0050b0382c02464004c0c0040c0c0510719611344009a07501c00c2c81316801d0b00e00700c01c0c0301003000c84800b9001c80560f03075403d0045141d45d0901c49100341c00b400300600703001000001c100108491000b00083c1c84820320070003146000080c0001900c6c030302195a49101050100008200140c1e41c1c000b07024812030f9000700d10750101440038000b01c1c4c214415a4220b80103e40000000503119850b4250211003540c0d0b0395041024034992000d42144a21080c0c2c01350014000340107105402c2060b0008503003101850544450005003030f41c03141c45411014141c0340110399450004401d50a00340e001003c00365030140304110660515001400500010344043c0c000e02040b0150b008003d0081d048600140501e0031419606e03650b035200c4011503106005103401075092440028a00380180b03520416108000d196007541c0d41000280100c0d060703445011340740581c032030312050301040080c42400c1d001c260b142c000e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 167281187 1250 167279937 167279947
    0x201051012081e2b090507050105090303090405151305090309060901030b030d030c0306080a0c060c030512040b010302130b0f010318021c0c0f0e070f17190507020c01020c060c030f04080102 83
    0xb44c0008001c0101306501d03e401c2203022000103201242007003d5550034213200d5100c240030303000300c1c3c5107010360000650810314003024008103d003c01d000703541580c2d04031542e42c030100d44d641c0313032a095502c2500d800c2219441804034401a1905401034003420006250008045140c0340000b071404070004075a0700440d5a0715107942c1c0d25640740c081c98020303001402c0100820010340c3daa104922519100709000c01108500c0c0d0307010180300700c0858200d036090013890070f0f250800d801c0540440c0828841280b254038201c0c2c2601c800f810500444444100041081c005090075000560141c03800c4016840c03040c00c915502c0c070050740c0d50b441380c81d207141c50440b128100540c145840b00d03ca400580040d040351903c54000c210007515091402d0307220b040c9151000c180442144203443d07805000407925124010002081403050589240110761541102d051005440e0034100361380710440344440d1801604484510112820440d0081142d8440c800459240c40c251603200f001c1038110b5045001540d4002031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 167282437 1250 167281187 167281237
    0x60f0306040303240602190609020d14061e070e03100e070311030c030706030f020f03090d0807080603031b07050312040608070201140f0402130c050a0201051012081e 73
    0x960f00c0c80c0c4d5090030104050308003000690baa8500081d0030403441d5642581408009107504422074003070303025006e20007001d1180340010940610700c2c0202d003030788118400602c045401025200030b01c071501980d0312040d11032034412518000741c0d0b1080c0343c0600ca4030140103440a0244038108641c4000c01c06001c05905604c0d00040e01184d08100b0740c403030b0784044038207070711581d0204408007240d1113400c00148903103010107800f000e030140d40ea130b05404106c04020444003a0700412560003020055550031259600c2110a5076140c6c81039509581560042c0003040e0003010b2070445410a405c1c0c0401c0341d82059031440080d10b861414100000981c1c000701e07007004010b0b00406069000402030000f80318805540000c0000c1400c0213204d410315408010100b415511050902500c032894501d041c07042020b1464080c1c51580098640c0005600e0440054180025141c03020103490345441460f001c4d000c151140c0a44e6006900003589003a480f001d420084040c1c80004c1852001d9454000300032031100da = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 167283687 1250 167282437 167282471
    0x90c0a140f06041a0c0705090112030e040603120f050d0504080c06010e0613091103010f0608070603090203030306060306280906090c020c130f090b0405010b1008040209060f0306040303 81
    0x6545035000300403e001c00e00100060b0440342d00444290114291941098001c840c80d012096202c96009103c80740041500d40801c03c90a034080d020380c03a6010040383d030784148400c4620724400502100c80b51444885414440c48901c4401d030395a14005080c000880401c00484000352000c80d0340c00b80014006628140c203200890040c90250050031032403802c000410581c0d480307150340030304a641d00c01805007000140d00300c03407043c2c0c0400350081150304802c2d24800001d040d14062000b0394450440700190880c440e01440445a81c080c3c00f45046071580800d000c1030350005443e46520034080240882c00d000c0601c2240b00781701c1040300784900d807890640c0000850b5115003210041e64141107078008003980000c1d404400c3d4005036100303d013140035002620000c048045102601d03d003405d140c2c10034800300100290243d03004070001c00280c21604100aa1556161658408a00e0140008000d07241c00590076a10241c090b003441c40d5800c10308002800c0800807581140442e03901c80c01d070302c004031482d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 167284937 1250 167283687 167283709
    0x30204330203040807120206076915020304032309010c031b060603050c060306130e030d0221010e010f09021b07080607030c051201030803090c0a14 65
    0x14000b0b10714080c100086140c50b24007034003030319503800b1b203080f00c0204548a10044490064103e0144030100e844280130036107501d0010119014540106407240c604420484017060700144076030070400c20488004010038102c1d148040071082c120384030399000480c11280000c840907d0044e0010794034640b601e8080c10706031440018038400c41004c01402c5c002080d100440f50561001d00b801701e00c0511a14080f19502d44540e1603000388206540e25600f088102c0e008281074a20440a81d840a0301e040b092150502080351250303480b803a9002d14410340400c0760310280042c4c05e16410380c0d00e00380c00042c064090703038401d07104510708401202d001c0c8220410345803007d002d0500105002c1c81540740c0070380000d12542500030341c3e801d81c0e4000303040f403001140300130710203010765001c07041d905902d60310703070310700c1e4880c4d8003200d155001c6400c0640d0644001e10031401c4030001042510003602c1079085898102ca6030300028144500d612821886601030340e200100403009001c3c2c0f03907140740c4007407208080c03110941c28 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 167286187 1250 167284937 167285039
    0x20c030a090b0a09090f0b0a0b04060923011b08040609030b07080f06040b010201150e04030f030522020121020307030e060408040e0405031e1911070b0307030204 71
    0x10a111803c056544900c20400310b440d005d5011401d4180420540000e10f1039400c803c3d4402142300000503102290006407049031495150190310503601d1348a01664903100c00c0c0d02c0c80031007500113107141d01e60084400034000700903407000c0703000c494140da240c400c20f0707000790400008901240d0341002002124040c040e4062200d24104210382007040b10090b0104000e04524881c1e5201c0c3c0f00c041a83e4800d50022401c0d03841c50412841241c2d584800035450101903c00f640010802100100c0440c0680940e600400d105007050420380a1100030391500b0750483c030224100010780d40c01881580e9043c40c86000c002500320010384d02d040020028003200c40440580d0900d8200804010201d003903001034030308854688851000550329441c01d241984141002420030f502d4001c80b0310103200c011005004000300b8064101e48400340208181d43e802085855001d0541c0005402d10814a02401942d0004083d08001d400d01da140e5410010700342100c0d110b0f01700c84520344500089005400703507140350161 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 167287437 1250 167286187 167286209
    0x140c010b120a0312020c031c0506010201050f0405030a0305040c1203030f0609090b040605071407050606010206011a0318101406030607140a1407020a030b0906100b0427020c030a09 79
    0xd190754060700782d1131059410501160701060000c801c0c081401184c2c514441990010826084000c0b107000504094602d85d0041d80f91000056800c401802498000c9400000640c1081000101103001d00b03801081180d203901c214100142441c4a40100c0e0200b904c681c8001c5401e86030700c0d80390f10445140c0e80c1711920003800c02d81e40c180449c52031402950040d40107400070501c0d0342c1d4603c05075000c0100582c03e82c403501c4001460024040c0100c0d80f1405608240d00b81e886990741d03403040d948201c00e140c140c44406034041001c03a104641c1e8003c4103036030750b034104203950f030640804203010200c0d005045031441c10620003042100c1c51606004050b4000d103182000020007890640c4140b090140140c0581400003e031038079182c8102010a4600036039004103018006616071030031041003103060780e26404501c20000400c20442d19400b08205803005500c91a00341441c0ad2120b0507440c100310203c10000c1d81042410748034190318001810aa00070000841da60040d400c40100101255481012051 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 167288687 1250 167287437 167287453
    0xf0302010930090f03080702040902061309061a030c09010e280e1e07050f0313030206060405221b03030203120c07110628030b01030b0603010321140c010b12 69
    0x110010704c001c06590b000205a511200c41c3d02c04140101401003000c4e52140000c94803409145440c82604140da0104d4014800c0944d200c00c004001d010b208440280c0e500144000362014030918050442c0700700509d040c050304030b410070100758070108481020440002400e4441d44d0781c0041a660401010956142801480d124103510031008105c5054100d000380d4402281840e8450b00c240c80140041c00c41e40d951b00d003405110000c0f07401045504801600a03100000d105207094411a4803c071f241800c1552800c8411084949449002e8030880b10301c000e608416500c4242011140e014622940003140d50b2280c03851541503600e8001d16911000d60100b107404d000603c840e06004105a003581d915807590380b07100b0401c4414002c040380400804041d1116041c10b61305802c0032600726403c0c2c0301000342004410912101c0d10003400043c1c082c201111508034054507400e03000901210707034501845502c1c10001003a0456214850a00c81030703461f40d00c514598a040f540c00460b141d1001c005041070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 167289937 1250 167288687 167288699
    0x10080708070b0a1e0507060b030318040b06040308030a06060207050d03050d050a0204051c030e010302040e04020904141501260c150f131806030506040f030201093009 73
    0x80340c035801040d1444502240003c0100d00072001c007520705145035806110703130a414400400c1038012a0301a16078030f0070601c1c4501039003030200880b680145581d80e050203a841000c2408082c05044050b1500101e003000000081002d5001943c024140e000c004100750340341200003890190240c100600c1140c10803003203c0000d4000707084405101e04a41c0c0802c081d40c84006c00d1000f8007642d800aa00440001ca8112402d01040d88800303070740b03129407140340d040c02103440114102d00640c02070404080d0150085005031401602855001c2d220b0180210740c1c0c0c2d1052003040c1080349000d0007403800c0c05850014040d046881080e8140e50303012683c86081d01c080000328035914280d00d00b400b4003584041c04580420303410201101d04030148411003d513101e1104c1c11002d08185548100042c1b03220b2071810044841c0039004910840c1d40005c0240311684031911800104001031204405640d40d81c44680c0c00100158070380d0064030040d4643d04044841380000b0811020910440c00c20411920424408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 167291187 1250 167289937 167289943
    0x303050c0f1c0e190e0717070f05090a0321030c0e0618030705041d06090d09031b03050d17091501140301020c030f0c070905061e240310080708 63
    0x207510914500700f80a00f1803140403903500d0380c3c1e80ca141208821060b8010412004007a00c003401030038540e94503211800120803810a003138003510b0000004000005031202d06101c0e00203440308041c001c01418045584e992000700c4480c1ba0040801141500c07050b05070b0b45038046c031440b1800300c01d03814003130044500003000410911404441540c0c0c0c154410003031415890401c0343c00090b18000e0020000c04c1c2c9190002d04401c210031034401c503103120701070000b07410b01000305080400283c9911a0041a401d40e1789601000c40d00f030760200c0c2071100c1c541000011401c200491032603001c3c83e44410320b004901c600112070008000300030511b41c1d032010205128044820100e1411101c52101034150b80640600081c0039200344501c203085840007003410242c100c3d8500007052284012412591056980c80525061f86e0007210029446003035440e1103406020603404500741d21a005185404c200c2c21150300c0d8101d80355208070010014000700030085082ca00241c8540035100d00d10040208529065035103035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 167292437 1250 167291187 167291233
    0x2071a01150908011103041211060403020f070506070b01151101020a050a0305070509150f0f040f06080603062e090f0609050c1c02090616120206180d030b13060303050c0f 75
    0x410100c2503030604400d4460a80303aa00010109c0c280c0f080e604150070700942e1003e20701c003000628003414400044628150084810856006444a1150380707401c85041150090307a18a4086c0a441091191006020b100800000c0101e4841c02d851781710740c0e04c004046a80091100052150412003503945980d0009000c01c1c19049001080d42e450b920f1020403094000c03058400019100490701082a1501c1c03a903a4090302d40035500c1c0c2402d40d440204050392503c00b95005461700a003880b0358420315950040340340aa590f00d0751484201d5940e0743c1b003101290300f030170340d11074100340c1d1030380f040c01091940c1c020150400d0307020780218100b6074001c6020f0004442940e2401541d540003c0c20502e5840d00c4054948042d0100c8088443c0c0146050800400d05400034010050003114000f48070920300364040c00022076000010100c0c20803414094008192450500c0c1e80403178038001080310340015004820103140719591782d644462248014a1400000c8481e401894010040c009030038a62503078541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 167293687 1250 167292437 167292443
    0x106050408030904110f040914090c0105031302011b05060702010b03031318060506030403021b030109240906181505010803120a020d09080a0815030c0402071a0115090801110304 78
    0xc445d10002c4070b0307002a2041e40000b0902080210700000c180d40b040e0300141145a020b980795980d5642e04c20501e4440058280f034078081407051010510052011a080625038418103102002c080a480d1050780180700300350071511580b0840400c01c02c198203010b180c0c0d802c081500110300780003400000030182041402001445440c00403420304031040e64000400414000c5c0000c0d03528105410020340b84c102c074218070110a004461007a078035040500c81c0547c41500043c1c0e0f81101440c0940e00c1410b01224040354844585944460000c90050f00c1036070804a00e9040072140e4010620f031904010a01c5044440c540d0318100040024207004401c60b0b07000d1144800000c0c2e40c0d40c41000740002401030300c0d414103800b4034285d0312100300080d5000822270000c4030b072940210780d03442c40c0b01c00c0c5969002c904a190503400c0208141e01c1400c00b44c01401c91175105180004002d0356004900302006402d07804a0070b082400ea6400b90f81d9908055030034040d1450720300078001c0c1a888003c40a8074413000d4802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 167294937 1250 167293687 167293691
    0x60a0f0c09050915010203090d080406230405120115090b0117160503060d0f0821040c05010509030a1e06050106050414010e15030a090c0603270c081203010e0106050408030904 77
    0x10607005d80c030a20407605482d50040c000c588030142801d0900380368202e03000303600105446e416040d4201190b4180d5400c0c0b00b440100d968503140c1800d050100c068105503041c6900d6480d44c104a0f00420082600009440c0c400c03000500c580030080014a000c0c81c2140b841d202c01da0301d40c14084032044460710390720861241d045c05503898460001180c444040c95002801150721000c1c03c1c0101b040e0745001380081c3c3d4102e40308441c03458540901345903a42040c5c0d0002c00200b150321040004e540035401130805c0a000605881c4e1100d6141c03070300c1000303000c81403c420031351141004102c1002520f204180c054601c52602d681040e00b03007040b407400c8206841c0780605110184220300803555800ea0031140e442c521040f0700361a070414510f00b0020f4100090304036a4402400d80c0450702d240300c1e1046003682107012212103080c00894503144d000c80c095100c00e507680c5440d90400314010400700b040384a021071143d41540d41c0d47c503103440ca24400b00e06030401010010100310030884040f0000540703000000031100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 167296187 1250 167294937 167294971
    0x905100903020d080c030c0303190e03030a0b0402040801090605090f07080d0c050a30030b18130203060106020a0b0604050601050306041509050c091c02010507080d0e060a0f0c090509 80
    0xc0b0180b07a02a40441e917603148030006080d096608040050350154000c00c500480400c510030040c025220380949142042d403041c000209414030380d03000040030072400b500051405440e0b00c0c0032401e442c40040c0907950340d9250400d008100801304050740b2095258406070016506058144d5120200c4102080402240007000c0d41846018400d40c05d44503403240d00b141102c04402040390380d485107020390181107040c1d400150042c5009005035440c7d090001c0048041040c15007001100760005800c02c091548055001f0006803001c0280e5406405c140c0c0043c9449a5540f0b410051f01100500e400c0c000d50800060190f2a600802030701d42020045034045610400003030420b091005680c8080200c03030401d0140502d10a045c0020184030205850040c200a400c50314120196400440240010400c01002002c640c03a0340107070000c49994400840d103c0d1046055a14000c0c0c10707944440083c0e81d42005000b00440b620034821505c02500b8064500327850000058600702e0010004425400c58a007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 167297437 1250 167296187 167296193
    0xd06030b101a0c030f0409060806060405090606011d0d0303021b070b0405130e071412010204080303010506090d05030a030524130f390504180903031112070905100903020d 75
    0x15100c5d0740150499054446a47e218084013900c000c0c03084c441140204004242d190409000d00ca00c120040300080260f602c2d0540112040c00c44400717920b1b41100c402011006940e42d05000c0c1966501a54003d80c484030b0311443d2452050034030407029403580c4032000422410740c6084c155801c41d502150010820304076240104040c00028901103106d0203070b0b9030041036500b500d550007991840b082e40e41e21502d400c0e103443c0c00c2c201c3c800c5000324000c40d030052004200d186850710041c85100c00140100405028030758a0600d1a00002c3e040004031307803558100305010b00340405070a40b0760540c020000c00e54140d4400f10b48070700004880300400c42d0729400f40d0b0324159003581003000c20540e241e045950711540003441c0c0385014000703509400700f006204c8043e000c0c80e200300c00340c5c0d0640fa4051340c4140e94514070000003001b0484031070110181078682c00002009101d8802070050188104c894007210300c0c0c080c40c002c008155a800241c42200c00c240e40340100d5074004c05010035071b82d06456503000300300d8500f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 167298687 1250 167297437 167297443
    0x51309020a1b15050606041409040212030a02011e020406080a0906060506180306010501030504050d08041b23030105130b130807050a170f07060b0103110d06030b101a0c 74
    0xb0341c0b200b200441c00280d038100101c4103406000c42c403191030100841c1d15403c04022140c851845160030008020401d44034178500002c4040c0c2092000b4906542201c0d884149410b6412500301e046c0980d541d60551000c0c14100d00ca80c503d4245111421482d050400030080c0c10701801501086c0c3e0959100a1041040015807201020b4100102529224000004101d5401d9a40c2c05440d00a008100c00000d555000b4050381d07000303651000150a009000c4078003241d265100401c10755144405060440c1d01d644200d046c20054040d88040c009006054070b13000b000c0c2d011070030301c0c207000b80e01d000204915042c003818840d055650010742d9125a8591b900300c41203180005602030061500000e00c50100803000405640c0300c0c0c03140c082550310b140100141c45a80c0111045500d181000f000181c00041940d4400000007405040001301c6071803502c041006c6030000107900058a42d55001807081c003070002c514560100210308451720300790503c10640c0c4c22030440385042988403c04038200912400038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 167299937 1250 167298687 167298707
    0x110d08030a09060b03070f0f0905070c0210090f0b04060215061309050a081218030f191707050a020f0c0612040f0f060b0901060e0306010312120f050601030507051309020a 75
    0x2812114403c0d207604600703160110511640d1002c507555280001c527907245000d114410362982d11203100b0404c0310380a00410f01000c40b500c40070860300c600c1c0800d190b4240010100a00f0908103180e441c0c80c04c1c1500030303140c00c51003030701444818091010025541c0d10703000e4800718015014408a010ba10600d07041d45000c5590300300802c01000400c4180d0390140c40c41d566880b90f10030030300e104407107a07000c0d81407130703c0f0300c60f00c1c0084c40c542c00f04110a080349000005554600340462820310700043c0d40100c0b00084050648011000400005003004600d5042000502180c030201c0580340002195002076201e10440300c0c802e103151280800a81400508250450079a0304008045140392035842c1c1000100303903070180d282c0306140c90400456000d1040c0303042a0325180c0a4005d140e203900707589031104d070740c1a0b5042103001c200e004140611079002c0c0e07004034003807080002e1000c9070604100c030014098032002003101e010413005008400c2d6111050840c6070480e40209801640c078040804211000480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 167301187 1250 167299937 167299939
    0x302190b040e04020f01260c04080102070506041101090608010315060806040c0801110403030c0209090709020c1e060903030a1e0c020a030e01080903040501051c06080a110d08030a09060b 82
    0x85800207149180e00d60342d9120354030844118500308810401582c0685000c5070b500f003044111601c4841c40c4241368415038110302c1902000e81010707500c480950a9038803040c4220340a801c0708050108006140740c00e0030564809003004000d150400c03d00402805051101030159940425414900031040e40801c000e0310038a41990b8030361400f4284a0340c81c5216120700c00300d035881c110b50740e8075000300c0009460540351300d6079070540038900036020050460005051000940150000000c0c180454401010b0f940300060203000f550384808020380683c1442d003091440341c1c12031001c000c8054400f0080383e5219246140025001c0c90000c2c14016141103084080d1b038407441c200294844a4000940070802c0c1e22985e101000d505102004481c0c40d0002e89004000381d0040c00240319540c05640600120a4805501011072124507090000c2c0c402d103500c100c0d200e0300041310349024489884c500252050003614000700d0750704250783d040c049200c01442d24645a03a205403107010018150009030302000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 167302437 1250 167301187 167301209
    0x1012020d27050d0503070c08090307092405060a1e14040605071e02150d0b18010f06030e10051e010e06011b080306040b0a03080d021b0f0601030219 65
    0xc003201000039000034024180d07030512840d68403c40103403050085900c5100950748508501906a484c8800c0340c22800360385605008004000c640c4541900c42c0001c141000c01801a40340d040c559541e1185c0919040240140e40401420b15a55042281c040c582101e421a40b000114881001c48512018201c03da106903400540080c0e4594845c000d8580c160240036128040103103007081000900600720000d4011111601407184101c88002800030381e15002c2d004241c1f113407000001207021790f00081d06d12400c01e9007801880090303010308000010313080314141048442104515240e4032a161050312100303c3e00c0f40000380299883e0b40b6504141d4918100c003d209503140c1d0101d800303014046403070303d000800d80e44030400400c0c40d006844200c1900040da640c65138413090306000162080341035964101d80c5031a0000005500c0000804054446410050311130425082c0c4843c0401006207080d5154403190a4440d40b00e008a51581140d03811140301c030030102c481082c1c02c802c2e00d5030760005010309 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 167303687 1250 167302437 167302481
    0x70807210605072606130203070e0409060c090f060e1003110c01090611211003080a0909060605090315150303071a0115050a030207020315090d030b1012020d 69
    0x5400c20307003202e603c0c2084d81d070400d02020284d800d80d04503101154603580c0901c403071040c442c0c0c1c815035900854000d41603242c1840c20b8410080890b05840c800301d011146547d440e0042e105150f44004070901070240c00c40116a05031070128010035481c0803021083c46852035034180c120040c0241c0c080840da001d01c84510f40c44040b04a00c96008007449203040e1000ba041c00c5420001c42009400c883c0b80d800c0300040803150016a4554a0106100500b12030000c00004008004644ea40e0080c1004034410f0780d03198001c83c10462200207868043c0e02880c00d000c01803125020583e004105450001004100c8281c0c0e40e580c0780448041d92500081c40381c15006c0065108180010101e850088110b408626002e0381d036071306a20b0340c1d8500001403550000e80280b0892030b134a4801c2d001000700c1030000f01100c24a100500c0000e15224056030301c40110380c4907480c1c0c011820303014041d12400550494400010212003903010701b6048840f49100c2140b40e001410903444800307a80145142031006180350311403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 167304937 1250 167303687 167303701
    0xa050d090b150405150d0303020c07030803040b010f140604050402130b160203071403060708071707030204150c030f0f1101060308030402010206092109010507141e070807210605 78
    0x26520b1629064015401d000026010400d04021980742440103040c040c2088a030752021002500705100d501200d0158000003c0462a0b81020f580602d018200d40c00c2594500020a85030440c540e010030000c1d900e104070a1059070310b600555003112410741e80540e86a6520f1020b104848650b000441c00e40e40c0886c0d0324124594181800d00d40320720a4040303506058942104000200086007501d9140c0d0103240050803852003101420f070002003606240c02090548221412a21401c54084001990208040000c0807041d20f1043c00000f81d030400b44010105514018052108103058206001d2860312150f04548280c6142002e840c0c1a8002c0182980320b0ce0100e0043d44251400d9005124541c00708190034804039031015030180082c039001c0708480c03040700401c4e550060f15545060000901110000c074401e42d404408100480c0301500c5080d0581d0304070304c43d003000c0c8541d01c811944aa0014020a007001a00e170301510f084c041691016079910105014070f4610640c020325690410080c8800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 167306187 1250 167304937 167304961
    0xc090106020115081b040e030c0109080d0b010c05071a0c15070206010e10090902121605090a1a060c0109080d060303120504030206070c080c070e010e0a020406050a050d090b 76
    0x12402c1e00c604407580180c2c0c0d42030281c0c0d00e0042c0400d03d24111740c03150034445603191075409642100005c1041d0390601400ea4489400c503502450243d03034000d40001c15408409642c4074248100909007080e5030443c08039141c5aa403410240103611002c3c503280680c40740c0c2c1d0340302c4080d16801d05a500807a04005405900d206104101356040d1000d44a000c00100f001c44a400342c6d50320904040b40b0f032001c424544200d110182c140c40350b0507600500081c0640b04c250f01d0070301140d4003000044401466981c40d20080c400d01941c010a645c5040e45454089503009a00100e41c10f8400c5e03044030115181c5860040c0c040c014625000020a4694000b8035005404d0aa030044022079010380c541c005400070241c075010540c1c2c2c0842d0028016000080045d04042c040e0341c000340424000c48032b01c0e0600c0d1412405074580061500143c6842e040780303004002074400c15071010341c0f10728640b03001d40c1010700d0004003410a02900d0a2401030010204100d00710030030950180b03000c1500103000f080706040000034510 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 167307437 1250 167306187 167306201
    0x307050708010f020309120f12090f0705010206130201031e06180c0e060a030911062110050108060907031b0e0f0901030b0604020702040b0306091c022d0c0901060201 73
    0x2425400c3c49207209030680d4a200782c0384280244405407004583e284074114055024141002071040240f080540d442101c013080fa202e14810001804250921101c5038a040e02590249045512480420400030200320100720010790a003000708005c844030b8000040b0144040600345040e240c501c0010700203101c8801382c201c6290b5490100000744401508592b6107100300b0700719810140400070034008501c203034041815075000700f40450200002c03100084866000701d524855900341c01e0001c0c0d000d0304d40c0741c50b4503404c8020030382518082c0b454000003901d20307240100060710500c80503002604860180c0c006416402c581c5900c070550300d001400c0540300351002e205060003005a1082445503042c5100c4841c180c03070700101402c585588031030800c00694032500d4200e0704143c542c4908007494504004082c06190001c000c1c2c0715540b143d41d040340811714586042000c56104512404603024481c4002a9040d40800e03c0d0710b079031007001d1040e490410341c80301c12504000310000000d101e41d8107501c050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 167308687 1250 167307437 167307449
    0x140a050102070b07020d0927090c14040e06010605030717130c09051014180f0109180b060402070206071b0905090f0c1306080604031e1b0f021203070507 67
    0x411161a01300c01280d4401002ca241800300d10b24560500040308050001c89012005140344141707100e020300a0030030b07585903d00c00c4491964040c814002d13400c0180200741925815101002515408181b156481c0c82c10720a900c10321800001181600344a80c410b26030a02c40c0303006a841604050428400c0040000b006030713480c1981c0c1d000410542c840b070040f5401140d1031000d440446003420280302c0d00c841040c5503540e0000a03000000c204900740c0450f248210500045003015614003404082611422140480501c003680362490001e104c0403116504080c0a403001a01ca0020307201284040c0300740840500506410407005006080c04880e01064070040c2d40c091159844948080d5543c1d01a44429460341c0c01c1f02030b08643d5414420548004001451804154182e4400c1140d04041c025038061307001609a43c6110007807161184d03551381442c0ca078a041140d2080448103940d40104810005000c00131a0802400755580c1c5601031110888040580740d61360310b9441d10560b1901c0754400e80b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 167309937 1250 167308687 167308703
    0x3040504140c070b070e030d08060913080d0209040212010e07021006060f0c050102040b2a0703031b02030c100512010503010902060901050307030e0102040303210c1209140a05010207 80
    0x44080c030010700d10024000c1420000d010b003802e901d07603509041c640004007204204010a00741c8189580d08000c2c2d03800088580e106d101941c240314003400b0405000810315030300c8006031042040050070460450300d0241c1040c40c0180c035524060006030191241c0000003907498603500012810041401c0c425002d07a8445e002c850214030b84440450589542e0b1040e00d000c01c0c13201c0c4801c0d0404c0c2c002d034812010f25100d400011700d0240c441c041c10906070000c1240b001004481d5140e1032034101e15075030500c3e808030000010014540766030b400078406840d11500c8949580383c0444501152001c109081c041003008004000790219424024801e420034083e00c030100c03440c00c0000485003018410b001c4215005842d081ca01340b141c100640f07050744084c1200003010f0761540c000b20300043c00e1025201541c030035a81c07035040c2070320611042050060301c00c4d010703e00f034904007040d10b1250b00000ca9010b60000b0b030201180c524100d0510010316645022840e039a80035641d07012080100650041900c0c612603460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 167311187 1250 167309937 167309951
    0x61401120b0303031605130806040c060c0b07050a110609061b1c02070206040e0405060f0115090501210f02030f010e010b0307200d030609241a070b010803040504 71
    0x201800c0e60264124582c054204101190742429508001d10b803403541414031529106c000489182d00c03000907803011160380c02980c1800b04019405100d14010100d9142c0743c071803041e840c2c403103040d001d0000c0c1032241070040c005110b071040c0d40101c0c00c800515104a05951080c40d003030309125142c04003185d41242d006605001500780e02c505005039403000302001e410300e948041c4201048000c2d400440c040c2d9024600b408002040760910300414410307849500501002d00741416078120760001a0040c0090b0103070000c5d81280c0f6640420000300f120404d1034650349041640d1412091310300c1e07034080c07904000d0a0041d0654100c41b03c1d0011402445020060301c0075a81e61150702c0a00102030003580c411090800100303800b10b10649190150000c003041c01c41c1c5c1c6002a00b1444d1500068850481c0880e4641c2d0781000200618402c2a01c481403020408214520600f091060551a800344504000108c01640680d40f040d4040e02e60196020078082c0030395840b00060b5a0783e81080c8a075a1259003400d403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 167312437 1250 167311187 167311217
    0xc0213060602011506020c100e03061e100e0609190c0e0f060403020303040306150f090b01090905010f06050310050a03150b060403080301030f170a0f030e070b0304031d04061401 78
    0x104c2c1108441c0b0780d0340a4860740c60b07080700b0800c40420546100c0100411902c215020341e6041c001140640c0b904002e007027010390780b040c840113185401061400202c401d000200001c0a150a0075036210f0011180c414980d901c00c0b4a0128441c28400c040208a162400c1c8003581600003100d4114240f0448803421080301c150208900c5100d035000027505500309020810008095800004000101565243d01541c55001c0c10b0504000d0b5404100c8080d190040c503192540c1000c9501c0203400340b407005100399070400301c225440000318400d00c800c02034000700140b0402e10549a15018200080c84588582d94038201803008039841c03600c0c5c25000d4030300b040c441030700c0c0741c0f0b00c0032a01240d83c4000c0c9281168a1a200c25030340b00500e5009842140050364206282c406c140001c203400440c1c2c0e1640c80b50b041401c0c000404941040164040c40c0d0302144082c41940001c43c166580b10b9410b1803c0140170b800e148501101c005400001504182030840108600d200d52980140d1030000303030f82c0e0034400c1031a50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 167313687 1250 167312437 167312471
    0x30711120310061107090203130605092a030c10091802131403030c1002180603041110140301240f1e0212070b0414060c04060305070c021306060201 65
    0x1440070000310b0b9041d601085620300840c84c034262010340c03000741c0304807036580c6207050144e07402166140c44c0740d00c07032405034410407500e4454150000c0344040205040c00c03510001d001402a00080c4101d000344540710401140c2c2c08006030841883c001d1b1500e0214440c0c3c21000d0b100d0905401500c1c9204680c0c0c0369813103d51201e10994403074a103d2a15100d0482c608221402c140c1d00682d252501030008010000c2245010000070003020078444c1e0060390758000f40201d20f0403448111100e840754200300140310209000124400c0381c03040448200414285100c0700369599684c00e8166180300750003200016103081c056030340030a0191030808000e400c03808418222103050000c194200454885a0a0301c840d422010410f6070448660040312802c008502040d0100d03040f6680840780e043c0d86504010410a1510014190209040041005050008441032240a00c1c0034a50406541c4c4001551292244816074030442d0060000c40c1031085850700200a40303050300800f000340d030030154a190005044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 167314937 1250 167313687 167313691
    0x80703083601050d060306140402130902090a0213051002030a0905010e01050a202a0609090f0603071a0901031d0a0620130e011208030121080307111203 67
    0x80860140601d40c200c019911500442003151040743da5000c00720010303255100300103202d10420805201440c0c01c0c4104085a910300d00c60480341824028540300680f14040d4407900150407110150700c50082d5035105200c41c03c50740c4800d620031708850500c61002d4000c4001d00c101182c564510b1005604d80c00192040c4140918050000d074041003c03c0e0100d2103800226101c40442800001600041401504e0040400c510715110a4881c0341c1c0c02c8522107540c1c800b0030601051f21580d0603c81548001503030325800903c134403c445010000225255011300014000d042200400d5041d2481042c0c50340d503a8002841032804245800652100c1145070302404404a0744180203000424007550354901924007600300f41d070010021520440401000350180101c1d0000000034001685804149131910b0010b80c844801c8031803040f032078404510355404480c199044100b40d25403410700140000c0009031008400b8102d0100030040c0b10016502c0783e00203110b16418803c6403440810140340c0740c0c0601c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 167316187 1250 167314937 167315017
    0x13171213142e0507020303010b070c030606060306080d090510051e0a0305101203050d05070c1b142d1903050312180c1908070308 57
    0x1000006001400c80d0040d820300c1600c94507551800d03010321040d0a290100070102c022a00294054902c0641c564601c034800461294109000a04010802a480348010700403000500740000c0d05d43d06101c4032901080003035500c034000f004040e5070307000001d0003084140150072031400f40030100002c00780709034680000d540005141c00131903103001d10152003d501c4202502c0307109141e400000389181e40a4040c2803003070f003552404106032a144854a00c50070b42ca4010156414000508002095128003500c211030804140080d041c0c40715041a10700342c00c5044c00510608078088600303031860490406508841062007106c090000090801603904801e1944002001c20010b00c0a0000900000860002800745c0390341c169040194940c0e555100e1b230741080d274080e4000580156006869800e9650229003440005171480d0b620700000e0302c0d44503408410307104100e4241c60480d4080c2001d103050060240404030b130940342c1d03240350035203203034001d0a0842101c5598100c0038208480038000c5000303140d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 167317437 1250 167316187 167316217
    0x301090302100b040f0f0f150305070e1504020d09020a0f1805071403070f020d110d080a0b030124060e150715090302061602030a0e01110a0b1317 64
    0x741600e00e034010045007950940c4a0b841720b0b14032403100103900c5a03404241c2c6007080414111041050501690400b41e00e07402c41001640c0100f011960119440e025980c881d040130440e5140c403809280a02c40408441d0f07409031000601c02c0d4540000d038002c48030f452007640c45955682d9100c102e4521600e691007080c2c0a040400603011224240d641b0031a407240a40c10718494220030204d030301102e038000716000701c049920803c081c610180c04010020b5402080d01d8815440400b46440980b0740b40c10503494014040da01c000315001c19800d070440140c2c001c014008100d881c4901c0002151000c401c2c050070f104202c1d518020901c103105440a00f006240644001410000c0c44d55290880e8002c0c40280c60b903060b00c000e8204510001d0092103070240c0243d00030074407814000340c0301c0018500c0d1140c3c0c5065600800900342c00641141d1103180e094805d007820600c0101c1d2105030760900c5840c020080840a83e00200030010804441803144140141d4000180301d60700382c4041e05500c038030603020345c0e000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 167318687 1250 167317437 167317453
    0x32105010b091003020c1e01201309020315060a02010e061e011e0b0f070618051009031e050705010203040308010e09070501050f16021201050106030b040504020a0302060a0c1b060306050301090302 86
    0x41c4145491140401007d00002c0d54844010301c9894a40d42180200d611506c002607000040103e506101c2c0030b07000d029400c6140d03040c9030603030301c1103804011191401088046071004009000f90f019020380001d0f80140c403442d103860303400420240c41d51b01c18a1100300b9030000110704d10f04c000c8900080b07a0025140c0d124058140540300503290000c07000190644020001c500006e001801501c0c00c0c09500c1d02010f01d2280189003607030601c00c0402c07402207140c0c41d03c3c0c8200003295010050001a40701d802e0520b01c0c0c4035041c6011615031142100c041d006600010922082591200c41641202c2e8000c0b401b4006031a044100783c2c485016219080c00610700384000306155800740d00a040c2d40004403042e804c070746426400b140c05456409614901650356000402c407094144c000c0341007000c8115004c2261f40381541c006049007407503000190044201003410241c40d40a01243d44615070401114401940325000100c0001c00318011036000078240000001c140c10305006504100360b250300504200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 167319937 1250 167318687 167318713
    0xd020d090e04150e0319030209011d0a05150705030f070605011208030708060105190806090a02090306011403012307020c040e03311d0115050304032105010b091003020c 74
    0x40e11380014602c0203804100500c203c07084207000100c44c0c16009440151b210100a40007500a02c0b561811075401c056941703400d2102e0350b0300b08001d0180d810031504021442d5946031008480c0c0105030004141c3d100004200040703181c0c50002d00304203841000107100c0c50382c0304d54400c0c2101c0c000315030081c45104184007140d2504e009401466020b1010714020781080007450520464181c040210740120f0040000e01000b8140803540b0380e4007001060f4194501410700e070210b540c45a0511441004004062079000b059500303420003441050940f0803403017001003c40028903140015200c1a0261140c1c100a464508141c0100c541000951011b1130a03c122200303800240300d0071500c20352601c440502031202882c009800c0002410014021030f03400080000b1205005106802a1803103030039640c1d0328401c195210088a034401d0b45854542203e01800f0038511543c2400510240d5403424000089441000c5034082c2c261038408031454003095104136000c0e802c904c03600340060780c03e800c4004a0700325 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 167321187 1250 167319937 167319941
    0x20304060807110c100507050c01140702010e0f091e07021b040e070b0319050c040803040b13150c031e09060509030a0602030a05010807151d040e0d020d090e0415 71
    0x3c82500401503c14583c0000300082c10040c3c0050400e001c40e401084e80d0342440403c0004c42030303032002805d014110120006100095005501c4000d04000b01c00c0040d05041d110a904003c0b01c82d1301a100c1001400c1c0f146640c140c08002c003843c5108038180e1400501110b10015500140c1007400890340c004000c22405c0c00041c0420096a00f02449009400a11002048011071042c4031011421a4189242081405070b4034050200071550000740014400c9000110890b03041701c01c1400303080d5442d040518a4080c5503125404195415003c016110080b900050007501c141d1103551800356150010407920082e0f10000d0b0340c3c200141c0b07c0703031050003114019001405554001012212400c40da50741e0b01c01682e00c1110305400d0540c48500400050f48104014070181850841d6005d507500b40ca24000c0c00c039a500300021003098156030350408640c03100e0b800080712026020075a000b101c8070840103540d604c1c84141c00d40c005040d604000600b010104031039070040764001c0191403031450070901800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 167322437 1250 167321187 167321207
    0xc04090c211b140f1c060308040e0a05250e0a0920180d06021207020a0311070e0c07060b031b0406140d0f060f06120c06020304060807 59
    0x5100340e8404190a9451010410441c000a0107021614440440001c1d060401101c214414000010f11018806114038141c03180750f420341d54403a0301d60051502c40202611344141e9400b0043c54203e001c410321030000010000d40d85901030840c00c5407900b034901030407a03900302c03817105404442c14940035000c51100c034200c0d80ea12043ca00148075030070300c8000402a0800b81c0c003801d289030340c500c6601d0b10504003a02c002281d08a0044e0503050081078138040d9580300c070010300d5034400e00b04001140c0030011503034142d82d03032244d4224040016181052010750746d80f8520760190041600c0c00d0202e403030b0510014030300050311424030125070740703444502c1d9000c0150420b100c100c903825102c1da14080c0303e480c1000b080c00b881d4840c0e022540e078800c0d48000e0001700c0c2d08640002030100c40c00b031441c0e105515059609010240e001c4a408807140e15410054001d001c10240c1d03459140c00c0c8140050302c1200f150707401100c14024107086982039542c403c203a903203200ba44203c030041041d400000b001ea50140031f21031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 167323687 1250 167322437 167322461
    0xf0f0303091e0f0907080106030b01020a06050103061a0a05060403170f27030610051908010e01060302042912070306060306020a080702010603030203030a021b0d0f0f080c0409 77
    0x20381060309010006905100b682e6006180c5481401510007518103191000c000280c15141d558107401c1180b00103100c804140503150500d5242c1c1d400701826403080280303c0d8629000081040156140d15014026040112040710144200b00d003a0b4494075050142c241101c1008181500e000d00c1c43c0d541032251042c500b00c0d0241190309010210420481100808a000440c84603d80304840740e80641c101c8150308003c135019510103420041c0381703030f519454003080d0b5000312081c0c0d40342e19003822041c01000040d04514010350820005c0c0342441c00540160080e0b0703100b12814040c0385144200502c0c4002118110034590003201d0542032141040702019144580d00010384a0329a01c0703440f0941624030f15407044a0140e400551001a1580080015000071052009000451031a20300030f55901002c1c0c900c1a00302e034002040d0048c0203540d2803404180b24210709544160f9081d24001d0528642e07041c0b64408201d021450040311441407608900c945902c0e4641410281468001d03401005a10400c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 167324937 1250 167323687 167323693
    0xf011e030c03110c0a0b0a0203010b0d0b0301090219140d050627010e1b0910030308070c050a0807031709030715020f070b01050f120a0602030709150522050f0f03 71
    0x81c00c03c1d50301100040030122a54130040090200034034001c0d00d841001000561700318414801400481c00c182c0440b18041e81400010070a1074620340080e005003c3e00100039440010b00022100c00d40088200c0b40450b4810307400c0c440b452480000380101c100c60703981c00a09039000003001643c106513407880c02c00d80c180e4602c60400c07454104d0a00d01d003107941b0400c2100d06940701401c030080c480d100d29000c60f441d10f01a141c0b243c40341060210840c0d80004ca0000a062100850000b1001407060250b01d00c400e401c001103440b00200e50401074410741c04080240d001440c01031811260f812601d02d9a801003000d84011031815010f612528900c00e50b250820320415001c0018140103010800608881809001d0a00c055403602c01040f40e2803c1e10700038030b400f94503200c0d918845030802052a0480c20f0b00f0060141e80ca945003a0115040070341d5030848403c4d0314207400303841e20702d070391090161246200006909102c09000c038584100e51b40c0da84102079020381d0340017114030309081c40c090403601000c2c00740c11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 167326187 1250 167324937 167324951
    0x70615030b040507050a0609050f090c0906070803150f0918150c0307030e0c030c0108090f070e0412020703020f101404060f021c17040f050307030e0f011e030c03 71
    0x6003058454041e2002c0d00e0b01d130b0008006220b24a091040031004100d182481c5a5075460315000c43c41d68680001c540e07118004450004528460f00b5080710f060b89401402c81365121054601054130741c0050380c0058074070225040c0141d86043c1482040c2200070700038160318096417207913001805e440e0350b0520800140107100100315000d0f160f4110a000d00d20300c2e030a4035100d01c3c25000050455041d1541c00d040c992010082034081d8070003027650301482c8400e02c1d00309056960302401900c3c1c1420042400203a10500e440002c284611038030540c06244254517108506e030703109404a948a903540170183d07120f40a0003040c061480e24080d051503212180c104000704801036072010742541c109501801c04030380c60350110803400c3c1e070600951401c419000e0600c1c4001501c22801040c11841c2c4c40e200015600c0d0348081030511400820b0345010581c801e045030755544d014a4003c0851348080885070046900c0c2d00340007050b600601480c02c45100c200c00842c090410358034100c1c00f5040000b80710702807650741c550b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 167327437 1250 167326187 167326193
    0x70203061b1603080609100f050103020c0c0a030503130b0307080a02071a070206010513020414060901110304030c03020405060d030f05030709030203062d130602030a06170615010c0807061503 84
    0x941c40c0e00b501039164042079103403a0b4140040d011004120150710205801c007803000e10b441a039400244d0f0003c0c40d006868040c81e46009180c00701801d03000da4001c3c01c0c044008100300c0d00000501c0c1107074041a4a00d80540d6800b0700301a14042902c5132800703e00741d5030016045441c560f0241414902500d00842c80c502e0381c15814010300410741d1a403006811800050180341000c0352a107500c40f40380c3d4402c628083c40c02c0001c598012065550070310401e00050401d00c2c0383e00ca20a03040041c9600c07010f59507110340e00e00e443c8000034003030312040f80140c1c18140000d900386009000c1645964060311286e4289900c0ba100f2140c079407008101c0001d22141100110158070b0401009101348428416043c00760008a2407034164a0140010903000e4010400c008804140d58076000503541e1040f400358503a10382c0303d000c201400850b0404940003d056030190340c101400211a0301616240c03640010400741d5400464911503900070107050403000304041e4000400d5030384400c2044011f02c0c120742070740307403030b56 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 167328687 1250 167327437 167327467
    0x7081204030c05011b1d060408060a020403060f0b09060d0c0911071a0603070312090b0a0e01110304050a120602040308190905032a01030605060409090303050606070203061b 76
    0x18030240c0000745184502d8042003001d206480001c044030300d5540000401080c02441c200281c400300d220308603510380881c042c2d101e100aa4004e441c0d80c106680051420102d082e00a40080c4000d8410351300b030134151041d198942c42550701c41e0701c010740800e00540c0c5071402d01c80022614007086520f0b58102e04005a0310038544035904114045030395982e130f01c00c2141070503416072744600032529081c42c056003800515580050036904a95001602d10351070003548205981a03c0560b1005146010004078040c0c2250301c54030803a1460803d03201d01c0c04201c40c89510940e24000c0d0b00419401940100051001840030303200b040200744114009458180c0729620100903800008041403106e04400040e00303030030b0f00859080085c0009034010300500f0200c0f81d98940e0a1861894030b100c4080940440d40300780d100340c007e0b0000d004090801daa0b580c3d40c40054000400c080d00003900064238101c0410b00501d1b006046a1071550000c0c0201042d40b503101ca280d21000c1c2241c80d4400300801005101000e21100c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 167329937 1250 167328687 167328691
    0x20f040609020406031104050a060f032009010f171801150909050d2a03030b10020f010e0a0c03140709050c09120a02280e040b0601030b01090308090402070812 70
    0x30754001d81c545182c42d2000c1c040e01c207410000e407640380c01440144600d0301c4584103541240c40b41c2c58000d001c4091500d0a034001c0c0300003442c8500c1e00d038020040c1518442101c00501c16138400380e0710040103014613002250781100424a280e8503950840100b40c04216103024a160208002c00005824014440161001d941503003d80300281d2191960800e2103004c0c0702d000310901c3c2d181000d000201d803165800340302c035060ba5051003100c2c04484400e804d040c401d40c000c0c8102400a080c1e040c0030020750f00003039559404003243c2c91241d070a02d030144502c0a0302003030003040315500000c0d85090900316500e600081001900d0203c0c980b00d9440300050f1a00b081c041c2c1070082c9008400c203540e803402e810038081c082c0c84070200421160302c162f11040050710307000100c41c0c1c80e0454401240c43c2080c1c0c424564122001a4800018031208006020622220481c224002c1800762420024201000d0040d103000e20a4840900400c0e02805421a181019001460344a116010f5145040342603270141a116600f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 167331187 1250 167329937 167329949
    0x60102060103031112280f0f1404090504140f0d051207020c09010b0705060112020f090630010501050906090106030b0109030f0303090308070908030a0309020d0204090f03080a060f12020f0406 84
    0x101b41400c110000300291680510f035618540308405941e040f5002c0c2030782103810310031010005940c4880302100d01c648161005002c0301d0006000b181414100340a6002c21404a01c80ea4010a0300021030718800103520052006540ca5940c00e042028401a5809500500000550044510000d000d5540d4440705010f042c5050070282c6440e4213040284c9400416084030003181c8805144c1800f40c0d4619410b604100b00c115188c2c102a500c44d0701042801c078118900d25441e10008000340382c102081d2510f58a491000d100030030146c1e980704204108100140d9226801c40c102000500040307203c0d030846c01405006041c1204565a20f0350307021180340b00307541c0980000355910072510805511180350350300040c251078034920140c01e20340c00c1c584030310460704404203040d0b0341d9a1890071912200912940160002c1040082d0b4100d82410f103800404401c3c110005107941c0d001603c86501d511880c0c0655400e0b014007255182090308508181349010402d0b030380490b5900d00074010b40d4603400b645000d051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 167332437 1250 167331187 167331217
    0x9050105160314280905060709050312090f1003180b160801050f060c010902180f010b03090a020904020310050403050901030e07050d03030207020a080703030e010e030303060102060103031112 84
    0x1c1001c0000c046424010282c0d4000f40e01200707000c52803108010101c081200500d401411403008100000188025000100b4034000c0702c0800240b42d400c01d00c40c3c0115a000c1c0c1c181c40700c40d01e00d08010f46180c800e210b02c19502501030340c400e030501d05184240034543c070ba29050000d5032484019248158120041c0102c9424078844100403044190700e180c02d015140034141a0a15411311001520640c62018440c0c040d00c000300348003400d488250003000c0215000b0700020280042c4100074a03485608848690020000c4800061207d505400f00ca110301861000fa0151880e40e034200f000c007000140007641d1510451002403900b1015210321409640700c0d44500d50344c2c0c4902d9001505548001c1704c410b0a90b0001c032070070020798480c0020724919503410700c0c005a4407007540c070000e05652220b030000c20040c81024000303c20150001d2802500c4202622000e800b800a00c00f010b07641d10007210300a00503000340c401000003e00409200e411240b80340c00b034480652821000812030303001002d441900712 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 167333687 1250 167332437 167332471
    0x309230105041202060f06040e0c06030a020705070f1410051210030c120c140102120403081e0304050a030f0219290405030a08190203010b0d060506040f030b060409050105 75
    0x1030f032203500c00d4284582e0001d0102454015130906601c0c1c2c0041c040c0303000787d13120042e01e005d50405002003040004003d02c859100c0c203001103150003e40262030101c7d018491040089035000e0041c0c00c3c10111101c01c40c10084001c046401d0100305610600780d401480000c0c00b603c4107810610302e0107441244050034081c041469401c102020081c9688482aa000032601d440c020402105000080d146481104d4403050f030b902c80101e00e40301001d0030401c480140400c0200c20805030100604035120079020005800c074941c600700e12188002d41e0000c0881c1e22900c60701c00000e004500550148455005443d4103140c00649a0074408031114116900250940e058200d50301c003066541e807a110051100040d032a10f03540783da03501e22a060350710007480b0070b260000d40384040c1c3d89813103a04100a00700654407943d641c848050f40d070b00015a809441410030b103000c15a8105001070382d08844000380081542c030301d5910303086110030000c0c0c1815041621030342c0240128409004150043e812104c54070041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 167334937 1250 167333687 167333693
    0xb0406051306030e1203090c030f0a060507020102180108040219120c0905070e150f040b031501021c050d20270f0f041d0102030a14100303030923010504 67
    0x908140e400a0003410b103407504400c8408070000701c40f00040c10a101e500c0c1d0300c0d11031f1040145070624410146606120f60301c2c0c0001c000f00d0100c1c034001890700c40c40d030510680c0c661f00700c140d090340198400c40161124052801c2c98542c4900c9086401900240424a1105208a02005169560b08422054603480c1060b004010b000841c2d00000c00003c0420040381c200500c000308000c000d806000d200d00f80390040c900d29002424101e27201c3c0441129450f960302e503941603081303041e00121781065020581d00075103d40d41d400424490292050941c09680c6803100c220309071516003004007440b00c0d141d50f4640f100311905150310810080307038565041c1c90f100c5200d484202420010180a07041c442006500400580c44030340c0c011020388400c58550201d45054000700e0020310751000300d20f1040b11100d41c0b000c802c0d14103600641c0681150300e42400540640003142001d40030076607e40241080c450403c2020074820340c000100d0901c141040b201014140301a014942d02c0440c00c0304090b5501c0c020f100c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 167336187 1250 167334937 167334967
    0x12020705060405090a020307091d010609050105030421020f0f16050a03050a03030b0d0209100302090105040c02030f0c03070b160314041509050319170f0609010605090103060b040605 80
    0xd00040314168034090400d00403031540070000d40032000e141c5c0c0210208582c20300030075070300c0c02508410108240900020038103412459080c881c0c400460302c442e00100e0300c0e5104104407440b9540005003015000c04003601d034003400c06500030400440c00381d2903030444404424024810345a2100b0010304984800303046070301c43c840c036550100707109032543c460401c000303200891a401c2c96505818001203048c83c040c0440c81c8104900b0340258810440010014180000030710340d81540e00170350744185640e80303600512080361600e0070f011015030300910803603290f0001d40d0000c200c7c840c8003006503410318010b0758644030032031030903141001c080e501c0f2050170242550601c42c1c08950b000b6160241d582d41480e403517500001c0d17081400d490040340c0710840c60050100400c1200e09240c01141d210300900740c1c1100042c803c00080c8040e103061082800070460f00008010a1402148000c01d0605503900c3c19600355040e60220401c0380c1415101d410010b105186003001d0b10081c0700585401d41e84107500d04600f8a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 167337437 1250 167336187 167336189
    0x3030108011503050a060222080a0b06032a030c0d2001030c0e0f0111030408010903022401050907110d03020c19080a050903010b0405090f070f0e060d060b0904120207 73
    0x69600b407a00310030404a2400101c158030b1070f0300a0341c01643d800c0100c1b18004000800101181000385108001a110b800010035520f0700c0d0040c03040030b07041c0d100c02e400c02d03466508014139081d54800624038404c0c14081840008604400281115440300e40e40020403032034003d0680580d80c4280c4110610f404030b0a100344804d1110003440d00300441e24864101620b0412080c194030302450b6218071403ca203074000c00c0320760740f00740c0081d0849440d29650000c4501815072040d00b2401406901840c042620604102c50110244800c07089090303820a4240812618010321060400a000044440d400010300220346020140c1d600566070f80708481c2610301d024a00c0d052005032010b40e03608e820100340c4071010b607900c00b8102e10f0200e80e5510400d000a01600498881a5000d8908401e0100100c000682c00030018401c1c010340c0d040f1a070b01c10200b91220490310900e00400c000380300041d0207281c03196402100c544107500c0044c1c840074a5010031007042c404c6030708031002d0b0341d441140010680c0410040c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 167338687 1250 167337437 167337461
    0x2070f0b0f070c1208060d0c032001090e1501020307081908090a05061b0403020411130803030c040608180f10060803090a030206070303020c03070c090f05040b1f0b0406020303010801 80
    0x40090b15581e943c0702c4d1075407a40c0000c3d200700504400816450342e1000d074843c590a4001e041c5a0303d032a16810100a00300660301c4c0c1c8503a0826007005c0800550045d02035108581ca030042001c440d50702c110080c00220092100c1030304600041000400180d0ed95014000c01500c000c556a08151219406044641c01600100d07841d8040401032000400006401d6481101035110466040e0319680342c0e078050003246c00013907006042120340e0407188010030240002e909029102525190380e121180c3c3c59100c1030324074103000700c800c10003070140c0c0d0b0260b901c581e0485060003c40d0342c2d42800c9406607081c40500f26820000c2c2c0c00a54036501c0f09a0341d07014420182c0002e102940c40c1081d800c00040e041010340c48000d029040104101042c903020342d05442848403140103882d43d406262410540c0415640194000140f9120052000c2000d130300c941841160f000d4201d0071191110840740175070f07101d000c03961201850165008030b41403070104c0142000380354640045440b54100701c111400c2d6004004a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 167339937 1250 167338687 167338697
    0x303010f0905090303041b05060f13060e03060a0902130507030b03010e0606012003040b0c0304090e0604200a090608010209120a0302060402010f110102040f03060c0e0a15020102070f0b0f07 83
    0x4807084040c0801120341096201e0101c01d440c940b22100b074520740c540e036401241d020801282b61004140c03110024050300460021050015440f048203980802004844039010790204001903443c1c2d00c03a43c05000542d000a024010200c0d40f104440c050352412103440c030000352100c1c001c140504003401985e0280c00c010014000c1da250903400240940c040d045428025903c0d5003021810b60000d00032180a05520344110f55241400503055541c0d6000c0d110380c0c1541c92401c40a045c28800208485000d00d500c0181286039019261031040070b14020100f01d40c1c001c00c240e00c00900d428043c4100c5000381008030001d40c482d48050100900b2803204072114015802241801c0000b075030220301c1e56481542400c00c0010501c7d010303005c0350100d843c08900400c5620000300403038003d40303074503206084901c85d45060000700140e10088980da507100c0200c0740c0000c581d800c01c1c13010510000c130041c0341039401e00c00141480380d1034a46002e4034281d510305840c41c0c596281030090300c0703440304e4403154400d07400c3c100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 167341187 1250 167339937 167339941
    0x4110d050a110313110d0f051603030e0f03150420030303040503040909150c1806210b060c0a080403110108010e041b05030303070306080c010f05180a030b04050303010f0905 76
    0x42c074411031200800b0608030005028481d030401201402d12a0340348400f0b0159801904189000003031480e2400090701c0511402d1290b1134051040b0340454250380c0c5c103940c0c140901d900101800152107185403225418040c040e0403543c0452902d54862141c1c1c060291758003540c43c00f00d82607203200784800d0b41c180250020410031012400000448040f20300e44007001944100c6030401e0032881a44020341a40207051902c0c0c000d60f5540f10000301000700c40c01b070307090000e95035913001510111000c1241c102c03000d41104400f600c1c0040c9501c4402e8041000c0d02e070620303203030300a81100d00b0b008a1100807110004080340510502c100300000c400350740028204940070754148640c05003000d00090000b850644a104803440341c085146100e40103010103811681c580c2400800035002d007001d40034007080d6118003008181258407420b10000000401e4513040c1c50115420004142c4900f85542c44d03402c40b0260304004000341c0c1c4442c00a11450080000e141c99506000940241d101c99501082c4c0203420841 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 167342437 1250 167341187 167341211
    0x60e010507120b0d0b06180406050601020618060f0921190203090303030a091e03080402040e0c0a05060304050c060a180905040206040b090f060d06060e1f1103070204110d050a 77
    0x4142c05030b00e41007008417009a890200041c04250007070341c480e078928203400c14401000447c0e00300c0f9010740c1090b020b0b58100d41e036206400ca201449803010f0342c150385c001408a445200e07661b207601d421010b02401c0c3c8801d000c0d031607045c501d0468880005104224000350544400e003060307003034036080221480511f19040061001a550f404003a101e18445540c3d00b11f001c08114612250b0203404151000c114042d81c520304000d04141000c07030b0207074043c0d03042100004a03c08003040740c0d503a18a000b0181d20405007408140550b907000104100c034148640c0586e03100998800c2c3c058541e04160365034400c0c07880451010141138010344c8c1d00c010380140c03c1c00107000c01a40d86105690554001100554403414030303000041052554404043d006940040c00040b0031a450b040402600c0c8135444820f20100c620091003002000110004a104808610000e040384a06080e5414074144802c40b414001e40760002000c540908003004003c02001444070380005030307801000c0d030181c030070103003000b118018030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 167343687 1250 167342437 167342449
    0x8070f050d050622020a03030306210302190f0506010e09070f0503070b0a03021c06090b010203030c0a05031308040e0403080c1602011211070c050a150207050d020d060e010507120b 79
    0x28080080d50a0702c000d984241d03245200c0d0301c0f8546a0020f048500d86c035540d050160042140c0d0150b200e415012200303040703090840414428400342d15500600306041c0f5050198011107840008942007071080490a000c9241008401e01901c8074044034421410440780291419003168040480906401c0080102c2d0b90007080400448d038129030ad599642103c070ba0100c00074410040044801c40c00e00d001440600d402d80e00c0030003a00c10241e800c000c030a1111005995a01040321402d00c490380400080c0ca810740710b100695007001240d820040c002100740e60300240b0f5003044e0000760340321a0101c100b20601d81e0040d83c03a600700c1000c229007460520000c030f9800030001c001c2c0001e4140108540000420701407036001c2d134040240c4901040d00c50015141c20b021243c003500c5001d2180c2c0c0061004140320704000e0b0088101c40c00d540007812083c2c9040148590340392284000e0341d0016180e0003000c08a09a4000c41400c00802e50001480349020b1a000d46034034040c0000c50301c2c031460f02d603079800c45031522 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 167344937 1250 167343687 167343691
    0x1e0c06070c0f080a110303090f100b1e06091012060f06083709110307050a09090203010b0d050a02091501140904060b07120225090203190608070f050d0506 68
    0x10556950700c51048809403015040d03d2611117107880000100070f408680030550740000d000400940d800c00702c8009009040d00c03151603025620051205194025282da458001c1c0d2080001d080541001d1910001440c2481c2070f41012010840cac01004105540310781c49950b024103003031480c034100c581c07c01c0740040081500901d2150410041e0070b44600380c00b11134050300c80c90443c40a2401c9080150b807680800741a142c5403c545000d8009a8400c04c2c1c41c011581000b0340f1400380c0240f04980c42c200150003d4034881505903015540c0d0244501030752207216600000034001c0c0020104a4807600c140100103500506804071070b00403240340300c1607a0f480f030340105204600d0310400703442d0780007000014000d08541d07000461941d000681503081242c030050704020b645140d000c0e68040d50006500c01d0002c4a011200d0303620303124051040c040b80b40c440c0d02844c2c0008a41e00c1c0d02e0740c0320000341881e0045802580040d9425072101c1420050b02e5220860f14000c1c040680302c0e01c01043ca250740346aa503842c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 167346187 1250 167344937 167344943
    0x9080405010c1a10030507090c020604120c0816020f0d08030705130e101d160f0302120906010504200a0e03160b18060a02070311061e0c06070c0f 64
    0x64070ba034090600100e00c07002c02600104019400241c188400088203c500034481100c0e02e00a105002500f200c65108081e4602000e401030301c27140ea1396a40b000e96480002840c0000d000170384415030007052406000c0c007043d00584907103080c4200e07107004011240c049000343c28410074015800030002501c031020341c0d400c00c0c1345003070541d102d82d001c4505485403549900680c010f4590801005080d0280c0501501290340a808070210300f02c101c040000b0f00d010440b4000d00004001441034100740c4103c41c1c01d81203815514006051144005600401c1c10041d540800b140e803009005000303d10b0244600d1035100c860001e0040844036502c9684418007800e84002c061014440240b00c06450034020225075540079100c40030500d446041c060416040000601084070510001241074207224044500c9000c0076002001020319540c3c60f03541540c000e4403c2a0042c105208030304000460788401c0f040c202d5140d08058980d4036640960303103059001084501003142845441c004511f03241c0c805000780760 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 167347437 1250 167346187 167346197
    0x110c03070618181a0d0b040f150f0f05070309030914180702010e070f0303021c090504060909060b0105040f12060213061707080c0a050705070b03040804060806040908040501 76
    0x4403215800284915640600307511690300d00c0e5540e007246580c2c403903040c00702d003041c0b0b04001040b030b1800c1c42175054901100800d42132480d4007040100780742160b807484862050400300342d9600b0a4442c00142e42c28980e9520076280c44280b04848000c0a014195000040746010028a2082c0c1c500400c0c05948bc466100c0f15400d114040c03400752100e5640d1200c40440010303503d62401c110500078005c2940c404031407003e008401c008940c00c01568401c038100d80e0568021314900301c00500000d00d00c035080a604052000426000450751100d0050000400d042400000d40b40c4031410441e050301c0d94070b4900c0b81003000801090180c0701900c1c40355429070350380310800b0a40802510701040203100e00140c03024410580a00010030680c0611484d100c18a03c60300040652143d00068404203001e0340c1410a40c074050243c5410640300340040c002e1709008100700c83d40d0ba076450208440590040d40d098071255400141480b2082e0007052003504804151804c2000401c540c81d1101c10340118040d00381088 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 167348687 1250 167347437 167347457
    0x110414030c030706080a060608010302011d0f030609010207050c0f01090b0711060d0f0c18050103090320061b0405030c130b18060f03030c0606191a0901110c030706 72
    0x20300c0c2000303080035409010b03040740c05041c0c070313070300007825550084680301e26031070810740b02003810b40c41100c1c4681280d6044e10381048104e5012001c50a06614841c040d800c21802e201041003950f04000207806212104001130752402c0d50705020f8100840ca84d600ca0060b41101c2d41c412a6980c000d1518044568043c40c030781c1c0314200c600d80941d95446008815501440106030324000781d000e540b00c0e940740e44030360004101410003c8016104801e003006059001c42e02010704000550281d040741d00030313503c00d280c4441d88440004400c00800745c1e20024010b01d0b4080d00c2048550500c40000e00800c00918001c40c1c201464400025654860151540c0c007500000c800100b0031306243c1c00201011100500704008c0021280d603111900e03908072241440780881402c1300505080110807a14540c000c0406043c0c80c2d40c4107414007503c1d03005c041c40c41042d038008071000540c81190002c1c42d80081c3d001000785a42d28010000100945990750000c501600200c8036901c0c07a6400003902411110076007840c119107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 167349937 1250 167348687 167348689
    0x10c03021204030501060e0121060218060d0f0c05030925091803090f0803090607020f060a171b19030b33030c07240912030e01110414 59
    0x4024801c0000078000841d012003009019000241030714981c016417000d80ea030f02d100c95020f80809118280c030104c0c403040075001050181d002000300c2448400d0342c4e102654590003194890340440c04800609030f0740c0000401c550000c2c052402c01030410f1400d1030540c104801601e884844443c0d171802420315078031181c2c07400040058101e00400305a48100034180c01026101c0c0300c0705101108078002042c2210100f614412031008030f0036150803100440c208410902400a01e0b4418101668003820000074000d150f80c590b0014428000240d40d80c2c02d0038020b0b580c00441c0c05030050300c417030b448240b0304008107242c05544060303400701c075200152815201e200400130340060601e2815241c011000e10314801d50b18200400e02031202e070552561009603420300040d0324081c0015200407400c0d480820004000c215680c4c500c50400c128420340a107900010f0703108508440c1903035800c544505013280032400c0a0303014071604ca1900d400d58000e001c10400901070300141e105034001c100d03412000062085103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 167351187 1250 167349937 167349943
    0x201080a0b03160803031e070c0201030213170a0510180308060109080f0c0102162409080615010206060405072a061401050a081f091a0c0a091202030c010c0302 70
    0xe0082c004001c41040d1034000c10b40d141c0e1b100f140c0d8011010b442c00400031802943da0500c0d03104015035940ca5802001c80d03030045010b50f00c1a40c041c012414120030110b00c3d07024854840344020542c00040c090060303a0f1034424244000e02c2c00341307401c0760700d0001e103904481340b4a00c4510703003e585880c0c1500c699a5110050310306000c107070442131851040c60016068544e000541001401e07090f02100c00401e00240540550401e900170296614112142400b01409140e886444420309080241ca5252113441c200e10b084400c80341e0b8401c1c1c40919a041c040c40d42c06002c001e41200d0b040e01e003070003d032501c2c130000b8000009444203d18a41e4058403c0d415061190301004a819071006091144a50070b1640c000c00c250280503444c071542000d00c00103000c9500240e203e0709414008401565080b010710500000c003081d40301035503400b01202c1c1c440301030082d14500c6845181c2c038161803500c90304003240c02000010035810603541c2c6101602d031b007005039070000350202080703501f40f0380120140c085107001c0382 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 167352437 1250 167351187 167351203
    0x150402120703021b03031b1315090e010509040f030509011115071107030b19020c011b030b040204031109090a020d030e090a0203060d030e1c06060e090a0201080a0b03 73
    0x110380204000d010140740e1640041c8905140303403216100d5001c400c44002e490b88001c1e1407440c40030001800201c01019003001901d002c200c21203207000010780e00c510035905200c0c5440107900041c1c1e020000e1140c11050700715180503007410f40d1300703c0c100e2420340d4072a40f10410000780501440b001081034007160b84140120031803030310894107594100418400d00303407061a056440c00007281c40410340c00300700c80700024508100c1780c10248050f041e407600c100c291494840e1011455241d502040094443d0300240124403a04021114911f68206404030042c110380421841600c02c034010001000480d100044070160004100c3da084125121000036074a03201541400070340010905898805054200303183c0046032070180d49600999503240e032480c08910003122640c3e8015459009480480d10030f100914501001074091404041c0c80c0741e201500d9822020b045540c140c072070702c1c18400140c005e421160030000d074100800480070035600107810924004c02444106580d24510000f42c4e40c1001041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 167353687 1250 167352437 167352457
    0x9090c0f0c1e050703020a050f031009081e18010905010507080d0605040c11010f060e0103030e0406081002070606050d080403020111030415110f12030c07050106150c0326150402 78
    0x2c08518036a10340301361141d405200692040b040b2050004030341c200078021141c5220010080d2550410b02080800205018001942d400d101808402c00d540d048180c4030440400c80e1491544511001c0354041c640001c2100b20380c1044101c41e420046642c01005a40d0855030111000f07881e441d0406402c0b00811075940090b0b07005080c02080350003a900314840c0381010303181038003d0100c01c2d4a402284140c9034244964400798030110010004640b189000c5d541c0c08000900c045406560340000a1510100c4c51301101495800600c2d0000c01c20540b099600801c0107441c2c0a100c11955141ca01c05800f5a200c06810300440400c038520f110811310490303020340504241c451140d024007800803c48074046803014458452140030040c1088000345204413154808080c516540c0ca40b031103075060b508401c0c0c0c1180c00d07640b40d000101d002041c6071151010000302d50740b2400c0010751400c004000c4400e01c1c4099501050a802c240c9000d00d000c607445520400c0311400c0100c04001c84003103002441498001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 167354937 1250 167353687 167353733
    0x50d090804060509280e071b0605070207080f070515120103030c020f0f0d060b04060504061415030f010b13080109110406081f0b150a0c0309090c0f0c 66
    0x1c14683d030048040c2c02618020703a81c0d15003c50401091009251524141011844035200100a40808a0380d8254000c1e85440c0c8100b10710401030440c00c0250065074120b500e59298805c205200d5410032915008104980050000708010402580c50360168052070703010301c50400d120180000b2500845061a802000d071044039030b980c0c02e00412000520b1001c900c15103242c1d64040891900c48100c1030700410060408031061655a28a80100b0209a00c02d0b0495128140010b040d522440b03042d0042c030310381c0c5040203401a60010862202050700211700290f10a20a210410740c0f070748402410759001c1d113102980c900702d10305004802e1040e540075000765800c2014075000c0201000802a420100f41c80500c10703a500d900009494103004000080035044414814000c103402d41c10484408002030700e0340018603800c08010f030781940b0214056001c1440b8140c588200350744284002c000b80700082003000000f4210200804e55010b20421104000f840d144140c1808102c110040201d1421045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 167356187 1250 167354937 167354939
    0x5090f06040605190b0907031d0304030b01090e01020421051219030b1c020d02040b0405010e240d0303020703121a0301060b030708010512031e070b180d050d090804 72
    0x100506404c45040304104c41503441c03000c0002c6980990000e81400a051001503a9052000c50090000740d0040d44070150200b84507415410620044c000b030741c09040004265030401d42600d0a644031501d004102d0b070310420040040d0405182074841c11a44c1c030b01152a03c188a0600d50701d400c41c8112000f01081000400307a00c0b1480d006503031640303958151024030654410f8000c00080c1059107556090500301244000010f240c4854400f100c0b920060000078407004003c081821070710260080c9040e2901103040c070003c0b104510394542807030341000c15502e0504c21000803034622208000c004041c503070041031031030401d40038070f0302800000803155082100041c0306400c40f000c000d009941c14002d52900c1404285941c600080301e105070000d44030f054183c0d1820081c0715107145c00300b00c401d919020a100c1c00c501c2e025001610102044c040f0f00c81c3e46c80740307514104003c8501c2c0240000300d019a03070345e030384040350000801c48125000c84c1e800c110fa01e801101c0038060203440301c008000c214500000d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 167357437 1250 167356187 167356193
    0xa030e0613150509061803040306111210360e070f0801050606091002030705011e0f0e0a0204230f0103062706090f020d0c0812090a0905090f0604 64
    0x7495240724054031185240ca1105410802292416500c51071540c01860016004440c002d103005100007800044900d06546d0707440b882d003203030090a104030060f68000340e00382101411469050b0402d1125400e4585140b400300d04820703c00780407034096080120800400102c030030001203606160354405003030012000043c13465440304068017850360242c5003043c0c0410000014851a4030030440580366501e08401c081c10400e507810248242021440304200e40030005000780500101d108485510b050b8442079003480c0403c0d21408039008800ca840d00e004059402c10000c0c0d01c204041d0140d900190f121019a0402c0d88446880d00d43d0103120305010038440c0c480c20b02c9805034101c030b0042e80e0130800200c0c01d01c170f400c00314254003c5418440014000da0b0001c03850940c04203c0b05840344003010308841480d80816071801040c6001e5429041c000341c1001181c1d01400050781c0100c0010ba02490100804c000400d58181c2d4003a01008640e640d000034581c86003000440c41480c2c143d0b0465081d85800d00d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 167358687 1250 167357437 167357461
    0x201091e080105180c090a021905030402031c1d04150b0c0d02010b0a0605031e040f0b0106030b061b01020918180a0206190201150927080f0a030e06 65
    0x1c4140d48a540c039060004089429036010788907005030b40c40140a0b04802c600c104440c001002d42046403042c1d01f00f00011840341020f035000704e8410f964580c0351b00c0e8034181c0105810b000040414240400060082c6810680d1080100c2200300e0034054440d108500980824010580030030400000414608040340345285040a0049501038000710703080c003130900200701c0c240d5000c003020f15085100303044180030581c0203001865000380c007003c031560740c09400f000184104c1c0341038809640d4004c1160240c2d05001251490034090603050500784070704815040451414842c0900d080a00d044141e80404844000e4045551040000305201c1422100b8407045122240685501c400180c22030f6100c0b01d1034102013000100b06400502e010309205450181769600c0380c14901c03a02c01c555a9460006c11030a4081c00240074182c12100042e200854030511340899584408142e001c08030b01d20341100048078841120049020055910f443c0d1f0760281c000d601504004442d405103000d503e0030031403080365907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 167359937 1250 167358687 167358689
    0x10504090f0b0916090209060304120516110301230c070501090c03140d030603231908030702010b0307080705040207170f0a030f09030e1c0501020d0209090c04061205040201091e 78
    0x407540d0b011005070b6031603e40c03007207114901f00d880d0001c2c411f000007004656582021b030050307100c80c240545031400e00b18502420100070702003284c0b10603070390403d058039050034880e194181c212070302032012622a1228220350008018074000b100c90300001e00408022080d04408500c0794007152641007142c80c4c0ca080c406e02c0c0801c860407022403007210882c3ca0b015210303001d11001c0329009126100c91003100b01c201c010b11418100341504900c5891143e4451391603114108501038020b0114030740364148188000d00f903134290070049209601c180423300c80c0700c001241c00006c0714421140140d5032085494264800c4428102e0a02d58180c0802e020300c14402c14802003e08941c81c0d9000c1029805d1032403020f04171000403401030f0004280b00310101076410841001d01040d0b424481602e80e110a50741e600d400e80c1c0c000c030100712485401080081142c00c1c091102034010351031000382424a4103200b4000c12011031521002c10385a201d00200d000d42e406940d480010f09041180c01c0c3c0758044c0d1400c112010308003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 167361187 1250 167359937 167359963
    0x5151909060b0a0f08010b040308030c0705030a030e0d0c02061902070f030f02010f030c0804061a04020c16270c05070c060807090501030e0c0103090204110c0a12030203040803010504090f0b09 84
    0x15015140c4896105e128024161000c88103000c2c1403e0842d203540b510f6400080003064089010401180892402c0000c0c0407810001e95000c00d80c00140c41c01a8180b20004800b8820301c428003103240010b980d00b2f0207485002200c1003245030340340c2560b1403ca141281e80ea000b4207400c001e0000100521030841010520b56000303880f46a00741d840410308a003190920f002c20000141850302090004002e0341048240d25144032168015030304540003d02240d100c4034600300c241d40201408200046245107034001021604440003c03e640d0f000c1640c01859440180150607a4a480e049061401001901c00c2942c00100c0f1748441c0f51034000141c0b030f180003079441c440440c1b850103000400350b220b402410b441041280c003038000001c1503401503001c0c002c600700490340f154841440711034002c44c03d0041c00d00e0540d440020115403045041c9901070640380d4802404250041040001090141c81200c2c11a0790a0318001100d440c40e04000c9080b80020900401580c401010302606110001d040801c01603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 167362437 1250 167361187 167361197
    0x60a0305040609021002030714060c030408091201060902091206010605030408071a01060906080a0e031c0f0e0a03080108011401050907020a020909010626060c0f0c06190e0105151909060b0a 83
    0x280032700c1c51303550740c20071104802c5081d000c00024000402a202412039000054103502c400310b00c907036080b400e48840341c01a03174086501140002c010300e0400d031508107044010300a04000d5040c42402001c40c03000810241401000203210002c110548036544000b02c4c00401003980c958681c1c0005040f840c140c0b05200c000346000e80840e1040920713200783c52072600c0b070400031841c0000740c00300801f00040d0603000f82ca030b40ba51050f02003c062680c1c010507101d200814081d0200582c5460040c201e9541030300101d0752a071508003d40c40c0e0b00b2182d40035905441d02250060815030354100e080746091990380000750041d1380801482007408054010606403111058500400c0354011403050700e400c40c8026141c02d47d40000702250700f030b003408001404010601e141d480e20b803079542d50401d031411500351506200b8842000380400010001d21441100c072182000070321a9050418140d484800c10303620861142042d106100c6100c3c1025510b08002c042d10a0188001541c1d030a05000b00e0b00310501c07241c0858 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 167363687 1250 167362437 167362463
    0x2705060a05061e011202040b03010b0408060108031c0213050d0b0403020c120604080d020906160515041a06040f06030609122609030d06030b0604060b09060a03050406090210020307 79
    0x440c01c0f040340d11601c00c00704001c25011020200446110400d00c0420215940c200070100e070b505804c400440c0a4800c64109a644a00d0030b0710711494208141c0c001c07d0751750024000d43c20312511886c4c125800962001d00540c03a115200c0340344e15891020742c00386a10542203041c000c00c20010881c200d00c01e43c0281c080c1c0f4074020b800000c0c0240012110194186a080440014001698007026082180e002c1e800142040c1155021031802e621460310704640072501c1103900d0030040104400040d048648400c00301c14200b56a031915000e100700044405a540d00c40002c420b9140c03540050980d00055806102c41580da06142008002c50903050b02d140004004078000d95014820003403880c09d89400c2c14801c00c0920740c4003104260040c00b55440740c04200a2001c0214803409180050f5000e52190b0200341801d02c104000c0351855440a4201e0000703010f0400c1c0c0350b50b40d0050b11612062401c0c003003426074487c80d10000911801c80020744c4507071083c0c0d00e80f038074543c00006010441d1040c1c208071000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 167364937 1250 167363687 167363689
    0x80907080706020a021c0b01060c050d02070f0e0613020f07060b060304020102030901200111040503010c020c0609060d0902030f06040209250c051c1d060c0304092705060a0506 77
    0x240749503008100159118000007001070402003044804500054000e881490003030b0b0b03440401400a074000c0c000030704990303850742c14418244a112960b410314002040030510381504010248100d03c5103550080c42cac900090159200e10dc1c0450b41020400c00031540c0301d12810000f40c242c3c110040c2600c29504e000d1816441d030801390110303401550160015130a004000b0011110300350f8001c1505007052001c120400e00040900900e08400851500d4546580c00d020034903003103400e0450b03240c0840d80080703e860040d44a02c4212100c90400741c0b031041d6240741c0c2c62644e6000d4048030170002c1d010301c288110110309407000b080940c000c0d17100315000661526118200e202c0c28808110f07000c4044007005841c3c00c514061141e07001c0c56132140c010784902105508009038a0000043d001000c070308812440304c03c0f09001345441144200484009040c002c6021080e0740c0c900581c0600e081441d0741d0351048001800d20000500719a17108145003120340380754901151582c5080da0200180741c00c0001103102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 167366187 1250 167364937 167364943
    0x60b03010f021e04120b130f030201140c070f0308072c040506060f0901030515120c102f0109050304080c0a0f080309010c02011b0b06031204060507200603010608090708 74
    0x115112200d0400f5042017544411903510340c050800c0010200c2860210002070030701c651084030900940000034020318520f50001a0f0000a03e000b070031800c100000d80c0001d00c014040b140d200c0d01454001844c4d40c0c2c1c62400c0d1051228000010a40101680440610300014110140a580958003405180c94550030b000c013a0103901400000c0341c80074400c0c803190354030a51000b40e01000c5460700b88031031450701e004601100c40f00d002d100c00c82d81200110030702506040705044038404661500e0310302d40044800340910540691480ca01490400b04610002802504160f84031a008015a0382d915501e00f100e99880024482460045a030314600241c3c2078054ad48510031030b84e41070091031400c5460303001101d1100564804a0502240c00380790a9a0401074080841c00341c41100d811406040034010140f81142c030041016002d13000700814001c00e680070f401c1d42c40e025401564a0f4041c541032400140030010360200d01d42124000c4000a149544401d6990282d4459019034058036100c500e0903803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 167367437 1250 167366187 167366189
    0x19020f190f080111071b0302040e0102030a050f060604030204110c01050106050408060114060a0807210b09092803030905391c0510050a02120708011d04060b03010f021e04 75
    0x698544c20310a00010035407405002441c9002083c042c50010744a1707002608589400004c900300342e5002c001c025001d00e00e48a4203800c1032800e0100ca403545030480001c3d51920480c08001c0c05140c0b40c005075a03042c820101507580141c5e200d0000c0c012981c541c42c006280e90044e00c01d8005622900c5c000140d00c00c8050307070812004c0006407001e4a004c1c0c04040640d08440301905c42420010314210f4016044101c0c1e40045031081c450002140c00c44000c7d0800c03880c6080684071000541040f204862003000f41e103080d1060662009040c4407580103420160700a040c50300026105008004001c1c174401c10305c6144061485513080c6500307511107100c08041d082c0552103607564105c0d074600e0004002000d5501040348691040f0110343e202008400c441041c0c803410f403410098a50041400d190030b01941c00c00c0f9a00c140d141c50282020740c90044c41401e4251442120a003d14124001c50140070140c0c200d4080791401600a2040040b80c0156000a6105a03a00f6040d00c8030040481d00e13200c41541110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 167368687 1250 167367437 167367461
    0x130b070e010504031205130303020d18050604030209060d061b0f050307090e060a05031002040303031d10050403030e0a0b06030d020c130c0903050a0605060405060a050319020f190f0801 81
    0x64180f5045a030744244d41e0b104c403403c00f01845002d01c000d0601160140c0414003961113607010f007070b8200c64082c024003c01c481c03c0c40c0500b05000c030441441651194010707941101d07011684500c2a840b031a0100324108852000507041504128095038000da50180d0243e0890310b5680740d00e08400b62500442e501d00003035a0703e100190495008201c52036500440a802407001022010f14946c1c860000f46000c60801d4611141034000c103003042816003511600008050303007450f81d18495644003005032504008000081c946507030310b006c28281840780c1c0c014490120304e003080760420b01b507506240c6501c1e40101c81c802e11900c12016807d21042c40031580c003003628000307800768100005010f06240600302d0519203008000407144d000020444c10000701507154080c810000d840d040c118180000c1e2030004001300d000e4280040200400c0c4c4001a0404c41001d2000651032200c0c15480001d0b10240c09030320941d40079020707040340400b250125500c0303802c07280c100404528441e95400810f080c0c4400740581c0e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 167369937 1250 167368687 167368697
    0x21030a020c010c031b0809030102043f1506030c03060906110c0703140a0506010e090c04090812040204090204020a170a090b0105060a1803030507052118060403020603130b070e01 78
    0xb20140701c40d00c4200000c3c00d07225001d07490031708480301f001c2800c90b04158030041c8001d102e109403c00c110803500c10980d82d81005071706007801c610703000c0e61007104c5c50108a00814400c2c03407040c5903076540000d074020b40280d5440f503003411409540303082c44000341501d90410784d01030b403818940f4015010120101c651181c0c140020341269482d585032141505081c03000c6d4110b40c01620100000184140003c5d03020b4410840c8240307a40c24a24084c0e440c000300a0741e50b60240f86080e001d107011600b5a829030300b400c2940344000d86d0a9070360307102043c007a003510316009400c607001041d000c0002d40c0002013102141c64102c020042c5070340300e02008003a0360038101e01405c10101e0030018042800c043c1c000b0000d520042c24410395842c050035031001001da140c1e1055000a9022480b2000c11805001d42a920039125406001204400300d002a1512488a0100311108985001c8a2507103410066400a50b0000e2803203840740390451441440151025046824807036200000d40c0d80703030050031095a00d030381c10382d19 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 167371187 1250 167369937 167369957
    0x60f0b0f091b0a020312010e01030b010902070b1909051f0f05060a03020f010917070e090c10050a1b060b09011203050a080a1b030c08220b0621030a020c010c03 70
    0x42c1001c1a40105808011404200101d000030444000106d008056004040c8240d6255040180c0c9090301a081480034900421012001c1610061469004940c0d108250301d4154422010801003042c204d00408901901e40100d104826501c02d40304003202c0e1403c02e200c1e114000c41c03c0c5003110011590954095241c04082c00542084c10010150500605126110948540c003102c900d82881140c85d8039071b03010341801e000708034001103a240c0007505a00284170b8051a900042c1c1018602d1040b042084004074103020558424600c0404070343c401c00101c807000700d10742071400184c100140050300844c2c81000015540d8100560090a00d4255559500300300034003000300c6510f070000c0c0c80c0d040c846459a0070540c801c2200811300d5010390990b2400030720f200658401409a02004000c07400008104140d140d4009100c4102c425250340709842070841c0e40c07210002039903004110064078042402120001c1d2941d000401000400c3c0c1a80850f00f40140c210011034656503800801000144a41d074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 167372437 1250 167371187 167371231
    0xe06090d11071a0403080304062009010f081009020d06080106140d080304021807050d0c09140409080d0903110f06060a0b180301180201030b060c060f090703060f0b0f09 74
    0x7003410003d03207040103140076030341d0700c90540580094409444407559840c801c42c403800c3d107048c43c7e03c2041101c0c5180741002200000038101a0310f4060310f2050103405000504404074071300781600a002007500c11904c520300e00c40c2da030000b09a14082c15500e58038084003c103142c682c40e610007050041c010001013000e0740943d038240e0340d0b800240080340c1140355001281041c61181005074440c59131a42ca054840c95070340317070314000e4681204c1da20050241c4882c05010004144010003144441590046500c0a40340352032003852013401d180032480c601d4680a03004040c0c0c806980705c3c40100d90811a050a4901c100e0607450700d0042d65100d50005650400300034680030300d006051781d41c2c80710720b0812031201c03881d01090031f4a1080b0f11050038941c109400d01c007190303018450000b400e0300c00c0c0c40d0141082404808541c0e00c400c0500701c00c000c080f40c40e00044280d00d00300100009035520480a0041101001d0040c01030300012185a20030105220a8003070303420581c0050344601c00a92205209020441c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 167373687 1250 167372437 167372459
    0x6030314040f0b0a030e0a060911180114010c0605070503010617070e0d02011e03020d0606113c01020d0b03030a0e04050a02120f010317070c0303030b060403060e06090d1107 76
    0x1354038800d05480e56008a041c40040c042c05074140e004d85c0d808901340c0c040c3d180c000307500228030301060721454041e10518100007100080b1030540d8265405011a01e0211005a0f02d075140e010340107040301d050100b00504250322801450488070540c460510f04071440e005520718080c21520312000421340a150680391a1010003138044a0040c1400f1055403842107100c1d003e0a031041d580340200790002183c1906015511a40700107081c545011586241c010742d2140d120700031a40d10900b01d00d001010a020b15040440c0c20a65403d0741c06040344141400d202c60303010f0340000850782c0c100d51500402801a0034080100d419903c07040d07841c010400d9040c000c201c000c020191980c40b002d6801c1c8440061022543c0c4c00d24041c08030506c241d603840d0715600e00070303020105d403c0c5864801c0c1014016180044c454a4050050b01c0d85800c0208060b00b120001c46c401c1c2c0604d9001401c3d0740d090080302d90100d42c01160045c05109000241ca4140207105415209055030105400712503008210401c6184901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 167374937 1250 167373687 167373697
    0x10c080411060f120a0903110f0712110a0e090606010e1c050106120f0b09011404060902150304080703180602030f1b0a0c060e0411070b0901110a0306030314040f0b 72
    0x80e80036203003003013490a4074096140c0100c0d90000c0c26940e40a82c0d100b4190000c6401001c21900401018010354603c20140ca40e1912710401c003400544140110400c0321690342e942d41100040d240080180e614200800814404e5070204614010034011500c0303540714103180c1c4800f51020b0071032003400842d030b54625400c03404240242c40c0c5542c1d03507401060004c00d079100140c03901d004e440b1380c0001d80442d003080c0c00780080140107581c60380c0c546081c0d00240480071318156030003904050000352400b15800410401c60009000d242e000500004010800006030040c006036030107651a030350024a0920342c40e203044c00707600980001da8028411800d280c9001c82c002d080b103402640c00f0460040015030380d540390407410901201c6500003c0c1c02404000e502101403240e1160440b0140184a03540e02403040c580304441d030203070030300305100b001500304e0109400c05600c06060a061f20344e200c1e18110020020501030204400180d42c142201c52100103100c00d59003610802002c4481c094500850003205501ca = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 167376187 1250 167374937 167374957
    0x206090307080607050a020610060e010507030c0605130b06010e09060f04061805010e10050a12050a0c030b07020c0639120424080118020d150305010c08041106 70
    0x320940410300b95400d011090140e5150345605031500400e80000c1d05126008161610b45e5140d442c040042642c8a86000030b0070a0a003001b550316102c038101140d00031001e580160566050a0500c21000484001034003040d00402070403015442c0c54004507124011000c04a030b007c41c3c01c0c8042000380c80c0c060a132011549000700002034096441020101f62655001e00c050103d64a038010030490b1081441154480101e003407200c07842c0d040000142c0a80c5803801800e014040350700007902040000c001132070b400344e00b1540d071700000383c0d40c0d01d003040703104c0320480f18600140146400c1c035205040481c01d50300380300994850000c547c421803948981800200480c800b0403480c880c00c0556541051107d40110030f1141d18030b503900ca00380001c103690807481c001d165030b258202d0b020306075419070b00040c010306603540314444240d0307000c0e0440b104002e401058164140340d440d000707500c00c01c1140340c004402220311910092041e500b10000a0350119821070f8060890091100c140d0300c1403602000030b02034526 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 167377437 1250 167376187 167376193
    0x30b180402090a0209030613030906090305030d051b03040c0f0803070314070303090b0a050402030615060a030c050c0d020a020301140c121909030f02150702030f03041a27070b040302060903 83
    0x41d85c40c0000e40342020540d0b01c03010340e28a5210000c01e1560021007000075124500380079021901e1a03581c590740b44510300703080384000d0303070390000c2140c0754010740c8010548440c0c013004039128182410524100d00051049605980c41260005888180801a03458070717130b055260300703001895055400340d030383e44008011000c1554403051100091714160308240640c0612500055529291044c1850701e0005480034074005100314103940c50741d50b0941101e02214040c60042500c4a8001c0c095402c0c0c0a0b1440d04502402800f0f00400341c0c40c1c3c001902d41c1c03031034003c0b0000d02400e00200c0d052400100c0c03d03184525080c10801a0f245031646c8071049a42020701490103840e0001e25014000486030440710840004200d0420280c11650400106e8886811f04c43c0c00c03c06810a00000382d645e1003452040524442d010001805010468109070a04024110b0130300007450b20402091034603203814400d109d12600c40c000340c0303001c042c0003801c0000d64021080c003500e00340c1950200503140e041070030072550500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 167378687 1250 167377437 167377447
    0x904051e0c01092303120d0b040212060105090414090a06140705071704030803130506061002030313020604030615060807021204090f0b030706020304260d110a081801030b180402090a02 81
    0x41c40c2000b611141d06003600c1700c030742c9403561f103014442503800a83c1c1d0240705900620281c0304080c60000303070640011003420583d85d56105100410040c1c0100300264403e082c1030403c200040d100030a40454807445030008000c44040000c940f0b90101055130703884005401031081100007524030740b22009140100c00c000b030500b59240d035840090390044070712445880142c00454100700e01080781940056003111401103a501c820301c02542c0340401845090391580b00159102507403180800c640145801000c207102802040c80039030341490243c031a602c002803c01000841440c8040f44400e000401e01b03100c1c81c0f0301072505000d00040d20210803810b0b84250ba0383e03824281c0e030b42d04010880c0201010380242d80c03164506405800f9940302c2003038540408921000d180c40d1221701094a40c1c40d080c880c108507400842c600b28580c40c0194070400188800e0000850300c400d5054203500400855091380d05201e14030103003040c00221043c04001e500964844c01c08140145004100030b603101d015071600500300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 167379937 1250 167378687 167378689
    0xa0602130906030c0e06030307030c0213110c0102040f0f03170d240503011815020a0e030303150a0f0303020d0e1914040506100801031e020904051e0c010923 69
    0x2d8005601c202c44e00e0b61041070401035040d4903407209a2241c400c07405103003425115140540340c0e00182100034450141d034540466400901c1e8481442900070079407080e00e6051003402c0030f000b98420702600030300e80a0b003000003d141901c40001c00c02d0f43d61020b0600300f410960b01000c005030304841c2170117440e1625248442004440711107403c40d0305041480c200e0145250900749400c413801c030034813405090b0385040c00c038012903081400c182540e020010010f80d80c9170a2102250030031181070710302c0d0307040c00000140f05510504801d14054004111102d142c0641c1e60120104a80094807000303000d40c00c2002c000011034050928055207610180034402c2e150304c0380c0c40d80284001c1541281d4902c400d2071820f0180c1d428540310b0117a001509a860320910100741da0080c10000e01480700414031403900e8042c00784880560150344a10354003402270700d030b641028542591940c0d45240c03000c40307a406081c1d0006080300c000400003000036043c0c4600b0801810000f49410703540903003900d011140941d184401071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 167381187 1250 167379937 167379941
    0x60a08090a12020a060606020105092e050103081201120317100801020a020f0f0c09010e071202030109020c0f070614090a0b04060801151103030106030b030c0409030503071206080a06021309 83
    0x34803280364060420312140d454417008545183e008002160316040412002c0440080c0110b07020385826115808032007140080241d850b40c10010140303d40c24100004108240328014241d080f600241c10355a603a2520f22540980b03540d500042c00180e00d00074401c24140b142407015030005a0160344412054589000c1801da034000d884420059220401c1061a0340040c08075500c0174845401509948084000080e04100d060144028901a48020a0049014103900a0b90703040e0a90290f45035a5a20a00e10080d0805032440c0064003d00031600704122010480750141e592a458100d000c0701204010200741d00000000e0303401501205000c500030702c041000e4002070105580381d808544c10b00c00c5a608086030445114140140c1c4299130200201c040281d9042d544140b038000760001c0142c0000349821441e056042e001850580d0700b805140c1d01c48000c42c0305416640781c0404111005441e501116414480c44400e031b0040740110002440e5900200392003811038107001000c1c0d03200e01070241 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 167382437 1250 167381187 167381213
    0x90901080c18070c0b24030c310c0203040303092903090307080301090615110303010911190c03181202040e0109021002060703150503100f0f1e0e0c060a08090a 70
    0x1241484014010140d1000c1c86c0c6d801e2180744040e0003a00c1400c14100110321030194958007041400340020200d0245100790003091084805400b080c0400000740f41d001e91654028003080e400142407000218100c4514203482c000d00708095002c1803440415542c40c2c145400c05803040e103440c0000c200d80c0300443c0c01e02001d0350280645a90006450785400c4500b1560001a000c034018000900341c00040400e010003900c0c1180e025034408549040b0b02c0da213084c103621400c0d24031a10080c00c0c8602003045a40702039612045480303500c444141103074117416510708801c0e601c58414840c58150302000141825002510003d10a400102c0d80342101d0340040c40d0111159041c0005030300c060304004031170b41d0501031201c110041e9002d881615042c02c02090300c170311004001001c40c41e104c001045000c405a40100b20080c4540010407030a4914000403c00c00d8292944407000d50030700d000e03550034070301c00320304d50381eaa80008091501c1e241d083d04040c1d80c0781ca00108060918040d41881c8801b1841c0440030310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 167383687 1250 167382437 167382451
    0x2100504050a0306020306120f0703060e070e0114030601060e15130f0b03040b0a05040f081b01050a06090b04050603030703120605030303190509070501210b06070503090901080c18070c0b 82
    0x158407447e1a200340007001d1035130f000090301507002c607031082080301d0045a50419070b5000100844c07544052a00d2a191602d5640100d00302c4500d8800003451031004020f40720601c0c1c088003514020b0b40c0c1d84008540b00c40c09507034a1588495004104004107441d18004e014041da40e0380c21700103080d950460135400a8299006116003100002088204000324841c140d001076030440801c1a4103040c1c598200080404000420600ac0003810f00220010484000152003001000380200c0c94840316803409030189200f1140b00e24141417540310b40f4034050152501c42c00703018006509040d001c2c0c400312494251000da41d440150399400109450f101800194030688200300c04090700f25900e41c07031608440c00289078400c541c00900e01408107a038040890400701c03110101a0070500c8481c0502d0008142d5803602c164410400941c0d04100302012010302010003045528804036a0780f90022900c03020940340e4142c1c05030b01e03035031000c148501c00c512260f00a001845c054115105607079904600c03510176a204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 167384937 1250 167383687 167383691
    0xf120319030b10022518050702010207150e1212060603061201090b0103030e060a09050f0111010501080706320a0e100309060f06030b0f13080f03070311041202100504050a0306 77
    0xc518500051449502100c1c8405d030020450352824856003010b044d4015400d80c055291008035050724402d40541e0311a607086140d45100c004400302d880000c1c000300705903c86500400c0080c0e245180507000382ca1984141603444101c61b5a40010090f07107070310050841d58031010022003011208002d1182400c40c03803280b1401c08465045042c00740c6038500401c45940b040700108000389400350b02850f000200c03241528031050040c03210005980745100d40e07412104661070500001030300e01000924100329002521203c4600000f21100401240c0c030443d9900b4651a840800c4150b100341002401c0b1400103151803050318144800040880480800e000700183c0c4512580b030a0081900c42d4540c0b1403c3c2041c02c21149185030740c1e01004000041c01c200b85070300c0311800601001c0d848000d984001b540b08034001da946231030300e100d401103030019038454001030716221103448a1040181100c01351804008281ea02c40c1e015401c0004800c5510404403c110017840f00150589442c0c020b500518803c10740 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 167386187 1250 167384937 167384953
    0x2070b0a02060f010b04030503070f0606170304031a0906131b06020610060207081005040804030b0f04060605010804170c1501150813030c0b090106030b0408090f120319030b1002 78
    0xc01c0c40d920a042e00328480c80b171801c0100b00005a8000210380b1525848101c051140c80141402d0000302401e03404000a068031804140c0420310120081050b2442050002810b01e0001010708603002c04581e200c105901c440701080e148980c0714842c0c22042c3c8521150210707045240350440143d00c40758410710242e0700c00418011034445014485000d0300c10340c03005102c0685000380c011ba40300422800c030940107980d100400c0c1400001d6044030040c42e005a07050400e8146122001c044c50005c0b10f00359841c601d402000304083d842840800e01076034020382e00790704d42402c00309822200d90103401e01c5000340c840d0500004019207150340d418020320600c214503441400500014052503001486948591007102c100800a90055a52003159400c1b000c250002d0341ca00100c0307801030401b500041d0104440c0c2c820441000103a100a110380072054418042c0c1021003024001d41c19240c2071040410340042c004e440c00d20707180d200d4882e81440c540c0b03004108981d602006c0f5881c40c80c081a44001a000045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 167387437 1250 167386187 167386201
    0x3040f03050d030908041403070504140f0a0509060406020903100c120609021216050c16030c08010b130507090e040506010801180c06051812010c0f0e06031602070b0a0206 75
    0x1242a0225900341004d02c4101035a50f6904180d2246009100903640085415949501c04000e058054000900100052481520300c110300603401c58440c8500706900340019280e0395607001d40c6018140040042200f0f072542e5a410780650840ca514917014491710b09030140c01100340c0240c1c5103003481740c1ca600d18104a140300d030905681e9039420803260380d03004100120f507602c008e40c0d11640c0181085107a00510310000c400b29007521500c42c0303072140c52046101307100542040707188010440b440384109803120799450f5030351404d0b00c0c05281002c1e44400918490b01240e51a5009070b0b510203190316200d5070b810789a10020640302c0040c0e5081c1d5507a03102c1c3c001406101000d12a100c140e000f0055480d40310340642c2da5240ca40401d9014080c06c0080104030b006907149255940606c01400a000001d1244441b541c01c1c020120f03022000001482078958044103801510b992050007400b0301880d01d10703030340c48101071f10040341000d0b075a04600c41c030078000600b50358081c003074408103448c0e5002d04420f0902c42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 167388687 1250 167387437 167387443
    0x130b09040b060f040b031c020102120109020415080f0a05150a1e17120a021906020703090e060f04110c1f060f05130507020a21090b030f0c0f090303040f0305 69
    0xf0745250180d46484407001884c2d9000903401407243c280c0e00c500074168840a002c80c00ba015600030fa003030020141c00049100312194000c1c0c41a02c0002c0c50301414080305804c100d0304110240c0c0ca1032180000d42c00404c170300c003c81d40c1040d98405e0700324520317003064070709003011401d10750f4542d214251910b04618110654581d1210400c004d201041c040b003501d070300f60740300140c45548428620070007810000e062014140240400800c5800c1d22222811030041410f08001039404151f00310005903004101244049280c4081401028050b1551101040070307000d00004241e82a0010f0640c1c10612000c4c824070810066802404941c2c0394a100500c1445215003d80700c00d80c000002c0c6000c0c082c02400306483c1c80b8003410059058600c081010b40320917030264101109528080d1207000c00801420301c0d2001c072085101805000d40d58040741951f22202422103000035904206106020804181007403a550098100355110319000c5181c00540000240f41d54001c3d4000f241d0704480c0c0000b002840018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 167389937 1250 167388687 167388709
    0x30b01120b0105030727030b06120d021903050702060a09081506030c010305040f020a0b0301080c030106030206070609030203040b0403060b0406051e10020c0301140f0601050414130b09040b06 84
    0x4110140501c0c031200c00043d09600005080300704001080c9000c013a400781c000302280c000c50322000c89440e21078403410000c00b00d14003200ca06002c2c100d101c19880c1241400a0580102c2015a015094410408507840214101407000f07404002041c403d403400342e42c8100042c44c5021040c1c40b00000b1910341400c4900304690707003a0f02030f500c03480e9400f044400d440202c3c018103000001d182c0000c0f19035071841c00c240c01d20214039002c2e401401002c1c01041460014008606035001031007158012010501010f00b130711940c0c00020341051051000714000342a6421907103881d80f007801134904203070300d0f0003003400690015441035030120303240d06990820f801c0c0780c071604010304021780b80310000810031045040e4070b0190b010010300a81014131264043c51003409103e200b801c0080091050110242e46055050400d076952110720f888800880c0296004104a808488149103650801d240003c00c2011080d5150b50a03030340c064440d86c00202c1640c5030286544103034814404100d4506040c004d0080310111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 167391187 1250 167389937 167389967
    0xc070b03010b0f0d0e0f0c090610090e0705090d21050306010e0f061e07060c05070c09050702190b040c0906211e030915050331050706030b01 62
    0xc100600203140480101c641c0d0a040c44800c0e40d0b0354002c028007400410081040345003038042e0300308281800354007184281d240a400c581c030705c07242d0712001c04001002480416480c081064404200030402e0142c5070103a029196081483c02c0003080c1020801d1b80b40581012980300b0300d0011f60000e041400d8a1180480140d07250042c00e500d00000042c00c02d41c2108159445640f40227800045981c40c4421900c00402e8202c46441c0a4520380e5810350075001b42030304451840c141814104582d00c940e090b203c40c0d940001410010703615202e00c540080c40043d14001c1140101c043d0b9882244a110315080864801c0c030002035645090b08010190b01c10310b80180c0a260305000040000704c0100c590320400d0000603c501042c83e0076441d00c5900000303002441c6003080561b02e490018560041d000c201194101d090106150f0001c41c1c0032200e522086800d83d2215000d031140710103400c0030305402600f41c2c8107030b0422043d074007403900c5051800c1001c0c0d2080c40001c2d00ca800254003940c0c403007010045142 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 167392437 1250 167391187 167391209
    0xb10110106060503160c05070510090807090e0c060c0a050a0309090c08012702130314060a020f03040b04142b020a0f020f18040804050414090604080a1709030c07 71
    0x28140346071071401034034404180421143c0d002c40000d1000608c03202005050050000211210b214805050a0201d04c03401c411400760a2002503800f02a02501498a908002a00200304900104090384c2c10550320036402c0c2c820f80003c0030000303e0406c04840721078002d8a4003070302940351880003815140031010f504200801c84004000d506a489403204480d0142d040f218032080034092820000c2c0520b4a01411603890170364004140840d0030050800c1266200585880ba540d1480c3d540603441aa440d00020b15402c00c00174003c28064140644c001d0301c521104410308103440c0300185040c40c40c072000b020038800b4504503603494017040800341100c2805e0018103044079481d01c4080745c0d0680c145c00a80100d840f800c212110743d6031000010302d8500501a07003000c600381030800d102e42e600140142070140f4a85a070440b00c0400c00741c600c500c81c10003e80144410303990390b603c550070340e04244880320174042802075002e40b00d902d402c0c1261082d0703035900c001c507115001c600307103140380440b40c3e40b010b02942c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 167393687 1250 167392437 167392441
    0x40b1006111c031419060614120601030906020a17060321090a0b0d0603030306090504050613050c040216050c0405011802090a030b01090c03051005010f11010b10110106060503 77
    0x60020540760a200c20107041c0204003210100700354060004c65424494554903c070420100781070b140d59512010b40c025008110980e00c411086d580c0d407034000300d400d008100602804080000c4000c1490b44844189008180071403140d680300c06903000121001c0100b4421140b0a240b00340195030036900100c05c81c0100808400304860b03161060940303a90360f611080c002003a02c810b859071000c040042c000e05e103140d5960040b0414084c0100340b42c0c00114006820704c80005003809071401800c1c0078030340200103010542c13110903100d0480d810000c4200c03884d020380c49404066541c2d51025080c2821440b40b1050107825034038203182040c000384000361007a071070140140007818403545100c1c006030840c40c006964001080001d03072010001e61006200d5001e5000105600c00c080e00310300715000442d20140034030b44404a581004014a000741d500058000c40007040062181c00308280840300f220000a1480c0da00012507000310441141d04007181401c558110845001d101d114003c12070761908038114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 167394937 1250 167393687 167393717
    0x41406060603061302030a09050304060809070e100e100f0902040303091208120903040503070303050901020105070c021c0206130608090f160303200706021f05010e060904050a050105040b1006 84
    0x84da6914400341c0307071140d0110008a042e1030f680d01c0140d1309a00802129119940c410303004007810f4084a03c0b0005000d000c1000a802500c850b9090154040030b04001c00740d410103e204103000e900520064141c0c1c2010030019048600c0b01222010302051170016955905505018054814035406600790401005030000420010400c2d916004103112140d011525074420141c41c43c0100e411007035060040342c400000b0140c204000b0005034100b0f800a20066445070030a40d001045068041e40108410031441c0c2c1440c050000d51001070310003000b080c10252800329070102d244c1d990b042000031a41120910171500c0c010008401c2d040380c0007000300410003840c01503071103005d0a031100900b44400221210003980304142d615100c014510100c50040c0d585940c029038030b03004074039001401c81c448102095116001c2c000e9606030740b48000385c00c070720341c8600060014203c0000c106584500484003410001242030103694000d6020300020425810075007000d85101c82c255001a02740000c0344408448 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 167396187 1250 167394937 167394949
    0x9120c0f010e060426011b0f0c0308010312030207050a050c010305061c02040b010e100207150906090b03040809030307060c030506100c0b0601050c12071505061507020103060504020304140606060306 87
    0xd40380011001012204082501c0112101ca2145c0c01d500d5424007807054040c01a03107021800c0d1024540e25407895440032001a654a60701040242c006454640188045440707003902102d154a1490010700e88016912010f0902d40c0c03400c8204c40c15000700000040a40e4103014040d0401c070308a0b550f0f241c40030701008012110781d0071300000f4000d6460f03274159001e90f070040b18168082e64010b443e0007000907856200a46030600c50140480000f05c01481541036441a801c05099030341c941c598841183c2494191460340d08002c00442d10600100b042c072049440901c00340004c0f80c40748d1408184100d0050026050720781c0244428060300140c501d0301c2255901000740b01010b500004440505d456180048507184035051015403280f281c0504c4c00c070212100f400034540e8a00070300b84843c0c103048a0310983c003514400e41d6420b82c040003c100e0350703125a00300c0008210b001d1050600290550361400401d003a44c02c00ca8017551801000300b9000708184c021700845900c8041160280d113945482400951 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 167397437 1250 167396187 167396189
    0xb03030403030815040e0606180601020a0308151906080c13030308070309060c021e0303011d0705040801140106030b0d1e060209042a0f020c0108090309120c0f010e0604 74
    0x100510f12001c40c8500030740e11302491328200050020303c02414440c41a5a41e490195515405000c822141003408a035000f00c00f405028140e018120407e643e44080741c50141c080c04202c003142c40e00302020407035500c000d220028079002044441403071b450312a0140014030020f041300d000c04010840c3d4040e8250800445055903850300b008280c0751600c1104500903e204517004106600e042c81c02c0c07240e01d8001603102450400300703103007580420070b03190525280d01081c13044101c4c44254400c1040022080011b4517440060703803501900f0300390303194446c509403514940004140410840148001035060040b5114103800342c5032884901c0d0305a4903084c43c806221000b20340c0031104202d0030b00300f00480c0c044031b01d005001002030024100d407480074010b0b21b40c54080020481c5002415000d10760150340c0d03001c100040c50f005404400d000000541c2e98840c024080707810381c00100401318a6a42c0c0c0060034560a0300400101506802c0d28180008001100991818881c40250080007940c03810b04541c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 167398687 1250 167397437 167397443
    0x212040305030a05030c0919150c05060c09060c10090b0a150501110a06020f09010e0306151c05011d010e010e060117120301120c0501090302010e0103050718030507080609010b03030403 81
    0x7558070750703074441404110f000c1c0c9480148c0c4484550300030b82c40c098000881805941c0c4060f2110700c0e1050303000c000e5407801200c507001400c0750003070b1000801c4111020080c3c05e44210141803140380c08036081150b410f04243c2132249840f01da0ba200a031007804400c1c54000d5015980d414200000c0303420a402201f03141c1507209441c100402d00d00003500988013030200c3c00b00180d10407415510b03040c0b00ac0000049420680425000412151a444840c0380c0040c0c40380c010300b428280048901c4921003444950060314001d4900302801d107041d000001c3c4244140060003411000e00d800c0500d0f0714500d00d0a58480440f040d0f4175a040801081c503070701c00424600d0454111650600c0d0039088030003118289560b506030540000804000042c9294010b40c0c00011a4441c0040201d0507460300015220a4240d00000c1c5c00074110020340881c0754000d91000c0d0304000103040004489800504800d4030b982150401c03916604000007c000300c901c10404182c0080c0702800a010700240600401d1b520300880c0f10103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 167399937 1250 167398687 167398697
    0x10060f0f0c11120a0b0a0b010e1e010302091201050702011a0f0f031c08090c040207080708070c030b0108030705061005030a0f08090d03090602100b0108131712070212040305030a 78
    0x150310b260342d03114815080000002c058a1012400c0c1c1411300e9129422500c901055007440445006588903540d00030345110700401210300b40c0030030090003a025140110ba05d040c9942000054010350316910029040c01940002094614000a00a080d04c646140e000601803440c0001d811568800ea000346014005480160848482c0000645040841c00c0002c640b0418020711081556004907010b10440410045611541000041c0800ca210700d08001c2c10140c002d0040b040022683e000501c42c0300e000394202d40d2556100d469449005400303070700640309984005071039010004103101050b40f00d4012406240000e142c040400d454108001d00144001c0740e0520070410000010140c54480300c001c0c0c184020704501c2e06c0c010f414604140100c40140c45050001c0c902406140621403101006075606062525030b0401e8907101d4600e0a0304848006821142c0c241d00994500035001a440c1e01440e0300709420843c00c081e0500e840c40d0a08803944d6001c202c00c0c80424000011100002c00364680 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 167401187 1250 167399937 167399963
    0x3060f05160e031e030d06030b0115020609120711040606120612050a080a2007050405090303160e0a0302060f070b0108030304030e0f12030c07150f27030b10060f0f0c 73
    0x2650030346c41075503042d10040d441d0000c04400d01c046110b0f201d060703071391440303140e03002c5d9200000a036501c42d0304645200c41e0742d0011040014541009000d00740380c07071007402e1340d0510b5025000000c094490030f810175000192b00d59040d0100580724024600245000304040340b0460558456940780d400d80800034010b8040040d810400c2c61180c1e060140100340d8858000d0500101519036448628903c1914403480c20b04020500285011040702d0080006051148610b1601e1005440d00c84908041c10782c0500c0c83d85000000d030b115100104044000250003a81d0f0f40014a814444600181c02100722540107004020009030004d9007545078040131200003110500708000114040c80b03900d50150280000304581e1003100c00042c124ac1910011070242100450549003190840d5510f000c80340069800c06582030341c540c0c3c812001603903603982d000018602da1240c40c0c005040c3e6082e109032040c042d40050820625902c81110001c1c10414500a000e54010b04001030406548100103440c424400705 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 167402437 1250 167401187 167401243
    0xa050d03090f0e0f0a021603080403020102130807031a0106020601030605060409080d020703020c040c0c030c15020403030203180402030126151003031d181003060f05160e03 76
    0x3003030041c0003014040c480d4685507481c000f0380d04401e03a2940f411422800100d10305c140d6a0003554442901503418400321016520110f0383c0c00c6000c0e10a8095550802c40b83d620720414030380e154080e200c41d0000b000011310303524080401e0748070a40140b410340b40640051007030a90101c5e02d1030450350810030102d401c1c2c6656001074020a103489004144450001d8007901c00c01d01798000c0c20043c1d0194090b1440c500303c0340148000c1d5500518004001004400e0a000007800750348210041c3d4060408810564401901d0030708036031154000354007681c004142d00c900e01240031385031503201100741d4066003903500d0140c1c421902c01c021410044881078066940c11081c4042111888001c11003014400a04100c5c5016615034a50b003c01c0e8000b0710341d801110100e150100400c080f0000c0940f444000f8100440c3c03881d50f0a030080c040c0203445010080001c046603041c0905012001c801c540029242000d60201d144215810b1001081c131104250082c1035581c0070407025a0b074003054500201c6422001c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 167403687 1250 167402437 167402447
    0x6080c13050c1c0b0a180b0d020306061306050315010f08010b0a030f020d02040606050301090b090112030c0201111c0f030e0c01050307050d0e1c080f1f0e190b010c020a050d03 77
    0x31000d517049503900000140c440a0014074090441c00b02404020a04803601807281c03a050021029405502c400c0c045906810212011001c90107005070001c2d0b00d03900c610010b800c0000b02184000c12040f40c5005000000106d0720200007000ca4034001c0101840f10744c0030820362880361001400044580c2664419034a8040302d03a004281d004100304205602daa1005d002500280034400c8a149000e003079100d40c0c108039402506840c5a039407a443c0c4000d0035030f0122035a900700a4102d04005004001c20007805003004000e050112000d100754940c40007000040c0101246c2410108260400d81c10141c0e403500803402e100610401c2c1b0344560750341d840e000706860500c00d0000c4003001600d0b000070041d40400104080c0720707104800d211400240a0301d03504445600041d110814481c0d00784002c181022520840000d501110102030080c81d5a18003100003020400c82c1c000300b1880340c1c07040d100303103c0c501441084101c40c001d080504206203103401080049010303005903070096070488806c80500d8020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 167404937 1250 167403687 167403701
    0xc0201081314010e0f030403020604090209030313030302010c02060a1107020111010b0307081005100b0f0306030709050f0a11160b060d06110712050f070b130606080c13050c1c 77
    0xe00c0b54115022081c626802001c070150760f04054010101c080111a130080101d50490360000c14042c03c0c01e08082030a002580040c1805131305100401c02c3c05000c55030406a0030003103010b41c000080c1c5182241c006410494000c104c5c0f00014500f0451101c19159a0151232030a9028a0103c40084a089a1074014200e607416158148552200000c5020001802140840d05103106010549071040000d0455001e07004805110006101e0307042e0700f01d500405580d01413070080482e098103943e036803034600700d520a0301d0036400390512004109803a4028000c82528110426001c0d207804a0307008050740242551000500700105c110200d0072617564414071008450708400c0400807800c00104a03495907009038400c03100c407401c02e4000d4020b0743c040c00555896a2601070500d103005002e0f99401c080210003800c0b507584046914982d804100380340318403009004c120004105c1c0c042a001000403580400c80182c001e681464100091410f49c4407e6880403405500280c04420380703503e00d50041c2602e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 167406187 1250 167404937 167404943
    0x9010c03030c0c0233031501050f0d05010b091801030816030e06040801021e03010303020c060c0a0f080901110102091c020105190806010f020d080708220c0e160c02010813 75
    0x21700307080106104201800754840d5a0141c94600c2c0941d10601c0314941c901045560022004003111413104c3c65000d400104215102010078901d408070000b4003004485d820b0f0800ca601c40004112001d041c00c04446490210100002096141d032442e501d1460511551040d580e030461b000042d10b0030140110103483e041400100303100e0311281c880d10441d000790004981100c41e1b4143e4a200321180c0740e1907085074143d83d099030160050380032807410b00c01c0c07a074052500c107151032003640d2112000c24144040070609a01c60101959142d0840c03000600300000c0c9103210300c01d640704118800c02651030802401040f2076006101c40952418001660175024040050109040b50300e25200b50329800078195100304003d80751070720701c901420703401c07644c40c11606180741c0458184400b03d201c1c02d014400159100311a07045141c01907401400301d40b54100325441c03c0b01c01c224488000c1c49214007100c031071903114120001c2d17114642c001103402403003002c920001906004044c00440e0b10280c180c0403001140f50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 167407437 1250 167406187 167406199
    0x40f020c030301030f030201060f0b030705072d0302010e010623010302040e090106031e0201120b0609150706180b07030504050109080c060612011b031812021501050609010c03030c0c02 81
    0x2071340781002c15542c0c1c3c0d0328804030019403030400701040514000d046a0250341800e0082030540d82c4451098841c1da00000d026100c02c07080344c1c1d01131081d103103144800c980741d49150300e04503103401940317030181c04e481c3c150842e4a61a410101c00348039a540c0099810030790800400c3d005c00d4110344c580141d000b40b003548c100b400399034240c10801444c81015040b030002ca0b0b114000035010f090140b400d424603c2c26030800240065262059603081d810350b5044005264401018540b800e0b0b00d05000454020300c4000852420b0700104000c82170000a201b02280e04405074503041c03441c05241c0e0b0385603404000502090a16543d940460b0078480258850f101d41544106030076520100c04451603980c04044451034404c9283e0710410000c407806006411400349820981c04081040d95000c0d40607064040e80d828100d10550010b00200d9100915041c1c0040941c02501051114400b0030342e01c0101600300174010101001413000303503603010020401c200d8041c6000950300c9007200048a0f00018624040d501c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 167408687 1250 167407437 167407439
    0x806040320010b09070e04060f06090602010b0a15080a020f030f010311040c0f0c020f090f090615030c060f1201030c15181401180603023402040f020c030301 69
    0x5078002240c0510800c2050030030300c07640a202466426038644000164001d0404008680707181c0c002c0110002c00000104042a1507865040603454003406520420005400f82c10403c801902881089a03040d801c1d1000000242030042e400b00070744000c00d590003040070340c000003548003c803581a0b6a4030715510060f26034a04003010242810202800207131a44072450980c0c02c0d40d85014464235041d0030903274031078190790094100c003654001d64000007643c01282c03490050040f0780c0d400890344d01c9954266598241030405d11003d5191072401405207181200e92808200103660020300d640c540d0004803002035583c0340ba13441c0080396002c3d00300e510f40f0b14052000040f0070400c04022900c1644e10080307034500c01c1c0c00d01180440381d030003075070702d103601020300d44401800b203109030b04288014010103040c003489040010203510014011a4403900c00640e001c03505d5060240e10f602c501003041e41d20203a0400e403504060801a982c000000028400c03561741c640383e005070050b5015540c1c00300c03510054a860b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 167409937 1250 167408687 167408693
    0x51908010203010620030306010c0b07030207151a06030702061609080d0305010806060103090f0b06040e1c08060d0b0f22050114010801020304081b100e1c09061202090a080604 77
    0x200d0300007002c5c1a548101c1655030300c1c00010010503213100e900b050b51030106206554403103607081007018225908154080140300c012643c901c002d541d0080c400e007000514a00e8000007454448803264010b03101d2401041444099540020203d80048240c1040010b01d0172008054804440c0c590015460b8007500320030790002078255101604840392981a51429980c0360011002c40e00d040000130030321a5210b001074003294402100b01c0d44084003400014000743c6000b1074529204503100881030f0980c85a414240c0c455200348141d070007100c00d807100d140c29542d40d910815042c8005112040304902e5000042e19640039400c2e01407400000010300c00c1405003820058041c1075000031004080c010780000141c50001482102c0c400ca40043c1014182001c000d1460400ca1841120342510300c100703e0103100b441036a00c00c071440070145d50b0007420740148030101da0040c1035100815106000800c1c00c10050960000740c1b41161103508800143d89044c0c00d400500c540392150032200d080e1003560204010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 167411187 1250 167409937 167409947
    0x304030813140d02060f102702040e10060e0609090403170c0c0f0a020f22021206010e0a030519031107080a050f070609060806040b0301050c03060a0f0305070519080102030106 77
    0x80d290a44c26144142d40302008143d0001c010344800000c00882c0c0010003925070032082491505441c051941c0c0710407182c080500c03c0e0b8126400441607040c40805004100e11003040510060916040028122681400090300f170f00038485c13041d01400c2c10354006020148641801022450254102d80947c1810f5583d0006a04001001860341c407500f04450003000000a1040501e50300414007a8120600d03030901c0891200c080c40f05003c98440c25640103086041e0014004a8176030b1001c412040c98680001071040030040809405526400014000f14002040c14068030340c03668403803010004c00345000caa002c108c900410344540201500410035040110741412914082c00032030707489905400c3d009440e0905032181c1d40125030418800c202d41c602505402d940440d004100140250021010909546007254503484100c400003c00c001454113802401c0501100444100e0217070035075807803030303660f291900032030b1310403100c065542a408120800f640e015251960007035449513505e48020b40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 167412437 1250 167411187 167411203
    0x9030807111c1107090c0e040b091611100e1c1403060906041b020d1b05060406020f04030203070b0d060e07021b010905040603030809061b030403081314 67
    0x2a00005500110040c0080e0346100b9500d02c0c41c10440902201c6401d4400141411103d0001c1c060300303000040755160b07445005450f001d240c5a40c00f45c0c4e4550010082260203001c4118403600d16802030168101000000802298450810b0389a0419003080980b80488885115400504000c0d040801c044c0111b62802c00007802c04003000e408001c000180d5000c8182d40001c0b0100106000244461400c0d034541500b041015000040c1d540500d440c1c081c03840e40012010700543c1c081070260700180e901c41ca42c2c6074061a46415000f125103150745290322400c014001510b00c940105200c60417402c0201180d006550040488800c241c2e81c1a0102060304042100c4001a03e018000245140304e8920f041c42182c0c15400750205105c21494244100c9a84264504002c8880004555900d40307116030301c0918080e840d803502510740a4000303440c0100003040c11088020703084019403011607520646e03030060340c07604210b511940c0d0701c58090705400700154080d0119401e56080b803003240700840c080d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 167413687 1250 167412437 167412451
    0x4080d18120c020d0f0f0f03050901091a0a0302031806070f08130f030807090915030212120a08040501021e070b10141e04020d0c180302090f09030d090308 68
    0x1400c01111a090b01c0511804401a4000400e40940c10001d189845000c0c50749220300d20350b22500700c00e62250f40e9021580e800c100e01246000400298135a001002440202001c0310b9151504020351130104031405249401000c0c0340c0c0210101d8580d400041c14a044140c1070001c5a42ca45814000200b00e503203c0c400480200c1c00000106902c0b0280900c0140c400784c001006400c0f03c8559034040f21500c800a04034401c10012100c089441802c0e80141d03803900fa070071411111000e08600400c04411050001c82821350f003d00c01584074180c1440640e0350400050800ca4529030b140d0030240e019100c1c501c14640c0003020034207410509048a00a8101e80d0300850f03800c00715590399807072107a1a107540c0c041c100142100c0190050780d0b10b42040403010b0003698644461484c2004000f2505980080804d5210740782c40d43e0902c403603941c3c001e0b07042004082250581c4191031554010560180c00680400c2150000e840055007103c020011980c1c0d54a0010f410014041107050007400960161040303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 167414937 1250 167413687 167413703
    0x7050402070605071202070803010509070c050604031808031305060901050f03010803030714070203070e070203040302150c0d3623100207060212090406170a05010b0405070e0904080d18 81
    0x200417a040399200392140710394008a40d601d140d0038001000329940000f018402000003103000240024401d2041a0280d40710341ca40441c2c401c407130b01120030080c48540040d02107034001d210072085e071f039194513a403c2112415603000e40c7d110f0190004841c80d1080741e40c89100b8800000001900900000040d441811aa91010344c3c202111400301000d02c40c50402a60540c88990300340310400b032030140345400c0710303490048030b161a07580e50200350a100300031710b0420700c42e1001c182050903140510000c03a404031a0302c1c04e510005c40c0e040480241c4010000c0810703603212152440228481c1502540300a4080030f0038624891315004260302100407000d4502e1300450b90303030704140b10b241d000148045c103440b6550040d0100215086003e81c0303582100e10020381c0700d51900c1000031419020350300c6c80b4030108510050601d00350b2a0410b50309440038800d85c90700407840c0804024404c0da001038201c00140c0100d44100d070940303403410702c1003243c02401c01e092000c40c6421407401115603040a445d070164844c2e441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 167416187 1250 167414937 167414957
    0x22060506040e060108190c020a061b090b030c13080a050d020d090506250302060f01050a0302011710080303010902300f07090b0d0209091015110705040207060507 71
    0x61118600a510842d0315001c000c40100c0e24a40c020f0f10341680c84121500c841c0002c039400c07800304082e5803500601c0c0c40035811140d50002807201c035001305030304200e6070b0100741124040050018105405031160340342241020010404008a6008645803c1c00b0781a0154601ea1a12640c503120400071000300e48621522076070400c05800031840e0001c40c0043c2c0c8400f03403000d142c202405400e40c0710b103420805106031104044400c0d00f03060580a0054009d0b401040d6a1401180f949007204040c0c02c00d0f441149072000c2040140e03400f0b0b04848140e510036490036035a40301c0840c041c0d80402a47c00c0800d4601002c000816144942c0e13020b00707000041c1c410784034094003640901a1404c050302c00c81200070799114002441c04240d5500c40f43d00030b6001d150401040341c1c1c404030400c5a800c51440b081d20f203500040c030502c0d10b203884044950080c151240000c0c096281614506001071030203c0349007030213084200000801414000e0400410018009542d11121031506200074001201c1c20f802080300c031701d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 167417437 1250 167416187 167416189
    0x90507080612060109111b011d15040201050703031812180f060e06040e0103150501050f031518030d0c0314011203050319090b07032301050915220605 66
    0x2040700814124000030701596420005d00718043c000440c00c50142050401c0805030340f5882e1042c900d010034020000051410b03c407481c4000c881900d030005a90f5a0200b042944034080c4504019003099090a001d5503030140303450140c015150048440c01400d0101c0d1920042c001c1c4508001e0120035207a4401400e150f02445240710700e040c60185149030008800240324160064201300c1086800038a010b041c40d40d91000c01c40b41c600c0c01d0f001190342281003658a002841c8134098640035200454141403500c90305030120f5034800c2200c0b454241203501801040c1542400d142c8411005d0003101641e907500d2120950002400e00a003070b10340000e03d80035110341a40f8050207014165032410400c24012080fa40b0201d4240e00003800c0d006d041d0b142c0100e07555010b0304500c241d0348aa88a02090310301d6290a1b04080c04640e0404180000780d400c201204800c07040304460300c0d06690044a2003883c94844400252800c00c4007108190082103202c0c03024499000038114110074140600184203040e180c038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 167418687 1250 167417437 167417449
    0x708060c1e070501091709011d100e19030b090c010c0c120606051c12080c0405120c060a021005070207030b04110312040b0a0305060405060607020105071b0905070806 73
    0x3201c007051121402501500031074080d008040141c06034001041c810b540d500c1b50f100e28428402400e481001c0081e83e10313200d5070820a641e844d500b451503082003e014a44c0401c9044000b4217000040040e5041d03071260701e682d44020541001c001098951a503500c5e440c2c0785240030010f43d8030b460319110740010024103601c250b4030700a02c2c0340e00101ca1019245030011015103221540021a081754039110045015140d00744000310100b069600300c2d51480083c20440c8110b0140b0702ca072410480203104020302000000d088400300ea50035907c001140100414290400641c2c056995111000080c169031150b0b0020301c001d20042d080800708201d854010302603079540c07600d00c8001c09119849000901103a02e4031500c50b8120070242c1510700c107a481c02c00b41c1c0c0700d540c0a40c00210901c14041a18400d0540c148115580403600f500c0820a5043c5100018580d0003841402030401100081410401002007440d45102050081c207500d0f454480c1d0250000e000701311407a0740025280310000d0b51a18000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 167419937 1250 167418687 167418697
    0xb040302010c17070605070e01110d05090d020604030f03110706030c0c020402030601021606050a020f030c0a060e0718020a1e0f032705010501061e0206060f0d05030c0708060c 77
    0x50b10350000e80540e56a41180f104100c2441c6440a0f0081c040d00740450014019a841001d0a9503035200d0304140000150101a141c03403000c0300341c2d00c0907644134601a081000c841500c60121250011880b0314030000b00e440c03080c0d030401011b900c12400601d0816810481400001c1d035218107960000e625031008a080b6044a800100001e0b11080c201c405418181d000b550040010f10650720713981d01c19409800c03000b02030f605c4a80064400140ba039192039060200841310b5417000091840d00c0030030280f40d41d440464040240002e41c2d1101c1210001c0d90400c03001c8002c00300340800c40c0200b000015140c0003900500300744404111014000d086d918024083d40c6080c0c0416101d20000c000c8048007100180106040c0c01c07100c1102e164941d0410a016a02c4c0300d130f40d4402c60003c1030b03560618a0003028081400e42d10603581d841001401c201c16004650030b0351148060f1919a560390a48000072130a8001c4c107405407190000080c010203000000c5422016103044004031a1281c685200911441c80380c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 167421187 1250 167419937 167419939
    0x10c092304021303060e16060c0503030105131e0905060601141801052a0c0306060604060809010207020604030303050a050105060c0c040b030109120807090b040b0a0503070215130209010b040302 85
    0x1808000308501d89540646820200003508440407904ca5848000311950761041000d2580700080c509140354520030200064452403900c25480c0c03030b80c0d54410759240018001d00c0e02c65042d041101031010300980c41700307010f4012010090075000c5500c00403401809210425192401100001a5a0750092910b84071000701018407a103010f94607030a20720801c440d03052160412004010000d1018240c1c0301d261141604c41d1042e000b00003d281751645450312101f2038034040d401003400c0002643d03529096a00711951070030011040e0782c1e81078040703009202c5c1c2c1000940c06032010802000349a071550106200726500c1c002044183d80758010420039000c0c0c030f41c0c42c2182d90b0042d05404883d0400c0d822482c6006000341c00800c8178007880e640c0f0010b0694401c0c40c28000780100d820096904d610215076002030480310b80d402e140c41e0030894042030313600c5400a44410b0000000101d6003844c4204010700780c009008043c000a030030100d8240000c10100c92003a441076130300314008a024070f0700c0e404644c00c990b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 167422437 1250 167421187 167421239
    0xc150807030209041b050d150312050c010b10030501170601080d050c0109021507030f080910110c0601030803061201150509180607081909171605010e010c09 69
    0x303640034003180a5805a0b034030940160700e462542d64200d04149000520912907100d440e103d94142c4010030448208560920314415482c1082004c182d2981d150034040c17003145052a55030300ca6103041c1d80541486400940c02c10a80c0500203641541507024606035040c0c005c0c0586426000202541c3e607900c280100030f000d030001d10703180d03891501810090500d00603580010036900401d4001605000c2d80c1e840134072001a001030164101070344951900a0441035040c002243e003004010b155484100100b02c4507850f944040e1549904400000d883e1064144030459072550707124500900035400075200503004140620b81100202410302401c0c2605501084103180c85240c90100000d6034000b5242c186600b00314910a0080c40f400d10085114034203030749464680d4244815002850385110725642a0f451070004a80e001414035540c4001c906c030800a9a9103a07c8115130011f1075140040d40144950310f00301141096940640180d400d0007140d880d000c201c2a52519180750000f150f41880c50146 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 167423687 1250 167422437 167422441
    0x40b070f0c05030615061c0e0304090501050108011d0c0c010203040c030b01120206070809120304090501081006030807060b0111010e010b03060901111606320c0f040e0910050f01030c1508 82
    0x200b41b080c003a08440c80d648102000c080c1c00701c0c0a00c2d0840303490354244081904002018801100b1a000761030041100f8640100316616281c40b64030403081d8000d042064019210105003030004500642c3c07110301d03500000715664100b80c500981034500e81e120454100c4849000051a040a444192195034014040780e207054881d43d40c00109500010300107a10422805607118400d008001410190400140000d000c0d4140307050903240565150f11641c445080540a0000442d29070507100c1060f800340001c42c1210707402005032003410a001200c030080d0319040c1900054070b0150031103840c10805030b0503a20a41c03101c00c1030609a80e2805400d0398881c00400c45299620000504241c0c0140694000036100f088a1001e0408a120040c1e03130700014400418075004060044006401510b230752501c0c2d280800034460150607000700d2046907008000400018000d44080c4a020710402c8500c6003080385113480311228171900401e000070307118401d075400c01003070700c4201002105c035000c240c6e142e0300070316 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 167424937 1250 167423687 167423689
    0x170f040c09180f060608060c0403060506040920180a1e0905030301150203040e192f09010c05010908041503050601021504022e0f0507020a0302090c040b070f0c05030615 74
    0x4805411520300780d41700b1002130620ba080c80464041d004140b03409566619600b080000d441c0003600c850321840c5451680d00001b0100c41c011000f00c1c070b500c60800981d40209002800501d8030313900c41550340c00e0a204021407005a070340056103072400d50078655011640d481e0410100c40038070400400c1a8010401403046202c080d100044450f010b10440f40303003544500072403440c880c2c255516030f000c4041c90b801f01d0035003415000351a01792511451103004c8561140f05481d0540040741d00c05496a40060405036070b9118800252085800c80d0092119190518041045501c54443c0041803031007201d098010318403c0c0a8a405108141d00900022500c6c007408a500703c00600100d03807002e095030088182d018800c0d0481003c40942c0401d050104c84201c01030108020321742c01c0c2041220400521006a83d00b1120205883d01070f2211251940c4008614101d4131860b0080780b20794501141d0b200401c134401255528140c41034604070b03145552034050503940e090171f079500403210200903004041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 167426187 1250 167424937 167424953
    0xc01030f061a1303120c03090608070f0e0303041a0705010501170303010e06060c010e0d080a0c170403090308070b06011803020d0f0c09060e060406060e03030a030903170f040c0918 79
    0x68008000b901c009901d5585c0c0e54401c4501d20300d8140d201003501c041c11102816000b1114034014519818410168980000014500d000058446083c801000c2d0a4007240c0c90800688010304030841d513551a0003018140403905800c82e40d4122081d600302000807035407005101c000f4003c0001040118103617400d254444107229001042c040d0031030018825030103000000d0140010406080740902803006003040010001c40e00105200002802c01c1560700300e9950040c900080e01e50400c502400c1030703c039807404427589080e983c400340201c1c40c0440c001091000342d09000c1e015140076201c200304e04055000c441c004100b60700c03002e035100502c1c0c2d030305001140c00034181c21402440707100d020301d00540790f000007401c4400d1174010a03844448042002028100340c40750001400c2d840c1055040b04101c000000d560b0b2180006510402d0f448200200070503000d80300d414120080d0003ca04054070b0000761091a08400711000d8501b07082904000502100310720908ec100107181d5015100c4101c0c0d40c540500d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 167427437 1250 167426187 167426197
    0xc130c020c0a0b030a0b01111902030304051513080d0807030f0e07060c03020c0306060d381f0305030307031802040f0b240405090c16050c01030f061a 66
    0x1540103000d12603506542e8400150041c0070040507403030322401e007002d0204c101c500503442e4905100b450300503418407150000d0318425110b0404024840400c0d00e02c0821308501683d40700c0f94025041c1c107400c0610351207841c06043c510800741840401d0542d10200d00382d444481d68500d0010400f50030125008520a4015240708420180080f829400c03002c00c1d10303c0c0c0300166000030001140600010704140d410320280720481d030f0071401031240c2d0034550300140100c3c03c40a0f000304007140041c02c0c0001c0110002d0181e400c284842450b000c5040340c2183c003c1480783c1100d030320a441482c800400c0031542418203070410303241c105000b0350450703850000a4005001c0308941810034041c440410b001a030300ca00505503100008803010a9103c00201803003150300303c1003081c60320003c25429403d4101e00710700660307048600480d110952520b07040c00c5801207105000c0484031010991001070248280065035424a190a980030803030b8803501c8020780d080ba00e1038019a40c00510a02c0c0411111481c640500b03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 167428687 1250 167427437 167427461
    0x50403020a0605161b080111071106031305030c01140f0f0106030c0201060b030a02040f23040506040906090c0302010f0516080a17040f0b0f010b12040c1203031d0c13 73
    0x30100c0702a143c01c6992143c01c5c44030020000d00036410300001d402805000391a28500803990706011180ea20034910447d400039142c092540840090610390603220490701d100d0708101600c0e511071202040c1c134040c2c10041d400e0600c00c0480c5004c2105811001c10300e600c100511300380503040381d00f008021406040c120b4000000c540d00c0da0302c041980f00340b510065005000710400140d8031480d00401d903084020582c8044003000c2040108c00010850310300303d070004c0c40c0480380003903190f84450004006010710000901700502d04515203003045100b00c2d2172000e1303038000d89408000d0351120504a406102d16070003482c8071302900345040c00184020001c3e01061006081c41e031100d2a02c0e44280100350070483d0296282406d80911000384000c14001075007100c50280180702941c10700151a0442c45880d6003030710580ea504000405100d480395941010700b0f0403640340800b100305803e00030003500c40302001300c0100700f4200c491510050005030780980c1075009400c1450310b400c0801c2d55001041c90020320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 167429937 1250 167428687 167428717
    0x70e090c040f06030e0f070308120703090803093405120a080c060103170702150714030f091c11060309010612240501031713120803090d050403020a0605 67
    0x2c1441d801e00b100000103001030b513800041c48800c1d8813030302e072400c00c3c0500c6006103500440001d1000c0b4040804440290345000d50a11040e125203400f24028072000c0700161440b24044140000c1e100003003040d194400703181f00d800240001070b003111803020b035014554598290b1100020041400c144080300003601000e000d4035014001500d61010540c00040310301c401c0e8001c0c1d4018001c1003d24080e114806400040c40c90511700e081c0e01059600f03042a100c00d143e40c0c0d02080f4030040021001245040c900408140e07511034500719050302e01c64100312030f481e12400f070280380c2180a404440d40c0031000e41e04608006810488202807160b01c0d03002401e4034209540360400031030a034180d8000228018462b01c0241d0b190f0980b0703040303010408004855103003914140401000882c00f14901c0240000802900c60383e1003001c480300000c0305030700e503101c406400c800c00a25030a2025410103940304054180550703464123902d04086401d4402c5000095100950380400d0140c14402c2c009403010f12110000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 167431187 1250 167429937 167429939
    0x30f0c1e0d1b050a03180909030f0e061e0901030b060906161b060917030a0e060c0a020306041103010b06071502090d050f0a15020a12020901091a0703020c010503070e090c04 76
    0x1c3c65080c141001c1040c0c0210300002c04812420145490a100a1424003010020810103680c003d200d03c0c1281040010880111030260981d42c07040700311041c003c00c0e48240d01c10b001d200340c250411600040003540c00b0030301e010400c1201c2c1c02c00d84210782070a840141214500350030f9460500c00070800a5003a03400d0f07000781c959080c1c80ca1101d92600050815074446500075481c020710003080c075844820f1143c1030303041807155801c07464011002035aa104110b603440d80380d14171901d07401d181c0700c2d0300c41c0d0203581442898280014804030107540348501c1c6056009100f4448110300b804058810000003c0501e1940310003409445000d80c0039019440e002002503500d048540c0b20b080c82c0081c60090958540c000040794020440000381c04101d9984800301036040c80100c00002c0c24405814820802041d00081d01446680c03180803550301511909090719601000b041400c5020780049034111b02621800281c0d022644c0a0320560384101d4240d0396030f41c449803188007444080c0801401400a0390410701c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 167432437 1250 167431187 167431193
    0xb13020a06122a080c13180b0907020307060510230901090b030c040e15010f140901050603180a06021b1e0a080a11030f0c1e0d1b 57
    0x2948004003140d035151850410340c0c82c40c801c2141d60400d811910f00d952440324219000c01d8207150b80000700181402d40d215a61a507001200b40b2802c3d0f50360b900b0380d1030050049510720f507100d00042d01009200d010421154400180a0070210a45216015a0007440642c0000344280c205c241d1104110600b95a01c41d900c60080d0381d0140c3c001e14900020b4590b82c2d1454050034180c00141c01070503043c5044c080c6810010200392103035021140c650060f9100c599003417406108010040007103a03600c032801220340c1e41d112003113a010454000c0d0710130b10050183c0c080861400d5401c5d2390507900001c1015107141c8a488001030f04188003501000d05004030340403030000c00d070346202800d00400740c0d010078420112055002d50170540e090200319800450104845010980000c541d010180d03ca0101559007011810a9980030349a1405204d58400080c80903a018800d20140c51092061000c603001c095886d80c030a082d841440c00030b00500da201c4e4407260035061003a2400c5000c400d440102c4d68001940380c1b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167433687 1250 167432437 167432449
    0x130c0306020d0506031f0908041d0f010b0408100b0d060c0503180a050a06020702180a140705180603061504030602092803020120030a0f030b0303090105070b1302 71
    0x54000d4a0040e400b1500c070003072100d81d001e6254408411400f070041c0301c16409130040c02407284a002e140c002d0381c40c030006040149107811a0080c2240d8040c161a400800c24016401e800848281c441d480300000000780e20705902098400b580c40c554042c28820b0f1156800c14000c1910319003c07035100c04140d1103180810058414050024400d80d9500da4a00d04201101011600072800e21480e5004501e0f04020900100f003030240190f1048015a458081d4000500300e04c0038148900341d00c52100c0144403034511264020300760b1880c038510303042c0a50349400040d02d0b9801001418951144e07020201d48141c54541c0055900a400a00b41503800002000d8035096030880c1c0c004640c4a9400500e00f0310030324007c071180e117010308004d0001490540303140240e04d150b8807921000b030500018182070b88062451030240c0841c86d11040840380c5070040c2280c01480c0d024030442c42c00102c0d1811107400781504001c01200d021140686550745071182ca56030b8108003031402440840c0c0d80c0c42e01c800060050ba00c0d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 167434937 1250 167433687 167433689
    0xa02061e0c07030201020706020c01050403080d0b060c0a030f080f0406050c04120f05010e0106030c090504050309040515120c150306040b030106060c11190308091306060c030207080f060f130c 84
    0x100040ca402c0342580b00191809650390414000c0d0360010440b40056a8042c084400307507940540016240d06213401003001030443d14a0a65100740040b034800f0707402c1e0000505208150181d6100c00045c510349109a403845429903800201e00c4540d40050081115131700416086500c03585002d02e01640c400c614100b10884c04011548a01c40e10106802c0c05002d0260404405440d030003040380e80c1c40d565071880e8002480c0b2034a940e150302c1c0c8000a0038001c0034000c0c0c500412020b0070a102c5450f04040491022103611201ca10a00c082000e84d030310f5110000b0140500640a8407481c1800710394040c100300d40c1c100500c0341e6031154958103102011348003801003400800e83c64032500d005400780d24116040503007210f2001d0180791040191403402040b08100c00440303401c408581d554540c181d000c1001d0480701c051801034182810800600182e01001280c0194081d5094649258840385003e440d00d54040071b41c00950f0103d004104c0f0344c010104050b03045048410108100040c950303c602d40600300d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 167436187 1250 167434937 167434957
    0x10f120e030d0f020310150915120f06052101060305030a020a120806030c09060118080601170303100501031104090f0c0f110607031d010f020406020c0901080a02061e 73
    0x116840c00c1c107030b03a58012501c18800301401541185480c103e441c903460312502c2010110705c48510900c402c04e01070384070300c005000303400030031b04030011483d0002c1c0c0324100002c125040540342c0082030780e2411035440740b44265a0001c3c1b04928000ea81101003d10110b01c04a01001b55a28640040001c4082005000590303080c2c019103a01c10003400e0540102a00c0a46501030000d0501040260f9a001c00c81038010801152a041151074180041f00d1500200ba0901c4418001c2507022a100740e000400c1b9040350b25000054246a0318141c00030340380c0c00140c5d007482c2c3c0c0960340c040c00c0c009507000b5007080072000c070610341d00c1d400c09560386044416a01100d14104c1c2443e40d07101c44100c00755000340b500c0176001203030030700d01991b40024030b0040d40d440d00200090105907840304204844030000c4041701d54404d4070030080c01a038030300e000310700002d500074070800000d40b041c52a060740d035080c49142c0a0407241f140000d03010030041a000d20090b84c1c01400d03400d11100c1c1306141c40c0f040c0400c481c060501141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 167437437 1250 167436187 167436193
    0x7080a11040c08010b03070f0504210209070c03050702061602090408070501110c2e020703030e06060405060604061b02060a020615091005120109020d08030f2202010f120e 75
    0x380001030004564080c42c4003020810b542c1d006110b101503920032250003800030f00e81016502e280f04011038081c082c079009240c00380540b4040c895225160b00304c020103a03000305d42c600c1144d1100350044ea03003400d5200c4000c01042003070109001525110b4060b100310795406c8584e20bd134402590000702901130482d01142c003c80041261818400244140c4100200c0b01c00014a40042c618030f0715602c109504501d422101c1c8416103501800d20342c070f00c07126010740e43e4101b59280c20323040ca00030300944100000624203118040014401e441d0500a081c003079800a086240307400d05001e821100c28080c00310034031450210031209001a1a08401441c00032903075800b03071046082c82c2c4000c1c600d5904051100d0311800300702c3e00f07104841072059050011503000311841640307216001c00b2a4050000340c8006944101071305081c3c03040c004640025440f607030040071031440316a1506540f81d14081b100c0c0c009009208900d070404019405031444244200840c240556001e000020120039100b002c904080076030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 167438687 1250 167437437 167437463
    0x1502030c030f010e0f130f140a03120b0604060c0c03020901090c03050703140109090302150a0b0109060201060602070504020921030414090906131a09060615031302060c07080a 77
    0xd10b900c50514050101c001c103148060034810b5030f0900c2894040c02c403403614a420340480e401c0192104080e8000d690090242c002420034a28698440720f40035000d4020500d140e2420408410510440e480044000d01c0760742028200a170442c0e90030000c140031120b0301031008001c4056038406117181d00a05a0000100f10242a00401005d80f44013034510001e00d4144090540100c000c484041e040d10b1000c0c0001401c4003560400700d1402c0f2544000d8079006440f00107200814009401050781e00b60207803502e1076200e6450030120300b250402d108400c0107030065a401d000c2460300781c0041040000090001220312606509040c0400500d141c440d4141e000041c200a40314030316900142c0560210b03410112032a0414520b17440340c000070001002c6c0020f00301030808100d08034224140d0b060514020555524003e00401e41e02c40c02510140d1040d240c1c010290400c140d10f00440340f00d04005200350181c00780c25424001103400000380302800b0f0140103804105840100805030001d80034105210000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 167439937 1250 167438687 167438701
    0x3021e011506050a0c080913110703140a020a06020d0617010b0a0902041404050405030c1c020c040e1506030708010e100e0c010f05090118120302010c1e0c1502030c03 73
    0x155042e8000410701c441884514102900b04030b5442c02d60340c03c944d90b0360740e44541c031002544901030110b0b000340d486e2a0030200c03914400140d0240c00c00901caa1110b084c1038082041c42d60300c50040160410040c1d020b1501100083d4154000c5c0c400319405000114030642c44948608050504610b0f620450390760b49131000c0c01e4900107030510000c0c43c66039401c52402e401d014100b40201d10346c41406000e55200e0b0041000c1100400c11940c5152490301a2040040005000b481c04294001c031000144100c040c1c42da203c3ca424410b40120b40b80e88002403414246000424034212802040c045d803500035601d0010300080e0038022910300c40c0c6444049c3c400e00654840200486507808151007045d481040e1161b9035903041142102048000d0400d542c5a00b051700040b00c01d240c020700c21a14440c244030b000039a0036010001c000380144290020700c19644007030750485299010102d01a080040b00d201c0036041400369107560700d00d9006244224041c5031402c0500241d130b0081d140d0f50807400c0000700b00120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 167441187 1250 167439937 167439971
    0x121020315091608040c050a0b04080607050f030f041b09020c0115031109150d03090311120c060a0306150527060306010806031905031c0b03030a050703021e01 70
    0x180744000c50307103003100d03003072807108140603e070061001d00074024200081070600803403a00007001000010041c1010a8590303004105641262123164030510821000c034801d14010700541e06da032280e00300000d045940700e807101468440003500641d400a1a0f49090886070182c00e00000900110440542d0b6034440d0981e01d0308640c008012110f46c0c3d280c0920a1000941c8034642180b5440120ba40d8000c0380c8440708210408400400c00c01e0303205502c00120801c02d0340003011070342280d00441a1503080340c080808c1c070102c00d0103050030102d550001492040c40707152110150002c0021454001015900e030110240d0400c0c11404c0307074000c035030f000c220600c88141440e00d00d5004102940d0000c19800c0042c081160780c00050103032418071100400144050b241007080c20b094109942120030b41000904000d40c50b9803204c4040010710300566043d1f040c1528501600894130b41c090001e514104903013a00b05c0701500041d104a0450041500001400320359124802c510803115000144007a041202105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 167442437 1250 167441187 167441221
    0x5010e0715090b190207170604030e0f240903060421020d12020904020702060706201c09020303070210050405090106030605011209050f07030b0103020a06050c0d030b01210203 77
    0x8004100c5020b004520807a0141c0c0e100034101013813110762180d025401d0782440c28680000704001020841144420341c005034403401a8041d460707040c00c2c52040418000c210880c04459500b1a0441f408028203142c41101c0320a1280590380e8141011084c0000034240141610180c4104aa00d1030030400800400c00c40900740c9803600050140b4448000080c0c642d06046441c3c1ca60f8541c0410a480d0946a43e0120795449074001d09450395940603240080050142c04070602c9035441d40c5140014043d5038008a40d0520409030303d80040da006407141c0c10180c20301d400103d805000600840c40184c0f07034040700e100244401c2e103030161541d04100500122980507030000c801c241c1804010001030360815455440c100000401140c00c025030b040891900c00c0c034025120a9201d149000000c1c0590183c3c0c00d81a24821600610150303554101200d66000d0074211421035000441122012402a80011555001810288409140c485600b401e203104000d544051603000420800b07150032040f010a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 167443687 1250 167442437 167442479
    0xf0c0c0108091b01020c040204030317160903150e0601030b0f060a1a03130803070f031802060a1101060b030f06040b0904050c060f0c0307060605010908010605012a05010e07 76
    0x503400780780200110f55240156200c02c18040789000802c051a4030a00c030341d050283c0c018005658456692400800c0052002842e48010504001255004034031210010101469940300d0b045141191600c1e140a2041210400072958800013094840d074203115460095000305c54920007840d141d001c1c0303461807000034a070511441c0702180c140540741c0413017504040b140748400700c0c50322950750b0641c2c259201302407400a010414080b0801100503413001c0c14102400903540e081c080700840e025004521170740500000e43c0124107100c080c50f500d220b9512010034000400011511076640c6203c02d00990080e08c000c150000030004101d240e05040c0a411004001690030040900c0c050321101e8841101048142c072500c03000880d903c0003840c150582d8001c10154055a6880016140100003444140319542c0441d8440000084051307042c42040222901078540421613546005401001054000154114021030340b5401c00300b0f100b449a51000d52003807000345586810041d4070413088201c04036003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 167444937 1250 167443687 167443697
    0x90602030709170a031b0204091b05032b020a0f0b060f0d0c050405070215010b21010e130206221e0501020307020f030f0d050a120506030d08070210020f0c0c01 70
    0x544000200081c6511314507050701c2d0107585401100c4520000c2484070001075403107801d18040c0e40038040c6c5c10000c00d01e40c00c441d0144141003541c580500d5103a25000030304882a40420b8141000c140b0030381c8403a16021190310644000442c40d594090701d48440560a640c540c6810040000c0d034202507e6048100e40100c40405402006a0b5180703108581350152502030343e2240003040d040c0c0c3c001c2003150400038103841440e50946c0c48403e051944d401558078040003001416165140c1495070760f030241a1125241d01103442da9820072031509400300c500080b6001001003201d18055480490316610703032a440300c074154203180381c060126410b000200d0600c1802c2502c000401c0180e07000000c85654a9041d91a01076003c000070010781801480e00d01c902d030074000c1c4404607000a600100070414841c13192510b1108046d0700344040120f0f00221112a01503001040f005070039030041c0e520790303840f00311841124650901400c0d0901aa000a61103039110a00071611406002040c011a24a440c080c44d207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 167446043 1106 167444937 167444969
    0x9030706020a051005010e070e06040b03090f0705040b0a030f050c0303030103050d0f030c1205090708030a02010e1528110a20060912090112090602030709 68
    0x443d01402600d01082038040d55124245c10b96502002200007a42e0b4048103072104d80c10800d58030b50060082c04000340118501c030003148140610005090b4000010110a15008498100c00d1140d070501c030a2034200e0310f40342c64150849800015084a0f225241803480c02c1880d01c1501390b415000c00400070061120025130b400c1a1510360740c54074000d01c80c40000300c046800306140e840011b0034040b01d040115405030062600f00241c002503460880d0340e00c03c01031841e0702c840e11000250751252185c205031901406400c143d580c0307964045c100d500d010205450b40c000911800b1b420110b0100d90150031428a41c005426504001c091075920752010700081c0142c01c0350400c602010211071024011141d0109115008030310b104001c1c0200f40c00d40c002e4001c01d400045c1d103203041105a00188180328042d014221500307001c2c01c001640c034241007800500380c0000e60000c000c01d0450900c = true := by decide +kernel

theorem cover : BRFrame.Cov 167266187 167446043 := by
  have h0 := BRFrame.cov_init 167266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 167266187 ≤ n) (h2 : n < 167446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
