-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3841
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:50:07.590215+00:00
-- url     : https://prove2.me/submissions/aa3c398d-7375-4503-95c5-55d5af6f9004

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 690647482 ≤ n < 690827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 690648732 1250 690647482 690647497
    0x2703071e050312030916080c011206080d05040f0f050604144002120a1808030c04060e120d1b02041404060b1c110a170d09060e01050f 59
    0x110311104546030300c0880c0c10b01d90420010a00700802005006002d0414013599416200101e100c2000515022000740e5621003200304905111282c5480405003040350041ea001e8000102190203254500d50000d00300c1d406031081714140303610204007003507821910a041c0d00311030009190a08180c00c0814881c000011141c501e84d001c050f01d00ca00e01129842101e268501074001100c0c2c0e40e41c0159890340031420502900c046009104102c40342c0e046540100403034100c0000c0070000f60302031803001c000310394000c1480d024120300c80c040200100410080020800e4801540c0c0d010000a98082401944074100c034442446070040080702c0d00b414030440c001981286002031382d0349481401c1d004030381101c003114050342c070b400e01c95001c00c4180210ba0141000364002035440c25404c07155409118101040c207640240340c00c030120200010f81d81e030051344ea00a056120428400607000e0a103082d52078008141c4c03400400c4105000017105405045034031013002c01a1155880c0c41c0c5405c04245441c0e00031034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 690649982 1250 690648732 690648779
    0x31c09053309031b01031a0d0b07020102070209240a0b0703080c090411041d0c3001091a030f0c0f030102070c060503040b010503031602041d0111270307 67
    0x1c1800180e4080013055801c03040c200826034180b0007000010282c6048410581802900c44450b103480e131200300285030f4084c1c020b4009041911002c0c000c0303000e4030414030084c2d070000503103003448100001c40301c81c008a19040c00070148042038110a109181a582c0308a5100c81d2082c044007003c80d01403103d440d4010225030b0340320321301003058000408407031000005003054070000c2410f1010050398065003480f55030061281703080345000c01c200016480380001300860050801582d171250140f003800c404011912100240a940c0c4030724002d0001c08001e00b03200c80e40081c1c0fa028510300d04010030aa25070001103000340c2103244e000c10a11032441c0341c42000e00d406650800c0345e03801240c211601140a021690743c2c070381d83c82c03c00b4204100d0b4a40d060300994803903081005207004080303804051303014455064a022490340784414403c2c07844400300b205c1034030300e5080c8525804c0c0c03d00010020305131040582a00d062001c0c4d01d13003c00700ea0f50341400304290554000c40c0244440b000300310603400c903807a840d0f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 690651232 1250 690649982 690649987
    0xa05090a1e03030f270f0b010b030403030b0f090a0c0905061216020f06060108060f10120c082a1b070f0611070302060d02040302031c090533 62
    0x1981c0c1c005884819000d1001c0040103040c00c0420150700d801400890300107102e080c498030070540c0341009140e800800f0002903000380d012500400462941d41d50703c1c260061403010301c40d80c0d142448081075004840480019203403400000c03a038a01011f0807855480050007804079541e031510003600070b2400e40d10070010300005c002c000416641c6d00c0010181700d400c00e0310b0390200d805c200040401c0c1e035803c994100c0c1550401031032481c2e654400202c1540c04a07007403800c03022a071100e070007150310f4801000101e03030000d1042e094207813450f030480c00914018031960410801400f900301d0132200b40307409681c0d003034032030001100d01c9042d503142e6880300c0203603008884082c3c40d05050a0b500c05d4445605c6100c51401c2e081032008200c42c0ca064501138000300841e060540514100300405525130742c0a0000a11940c00462101503a1810798140ca01440e0702508449808240c003501903e140d0302e15410400180903842301107184e05054800360302000303100502d0007030440b040d0202881360950505041c4904c605 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 690652482 1250 690651232 690651253
    0x504030609050304030519240209030f071412060604090201031e0b55030302161a46090602010506061606020915030118060605030a0509 60
    0x35208040140b072050005568952441c98000c0c104150012120200d03070089001d5404a0000b031032031108080d0b00c40c2035003d01e20800c00f45000900031040015050322031500c2100fa1440005038040c02d9518800004202c251898100203280f8002403000b2441c0e0010f0000c14110704194000c441550302c141404185410980d1089611a40c0c825a800d5500d455140750105400c0203c1c19510303901100011a401e0205080c2c009128090302d4031030030409980d10514a6483c1854105200c000307003420400c84d1140d542d0070025560104a0300344010382110440024104414041d03018896001040c1e103400c10b0000300f180400c110307445841101580310900120002950155071800c0604129000c00d940144400d004120060b180c0042040d60302d00410321130140d9a01c1d05884002c02d00c0c8402d030440d5000c6180c448d000e401030b10000d030303086600526131382d9000400700e001d94103903821244030501c1c0d10315511040f82503c0d290b00c64200820410408100d0314480380c0c100700d90113004241150303555800f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 690653732 1250 690652482 690652493
    0xf0112051905040f0c120f02010f090e09011505030f07030215070803040f030e240912030a080115020a080306041a0a080f0c04142809050d08070302070b010b030601050403 75
    0x45070200d070744440c1c103c3d004c03003003041540c19030015088980c44144d0501c0c25030780301c02001c2650080a4141300150145402c0e0070b10070f6070754034046c3c9081400041c00c0e0621241e40d1703028202c01d140d034034201c02c450013011a16050024440e8001d0468500030300e4198030796001c2c006101e03c003004007508030900f00500000700ba0410000d42c02280300f2031240010a120713040041c00c0a050701c0c2580d120300c80090f01c1107010f11311103001100c0c08909001003503503002440009115104581d003c40c031075000c046810109030790001c403510704035112130441c890141d0280104a03144e0700740c02c5008000c6070b424408100c017424030ba4005c0a580301c0314498189000d4071200041d101000580c46004180d0108030091030710f038014869006454416201801076001d40641d4111190001b0420031240f518500030101c0a5800842d4408410817980d0802c40c036440c031b0428135159410504488041002d84001c039612511071300c00c0320405508032104400c1e907420b000410440e60b1016104504100b4248004000f049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 690654982 1250 690653732 690653741
    0x2030403140a030305010603050613180c0e04020f06071502070c0302040510060905030111090f01051e090a060914131e0603060e370816060b0f01120519 67
    0x1a1010051255114034030f0028241e40050b000b0b041010b080209002d5940c54100508030030302143c20340440c020840e0030312480420b2241e60041c000501780340001880e002c0714009a400796000342d406101d410050ba06100080c40f8400e4002c00414003a0301c04240746425601034030400d0310a00c1150441a6281c00050507603805403811851a01c1d002d00800c0b8090300142a200202400c0e4000e1004a98424540c1d0260154100c014018404802c40243c0c5a100c0c204440000e801c0301c00480300c0c21241c0c8006181c582144040b14000c010341600412043d004440000861340d01c040c2104002460509004a40d091618400c04260f140c81392640c130524803079000074050b00f01c06c000244035490b6050000654020407200c880a4005d01c2c0e86844030182c2c01c1c200ca0001c1c00003000000703c81003210301c4000080e248003000d0040c82000c41d88034200c4091064150410b4000c01041c4012400f8008110350440c045000034082041c1c0303c2c51240001640d00610750104824031040300c1c0c0c0d0440002c031402e44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 690656232 1250 690654982 690655013
    0xa05040e030c010c0207080c0f040204030b010609062d05070f0b0702030d0b0d0c0605070c0b0a050c1507050901120605131e05010302180a18060b120a02150a02030403 73
    0x907000811070070301c2e41c0801d10a11814030900d2009003140d628194002341c9503284400c0541c0908001e10019a8603251901198021684003a2032296580d480034010825a071034054400001d2080841c07048940c030481c1d078140b04619400481d02d00b6011000140d0f03882e80002003c0b1964044a44d48001141e5204440751081c00d070740d005035035500c41e4440518100ca025000c0a0b20805441c00c1e071802081c04411402c050f1240707030a02035076408990070007a0008205034028000802c0005d00724000c95803020140058a02c200300715000d032001c0c804078819440c41103d0000010b5000d01005400750b1140da04075254121003140002d10035229001b2031040034503450041d0301c036919a00728500c40d000c42400309105100c1494100a254190750000b0240400b4070b89940f0424030083c0401c5018049601c030701c018404126408840c1d68113880e22030043c0459542c41d80c4100621500c0b8a1042004607002d5101d642c000c0440030414013400015102e9048801d490342140f00c1030002000007903032148441e916 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 690657482 1250 690656232 690656261
    0xa0e0d03060f060507050c0603130c180b0409031d040e01230c18012006040b061f080406020a020708030c031201060f0203090d2a08060708190b0a0504 66
    0x5042c2400c118821034526580071904124080200038089400400e070458204412500d10780d403602c83c0081c017000007a0079000505000065100011219510403507500d2511900c0c0c0700707115600303250b800c02c01102c100c440040d0208015282824004c20a2940756003a054014000108085070000704c40c215001c1c0c064220f5400403000810044c095140010369204a90310011840c200100a101100c0410400d42d1810f2050300380da5030f442c140c0304007682c0310404200e07021100c0718542401e000e40904000d0b502c02d80034a032110301da03411403800c18080da80500d0054036100115201c40d51544001d501c07000c2c074002140241d14003c50422018801451040001c50041d522042d03001042c600083c41a4011014000c69282c2d04c4034060b00801500e070307082e00868003002862100d050881f9510040403090901550300501d0107001d4000c6d41012081d075180f4030445856669164041c1c800301da042e2424010040508080258141250455031122101900c03001940d661000402d0640f914540800103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 690658732 1250 690657482 690657491
    0x6021303080405030c040608070b0c0703082b020415080618010e0f01080604020d12030e06132f1002010f050a0e06060306010509160912050c0907080c120a0e0d03 71
    0x44c5001c00000c0503802044908104d1710b46450106991080c4511549079111808034442401c040c0611054000710b803c010f401c0e548402440380c0810f40e1181941203d010440d072704049509802c103100f0794007510b203c01040d506e0109926402d413441040202a180d1001401055410355541e8540721802270034031340100c0110307003080302c171a95440700140c00a10540c0e1020007084056034030780c2a03070458260030400c003c3d0309000341c040c118050140c0c1c0c48001d2440c850740050166144e00c419400005074040c000d0b151001110040c0700c0d80411100c2241d0f03042440e030b40200c0010303141c10a407007800e422030f900000803043c10440f406c0d010748604071101c40c4c800741d070b844810600c401c003407111580c032040480150109604090000d034040c4c4000e000c4500400242c407001280c140504a0800030f0300510f106a90010302519080795103086100e40c50b4003030940380c00030031002406500e2980c041d2000c10411400e0050b00000301c2d284210040c030001d91181c442c00400711503001030140915600050b0f80c04503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 690659982 1250 690658732 690658739
    0x80a090c0807060e1806011211090405070e012006160203130902031501081e0a1512121103090d0201120e161d13020d050f0c03011803120504060213030804 68
    0x84242151039100c1131710361241041507682c0d20007088100d1041c50b4000258142d01030300c150f80075005c1c030041540c015149c0014060f80c0ca07040f800064940070240c2e240064004107034103540d0200b01159a0002a0344900c010800302e080b00140c4440c400c1d502e20441e800c0081c6030004818511090b840341c00303120703400014000e90b50854030005126120a0070501541e041140292500b44590019814000462004220b101c3c80b190004082d1001f84048544d03100d88402032a0840c50104130115003010000708146503d07406004e100070305400c003102850400054900740040000400b00c200d0401000c600c80b51204e1100740b2503407207030070401402442100f4285401001e041c03400d40020200f0100d00ca6030700c040e80c01c107002d182d902140e0b24514001010301c80c80414010502c2081c010158002c5a4100008080c0000c4031594902c00710020f000340d1a180c2025440c0b05501c100280002c0ca0b020003084500100744c0090f41c000c0c0c401c050040c504850740e9884e4220349015042159034120000c2d080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 690661232 1250 690659982 690659989
    0x2070c0308210129120a0e070b04090522050a0602030403020705090c0a090503011134030206160807080406020c161404050a0b0a051516060606120606080a090c0807060e 74
    0x7130040c070744200881d03491329071405202010303030030000e24a5018070f8a0704c2c103000141c0010301214000700380f080b103e40c0e29035884140ca2009020b0465040460400c1210031300c00310b1820040a043d02900507029008486141e110392000c1e510003030080d0207503c10304c0c3c4000303200d03181c21400c944186100c480c0680c40c0c420a6030000c2481c3c0c05680440d2182c2c2c1450071107400010b451f01259598510901441284c400c6c0250b111400d0342c001d00031080c1c0750840020314040c950085006c43c0f040c01c42ca41d051101010460042e00c40e08803d4548200148401000800090f41d90340146034041d84042180d403000c0e10301c80b0b0078000300c095401492042800c08680091800c00d8005d150b041143d010782403151000480214a030300c42d082c4a1144614009001c48954204450440d800c140200361407a85004a605140000c0d0002d44100c40019103500e1a20790f40038220f10072a02550080e0751040c00d162541c2034600090412032a01b80e0341103225040c002018101045030400400c101d0300c6000f8200814401c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 690662482 1250 690661232 690661289
    0x80d1401180524040b281505070b13060e060103030504090b0f130203060118080705010905030f0a14070b0c01150812040e19020a0801090e0102070c03082101 69
    0x14415450070194800146010b81c0100f610511410b840010701028100005042800e42d815500e401d809203000d040f454040405540082d50000e04002008100f828021034083c49940c00c0a0560b01c510000714030b16500d4004004a00c2c1d015003004141c0c02007124000e42813500070b90003240800c40020301044001e00c1ea010b03841d11460121160b01d9525041c201040310300756031030440004154008001416a0b0242c10440c1d4540300388407040303420030b0301c80c9031507aa10700d9a4050180800c5685d1000160b502d800100f44900c0c14444010b032200c111603599648030f003614401600c4250242c414081084242880940702060101c0d0000c0355400c0e080350038111840721504a00002e8205540c2c04100040507022102101d80c81103010700141e0350f0b1140780035028202a41c1c0c2407254000100c80440d05d60202c1020b0581d41a401d04000c880a4003800d43d00702e20414600030441804204c0800109201c800540701201186020141c810500b03001c251b0f00030f200b600400c003d40c80115400c1080240c0c000c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 690663732 1250 690662482 690662491
    0xa2304050112050604300903022d150409090602030f01150807050309120d05040b07090f09020306061204051507180e090715020c1f0804080d14011805 66
    0xa004142c81450321815200c0c04000c0001d40080b0080918030120b10b8007541c1c2a244088662038501042034007840142419014031050f8859580c891341071242800c480c503000c0310540410303030203004000d4460920004252124144c80120001c0c00005505140d81c01400c034801d2007003d0040e40ca1804209801c1d030310030180c0003403a90000c801141c0d4a5550800c1003036400407080c7c188180c4981c0c031902e14600c1d029954030100480c02011030700d0031209040d030304524000e031710921001c40300f0b41c0c540800300c80504442c458801c6d0fa10307003100100b00e0203030154010358010301c1c0641102e140a8030070082c0c01d000031040d0b0b411a041d40c042c80504144032000d40c20250803104a140a0320b41400d0302c64103840c9021a030052200b148070300c50103d20303a01400c2110000802115031801c4a18500381e030065103c8110000050082c03c40da801541100340b083c00105100032681c4032803900b9151911210210b03007103424020f5116070b42d00540070494228840290007444c600000f0034090102c85500d00c10390f1400b90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 690664982 1250 690663732 690663749
    0x11010e06101d06030c0108040609050a080d1a1e01030b0d050f1902010903030e120a0305090406080a08181c060b01030c0c0c03021c0602040906060e0a0605180a23040501 74
    0x2d0511149039408100480202000d10b003142c81c43e212414100020010b4450040c030300e101d526111020080b418000d04140541c01c001003000303901a6103c21401a162800c459000c0742d00030b80d503075500840c5060421741d000185400103603040310f0b4000c1484403c2c40e4605030358944c4640100041058100940c3c644071403c100314040c51a55940003800c010302c640001010700c58011010002501e402402002c200d008204032221450903060151140d0300c0103554a0007a030030010b01051062000036070419050380032490b14503001032f013032060402e104076858a55100c4c440c414032080e0403080d03a991143c02405804001060360052001504460001c18140c040c0003035070200d10f001c20728056004c01180c0e0160799507480c00d00e4101c0e555000564002000f010503101040202e401c41643d030140341540c0380f0340c4640c6078084440f42001110011881003000254041050240d60194889020520740000d82000c80141d2110710480d00360a2004c8422311007010007203403c00c2d61401e0702a160042038900d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 690666232 1250 690664982 690665039
    0xe040b011803321c0f08010b030411062809031a0c07051501090c080108304b0903010b0901080a0b15210a0203060906010602010e0d0e0111010e0610 65
    0x1740140a500c41407107514003089000c00002e00b4013010b1b038001e0f03500882c0108981e6840240000980021001400021810782c114990b841c0b000c0c001c0f0036100c2901e401c8a00c2170b9248d1000400d42e00403c1008141940401050084d100050010000e0136484c2010240d035170301940c14140c1d46004c1711125074600080042c2c1c003004210040000c500010201d65904c0d280500070501c1c1205421270b54180680e4036480700c006010800e0a0014200002088041084078888000343e40ca59541c02003c209450000160303601c002d010280000040c0480703600900040780c0401d00b17000113032003000c1c240d2007128682c2017205800100300000d40042e502c40b5040b111f2603819402a00810480d50f00001c100603091020011280c1011040015100003a8009c04441940c81c01c001601d468800c02e00c61400503608000c00508080c0000c6030324214000c2954a01041d14030b064011140703480382c4079280241c1d541c4c800c094540200c050003558407420205944000507131034410780444100c5988451005407801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 690667482 1250 690666232 690666257
    0xa0e37142d0c0a06050d0603020a080a0323031819060506010f02120d0216020a06031d010903170606070b01080705120105010302091302150403030e040b011803321c 72
    0x640301018103031013039441d2040d2507542001d8403d0003028070341c2003c0e51107040b03484001000c46001488142c60f034880c0c0c0e0f80314042c2000250841c0040703083c030082194680144000345400d00074041e081c95056484089034004036942c0c01c89100d001d211a419200f01e52100c0c1000702558000301c8500c1030510a00c0202041d1045108403189030260104802c9442d40008045183d504041c0144600f150010301d1910356541c1c03048058020000c000500494582a409880d040c1006125000002e0741544640c9001b1481e00050049c0c241c004081c83d5020300280300e4900030482806016019005000040070705500781400c0141000c40c0003025a5503038140001880180c88041c03207680c1086c5c4220385810200385a100181000d5441244954030b80d0740883c0004c14107602c05815809950141da08000f0310043d44011600c00841418080414a5510003000080c41c04c403421031040420a00701121020100f00c0c1c0c10706581c1e00d11109409511491100403042d4000c07855a5460347c0508040b40701030035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 690668732 1250 690667482 690667489
    0x12030219020312012715062304060e0127050306062e030b1e011205041a07091d0105090f13030c15050a0e37142d0c 51
    0x500805c00442240340e5803c420040790720b02d0b1520042c0000c1c003440999200000001c0c98511403080321b00144001c01310780600450310010000b014003141080c1d01e4a0705044040d600c4440e0600064100602491400011540c3c105a0b050b40d05416038010310140c41d0104040c03500402821a80c0306141d004150441078508140c01030440074144049102541c0c4244140c00818000900c01d401030001040000301c0201516040d0030b142090b21103051829055220b5002c5800c00c0300e00030841910420180001c207422446140d10042c6d42c904124419114603180c03075030040505440300e6002110b4014005884c1030b04515500c41c05185481d500c504e4a022035491003034070080007900f405071a2580009018141420301d0301000e04020030b005c0c1e42001488600100003a0a48403030501542190b441101c00c0054048402c6408468003070b01a14988100b28010b034500400704c6200d170f219841070000c20414071200c1c011080b90030240040c0115549909a00400780001c05016004076620380043c4c1e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 690669982 1250 690668732 690668767
    0x8130e090c06031e15060309330c07110639150703060f060903060b0f01020705010516050d080601020609120304170d051f050303040b03061c120302190203 68
    0x10014075100c180b1348030910b60300310500d411882181c001c10004100100880006240002a40003e03042c0c2607016041280d20000c00050700f03007805070a8810301041400c5d68100c00f403d461400f9480016215004200003905980101e40c03090030140c0b01550500c5d10003685016a008080038800440b900ec2d070240f07425100c0d001101c20107000700708000031524840c030030341c0004c01800200c08600b030021341b01c0d0006032082e81240300c102c0d039180c1490341d00505400c0c00719901103501c0e0180c0003000c81d5410807005543c160458076040c0350a0110312043e8010480c01c1107002850041c40e11000c1d5079003050300009042140080c24401c03142d1107030100300d642c40d02c0b04040720b074003a4002126849400000b1021441481081c000c040303920308000a001d42ea250b0781c807015900c3c2c8001d000700d0346805e03683c40501d40c4a004a10036840c031f07102d050000038401d040c541c0e66212180c82c00141000a0700907a56010203114914034100c00103680410101401e05051150028403c0039000440c00e00000107a03580244 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 690671232 1250 690669982 690670021
    0x80d1b050a064d0a090e0703022106090f070e040c05070209040b011e0602030f0d1e0b04060501030603120f11030c160f080307030c08130e090c0603 65
    0x10b541d44401c5a014403841c20702151522076009542d8003080364070410fa5140144004185140700e000a200c10300001c00b07000c50313480a005490340c0111034907014164926105c01440030040c0344d001c0140c841c00810002006041c0300082c0010b00b03403414880c050003180403008240a818480503011b00c8005a00300c100c00c1e10040f021600403d0b501c0c0c400b80b04844900502c0c10094001c06c0d214140302c1005030410143c1d05950b641d030710b00400e10b80c4014039503004221510412025030030030082c0504550a600092103041400440410030340108005030101c240091072a4209950b1000c2804181c5094010b40d80107040901c0d040c0100d50550329a104148039901407401401120202e8195142c092070040e02c085c1525815030340c80748500500d003501c880810b0032440038011003650210b241c10b240301014054616035030043d8140821540e0544c0c00e00707508030741030b240c0c840c0602c4500d005184241c2a04040c2c200c4150403041c80c1090b154561400a13600c0b491445140c0920130448044814072260116 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 690672482 1250 690671232 690671243
    0x4060303020a11040603080c060f150d0b04021f0203030108010c0302030613050a060801050a14061c080a02030c0307290601050306130f0f091a0603071a0c07080d1b050a 74
    0x10030fa03000001600812540e03000622050002c10011844070300070036407903c504112102180c55a40e04600c050001d4014100d00c0ea000b0700d1441e141c001700f0302100450703501c1440a00340a0419001e8040d80c54045007203601b26005a00000060000741d40a01135942c0b1001141000d500794186900001c40320410499040070b46940d0720b000424006140e00200300418031803000b040b00c3d00f0466480300203441d83c009140d21545440340894624203210224049001410041c4900c10b0041c3d070320380c48141d010841440452006101c140006141071000b00360043c410f40700c00c21840920380d08a616216150400c02251764403004003d080d98000040300d0b84181d04840041c400281d80c0351040c0200f400c542442e00d030314501118071059080590002d11854022908152030000f09000c600c03103100221560354158200c9035040041c095410030640c6020980d503801405c1c00110881149484600c2d030040300940e0140020b4801c60341c1240d890090071010140c00050f0109540314640d8130241e100d4020310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 690673732 1250 690672482 690672503
    0xf01180c05030604111303030201050109061707120c09050c09120f07030821130203060603070305100b0d1a1803041a0706110c030301051f0c0308060109120b0a0b04060303020a 77
    0x5080104404486c40b0882c84203c0895058483c100240241024001c85901524000d400f00341c6d4442440202c02800401000300308882c02c02d000103820a542010450f1220709401011600400c00d0140c07038414502c2e503800300d4030350880300c040040030800c040d44940e007500200e00d15804641c02142600589401544072030b82d51100003401441d03a4440c0c5039841c0f11801c0c8009001c090130502c1c100e60740042c000c5040b00c920f5180c080c1055111401448014465401148015801507071a040413405c08402004c501040030542c6a121a10600034440400220400c2c204450601d100f0154008c12541000450801d41000c00c0031410303018486040640e40400b007018401c20181d81c029a010300e5150019685070100c60102c603070340b600300380256889007400705905001c0003c1d1445145e554645c640d00c0868440303a40d181a592007102600d80c504000c04103401050101c11300c034122a165210350300d00c00252504a45202c201ca10030810313603128034100300f02000460b9000441e00c1c18507811031a4030740e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 690674982 1250 690673732 690673751
    0x506012f07170c121513050114090a0312060b09210106060924080114010e0910060315050108010b0c1924060302130e030706050f01180c05030604 64
    0x10724006407030b404214003419a01950052203004200c0c0e81c036120b0b0640e400001003828000c540e840e100c4521125020084003c0020b001d24801d642403900103000d640001f4450b2a04454480404401c850013441c540c015000d42082592010f4104408007d2000c1002090704000d00c401042c85000300041c0f0522a1150422200022034000b1026510340c00c020884e050792890701030240d54007481000801440080c1200e2000b040c504e00c011150980c3c0d503401001d0303080c00c008005041d26950454100181000791800340d4480e41000360048400342400c104440c86c000004042c0c0b000c001d030003005400b002c101004981d8100c603034141510803000302c41e80c40c1c2080355500d41c6815058200030101d000d14143d2141807001c12542d0220712550300b402048401c00c40302541c81640c0c2c80740f100941001800245422803d6507a014600703081484066034580b0540b40c9404040d14070548245c510828810010006540030701594013440303141900510030690490f2000d051400700410f80ca024136203944070340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 690676232 1250 690674982 690675077
    0x4090201021903110708060711061b07050c090a051f08060f0403230703090b1e0f1309060609080d09090c0905120f011d0a1502091309020301050601 65
    0x6000304000002101c28003a0b980811690710700080d240c8601042034800e018842503000b01300c0340c3c8100d12201545c03c5c0d03841c0b51101012f5136800298140c8440c00f03030360b5090545959030300c000c5000300c0c0c000f01d01081c0350400c0c2d00c05401c2c1484800210359018404103080080395004036919500c02d00683c3c2c1807540341c1e1503040c203036420700e404440e402e0300d540154083c4400f147c0b1000079003003081c06550707607136042030300c43c4030030410340c0300f58015804e01d00041c0043e40c0307400c041d81c40101080b03121074810074100398914a608601140c160003602c061519000d01340f040c281d0000b50301000303103403807001004510580320010348080d00502540040b5130b1901000c01105001c0d0158000030040501010111895100c1c0d26842d04429888040d140d400c4c03800c0355a14103178030403101c000b05104d580545103819403640d134400200c01400c151005540c007880703e5030242e5500c1102c055420071a0b440491003c00b944101802c446000701114144099005480b00403160ba0f1410001092400241d501c20020020300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 690677482 1250 690676232 690676247
    0xb030109170d020f22050108040819020c0a03050a02090c070f06050604020906030403080a0501061e050c0f0106080607180b09062802010905150403170a11030c0a0e04090201021903 79
    0x1000c20880c40054000301d0002d00d10040550117813500e15020b10b090715803004440096060b90043c0c5516800e101c0d60311083c00c440410507021140c3e00441e070421896401141c01400103a00a80e0107401085540065040034400e1381c0c0e000d11151802e5162040365501c1402034030501b5170203009aa038501c00076810f074446904581c1c0f6604003d004944a00d02860000c010350011111103010700c0c200000026458002d4080c01c08904050351811008045180c08807040c0d0002c04502c0d0080c85a090000b044e800207108141c0074180c00780150000b0720304503034054900c0d0100100c0d0040c482d6503600421030700040c0d0b000d59600300310464405903110301000500308600f22600c070030748000880e0f11758001401d405511507210681324409840b49550000310300b003402c0e40704850103030100741408841c01c1099005010380754400344200000a400c6a4680c03410307000e0704212110000c848002401d041401d4111100540d0780d1001c8405000c03400a95000075110702148004d15038040f4100070302020540103010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 690678732 1250 690677482 690677497
    0x9020f0304260d1d01050601140c12030a06080d1107030b060609041415040203040c060f050c070b030f13050a030503150910031a010305190602120f0403030b030109170d02 75
    0x10b510742c03610090b450722402840500e12004550303850030080c103c2240c041c0142485200d058482c1d80040313002070010358550740b0452051526000c1e144261000d402c040e0061070040c10f50000004840323060800140c90308840020b00c105025041c040402c1c00d034000142c9000b581d0b449582c1c01031549507000410218003940c020170741c3c01800e21b0582c0149824621586205a22008400c2c2c044c15007081800704030b210599000c0e103c410405010f10150740501486004050700d49070603480c0c0001007c0c5141440100c2e0003600004000205028032507820400d07043c0c00800c0e05061500e5286d40f6038a0300d582d403100b00d60017002d200d80030001404004a5151351241154040c110360141d2500e26001803450f283c0303010803100c1d0107004c100520309070904a500c41c181c2c2e62110040c0405001d0042c02030740c9004031041110440c3e001c1001d5143d52810707004040c0039407210806945c081c185850007405032a9142c1e9500d009a150064040c003141e1030280c24071fa81901088569641e62206103860040d11070440d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 690679982 1250 690678732 690678803
    0x3030609050712110909040f020a030209040c031a01050306190b0411120c1c110904020d050403020d0206091e10090503070c0f1a0c010b0907021609020f0304 69
    0x101080031894000c90b403110842483d5004001060150351445064015480655086422400020005204540c021003494002400803444039500d0740060300814045070100c0d160b40d442d00d404c200701300043c003134810b03010394009450a0321340c104004a0380d03800c07005003090030a4900e11620812561641d0142c985d041002d00184205030813031803001c410340e1105491440d115100400904500d1182041c1c82c80d82c1851110a00d12010765290040603214150f00003410640400c1948026a0381c1c0c4000c10b4846603048011410746420308002e41040030132100c84040d904600304018401c2d2006c9940110348512003c251043c036824403503181f070000000c0802042d540307012588814040000042d00007180301f2151801c042c7c1c0c4825451004c0e050741d204a0010010301580d50003144428400390074010f03541c0000203040c080c540001400c0300320940d90040981c00140c1d45170341320300c6e032101488080d0406031002d529000c032100c0715010b54400103001070107122010400700c1541c3e158000c0d100c0c68000d0107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 690681232 1250 690679982 690679991
    0xd05060a05091e0a02040f18061e03140d020d0c1401050705090a27020306120d0509130603020f06130e160e040b03062701020409020c2e0903030609 65
    0x203c0070003c041d166000c4221610041000203001402d0310300881d801d8171140380069142c9484c004400604102c464100003080b500c4100100700d040c0802925160042c448060841203861401d002284044841103d0300f6500180b4046003101c1d000240f01e034802d110b910300400032840340d00305000282c06140124659500708801c3c0b00c41c40d5841405020403040c01c884200b0450b40e140c10042400f008200304c0c05403010b847c00b005d07041e118036a002d0f5501601c0504000a51303018420030382d04009517412001c01280c3c001c181c0c4c80407401e11552004410740c00e043e0400ca0b05046400241c03401e550000d585104400c0010000c44010240c40c0c40001030451407541030740c40c05d0640bc0300007941100b140b00d100242000d502e5184500d0207018a42d61801c01901903c0030387c541581d940b00c646071941c480d40141c4900e01e15078030768000902c0200300400603854010b80321130703030300000c0b608110700078111403a241e01e221000034481800d003114070304011281d0000a01d4403001d02d003c3e00a010148e1081003000c1ca070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 690682482 1250 690681232 690681241
    0x24090603090a0606060203120417070203010c1814060f0c010b060301030f05060f010e0f2706010f05040b060307030207030e0d03120501060504060c0f0f17070b07020c060d05060a0509 80
    0x140c81091144142c07010304c0802d4580780f00300c1c0c7d24015110301030400b20ba03000224001c0b481040c4102414402031030319501e08202a00460f0030740c6c1348800d00c0c00016400705d040e40d48030301c5882c91041c06010030b18050b200c5540507034005034450103403298035403120500190844400200354080c40d08284003410301c2e5120742c0d40741400d060940000405649034000c40e00054040211040c03124140c400d052003500454850200b00444060000c1241d140c2c0c40c0908889001c01d404c0c1c002c4102e085a03000014030359903041251f81c0b8004101d5034480e500480c20a65905c1e010f44c1c0710800d44e030303101ca132515006031964910709040b65000019800250406660501c850905500c42101c99001403880028003041c1daa9560403900d500c158403488000680c074000c003a00103403810900900e4540a844011001240c91b101c006401c0c0301c2c00010321045400040c00c4080021030400994400c0090015050407a11840030610520840e0200c2046030796400003c0c0d0346613101c040b03101c080c4c1005000c03104549003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 690683732 1250 690682482 690682501
    0x31406010303021507120c090801060f050109080c0d080a0c06050a090b0907150507050a080c1c030204050906040e0102070b0406050a15030218180f0c0f01050924090603 74
    0x401c0c00254010b0041c00221000e0402076081c0034002e14480c3d584560a840b000000c0c0001c00040d820081040f000000008a00c1c01c02d00998000d00b80c00c003541040c1c10715250024000d441c8551110400d0741101590350081d41d00d82e03c601144a40050b50079a03110005001200c0390140b0f503000801d2180707040c0500c1071350040e0b54040c0c0340c43c0d40305010100050f00c0d030000060381c90203544240c15036440c1b00100089041c0c419009080e41900c40c5003280c2e102c0d100e84c1e40728200d41d0400c0031404120ba0140003103102c4c144001c8500075580c84c150130f0851805080001241102800826050145480750404044104258110380501c2d8100150420380c1c2000e141203005043c0c00e64036118414100344140d001c005607000b007502203d60003000100f200703008a04080c807200000f02138804904401c000b4250860b02400211104207900c0003038400600d0b08030410a2013400c0282160401900340660310442d115021110129820140355804080300001c1141851240d01803403600004040207011101c40b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 690684982 1250 690683732 690683743
    0x2b020a1203020d2405010e0f041406190e010b091512042105040504050406140403020a0b0a0b030a02130e03041706010909020d1103011404030c1a060109090b06040314 73
    0xc00c0c3c0002e200c049464006440c01211013034a00a1301c0290540c108404c1d0300984171000c19003400b42050059440c0b9500041c00c40710310100350340030008030b0002c010325032520042c00c0d24003070040c00f41d1041c0c0508108801816503014002c81c00400c4d030000e901e001503620401f00d01c9868107440c032215030324000a099441c003150f041e0760445440e04401d41c01d15424111100740e6000c1e11465858a051034602000c020280030003500903203880380d60b0811040031001c1030022510480c0240c00400c4544103929102c202034800804007803c0d103191180c00031156901041d80d02100c2e40440e1a958030f2400e10307580900811090f07192000f60f210005002420100a030080195034240c9400e680b0075aa8030340309001038031030712800254808081c8035150000760410440706443d40001e0f0001905098048078009418825102a00070464041c8070100700812180070f00c04240c070001e1699843e08100001a014145078054101415201d0900c04032503199503054600658200000e03491481c0c000a040b510782 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 690686232 1250 690684982 690684997
    0x50a0b01060f0e01032310030f030903031209020901030201210c11010b030703080909090c0d0b04020405070c05070b1c0f0b090c130e07030e0d020f0f2b020a120302 72
    0x903140b80c40b03c296903020303100300c86500a00c826541070380b428050904a03108401002030324215241072012011444005142c400d292181d210700607120b04504014100c81c2003121100c08031030800c070100c0c006071502c1002904580d07080c00c0c10a80b030707019019980310020002051045d00ca1803d006846c10035800f01c403500359501944002c00012410350189070f1a40010b02015088480401c58100c1c0d84c140104420742c010f61150075945041c0c80540002d8040c0c803481c20940b880003804080c40158903061182c00d41102c030906018180440550740c246c0c90f10100c0c072070b640030080e02084085520141d01c0e041494950384090400040081d092884000d140f01038030140149280d01c000390a0440d1203088031030040c12652542d82c0b05d440d00042c00240c1d08018080d008060711500610201c2c03108114028000d5016000b91044c0d240e2441650700e403000200b042845607114040100c80841c01c01d01c03080304000c07000000615411407041c02c1c0c0c0362030302e0032400803c5c0390140700300200b48a50503805031401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 690687482 1250 690686232 690686237
    0xe010f05150312030f0c0c03030702010207020a120b07110307020a0b0403060c0f0206060d0204090506130215071e020102150c130b030603030901030902220f050609091009050a0b01060f 81
    0x29040d502415a5040000f1486030000c1c001c1003c640c80701c14140e111503100c11800c2d510b900e48803000c8115810344d0800d88820001d83e40204044045142584040024040c0501080e141c40000d0b02c40310340c100c102038405000d00c19500c6e096400b0714800d204071f881142c0c028081c20303a080d50b242180d520f20f0b84244400c1c0c900900c2e0030b080607c81840350618481600040e4010035080e1203500400c281d640b0740403000c80c3c0c031594840d5003000040041c010345108082c5180c8480d8403220600510082503c0fa20686142d0401000810700240000351840c0945070b007006454056252440180e00e4118040c480c54049032103801000150000342009000190740103140d01d201d1035071410011840c0c0000d440060b815041070018044652080d80f051100c280010803c900600d06512070348d400d034401c0b500d21a4455107640540d04401c00500499401620550300702d0240d182414003c2d845443d58404084403545648910040c840100320707400e440740c0c0202c403441c0385580d0bc14000c3c14000015409401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 690688732 1250 690687482 690687511
    0xb0a0c03020912071a121f210213060b0409050405120301170c030106030b04060f2c06100f120303230405060f01050102060135060f0a0603020f010c05010e010f05 71
    0x4500a001c1d0603103120280c590030071b40c15a107504004d80003401d6180035400ca00401c4090015045110b402d42c001d4080d0200c48a855200e06401401802400384221051007414000c0030082d0f43c1e082e0b41100e00721192840b0008454559142a905100915450320144000440003156488414060071302225004045402d080c82d0301040c9800e0b80d24510001c4c00681141001034045403154005101030300302d10304001803261040801d1110281c2c8a101d0fa42a120990110002d0302c40c104007094000602d080700104113840c0c43d00da1a038500945c0917445040080498070004c142c041d8101e089003200215a28482504041414603841b604540589031445604082607005050440c114160b03339040c2e010740881e07802d002c108040502c0b4509100407090100020084001d02640c07040107aa949030060076107803c000041210a41024104085041ca000070800059032442c0316070b00d24500a00707002c88101c03403500709107005041700c0f440d0401c00c4d400c02d03001203456029a800140f003a04139000303604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 690689982 1250 690688732 690688769
    0x5070809011806050603030910020705031e0318010903150b040b0603040f030e0d02060304060203090705060a09060f03020f160b070f0903020d1b030c140d0b0a0c0302091207 76
    0xa00361100c40d10032110144003071002c403001c14800d41000354810300140c00c891611100c3c0e030200701c1d0300c1c03071720807503200180c2011805020515051100c208a40b0941900c494040002e40469889200740c0c0b42d1104203601d41070300344a00707034080c055140c0155040741c40540381d507845e84903440240400b00f102c2c510880c5010308401140ca0100d054034007581cac201000b411486038030780e41504c203123404442840c0c2c045000c850040c0140c4c1d0f16002180f0551240c4405604d03070074150311481c5400d45607004684a44411301120240d240d0048403482199000d207070044070b14044040a400a114914205042702c00000740c54150300cc070003040c080064401c0d400020301e43e4500e0005c030350034044180d40321300042c180c0310100094540358a81928007401000c054010103100c0e0301c050203540f910b41c021214130503410000c01030244184202099420700b52194100c00c4190b6484850240c40181110b600d0365550030003400c40391103507040e00c5500381d003e00f1074a94181c0005c0855901c1d20741d846090519955500d255 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 690691232 1250 690689982 690690001
    0x6030414100b01031b0e0904151107060b0a051f2f07140a1707090905070e01050f06250501061404050a02090607030f0212120412020a0b06040e120706050708 69
    0x402d60f40900e5991406e07085010080101c104000390003560b070003001600c10b00014010744103010a0001c0500c0081daa044c451030181d05603542804650700c2100810010006500e030840400200c0307c00032a00740c03002d181d03036105807071a07a12a649a003940e148104948210885d80b440305d040a82a44100c480590340c41102400c900385c001c4565401c003024035003c002110078100c940014092142c2641d10454440c039410341100c4c0030003400c0d15541e00c0b07500d0801401141c800f0807800340c4015102000b030031000c00007052032845450311320190100c03a030091840702d6100700381c403010056004d0000c0c0015583e8450381c064001c991607406101d680303441c0c0400c101c161709108550302e0403006440d5500b80141d940b010f503407428400702c4440660195400002031162300c1402064044108503000c1128241800c0c8510b003421040701c080195803205210001140e00588142c0e403001048801080c2aa11040d8542c00e12900e0b03241c1c00310110740402c1c00401c02000741c1107580b1604035681c80740d08070b136140d8401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 690692482 1250 690691232 690691271
    0x6070c021305060a12020103060308071110090b090603071b05030c011104030c050d0c0b0301030b160c020109030b09160e0906060d0804030314041214012906030414100b0103 76
    0xa2644241d04440400140300700c00b2034a501c1c03500504000400714ad8940742c5681550040320125044503030000300c81540d203403000c401d20b1000380503d42802c2013801c100d00820315100303119240384507040100004031454441c00240da0500b0716a0540c0c6202c0c0f1403480d0090740ca8000399145d01c415401e0690034140180000103079030440742c1009171108580e1411060102c1014200703419208109079403004240c030a8940001d60013103200c1c010504080c50300a85400242c110801084104510f003000000943e0b84011504107880d009103010b1000e8445040b118034013414071404141e150345001d4005180c01100340c00314840d01a1400741c3c6d24a47c0e845d400c10165031301c03038903000b49100020702050006c01d200e20520016042001042441e168492144008081050400301c42d030011452800c10305d440280039616200ca8410f2102c80310602c800405954400b0003001c883c02801c3c0170000500340404000014840c0031000162030a00801440c1d0314041e044604001e0b000c2428080c141c100805980c28 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 690693732 1250 690692482 690692491
    0x3030e0609120a063b150705070c0527060402160c08011104080a060b0d1a190b0a0b0708121006021204030804050105090102011d070f0503060105150a0c0506070c021305 74
    0x19103405c48590040c030700ba02004071400c03111184641d156102544000c600d03064080c401070340781e480d2640c1d20b81c541540c0c00e1480b030700130034041c04142015540354038183e90310b84010340100841303540951f00d20b00840d0003130141c40c0c030347e0541140c0d0310450070500111032600780030744083c039000340000300b4032180d00540c510940c07007a801d80e940441c54801c04190300b5072082d985140000c260400c141c40c103403185a0101070340780714003610400003018803614001c50070760010b174600511814403081110700001444c90880e403054155203940000c0e100b040100c064200d40704600306500c2e180c070300e00f1700c030440c4108801d40e4005e200c05031041002407181400c080c07082c1c408403540f006420b4500790170314004407502d41040d41e9803815507485884040c19804100903507a18440040d00400f065440e101d00c80c40f4040155028038000d400c590010301072901c898907000400380303072420b01c15034940c08010100c82000010802400c07601031103040c094110b9009429012040c0201c40003400c04000081d000f04641c0180c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 690694982 1250 690693732 690693791
    0xf1e0f09060a0201060f06030e0f06040210050903101b0807050906040302150c01050c0a09060c0b0a230108060612011a01120e030d0203040c0e1003030e0609120a06 72
    0x4401418540700c80202041c03203040c4004500c0d1a580d400154003134699070400d00c0403135243c804c1305070322400400c80c0b40c10819261004014a080a4000c2070041e4060030440c420402c0024411881d904e04110980c40d42c081001c0801001e118800300b5a05214007000c1500041c1c40c400c0410404d9101301d0070b40b2101c0344010b111924051859003001940c0d403200614000e048002e0014440d80340303003803081340d00c102c08000f541a580c00c0d0010008010620503048002802407a622660102e240800f0140d0f0003004036000041c0d000c0d890268620700d03104485209911907040001107554240854081d0148000742d5020045040000042d0b00341c601d50b581c540940410a01400000d61090501046500100c0310004c0d02d2045d8010050941d442254411600c0350004248400c0200c1003d0100060012800184840c206045041c4105070181b00c06800c02c5132904425045a9038007080b590101c400505422101c00f0020001c0e40700c20f007010058448620f892051000440c40c062400e4119034a138 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 690696232 1250 690694982 690694987
    0xc030106060c0c090b041d060a0506180c0912070603020d0f111204032f0c0411031306060e07080f010918080d020403050109050304081006050913030e060f1e0f 70
    0x80b0001d4020b214455900364415107550f2090304203100f0460032110900c554019000c2450035944c641c0a4030b2000c0c003160301454334802c41c4601560240030454014003a54040c554801c1c100c0001104565000c101a440340121b0a00090701a0550b0007441c1302408514280031181a940d40c01086850314aa000c820120801c40341c0310943c004020395074000d20900300700106002441e03c107d100704451251421000c410704242840b0042001b025088440072a014802809d2241144a40e800090031240050761030b84034410030070209410450241c803561507010000c1c80c041e54010a42c0e10181c911001044588002040c22000b038000d03002e11140c050820606a1001ea13070b02040b940c005420041e24903401d00011000440a008040682c1d000380000c546444c24201074900f0944090581c0c10f0192420384104242d444229041d0303400343c03e40c465070880104034201554032012600204d50701c903000003512900420b40381c4c00390080351050864041000f120043c03810491090400d4801d004405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 690697482 1250 690696232 690696239
    0x1060b0a210e03070501051302010c0201110a0605070314070306152105040602122a030703021207030501060306170307081303080a0804030f031b0f0513080c030106060c0c 75
    0x662484158200c1c118009108107080781021000ca480000b0b418140b600300103600c0d801c1c49024020680c200011015500d80d01d000c90b40081c2a0780342d0840c0003418801c0c427040d40d584001040c420401055006281404280340240d0000d0040246418050b00c0b550480080303551503110344100015184a01403e2041c5007809509441850a1002007030300030340740040541e0f40503003500825002c0c0340300e100d01584404030184190707010314004080c0f2110000e0118162079480e4804619400710040240e0310360340751250081200a0301c200898041ca00301a0070074810155810791001d0704032442d582c0d080052a49442c1111585050b50500220543c0140640c1001c58107100c010141901100742e0030510036940d546005041c3c0110402c0000301d405901004240354101e002a00f07856070394602040f0207042ca84142c0d1445000f08445010030030041c2095000a001e802250800c1c0c0b401c0341c0745104156a0700c0381e25611400051140e00a5080043c0000c9203405503040034807841d4010b290392119402e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 690698732 1250 690697482 690697487
    0x15171f1508070509121504020a0509131e062406090b04210b09010b04060512060a050a020c0f0c2106130c0e07050c060114060f03040c0e0c1b01060b0a 66
    0x400c00940e2001740f502801040394010040d0b00c80d803603103003106110075103003d0040250400300b07640203038000e94000d0104055040c49080141400d41d12142c5000c18003028419914641c05a0700020b018a2401d420540d40d400a004001142141151034044460315448110b500124a1261368409507041c0000d0281100702249854110003030002c2c080d240803a503c42035001c00003038030310710b9070399640c0c44801d10707642458000d2001514040d41c1e2184483d00c0b0340c07a01a40e405004108000e41c6613200c0101d4103103117040d0101c403c10180e4004442c9844840d040e45502d1381b8518555500c94020800b00b8000040607115802c1c0c1c0011140207483c130307941d0340948c51000101c1c0178802c03214007100d0800440d0b80002d00028a000f403049a65668441410380c2000c0d107031030010380001140c50743c454880f0707001d5500e4104850200d002c406e90140c60740c0340c40ca0029510403403500202e01104007881000071004a02c0040d10401c500f00c0041403022603110001400c9800c24090032030160410040b203202d050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 690699982 1250 690698732 690698737
    0x20f030a0b0f01093b090c0307051003230a0b0301050f0115050a09090f091406092e0c020303061305070207032a0f090b1915171f15080705 61
    0x1c03031902100810762880c481400c2d100480001c01465505c00e80b09000e0000e100700a80300030305a06030004c102030382c01c3c0342c001050100404140301c100740d101c98084840300441910380c081030036500d003040c4050038918900c030054441d150409007e9864000005c3d411103111840d0781c1202d002d659900d00c140c2040302d003102c007507100b05d8212050203c4240001102d5886128500004020041c0020310301210300d09800d49455800341a861076111100b401113500e4045541100b205041802d94030001c0c10210399102030200e103141520040c54005d0740f0b01d0543d0088000c500c100c00c11a140029001920310390340407aa4142c41150060344640d4083c000202142e925501c0303404030402c04038013461242041c9503c0f0030a9082566440900f450820a881c464001c05500070070494024900742603103c000304511101e40304183c039080c40202c030f1394401d0b401804440c0c400c00c40c2081004140c9050408440c03108001ca00d511390810500c1400981000c0b1582e40c0b500703444c1e05030ba41c40101d8a070030404a403681c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 690701232 1250 690699982 690700019
    0x60203090a05030d060311032b03090c0b0301060305061e01030507050d050403020f0d050f0706090c0e0a140f011503090c080f0f06010806101a0d020f030a0b0f0109 72
    0x91041c801d0060108608101070702c1942c4d00558040f40007411403802c2c0b400541c0000303455000f0340c003080356400b00d1503015119003c1905c0c900e402d1503000d903007101c1c111301800829001600526520b20f01040c0c41c001200114142d40c070030b032014001b9807603031010310024021012001400364010b00c92074925610a03048160884954039080d0b04180995400d402220800d0350120050783c450404a0452201404503109248030b41c00e100d400c00440c00d408410511030440001c0000380d60b241e10104001030f501e00f00d0050040c80c1c2c04210b19150186001c0020a603503138410b5403010001c0001494401c441e00c40505aa0041c100003160380c07401c41003900035140c032850840d1302c041c102c4404070308050f0810214880c5c0c900d400c002e100503109254807504101c01030b0080100f41c4c008a040004801105244e01c0031100c241d400c43c00a0901e0284003240760240403840c03403a00303000060302141c850940b0051400b40140180402020000c001000701810782200424082003480d141000041c1c0e105603aa00707007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 690702482 1250 690701232 690701251
    0x1003020d06030602040602030a020606030606030c0918031314061e030a0e030a0512151518030102030c0903010b01022a01030b0d06050417070b010b030705071b09150b07060203 77
    0x44544943d220b60581e0042e40080005a0010941c440480c1e03040000a40020050f0080c284508100c40880d4546100f002032500035000100810014000c0e8900c2000c0350a0440544e92104800d01018203800702d076104402c040c0c80030701101c2d8440d18002d81159a9540504001700f1001c08100e6a0320254000030f02030fa030165621545040421030a0000340002681680d5a0b036452900c1d0224042118014040b072000f080308007824001519202c42802c0040c0d65500d415071134510031b00c101d2501c03c9001e0301a0383c06500200501401554040140c01a540c00710024408110240012070350b03100400300104214201e903010034511120f0510012428006140104e00c40a440d4003103a04030f103a2000442d480c0ea584c500704403d00c141c494140c40a8204c200d4824035207851911030030041c94060103604181c1c0800400708000c140110122901c19600a55420031011881301c0800300740854450b08000381d04180004c0c11284540c4440c07000e452020340a181003c031a926240002c3d000100030405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 690703732 1250 690702482 690702491
    0x2701121431030e12010203040210030e0f19020901150206040222061d0907060c0b060126070311040303092130050315010e15040e06030d05091003020d 66
    0x1d809441c81840103003900a866034807400140c1c0003031002c040240601d44100364030500920005030340c2d42000c113507804860f28000c101d9590603000103050424001203504244684042c1400c1c40129102011040b070013150761490680c5e880c0340c0d841c3d0200b0000480001604080001001840d01c03410310900243d0001240102081188000007112a1034112002d0310551303410940c1d0800020812540c0a1400c401816190346003110203451a90000002002c41c1044400078001e0f0748988848940302d0b484001e41040710824510450300c2200980b030347e400080c1402c4075419100c07440001c40e421aa0300d695407802d0189042d103002c00c0c00050001f58070004100c030f03e498010076019030140b03100309120b250460f000d4600d602044890b400c4858140107011007801041000d0b91b81c011003421488003800c0a5003d42140070001e02680065114900083c002240118881d01001625171280d00d064007102c03070180c41c20b0300554030b40c010480c0c120b0740411070210018180307100c0d4002c1c042c400940b010204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 690704982 1250 690703732 690703801
    0xa081c0306081504230303010f06051617070c0e07030e06160c060605062209090206030a0905070305120703020106120b0115050c03210f010510050f27011214 69
    0x8403240c40404202c17109502c08801400800d4040301030000500d42420304901e450049a00c00c0c60341441c07413001406003001c008440015502c00d2044446c0b03039138804002200c0c0c686610303042d10500d00c2510503400080c584009280200c0f000075026014140200201c0364244820600301c42110300c001c01220381030b48885000802d44c46000180142c080901c00d1649a401d180090b00c0ac150103035031100400d24144510744000da01c034501140d800070003401c004030314110b140c20302900d00000e96000030070034880d4407803c002c0c16410030060408103210382e0080c414983d54031292202e00b0f85125000e4140400800100151019040c10b400d442a09040050510f410080e54a00316000410300408804c1506207804042283d0180d081d03209c841c002e0144855410301011810b0088403070b044d5001e02200203480b413400014101a6100050103516842c0444604000b40403055003c51105010441684810b00460341701e00800c000d4002c08a5070340040c0d61003032680c90300c0260402c0c460a011420880e00d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 690706232 1250 690704982 690705023
    0x1051e0303160f0b07051606020c0a1208100801090b06012d020604120f0c08180a0902190206042d02211603020102100c0302090a081c0306081504 64
    0x400c960f010318590040c0144070300b045807040000030a5102000410008414052200918814100c2e080340c0010307107400d070007409145410a51107014041c400c100e00c1c042c0b20158046000c5220b01c03541c06d8004140c950383c0d60068203035081941e0040030160340100191541d40300b801c2e03004980700b140c00e01110b10402003a4500074041501d41c44c40058000000704010f012800512510664440c64055010100d2800051030358683c803400510701c501c0020b50503003e02c01341411515000c0014655007030303941d41b040c07000025400702d03d40030f480c0da0301d03800702e050340500105400d8840ca81000413030100e40e0401d2114840c074442c0614940720400900541005a02d40f1100310008070f401c140340160008007081020319200e0a40c41d00c1612800c068020310050341c1c041f94981d9554540300300030400d00100701d001d030081c2c0100504140c012803030b44e2002806141c0000c0c60140d1041102d10000b0b243d8071801c04070b09550140c001d0188a500c0030b01e8007010b001021941a6200d0b0240d044480d0030f2410b090407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 690707482 1250 690706232 690706267
    0x111c0b0a050d20010e060a030f110a03021923030703020d110909060f13020306030a12050d06050603010e060d031416030813320703060603031701051e0303 68
    0x340c482c1d6480200c1e20207a03881c0c148442d0404042405c1c000c4000b254040056a9407068100e02c0c0d00301500c0b84c0307109845840fa40c0024841c1600c180b61541c4130620004000c0003034210021201d0032448040c0c0801806001e14104084d400c03001d0304440d400702d1105040802680040c014008043d401c0040340940070041c8902c121215800d00000d0707903a02c048080183e8904042e00c510b22030030308001c0945a0380c0c0e4200c041203001d000d100c0c0250b140c0d640c40c0002800c081c40f118003d4652191400b00c0d0055540c458010848202181c3e41000419110070601405010034001c02019040aa01042c0c01d4a8212010759406100c1c1ca484402e41d01000d00c4c00130641c01001c00a508407880b0040f80d41055004a0402d911002465414135000c0407034640d01c08070f0307070095444041c0c56000e0040c0c128111000031041c0358480c00e9800c441c40c1c00d542c0e24205008002d0340c4020341c00905040720842410507003034040703070403a68010804084000400c09041c04606c1000806905200070001401c000750306e0ad55 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 690708732 1250 690707482 690707509
    0x3070b09031608100c031d15070801050f090408071a0a1808070f050708010c09060807020109050601060e010c0218010e09160303050a050d050a0609111c0b0a05 70
    0x1001500c40c004082498a40b00661042e03015070000c6034010300000000003448029500c8002000c500899650002c0d0700620308a40480030031200010707440115040095450b00414002200c00c4980d035800303008031882d030002e00030140e0250701403811407868074002480c5904140210f0030740d454a81299074030141a28010f86800d111050300c010461140e465106101c84d0f03102c48200c100740d042d030315581d406161049100c01001440d86100314800d016040007004003918040c40200a0900301080240450b9901e1140318001072240000607481362060046401440e80b000003031510380d090003810340d01001110b503000d04200f0844141001350781c40e01e510701b00701410720310328141079410000c45480c3da441c001c110b0320156101c403142c000c040740c40303800d81c0c0304494240c504192240d030307003900842d05440348043c5e00e4606c1c0c0c208418070640ca456a0310100c01c88811b5030b402c110502c45501035242e540640c20200c1106203000100c1114280b40c0d4200c01d5116800410141080342c032900000e182c0c1c40c1040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 690709982 1250 690708732 690708749
    0x305030a0521091524040f09080310051e090f0a0f0216151803050307021e06090c09070e040b060706140106081509151305090f12040803041a04050307 66
    0x2c0000e481110204d010ba000301c1540708541884180310359011501c00c10034640384c000c1d640c40405601c41c81c400e40c400d41e04554000101e0b0b9603800d0030850b070303402c968960048600c1004104450b107162650b80e0446130301d070900600020b00999031090f0007403a111004116104d0a512441d034950a8101d900c000c1610b11146c45040c01c0701000d5080c803509910450940d100100d02e02190747d4040310034030100342c030707047e07807515080da900d40e5441001c908020600008032100c4d030241203440c800e46008160507102c0c603900812038211000703080070071860701400e0352420082280090380654070306290b0446c500689002e03028900d0840140d0301d581c203c0380c40c4803580200941080050002d59403189599800800620700410142003120010340d0006018040440041c0b02c80242c1485030ac540b0000d002c40c03419141d0402461804e00c0c42030b070f00e80c1010a90464680220040004148011001d0390240d81c02980114107241c24482c2c0002c045901c10080d03011281c0078080050540c1e82008014050141e40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 690711232 1250 690709982 690709993
    0x230c010204090f02090102120c030403150c0e010f05030105010315080a140f0102070206041412010c0518010203031e0c0706242c06120a050a14070305030a052109 71
    0x3200c0b0030111100070300101c0340540104030b008003580c4e0000b40c8103204a40c0114066961074503000321840c5215a0384000c01e038030600b000d104e16030141c0b030344025680800c5840f1b84007050700c0702004551080c0005100c80108a0034401407040e54400d60000801d080200344244506848610b0f00f071610709001e0046954000c81c0c0342203003054200b48440d4a843c6040e2000b50b0500700742d40d00007402c50240e40202260081c0c5651845810394414400444d01c03080e100081041c0c1b0b9100710010710030f6010101a03801c0d0410300c4209245940300004403803040054154010000d81d0704149480440c1025104007140310042c810180410342c0c0e4070500c01021490440440c00710400b01c01d001160384154040c1c148140c4141494204401c4e08079001824400300c01c3c140c0a0781c1d1080002926401c0c00b0700000e2291060458400c100f1800180e000d030441d019400c14890400400d046603500d90003400b0042403504244110035003603004d407002d40551240201c0c444840e1220704640a160700c0101c4202000f680903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 690712482 1250 690711232 690711239
    0xb03030706092604090b01141305010207050a030203060c0304140f06160503010303080a1d160905010b04050102030a0f05040e1315020a0f23220b030412230c010204 72
    0x301180003c042644000c014894504400c0c2c0c0c015029521410304140d4440344061950380c41001040140c0a50503ca10b407125140c3c40062609107480c00380c2801752088680200c6c0fa85403042e9030b00101da0b4000c00407c62070340c920440c45466040078100715804a541011640f42c40000e020000801120000a265528004400c0811240301901000900404100501c04641d104281681c400140c0c14040f81a4078990140861001800d06006150003132020341080f1400c1100408200c522071002400180d80710180309020b80301d903100d101e0146e481000300d1aa114061103242c0c90315415414000d00340303507640d441103610079403c4495510442c406080c00040280380e4a41c1c1c030740c480342e6190450510309503800150860941075000428440c0301c0b000840c4d003420300d0a84101020b25081050340311880105010581448034009990901e0b121102240c580c00010a8a2250360040258882c0d40c02c155800d072048040780e80c00714644050080701e400305400c82c500400428152600040c0d64514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 690713732 1250 690712482 690712493
    0x6090c120303050a141513060f180e21090a0f03140d0e0f030f0f06092802040e0a0c1701150b0901030e10091227180b0303070609 57
    0x10092090b1141c61400e003600b400031140b045080d43c13006d40300c40510584628500001c0f052080c401c2c00c000864100800494500d13080c2210300225141194000c1807004910742d0a029101c200d5031380c01701a48014500b45212440c52030056120000103c000d20b4440d130b100104094840640000340480640b5600304100301c0c100485001c1c0d0022803010301407101c50040010051102502c2c4103100704650102d00d80746680c00d0010700c031341c00b2240013168180b4015100e182c0e2144421280302e0018081c1104448005101c0c080c1c1c200d40032801c0700c4409441000380d0802c0010801c5464104851003401c2104000030540ea2a074405400320003505100071110500b002d0a43d00c66031040891004121030421071605103005490f034512090801082840220101c6443d110480c284e0b00e004d50b007881842010700984c244000100601955658000741103102c50b6425054580c941c11140a80500c040000e003210511240c0e811260b404045503140b1000c0010740313550030402c42966030a5482800008204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 690714982 1250 690713732 690713741
    0xb0c0c01080a02120a0507050d0906140c0a0f050f071b0e0603010e0601051c0c0f1e05061605010b0325050a0501020d08150901031203050c0306060405010c06090c120303 74
    0x50b8010705602d0701001e500014506240070f044140c8203915040440c2000780200c0c140d9515003020401000302945500300b40010344160303079401e80c5410800c4007180400011500f02c800f070b01d065032610a01d080409a04030b07125485800201007040080c000840003d113070b03022907080301111003070784841c003030402014030307841440031300040d120368580700c80402d802d0004a1001d04440040310700e413000212182c03001c2d81d01030320960018860301040d4000700d0076a40781030b603020607210184400b16000e940ca4101012459071f40c011250700841c1440212003051090301e00400d0b484c070580011076403200c030102083c5002e84400d075501101518045403455010050b104800404003254551450391030140081d407103448480c800d0381000360b00f10005c0c21415031440556050900a8820b00b501c1da03580c140805490050105000084e04090114987c0404041a203000300c000030083c030310301460407006444204070a14121201511180604c002c030300716402040041002400780c00a41070ba40c50020201c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 690716232 1250 690714982 690714991
    0x4031104110901020c0904061808120606031302100c2111010926090d08030906060d03020c010c060609060f0612021201120f020310020a020d0801050310050705040b0c0c0108 76
    0x2180d0511030b0145582c2d001404c0503c101c019074080e411500d99040403c054081759042c3d240c58184543e504041145650051000101800c01408686c964008015803440264cc0009681170050401c00142c0f8190002d41110500c034101000340c0b40d25940d859007100c449050b06a114050b2030014806c07560400051180280c1c3d4000070130203e11260794040040911050391181e45000d101b1600c0140c040104540c95410001d003c5184c1074800d1502c3c1c1c4c0c00e40d100700c8010030103005a50200d0068280050f1540c1501c0c0c0c503401a1114040190045540c694140c070181c682c99103c0b030000441c81480c0c0314200152101d0344c4421202c07410070b2070161900a1040a94030001c5c03041180341e03410300c50075400c0c506590800140403280907231410040b025001c2c00700d0103941401051030220b0ba120480d401080a00125004d03103507600712421003a100c2213024410b8070b41603000050030083c41c006a42c8016440b00081c14120b00b46a02d40500701c0880e0000304041d405503100742101c1c562580c0100703072142d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 690717482 1250 690716232 690716261
    0x3070506071d044b051006050a020f010e071a0a0914030a06061403011b0c0809040902100801031b050904060f0e03030a0203090c040608100504060f0e06101202013204031104 76
    0x728142441b0744400d2041d2841540304020000c10340d00172040c401d0000c54086080b00c2c0092100c4858100703855252165071041d65041007403c8410780341d021844081d00d402000b1500c801550300d00d804041c0c60001d10b440e1110364540207410b26840007820b244601c42c042c0c001d0a146680040d104824075084900c224441180785207008031411300f1551102142d0782e200d82c40703031900d51550b42841c00309020b011040d5000b54440e00c058400808190701a0084c0e048074041c0c1107405908050070301407004c0022a005168202c601240003402003403040d0810040148000700008a9907000d40c49603045030020341e030208443d50004144009607000300071000b50350104843c10020b0343d1500c0c00c10756841c1c036241314420495071100001030034454568440005001c0807a0144040c0c0c440c44c003007030707203030b11045031203030444040303a1404245025010f164482c041d0b0b040c0c591b114005181c210443c0c910b4859400c07400341040d000e51a910403248280900b00561150314034854141d02401004141d44a204d0b100300c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 690718732 1250 690717482 690717491
    0x10204050a030f050a140c030d030605060412140607020d02060603070605040e04060e10090c09023105060a030207050607140f280203070506071d044b 66
    0x22507521008000101c9901580d08100020180752541c20142d41d214090585070050070a00803090303000c6041204294210280e07000300345011025411954103000b520707000102448240905900001c0b58860750b4029503c4035000742088214a00e0310004070303182e10040e045a0b009000d8141c0400078181c001c035089001d84810381c20b0410080480c0107030300c00e1504a02c410008a020301166600241840000c942a2582d2aa2101881c00a0081000c0c00c50b0305500210740024030441602c01d40c2c0c19082c02e6619000345880d07884241952180e400110f54891a40500025440d0348600003080f60014644001d41c07140c229040c050f0402c1c1d00100181e060007921410a41001041000c40b402d2041041c44a034450000140c0740600ca002d05407109807040140716804103090b0000042d00810340b08a080b00d030241c0c1e515804844600038400c980b02024000003107100103113055040f412500703401120219100090320030488120852000d5446490070204403210710440d0000401d182d03c000d03240500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 690719982 1250 690718732 690718739
    0x2040f05180f040f02040209030105040308060a06092414040e0621062a0310030c06020f120d0908070f02040c0212160c0305070803030109050138130902030f09010204 73
    0x90b40003000500081c00700c1400410201155200c2d81a03030000c26000d00200f205107054034025106107802d6800034890950600c0014088e0f11861040e025a00f8001d14503c048480395901000c039604c80d8005014000342900c02012803044d64041c0005000d1010b0520050070040306202240c00c034140004288060410036244008000030444d03001500c0c94100c0e01c01d42074400390300550548094504407400000814002400d280c0105201130320b00601701c00b42c11555072601642d66115004a000440e0001d01c0e00030a00d0401c3c0c2c01500d103411904001050b406100c4c0e42c0c6038050780c0a418120381200d02d42502d00c2c1981040e10610031600101d000a041640d4a07040001003402200b000c84084c00035108580108251a401a0021684802268086034442c64596240c1c2c00074007070f04000c1c51424000040074400504044030b000345104030f01c0c03111158030b1115540c101d0b2070000400b22010410608807600362446005004011070900143c503800c4c44103c140e0a80005810240300340c1c0140400e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 690721232 1250 690719982 690720001
    0x1911060c0a15020c031c1406010f030f061203020a0605092109060c0a080c0c030c01090303030513200405100b340308060f0108220c050402040f0518 65
    0x4400399000307040c0c0b038007030b0030241d5031580644101c02c04040d442c003000c00c1c4411022080598a850a0b5008078103028a003004516007070207031710440750340340010160030088195034001d500490841c403a200c07003c80c24a0b15407009007602c40c40c0140482c0140d01ca058820103222081c0304484c3c210400e04090a8000400d0030081603101580c1182e46a001c00012000d100d40c0c0c03082c04841450ba400070a0f10030402c16428185460f4000300d13a840041d014058100b4054500403540c41181041611868521415901d08034010704c801007190000700700d521710701004208440718520060707030321214040454506101340b2040e6000a48460b506824442d03003840540317540c0041c0c071300104442c0400d02116400e04e48403010362801466501c43d46850803c000103066000c0441c0d845000d051315015141c010b0000111031000040b50031b14904280855030356510680c0c2080515098011802e02022548880004089a20642c0812680291000100074074100b4080d14030525510100d080150301e8182c0d0355 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 690722482 1250 690721232 690721243
    0x3030f11270114180a1e0801020405010f0c02221a0405060303040501030203131407171c2007090e0106170a08090a0b031003030305060607050a02060a09081911060c 72
    0x42140030f0001c03508007108849030510940084009003c10100b5960300320145d038151104410003501c0601080c003040030101402203c048440680d03c130100f00c81401000c482c1c44881082c102d074030288418101e10325401510550b5854100c4042c00250343c01c85001d030a6044c0c07002c80308e450096050404005c0c4613070b008019941291028240540d5942e03440201c0301b00e9125003040141011008070f0074403415040021070390141c40f0903078101001c7c0c8450108595840c41d9a03c07850b00504810720152086611841060028080c403000041c4200401c041082c00c107401c1d0741020131441e80e2030b1460310700500c0900903a8000c10159814640e8034101400041d10b94a050308043c001d6440004c1d42c418036110701040800601d078180d0056120300b01803650301c2501c1003a00c4198002030410000c42c040b450030b038045a4180b58800001c0c00c028086500b44155600030030044800d112035241c00180d8281c0c180564503207124424144141c0781c4e010302e003000d080e4100d40055809400c05101030310400000140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 690723732 1250 690722482 690722507
    0x902132312120304060c111f1a0d02040b010e330c0d1d130203072307060f0e061006020f070b0a03021602270f0c031303030f112701 58
    0x1002c60164080c5101f40c40200c8420703e9040c40303108e2040d040804194414a05420380e200040a00044503402e440855040c2200d681d640d0200540d0110001032230b08d030340036403038240060610345080c45914000030f9903c0b41d1034041c4039410340034003130202403d1b801d00b4100d0324074021240344c0307810600e00003111a80e0310903041018080c082c4502e0100080411003c510301200ca004203849a0104c1c8240d017407029400079680741000c101d0700e0304602d035528100038480701040d40c90031080b401c0c00015120000582002606010708940d141510055508140103081c40345c2c480140011005252080003440c10008070703c2c0b090150003959082c015030004204803104900c0c1441c01603102e4040e40c07215002c4100b903000c0254084041c1d184d2220403400c0c0380c00e851001482012407540d0750350701206261000c4046613840c0008200b00000340b07600320303041300d0b030b603585406841c0001d180c50b0400c481001305c416640056006c0701d0007003468040d0048209490b08001400c00018507038403202e20020741801407014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 690724982 1250 690723732 690723743
    0x1d0403020c1212071419120c061d010b150f07030c141c030f0608060112080403050f060a0e0109020f0603060301110d06050a050d03090902132312120304 67
    0x304082c40300404002000d800b82500811a590352000d00d4443c910f001852011000f6010780c119a00314064480c0c1d901e40100c2d0401440540e03a42c160302d085440b07400a150846540d552403000154034404200048242240b183c000642c074402c09041107950a074002040c100004108054002021403905980190782e160510b0041403c46242203807030340901c640c11142c68490f6299245e0b4011440c5408111030840c0e840c2040001c4208500302c007514100d018090705503005400402c10b84034004044c020843c007d5800c58109512039650a09241d4461003503c2c0c1e581c03218080c8400e20140388074000c01410168020000c0c407150390f0120315001c1501618070301c90513000c8001071081d01e0a42042c00400000501c00fa6a9115200d041c0c000307011a001d12400340d20b40130310215540c180000c0701d100c102e82503100c801e180e51814510310081e5000c03175408202603a40e802e0004095509030400040d00440c02880500d1408410500804455039202032004c0c2d400304590440495418040382d80058008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 690726232 1250 690724982 690724999
    0xf0403120b060c010e07090c0e091603020f040e0108070b0304021815030f160f0819020d020901090903030e03030705071b0510020f0d0e060913060b03101d0403020c 72
    0x410024105001c1c80a0400301c07942041003213001031030003003101300130754032444810041d5072014501203488989c12280260040300400104000c08d0102076600c090841515015117044081d843c0d504140e0003542c0034080e06c4040c44014402e804c2c0034048400a000c10f044060f00350314290300010100c1c110704620103131240350b82000c544003000030408421401c0001e012142140345507030506035602d140544100f0428100000403c102407405060350803102154000e080045c10981c0c4011102c00d02001240e004030454030148c016103800300c501e03009140d003081c0000c414082d824058191041c40d0913281e00303a0000c0003006000c1c0c3d0401e094400c07241d040030002c4424080d1401642c11411242c001070361000b00c1e00c0b640c00e04540d0000f240440c50304a0340694a50300100441920000f101301c1100c1d6000905001c00350035420041d440d0141080f1100e000705020b03554240c0042958010340b809114104854414816400c62100c10321503d0b80080c50101c440c94141c40003504c55042540c50b61144481d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 690727482 1250 690726232 690726251
    0x80a030b03071a07140a08041a04031a1f060f0c0201030204030605012918010e0316060e040e0615090c0c070806060a09090203100e100615080f040312 66
    0x412002d40070300700303824000c0014000685621090781102d0001c56510070900d500050004002c074000c41203d0744501802c0c10681403241a0040d00080c04c080c20780d070002440000041951003140c40b40c40030500131081540d04000091192124500000165459482c4002c03c5200e6100025803050b016030b00d0550907401c01440120083c1c8216030001e07101601340000400e40144004040c1d114040f641500c1a04a514408a003594014228132845504c01c50002c40e07015405902c503480c0e0183c008060318400c00300384841c000061550f4002400291043ca80c6806500741032040d48400c41c0c809006065600e09104030120701514003001502400c0c481012900010405041d6000c005a5006a404c07076503c68400550300d500440e070640c41035560301c8001035914003501c00c103120140c014000d48508405511a04e0181400340343c0b00a4601c00d00404c4110204d0505c21003014180e8642c041541d0760070080010500040030340035a040743c0d124014032000035003005020308605070851003c0f600000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 690728732 1250 690727482 690727489
    0x15080312071b020409142a0618030105070201050709050117060d030c08071203061a07021e030a030206010f06052a03070c09020903010e0d02120304020d0804030305031b07080a030b 79
    0xba090002c0d002824544510104002d0a040741150403003082100d4800c4c0910080ea0916803c4841d04018070103441000151400c052006082c03540ea580b13032401e4291480c802027803c54404460050041c2d6403a0305118180750b01001d040000c040900c1c04c042803486200d80303110360355005414240f241208900000c2094050301000b801640c000c0c00140d22404641000400c1c2d051110140000900d0182c020440022003150041d0141c04a50498213199050b4280400354100ca80820103001804040e250580d4080150441852103036001d4002c1d035142c204401000354494002070b00f801803d0000c2112421162955041d010f0401c0d00071750170b010700070100350071072050030b00261069102000104a003585a002132840f4202a8000c00c1003244e050403264403206408294801038202203a21403040f04401d01542e04540001c00300208415a59241950341d80640d1003100428004810000181411990260840c261008082c03400c10141d60f00c00c4a0300c586010341c0141030b80c0700890a01d07603d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 690729982 1250 690728732 690728777
    0x31801180b07030503090c03011413020d05030d090201030e010c0219150203010603020c160b090f03010209120a0b0106080105150d0e01060311121219020a05101508031207 75
    0xc4040c018950b1295141802012540101c6c0c1d190f0403441250b40a10450605218140d5a4442047c20907005e4450b2210188019135000c0c0c10390740012035030b10364000b00e5400e06c01040c4500d1161000620000b09100240507500b18942e03c000e80c0e4906a0030181c03132034012541c1036880800001d0710003892160300e0100c070505482864940d50b03a20202c00483c04940640c000e02460340d60034100c0300180310104c401140c1811602032460118400d02caa4000342c1401131200c1000e11009001505009110002c1900c0c03140189042e04a0b91000000d44140840d9100560140503245810200d81d13041c10045401410040c54600041d440010f00000e41440c03540301400c041d02e4803000380040c0c1e075030703090880e4081018000244985141040301520140000f9101012000c500c0914103015181d081d91b00000560310706907065000e03800210380024400c0c458640d0800481c480050717524540e610002441140c3d8205d44140da104003e03003486881070344d8110b540098580382030402124100814440724 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 690731232 1250 690729982 690729989
    0x1140f0301030b06010813122003031006081614030a06091e15120615080724050901020c0f04060f0303020a1103030a0c1520180303180118 61
    0x44044008410032000440c1e00c4e004d50003da8500c8101d8030390580780300c03118002c020b000f0040c400c0d40140c07808071400389002d401902c000c2c3e80311614010755401920304552003100e0348030b64118a03400030300c003141e042025a03400c980103040480350326038403030001f070b2107460705901b13032000d5400100000f0780404060300041c000e0103105c4414000080303904406030f110104000006029820705400d401d007d20511480000ca80044d41c920b034400d0055101d0000804003041c0c000300000c0159004107841c80200304102c000c2001440b00ca8030000c0b00e200d82034115920004090421400308000c0c105030303034000340c0c488039400c08560004410030120300040052241c0e034003007010701202510000905030003160007402c0078000d401e4021b035030030320701d00301626849450701e030802250004d84440080f841c94030b50f40c4072349005602c001555100a0030340042042c140040713115442c1000a02030580c1c005211079244692040c0d0045041c445445200f80c1c00c00003881d24541041f51508601d4500501585060000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 690732482 1250 690731232 690731257
    0xa081c060b032208180f12120706020f1201150318060f0605030d050a09080d080c03041104021602032509020a020a140609070b0c0304060e011e020309100c050c0114 72
    0x8075203511011041702d4410724401c602c100f00006100a290520f4103c0403c0030744905d001d00400156050404000d0700043c000f0785415600b40044405084a41c0082005250321803507036466614008000003010b03080c1d1001e00406080c86e13001c083d001c400c00550450035a0108022843d15070524803000185400e074445070341481030070300300302080d5000310081560b0501c03a6580d4160588511010303580d400315905100014480d600099140d1261802850f0400d103d42e100c100e100ca2440001001e0381c0040201c01517107625113450004619082001c010030780142041c6a00314440c041d200803180f1603911807141095000980e1200365842408071400310341d0310030001142c0400c40c210446d503400c8116140340e51446020000310b1010f403a80300307480490341580c0044d480e1506045c002c0b100308401c40d44d50741c1800032282d0280c99058402c0c0c00748509000944c01141c840e080e00003041400785584080c50140682060318101080010410f50011030003801d0043c142003100902c11100d1060140c01c054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 690733732 1250 690732482 690732487
    0x80d050f07030e15070c0c090501030c090e0105090a140f0118060b090108030702130603021003140a0903050d0c0e13060602060f15120705030a081c060b032208 70
    0x844608003925602444030360b942000802c0300c88001503038032030101e11601100c00e00e40c0c00040180d4440e0b22207081c0b071482800c01c41c11056072400000244c450a82085600c1100b0f02e00070303c813035082481014003000407200207010b00e0400903110b680390416070340098900c03040b55006510f840f0040140405440d02c1100070805e080151160403510046120101ea01c45d007040704c520f215150865003681030302c9288019510f05240350307080100d40c1140c81811103602d915454000096070b00d800d000090190030707881c0800c40d842c8201c12101ca0341c0703005009094440c82d1440c0c401c042680803064403c110a52000040c3e4810202e600f030391407070814141d03540d100c9001c07841c1e05c0c0c01200d00d4100394201c1e4481d0b02111000c0c2c42c6c4000132004040b003100c10003240425541c035910507140070115041d007140c0da841540c000c503881d90302007810494814801d0f80c0400000491800e440410701c0203610b800000501000814100038142510740f0001e001c05031440d200303200802860100348201582160301407060359 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 690734982 1250 690733732 690733741
    0x4030b1f1d090d0201020405010212160f05030703090503011104090f0e06010611071211090a140a29100f020f0a03081608060a21021305040b0108030c0303060d080d05 73
    0xc0074100d80303007851402103520b082c00c0180140240c50079100d0503005400001418081500150001150107000000c0b10300428086620740445860450203000a03580d00e140b83d04002d85445001d50007103000e40c0c07400750115011341407501601e003a00d400380030116005500e0141440607040d030558444290084600011b00302d60001d0054a039941c49100351404241d40754807560900c0c02e08803000e000c0c41070070003180d9090b144c080c044035803280e080800003807403004800c0117880101c0100c60b0313011134039a13a00e43d918031403a4a075841400751420590b02401e02080b04041511450b901c00070707100b031081031000e1550f194020f01c2103100000b107050469801c01c4e03a0b800c0041080000380d03050810340c43c0440e83e02c800d0304d10a01c00117200f010b016016104080c41d001e00c4582d41014400903805e001905005a80160741c2c021040410064850000c111810242440101c950f4103a00201d03050784208441070803600b000c802d50f5441542102d08007021100e505000015104180406000318a00000c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 690736232 1250 690734982 690735029
    0xf060e0c0408061005031c0513140307091b0503070c0b0f0a14041a06031207080702040e0a0302060411011101050412030e030a05030103060f020c070e0405100204030b1f 74
    0xd00445074a00111005504c0e120b208011041d00c0340981074040e04000048001078100c4040c01c03600d11032a2901e40e00d4910308003d940c101c440c850700200510852090a0021450f003004000060100403401300000801c07070002d400401d52001c0303c02c0034064040001034225004d20705403180540c108111240600d894942c041a589041710000c041901c0c20b00180c00c0011008030a503c16940085000d40b02c1111541600480300c004100a506116840000c2403012072071003d407020b80e1248642580750a207a1040000b5203046400e5801e081e801134640c980440e500080a640142d0807261080b81100c10400480300d0b07040500100c0341540c20807081c4001c2040d04c43c0801025145603504100d02040e80264548074440d03080e0b0040003600900050012900a03440451810400301c401171800d00041071450030005141d0003089044180d00400007805400e12400805240d111070841c94a03046a07103414150f60007906000c03d002110020903e05003000710303000050903241c2d480c002440e0740340020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 690737482 1250 690736232 690736237
    0x60319060510151b060f090507081011040e0a020403021c1709010c0b090a0c0b03070f050306150d110408160e0106021c031b05090f0904150f060e0c 65
    0x11103060564000700080d440b83c0007540081c1018a9611105804c030705140c0c042005000310f00640b0107941c0c4500160403007043d4415400da20340b040001d01801480c111405050012100c95403103298181501c10461820140440e415038000e500800c0b15030b154002800c00a0156820082d0044038100421a0f038115100c8006525880749140302544221003c001c58035002d811700050204140c42c8950780020380b1314089641c0810054201c422460550311041901040b99111000d1460000144200302e50711104580002e03029013882455810014081041d202030340503040c2491a021440e8090705419402518413400301e04e605545032605d47c0700d03d80d100c071075603503000c50128500c084c0040d090b40c20004141c1216507540103800c10409401c0000111408500d20508150b40c811060f48484200300b02c20440624566031030b9201c2681700300780a50010381101d95403007410f118080200042001c05101e5282c20748000110340306548031030388000b0742030703e4001102c1c076050301d0b04200c40103004101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 690738732 1250 690737482 690737491
    0x3121406010f09180b0405100b030c090d020306013c090b03030702040e0714040b030307240c030b01120b03060a0c030216080706050f010e04020108071106090f0706110c090603190605 80
    0x6c1c00c0200d81c03a04c070101e04040c503013031180c13450050003032000403014840c4030082c015000010b4140d44c000809036000904001003600306c100580481c071200c860b179210b110740c45041d5044004442204440c508202c200d0840340d44503101c801515040c1490064806005131922990b003e001401100c446220080d210042ea010b102c1d184005001d02c08120314050260450200001d40070351300d0060079449041d088aa0181c0c580c04c02020351400239200c0d0f45600c620359401406907400100c0c0c860f6840010803501d00c0083e0b207000d040c02d01c1e428030b40660340804c0260f00300303e50100000d0383c100118001c3d0068098440003003500e408140c0c00800b0710100d0302c0146032442c030a823005c0000350703551000000152004e000301340072820801c0018006501481d403058000d907003418040d9504200d00300013840d00004407103481c40d5030814100012030610030401d140107400c3c182801542c4d0074000140550383e01041205030b01c40d500180101f0215103041c418440e00941c1907035902409922403e00801900d41a103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 690739982 1250 690738732 690738739
    0x816060b03010b0103060e0412020f030708071208060315071416020a0e040b0a0b0316090b010e1e0105030c090603040308240a0909150e0a03121406010f09180b 70
    0x2e0381c0581c3c0c1d0b10900c0368405a8003c0c0201a4039030302c1c0c0792250941010304801700d00543c4141c48400301c0044c4100080c0c01100d200e00742459850b82607203401001c15140410050500006100f84080d40d84d0119111031100c4206481c401107036105e902c11520403d54100400a801c0c0c0002c5210100300048010040035000f80d514008403a511401002340d15000c42d8050500c0c00c80c0700100d965401c00d90013841c4004401021900402083d0100d40c035481440d0b40203441c402c0e80c40080700c02e15600110340864000301192034125010034025604071000d503030800030381003110010000324000001000e9030b0b01d1000203440d05440b8a0145805088043e042d240d00b114644201006030341803010340001110690040c021812252401f00346401500006008440f04501c03e0700a420040d0f0302d00c0740504110303d950003840d007100c1c60f080103015031102041005000d81840d41c0712400c2480e4401041e008042031800890404100c6022980340c40560010024081d1100195a10441c0c0c1d80000c00101400c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 690741232 1250 690739982 690739991
    0xc030c0b041a01170724050c0c091603050901050702060a09030504152c06090d0f0f0c060f0905030616021e0106061418120304080715090609080601050d0816060b0301 73
    0x201c003015044200c01c0c1c0291310340c442146c3c0001c0018884c40c05002e54038a02003c54a61891100001c0c0780310300102d85040002030318100b01111250705001e4150442d0580000300240c0c10324103402502c4000040010310b14a0300d8040c81810580700344200c0d40104400114009901313490a0018240040f80b10641c2000700f0f00c203000e6151001c00102152072000c014122441d12407040b0070701c281400c0c40309040e106205270030344880110b001101d454017980c0c42000c6102e0703060b003441000341c6240c40c002007000820501d054207020315140011055040303072034510b000c4580064001c00303e2400d0365079001d011092002401c0305244480540120041e41d403e6203914070321800240440880c1d000301801d280b003a0303020768810b500c5814100d15030300e1b140000c04240c902c0c158507240e40c0391078018982e002d2601d00c11440c80301480340d54002c8020001e800c5c00d14103010700031b24003022556104010700540384030b4140000140100300fa008200c0300c500000c5140e103c409012418400c00030031056100c5402942407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 690742482 1250 690741232 690741239
    0xe030f060f0c190e0a050607030905191d040203031308010504111806040e010204051008010f1d221211060919060e07050a030c0f060c030c0b041a011707 67
    0x4000079640c0f00002c074514561850000c420841d05107220300d4015802c08260f04010a03d030b2074880003441e0250203074a0705c1c14103034500030922440c0c18408003c000044103408040c00960364090480202c0702030040c0d140302d40d494034000241588208158038602c4c1d0048040011040d506402c1203100380c2c041c2d1811f01d80170741400c06001064600b900d403150134148020005134180351540c024111940500d00046c00c0c6a2544085002c5043c070140000c0440c1001c001004202c0c8000000009400651344458241640e10000a00c080d409056003040340c1c080c940322544615601c0c0d2030441590407050011181d03501c3d16001d00101002c8803160b20700c2c00707001d001079089100080d1104862046960341d52040c2d015846050042482525881407400b44400c00035540d6152224440a54080c4087e0400c0914040300740802c2030032507001d00280141001a41c01013034000c8200c4034003941121202615584070304d00f849001010300301c4000d003041c0f00c0d000411744400541d640032460380d8440c00c943c003c42e00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 690743732 1250 690742482 690742501
    0x8070e0421020c03160504050105030c060702010507080903011104090c0f02061603020c031b19020901030209040f0c180f060f171c020a020a0b03150609010e030f060f 73
    0x220380c0030705100c940014000340c010400071164140703541c0b8816558000e007408002410b2404561411280c90324164040c041c80c5014031885005140c114010704401e807543c0d0100c0c01d44d000d10040a0b06000c4080760f04d005200d0100200c484505006000300050080c0d02c00c0320801e03802c41d00403d0740040c80d0103c0c1c1d641c86400b80c843c02400071400d4005004540c0d030403011041d030780003940085042623000e1110311031000c0101b015255400080c01548400c03501c422200b450b201c01190142c44403280690032038056110710720068156134041d680403007540e403242000880c1b110f450b0390041c49240071110000e00030519008920400051103000e0003200d00e00c0100c0340990303206000304003d0700321060041061011541400007036040b114103488462850740304c0042811728840d070360301c0517821980710701c41189481c141481c0545242da00e59421801d0001a98040800640d03141e40190800142c507501e51303024906050007220700a08a0740e80750762100c0c0c2c25458403415611105014000c1003c20407450 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 690744982 1250 690743732 690743759
    0x3060105070f060f1802130f0b13061a070b06010e040e0613031e021902011b0807060c05120a0906060f030f020f12300c0d090f05010207050f130203100807 68
    0x58004140500d0400f5a0b0780c1e4200610858030900b800d02da90709c0201c861520340103185030380031144050008031340d85451004d10011500394406070004504200540009030081d0304560003150a10b4221440010280410000c10348104102d00a01c40c5504100c04c0b0076115181001c854071a9581250035603405005c00c504002102903500580c1206108541a581c070100e00348050303005140c00c6120865640d0a0600c8445090701500d18a9000401e034092200078052540c1c0318403245400c501c1d0400e81c41c41801004006040c2c28201c5440c1c4080009020203a00000054800e41008110710707640d91803d00c8850b140003030124000d4140441c00c041e54a8800d00034428628240080d10582504101c82c20f13420b0014144035083c0641c0c0c2c2c60084a80400310090075940080c2e0b4010700403e50b1040014140e00550341c0060304100f5201c1d02480586d13400f0821100b00d0b81d065402c015410000c60004071440fa00d5001003900700e01c0801007090400c0490b83e01011076900105451800d62622030402510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 690746232 1250 690744982 690745031
    0xb0c070b0a091406070b01081e0a0b0705070507030c0609090b0d0c06051c1103091c02100f02041205010204240503040b0901140a0e15061503060105070f060f 69
    0xd42001007080f038003501d4422412800e40042041e0728003001540c9014500c0000e820946072a0710042242c203203500c06001004034003106800400d42c1f51883d503251039160800070000d408001010920000301b10041212002460b40700042c58255500c1e4500203118038518440c520110341070070801e51507400e0151407444541e81148482d030352281400000d494560101c607021500c001500d0145000990520581002d0f00307103595003554905200000c1e5141c0b002d44004124003100d180c00c034030002c42d000100e2070502406402c8c04940a402400204020b00940d840045025a0341c01c21804000043d8010401d076241c01c05605030004100c000d0741c0308003108003840d070045081000854040b6004602140d4060b040d00008514010b26034100c51803400d06039210306507103481e4840214142e10030300448081200e003099250141c600b040028010802032a40c0074154040000469416480b50044440f041d80000000078882101d01d440001400c8000c103c540c407074038102e45403007581500210b06102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 690747482 1250 690746232 690746237
    0x509010e0a03240501150507020a180204140f090403080a061d091618021608070c14010e0306190b0307030f0506130317090102040f03080c06070318141203010b0c070b0a 74
    0x98650b0440c05461548c0106801da0340301c002c51400103075204984100c03000010b0803141c05a2510324041a0480b0032420901c1e09115403141c00341412941c844440c1799520680514103002252140078103880244401d400100000c540c0c840c09940b46d1071070ba041240105850400c580301c041000b86206a107170b07464014a0803840f6035410040c1c1501d4640c002e4009000b100c1c3c1d0f4540391400c541c1c6c81003810351003040200c400880504042003013006811404003040d00c2801c000040c010000002522910300400d6282c40b00c0e50003031400074100f19948140088440a4102e40103943c89080000b0a1040501c0441c1c1c107102c0c100002da565048074241c21195607058407070080c07103443d480144086490042a0f20840e660074880001c02c0010743c4514001036001d02009544d035424028031504000004000034249070030403544040e40448c106c20f50800c590040b00d0103c4511610f95614101101801181c26059010001040d00344c0d0b0701009106981050f800c4410155442000c2c501a000b841750001c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 690748732 1250 690747482 690747509
    0x712111203070917010b041a150c011803021c0e010f051c0606050903060c0406080f04030e1005030601110a050709020f0d090f020a0b030c0a0509010e0a03240501 71
    0x18a00e40c410080c5030048200e007000c15099031525104410403010180890340da1303448100309032140c1001c0c425031021000500d0718244845418001c50f41c0c0d4030304442c4e4221071880c000ba590b4194442036100b00d186030003000c41c9901490450800942e03801250a003447c02941d032105483e111030043c190405080c806071240c420913540c187c010707100c41d00b00e85160310f10800c1480d1201c038400170f50311850014100c01e8075265103c49400b814149040700040c145680b01c07404000600600760042020b90703101c071341d05901c40b80c1039849250480d401e0440b1440c494102d1203906424100f50380282c059441000f0aa89541640c04486801c03940c825101401504d10b030070480c018401c03480960004c042000007090b8040c1703082c0000780030034101c0f00980002d83d002c1025081803021071502d425182c1c01440c041c40c0f81e50139800c0c0790b050b6407000d20694003014140500002c3c8600c00303900540c0107080e030b100300425819000b5035a080c210108501c40b8811100389006424840420103148185810703100800d04104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 690749982 1250 690748732 690748753
    0xb06130f090e07050607031e0807200604020f03100507030501050906030d080a2705030703020111190c02180f0f0c070f02150f0d060e070c0f0201141b03071211 70
    0x1e4144c2c0261007e500300603184800c2c965082d081c401d14140400c080e0349006451800b800e0050031410418400403560301d040c2d6a00844440010b0b18a03001070701124801c082d48480400070746005041e9002c162440e05240400204580541c0020304036101650b02800d1907851004264481003a81d0a0784085203406000c80c0060300664003601400d690094404510345008640c0d1502200c6600101c035a0783c0f0001d544410141d0a0168070300130080c606c031042c106240540c03040c04440888962008000d00b00030014155036610489481d00607040c00c2c64001c6003000b202c404c84e102d00403038041160380c00c1840464041300c20202110000354005000d0389044205608006003c80b0035a1506546501808100b81d0b000e00030004110201305500009030051500903120b1020304020907840c140241c1070091000b00b041c904002031a59824a044217005445142440041c0690311500d1003c06600e0f9141008020000003001214091004030303119510a500803511074550000b04a0140c0098000c1c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 690751232 1250 690749982 690749989
    0x1502160f1104060305100f09020d140102280801050102032511040c08100f1505090a03050706020304140402030c16110303190e030604030912060b06130f090e0705 71
    0x4840380e071290081c4a40d15101400003002d0310715a070002d50342c0e90400c00d00039401c40000d111f0310b80d20951540c0148599040e540000b0300d2548070f5003010f010082d03516805030883d0b000394121103440e0160050086144c1c2c41380641d40c80388803c42407401c0400c8a10002103000c1d030000050f82c40c3c4002c104000690031441d0354a4003072209034181700303c0b2070020510382c64040342e589004075003180209580d050458505403240a04076902c6601003130000e91003041c28000074002942481c1180100c0c2032003075561464a000c200903114940c00500140284e0300c01084540d80800108200c9482088014001f40504100802c92000707603800e400c0d80208003d801c2d159042a20f000c0091070003100c014032030241c0000840e04560200045800c3d203c1ca541804110540041e548109000c05030004c10700c52425640c090294200340c01240b404681c0341c402c070010407001e504141000e20300039110984400b01030088200441c120300406640308140300000c2000c40031032240d00c10401000c0c0040600c58640b40c1030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 690752482 1250 690751232 690751253
    0x4030c0f03060e370501020a030e10090314070201021e0303190b06040e1b0c0105070914010822020406090e0616140a05120403020604110a0509013807150216 69
    0x21030072113408440b80f480800c1c3e00380b010b404031000b10707100450a44154a038080c00d18450025089526243c5920400401d0780458114201c0b044a21015a1840d4500050380b4040d09000d0200808030f8070040380d0603a180100280d1f00959000448a4100c01c80e406904140c55104400d80c1d00080180000c10001c1011640075401c102e25954504520aa841e4013000e503034409840c40209030b4441e1300f404481c6520075500170041c020b02c600542e54014000000b080444060b0103e002c100354081d5040b07410040521000c507190340100204651682c50489070050007072680100d100b80540d130300040c241102d42d2415810b00d9043d80d01c545500122071174034092600450070680030000b061244514000106440e540203038040d8004024a18042c6801002c001070211014010f200c0c0780010003c0e0349480000c641076400702407a04650101c021840003024280300050030403d9120741015407054141002001c0d054020100f503601b283c83c1e1400002a440351542d040e2254074004200300200e10003804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 690753732 1250 690752482 690752563
    0x905010c021309060b19050108280b0f04020a020f0c03160303082203030f2004060e030f0a0c080d0f090504050709090e011a0a151404030c0f03060e 65
    0x42c00610040c4e41170110b80c0042c918031680200840c041400d005a6800c0140385900ca031900755071041401d9600307070903010200e800161800d01c2d0348030103125289664009081d4140c42004e8030854558042d508000d5442c02000550080c50290035400781c402c4c10046a1100b5502c00005205080c51070f503503080750f035104010705c000021201403014100f41060301042e003d05600a40c0c000c00c04a440340c07840b80032224514418003c102c444c6421a21400c580004c2e0750448030b09081000c084044200820704000719415441c41d24003441e010352040102c01010340b41941c01c280212005100508015186a015068140081070000302c2c100720303d21f0a500b00c3c6034441c0651805c40c24566440554800f994680d00c642030300c0c0c1e5181d00b400003113148004e8001314894000c40d16100e581d441c000090303501092164054040011000260001d82a4102110011640312040c44030881e50341ea804000c0000d5800f04640440c141441a0f19030500016422860380307982c0080310102001c6070310f01c0003507012101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 690754982 1250 690753732 690753743
    0x50a02010b06030414010b0102070501020c060a03091a040308090d1b020d02040509031e2118030f040e06060c060105090a150f060e1002190f0f050c010905010c021309 73
    0x4403801c6502c40b40060340c016841002020050032010503a242500c9140400e1811076110100401c4140c1c3c0c005a01803519509860203640d411084104030302900340c4a001078001e0428058200318001e00c44450361265010b944c0e20010360310b4881c2c000d03440c0c0c04426000e200140c050040c240c580f1501409510000f4802880c05034405180d5000c40d0603241c046071025010380022030004180f52007200121076403c40c1030b400c01d150002c00b1841001081c0c21110291140c0980c00000d81490000c0d8212008032418108032600e030403000c42c224401d0b52042c010044070000107030204841c0d0402c02d0641c1c0c03941902c04040c210b0780e0b0030700051144401000381610482030b2a401c58040030030b0507100400184c001105894402c5003451009061208a100d03114020f41440e501140120b41c0803030140100166400c9800d050700303031402c2076490b5101201d0060103014813001d280c401c2100010301250003240c2a228410040c0e038900056070002a1310401a4014000c0f100d41850b9941c10f90094003145c0c40f50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 690756232 1250 690754982 690754991
    0x1302040e0c03160311180a32040203010b0d0314030a0204170601080c010905090a0f2702030d050408030f09030a02090106050a110102030106020a0230031308010b1507030e1507150507080601050a0201 87
    0x148a00d44600e0652000208090142409e00083d42420300030034070303508030a980050020800d942c008100e164101110703480c051000c004200100300c103404480084c01d000c2d0032041d80e034058103800c0f40c4401d428415019a4407075000e03803c009500800d5454100c810050601c4d0b401d0b62040b10030b10160a580700c0b1240c031184da881c1205040e2403144141d081c200c01015001c0ca0350821441403501e014600d05162003444418041048149400400c507100c0e181d80300b0559480c2c11b48031001c00e1a100307086900a5112a0030300004c103206078040007500c0d07400181e48c0ca800e0902c1000035814200c0c4428003030301e401600b10320303141400340c2000c84129502c080890300c1c0500c0074000d000b500c080c101c0c00c101a0704941d000050511099039a003010b1001411120000708482c81038000003603507260710080607408000001c180d00040c0741c00ba840e0003425200282241005030300b00850071040d40d02400c0101c401401c44810a4040380051140d2486104140c844403030a884590041d00c4c1c2c1e400c106001c408644d06c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 690757482 1250 690756232 690756281
    0xd0c02010605011d010e1c111903021509060a0e1c03020c010e1206162006070c140d0203040f0e010302060901031509020409021b061302040e0c03160311180a 69
    0x500e15052602e811089010b43c5400700c80c40c1001c0e580348a090080d2150309403407408034041d02c9c1100e080044990444112040b840d0b030307002d140d22900030060615840f280200303680c0071641d0041c3c600304003000100d4050012082c000f5110842d0140f841c40900141d015032901c1c20694040c0c0001039844c08000c4c15442c0c446503500c082c624001e002c464071011103480300d100c0305045400107143e9a251000b0b05603000100300900c041c41d92110002e1500d010095110b042401740480e22003402070315540381c401e03900852800c00000c0c0d0350782c2c4a480750303000c1c085131020700180741100c101409043c1d03540240380390300c1c04412000446c0a0100c100486040d8413804400150020051000b0f00041010f46405a218000940241c0d00492100561091900401e0070018131400310f03114043d6441e41100c0006045036074842a81c07804190445071394240c0708541101002c0d6503e4203105086901c1030302d02c2c0c1c14540f0082d092205040c0c81740c542d6a88224541c0104d40321810303a4200b841001020a025003400c1c15 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 690758732 1250 690757482 690757489
    0xd0b0f0102150c2a0f010c08010b0a030915022b06081b0609060301080c0109090b10200718050a0e030a11120d140601050412020f03150c0d0c02010605011d010e 70
    0x104807454040d03a1180c00e10380f886641c20b0007501d1407e40720782825800b0350300d018800c0301c0511444140e24105a501d0404004004140c58070814901c0c800741d086440d0051001c1d201d441c0d200401201d600d4007181a8547e00042d4103005e003200b940e004e440502022015041c81c83d0408007040c640d10341c4000140808400d548030400078500804a20340201b400302044d0300054400c0c00300340c000c58022030034487c84004503160702c8030320a686800c92501003004a5904c00890300d40c1d2134400d0448090060310000680c04000542d011202c2c2d614042c10420b030340750300400800300c90310400c0c0c0c8100c5810070301928007150b000304540c01000c03401c070064500c04155903c5101883d4010003c42d00d500c1d546075402e0001c100c4400300568004020f08000c4c4c03030682403910b01c100c038442e020b074002e2203815049914442501d06000b41d44d03c4202d001c50421460030300120300d42564008a80d1407256915261121710b1780c82c41405200100c0f44107841d50301c0894000b0760030740b2091070b81c0b204150510000341003441c000e84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 690759982 1250 690758732 690758797
    0x5120c0f1201090c180b0d0f0219140306131713080105010e0420011b0809131b0c020105030106121b020304050103060b031b0c0a080d0b0f0102150c 65
    0x788261030a581301810462041c001ca40c1c52400800c0311441c01458031803d80b034007049241c901e50410b01d07203d180e030150710004502420511020018038a12940060026411651300a00e04001c40c140d034010344d22000c0c02220200960700280c103007a9140361b1222404190001400c60140c2035807a500c00917110207602e402c0d107500380d1041011490100c20002030121201d02c0d0070181403006c0c00c08501c180c0031000205841070079405511303031401c00f500e040200034030941200d0584402405480e4808102103114004081c01c80c0c1d00030f008843d0059124003d4486c1c481300b00d6140c0d05071a100d04503420484101c034203083d40a100c608072903545403200e0b82d04078148008080007002e0740c01195560700f000300043c180d03034aa40c000d02d4201e5007032062021184040c005504214220071000c3d031100d1086815500e003440c0300b00f024048482c0050300324064003868200fa6087c081c103071411050b40078030100480c2c5e507810351141d59006c044180d0124113080344150051504015844425020f0004250000c0207007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 690761232 1250 690759982 690760001
    0x150f030a082125050a02011805100e030c19030c0f12030c1107090917030a0515090610030b03250e0c0a0f030c03150e090705120c0f1201 60
    0x4104000020341c2d511203002c8001d03480701521101243d80c2e0900b0b00e5203a45000104190000d010f000306104c810a40700754403030501348c0d010851002d010316442c140390380c07200c80c00210b4145440c10400d03454141d100000807202d41e0907600c401040492048c140b2003400d081c02300300807020020642d69010100d1110221a8070083c01920701825611600c00c014007244c64003c101c0042c40790040000382c401070045204000c46541d0342020070101c8107442c28148140313180d01c100c2801302d00030080c030014070441c1d0300c0f1700d01c01c03038005101085101a4004000000c20203e4030280c3c07180d42c0302c109600240c0303c0c0d001815292006011034000b2454440c07581c003c4d08026854442151020a01b0070040d00450741c0700e80c001c0c1241d480306141c0100e413040104901c480c0d0040c1001c0c0b607104d01284000500c01e0b40076442072400803400400051702c600007880488030070340b0703000d401e44a41c0e030010030360b880c02d00101098880309800401c0d0203031020052022482e50941ea441c1d102c400848100c0e08100c003801000400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 690762482 1250 690761232 690761257
    0x90503030f18071e031407030309060801031101110109060c050d051b070305030907241101110910020705060a0302120f010326091002060915150f030a08 67
    0x200d10705034064641c409401001e40d452800b6440d0795102000340425218180c03107040a09945003808400039044402d015400108020920800040c1009012038004103803442603499400e02c03561148112040a4207000144c411507801482d158698015038195500d1041180081035011803a21b4500455492011800c0406c60000f04124084650320403d0390113240310007d401d54050f103410f0002c840c01100f500405109001000c035052510070805400203081e020f060806c42c4101501400b842d44814840c200801c0d0911040e0119100601410b00c007895401a8581021241020040510f04081c00241907000d0b900007c80c05445541c02442c0103041d50310050b9030f6101c4094807800c0184002c0070104905c1c13807a0300510004400030140810349010340c42d4820100d2403900746154a10600005551202c1c904080c04640d540120345944100d0701081640c0d00380296808041e05c40d0001c0714205055150314101080c80d2a191003401d10081d80030b0121000c00c0160303940c0c0c6125a1180401909 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 690763732 1250 690762482 690762487
    0x3221104060504110307030213030b0c0d1b1d0a0518010f15080a0f06080a0c030b0a2322051c030e0606102f010c230d0b04090503 57
    0x1440c0c10180548401403000f0380d020000401d40d00c2d40d075090390001034a01000c16400165034a00d404181d919600030311703003207080503d1900b002a000609940911855a0340f1820702a100015200030035129044000e0380c0c452032500001603039035040c000070005186600403104003000c00c4030344512170130707000b403080400d58225294141460060400600e611441c03400e1940000030003002c0d400700903c0d8002c0201c030381c04103428034034000a00140c0401c4e004540b2501c9146001003d00a4020710341e01100d020305805640c544490301c441d0284d40045c0d100e000f02281d40c001d102e000110b100e0003550700c0040301750703c005440c0360700301d403250303100300c00401a900303a400641e100d0700280031480004026000ca040411400304015141d58403505c0040074940718000000c15119014095007044168108001c91040015030303011000c2016107480d00710042e958070307049003100703001e002e00343d04a403d080700b41010002c1020312003259003a600044120a1980e280c0344c5a0555071524000c000009100b24061034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 690764982 1250 690763732 690763763
    0x20d0807021c030608010b120a08130b0a050a0e01110a080d020408061009110306090402120c040f0207030207050a1d09070b040e090d0801030224072306010b040311060322 75
    0x3421f503003c10b50614403072030503101c00c4411400001058030b0401c1d030020b4045d0300c8460401d100d0170701000e180d000031f04070301e80050f1303c541c0581c4c090010144100780e51540001560410011513400c160400d200855034001096603000ca0f480743e0103003032601c48140c4094a0710f42c1315030b01203060050943c1c4d8482c00c1240f4681c24000d00700907008480c0a40c600035006421454240001400d55002a02c00b81c0a41001e11011030213400038008490b00800c02742c0180440c0312a0603111000b51702a071026001405181c0c80440c1624105c0b00c280c04403903080e2585004800d07290b1104100e00d101402c2c1c03c1e01440380240010b45078481c0340191000b018440d20380c51080c50706880280c1084280c1d800c450400000200510041c1e4820019801211001e00c4042c10301e081001c0187c614820340c1409090f1144807407203181c0440300501c0300c3e00d82d901882c0a442080c2d03a905030500c40750096000c0141845030154524810741000005141d00c811400700c420b858022404855003094400303442076821024054114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 690766232 1250 690764982 690764999
    0x9041109011d01020316050c030714040f0605030a35030a0b01031b03020d02090402040f03021f0206132f09010b0f0412020d170309010b010807020d0807021c0306 71
    0x1c600d8942c0245070b040103448190000351244190841c400203000700c01c0101d81448410007403050350380f8010307084409068032041040480d8640582c0c0c0f030b20843c02c0c1016000c0440c00d0340a081c0032590007400414140d444c1d940c4200340b034006d0451000d450140a03124038005c500e40030803100703181902110b040c0c3d00d061107401c88042d514800d520605050502060050007121800c821400382d40c9441c00688404071014040060302c1589007580e8094004900804d07000942421442264400c81300e40c042400f220300107245103100c1d01d2855016070810000140c500400d12020201c0350b01c82c00140040074a005c1031044a60050813800e9501801d8200210945c10001d022501424071102094200030310755800111038440c60041d42501e400520501d4219120b188105590903070054a200f00310740445410090790700b0440e00e03e1669800c04c0d46000703030355000b5400d0f01d00031505503014243c00084501e06441e58000036094400310b00c20102c503040043d115080c040c0607400d41d0b07600443d50600d800030a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 690767482 1250 690766232 690766247
    0x90e0c091519060e120337020109080d05040309050d0b060103050f0115050d021b0d030c050403150b0d06051e09150f07180e1e0408031302060904110901 67
    0x602280e09014902030041d1904544184135811003200d81101d055500c250b864114022068042141040d004c400400414615030b00f40f01502e44441407010260b407440101e007a52040c440203800c1040030400b002c22504103801c0203034410f002e810039072850703a503074000f1a02c58660040203548518424003071000303d40c0c1c580561074100400b400a0501c55040072041050342c101b01000909101c0001203c152210881e0181e420500d095100c00c14400100424103444030501c04034040044d02d0b0a024803d1680154192016a034111500380040c18072160f250005100032504161300220040400340050000e0144d42d2040c4d0480c03091501d88003240105041144018148207155000212a0510094071075000c5901021280c0c1d549416154640c05032400c4506210303410542401d2640401c01580011383c10b4028141103041c7c080c05110fa0789006000030050714000c20800080008c00c80c4401c2890142004600040056141514400000d812100000100c2680f10070120314102c0c151b03000307032070b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 690768732 1250 690767482 690767509
    0xb01020606010e04181202070f06030608100e25090f020f160812091606030209090f10120606140628050c1603021504030507090e0c0915 60
    0xa2100d801d115002a2190040c0c41020340120745d200044084079081a400d11758043d00922645094400503500031b49400044c0925664403d1340d140000f0118031070b226040c00c491200300900040440045140003820011155402d54841c0960740f141464101d4210106040a544000012440c10003a03100751071906d2004d00d0103a00c10b1001044030a1070300101c07402039038564141520700c0514035011450f4066241400341c021a2041003140c104000200035000841c3c500380d141c00a50344041c21410791080c1210b054000180d240440d6094688094064100d0354041c05544020340711110104d1628005a0036999030303071900c404204003232440c08a000c0354541652035921300100d408803502405e000300709010b940200b880031121503c1c4a04103a41e0411818020780310b429285c4414520420030501040c0c0c844d5014940407069614681c048900301c1c0e41c050094100d047c40e10342c90800400c0c04501c0740c640b90040702503410055481c80c0e040c9210702003050006045820381000e11070414002c0380c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 690769982 1250 690768732 690768737
    0x90b060a03080909041a070806190b120703060b0c011407030506030307110105090a03030809070501030501080c090408120403080a050a0513020418061b140301051f020705130e010b01 80
    0x304284041015a011140d030300400f921814030030f4684d0b24003010380210310311403049aa41414140020a035000d214140514002c0b9605009541400200d1010704002d11030b0a800080030003601c0034441d02034003681d51140207805d000803000c0c0d5a409690303056000c032016240507503480d000c800d00629010140c81e08038280d45410070840c54a0004207589210300000580308484e0100c04441030380c0300701c3c1120040c3c03402611a01b001d650303030328020346999400d4821049c00d004030300c0041000d500c40d11499040b20340800081500c40ca07002c0500c4103000b4090820b44a80d441044034000b082a03d404503405107200c1d035989146072419000a500701c540107400703081450308100a110084440e103044c05a1280c044a001032000701c1d070803040500101c1020018030050070010709a054560003c1c40300600d24464440301008107107003d40380c100e03200074003440381d0015440404215102e00480b444810860500460300403584510025015110044100e8800c0341c0b1100603041c4200207015003412842c0a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 690771232 1250 690769982 690769999
    0x6180103060e070903230c2202070b0703051b180a0b0f0a09080106080d0518040903020607030b0301270c03140c0a080a050a0605060402040b07081b1204121103010f090b06 75
    0x19a0341b1078488220804241c41001c01030280801406000c10030844000221011907803614540707006c0302d61510454901020038541000200202901d6505c0d90030810b42c064400d00e0038903400d15000c0010600707809e803500320801000106507111403800070808180d5050400d6109c0303102950050008a0681049a540c0d0400108100c8078030700155403035611100741050b603280e140ca18180d0400081d400c0d05140c0c03180c00d00e0003900501d6000b151840c02403480381d0f018001c00110f80289030a0300c2c0d161401c203100400104a403c88500d0b0002c01c40740052140c0e00c080501c6950f500c503c5102d4000b02c0001030300340c00c5111a5605443c2c00030000d80103000f003101600c5c0a64048d210181c60b104824000307014280c071940010744075034549e811a40036000b504a450345032645401c004400750080702c80c50b585a81c4041810540240004d8248400d0f417480c100540b8242c03c00b40c1f00314501c3c06088080b146111300c941200400d41e0301f801440c080e60f0b4030040000702a502401c1403800d0441c0a040a03000300c221 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 690772482 1250 690771232 690771293
    0x9090a0f060503030c06190902040f2009130e0a1b0f05010918090201020304050307260114070e06040509040b070201050109050c0f0f09030a0c0815010506180103060e070903 76
    0x2050547e800070305100302c2840404261080000785c01d9100d4002c4d4042d141000740400c003840d80c0e000404400301aa801c0a1200034880f259450f8440d102a4551152600b810042901425085004e154860741d0a170b13140b00c2c64039a922007c0010801c04520707105044001480f0300320a04401c080145802d1804034541480d0600301d401c8422110144807038240c41d43c0e210420b5900030811900148806811941011364030481100540e0492500b82021400700c00820180c00c01405881802c1c20220035041c01070b241c540c070035503804d0840e001142c1c200708180400616603940d144402c2c403450061039451080d1070201d4000b03003142e2058111296041c548400d22001e6030354030081e1001402041d0718640d0f12009020703900f2085c0100324401e035151140e090f0800070001c401c08841c003280d07181d6080394010004a0102104c4000074090a50000b400303000c6140510750743c2050424020741810002082502c4054801115008075031201c0880d100203405c20811400300340c0b0805a07005d015001c2d201591 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 690773732 1250 690772482 690772507
    0x81c0206040b071d03030a0315091407080406230a0e2802010201270213020304081206060903010c08160305040215030405120301120b0106050307210209090a0f06050303 74
    0xc0107401e040070401010740580716494000141345000c18001d044070346580091500402410008004600480ca40d100c0001c20444070302825900745007010301101d40d41d440303420803544514001c0c001d80780b8949414214440c032401072045c80c1180c0e21102840607515110031120140c400c402c0309903800e54403154414070b407080725121040d408511001c450140070120f00040b030241c490b0300e0700c100344200c201d0f0107640c110b00748810200d06280b0a882d4a000100700741203100480c04100e6000e0241d100400050749007548680b0050744c401030081900d401c01200c080442d085030644600c1502144024050140b45135003070140b41c0f44040760340b0b828401c900d0a41c0c04915070b141503180700c0c42c2040010000c203040040c00e1041050001001d25a40e4076581d4480301c01144814482098400c4e01e903000002c40c000c2d20070801c0740d20480d41c075101d480700a03803074040260328240014103441c4559824845141030b50342d0694210b00900180c4c50102c1c0e502800803103101143c43300da01803480b0703500821440e494440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 690774982 1250 690773732 690773753
    0x10e160e0303130905070f0c0b160519030b120a0c03060504030207030f0c1d0c0304030e06090a0308071209050d1401140c0a0806010e0d0b09070f081c020604 69
    0xa498803069a124040101c1d00d076009102e8600d5030800040800b10b0001e10300d0344150300ca02220744d141607141200c600155074a9215500c06410301d13003800f00040a00e15180c4502c11850101e1400620300b181d5680410565503050100000203912400c044c1d01c01c0c9800c1d0081d4445800100251041d0701e140d5030355491500d11407000402c059200c4001a091600901007035004580012449545042510b0414030300300c50b90268181e186020b0a2602000080703124091003128032001092075501c0d2510300795081209050200d87c480e6003003020341c40d95103410110300000c1d032043c14419160a440d24154a5420850400c002084811002001503a890300c0411041c82e40000b2940300082501c9000d0b03024164034503403000304042100600045568400040c94400169980e0450729100d400046800a200d282050f50104611270488042007803801810b4000307142c07a085580e020380e620111000e00015510440c010741000030003e446115803890419451013074406400c031407510303640c0c1801e40c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 690776232 1250 690774982 690775021
    0x20a0209041a0c0a08070c0c1206110a030609060e060f01080a111206040b040b151c0c0203090108090c09013011120604050a0b0c1e07020108010e 64
    0x4540100100e401d00440365004410030346080e00d00c403039920f4030b08881001903010305521000501243c0c0010800c9201d00b864a000641c012500b01030710346001c40d0b0108140245d4810342e001e81e03459800300b0400c20244000c00850030903460120702daa10340302000084400c603600c240c4002c0c1c01981040059522000c1300310320200c090810010f191180d070144802822040a00e80440d2000101060064440d5904900c2003800700d42c1805404c3c5818103100c02d6808d00f01030702d40c00ca8010740c80102c0c480d201402914100d031288803103c0400c3c0f280d07078814040d179902d203410802507000020700c07048550b40128030b2071340040210300421741004130070082900800140300e0740307a0503a0001241e000c0450148407500e58107010003080506070a2074101503920000507402c9910400c101034128500c9507010502d87d20498000014048081c50303130303c941c010b03200003d00c00d090f811000c07c0384c01c592403020500c268880840c181c6c001e0320346500344005088243c5c10b82043c8070001c108010015003031004080030840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 690777482 1250 690776232 690776239
    0xa15090f260a0b070302030628030305090f03070e011e0b09060913020d0608060907080a080703021c0201091e0503270604080f070504020a2a080a020d0915020a02 71
    0x44a84090042c10300c018404014a0000c041c02400307081a81a0055070082e1011a6401030325074007400003190007030758107009001d09004107074100003007401000540b4103107d01414085880b013400c400203050a00303c0c0c00c41d2404032600d80051051401c2529100c055642860144010904104000f000c5009419086129500004102404c0c1e1aa1015400b820502e40802c0d52a80c0f03484000c240078103101d008284003403141400141e20144005890b10447e1106070140c618815261140880b0f80e1041c2d00640541c4607001200036491589001d4071100a21603000080352650342c500b69500c501d64101c200307545c6140c0f0300394070040340c800b00c02c95211100364a002c40700301000b000315401200000c041540c0c01100420005000100480c00c0b900304a4000142d440c1c10ba00c030301c03c200c00c90194030700e420001404880595619a550303071800c0c0001004500d400ca050941d90b65040c450745c040781c2401e0050b040380e07861408098112009001400515a813080154803103d0700940c1c9a103d0b01003c0c0c803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 690778732 1250 690777482 690777539
    0x50d17010e19050c09040b09070906110102090303030f040309050306070806120c06030108070e090703080313050c100c110d03080a1a0d060618050603030708180a15090f 74
    0x101d07081d0540318055205414106000c03e2070304c50303020090790b0041c801c00f80c001c034109044400c003454403645451085200e038603a51903c50804c2e0b02161039a031400b5902245640c20041c5803003540d01000958482e54205080003920314103403a00815039500e55021a000381c0c000814000840c1c0c202d0a6503070301c500140c4d00c50000c0d06c0860340c411b250400070b02c0c285070405400800402c03200300c0402c2e5142074985141e40c6155989803004842d03500c62061001174806042030020600c070720050354403580d1650003401100c14050904001407130b02c840c403e09000100343d065040c40100303c1c203100785240d01d034821240c0081c10b44031500c0c040e01c4060014141000c056644082d44159034811421071800000540861280c0c601850280014000c500031780259100d200b0210120100c0303400b95a12414014001e182440107607a146002500500c040d001100030400f034003540b0f43c481d85000303c006c1181c103242420800e500000504169041e400248290142c4c690030310491146a50b070fa159513148400c3c07101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 690779982 1250 690778732 690778741
    0x50f040f020d0e0d09080318010c05120d02070c0501030b130b120f0708060f0108071e05040f050402241204020a1a19050a0c0f020a0506070f050d17010e 67
    0x38418420768880312440e04000d02a0f03900e0001d1861925a81504c1d010086070300d401c80203550380642d082c4100100e02181e07140b4055442903150b0345447c5d1040c011a10f038003d103000011b045030494010600820703400300d0068140440c03900f440340200001e0078100990b110300d8000c40d00301100f1700220305030320f80c80d018a00290f4031000356440c40b00e2a91415203000d0480c1012850310760509200b03c1c003041c882c2c50040341790052001c0f03841d8100c0b8500c0008103211842c01800c40e41c0d006038003000c1c0d01da0001115001500362114000c507003603843d00740d00000e0146854070400202075140500d015400180ea000400074030703040c2e0106c5100d00b070032107a4080199070f6480080da1034041074001c0721204010610017118010684042c05d6035a050280100c2c03d500c00101c01c5405004507110200050400b90300c40c03011036091460f4a95444c0064001000301e5280d00c0407400d958059481101e104202e03000220600c90b00340b2000e410a16a440d04242c854540458241d02c1c42040c012040401c0e101400714 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 690781232 1250 690779982 690780011
    0x4111801290a0206060d020a0f0602011e0b03030d1e05090f0d02011109061602030a0f0614060a0e10090c23030c0906030702010e150906060d05100f0603050304121704050f04 76
    0xd030014000c1c1d0340030302700550701e41000a0181000c41459248401c40e40401305600007117010303080c020b00e0007400071401c1503844500d18000d4803080918020311100494000799003811801940d1240064a0041c00c40520402c101071400082000e41000c42e4546000e01450306610f00848aa64030116090358031642c0c4007410b541100c507021402503040c03060300301031800c212586460405445c0244420403046d03e10603118000d84104480030350740f0000003041403008a090743c4071150004081204c0c00403483e110400399040324100112070010590740500011100c201252808a204007120882d0550a0030004c02e0018000c1800b100e215003800f00010f07079514801d40c81034100c0354460046522404509040c984460810f031907001c100c1c003503e00064030307a0901c8103100c0025648800180a059104a0003100a09640040b041c00c141c4074100000858001c0021f030016100442d040321741044140380504141034040b2034644a10014481009103035514a20700224410644003c04c80b11500141c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 690782482 1250 690781232 690781249
    0x1e0c070201020309090a0b030f01090512071e03090f080a020a121a01120c0501050307091a092106091f0203070309140a020102160e04111801290a0206060d02 69
    0x1880c0d0440ea46108000081c500c0387c20450703105c03c1c10b4080e56400c98100c8000c1d42070710190200505203500005000105500e604001c140640c046c9001940310044408402c010260501040c3d000400402050003100c101d0f030701c0d900003403410b44001d084001503a40410340240c80d070321981c0302444d02102d8003018005a01c09404140074255110602d81d82c680c0b402c510321900316a01554143d110080116195020b5000c99000d05400d40754400010314000306c2e86c20b000710456120780717082001d015a12841d1220088c451110707903c110300401d0107182c801200c2c03800000409040070350303224000e00044442c190540c405c01140d0f102c00584e584d40d417a00141c1c043c1056a000a003050381880c0e40319401c0402189400042d4401d078291030780300d8001100151550002c0c0907084468100001050000c0d48903010181306800203000c02c00c2030716282c9501c0c0800c1200f6449464541c47c8101c1d0070403000c12840200380c4580311080418200450503038001d5480b034006008501a21051032514255681c240c030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 690783732 1250 690782482 690782497
    0x3040c050a06050a030b010306051c05120c0c150901080a02090301110d05040605010b130522020c1f050c120a0905101505030a110603070c05011a0102061e0c0702010203 74
    0x111001c1c007541c41600401d01e500c07400a60b00000e1070025515015846801488211345005189116035440c11400032000c6164640c00c4907244142e11079507000400320800742284044079030282110500c40e000740b14989204100128201500300450556680c1004065030080394144005894002100219005180d800780c1c0c00d92405010600300c005100700d80281d4480c078031680c018006642d2b91000103415000300e814005039101125020b02030750900b04050040101d004c9270100f0700540b0740d03100303108aa0040425040b5030304501d00300040503106105422015107034030020000c0b071602d0701c201c0203a40503d80342101601641000f1440341041c54000e6540c2c02e4215040e107462041200143d401403505c1a041040d0300040200040e141c5001304558484e281c020501c0704101030909d0400500340d100419860034850848074540100310300344940c0c900580d1901c0040e03400c5603841c001a280000c014007040510a0780c0c00320b0315050b481148042e403c002c0380346a403038955800740700503410740c0038080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 690784982 1250 690783732 690783739
    0x70e070c0b070c0f060c1805060405040216151b020d08041106070606090203091b1302160813091b0c03260f010501180605040302061c020a03141003150203040c05 71
    0x180380c1c401744016503200341c0701e540036625050702c807280058801002c81d40074804e0560280082c0420080750920b80c00411000004d09840d207025081c5030f039180100f00a131044244066500d00301c940412045102103101540f8a00050644001c4480c005008000c0140f009101c00c20300c600602064aa5000f913445a551040050052546031000e40000350402c8401403698480c0c078050440701c0550b92841740145001910f0121070011400c03040000c2d611a68044450002665a180c041441c1102030036815150020480d822850200c2030320580c5c403406100454034400403e8880c160350040d20803c442981420500b140300842541c031040006038410352440103607804204030035408071000c040c0c1610702c02d8070340c0380e0150040b0300b040c80401d07404d004940200310200424005890040050100480040c1d0002400031550602505a80040d18810702198580c5008403401d240a000c0d07503880200b020a80a5152a645594580900e0340480070411a400000316090200c40305211000e0720014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 690786232 1250 690784982 690785003
    0xf2607060b0f0a050102061b0c0307030305040c091b1101020c030a0306030c0e0433060801050601080f06030c040207050c1c05070f0e010b0a0306090c11070e070c0b070c 74
    0x5040820190201455091144201c0340b1011001d19101d10720100f6501c0617401008181d03510049178401980841c203c9420b54018001c4d00c2c06224200002d003035140c4a81e802051500b030500e401502e03901e450b046803801ca42814102c502032a04180c00781c0c80c401c00f030300d4101c10000040100c94028440c0d0b0308a03141c0c90000090b0704142e150141c104404407480b80398500080c40c0d903452400003421060302c00502640c100c0504501d0304100e40380151400036604109440404c003000c078a0704480340d66000e0000d0744d441c3c40c1001803035a04803a0855002088d4142ca800518003000040d4a5158403c00540300d5580813070320400380001003007002030662001c0e10040b074481401d6a030800443e4250f80c01c64043c421020003140c80100c1510341d008031081a0080f094030f90070180e9a4545801c005244400c140d65401c00003070b198001d0007003224581d055110100344014810031700703080154940013005a00a04c074140506158080407040a031034202c1010309007070b190850102d4020412480150124001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 690787482 1250 690786232 690786247
    0x603060906300c080d0905400614031b03340b030609071b030c050a21030b042906040f0b0a0801090c0f140d02130602070b070f26 57
    0x1503a40c04881d2079485401e00705940307002304614800b00855903204d240d1881000d2031144020290900844c0e8020344903001f075000c034079100040310304a038132005800f002d8521894039030900f03100700060b010036919035242113a424400301e80c2c2d8440c170680300c2007003d000c80714070042c0c2240207141c41c8400c0c940803030600c0c203e0303541e69102210741c005554061181001502113503605018110720f07908185255106180d011003500d0960b044c1c2600d00054510740180302c8400c000442441040752880e44000400b202404241001001c461070b102266005c1c914201c1002804240c8d4680c60003019850202c01c030b120003401c8041000e41c0106d034803524000445041c0840c410a03000301034501040103075214002e0780c1e41c1d1071000c800d4415002010300800c582c2000407403070b10b12a0944803400401c010031985014250070864040f82e101d0801480e1610561509221055060240c20010b08040b9030035400d1041036142c2c06a40f48045400070245603600c43e07010fa0b10041e010560b0350303040d1782c280307070b00d031038188 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 690788732 1250 690787482 690787499
    0x20c01020c010b180705030606090d03080412020d0e040e070e070503010614090f3c0901081204180b04020406030e1e0a0602070c0e010b040603060906300c 68
    0x1e144950225400c1c12941c2c0c4040c100351071510344c02e85401281c1402a210840300755859030000c2c100a03008801000000c0745603c440c05510112031082d560070913180ba060500119240b8204100c1c07046401c0b1045441074240c0c000503240700c201c411140080c02400e04800c0d5850444287c3c4800c24a848580400400f1034010000c0e43c101c4040e80c0b55002020420941c0000c01d100348030500b603005a1440c424249803d0010320000c104600003074100718208107003804900c0040d8901076200c1d00002d59032038001703400d1503030001e4014102500100424120b42c0710100301ca0107607004807816032689183d06820004d81da0030641e001c2c03801030011940e41b615160024060024018011030034860102c1c1c03c00d60041048003c1451101c10010b42130080b0a40e031688069800108150340c1c41c2c0e030341c0b84042422621615240d0007020256111a621441c00078040c0079110b06611074280245001c008100c0c030300c1800300c117851140c00d02c2e51060b500d140d080c402400041030342e10041d01c826100040442d0782c84 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 690789982 1250 690788732 690788737
    0x6270515090106120615080f0c1201181704031e20030c192418031101050304081c150b07020f0603070203070501020a0e1c03090303080c070501020c0102 67
    0x1a4038200c880e0076034034a49040d0a070f03030b018452451808440b0084202064180e0301c22079180c100501c0503a1220f45e5002e0b05031920b11600710380f2075960071035500041e40345400c50070422000341c0c98000f80814010900315601da5140e030720b8068820300006120340c20708528031003110041c60f8010b004960303101d07000c60710001c500910041200c0490f00400c1510501808030100d1242900c01001086200079400c2404801e0310303244c098032a410000c2c007000c145400703ca81c000200c110b800440301d010800c1d19130024100c070b03910005008640c00000090002c24a098800c3c02410740030b083c00c56a03038480c0e107803a14040c82440301e0003400c02207a040100d08183d0640015120740c1012001084150300c82d40d000c0d140d803047e540029808a03a99041400c1c506240d40690360140180c01034904140d11610303080d09a07440105842d0001341050300240c000d01e4180c58203400e180749003650300c0c03101200c0d40c1d029000007007034080038040c04a04000075006145110840b00d115510900a5403180307501c022450103034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 690791232 1250 690789982 690790003
    0xc0f220915150309051e0d0f03090b010b0901090308070803100f080a080318063408061003060e0f1b0301050907080402191d130309060509040b0a080a0308150d062705 73
    0x3076258201c40030300b23501ca400389201050b00040900000d0f4604000404141d02c00310445040c040700200010106640001030803825003d5000700d6a40d2030403c0818000600d60780080030125010b18060200460011f512900641c0c4101d0481ea00e49990000d004510580b600003a014480c1c007003040118001e81503106101c0e140da41c107041101e00c40e6511000c10781c4000340c0d640c00084d1480d0005115181a03150303045030341400c5c1000640c0c40e072641c0c29100882009c035404c510210610082c820310803d504049909140048081d500f1941400c00189402401410380b20030004480c0100b8103640d42c10940000c0b110441e4411000303199904007040041078254135140c15264100c000582c1442ca139500701807541da065407034512060601a06840702d4100811041d0084d07501c40c0c95001580395907101102800c070080043c1030343c1c0c0340d41c54010a1148000d1204001d00b0048000310700320340f11608030b041e03048d81c0004003041e00f50b0441d01c11040408400266049504001c0d0703100103000340800e08a400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 690792482 1250 690791232 690791237
    0x2030402011e02100f050112110406080118050c0619031d011a0117010501022a041a100f080105100c06020d06030c080c06030c0f220915150309051e0d 66
    0x11005c07500d0130002c4030b00034403a810020f02010f400348000303121080b40c2e984070305c0b004100280326500c5243d0182181c1e00c0c2084540c007403c8064145040c498204400c08031344a0882c1c0561412a000360800d070204180d0342407070103064668a191400240f40ea420500100e030980081050950520176800416070b01e02ca002c0c007003540d01c60140e207040404a0024141c40c0180c0041201501031210041d102da10b800f07070312841e420601c4400e11a581c07107015100014080c0100001512000400c00031000210580013084c04461100201220741020b0601e0444000b1522280e010506080070f0f980448074140c0244020310001e80d0b0b1011081d20781c8080180c2e40180c04000f645900c81041540e80c070741d2501159400355042c00040c1c000458400200380260303141380a1800c0c19000f040011000010340e00440f801640da0000b03111542031442012400883d000203840543d2500043c0f040404036420898105503c0d01202030901c901008460150142454400401d148850709640c499400203040c100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 690793732 1250 690792482 690792491
    0x9050f1b03070b07020d030903051506271924030501050601081e040606080d020f10090c09020c070e010e0601080c0a0e0d03200f0616090902030402011e0210 69
    0x80d5820000350b040b054440d01001030785002c3e41c9400f003046005030030100300d08000300c504010000a000340002503120030441c2c606151410b16404024090801c988071002d01c1400a0515840044e041e204980107025140e0b85d4502c1c9071540138030000742069906152000c03620740f606201b1001d90528040889015000070002500c0300001100c039644203580058140c43c58024941180454041042d002803190000080107541c845845042050036a0030781c3c09030b00100c0d5407150ba50014040300341880f101c000100000c1074540c1c0c0300c5900082600416560302d50114551881e1101000040040d00d1a82126030a541e901c0c0c44100112404445c0700d070000313001d41e0100b110700803440e064500202e43e646a1001c407556146c2442010f1800c50303010303010001c01c5400c030b01d14155030449414540b4041e801801100e102c81e0003041c03070400040c0046558504510032100174603484104407040d44d80320000981d036a111400100c9128203080700d5050f955261140444840b9000504100c02501d401002e12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 690794982 1250 690793732 690793783
    0x609030510060b040e0901061a030f011406040b030a0e070b071101020304060e06031308030a0c3e0f010614100809060a0c031d0601062309100309050f 66
    0x4140c50452240b00c2880078203020038006802240017403940800070000001e40c280d035031060040e000c02c03500e1003582c8600000091102c11001006041c0c00b400d81c0e041c1544c4400081780200d03820707224520402118502c0400411540c42e040d0708440c0d0006803940860b00c2c1203032101268036140c0d2008008449484030001c41601c4d650021003900c04949864903404500e0041c0000d10410340d000034101011540c0e284088400107020002940c05592036900004100138054030280401098036512450a800100b8a0000384003410302501c040d0900c01c004610341d241411001e1a00d0040c03550440c1c00d5003400d10201e030064030010220500d24003101c0614000414000c01ea4410a00b038400541d03e801c0540000c0442901c3e400c41000d42c60140780020f00071040d80307a052032540d11806039a0700c0d03401042c01040300c0b0f13900801a5220303181c2103400c100d800c4005000700c03d5500c9800503042c0200c0c51b000f1019411800f903880281459000b500361000010005840e0303032108244070055200e1701c41d210195 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 690796232 1250 690794982 690795013
    0x80c061006020a020409150c08100b030c07110102160b191b030e060403020405130201031d030703030b0a0b1306080117030f090402160b0910050618040305040801020406090305 77
    0x5404466803a00a494642544d80900018050300e0000381c61210800c04500d103846482c0c0f01d10200030000f551040101c0c2480d00c66106030701c03050307030081c84000c000384248204150100121891140c0c41400c0c0c141140030080103070f040c1100003d0b100348012032a20700090807481d0f10010070640035500194110108262400d9491080b002d40090b03140344004003032400640140b902400e0311200500160400380d80b5400142603450481c0c40b82503c4580c46041011560113016450107080712030380d00100b94010b4441d042d0340e80582030028040689503080400c030b0380c96145440020344080321a06546282c59158484480c08030b20a80b030001e007072100002400ca2010605202e03140404014601c2c1070800c80d01e09040781c12003121b00d580300b5420010b1484d00303150700d1105001c1a101d051032804602c2c0912215041c1040100e22000c018140820440c85648000c6200341400d115600f81c0003c1e1110b040803640c1d401160400301182d0310000303012910340e400490401c112403041d0105c506403181c02542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 690797482 1250 690796232 690796261
    0x312071412030411120d0f050d020d0207110301020a2a06022208030f0406080a0f0c110d03110301090207060b0604170f031e0d020c06100302040e0105161206050d080c06 74
    0x1018225000f03c152030082c03d02c0b032a0a04647c80300f03482c00b141840406040c1c802281e1002c003404201c40d5002444100300a09d2060021060804400840c282480710b5005800c9111124450700281c101e04524000011890380700010b003500014119201c0a13801c401b05039030040c280a01000c001d51100014900314008200c0c2d6031440c0f0fa002903410700785890380642d1b0310b59000c1d040d032828a4076a600c0b0f0240c800700b84680c003000119035540c2517a107880030421a062424109040c1c0816051000c101c28105211003200e045400e590320050307440003d4140400201145950a079001030f001500103660950750881c1b15640508034240c42c401440301c0d54190b600d2081003604a45c10f14880c0480100c016000e004d04144000c5c0038001d445e00038451034540c00d01408442001c45070007071610901c02e6051078400d003101c1100030307030080000b800c010407459146c1440902c0c1c6410060031035a29112801c0301e0b00400010308003d800564050076a24054003d031f003202c4d0340e04160388160701c001a12810b40488 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690798732 1250 690797482 690797509
    0xb0916050112090204090506070206160903080a080601030212090610120209180a0507180615090905060d080408010606110715140c06090607030612020312071412030411 74
    0x407010020000303465040c000d0283c28100f0b0ba0301564540d40d00011500901006100e0300311a400343c4102c0c600009403240450031041034008004142c04184005407042c01120201a1030342400040b5586000c01200603118803a810888480001c0a000d00c440000411500484240400104080e211645051085a0b00a010b9400684200400c41e00b118400c0c6034000d400102d0305403404e066607512001d03d420042d0b0b0004002c041c1484c00d1040040040c86190003410110b0f61184483c040140001e010b882c103809005802c03659600440d22541e5019000500540d02000c900e46669603842d015009100700c0c4944004100d40d1242c0700941c0e08041146001d8071811501e09422201c8105d007290090340b50f41150488407010007945082c00e1003080190720070b64603e8000c00c414900f040300241620703031940c8140c05442c110140a0300590b80814550b900c035050607c9181c9984942c2414640d01841600b41d14145c003071000b020742000040d000440c0300303d0040030346224880e1410b081c090810020b42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 690799982 1250 690798732 690798737
    0x80a030f110c010e04050c16050d0305061c060c051606060533070512160c0801020a0906051c06030c0303031a0108060618090c0d0f0b0d1209080601030b09160501 71
    0x10b0b28140340c581076000f071742c04c1f2941e074134154200382c3c00c80c80d468040c00d00305600b6070381d550003401500c01c00c0303600d40182a4404001c0d185100000e41810043c0d5401818200c010100c0e0380b9010302c0f5040e1481141030f030714154126000700c00780e441c1ca8249030700203009a005540c001da5002841903201030b04440d07c04101d241d03c44000d1040c0400d000a0b04480e002028201c030513001c0c0d03400c9100c0e08030341031015114070004100501d80c2161070b442e15903a205060762025807280d005118101035503400805000459105040c155940e14404050308000d0812820115035a46484408002e001c901c05001e020f581c80fa48040054075403111003e00e920000720800c0d030000d800e000000f01e1900f0440b02402c03400110b103800c040515001000070300004012075104140b440f0220301030803094124044e20001071551481040a0380b169004200300d202d43c004003605403006208084c41042c4075080c2c1c00024a890380a5138155616441d280c51020401d03140c45c4030500c100c03042e004030060090011400c0f204140c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 690801232 1250 690799982 690799997
    0x120f121b0f07050102161109090a020604060f0212030703050712090503090f01030b0405360601030f030203190f090611300d091a0c03010e0a06080a030f110c01 70
    0x1c900c600100e42c08220100c40554080c88a0018108500c1580701d00b50b115000d02100c0c405114144406001c4c02850040e07668040c2048001684440c0111800d80d916494820040c003c3c40e07105070b00c0e001d00741c1640101d01c40000104003043d40e2540c0164012507495983d003a031043e041c04d440043d00d40c10b600240143d0000c120640d52498003840b40c135040481810040b8080d04040c001a04960301100c512409111160405107801c00c0341080e001c010b181d1401d124544945070a401c1c0e6988014000204148000d030b001d00203042c001c00640c1d401000356112250640d5440d24001d1a24003030049c80b90100d01d1400340880c4403402040702030528a001c0008200b110f0100c42c00b210300041b182121020590a200c51452459200c4003c0118101404011540610b03500c2d101114060014410041e03004038824030004030849405c0324111560701018038201c2c0c17a0307114403070002e080030341c4098028402c2441d28000c158028203641050758854450085251040001603121203c2011150000d07260 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 690802482 1250 690801232 690801247
    0x120613511401110d020a0b100b04090b04090506071d040207120c020619030212010e06010801060f020114040318061107050d08040308120a0609090209070809120f121b 73
    0x829403980740100149400500c40303400031140b500b040030030320041006030040001c0b8400e01c54031401045d0000340450040451600c0c040c41203802d0300581c00b848403001c0d2191607000c00d030341e103c2e080030140d1500001aa00582821100030380034005038403400341c084001c0b40d0780741e40701e207803074402d40341c03900d030002c00c0355803a405415001c448103c1001c001720b0f400b2400340704d941240c00d0b180241d159140307181d490051b41c1e55140d040c2c1c4079200105074480400da084003401c114180c1d82c0300c01030340d0440307001e814103120301030342000180e014105915200d140705004c24104401d0544c0081d002c401d4240c0b080409c00084e440340030880c0c149100700b0070540e0540c801c4200300010308101003144001405030394a02d04042c1c490b42c43c070f4902e41c0701003089804c1103011000d12517004413900c00c01001b041500300c10400d0612550204441d024001c00ca407040c0050000010001c9000303210000d002c051100f83e803541d501034101d041440307400000a501e0f0034100100081d0900d142450340341c040007010032020703092412 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 690803732 1250 690802482 690802499
    0x2031603110709020409020c01060909050a173f04120507170409051b070c1809020d050609010c02061017030408060a06050906040212061351 62
    0x1c0002002071140328525000501001c9031000e040900800c400240c0d0b01c5020020310fa00303440f0503401031001d0525080c1d040c80002c10000e0ba103061994403030700700441061303c202103140e54000e070000305c0304901c0c03002c00c901200014130400f00c50490f07803045050311b5888110fa0800100c00f04580013014082841c00001880b806103000c0c1c50528498a003910140c0c05281144403160082d03030142240ca503d0300d06205001403110b1012410003068a41c841c2028000e49600805044034801e04240001e03800000c00030350440d42117040c00b02c0c0c020703252200780c5005182071543c0711000c40e48a2415440c00075000101e030301c04101203010f03481502c01d00d1005404d20125045160f039181c1c0410042c441044000b844440071312049200703a00401001403160320300702c1480f225540043c4814402c920410002134030250404066400000540b410b400000c8500c9500c3c0040c40c2074900011550b41034440e912115130766230407a13100702c0400c1c070b40409140280c0d040d46100c00101c1d0b410f5602990340b8a01400b075041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 690804982 1250 690803732 690803747
    0xc1f0c05070213050a021314010f1103090f0a0e13061512080a03060302180405122a1f02070203010b0a081005091612030e03061b030907050a1508010602031603 70
    0x60b445e03580185040e40405060858142c0c0741d110700105002c00c00501015a04024800c065040302c0c01c0c242400782401c48040d44912035044c50503c00d203800001c0b000c05413a400950000f90442402155141c2090b25585200e15001e00c803c0b100c031810245491034010f1000703036001c100d5810b0744e480f001c07a11603542c0e40c1c41c40790006182c0a042507503076540000075a40300d0540c19186070026401c18440e0070107081044c00c0c0304d070200541907103a41c00c1204424041e01403107203801c00141c043c4000302c2e028070880101d00305041800300f100031700d000d00d02004010f2415801000c00c06d01c00c078000c0225203285014000212000e01c103074401a00322005a20248040e07810603680401d04a013919442e03459520032414403401d640150000300307100461101003541003c41c1071044401100105800d141c144c2a00407190404078a0002484010021602000041004001404008142c5081070340c8800130a41d040d54001c25480021312034000000c1c04038004401c5424000610002c0340d194542514241c500c030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 690806232 1250 690804982 690804991
    0xc010f0e1c0f05100207031709120d02090a08071d09011b050d0f0504020f01121d0d02060a051b07020d02130e012018060c1f0c0507021305 61
    0x80700d00754903074250524080c0c9a1103980d00c144020700c0c4061480c01c050b464040c815220101803481005111702098110803c4030300258240c0e0216141d640340e8400c3d50418201d004503039401a40030560303030b041070000d8028207442c2c031050b5400b180c0c4075a86d5a050b90381c0c50342440340c8800030006003511180c4401d4000400d600034600b80002c074400c11040c8481010800f0501c1000010304040b403040410003640c0500a080c51090000f40700314103041e00050f4225040d4141c55041c4400c040b1200280481c0d030300110b1003001079802200144194500481d103e5100c150b0320001802054005161212241304840c050101078449190580150310944441d901501c4140d9102041407203010040c0d4403200c0c82d408407003c1c03c2000c070301d403421031854a00703558180c1110354048011210048101e41d40400b0784054450020524194001708804104144541c0c12595841d02480d0340e02c004240c0d220840706140a00d034a4200128400503034101e40d103005090b402540011102d41780c018806058200e960007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 690807482 1250 690806232 690806239
    0x40b09011e032909011502010b04061404050106050a0207030809040621021914060a030b13020a020c0607150c1817010c020610030b0717090309030d020c010f0e 70
    0x10000e182072028000381c211210740002a4440403d4025119400074000c0c0809003040d4081445100000241882070140201c640381c01400c052496064801d401039024004040c1c420814641c03541c0d0401201100030800c42d0045041c50000a01d8520610403140d0600d4240c1c0074008003811940c545813150300884095074000d844120202e691402800c808003d0f081d0041c102d00700030100e2050124401d1541041c40640c04a51410001c00c42d081860032002d5504070b40c0c40da0b9030640c401d010340c0117014891401d504080c010307050a14541ca6a4001c04181e04581c00f10740051031f072a010030859110340c4100520b8541070000101c010001071300264501c180c2c505250004111100e90214103105d130790f01c8070b4407000b02d00c0f1511040c01820b101d1403200101910190450b894004103c980e02c2c0e070b061000034210360b20000010241071040c0c0c1c6010741095010020401401e000301d0f880d80c1c80e04004003c82c82030040e0820f4800ca20f000007900c1c0b0b6001c506031280403c810b001007054502000b441c3c3c89581 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 690808732 1250 690807482 690807497
    0x90e060f060114210703090c15020309010809070305011409010b040b0f060304170f180d0b0412050409050708070e1915030b060c0f071e09020d0e071512050c040b0901 73
    0x1141c1c20f2075611346216404035540000c01213440d00b4189880c0b401980004034001c0411036015407160f020044644000d020708024031729071220703508107242012541c0090840d5280101c104025454480d0450042815000034080a40c0480c2004102d1305011413882e408140c0025802850800e81c0255920602901d040b10180c0ca145084180c654419850903030110030000d2b102c3c0e4401415902490303c9801910080c1310705440341c7e2640c2401101500240051201220700740a0741d11420848014145000050145007020003014041c80015980c440c082050404840014100049884075280d550149450200e18001c201c04140451190b40004c15407207112009050301c030040101211401100200300e0410014030a608208858100d003114540c66201b4030302401266040c1415210103041c010b94650f8080c00302c100412103c400f2030b0307003402030020014112800b01c1d8038024a401548a080f400d2207421289000c0303900031280400301c0d05041c03006000c40c5031a1000741200305410304000301e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 690809982 1250 690808732 690808777
    0xa0503071d120607110609060403031512150f021204140120030106020d2105071b0f060606181202060c06100f0902041202010f1206090e060f060114 65
    0x2110b03100325030912a1981d2044060111403503001c040798040380d5003480681054189035080c0350f2548409000074080540390309152040001c003005c9140105124100b40c07400d0403041c030305480c0d0241c9095400c01080d203050901140d80c1014000c03900c6145404803c4802d503030f1642d450521500d03135102c0c82d16196580d0480150003180c80b25079903041100e00303107490f905c96140c20b400a14000401d000316080004510030b0b0f41c51480c0c0101001c0002006240200c2c0340e03036942030708442c4038403d103400640d014061038500083c007803001c064a0b44540180414044151904016120302c00c06c5038002d0300100c81740008000100c2030800f01c1c816144010002803400c0c0d00205d5030351810505541d03105001000c801e0400441c00700000d214000c00704000300350304007440c040d00c41c1141650780d007005e8148510044040711180c81000c650b01c03503280d142c1003044a00d0b250f54507500205290403405030544140703008107004614219540740319440503590515110030300074042e08c181d006000400d0b1102000c90460707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 690811232 1250 690809982 690809989
    0x607030f0213080a0203010b0117042604120507060e010509060c0c0415090c0e1305071e12061d13050f0318010215072a150209090901020a0503071d 65
    0xd5000f404140d005050651040c010142141e100c4800e00f41444414140c01c2507000440309155030003030300700315072095412900041c081e0a1401c0b41012440010000740407801d00e500d503030b858401a0041040b140f5054a9031421f640740a141c4a100303001c00e1044c45603124510303010001303002c5d21070343e4001e07105a14524804503041c2c8422020001b005409800180328002ca14070803107960603450301e884616501208081960555080d66095100d61103100040303009000e0380c42903152500c1c0c560740300750128609100a101884070047d003c42581001c030001800b80042c00484e0398030f424582c0e44506034485070111803440702410000c032a1406000003410702d584003840030f4003144031078031948080f010014000a040400752401003071814280024001f0082d842918030140d24007813000c11402400388010021620388224009020341601e910701c0d00b40140e590054084183d09941d0412151134a0309040d00742e000c0c4041c4000094802d000142c00c05104840d180a6041540c05407952010403c012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 690812482 1250 690811232 690811267
    0x150a030507031110020346050d0c0804050c04050702102a0c11040b030304030510020d0e0304140d06090204180506070c0c260d08150409050607030f02 66
    0x1d40300003c1c41e80c40424203040c980c1c440c0c582100c0a202940c0307400c3d80402e828100721029610740071288054242ca024101c040b420143c0c4401d0b03070701070300c614124000e10018040da0200034a06a110709044240d071040e0b004644150040e90310201034011980400e003804020540100f20000314481c4600841c8024140d1045551254580414800c114141c1c45180243d40d80f20500204001060450a01140d2900c070b01c105a45003c4902003541d10034980024070b540540d4001809601039455403080e840f280d03900401c170003007490005011240071000b80da5100c0c09584118050b4200c9401a03104500d46005003131842032140d04006480c1c44a50085400c0383d0900903500120029845820b0034044100a00ba900c10110b00e42074a04140c2540c0e00c026469072840344168060a100c0e00d2907200c1050707141448418460300440f58940c0c03989100078500081600d4100c2004050f07050340a0904060052004403900300b0700400158a07060700440083c0f16881400d09c22550a002404100b05407085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 690813732 1250 690812482 690812489
    0x180309120804121127040b0603032101080d0801050310050a1803050307030b060412030509030a0f0b0f060a030c051210021305090c0301060903080708130b1b15150a030507 75
    0x11001041007100b00b4446211010903100f01c40d0510031140b144583e00b54111703d980154031070ba1105840d00e541001c6032131340c00340b840c0840e090098030900d0f202c4c01c01c42e000c1c040d04032030940c811110500004001629542000e01850350540c000170351511146100d60045500416884c00c0043d4079014000c00007400d07801d8001c1240001c400005004401e130b40750040401c0380c0d0048a4035441c00e4a05070010b4901050001d0090034401e01182085a990b800d00c0000d11903500321040a040c940907140602002400b100d140180c18007003c08520a07003440c1d010310007621307404410500014100410040070940c6662440014490314031010007540041c0094410b022000380c441103a10704103810040d900700024a6042c54682c01c1c001003244590102c0c2e40000c40e500905409e56504090070302114620945042c0d285909014400082c41c03ca040014000c101003140207800c642240080c2584540c0045c00d60801440440d0120f4070080c011500d80841800041c5031303007400d03a84c0390303101400c00103640d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 690814982 1250 690813732 690813743
    0xe0a031b1211010509010608030d0905030f07050a0b011a180d020d20010e0906090402010909020703210207050a0b18061510020a0b190902061c18030912080412 70
    0x4030700c9841c0b0003400344035080041c6070024000c6d542884640c0f0340d80c0c0141c6850346070064880d000c0ea02401030034821a81c4403a0049101a9547c20a00300b1380d5544004040c11101c01c0344440001922400c110b58a6018405000455141c902c40c0390051000010400c08503501c00c40e502020001a6034003001031852910078007905808003620010b5912074030a4241c024180107413160000c03840e6590141c0d0b6688450b04407425910307903c8600041316080a01c1e000089464400035a0700c0034550410b1540d9038407083c0300c0c0c0400c16680d000a00c20103900800e0001860780c0d200c00c1074000000c030a1a04540c2c0300306141d800c550130309800e140091402005079100044c0c0e580d4001e03090030906104412204801d5640010034182045640314400010001c0070030810a041032304171007030031758203130082080b00c2d400400d05521559208007512020a1840c0e224a245107000707550070015a44c0d8104400082c0c0545078400820700d40825042680c045200c01c440704401084046413881035a2400b88034540a032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 690816232 1250 690814982 690814997
    0x5090d140f01150b04050a1701060b0c030316030209060d0c03180c050f0a031505040602130315140106050a05090a050414041a06090a150801020a0315090e0a031b12 72
    0x59103aa503e18550381004d4560b0004001c14001625a640a00101c805181c0c8002d4004e0041003114014403c54011301c42408001030f040c10340850000c0034600030700c00440000364a00c00c41600b90120310460f4070f06900134805215040c0544159481141081c01d10704011400c1d03002c0c6200c0144031003030020704039904000d0b410203210a05010000b0381110005548107102c0c0c600756280c0743c241201c0300245018030350700e800026041080305c0d010303600002c40508061450030341780d02d02070b11020400e1402e0071070395103002681d016103408841514106c6a060715134610300307401c0107401c49055101c403408980181c40700d0400195a20b5522850641e203a00540110071800c180c41e007850040d0303601043c0f11700304600d00280400c640c1c03816041d94000000510005071080c0403c040030302c0e018158820320f065403011416207a1913815420410b6020502031107504080e8441c0000c808890700c2a90400065100a462200190040f01c0f03140c005000741d801c1c1c16900b51180d940101c0080c40300300e5440040c402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 690817482 1250 690816232 690816251
    0x906050907031a0f060d0302070f0312110703120c1406010807080d1e0806030a060525020f07090e0f0102070f031e0f050310050d050f0c0603010605090d140f01 70
    0x11007252140032010f0b02c0020f81e8140b12601c81600070707014102d503108004088080b000c0500810108004221010708020f16a80d01e0800302a00103c0303001507801f1601d078030f0000c5001600855000140c80e0f100b002a51100d40b8808206d41410b0b445400b02c0d083c07400c2c80080032261404006490080002030000c0040340c0c200f8516904040d003a40616051001c80c0300c9100b801800e0050304200c0218078034200f010b540d50503001901e0301c440c0f41c1001d000d41d403404051101901422080343e0600c40c92050403550704842100880c2c2e540c180c0f44a0f4402034024a0b4144101001a00815a1046100210b0382004801e642481c03c80c0e000385d104613040400c550b106000c0541004000943c91000001c9100e00f060a01000d442c07442807140c104104200000041d42c0fa4001242300345c00350902400080e0024410724000342d07100e13481180c4000a00c18918030600c01e00d4542c080703034141c60031030342da030350502e0041c005010f42885c209004841c1040c000750703400d500000c1040319034100b000250010421424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 690818732 1250 690817482 690817493
    0x1107031b030c0f06020705061c050604020d090302011508070b1e040320090627091c0e0a0e07120c02150406050402100201020f0a0c050c220b0130090605090703 70
    0xe51f9441603004940512501d1010303800c0150f41d00081c1c0900c140880d03140e5070040000c00900c201c00d044840149044818001e00da415400300c4182c00c000e0030215151074480811566907c00d074864920140c508101c040a46003040c80030958105880d5000341c2815125520342440c200300380c49881820303040292455440c030380342d00d246410400c02e40e8903900080f8284000c0c5400c500504540700c01003508070226648110401598940c240012040242e05901290003064811440c0d006031140c2c4126101103404083d0803c251301442c0c00381c486200e000c1c505401d80015111414040c0154059032880605138190f034040ba80c8502d1141da0006224038240c0304010a081240380d842d01160300c14007220107454520001c40310000564103080c1001c02c4d01346404c505c2c00c503102000f036400c0f0000e0200c241c9800e94003114030028040a0301c05003e040705001c0110b40c8011740415021240c00324a840105103007001e1082c4107504640350000c28001c0460302c4090984800b074850803607542c00741d0010401d110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 690819982 1250 690818732 690818743
    0xf030a02100c0309110d021f09090e07050901050d0f0606090b01030f0e0304120807050709090c0812090d030203090d030513050f090606250c0608071107031b030c0f0602 74
    0x203010f0706040008840b251500303100d4800e0502054000c1c0302ca03080d05002c0d503555000d94000c004da032803540075840c406a08010003000052150b860700d00e042140c0d050601c1070200d804003d444001c0c00c643c410b41e1034003042000c0d00e560410141d0322119502115004541e5900924002d00840000854800728680c00101200c0031602190074451400d060316007088800705c112011101c0c401e81c0c06002c0707961030030144000e104540006125100e01800020f6060b255000f03010883e02605002d0451a41d5091041e1500d807041e00321800300c1802c20291200746005c0110030759042c00303441241d090001c0c0c4004903d200018900030b0b000f00d040895030040030700e80a803111001d41829603002041d10758490108851100280140c1e12488002c141d540044400c40358a0302c42c00020800030b00d60910505042440360514080c50380000c8000000a03d103d004108100158210b200105242861a201c001c3c140c0c842c10710401c8040c442c2071000010503803d4260f003010300152190405101e241c1000a40b030074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 690821232 1250 690819982 690820001
    0x3051603080f090307050c060306131817040f0603110903010e0715092103021f06140d051f23180f07090c090b030c031006110703030e030f030a0210 65
    0x2e5000b000000f000606c0030400000b2600309403100c0340c0700d072507200c0024004008a1880602c4600e0b113045029a1030744240b03000040c2c1d01071030100304101070070403101d000c5104078000d01030300c0c2c00d850030200442d40c40f9910028400441011060820f0707143c40020b405d42e47d40300280440c40e0b0007200103200c14803100c04903405110907401e00c0c1c10b42c11b1419010804040e0401c0c0704503d81103440198005041c020b106021120884c80303032a403a180802c0d017488000703000b00d000c0c0c0010703080314184082460030a5850310f400030760440014181d00d0039081910039040d021041d143c82c203d0301c1e007001d68640407410112001c0c0500b0b003130508480303151800d036107101c0341144002c1154a60001102000002003c90301c1020342d4a14100403c2010100340103940142c1c4a901c8484d1605000003042403003c0b8200207103000d8070800d26850b11030741d600d54003241c90b503007104810755894201200800019000e0310f0b0082c0d070076201400ba0740fa0440241d0034517055801803412440980c10000310069400114401c00c440e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 690822482 1250 690821232 690821251
    0x403021c140105070e01230a0903030e03070b0304060906140c09040f0b06090d050c0306010f0611060f0a0c0c050a060b010212070b0a0e0c0a060e01020c0a0b070303050403051603080f 80
    0x10751a04c090000c040250b1048003c0c141300a0300c1d01d00d55500c0c411400304d02d00901101c080c030350395203901c400140b11102520065000444110001b40945404142c0504480c4038011082c1585c8894881704010020010101c40c410754550303411051000000b0047c0c4141c40016400341c4840c51340e0240404e45441c5080c2c00c0490b490120074104540d41e46080c2c0300d044005072a2046030b848a0304d402c81c039100a80c038129a051282000002d0441c45140c0d00c0e0040c0c503100d40e1495103001803121401e55030740050f2490348405113008000b0340a0f0071140e100c0c0c21742d2425841d1000c121070254a550781845200ca40035a405da803104011009940c0410034001c1c1c1c8540403072206e24000207900c070309a0301d040c0940102042030315811010880349c0e0802a01000c00b0b4020489554103984a03005440c0c40c2105050602500132200c84020500e0043c16800440300c0a0b01d400e442c0c0f074015a011070040000a10840c14000140850a00c002c4604070080c400740c482c3e103404032242010002200104330003030000c3c02c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 690823732 1250 690822482 690822491
    0x4290c1209010e090f01060c020a0f0e011503140705130914092404080d0b03030a020d08010b07080f03040f0c0305060405073302070b070804181103070e04020403021c1401 75
    0x98103c0520400c50442d4140d18040e2230700685480061101381c42544002144003d8080101e900204099001c0c101d6030488003612040991540607025075080c0301390741400c0c04410001441c40340c00b507070040c1260482e4604d000492901d03001c0440840d01c0080221740c509240da03003004001a02000803220b50020324140c2090f440f448aa81c0c442250300410090807501e0104a84591045a4005402104005054079290092240c000b0343c0d034002d554040000501d007400000b66401ca010132201d620742c0145145160102d1862481c0300b030340c4040e004542100b8640071481c0442d0900300444003451040005d05103d04040c10700b0b41c502000c0b074002d030200491240016051840c0d020303044030381d00c03008561884410404181603013400c406500404040d01c0000d0601c04121a2a0003007098030301c8200c0d0440c0d60030400703130b16604941d901001000501c0701003010498590151082c20108200280301615064403580030480c3c1d880c111090180d2402d01301080b00411074000b0544e060350003911700810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 690824982 1250 690823732 690823741
    0x105040b0409021c0b100e180f06040506191a0c01050705070c05100507060b030717010207031e050f16060c120b04050c0a0e040921080a0204290c1209010e09 69
    0x10800082c0030901814401d4a4124240545515030b400b59540d0001c46ca41408d407038903441981001c442152110f11841c5444005451407404403514201c000409200754003017400e0040c51804074031107d00100c2c02940910400c2c000032024011180709400b9590307200d4990340d06103800b80d031041c5c003a080306104004008840c1c0cae0480d0700c41c082c0c6031701c160080804030b0019031000129052180307a80121200340080c400f04041c500054004080a91003035980f0b40095540c54005900c0710501c61a850006104020030028145800d0140100e280e42c0c0f1150501d40c6071560350101280c200c0c0c070500313000c51918000c542da80100c600c60300061000540b414003141c035101c81360701c03506d100340030340d45c802c3c0019002840456261907101d0759109030300142c0051644400304c42d02211100400c680c20005440c100001c01c0c80003103000303903811542d103510585034510000c02068141844180b00406940b42840000c0d400c0e4410410900451650407001c0c1e9158030b45070005244e0001c08540500403072480b014003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 690826232 1250 690824982 690824989
    0x30f0920130b090703020f0d050c041e050d140f070f030c06050c070e150d050708190b0403031e05190506030d020303040b06010e060a02060603010c0309031d0105040b0409021c0b 78
    0x5a03100c44d50707240050340d41a01c8542d0711950300070103103251b8469142a041140100c5510000d00503514800001c80c80c0d201d403185a0100107245001c8c2c0c40e006040740d007001c40002c05402000d031a00390284160340340304c50b00c210000d1030020564040e040e420341c1114100140560654a41c024242529006161440b880b581c9551800c07584540120000c4010000e00ca0640300366110010b54001040700c803220202c0d0401a590380c002c0c1c020704110780038455081403815040041101e84a03402010f6070210307901c40d14168000c0c0b191021201400c0c400c041081807641c0781e4803c06105005004003003100340d05c00389600c0308640f0020141da0203640a04056064540c0010030742e41d0040d4814030748440c6a498800407544481c440c0c40241e003100002c02c5810a0300d4020486510420080d402040140d0390104120140c510002d400780104901c4447d0b4894100d101c0c0001140d00d00604100d49816076660806480e40d101e58044030080f540842c02001003c80c00340200c260b25042c2005010580040000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 690827338 1106 690826232 690826249
    0x6080102070c0f030c03061a1c050106060807022d0109120f03110f160506240607080f0307030b0d0f060e0a08030106030f0920130b 58
    0x4070710402e0032910181240d0f00a044d02c00524a587c64400042544410301030007025002481d24840d124801031a20000003185800c030652103d05055003194915001076080000000c144042d440e030010310700001003c8851052250318140c2c1d94001400154402007074554203080d09a42841007483d042c1d9040b81c00ea841c1c0f408462540c002c200c0c101c5400380c500c660581320038401c60304510400c0010345000c2d00360343c09164030111192506403416900300e9510992402a0115581e450282c5180700d600520a640160601c0056030750a000c0b4001e4080340c1e0310078500440000c1030184642c020b0303015008017038500d036a03440d285c4c18030a4a0345c0c0c9031101501d200c1c0c20205402240da00000d202400240c029038000e0460742011400c802401c10b0849050f5443d0300c425180c0301185039400041526003074a0030440120014000344141c42a0301010380c0c0e04079180c5482c0c1d00583d2208240c = true := by decide +kernel

theorem cover : BRFrame.Cov 690647482 690827338 := by
  have h0 := BRFrame.cov_init 690647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 690647482 ≤ n) (h2 : n < 690827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
