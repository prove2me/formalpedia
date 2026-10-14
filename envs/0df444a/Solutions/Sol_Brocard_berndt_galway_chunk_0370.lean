-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0370
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:27:51.564727+00:00
-- url     : https://prove2.me/submissions/03b9afcf-ec4d-4378-b9fa-a6e1900b7d7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 66366909 ≤ n < 66546765 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 66368159 1250 66366909 66366919
    0x40306110307081b04050a030b1b070c0605030c040302030102030f01090b0102070303140d020408100b0f061c0b130f021305031507050d023006220902060702090907090b 74
    0x1081c09480100229405004500c5504140c0165070f050780074030084800410380104200e6000fa5285405240f0007001c5461a041d002b0544001c00c0481c0d82500703c8065a074852140040750b420840d06031095007000d010510390320424007012005072400d00c000d5010f01c0700121000251b40c9010390a10684e07e000012a0464124440800010350440d0740103d044103894941074a134400003050500078003d55200d404140709001200f140200d4580c00a44142070550320100300000c460140280b510480021203125081422102c030300700d540360b1102c00c1e0407034024409403102c00d80404603801e41e0400444560072650000790000b4801180555400900042e406481640003c01402c816260300074007040621000088150b0038007100ea04603a101e101400c4c46000070f8480420030b01607882078450505a020190011400c6850403050902409102414922460010320103040180810b0b40003260800414440e00740141d91784c94245d071040000c000104030451500301e1003010b403009040c0041c012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 66369409 1250 66368159 66368161
    0x40b04020f070b04020d0209071e090f09090302010906020a02031b06010503060c37030c030b0a1202010302071a04120f1704050a050d03020d0b03120415051308030403061103 76
    0xd15100d2098030040b54102d4400071941d40c43d400819008100250001c0d404207140040001041d081440003070007452100000c0940040c42005880c040d4007801102a1605014810480f59005421101030707503100f840040303a201c1c00c40e0b543d1000d907000303a1562005a08045185070b56408090080034401d0200d00c0100171651501d1b01103500c0e443c025043c0302c0d0b13940001419010960301400d000c40041c0c12100030544400086480d8250b1516a000e403600082c202005000300e140f01c1d0040440c041170050000721502d1809103d903010400d2124124180342e001e00424001c66501030711500b000140c0a040c20143c5800d00c2c0ca0961803420b46105002e002c1c10101c4050241d43c09089090792542c42aa0345905032a40e04241d0310340460341400070020f02c070784411448070301c1c2c1c581c001d84909514100c084c0000e002c00c40826844020554011440c0902480100103e4000c2c50f4103212007005420541d00d170040400b000c0c0e6101c03807641c010107501e5100003000c200b040b449210390040f481201c0c2200b411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 66370659 1250 66369409 66369427
    0x6020c0105130e0414070b0406031404020f12010f0f0501030303060f060c02010503180303070e030601380f030403020c1503061f020c030d09080708030a05191b05010902040b0402 78
    0x60803041d80110501036440f100060204028400d01e0344540011104507440780c0d940d20641e01c540c1e4020300078640042d0030b0840d24003042139540510750085900420201d0154002024000e486600700402c4016640341c248108001e8054070680f030001204c0c40c3c1c00305241d811414041c05644030b592198030448030860b0108100341d0702454034444c42ea82468032956a4a403140102d00b581212803240030180800014020300d2a00301d000e41d040104280d05a0b0807507a600c14072940c411a0303004000340da85510f60b581048103411440003400c291f44100410341070244041301c410749508115000c401503800000c1822562502c01000c004101800040c2480c43c513000011030000702039411030121107070412648801060007071000d401c900501a044481c000c030081070080503400a44101455405581c1011410400220803103c100006460703080c035192010518140303040712051094100031425003400205a10741c02105100d07801132002041100c0f071401000304560004081d00e09c909d10401038514 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 66371909 1250 66370659 66370687
    0xe01051608010f0e0601050d0e01020703090b04050109060e0303040e1e090c0f04091104020a0e0f030106120206180307090207050606010206090d0e1306090212010801020a23090a080706020c0105 85
    0x800d50744820201c2c0c9585c2c80b41d500685540c000d980009008504080f2541001070055019010701c5020340e0b10045141e5480c0c07400c0e142882280034a40c0024942c4000703002c100d0150141c5074001802404581c1b03090741e02e56181d01e08803002cbe10200c001c8107141c2020601410362107044e54111034410301030011801400d000070030740d40300080d4240c05640c440d407980e005d2203032164035840c0a1f076000e0015540e8000c40c1800401040c0111105480744110740c405400c1401c05201342420344203100000300300a42280c00b0404142c004100c0300c04c580d01c8582400c0c445807020700200b0300400f600d042c05600e0700358614040341803550081043e41154030203c100310301c0c8c1000042150301488941003003030404c044400400c0c00c215041c0d18801d000c034141200090649050303401403c6141ca4010810750340c0c0d8807501181d0a0344140d00c412000030790000040440074403061740b5181e1032078100916904d0003035084046030b101c1c502940904581e1704803540400c0802d405000e410340d031107001d2810b07600d01440065090 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 66373159 1250 66371909 66371939
    0x30a0f0f020d0e012309040612020906280312030b190905090106090204031214030106050f03280b040506060c0307080901020106050a0b0a0e040506060703031e0e0105160801 76
    0x7003111540e0f18081e07503400b5020201024540010240c2640b11690f292841070340603080c40e41c081d03481d00400160b0f00905800c520000380e40100044001d4a0710010003400e83c5040e021046001d0714002102d401040c4803806400551151107074150760b150290001d400c0f100d814080b0380c059016501140301e000841100d110640b80c690600080b66120110a40d0041c40e561704400701081c80060080180100e0712002c4182082c6640c030f00300484205640c0f009a0700084c442c03203000c81d0007070101c171025000b520051507010f090950014005480e8420200c10b0781c4501050b984c11a645851221140c181703801815401642581d000d031605002030f54442d84d910030644060440140030034140707841e0303100390401e5004003030040840060303640300c118104080e031280b00180c010942c0144055564145802414840c07080241811305001d89901c042d4040c0104900301023a00c41083e04106585503248640500034034010700004d0149846280d0b0714400302924007540034000c80d5070041101105541000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 66374409 1250 66373159 66373183
    0x12040b0627040602041d01030b070912080c0c0d0303020309010c11031206040605061314010207060906030e07031b170604050c011404050604030b06032a010e0a0308030405030a0f0f02 80
    0x1580720380d52241004002400756802144c503800a44120801104102c9420b6040c3d0b0b00400d07141c000c41d203034400283d44c1c1042903c01d00c0800410542400c010801281c00790154a99481c255100f85030100700003055100d200d0b408801082d4003005001c2800c10034860050021541c1c11b0081410f00b040c07554641d80e000d03050316810010460030000700151030300e0300306000515015200c2911401c140f14011014200c074008d000d1007802403509080b2940c030005000e000c40c0c01940790300c01280c1c14050b0850161500180c015503034032420380300100081c401d00040421020030010b9040b100c3c14052a40580c0ac61008c4410750740e800a82800041400401d220f03a92100901307149081c01c0140e840c0034a82c0c025513200e190300080104000061149045ca828894075084040e2602c0c211403540e180b0102034503440c80b0559007003505191005c0c2d405690b205100400091425200340d039607940e80a10780d0700481341199581c00100355420400e801c01c4e080074081c5600c0c240f441094480c14030082d6116030000f44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 66375659 1250 66374409 66374479
    0x2010801090e010603050a050c03150c0406050703030212010b0a02070801020306060d27050106030b01171b13180308070507110405070e060a020f0601080a0c14011412040b06 76
    0xc1100341c1c42c00354440d00007103502178150342404030703542000c940754039880c000385003e8003038080c000760fa1032004003000c0d21030851569550b05003400d0640c01c503403503000107108409140d42004026608170421494a000388404083d4560ba144600802410085103920448040c3e005100b408140c0d41c074601a80c2c1c03915403014001542e0b142d488603d00c9d4158000309040c0a000c1c00070115800d100040d00b050046e0b034024862001240d98400c5905000c98041000d550641c022007406a003005554080da55181401409070002d840160010800c40d150305150b46c8865a004140908040c2c0118429a10600f241002410a00c49495225200412024481c81a680d0300005020107008218618403140c014002907100d60301040040d60b2982006401d50030b9114407000012030600009018070810707800120310b8103540c5412130315107010701c44090f142c0c10700a0303a421140148100702e001d001e202c22900000c1800d4103090815040821010b004c85000e28200d5488902180c404060101c40d080d0ba40340d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 66376909 1250 66375659 66375671
    0x90e1801090210030b0a0608040201080712110f0c0c0603010602030403110d060501030b060a050f030705010c110d0302031b01020f0a08060a0308030a0c1101020307020604020d1401050a05160201090201080109 91
    0x4110380103122046000394401034507690329450a50550005e001180f0649801c034031551501025030f00d40804940080c005403034000002d1045105961003180700b4501403010034400c50000d00030307009800071020b04400c01c5004c11070707076482001000702c4500b403802551340314515410301200039260300c03640c00040c0c164102c0b60910034083d01c0c0c0320641005942c02c034101300300c01d585030300d0700e800d86050a4494900c68810b0890215a5203005489400220001001400a0ba250000550303603140040400c0d900400702a0898501d0b4681254100c81c4601c03a501441c1c1d1421802c40865020206001c00c9545a01c14441f0189401c0710400710303803c666032410079034090340e1040300040391010305403c0248102c4021081c4950715045411050004040d500c54020101c4c000d40e40500700c0c001201c03a800183d1000f0043741c05801c3c9078440742030032401514800001202c2d0403d4600356030040d6040c0c55004ea0f25010030003080808030042441d2059440244600c0c4071760340008103420010300410300d0f0650303610 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 66378159 1250 66376909 66376951
    0x19030b010314030c0d0903020f0306010f05041d1509120705030a080603031b0f0d08060a0e1b120601090801020a02100b0406030611071a09030d09060e0105040c15090e 73
    0x82951000410b07901241d030305c5806650024040800c51204070b003e05400601210545004268541a0b40a00f041040c4203841c0c01e04000c09880345101d071906040c80c42c1e031581c941400611204201040040c10740c525820f0000c80c091400d2890110340c0020b80081c01003000003000401282c1d00d409541ca040f41160320342c940024154843e48900300e107114602d4010208503040820400040120041942c07503a0001110030b03161385c1c4044402c20351024001e40d0603c586c120810003544c104260070004075201c48900c003110b00941c4114044001c000101041264a40e40003500001070000f40b8025410a400c01030040e42c1c40b0584034040001c5074a8002d035400d183c4440d80400000c58004006100000c0e2480c42e500d025880600241c900e03404500302e0206104c030b00c011240c0101c0c2110000c5180c014032580f0a40140110325086a0868a0b90300d4101d0b002d40034014103001d540105d410081c1d0f140b408140520f82040c1502403814450030000c10440b0b480e03064030341da900403050110304451480039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 66379409 1250 66378159 66378163
    0x90f1b09040e030a0f090801090203100906020708030a09060606110604060504020102210d05100f0b030a0603020603041a0f090a080306060403060c050307030e010603150b040b09130219030b010314 86
    0x4140400c400344804a20104419405803550980c1d00e0701b43ca94214580c0c4a03010242a181804006901070b484030140006600301135004a0071240240c2c1c005040540035568210f15500a0b12422030140c1c03030b1000e40041c0501c41c420780c8001e01303ca0402151803165280e100b42c032480020000f51200b5074030400941964001d002041101222040344000304a01c7c0e03000e500c181e00310070719800d06145000e00062a680c1b04d000607a041e5600640b0740c40c042842c0015021080c0c2c0001c1115003001d0b00c0c0d4000100603100c1c02d0156001d00d20070415281d00c0341031001408405040144202180b642c1202484000c0780007007410034210b6040789015580341c1c4e854001c11904c0c1328641c401004039107071108442c00103500c400030318050b000c1070364180244042c0008980c2618000e0002600f11001c2001159201c0c409611030401c5040261011550841100001f498001c00f150707040329801d100a0f02004600d0310040c0c518403a44607545125200d420342e00d84041202c1d05000040030201c0c0710086a003000c0007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 66380659 1250 66379409 66379421
    0x2070e2203020c0301110c33130501020406080106080a05160f0e0a14030d02030319020706140901050618010f06030905160b1b030c0606010e0d02041a090f1b0904 71
    0x80a0003d1051b43c2c070311102060b0951141a4200150154002c1c84c013412400715689100c4030601d1150f100c3d544101c00206a95410250400300101482124400003c0c02030010301b0042c011501c65130101c1d85040030181c01c102c801442e8400703061501c0b0810641d5080d03440240c0c0c020300d440c42c28030070150603000b0641d4440354801c0750230b43c04103406000142d412083c0c0c58640300d01a050b410307500781461956050760b586c042a1421480449566003040068a560b40903100d210b005540c08613100d21038040307903600c2050980c0c10318801d9440710b0400025003454101103039030401803a039541715980742031042001d48402d4010325042541b560401410722108210b04060f54072620901412a07036210502c1c8030b00e03800110847c10385140d8000d2700c10f00306000b00954100c11005006000c4543d644c1004550a480050050380d022442e85462009a160741c8503c941c0440fa0500c104c082e84940c40c00c01c40900c50042000300b40c03080e0744042101000140303054001c000d2881440c0303610740805000180c05461 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 66381909 1250 66380659 66380683
    0x1403060f18010303030c0c0b04030c0f0204020d0c0e0d08090603060613090204051003020c060718170c040f0203100308072105030a150605040314250602070e220302 72
    0x4415800d86010328403007107860480340300b51001c100070405d0078070949083e419213502910580345000000c001c00d00500c030001c0384034411072501c6060917031540002e040381c114245070303000d2a641c2c80c40c4180d82900940801d4980604540e0000c41d201280d450040d5880350f1544680600701c040085841c0b0340f0b0358026101d40c0e43c0900312003920180c50b5022607000750042d2040324031407040c440410180c0782c060310848150206c0c08016003201e0f503411000f550060504003191206000b01140000d07140c640f08000c03480500500b000e803500740c0d55070003013000b1380304900070400202d031040003072180540c2100c2028044a40c0702031003544442060610140803001c01035003400d00e0b40300d210f00c00c1f0017580c4000214410b0031545410800403120203214006102c1d280070708030100704100014004200301c840c0454501002c00b00b280d060348000c02075409403440b6160840c82e603c1d2011030910050fa018444900030b0184884840954501b0b2020090703c04c9a0b40382c80f90401c0a020710340001c1c03520a000003034502d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 66383159 1250 66381909 66381919
    0x10e030d140d0207081903090c03020409050c0a060207030c05090c0a0f0509090a020d1404050606011805040c210b010f1b020a03030908010605060f03070503060d050601030b0a060603020702011403060f 88
    0x2c44c650400b170350140c2c0a5a0f0f4080d154051006100c40fa034003d01c00c481074180c010b845a85468103550a0000600c110f4900366014840c840d910100c030b948100d44000640703c04c1d40940302540ca14689080702c21810b4000e58481c6580ea401c002e0300c01e101c0415210707495254544010118940d00f0140c070b90380310f81020075030410000d5080182c0c03a06c59030020000041d240500b00306c10030401c0020106014140c40041c0190461030120b6150f6100303142450049040c50364900c1d50b150740e0400941240c020100301400b14180c0951448840785034411007895000c818014800b0303442c4080000c05200003a140107050040b550202004504c1c03c000c0b4880e166030180a090000d034a071700b40502070003a0303881144441d60800f0b001103450308001c8142c81010307441e299000d0031a15004d10a640f0781c1c10003096070340c0041c0d1221400011680420002c2d000303601910444050703003400360120382030f14600e42005003414010000080140d03840100d50025034a0171b481c0da9103d484840002e080c0790705d01c0035016070007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 66384409 1250 66383159 66383167
    0xb0103050d09080109020108041502040f081b06120c07060603080c0f190305162f010207060e01080f0718031b0801050105010801090e120315030c010e030d140d02 71
    0x8400100410107030031603260441940e03503540c0031078261221400b000380051008004100002d0342c020b801000101c00c004058180703901d035121b9508007415544010855801606440c039080c0200c41011031310f07c8240c1d0000d242c03810592081c0c1c1c100310080c01094003020002007040512405a00c000061030b0312001c42d6560381d0b244407d02c0d5036002584c0e8040480d00845005100040c0b0603254030841c00e42c181c407546c0c204811440300e00a50f00d4044401d882c0110342c845116410208000c545050030702c0e4207040300000e008500028580080794000c50240003980342c800b540c6a0700448402d9004101d00d40d4008240e440d211300300d5481c9008140340110300b20f0060003104101400030002501d034000354810700da880c2d4031001c5500383c80003071080501040c40d038001844205000d4000d02c401c0c07104402200c0d8800000500314919510490351580350450784007904425240c10700c440760058500f444e01900740c4003040000f90302d851076000300b1418090805081c8580445040688589485004085440d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 66385659 1250 66384409 66384413
    0x20d15021213050f0706090501050714060c07110f090406020d0902040c020a0201030f050105010903021504080304060809150403050d020703091a1903020304030903030e0f0406090204060e01020f0d03050c070b0103 93
    0x8200801e0b01c0807919030044031800d04241e01c001514004442442e56840480b514010040d54542e00c186c40981c0c2d40d000b060007400000c101000003602602400e4902943c0d449582040800000000315240c40b8bc0c0203200809460740d04c5480032078000d50003400c016510044060700800902c21507d00a40040c00c2000803e0943d4002c00c50008150003078030140720b4902c010701c42e00c003141d509014540c00b00d044c02c00140050305140d4200c859003c40c400312103280070f454a44007131950700254407000004900f02c0c03c01114030402c3c8588100c0611450b00b039590760030142c0d13020b012800382d078001c0c6130400c5e40820640c040c54844c0030150000c096000e400c210142e00d0180c540403561050103c40003031074810031501029032191007200d20690300f680e01e1400715821550210343c94010600705a0307010f01051245101c2e55598403403c001410b0221005a40d0b03032030102c01600041549240f141550040c54080c0074081c008201c646405241b807500254075034410340d0791007246c02004e03c050991814071001000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 66386909 1250 66385659 66385681
    0x105070801090c02151305030c060c040504060501020312041103010204030b010b180a06080a090312050901061707140d05010608030a020106030b1005130e0106120b040b06010804020d150212 83
    0x41610982c66050003c0c01440f402a6a0b58100002c025001000100050f0540e0f07030703682d41c10005074032460680746440b0300c2081c014640301c07003595038600c2104002403c105919040c0300340f07002000203002860402990b80c3c074560892400800c00f4013200c220240741000c956083d411038000d0340d48441d0b0f050255840c2e00c48000c0e1038204013090020b00d054850900e080c0d10b060610b49084a18668a4038407603a50850302c0b01c0a804103880450a1044200300d44150014a0150b82e12a1818500005003d03180a4500b2441d50703802e407000e102600400c0b4107106020060040c1d040120041d998002d442c81e440c640680100702e103912140560001248689100e5410340080e0200e80c0030f20300c201c0c07850300e50040301400c0c2030191284550004011050441c01c2909070011503228400100010b0410f6680e1007240340412900803c9a131000c580c01000704004040040580105c000c1c6000d28807864143d010a61a100c41403000c1c01c44014148003d284840640449001e000301861419840c240400001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 66388159 1250 66386909 66386911
    0x60602030d0608030c07031e1202030306030d0801080d03020c03040906030b0f010605040b030f04061b030f0e0105040807020108090c042903010b01050d090c0302030a03020c01020f01020a05031909020301050708 92
    0x741ca03908141c0005a0307000008166000c26201e4006010942d01c3c56480800c02050008450384101010314600e02049104200711181821074003c0c65603031808000300350418800300411010301580000500800300300081100c0c0c0c2c04003c1c28010b95841c8003003440c074a14020b641c882c5113440c2c100741022041121120880740101040340c8586841d03600d0300707815a0280101d00a001400e03000388006101c0e1142c800300349800c180544c400240c907003100400d94400091703040c42c00300800d44a103101240d2170031a20441010380f0b80500200003906140d5a0001b8034412070b900030f81002440780c0030448202e01404100d1107040014020843d03c400020f1902080c0c41c05005c003240c150301d4404210050606000d0135801100582d201440c000c8081c4401c8020142101d05031101c403041080031005072400c121420100e40a900141140100c00c800245019140c00d441e007070690042c00b92a040c00e4103c800e0707a4000d181040c180d283c00c0d14966000000740040c11b8040d525600709028020102d0f0018045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 66389409 1250 66388159 66388177
    0x11b030c0207150e0f0d0f0308090c19090c180f0303090e0709050603090a0221010513030807080c300a020f030103060b0f18090636070906060203 64
    0x1c2c4040a03998201a1022407000e2484070124800d000c910100b0301e4403110601c2030800080400d5280d00950716003695410a5402c01c44c0414100c0040c0004100c0420411046680440d1400046a0070745c0e0713450b141075010b10401c0903043c0c0f0361007580c5032140a00f250b9051108003070501d9690f1795071400400142003081c0f20540115060035008034040144010542c8500265110341c802a450103043c040c8a500080880d080360043c52034450041c0d07198146900c40c201c5d0b6041700351100041c4d030651421180080c0088002e0b0403034081d44800250480b03501e0f64041c1540c01d01c01002d84c3d417040d540e901ca200c0c85240c1c035604401d0901407045010003103444c00caa050945900304031540c0e00301414040b442000c422008149091004100299154000721900c0c80d025203005084034020b80891000807103800c400c50540f2249007000341f0310a08110540c0e21030910844003908018006d18099100b84498040b201c00e201850144040030040152100a01031000c0c20091146d0761078009469030012006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 66390659 1250 66389409 66389413
    0x50c040e04050705190821040815040c0e01030506040f03020106050a0803031006020615120a020909030301030b160507020f0a0b0c070501140903070509040c050307090914070e0c0903011b030c02 85
    0x303200c0d450707650f100b03006c1ea00c0c03080007014904c0c82040c3c1e0519080d401c0031036402107030007080042020b42c03045c0540315003241d0403521070002d420241b0380200907450310707000245154040e600400100c4c1001078590f801c99007101c074481c000800c82c10203d000d050309803c01600514003080010382100c000000390301c600d00700b070b80302e04419480d204100c4e2260740948242d00d01182c110044105842c0c001d0107891316800070030031106049881d5001c0f924891044074400e840d9000400108180701115090710b83c004225007054a006001c5500548030780900000030303004280301e1036655030b652103094202001d0309080e5455a1100f00c2104111743d40c0c0b030341e03008071800216010800f2030010420340554603941ca000b00600320450801042c0820004001c0081c0c5010341a000e00180f20b4030b042c00900c001d0a096280441c0c1c0d15071500b0020041c596007004520207038042041081500901c0401d02d03000104661441d41e61308101c00024050a01d80d5040ba842002c4480440000354040d13108206001d810b0302 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 66391909 1250 66390659 66390679
    0xb0c0c1b011106010806010501110705040603050a0b011203050f0d09150b0a08060412050901050403140303040209010b030f0601081b03100f2c04140307060c0306050301090302030706050c040e04050705 88
    0xb04071a1900300a114041c01070744410010301040d80200c00e006182c41080044079030980d0780744006001c2d0b864a910070f8801c0c0d008510711006120803025042d0240400e2644aa690600c0343d0b0000c1181c481e045000f0001280460384040d50015034000074071190704510018002d05e0751a2080c4000c12a15010342c0c80b82042030310010304071a0220b00c4511441d0031001d94000c0b003c200c40d05507031503407041003924100881000080700080d6a1b0f04680c000200c50001103499240070300c14084c8440341030b000320440c07100c14410007400c40008008254000002e00c0c240c3c41903202c1c12003000b00302c0e0500038000207100000c170170045510391003286da400325030741042400794850350340080039074520485d50603c54480000501503056040b80050070382113842640d2042c0f81e4080c03030000c1400c0d5000708030111b90aa0b26509455070095040c0545009408124001c02500003156401b03582c2c0d03c10110003e062030f44800000b09003029030400e86008094951b03103190b40345402d142c03007625002036004040c0300e201c4001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 66393159 1250 66391909 66391937
    0x90e042123030915070c0302060601030b130c02100603060e0d0c150b01090e0f09070f2108070203060115030f1a190906060e01020c09070504030b0c0c1b01 68
    0x203164424050182141910141c54540e2030220341c0c001044180503206018a09680c070250080e66171185035aa580c121022030103207402420688041c1c1503038100740c100301c0e8820030b035503d001c2072025804480b04006807007100d11100b82d0034207480042c07102086241c07a40010902c8000d03002000310340004000c1e50001c0805580a031041000c01c2400380c03410380021920341d1510140d501154401105050a101241d80e607101100301000440320200c0034140c11044c4203445d81d007042014090034400d107400104904000e409000100e480540e100313035244080070102803081e2007044034407050300601034505a6031994826481c0000d540d900c1c00010746000c1490042455900c030340ca250700043d07085100c091000408010350307820384511941200c9070480f00042c828441c0c2c414200184140d032550000c041c000c42c0060704100d2941d00c042c0c010000c40d030401c82181d034020111411340794007180c103014545a00000d00760901440c10307404114800c44400001c2101c1640f0400c4461000740c0e202c404117800c00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 66394409 1250 66393159 66393167
    0xb040e1b040c171510030f0c11030f0d020706090f020a0605030615030603031201030c05010f02030f040b07031202120406051806010312050c1b030708030301080304090c090e0421 78
    0xb00076040c0001d0031180d0b035034407000c1505012070b0084080011500c06094203400641c49002c8281d0704030100350748034051414080c1c18081c0d1550f000319824035121040040c0c51741c548a200b00b0031004028540040d002401c41400d070b0543d1801a00410b04101c1c00d01c2a02e089058501003200c2684500701345140020400c3c8288100e034810783e400b8020883da4068410002c2e00d64001900081d410b0006126650001180003581e9000714000e0b0035060301586401c00245c0740d0420f250040e0300315003080068032125641c0f10b0444044904480308103655103102c0c24202c492170b801003030049216000241882c814080c88040707600441c00794400300080c3d207542101c04d00781281e0140610039038002c43c2c010000300f04418540450b41c3d0243c14600d140411243e0784030700300301c2c02050303030260240101c0761554203040801c50500a03026400095185504000585a4a020324072a10340d40a89992840300010700c07881c1d1a50007404501c52007160b5080c24602040b1510070700292814441c0e079401c0310840c0b40d01c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 66395659 1250 66394409 66394421
    0x603060510020714220b0108070c020901030b0c070803010b09151602131e09150506010914150406120f0506011b06020403050d020d0801230105030403030b040e1b04 72
    0x4190010010540390403004c02d065140f40700c489600189000741c5002c510181c05124101400003140010030140d40400500b00d25000703000c850400c103011500c5401600d550030354a040d070b500b144264116a50b1820100c040c0d100c0c20000030b00d40c61010000044212000010f0070003c1c1080317501c3c1d12104000501309000f8000c854050b00c0300034005104a0150074101d46c0c01038907040c005804200e0040e030543d00a2090707408145c0304030321941d4441c1d410500c0f0009031201c00e460b00400090081e810541e00003054040180900101c0c10b1030300143e0109a038a80c0d11240f80c80341d208155985803541c604010b4000080307010303101125800d2a06114140f601445050303c101816124524080b0b003401041031484003070308040b03d40c0e6508100200208208000700c0008407055030084c039046030038010040c00c2901c1a841106080a500070743e00481d203038400480003c2d40d080c60305da512580c80782821005802c14921880d04541340a0b59080701d400c1c0441c0414010a25500720448120301406110841310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 66396909 1250 66395659 66395689
    0x5030a02150d1b0e0109050a26010b0307030f05060f0f070c1104050a09020a0806070e0607060b0d05070501020123131406010902030a0f0203070e010e0103060314030406030605 77
    0x18902100403100079001c0c0600001102d02900143c1540020125540b41c0d42000c958804600e0050b002c03851581d002d03036150080c00c000c7c1d940340d20040c60200040c049510840003440802050f5103101c801d160250720001c0f035540000e08440c041c960341e05010702850140c0c881510719004240000c0c140d824141600c5018043c546e018004950b15034a04541410100004445101c046500d814607076542c0d0049500444103070b5000030302c08e02d47d40f04201b107100107540305c44840d0308903404014050b9003001000840e40e03010364280b03680c0c2d010343c546003000f07203141c052203540000c2c0b0802610174001c0010f80c107070030307151300b03070000c00c218203140550801501040318400005d071250400544070412079801456114400c42036031910344090f036000382c00c04000360071062086601008101070384030380d80901b0214101c17495003145141040003000341a901c41201d5035041c0980070a144007164800d5101c3c500a54100701000100e00380003a0041c6c40303a0051060780d00290821801044c645080d001c2c08038002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 66398159 1250 66396909 66396919
    0x60201050708040b070c0506090102031f03030203040e1312020f0d0c0c05060f0c03030c070606050f0603270114040c170a060f0605060a02031c020a09090b03010603051606080105030a02 81
    0x350b5141c4d030b112504400280304000700060072407224001882040410b00601c501400540ca1f4a494898041045075a07180003000b040d040c10f0400100340c010003120191100d9071f4034203070155941031064107000c0390004020700e1703600400c200024155000c50f00c010503403110000c0e2130802056500841d284c0080a03030183c080c009110b0704200c18603100c0d000f080e6640500704903c0c2094010070b402400c58100300d03000704038840c0004000013002018440c00c0301620045505c5e81141c000c0d00b001c50513601005082d25850003103902d00941c1001f01017445400c00c0c6c800360013840403a103415806020800251021243c40d0380d2502c01088040c61840280d2110100c039000b409454129290480501103485c1c0d40d02031541c0d50311000c96682c80f600c2c010304054100c0d4000b50341d52260a20388851034081586507000f058810b114080c04194020480b01c201c07600018081034a00030800064010030a0f54001002d5201f080400e40c07028540300421400c4914940310014160f85e01c00c00d1540754241c0d810700070b41c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 66399409 1250 66398159 66398161
    0x1d150f0114040207060e010204031214040303050405010c020d050f01090605090607080f040f02100c0b1024050418050412020f0a0f050a1b0816120605060315010915060201050708 78
    0x3030708240d8060b24413507016034804034468624203121400c99001350025624070030f0003101d0201c49600104030700a01450b000c0c485240600c2e40c1c800501d2400740703000710b504201020303100000355901c0100000e8001d070028180e510400c80b07101d200c2e000308007503401102e2190801e00060340c07810012074018030550144d16400790940ea440306a00003a080100116950080650780001584400708a00c00d01469a101c4901240141c1800040d01c20014130818200085260520000142082e2550403494880c0b1018203598191300a940c40d00070794104a0100c8000800100408442c1d0021030245018070f60301013140800001c00c81e156080907803a040991300c0081d20100040c940300040440a0181098a03c10b02482d99180820a01030720440030020002e48140300d003540500070118103184910501d4a55032409031001c0300c15091120150656130342e240015803030780f420b11040c403104e00701c41c1d8406c0e071642e1514a1080185100c03441d10041810842000c00e029005111341405000d554580c5016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 66400659 1250 66399409 66399449
    0xd050408012d0b01050d02030a0225020a060503070207031b1403030a080103031d03030a031a0301090203060f041703100905011202061603140706020702030d0512010e0702011d150f01 80
    0x240003000c10644c10030a080041000070b00c6144059402500e1100c2d0160740c5032010300010840e0320f80b07100080442c800320443c007001603035002920000c564180c2070090306c0e6543c1030801d03800d0011681c070141440310003c07200c40c11070143c0c2c5509016202c015400c03801c0740c000c00040c181d6901500801c4004241200014000302c0e0040d01d0b004800b4020034424003441000d2000700341140c20074084c240c040ac2e12140007071060050160520a100390982c020014110356800003540d480c030141051501d04114070104003400b0000d08291140801c2011039a1750b81848110300c442507829100e0f43c030584e0f1400d000400c8802081f2220500d884c2c008060a041150001002c0400d9001d110200c041c01011160500700250f080d001e041d0050250100503200c075105d00625007020b420000290400000b00042c0000c13810300d0101030305451a0425140c0f4907901c07000140d0041c04070361031000000f0181e0805c0c2012010002c0c45a800360404400680503403202101907411500c2800b4125030a00c0c2c56482020f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 66401909 1250 66400659 66400661
    0x120f0307052b050f0c0a02062d0a09050d020301060801060b0c0f0309090a0c030f060b090a080d021c0306030206120a1a13020705150103050a03080702120414120d050408012d 76
    0x741d412441c0b420f40d03103864a10b50020b0800e501002c591480002000009d00140944490214800d540000468900000500000c20b02c840c80e008461058130782410038403e544095000c04082d1000307030700070815541c9528041c0c40a0300241e00c11183e40c0b155442620303503820040260303111440007402d2038040e03494903048840030340765184200040699400710b02800100707e00404008203008070443e03541741190414011b8a14168204001c10392102a0039508a5800291391051607400051403c03c2000f402c411005011542c1c00694003a00c0400e0410b4040d0380c665150340282d0403401d04012103c01c02800d084181110005d0a50109021040540000141e001014940c0c42441541c084601c501e101015030102a04255101c0e40146229410140c000c3e0382a504070140b0300062100b503c0403801d61440d0f01c61400380c00d040380350b01501c005040d19218030707440248041100741c03503601482500080c9642c1152145103469800c110032000c2c00003084820044412907056186100c00503010900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 66403159 1250 66401909 66401917
    0x16060905010e130f06090b030105060906010e12010c0807030e0d08040201050a0504120507050102121303020d06020d0e010b0307051507080922060f0f0e06120f0307052b050f 76
    0x5400103110701241422600d2803007040c0c41005140350000329107041c640b14070b003203070b500b40007c40c00781e8540310a01006039240c02c0d060f980000c003440c0154905007054081048850aa000358060b0360030b00d0041c1108135003080200384901d80c9607800b0006000403010803075480c1a920070810203e1300c8d800105001d9403240005018800c100d0402510706940e441d0700d40d00640440c0b00c207031902d03000604140706039a41031010079001010448128149904a6218519040c1c0381c40001e211b841d400e9004403c00400360141d0355024000e00c41003041c080d04001c003501802620990500c07a01482c41c1c0880c039440c040d28256501300304070401e5401d1400c16516802c180c1d105095495000d072508150304580283e0460703002c1000300f0798a01061141c41c04003940007408842d0024103000040000038011220844c0903c1d5101e901112900c401d400da082c10b4a0a00240c0506c0d60f109000c00911132041c0320b00051452695045000c03101c500600c161003103242d691501c1075150000340b041102d00d50304006000a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 66404409 1250 66403159 66403187
    0x180204030f0f0221030d140705190918090209061c032f0307031103030601320d090203060105030309010f0c11130c020c0a0f120c0e0c09031606090501 66
    0xa401048000f040200b04c01c640141d40302c650000450170b104071114012a5140301140b600e01e407007400e0001001d0000e0041034296050000e543c0d0b40100304a11032001d0000900001d0f0500d001c84141f214148064080030310148d004076503001c0498860300307000d1340c1d5045010044455015060590b5411646c00c1c00401e41910001554410003121020354040350580f400100019541c600061401034a41d8110500d00840d94205108005031640c00264411220081c040c040c16044900c13810701138800405802140c0d100000b042050034802e0f1503001e904118000c4003221116071362101010390ba8401c0d17801c9075000580300040f60f500310b8050019105481d126030080303a40c80c000000410b642c4c01c3c0040380c840c00e00d40c50b9a20003041d19010300100145010586142c0c480320b082c1020521210414030901e6420364001c01240d0070300107030700a450f0282c0544980e00000d81082c071900740c00ea030014803a6901c43d0051904105515014003500c0c0c04841c03081d240d00c0c02d10b83ca010015200e401c150b42c03039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 66405659 1250 66404409 66404419
    0xb010e0307150507060f06060201051f0e060d1506081011090d0f020a08010908030f060105160803061201090b150105040305070e0c0c010c0f021c0e0402070201020f060c04180204030f0f02 82
    0x342c201b41887e00404000e81120b5000040b02c1c6050540300101c00c0d0400c030041c4810280030402d000f84171105003c960300c0242541c1410a10155140c000201c090046010040724a004070120b01d1503c08035200310300700046401031000043c1000818418440c0590980d48011602508000151100c400c500e0490008210b0346005940d0500320b801c6d162140c208595020002042110245100c890320350010420301e00b907418403075110140e011410700c0c5000a03050309804030000d000c995801045e0000074580701c00a10001101b4604048244001e0301c0044484a5202e9028842c3d4403450a4408aa03000002002c007a445c05500c00d40c520405000e40c0d518480400c52000040002d0180f020940d04550740e06a83c1d0b10101002070600e640b6a498140d00700c3c5c1a0682c0c0005644502c42c3c43d50041c04680060392043c1c41c0c40141d1411030790702c4010010b4003484082000c801407072400b90045134000250b1503c400100e200943c100d11442c00b00404a002c1c02c40c000002c15600106408400d202801e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 66406909 1250 66405659 66405671
    0x1020c0427060906050114010219210507050f0a150209010c210801150509040e0705040509031c0204032a03020901080109200307030b09070e01090b010e030715050706 73
    0x5141c0d2291a901e01d09841003034841004204021441c45070324010300b22205d8420103c4402e41c0000c0d01d504500148100104001c0f0346082449850b20a6540d41d66407820418200380741401e0107451504140d4044c0d60900420900a1a03510049612200c82e68004a100032826000300b01400030340008214504120000604000091040384441e85411200030001404c0340e10003802052042c050b08880f107010050813864210742e4020064420440040b600070034541d098505d410b04d401c000398806988a8200720074400030040110042500119070310200c03000c600340507000c0d0f0aa20542c4801899107100d0400740b5031030320146800b03c05e0184c182a002020700d50340d400046034003001780c001202503555400e0350b004208059020368414038458400d007a02c81d250070300180d15909188009451280c400380007903007420f001d2003420f028046655171340941c3e584503000800101400c10f00075011402e6240c10622a160000d803003401c03100c9032143d107000851508e1007160710703401289045039801c1d103542d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 66408159 1250 66406909 66406961
    0x302030c0106090207060f09030503150d06020a0c17070b041101020109050a0506070201060f0510030c0c050109050a0c0501081b0c0304030213051b070302073c030308070302040501020c04 82
    0xc01510014448401c0240c1c80f4400c40c01c10b5001c1f00c004c6007040420f03174504410307000040c2e04a17040c2d039806900b0303c480e40d10031048140070840351007003900010011403000488008042d005950680894011003500c1c600202c0c9100021842c81080805000035400d07800003000910011a020403120040c0700100c0e15071001c1c3c0d610f5107040402002120641c10140c10080780350f81c2485031500822380c070300e100c080140c03070000807600c180c000301002010951204020314440d4095202802007ea01000821241c240c40c01c11503100c9454800466010316404e1001580b588250015400388040c000e042440160103c0107102c150302ca210355a045010910000001d80d0b0f030f4400800c000c0c1d0b0308040104007494841d103110202c1c05003003000c42904200303000c0d03100402c0d4005400340c26140100b00948001203140c45143d500258104a9142d180e0410808003210103104215411244281c840981d55200c801d0b041d4161f0056026072401a8401e00c090207180c07403d41c20120401000f0001001428a12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 66409409 1250 66408159 66408161
    0x5030304051f0c090308210901060305060109050405030d1508070303020309100507083a0b01020c0108060d020f06070507061d03010203070f0c050709051602100e190302030c01 77
    0x855007550907801c1500c00001d820b048440c0c1c82d038085805001008001070741400682141c2c040c1c00090050a00841e1090b080390000024103070400b2410b1400341c0c0391030620305045c003070030741800229080d0041c40c000240c075003110301032107002d554024007442c1800300781e541c55001402c3ca441000044c0300c130814005401c503000c2c80074001450003076004d9a030b12801002402040700d0910060010400c0400544022400b000203580c60b840b14984074608a803180507800200a82d000103042d5920703210f030400c690002c2550300a0780031040a13020386403041c02040054030b100108449080c2c001c080d0b858620014070b0441c0390f51580c6140240038a00b000669116a0300c0d0282c150060713000f00300c031002e440307002e15054501c13a101c121b808c5000703616600d0304800044c07180080c68042400e03c0010007280080090074800440640103501040103240382c88007540a411440154403005401034049298400320300e03001c0c2e045074050a8000b4807201c10f4511031001c6400a0070001e030110300007400048129882 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 66410659 1250 66409409 66409411
    0x12021305060a03020a110f0a0b07120f020702010f09080c010c170301062105010f0e0411030f100605030307110f0a03060606020703120806030a020f0f040609020315120c040b010309050303 82
    0x11560016100c4141700006401c0302d408503582d0142d03605c03495282075241400034001c0543c035403003000311407a41c40f0303801c045e5010060a920703901414100003990070f00840c40d44c090010356001f40c1c0d039864002c50b140d40544428455001d105000c0c0c02001440c5c01d41d50069607840b1b00c10f44500461040003804101002c0300e03400070b0b0011400202c1d5131400440841c0b034146000d03c043c64000d000c002c9545001e2b048020098180300d50001c008007840010140039032104243d422460207001d83c2e4501d914905d04580b1101c003242d090001c2454010042010b06000050700d000ea5840040625407001a400300003a2034400c090065004440090120005159000d004c005000c507030014403041d411854940500118458000700304821038041059660b03001071320a05054050f01c90512070030300ca0002c030f134540c03031501030700354000b401c100b00014640d880b0790045100d040d56035101d800f64000c10040085180030894401200d602c03400c00c072005442c05510914100c0d905050009520b40a90743d42c90031a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 66411909 1250 66410659 66410677
    0xb0f0301080105221e02030102030a050a0501080a0803060607060e1c0f05090d02010c2618030303041a060307050901060309050601050102010e0316061401080714030c011202130506 79
    0x4004001001149802d018a5411421500d031006000c00c0c0a002c640700001540000740001d6241c8140303000341030f400c03a01c0e01740c0160041c00070b541d0ba26004000201a26060f544405060314102c000a000c4101140c41c0005641c0540c07414035540f68001049101d41040c117080d222941c0d100c1a80d502c00e01c040080b1041c040441e2883c00c0350000c2484c002d003c0210030f01c0d00c00140a0100b14000071940c03410030556120780d090038240c031a0013841c1850400910a019602854959102ca50032261008806801c01180d9003071489200303004001455102d000035500207180c4c8241c02c01009640d0f0080040d65071161000e821520207665035000104a01c40c282c3c00100400d0307079000008140403050081d11f014010a0000340003200004030141c2d41c0e84038403099103005508803841141005480d030407080d07911030000680b004558450005545030390840c802d04450503c03101d5800748605000c01d000d002064140c68402030401007060400295010f548803221215031080086815a1100043c0407110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 66413159 1250 66411909 66411937
    0x90405070e011d0105400e150a06200607110601050a06020c1509031506090f010303020d0302070c080601060906090e0f04121e03020306040b0303090312090118031b05060c0c06030c040b 81
    0x600d00b014070034110a001d454094039852000001523a030b100c0341c2000301110300c1c91401055180d01c2c00840d41c0401182e529505a030b000b0442403003801c0d07a1141700c02c0a00142207007560b0f60340e40d80c0c2c01081803e403110310814001d0780007001c0400c02464452064202d001c0410b001030710b000c41c5070000900380301e652080b80000c14950700611940c3c0c10311035680799101c80c0300c000c1c110440d41103440180d0b441c0d2450440a040540020300c41c2c04000c49411450000c01e90603040701d11550b100e007005001294180110000a0100200003841c4407149047c14003940403034107213440380d48464031241110202882c9140512a12030200000f480d420140100e90a00c240c0d001038590900004020980d600d05c8030451080d8000d00501c505540c01144045000124110341d940d50489840140c514140501c06100d0041e01000008240400c00140c8441540e50b603020307241c0740e074441c01081114080c6103074502950b800340d1400720f07050401c90002c68025008098403410150394180c41c160340e070b024503d030359091 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 66414409 1250 66413159 66413287
    0x161e1b06110d120b0105130e01050f0316030809012a0204060f0f050f0f06030103030f03140c19050415021506010804080f070305090405070e011d0105 66
    0x24680c4000d9184603400400c1c0500128086403100a0818803030301100e266469031940c02c51090b0380554103ea98002803814820042c903500d0200303101c0b0781070034400c150003a50756001c04562417401080d2044000320b1100c00e0b01e0180d05544032400349030450a03415052291000d49074001c624000d0780e403050201e6250850381d5039112841440251910b5078000301c8141c0e0800c1c004c0c40403a15002401c01a110242c4003c1b201c500c5100000e00c2300d081c04081c0ba90030020000012040c590701c81c0704040c0d8540700da24144030058039180041148101210015a040b03010701400752031140202020301645406d0ae07046041c685c5810711595482c4080f002c5c03401691002602800151810400d0303a400b542c01d0815071b65901c1e2075245e002183c4148070a0f00e911000c0080c041d001c00d80180180c48540c040604200076516080301d014003c1c4c40c0c03250001d0301154181c1000308101824a00c00407400c40f0680d0362608010b04414818402180500c260010180c031186108401060b0741e00a00017200c400120b00d89 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 66415659 1250 66414409 66414419
    0x61807090b191401022509020d060905070c2d02060d0b040e0a0c0b04060801030206220b071505070219030201090803040503030f07080105030309092a1b03161e1b 71
    0x1070701945801d2100800700b01b4500d60100048200c012045074440b90001d643c0f0b002420341c9070003c00311500705482c040d150030b05014995034011072040704540b04100c401c06000750104503000c1003c1e8818144a422039500184005050920203400302000310b602c04900020510000f0b0240c5a0f0514a00707001d40c410a6480c05002091031103800038540c1e4040140342030708008004050340014040a4007a010005a8480009400c80301c0804448450600c0301740325150f12000405a100d0a000c2d5900b10300740d00d20300040c6695103e0b140c0184038603001003062170007215501c203904501c0d54007036082d550384078140d002080e0703244001c6108600c120061680ea01d094840e022a40a001c1c11402c10000d910006000c075450001c102c800502c400c0f5120301c113030398903c07070421070b10320b0110040700091010090100090307440d24050f00d02a202c0242e5450001d03e80b41c01143c0e24000d91269014288110070008040781c0030103440a103e6a95030604074034685079071150f03010320901001e0000c00e11900141004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 66416909 1250 66415659 66415663
    0x80601030f05090606060313060c03061406090d02010e060d05010306020c1c080103080708160c0e01120c0306020c01060506030705030a05010e0c1801120903020c03061807090b19140102 81
    0x111881e1107003010030860030aa103500c1e90b81d0400810250061000201107103041121140250b00d59038402c8080c8102961250014060b01092064441008200c0e80203015440c14070140c800140d40604400d00d400f01c2c0d03400444a2601c80749a154002d0f8003080070080000007805003501039802504050381d1036611245d65850000981c0b80840d1060103145964505a03116010b103045070717085259103440300c4450410480343e2241221008003a50024181020130150900d85c5045030300500c943c85c444c1e83d030341209c0d180100004a000b44601c286120900001701d443d03014200d0755151000000d010364503a400b2230400d0f40705543c20030114001000708102c480150242a001d000c403088810401c1c14130300103425890080f1003c00781e03015403d01c840055030f48501014050541c5108080c88007100318180652582690310200e4020300444000410038400c070b1895040040a01c1c00074850035107003207a040010116444025880f44024008032406182c100c05140a0b1032410400103c40c02141c2c0064 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 66418159 1250 66416909 66416921
    0x402250b0603030406080103080901090e0103110306091606050c030403020303121b070314090f03070b070605060d031403041a010b0d200301051903050319020d0c0c030602070213090308060103 84
    0x40e200e0f0303200304014004140d0044400341142c3d40000100e40f1586000010380341044503400100d08145088000414400000c00200c0c0c001415015140640c5030034001c9511152107180e40c011031001030804000440c8108000c283e103946e03031810b0703905080d120b5000a045600102054070490718540070b01c8081032980c00600410380d600e894151404880b503502401c0324090a20081d100304021130010166150b115518000f080000d090341e4466403a01544c00303507508039a10986003103103071000044660170066001e841e10764040e16003d290910100d0010b50307580c8018012140300361b8041140d00c0c01815652600d028100035078600d074a034a0842903603001c603070a0110001001003a0800301d400c0001030b000f00c0c3c1c19a00b090350780c00400e03010680481c0d8540700035800104035120002da50710100c0350018000c80c900c80e00f507080c0c482d0f40c02000310448a040c0000c038080e1070131190b0303c01080011040e90041c40c0540c4040c160001c40c00d0044080030417504000002d0300450709080c01c1006075030340b45c441c1d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 66419409 1250 66418159 66418171
    0x30905062805040f08210109020c0c010903080919170c10050304020108061509030615150703020607030216021305070806041e0b1f0306032612060402250b 68
    0x70003580c07a00703480d458510140e05101500417a4002806904048100041c00ca0b0400131078400980c0d50751001340d01c1c003d41c48100088042d019040d4020300e00e612650302c1c54100d0f90419070aa040c40610001c00140c114881d07418207180703044100000325100c500c1e03003903e008541d0a0242c140400c40310b06114801e4211110385040080030800c110043c0e07006800d407a0488019611b054003464805c000d010703070b44036840700c46605201360380420000507500b0080d11009602560425030782d50b1345954140c0d1030700a0b18401005600300c0d1001030465403003075003e050322003c2445104880c0949401264001400f01400c1c3c181c142c40d9410490b0403504048499040202903a0801800c4100c010018840402240c4003415584074040d00401d59075a08803164641c110003541180d45141c14800341c0200218841140c12041c41070302c0301d08241c0c080e603901418008541801c0d15081c01d0399105402d00600401240d4030603030a00c00c0d154075400741010b0a00c0342d80c6591251007101e99600341641109402000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 66420659 1250 66419409 66419411
    0xe0c10080108070603380307120203010c03060e04030503061f08040501060b04050102120c01061d0f090a0809010c030c0c0602160f050105070305070f06090606090e07080d050a0309050628 82
    0x8600c00b03015801c810700c016503540d490444d000101b9407070300881d040400000d142d051050040201c1d0903864112401c074154402c5000308456043c5110aa00703848440c82420501492030380002c6c0800d0240c001568044c00c02410030f2014800c483d040200003c4c04291304000980300805c000810000b40300d194090480d4241450501d4a0040000d580e2500108100c01c41000480c5041c0400403d412060207452900d0080311f8840d004502c1516610044880c84e1300090280003140c40c80b007002c650044503582111510b4686030317041d40151000c0c0e0b942c1c6801c030b040202440020003c02c1d426024074014200a40c003422510080410003801c0064503002520814280e680400050380c00c4000c440c1c24031f40c5400e103503448542c0e9040c8076a040c4601e40e006010709042050202c1005041e40c4810f00f51400c402d420000780c0d0910300342655415840c0503180140e803000a050038a2070244015002a1160346030200798140e6990702c01d400c110040d140d064454005510000c041c0309905109111080a910 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 66421909 1250 66420659 66420671
    0x3050319090521090301020315010210021c050402010e030a0c061d090708130c030807120503060a05060327010510050d11010c060e010c0c0611040302010e040e0c10080108070603 78
    0x39056203c1510901d0390071150b010300b000c404503440d0070b810303200d40200c001c0c02107480e40780c01e22440010080100540d801030180300b20f800703c00422031003640c03004403603230844180102500048a00900000c0d10603410f224003400ca0100d00d0303904001c10700c6400d11520803003411901d04440030700310300410382c800c81d040f03004164a0f03003d035203c12420303076803210192a006d80e03281c443ca82040d13415910308102074980002180c0110038405084010800c0ca031040c00b41443d90032501204640f58042a621140d0241c0010401c0080b403600da000340d0341041440c1c884003414020b0184070020b03030000e800c16203200c1c4d44400411210001120b000c000800303003a078115684140702d5991800c0c500000c642d43d03041c07000a0440005008103548070191a6451340002c202c801080200a04241580c960881d8041e061440880d903e00800090b80c040700ea040e142c00b0380001d40441000050b02071480000c1240c03240b01140701290f0349400010911903a5600c0728052541441d4409040460a07000501850f00b444 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 66423159 1250 66421909 66421913
    0x501020a0f0204110c01090506011a0d0903050d320402060412051608060a0501061b11040902090c0a0e0901050f010e0a0f06030f15060e09040c120305031909 69
    0x8242100300340da010580c0059030020b0300c0003038001c0c075100803c042035010200704090a5481540010080d07401081150394583e030750b0700084003221202074011101c43c414482c180407606140c10a00c1075901c07074244641000384d400381c07840858110158a42850144140d90301030321401c201e42c80341010300d03a034136400c0910b800d401103403d6101e00c0c42900480e20710502c050044c080c4c240300307040080d40c4801c1c0c8111440c0e610314040e6500c000c1511b80e03684031460100002031150007520240707c81e00426440070b07c1e01c0354940f508000d0400da00c0203d50003a89a4817014016501c000d00984501e854400e05900c1e150718050060a081c50f01c1941c81c01429202c0c0140250f0b503030300c4034810041e5001d1034003140401351000803c0c020240c541c4003007802c4001e480301041e802e8040e0004500412911020007480d540400319800d1820140b09040103c0c900010845440c2401961150700c540502d01140e44035588101d01166800a40d00c2030f800140084103204c0c0d0074040da00781c00c10341c8841c5402407103192002c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 66424409 1250 66423159 66423163
    0xf021809040b0f0c07120c02190e010605180a0801051b07020a0306051f0801051602031908060a0f030609030801090b030709150806092118040209010c02030303042307050102 76
    0xe003c0c07400c160a60f0000440c0110460101c4440359804541c803465100d01100140c050791410400f00c3c03068032100c8548512042d00c65050307048590a26445074a41d00e005000e507000d44c00110400303540d072070300c12920304640c841c20016001031445000000d020300c4c0038405410321001c0000c911010031402c2200d1000340e80c400301858292900048005540d07120111018240c0325506904c11040040030b40c002104203040d80f0041c407500c54500305070040500f0490481e101e2142c00c0c003100b60210b18040c44000184035030101c40c0d004502400d65064251a29040b1340d5018a6503c100ca880d40c481411008141d07201d0081801031000b400c05011003c1e0880000707480d2402d5002c0d081c842991000b280584000c09002a0000c00e030340c03401d44042d410302010560b00c894194120780e46400d50b404032400740711003040445000b038022161000e04401c0e10420003020b50721607900b03941080f01400f03040d80580d03070510055005511421400c149130f81101410a500658940310b1001a00014003c02043c1d0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 66425659 1250 66424409 66424411
    0x90506030d0e04050a1e050702011d1e160b0d0b040b012106051309050d0f08010e0705040b0327010e03040306050603031608030a0522060f0f0f021809040b 68
    0x11140402c45a64550b0480014050307206e50620307244c4450020145100c0c1640720074003901040c4d000303122a0b04991044111050f0304a1180007a034800049015401003a40400443c030900e40c095800c0400329514208540032039812000303101800040e1031b8120316062284601030441520240b20b0304402c9030000e807040e02c0b440c1100c201454031014911107600141e000030701614000f000d020050380e18000711b00090141c2881101c0a1040200365442140104031a10f07045041d56191846a82003213055941584060542c0d030901805000101d8000c00700000340d840f42048080c0d00b41d10410b03a84039a8240c01150680c4c20443c7d14092400c69080f8012085805694114101142680303e03940030900e1071050759400741e00200b03002d900904000050005601500c000103003031200da2940c003c9000000c03550b551083e551750010180500003001a00040043d001c1164006110414031000d4410f860088900b05513050b80040e8600e0214840030003281c100a041d200c00c402031410b95501e001e0408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 66426909 1250 66425659 66425687
    0x190c2a0308041202010b040c02150c03060a05120a0c0312121e020a090902040e040212010b011b08190e01140309060402010509150409021201050d1101050a090b030f01090506030d 78
    0x240c91400f05035124000d4000c28101e15000d80300300700d201c02090009403110a440520452070010350003080e00c100106094070b009800c010101c44500d46450f040140d003800448144a444c010078650701c0c0800c0c810b402c10070045000e40e400c24001d00b88500c00904029280c4810402c15240682200601040e00c0c03911161641c100c500684c3e442204c1411350343e01d00d0702c0c1d00c00c0c80090700015020469401c0001c1490103644244c07000858034401e54105800c0c0c40b010100103000400201444c0c80420a9440c1c4003009800345040b249040902c004260203610001a060702107000c08000809550340301d40d001c1c46864103d047e01c1d04600703000301082d84421001d84040c2c1000000300790790040d5640c103010743c4121030b4103929595170f40b651600c45001a400a1000b1219010340380c1c00010345040072a180c000310ba90200c400700c5c0001a1070015a0680c00075121070003084001d03070001c600d07540c101004500900001c5e0640341d4640c9004081c0098a400034401c0740240c01c0f041203028401d8004100040d031030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 66428159 1250 66426909 66426923
    0x2090906040c15021e0706020106080d0804020f0a090c0309050d030903080c0a0215010e0103060b0a0501020c0108040c051002030310050d08070312020d0501170601080705010512190c2a030804 84
    0x680c83d00400c9160a660360451242c4407440111100d14090001e6044102d4030250001d005c1d403a40c405c486910b81d03020b28004070124500d50000b50043c0380128080c081e0800007010010742686552110085801406201000c2a40c410102040c02400c0203080880092842c041c0031491071035600a04e07070315024210741c040020101d40922524001c0c072901c1b50301480f10300152182d41c1d6a6098a003050400e20050b181c00307250207110081e50034581414002d5502c181c0041c100c0c1c2100b90011114040d0040c01074030a808007080c003240315030380c02c80c009002c0455580110384034102000d03074070044509035201900c00c4030395415402c0001c0b00700c010b5078400358041c00d20100d26042c84000750003074800d0000005a4038607120001c40c44110035811803207090113039000c4400340ea0700c4489d1035a50345554000c1c03d01081051100800c49804141c40c40d40c4001100100900e000113000c2c48002d49003c800e074140410406c603080074681c0014000c9084008026074015150703451510050009180500050500c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 66429409 1250 66428159 66428189
    0xd0c050c10080714040608010509040f0506100f050414070c0302070905070c05060a0b01020318010201021c0501150f082202180a0c030b0a0608060a180902090906040c 73
    0x8440148240482440c02805022258000c072800801c40001240c0b8000880c41401c01c59900b40096800d032026541c45441f000c50703903402e11081000b001d200a108980b4020402a5a00050801d0200c2405942e020400320b881c5c0c0d0030315113080d900f0180c5d03800003409540307804001102c29031940f90103908070b1114141038010124908003203040c0710b48e0b0f400408180f802c210603c5005581320761120400750060041d600c0c180c80f42e0f2507240a6030042603031103005078414007038180c0440c845550030145e2401400014030305403480c5861905800c2640039040401e81e54030040100c0c548145900c8a0f0b440d0b01e2a2500000e24070800240c05000003a0100504c0b0000d80c0b1080722020f440000070001036001071644070a005018191103007071404452199415003007401c0304400078081c0c0035900130110010500103101d420400b007294241001071002d03034000c40600c00000d901482c0c100e0540021168040414902011700510198820103004c0c1c0199500c20010000410301c0e000bc0c3c2c074190360b0048461441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 66430659 1250 66429409 66429413
    0x409050a060914060903040315050405070b0901050d0e010e070e0106050a0503060a09090b0415090803010b180a0b09100c02010512070504090c0c0204050c090303030406020d020715020d0b060405030d0c 88
    0x241c5400011005414484c040c2448400c800003c0904122071240d010594200043c02810040c0c86013a03400070325591025400b4002288070401a1030081410300d095030401404210320405c1d03424110540d041a50346244040b1091001c1c8402c03400750200c00d08050280d4036048004042d845003040003010400c010000ca001e130f1350f031013090100800000001b070140584a05150309501c400303031400c40e003001e003030649030b0b0403200240501d802e040d4005564031304580c40e001110002d94001a142c411044410030512036980c0c8140c1c00c1c0000d040340242064440d01c44400340a88250715148040500c40e4015010340140e03442011201600741d0401c1c2c034155a1128034058690b400769401041800c0e081070341300c4801030703405007000207664005c031420310031a01d80002c0c2003010300c43c1024280d096013040000070045001c1c2d4005121071806500014605180c5072156080c0020054482000a400240195141c6c52501030032010b003508442c11031409240000081c0c1d650724425420092118000ca0002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 66431909 1250 66430659 66430673
    0x170601030213080303060a2c1905011d0108010204050604090903020c03070915050411070308040f02031615110c0d0f06060807030302060108030c0601090b1309061a0409050a0609 78
    0x42d401210355021a06035250010316843c0d400c21210b080c0a0400500000b40d2141403142079542d8420700d160240d400c41b0024204480100001e2549442d480554901b90314100244280b5008008544d034010485500c040000030046040e4410100d681c01404180060b07075444080b0f908a4000c07079400240031210b45003d074103060545550075403600071140d001950192075085214071028000700c009245480308104412200309000028641c00c003031000100103401050800e401500861202044c400d060380082e147c900d00ca0304600c6602012081000346e0b020303c01200c02d8103c10f900709280c012900803401340e90303405c2c030180141c403600203416441e0070302800e8003103a40082d07003103803050181544914080d90388518900c0110010711540c40002200c2d800070042e100d0100c03014000d001350341d207400b4402c00a4411651030f10360040040250f00e00c000100d21500150601c80c10740814803110501c00c0b081204041c100c03440c020703400d1280c1103000441c08030f50744074159800600000e8210803418019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66433159 1250 66431909 66431917
    0x306030a140105060103110c0a0615030507151e0e19080109050304081207150504020f0402031509060114030103080a020a05031c0506040218010e19090510060507031706010302 77
    0x41c1010140d9480c06400ea00190455480b6034000c0c1c80034007035540d0151103c0406d20900c100c180940c0c029000795000181c242d0481110303007a0002412460945039141d40e410060144e0142c030702880c10b112348413812500701e074810303011034003d400882c15411012f002600c4803c200005a10802c40080c80089406428212101510820000f00041d030030a10704140d07240c0c40f500a03400725200380d02c80000030b910f82c20700b00e0784480e40c880346060f8400d00b44016a80980b0000d0012a400350f0041c016850903112031010318411514412070840440300c55080c404029400350640e4100824809098461010081201d0469a208a29581d501d08002c401c074142000b940008109000c00034800c5230182082c0303103c2c0d120a200600812940d280c410801c4102c0c4550840101d0005501c1d034144610b40c05070070b28281001c8060b240621100106400005101c801d410403180c036a43d0300c0c00d10800d01403048001d0007a040710f0030400d141c9149a01c4c090064050403086210201c0c24100060341c07a4802c2d010b407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 66434409 1250 66433159 66433163
    0xd0201080925030b0a0c02120d09080f0d050c250f0203070f0801050c0a0c0308090a21030b06030402030312150a06080106031a0619050c03040312020d02010614060306030a 75
    0x20b11020204881c0303040c4154a440191402d10b0341002066102c42e50b032040e040304e606250010f2018035000300103101c0e40d4114179170760221030340c0e554022004a040f9600030007109401d00032881e940c804841d140012101701a2450400300c00900c10008518020640404c101d9600328190114456600d020704007603400300d10080d00f601a5020020f403020011100d101a41d101400901076079441011240135401280e1104c0d0000f4110b100d20b0303003c42d000340c1140f03402c2070701e84c070540701590038580314101c0000d040c2d0501070350300d446050036505041c0d061080080e2000b00301c840034a0340c101500066501c0c0200c4c80c6c14000145040c000c01c00700180780490045241015000c5540c0c0340d620000036080a000341300301008241880c0308191107220a82020803820030080a842c180090070270b6032240c03540c910840c2e50078040200040001420304002803c015807091050700d850b2003003404020700b007200400340b403400e40e2304014060043c50303015070201074048025035110361241d840100280c6006620000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 66435659 1250 66434409 66434443
    0x315050f150f03060a270207050c091f0b04030b0406021c050403030212010b0a210204030204110705010b0d2105090405071d010c03080604020d060f0f090612020d02010809 75
    0x2003040b0504004080c51050310f00716840ea0b50035540d06131414030140200e41a02d40c120791215140c502440316400750250341d003d00101d0b085410010049441d4203400d54846941811461010085a4598000c50301800c28010258103041c035680d22801c000303102401c0100201d4000c103030040611488c000724001c004d85d541081c00a41882d050140003540603101003d4250729110000c11081040412586801090703521226540b003030071290054050045501003101350204030010160b40e4a01680700e030311403100011660340710240303011030840e400c0c005038500402560385820003041030366050014a5011107600001c0d0034a030a0304880070b02c9002d0800f5881403500040c000da590380884400e0b03a082ca0b03120304d5201282c6800066a62242c0d03142c0007800240c0041c001103032402c09801401440ba0240c40104140351600da280074528415041051b000c6941241040400030324010303600101003a040c14400d04079180c0104054000024001c0c1c140072844020840101c4100300c54440c02c091082 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 66436909 1250 66435659 66435667
    0x80613061803170c0702010503240303070606090605030d09121a0118060b03060d1e0803040b0910060b0405061c0203070507020306060405090601030b0a1b030504050d0315050f15 78
    0xd4042d1041422000070300307070041d864000134190f10030f070b0341214441c42d0140c4603141959a4120340604c150036030001c0c42c4882d4150240c0302d00c151000c0001c1c3c1085803141c6400300b8090704000b40c0004489165024620a80c844403c0d20112364100f8a642c0030741d061000c0c1040821440e0400c442c5003441d280100c03000d0301d520000000d1078040d42101000c6240383d01e5041c8071850741c841150134640001daa83c240d000c1421501040011a00c0707510300c8514010030100701c0c40141a89501c00e03e90011642600c0c000100801c0000e036007002e00c42c50855130721488081009a0600e980340c0214001c500402d8040c0000191303030040b42880b0001c460000303800b42010f55892504e20701c0100250042a0100e010744240c101081c0b10340340601480f4400c0a144008100c0d503880c0d910381315406500501030fa11556510301c40450100c0d410b20012801c02c1650f04c01141c2400c3c64544545020000e440120416203021a042540c01980c1241c1c01242d0089440d00480603523180004e60300e240d468100d6200d054002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 66438159 1250 66436909 66436913
    0xa0809070e13030e010f08012105100204030506010f03050703080901030e0d0908010b0607050a03030903050d0629070308010501121d0a0201030b12120d0b100908070902040806130618 80
    0x35002c2c4038628820303a601c1084c99443d800544e01c1132241100e42003c20000e100501402c00030403c1d248a81c0d0751003c6940c13440d81c59848060504404203076140045400040a0061103010800d03035004011280d54594418171b1922880d440b004140001006050005100c15031a80300c0e030003552111911070709495210340d02c580090150b80462060301a03d508204c1c04160502e80700c000c1d40c035503607003201c003a250104050386c0c00c030024075204004500744002803000400010680c8107003006091441d0714200d41580190b52810004c0003a564480b00480400110000943c043e0044d07045800a0820306060701d0b058580201902d60264510070f4900103980300030b401400024011703003050003038070100052014042401041c503c1070079809003550109024883c0b1481c1000103003441082c501002520411100001e2684800a8000c07000031720446811300041d40f051150800a011400d4114549450076030842d441388801406140906910302200041c422140c210300407107141602c11558514040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 66439409 1250 66438159 66438181
    0x2030609010c03060902090114030606071a010305101e090203030c0d03021806040302010f1202090604080c090f01063e0607020111040e06040203060a031401020c010509070b0a0809070e 81
    0x1550780070020381000d10005d045000352084401c00b01c4d041c0d40e4102315410111000f6a59407002d0101c3d900004104413441c041020b00b011020480700ca2464000e640d4034505045103081c05400e00900b00034030700002c2e420001ca6880300011614240072001c0742814171800001d040d4011b10144440324050b0080861010f9890b50042101e00884154804d03000b010006101490040c2c0c00700a0100301c00039407d100c0320340524851130319041e00b0705005d460a210940030491030f8100340e200d0512540030703400b85d400e01d2074a16040c2c1e03844181210780340e070150300d01080200680c0c0007880c41e2452489060100c14412035001b0603101800c440484040c00016101040d40d40d620200e400b9801540f0300a001200d0708090400c41e011107548078460825070700d8001c100002540060301c003d23403181c024100000052041940c000e11104500001a141c007202d444282c00c1d2000241610f1940e0030010062009260000585803c40c02a1424042c00c0e0f6600f85441d103065260781008078241034200402600401c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 66440659 1250 66439409 66439421
    0xa0e030f210106170a0608120a17040506071b020607050601030201120e120903031219060e092d0105090a03090b090d1101030f05041b050a0b0d020d090203060901 71
    0x1107100a811a50980030421009002030003080009403400140d40940c010321070070641c0001c1c000400040d825a00d1464502e04a030062028040b070102003403101c3c920390040c00c1c29840c2d42d29280c0e0620540341540d54076071145e40040544050140c1804064801c8020300c4a8aa0280d405400140d540380c1034149503a803800c09200490009a007620b441054030741c0c5004080640d410b4100401c10140c14060401160308181c01c1c685d05032209010b03500d02050200f8065019140c00d40c10b0342c0078031040002041c195200c0350041030003203041400340540a0340010700c02c83c0c1d500c0f25000c40f000801142544070500240540002c4166080a0512051040101c0c0c120f003c07520a849488102d561990180707628040c48100d15403003420441d04001283c01d09081c0352404005140c00150700c520301c40980c0c100c0380155020740e0078182510064104040ca900c594020305011210003e030546001c440301254442c00034400d00c1d15802103a0441c100b0a10b400084006070700034182d030054a04403100d10b0003844 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 66441909 1250 66440659 66440677
    0x201050c0703021509040c0518010305150d06060602160803030417040806010306020301141c1101050c030a180e0f0109090f0f0501020d0507080c04030b0910020301080a06050601080c0904050a0e030f 87
    0x72906807c00da80c103028001b100d20f181c0c1c0022011400d14004801500101001400125031802c8050f0002a036500c10301e58081181c41b6a81c0002c0701410550300901d0300c007404680f508002080e80e0188403404000041d030340d00640c00080310512041705001c00c0d00900aaa00c140e02e50f01c41e060020003008030b6600950306803049540e41c00840d501c0c1904205581c5c41e010410200311000901800105007891000948501c040c1041464510440b1540b4610792140c51142d001956016510110030355500141c0c0003000c100300100d52508001d01900310001061140c02c46641d03440d01ea840c1000343c20310100403019000305809034140310038200300d030107980284401d6501c50303c3c1c00700141165004000c00350140c018080050b06007800c40da10319082c1c1d07102800d4403410784110b26050400100318001580078214240c0600324a03491490a4800c1c1c400152050b81441303000e10070000a07600e480261b4030b020000320b40115088c1ca9540d2410003d003000204a00c0c103000014070100c10041e25401405a02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 66443159 1250 66441909 66441911
    0xa05070302060a050112060906110a021b030d020613050a05063603090103020a02070f08071a0909130204090606141305060904060c090b07030201090c080a0c030201050c070302150904 80
    0xb50b101000c0358104c1d10709010701030f0388491404544022070b101d6400700c00d01911031840000e20001203180d0280a400030200b8100603070020004032002180d12511111100080c1c00501c03044080c0f0201a480d504004d01d2101c220700c842d1035800501408014455503150080c0580d44107042156140034540025001d07109507000222201e0b0800e04254012504011100051400c000d0030702d00440c06940001814821441000804180b03086d501903040020714240c1c0c01804428600380c1154100c3c0d4421030350304200b44080c0404a0140c81d0395070354990040300e18080d6210102c2c1031000a0081c20202d0011f85100e14081000c42d20400d03260a81200541c100d410007607903100c181d00c8100b42ca50442c0c0303082d000000800810001402500255440e41640c00d0142100d5114103262245412000f4144c0040c0c2d1207854010502151110500240040300094581c0094540711803806c2e4940e4440241000800541042d80700402e109043c00343d80d0042845001c001c08909050068005049051043d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 66444409 1250 66443159 66443161
    0xc03050601020a0c1e0b031602010b06030426120f0105040608010c210905030d020904050a050f040f06020c07080a12021f050c090409050307030f08010f0b1e0a0507030206 75
    0x150b00003c1c42c0e001659104001030051804c0c5207001e10f00840c600105001a2400740d0049080560300c8091403150105031216002d040c40744600909480c03100f01d00c140a0a020800c0c48003040321071440804898260b55102c41d034094460f0803041501c1042039200060400006000002201c84221412030340120f07018032501351150780307a42c2203a1724410580042048100700b403242e241c4c1210801c1031207030004000200f40482c1d888840c156802540b0041d05a50300042ca00301c1c0c1d2038148291504a408031350204074903d8000f2102e403c1c118090405840d13403410451580422410350105c44102056400385c552141e902c90140b69151610b40080701d1a450148204000d1840003a0009403034000c0220940c00e943c9050160000304005400c010480908000740360f03240d21507010307070729443d44a000250307658000e505008042940c001c85250400100f080100034140041410310240c94001800c2951420824180c14211400c44544489210045203010141c0e402001600ca0a03000b90255112 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 66445659 1250 66444409 66444421
    0xf060306010b1206030a0c03050706140702060d0906240f0b0901020d18080334120e0a031703010e07050403080414041e050601021029130606030c0305 66
    0x21a5000d000c1c01c0c80a100600164105040f9600401d820500150076a18601c8040c2c80e81d00400c9101d80041d41c45034020001040b80c6d80d0b10818a81107200100c0380c0d64146990f0b54000fa505202d0300d442c2c1c20b144c0345c480000700c0900c20340b54001804244141183c1810202440514282454510800c11090704ca228001425400d10040306c280490503800360501840840c010354000c14102d00101422412150200f8a0303103080000f84500803511349890301c40000c804941c0307000344400d0340e007880004e0545c0003440090010907001c070640c841c13410410b640001c401d021800e0300789940d0014161210f2031201c3c4034260448002507050b1806412009440d90359410151074a200d00c0c4401081410700300030410280007124034144c1c0500e0002c2c0003213a03441c40e04821340312041d038046e10600e0f10b564880c144525580c042000110101982d24140f1103c1d0030300800c01d403460180c5402c002621028220240a65211040200240b032810401c00000d0389442c0020001c00c1c1c0e414084020918150100314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 66446909 1250 66445659 66445663
    0x1f0e0109030e010e030715230313060e0c0a06030f02250302010e0f0d03020f0903010203070e03010e0c010e100509060c07030c06050301121113020403030e03060c0306060d05070203090a0603050f0603 87
    0x101f6207140041700d4a5880c0e5005d01192040010285502c1d14400e02c5c960700002d003509002140224111280302e860191103040c031304200c441042c1c50180303507840820a01015114103048030b084034000e090000d415140601341034041c0c819400d004000d08210280b10000d424600b0303240e40035a00035402080b801d51901141695000000704e0038490f980300da07003603281c854466001064901d020108090400209102103401d9801c103955410210b1200e01c11100b1604091040c0503168580000800300950340500103000040545115801103003440ca624900b24090f0040b10250b50000d0300d0180e03541400d8066680300d580c40c0c00200e0b100c500c00c0b00001a403510401c140c074144c7d400c01c8181c0c1c02040c50380d5206204901c41040741c1c2e4010700b81151000b190002e51015200542c040e85a0500c0941c0c008109410084010000350405100f40242f0456841c0c40090303400304c1000344400105600c1c1d80c101680740d03004120070320b0750185d05000003161044e8990016030081c0030301c9280120640350f41c82095 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 66448159 1250 66446909 66446923
    0x5010f1703072012060402240711040603020d030c06060602010c171302030616020601080d05160602070f0f020f150a030b1305010b120a0605031f0e0109030e010e03 72
    0x3615441840100c0c04203034040c1003d09900200250070090b4101d040104407040380c140e03038140061700500100002c2d810b00c2191300c20150307001424080c1640c6141e0519005001d601d402516600302c1d03201d2007145840300e51000d0040c6800410702c4082c6040e41c50001c0c2511240c21003100c0b074600b0708400040c0140140109000d08290b0744600030505040c410320740c14032000411002e07000000d07004401c0035072020f00140c0d01a20700c83c034858070316000000c03020345000c0042c0e20001d010351060611407885940803050703c0301d2250382c401e031400410a90030300748064040c01d807029061444124000c810080040c8499a00500c2950300c41c0d13a41404a003040f05407101c6040030b1040c0207003046124a40d6201c4d0384200103081c1d000b0110b40000001ca191603003254803d0704210060b031000903c0301d100b04116108e00d980f0115070481408250f08110210f5211542003114a025000c0480f508201c050750340c000b84104641080208200780791810300810140c294110a40841e14600c8012054100800e080d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 66449409 1250 66448159 66448199
    0x10f0801170f121e030f060d0206090d060221090a080705070e07170c09010e06090a21021507030504090c110a060c0905040b090c0a02011803030501030c3017040905010f 74
    0x1d2146d6980d540070f10004101d150002c0f42c2c0400100a0080150303100050f01c016240070b40c1c1c0c0141c545201c4030744103003120502da403034010707a10904003004400440010120342d80c540c000500c43c0c0ba920903203413082c508030240d040710760086900401c0000040c9e000c61040c40315140d1001c10100e41c0ca82c108100002d12480d948140010051500002141440001094036410180240e040d42d0364501c4409450046003505c04c00000c041c20001040d46011352210224030705c1804600c1ca0031041b41e50203411449541302d0b072440c0c02d440700c403407500c41030280009100d510094001e0700c80c1071886140c00002001c02c807a0700c0380480e4800c18040750301d04082c45000040b100181130103040c0d80304c422400c40c41d03401c20340320602190f49907a40d170031488198201e4101c980c0d210380c0300841d803941903182550b0030f0000ca400c80283c070011602c911224141d00800c5400091111580102e82c84450030000c0c404100c0b0400750000da1030002d400075000401da44014129940002c0103034800b500c1c2d98640d00740d07003064041703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 66450659 1250 66449409 66449431
    0x315040606140f0d08090316090c05031e0406060302130e01050f0603030a080405011104180c0503100303110c030105010609050a150509060a050d0504060c020606010f0801170f121e03 80
    0x440f000504111003162400c074040c06605060500500010745001c9070341c0540082d0740725204041150000034064990301d041c040c10030506529240459000c103140741018007950031501c4011a050082690048000c0c54020707080d460005440700000020b4803607603040313102179840c00c0c0001c0c66a04810070914081c150040145280003280c3c0e200711030064018cc003d4520303540e00e642d902000305a000003000141030a181e8421442c81c1d0125100490311180d00400a11134204208040c480400041c0c1050340e5060400b11580d80d01c21441c1417a0500890945e49c16603e44400410605e4100d520003003141c00458288452a88030290305c0402e11104121101042c42403002c0d00d42450302c040942219912860f161f428052500306080075a0303002d07030701034400c82e980b0380350580c0c81ca50522995604c00401c0c240201080d0628400030b0021405100e62505243c03450100003480c00b00744641c5116105e050308503040443d00082038801b9074040c00c02071100d20059080c4460031010401568460051226 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 66451909 1250 66450659 66450679
    0x30509030306041104050405042d080306061b0a050c031212150d0c090b041a09010608070e0a03050c0102070501021507140403020d2f0609130b031504060614 69
    0x2c20f10002d00b81084100441a070140004101d03521244251803080340500c6414040742a40c940102031004035031240514440d0035441d40c004240e54800f1071350000c0c000d445a84d0f8840c0f00200c0d024101c00b01407003d82c00e6015046069007030150000d00c0750b0740c00c0c82c01c600781c6200003100c0407885c043d485015061080721618400103070503041042250101c103480a0300d44114980305c1d9461039400351503600005800e1303a5a003070403000360800e48600ca2040b14900703101011401c0c500c0014406001c14407480007001000303000941c3ca28851000c90b0340814003d000040e23925102d00d8000d80391700030320741e0160040c402d2040000d07907584001440c058010301203440c881c0c581c50f44101111000d42c82c010810041c00100130000061720303050131004905004111184094400c1c000420340c9545140211304410141110f000f0300365284030494814000c1201c280903140714400140e000361000e81085a0705010f48198030b03d80c9443c1c44000b91040e072050ba000c0019070f880740e50814084041c1c4501c203030800150310b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 66453159 1250 66451909 66451921
    0x20c030a080304020d12030203040b060d020f04150b04080a1502030f0f06031615030e010b01020d051c060f0303080702031216090305030f07021305130f110307030317070305090303 79
    0x6070055401600207000d1240c91401501c82041c9842044800c0d00040d50000c00c000906c111400516004003044a25460846650300020712542851500700c1c801c0da562842c541100280111880080035950038040d03d45079a9a086c6131500c400c020241c40710100c00c7d403c510100528402c507413140c02d0701c1c041c049694681e0b00e50b49540d104c0c01071a843e090b10514080920182d5050700c00c41c020444c4540e028004602035100a09035110000340181e160304001c041082c07681c01003180107080d622403410640f030f2040145003a500c0000c0e9a20a01040c0ca042c074045010b03050404003400742c9009403100c82884e1120714003280c2c0ca200b14107040340002c980c030010803a2580030a01e100200a814900040c0701916515504d065500844400c00402d4002418408605011481c2a81d140103c113003007105103400c0c1001108246020b800801d170079884002ca00030005182d007810b449107005403c6400741a241c0c40d01031301400c0c11070901d0325803403955800260320603c0303805098881d000000185007142c0f125 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 66454409 1250 66453159 66453173
    0xf040b041203060515030103060c020c09070f030b1002030a080714040302090601110d020c100206091b0102030c03030403120f0c090308090a080115030b010e090307030c0204020d050f010312020c030a 87
    0x181400d0340070183c0ba45070000d0542c0d9402c1c401019544d07240d60a5139254911b00c3d19204661201e0142e00035500300c0b0b012183ca55454402c200d85c4552141000d112090720b11408800802c1c00341691503100d01001d02d13101e48154008003603c000c911903121074860380c98004c01500c480c0c403c90707403e1642010400c0140010709010010a40011042c180758003058a4a807960307042041d80c10340c1c0801a802400040c1d40c52400800705551035440f0300183c610360424105003615078000540e0100c0e0040040d0301140980d1003002110310301070144050b0b07601c03400c092600806c90f10a002e03807600d14a003082001000718a042c0700b0103050100548076402d449107155280b900a8015049060344504408000500a00207006003104c011034041c44180d018258501682000410b8000000800502d0100300d541900081102d170810b405003000145410b480c400100070b4801c0400d000007071420542030040c0d88440001c0e10381640c0c400e250350404034a10b4a0100d9a4140e45009294190700c0020014042408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 66455659 1250 66454409 66454433
    0x501030b041e0515040c09090b0604030c03030806190608130303110705010b090c1312080f0c0a020a06050f0a14090303030103051f061202010810050910050103050f040b04 75
    0x203000480d40440c5201100c1000710345552610300a0740b11810010700101e0110501820038084404000541b01844010220240c81c002c840c01c00342c0e03400c80c11400e41d85410994005603030180c01d10b03083d261030b454000c2c118442550924007641d105041c1d0300c1440300e0310200200350b500c0d0340c1c4d60321159074800c040e40c044001480d13001c4c2c0605598280b068500210300c0c00034082c490080c000407031080d1411050101c0c02100802000d41c8610034082070b40340c035103ca07030703403104540781c0c0c8400d2a169411800c20f4a124421460049080c680000300d06000074000304000106600031501107c1c0310b80d4807042503134544558000c210920704104001001e0900400c1901c1c08a54509070460401c0d580b040400d166620a070010788050388070803ca00c042e20380c40c100c916400e4003203020500056290440c5204a0f621042000341801032a9000420510181001f0002490014004e0102c0e04042c00c80c0c0700c10241fa801013500190820000480d80c202a20b211402603600c038029084030b60355510307400c40c030505c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 66456909 1250 66455659 66455681
    0x30f0c0801140105060a120e0106140306010b0c06010e04050c0307140906041e0f0b040903080103021f080406020a0c0507031415150f061908010f0801090b0403030c0c0506010801060611070807050103 87
    0x40c1d40c0981002e423140c00d00c03c10703002d0f141c104102008030b03018008141c98160141d018208800c070400c04d1040103840440d84034111b90105903003050580751494514240701100001c2a050706c20300d100000d0f8809046254009444c060310b21402365150b040c2400143d07821200d0301120130201c4560080e501c0c00341d502c0001040c600240000b203140fa00400a0160750f55031030160000307100300d40144194074041098410080403e286249018100007000d00701030001800a04800d602041c5c0c1c400c501e002d002c004075010351050640b0901303522460410001d02c681c40380e12003a8402c9515000d510004502098080c120410680d104101200c041140e8040f041c24072681181041c000f42c2450410070109007890900e545640f00c2c0c1d90b042c02034076041200079a0105407140c0c1410034040200d104424030503041601881e0124038080d0954082d030780400c03c520001c3c008c2c4a200c00004881c0e1040d401081a200b0360b945815000c44ca504009944000074000c144083e00418001c0045600aa05c5500105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 66458159 1250 66456909 66456911
    0x5040e0d08100b0408030a0305070c030e0607061b27050a050907031d011a0108040b060904020312041205061503030d2a39020603040507030f0c0801140105060a12 71
    0xd0f110000301c1e0b0540c0040e8407070450f582c00400e401c40d40782d070140503166001c0c0c1e00f4600860340d10100d031002040703030305c1030310711540964000503911080c0111608060400c54019003800c5003a0031400d07009141e800c82e8403400b0120805a0024100314a181c2609000c0300c00c000d0030080d003d8207000400040c06d00c0686807406050b602e100d100d543c54980d4142100811401000044503507009080100100e01024000c0c1080000010800000c0c03004899130382040c4203540300c2070380b03565a02c08a07103070a901e03802c1d5004c034100c041400504040785030030b5002014482d00c103032081601c0741c500640d924101d80f0001540341d003041c84058070400d181d92081c1c0124200c040e80c00030005220868900201c9040b207400001020045280d608000302c1603442720b181e0340404070221aa10003001c903e44000c1100c030091080703d0003c041010300c038042010401454201226401001003840c000d400d0ba40d051040704030035401c02000603290005202d03000c1c100c0f1400360500303280185500717007260176004004001c28a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 66459409 1250 66458159 66458191
    0x1c1d0604020a060e0f13090f050a05061b0d02030402030109080c070f1202010806090a02090d120f0e010206150409050d03020304120905010509060d24090605090c040504020a020307210905040e0d08 86
    0x108c1c00348000290650b010358041e0004040608245080c9030000b00780c0c15801907005806840c000b000741c01ca46100780074540058403500c1d5440004d015082c0c05c800900341c941c0104010b041e061021400d01c2c03c6541503001c06c0901c0303699110380c0044900243c006400b01c3d0070304001170030364142541807940c4000c03511001450884414002021941886020340305802410084603116800000301142400310f400c003c103060841500003951950001c010f014508007101d00c8054507100c035000b4443d40e40c1d20a040d94154411a0b00080003504103da040d298504200c04200c09940201c0060091341d00681d19540740c81c0307241c4284082d0303600460808003a640c1e1403100e41c400d60241c2d0008443c0d152200b8020003910b00d080d1a44007501c031030703400c600c2c0305000c0b1505000184407003904850854005540150310f0385884403007603013140141803014140e021100001c00c0103503085030a140450a00d9142c051500341c071502400704a071031084800715154407a40d0205422070098410030303400448480d8105007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 66460659 1250 66459409 66459413
    0xa020603011217070c1508040507051504090f0203090d080403080106030504020d0f0501320a0f0e0307140601090c05090d020a05100c0b0c070203031c1d0604020a060e0f1309 76
    0x4107078132546054170300541c1d80e0420301207a600b0711884030806d1194604100c15040c0354403040e448010310320901e44201025050700301242050003e0307030020a240b50f42006001600e000c0c0001a5104682e05041c60245000044155010b211160f00464043e03076100882c0e82003000580c0101009003062340d00c05075000050002610030141030721102e100e503001103551020524111440000d005030009a5032601848581000d84481e10560001c0307a054081003189485803440001c0c805044085603c1c0800a001000d01010424100ca904000c4044600aa0780c0c0c168a000700c032044420000020000c10103010f00b032604500303407124180010300071000c0c40d9861000038483d08450f5802c00c04a200f1000754018402c020040551000350108158035148240c0c0c0007036100e1084400801102100c0c103542e41c00c0c400070342d000032081d901c5030001850408007058a9681d40a01300c070100e1013410100004601d0310721235135000c001c1c2074010b4029a26003d00034100050407816620222049984100c0c41c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 66461909 1250 66460659 66460703
    0x2190312050c090a27051302120a0b0a0507080c281d090108060f07171810060b0f0c120d1506080709060806121b01020f0a0206030112 59
    0x2c002da20b0344201c01d9580407024180800005640d006900b8a00e00d04808001d0b0f03280f01020f49480d1031524000501945d44e224080b4030300c000c005001e508005138125030f041503c0002200b40e00a801003640c586541c4d14401c0079810b40c1c84c116842c000081c403213004220900c00540241c00007881d61403030304101400c08601c12090300c1030140d1502c00941401031000e10740700903d50300040e119080d03400440b298102002c1c50b50f070325005404100401c128400144c415489801c02140d0502c54000c11442420180c40c40b032016904000c00c3c03030490049031004028104a4411042202e00700c08a050800545444000301038001d01d1580c2003a00400c030804261a880100810601403001c90010319410103140f00044c08099800c504c0070302280200b48640190044040c0701210174500e418404caa0f1f40d400440c0320014540080800f0348200309003200c1c54140e080b1000c446400a900302c0711003400900704c1d1959030001201c06500301d0020001403205002c21030354014080e0040d0032192001400300d150f05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 66463159 1250 66461909 66461911
    0x501090608090321071b080301171006090b01110d09051e0607060f050708010614030703060803070510150302060316140d0b0a1703030f19060824070219031205 70
    0x1000000044c0308010403075030050321092440b10400d84030a0404e03001c1d603c42d44188018000e409c2181d80700503d06040076000c1011205543c0a00400d002d0181e888003034401424180b440c05021a01901c00c21914003000140e0340e1031000141e5403100d20310b1900003800080c908940b04c02c81c3c0c0e0140d98464601681b82d00c001090820311600c0009558208254071104690001e046107007081a220010072000d64809000c0c4080140c1e801d0303843d625115100d09034024201c40c0c2c400f1f800703800041040010300c07202145114144200d18000e0205804140c44e040c0c040c50310780002980804180b01080620000160b1700054040c903041000c0408a501000011a017103e80300c1100180c44080d4040b807410500c8140c4020107040071041d88000030810041e03241d00004010034107440d0041c00181074110205041c50015241403410031282d52074042c0643c485044919482288041941000750080040c1900f842440154046c180b06440005e1120341c5095000081d020046088a11261081c8504c138403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 66464409 1250 66463159 66463207
    0x70303080402041b0207140303070609030806040f0507050d0209040612080307020d08100504020901030b090c0714030306010c0209090a02040f02030702100c0e040b1201062d05010906080903 83
    0x11108501c0c007441007206a80d00c141c000062210404e500c49560354000850606aa81034580144804101c00c042846d41c00344030009000c55003041070000525800c050703403a010b110140e0302403040d1210115640d05590b8140c440d080081d40030048490704802c0c59029000c1d0342c0c80200702144059980d5000c41a2161300c0701c09075094030f000000e00480c50f804001c0c9062404443c00c000200d86401c0401003080c00c0144900380c003031900094601c886a229612000031108004d04031616401e2441e032015164200b401c00f290309003040c1c64041d11780a000001d50f0f00c1000141d4a40540148981c03d00c81c00c80000780842c10640714000702c0d800103944134014450000c1c4950340c0103880b4900170000a1030030300b400e9286100d00c2c1c644910390000552210600601071025074010605005680c0440d4200644510706a49940b80c11400b0503080e2240c68600c93743c0340c0c661001c0c0801c81d4100309942c505d203010302c81c0740c1c00b18142c40010444280980c80c1076074068034640650781009041c142c0ca00b103081c00c0341c902c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 66465659 1250 66464409 66464417
    0xa080105091c02010b0a05060a02010e06090f12030c071b03060e060a1406010f0e01020718020409051b04120807050109140d02071d0901021303050705090f061003090201030608070303 80
    0x440c4141d41090902c0501107a480c0300a200e40a0301002050701c0701c8240c05140d00980002400c000a40c0c001d4010894980c1d480c1c0445c1c256140050b1269183c82501c032003000180101400b01222009800c1a039006421098846182c0042642c4546c081d80c1030f007075022101c131280030300040405c0306031052a02c8900c181e809082c0520740010f041c01101c401c5048071600d48864024081640d030f000c048000130a0309400c0503a00c54010b2401030b840c1c44556885140c103c1034400c00c074100411907170080d100700c620130315081c00651224030a0840f1060100364041c18a04140b108100110350310b8400d0741014054980c90f40307049080d4540c1030950b640d141003030324408a040c1140e44c2c410020070030081461032a01c0a01b000d14141149031180380d041c41c20240d019040031010950f2200298111240c1e1208445143c00b004c0c0e0300d1800507107485851180710b102d011200d0000765020030716400d040c4180c030000d060050441609900341d004120042c400d9040564030076011441180412a06000c0c50103916 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 66466909 1250 66465659 66465673
    0x1209030203010b0108011d041b120b01050103091218030c03050a0b0703050c0426010203071d0d020d080715020c03120901060e0403051605030a030b030114100902090a08010509 77
    0x625003503400380c036201e03810098901e00410101a81c01d80030100740e883e0303290461f250340304c03400e1214071810020391400d401541e103140012501c0002004c10442446042d84a1040c0c1c0d03100015411503602c408040d0140c144004051038013403151151006010805140340031032130701c0b074413800001003203a04200d4003548825403200a2050b80000c036907010040b882e06005078586211200c1080c0a0b510543c030b0310039810400c180b00c00d80e412000280d0500c40c0b1000b1074a904d081c8034020070241c103221800400d0600c1c3c1c141d000850a00c0d01c1d0140d1910307006480c0c401000b00b2580e031a02c09902100054500740b0442461241e0181203000502c00c0d8200b8000460303d602c1841e50300203001c040604480d035160303d4258104461031620301542d51203505400e04035140e403241d800d81c00c0196440f03c802881e030b010002b0f004110f00c0d0140c1c4071410f07000094000300318413400100d0464400e20143c40b509040b075220442000b03070f0b010a400070106518003500840700107544104d510b00707560b4159000c28503508098 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 66468159 1250 66466909 66466913
    0xb071103010c1e0e0907020a030809060702060f06060c070b030105010f030501030c060e12030301080703030e06070b15040e01050a02030601180b0307141b0703050d0215010b1303120903 81
    0x108102001640450003080300d80c810030b5003d0a0351884044440852a00e00103055886005408544003083d01408564141c41c118800a49904011200b113020801e40c0c0b0209410075000140d1510031100c46e0020315464440042c3d2080703d200c001d10381c43e0f00c0070342005848281e5000f44100d400421000c0d02c01a20395060000141807807501c4e117070040c10140f0341070042010480d442100d20454206090a04007460310601060307240c1300a40c5021924480080002200c103070000303048080724020b0f41c0c0e81004c1202007042050303078811840040c10651b00c40000c0b83c2520110b007402000448003c000056075220f5504060a5130001c0701c0c3d54008580c04410802c1958110640000d81c4d412217040c0d0000500b03001c0940c82034000078100101b0007070101c0300d842c1410b0703541040f075500c09200340b0110f64001120780000c1d52156180000c840c1402405910b900ca580000350804180b481d44008100c81ea0801414040c15001080001400e00100e84000b0218844020490190f04190386a1992178198 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 66469409 1250 66468159 66468173
    0x30905060112020a090c09030f080307021c1205100503010903120c0302090603040305030406110c0c040b010e030a08070f081309060509040b01050d02030109060c0309020a05040501030507060521010b07 88
    0x5034030001221040188075030042c2e481d003403880245e031203101d80042d039443c03400c02c100e4081f141d40d00028141031a11281c10180320004003c5e611585040c0d080b603107a50f10341d01000d85c20f20343d0001c00801181280750b419001040e141c100550010030b280c00604240e42d2500000d00b911047c4034190081514002022041006802103420389409410b0542c0341c00c8041000c124a0320000f00040e00300400400403a08101164018010710660024150f4442c801441055168101a0076551049203090110b0010354050700980c040c54500401030040c0c111551240081c59208000407134110740060744030780c00607180300c001c1e00b8034a1422411102c00303400e00c40041d0484055400961041445c4800c02c00025403001c02203040d600250b400600b65602071011a016001126006190501f0724282060081e4541d020340c0c56a8021582c850707000e59075000780022102c0c203001c0a04550071680e018406540601c00074040c0401e62040c4071000b440481d80c0902c0c0c42c8003a0019042683c00180035002c0c4032030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 66470659 1250 66469409 66469411
    0x60302090105150f0a0203070c060807180f140303070b011d01170319030f0c02010c0e120a0803070908011406130b0d0210030b03011d0609070b07111c0303090506 71
    0x105480d40443c00c540403007400d5080c0a0000030340744005000440408a0707100344169070003240d0016400ba422a19800007820000080711100005000404695000e5810810501c1240c0324001c0030102c40d41402c000e81e5a80007041b0f00541c1503c0100854400034454a624038000c2010385003c2503042c0740010803419450060388201a0491580c00441c8a02000301c02c50301c24034141c01c0310700781c08019050168043c1c082e5003640e94005180c60820000c040d0190001010061550b40344d2100b00c585004014a030280c0c041803040560060a0182c00101d07080c00a68004006d4180495810394a5191500f51960a0500da0200000c0410311405003000c1e18503200c0c490b07204170140082307150040801d03e1420003080207031058824004842d21140698020744094401900900011290b0110010301020a044a5840c0e02c00c410000702042804620207007070383c40c80c108aa01d070040d580c4880604030021610350385d0014025800c4001304040311144d18915100c1e480106400900e41080350a082d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 66471909 1250 66470659 66470669
    0x30405130b0a060206041a070c05030c0d02160e010b03040606050a0f050102190327091103191509020c01060b0c06060f0306130b1905070507110303180904030309150603020901 77
    0x100140c28800007e200d00a03a1454610510100e0308503610324030300315501c4070341c400058140d0000085010384514082020a4603402c19002c840000030016600040003d8038420581c00818200062044030008001103030000c1c004c0401099142d100c01c0080c040c80202d902400131141d0402040011756014081c4481054049a1a1b0050506c1f43c030003030a500d0131031044601040000902c5264500a100400041c2c90340c003a040101404540b10720040307074000d0302c5418900340101340200e01c21030580540d000c2440036a40b103848840c0307405144c0b0003a4100d080d1180303095484820108113003600b14090064a19800c008007168144a005c1c0424004020480d80c000e8001c0b100300040481909907824282d54070032020040c44d528501d110389607150307440300b0741d00260400c0b090107103003980b1401518065025070005a420110b00c0704050781d83c42040300740100c48100c40c40071a01480d080301d6195200d8000d041c0880c0d80d42d0796654040d52040c0d00711140488a0b503600d028015400e002280b075024003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 66473159 1250 66471909 66471913
    0xa021f02040506121306020c0a150501080705100c060207030e040e010501081207050102090a030308240907050a12050a15080708030d0903020a0506010b0a1d010f030c02030405130b0a0602 82
    0x3070900e40070403524130941ca846000c1c1020003021070011101c01010001458220720308545035940d1114003601c1c2c094401080e9408003403581d01d451004601d00c1241d0484021000405c005480c042c00c1c8083c2e103d0f550181c000740b005080f002c50100d16280000d0000c1840381c1e4a031620b14450b0f100304003c0703403100c40b203140c03007030f0b14100061058040000e44501082d108240c00c98945107107180c02c1d8060302c905c008042c1c02400042000081541240155004e4030703c180b00401b08000c0c000304d407404043c0000203141e0289041c800b01c2c460030700a0000301010191858681d0102d6802c43c26a0142c0388181c0c1c01d40b6003030b0344d140500c039981c0381a00e01c1c0710050310394040600701c0300740f4100071180c1d03e0040c100714201c2c2ca50307184001b80801d4004c0250f8a03a06a1010540d40250ba40e03081030400c0e0f80040341c8020214010f00e150700b007000105451a107107118140c48444101009640071801000550242000d40c4810003011500d5610303508520300c07d5001c0e500215003c2001002e001903501e6070f5109000355 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 66474409 1250 66473159 66473167
    0x408040512031603031109120a03020d0206090d080c0d1803020d0c030818030702090f04120e010c06050a1107051b030a0308011502071706090c010513030303020c0109080a021f02 78
    0x350f01e050300205220b0342c162901048000d010a81003109205940c0415844004401480107a1101143c90481907009800f518490000018284e8440d5812103541b00d0f90b8000200507840756005000254010508119850600c000304850000b11100c0d103044074103140540403900304143e0b0400c48420880070a05e098890450203031350245ca0301c2d002910300d10072008200380e02d019009081040d221401d400420001c1c46083c407000c1040b1608042e20242c9500c003814045503101406101d201589035010f9403062801006901c0d00d100800001e00390418140d102c54030030a41c102e000c0c001c0e000c80e50158015090a250f43c0b0074501507490300b0400c00b400307900001400030109030083e110034110742c40150300800020104008900b0b011041d040300030880c2098010407146800080e0301803041c6424011a602c600c86800103440c40d000f0384540c3e22507103250350000d00029100e50058096001240700119401d000b9581d09000340d00724400010059020340c42240c00a1880f002c08030202680d40021450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 66475659 1250 66474409 66474427
    0x10060201060b0912010207020301020f07030e04060e0606030403020a02371a0d06051008012903070e1903140d0503130605270105060f011809110c06040804051203 71
    0x3500401c038801d413140c0303001076a040c900c4500b901120300d4668010021981c0d2201c48140c0c0010741c010b001c00f130380020750494058459041a22481050f500050707220946641d50b8010010103070320060088045005001c100001a2604400302400c2402105412403089100c40c54401ca00a843d02030747d00c00898a00400c00d4007296200058008800b111240c0d98180390305403440a803900394400c940220314000d18901d256400000d8038141c0300300324481c01e143c920200010401410207410207a2503a803c0010a41180c0551100c256001c4040e000d0b2a803801c03840d5002120382e03d0742c0d000ba03e0044d0103070302600f0004c00512803282c50040714207000d421030508100c0d6150031905510f0050016940e8408203050800c01405403e9411000f880344200c1c00e04081795502801040d0340b01802041500948806980190701c01c0c4110310038409030103215442e009c029006401c5004000c1e2140318100f00001403604240003652155006854440c3c1c0c0c2c91900302401040070b2a4040ca5259030014400091 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 66476909 1250 66475659 66475679
    0xc081504021206010c0203030c060f07090b12010b0c010b03120a0f0c03080c0d0204050409030e0102010b010f05160c17070e0c030906180316051005010b0f0a0c030e04141006020106 79
    0x1e0032100c01e00c0e11103030030030317042c40400d01c0d600c20040030700c0342441003200b00580c41f5000c010152040038613540e440341e2203036554107108850185464503100c10159400602031044620054607000b0545400403450740e60400100b42230510404040841100010381001c03481e0300103e01288109091030070001c40512a10300600b0010080c04010421800050180e040201c0d45c0503100542001003040020554501c1c024120300c190340d5109005d0350900851030f0041d802905165580c0055840395403400301e0340d804055198064003000ca505016440022409100c40d0f8401c8803030104500007010340604101c0d1180c2c4d8960028091078020104104020401e480400d07401d4220400d144114018803403008424118080c0c0c0881199040141c3e9401c014440f00050b40b8200b4007012030300b00701d0350340c9903010042c1c544035400c40c0300c100003010480c19000500c62400c50030118081d141142030604810b0000b802c2d280104901e09001c10b01d5803d03c003250043c1c505050040200780020001c0b146800100c01c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 66478159 1250 66476909 66476911
    0x17060603100507120606080a141005130204030816050601050301060612020a0e03060907031104020403051504060f090b040302011a130b0d0c0306061e05090a050414010c0815040212 79
    0x103101c2d100c50200c0d207514014880b0f541c42c02244981401071782d4854a0080106204403131543c2150300300040300008601074807010340a40c0020100319030b194181800c6c0855070111480704000c0d550b08220020128071113002074424880b03042603040007102d450428610389801a04074500c8ac0c1d1407c0c508100c05604107203150300e01600c040b0050380700d5175080800d680c8416010482e54050260400f004000c1c0340105950081d01d00c40c2501d070141849400500040f030165000041c0f01d54440708072480c10b0348545220b2940244104008241e0740f413311500e0041e1000300c0ca013116220b034080b090004058080c02041913000390002c1c1011003401980008489410034444102a55500c0100c9542611481c01300c00340241c0141000301090b5986c03410b44001c2609100701e24040400034800e0607204144080341d405c80d200140360034503903225081944018034026000f1500c1c800e0303520003105503150a0041d040034220b07648070b0160a140c0703402d00740d005000303d6030a14403542c410800601c4ca01d004005403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 66479409 1250 66478159 66478183
    0x11401110c2209050f031306020703020a090504080d09030c0213050f0408090d020402030c0c1e070e07110d020705040513020616030c050a0f11060c1e12040f17060603 73
    0xe0b6900c540c0c04103110000b05070b02d082c060410700603c00c000c51036140001c02082c501d601e4a03401d4000503030340d98080741c45011a000095001591400400c03401c0c0d02c03a0801a005800380004900c0d004c0c2d0103070b280c030031650b0381c0e00c00302c010030100304501e000d61401100d480f86114608005000382d2401030303020480b009009000520455004c210407102d07444a05621030410381c0603004560740c3c2403910f0601510b030450485e041d507901c6448043c0b407508951080d01021800d24000521400e4100042c808400c85c00824040c108400620500414481044105140700c50394001d0464917040c282840b003943c800070034040c00c140500e16a0340050701d03805c08440305420840c6043c0440301481c5803c40c2c3d0840c281c680500b4038850088480c09000407170400703c0e6014822084620b04043c0e00007400294040c4400c1c100360b42d000101c0c5c0b40c4031464504882c0c40c804c1c4d640000d442b000410040d00c0641d5130460740200c0c540300e2030f0703a40a110849004046020f4406418002c285500c1d25000103a0f07514100c40c0f903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 66480659 1250 66479409 66479449
    0x60e181c020c0d05010f0f020306030601090e0615040b060406050c060c1303030c051914010b040c0504030f0219060201060f08010207080901050a0c050304032d02010807050f0408010203011401110c 86
    0xa0f60341441030070741c000304d0620320505042c000200b844404001a401c241d0350544640100740000903c12064440e0205036207500018281a5844400741040707000c1e035506054010f501c0380e07448900d6a45600050019000c1c1e500e903aa11b0b110b00300e03070940c50100000e086212040c0c3c20005050401c0c844400c00c01141c1d81071a00a0304081e080c90701c0c0e414069040e040400040720301c070078802013000609168528440c0f150080000c202311000304010ba440e10320103400401c03402c0106002144408074000041400a000403e079519103a4440c8400c0e0501d5000e800142d40d83c03035050003101071000480c0001c0c0000c500035420700005850300c643c00c3c0310303c00c000c6040c014001404110240585c080e0b00c8400c2d0403106030b9440b99131b2800c1440c1031321241542010301c4e0141c5d400841d52501c81c0c1004017034075034040c3d5030182035907600780c4255819817092007021104942848001100c41d400d0000f14082e042ea5145c0d808120007a800260072a0702c00c0940501c0c640001c1d800301c025031209030002e03000c0305103608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 66481909 1250 66480659 66480679
    0x624081c030f050a020c1b0d0212011d07051903120503100b040308040e0c03130602180301050114010e060a020606010c020409020d0b010501120c0c1104060e181c020c 73
    0x806070000c10300054040c000c036041c0b50801c45904c2030f65001c0c0c41a40d48800581e0407a040b0205003080440e840d1802661040320083c0000c05414612440211929503000009140404a000900000032070147c107000f984404010b010508004290319007040040c1c0103010064111b40d9100802c910800c00003040180100c0049c1101104a11100c001c005482c1015602c64903070a0905450b8000c1c061944441c41c440c01281035210040f08076442040c07071803100b500c550001c1e522140658044807651403c1c4a0040c08050565004c0c41080d0082c0030604040942d520420005846040c0202c0f040744948400d100b801d10580e004aa0141c0c008024038054a6010031480001c00405101101941200788010004200a003640c207a50688400740c0720072410640c0c05682a060f200d02c6e01c580000214080c0c542000a422a0043d801c1d11400030000b045807038666141040001e81100c10100160031100145071000003445031001102944407817403464031034100080c0d56844905445402041494 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 66483159 1250 66481909 66481963
    0x50d17070f020d120e1203180a18020d0b01020c030304030311030d050a0203060405010503190b0a02040e070c17090d08070203070803030907060905040e0a03051303020a03062408 78
    0x40e0700c4204280c1d0062141c0c1503140c1c54200011040000c003441c90102d60700c8040e444d850f241104a268030401d0220046150103808050804100c0307503003203055000030041401041140804d80d54503080c1861700030068480024158003010303941303160bc003281590000c2032042c4080c0c8000c030480d000c1d0394250511a1108412a11051440c03142c5800c0008151a16083c0b050700449600291b0007808111000d200c2c80c2d8075001096180d03401402400c1d541c250f18581c61001584110790313150b00483d00c140c01420300381d981ca218000404121030940c0041e01d8400e91f4410002c00d807100141072400c56251a0528103810085070b580d1282e418064242c140110741042195020019180a090460103903903c03410030f80c841c20394a4889020702401314910100216a9080a100d00c900908610b80107140004041d103055030107901512106100705002640440981c5031084000300039403241100046c150b01d0443e07201c5031502100341941908155044c1000758007030004104090028804100362140c2501c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 66484409 1250 66483159 66483173
    0xa0302100c050102030f0108150f01090b01020703020a0308070512090901050f03100603050d110111030606250506040317060a140d06060803031006090806010603021b06040b040c050d1707 82
    0x71290003409036000008024072a540090f86504030381d032843c201c60b20070481d101c1010041004442041541584c00c004016820190308814180401030050b5031a407501e80d004510b082081c0d030000d0341c0e00c00c00044c486040100400c0080c03480b480c0c64080780d08052403400007400d41003043c810300b80310300e040b1144160740355410b018549600303a809000700b04290742ca20702151144c07007040b0b014010489030340701049004010f014449180071100605850340da200401c206045c0c210000740000e5421003c5900f01e82920440c08840260050b8014021440c06260050841152400c00d02070003980505006958481c50140700a455800820700c16040300e9101184118550300e0300601045d003840d500203001c4001000650007814002c14014099440d090161385100f428801c0e0b071016070107040100300c0c091003980030f000d0741d031083c600c040c12107148025038a2606200791001c2d201481d0358002d010400c0049840c5600411080d07505590412080c1c0780c010214178952080c05c04008001184000c01c068 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 66485659 1250 66484409 66484427
    0x70906140d020d06050102010b03010c021005100b03041b0b0a120525030902150a0903030c050a06020c0f250509100801290910052206080c0406050f0a030210 69
    0x2103074001c40d00c5240240c140c0001c4c004070310030207000d03510f482914502ca04040c0031f0081c0d0421150002d11b1140b0441e5110030003403070000c1004401c3d040144002c1083c0ea180d200440c00b030f50003041c8242e09040603118101240180d40d0000a100030308004a9102542125119160040000d0001150380d601900c614078050003846041d06a240544c80c403941c01c0d0103030300100c8114000da0f0000e018104000c408485445882c0b041004205c941c0c2041001a10440c0c038100b20620640a480304d000341580c890b01a0b80241c038601405802140640030b40103400c000c02092064054a055009820010140b2407440a4050540a803c000303000480c0320950000e12802001d04100801c105844000070001010055440c121040c3d10346040c00742178500100864041c52800c106021600d140000304082c3c0c0014010110490003000013862040e8020700c1003100401d201406000c000c02050100001c0b40c0300d60304039510075100c4080c071408544031900c81009a0f64145ca01c0904038254081c29240500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 66486909 1250 66485659 66485677
    0x509190b0a06020a05011a060715020c06011212030c080a1508030307020706080f010e06220e07080d0206130f02010c0b041109010504050708040b0612030408011508030307090614 78
    0x11a005000441650015051890320301690082014807c190300d020650fa8400d28030070390200040c010b100106a40240410300f54844400040c80d1005203060036043c4042644203690141e60708840c039040c00044068038110000e00e1a040001841800001c1c1034000c000e07095070101503503401408500c030300400c070100107003907484116a228034003408000d603106458014400000c0085011900109050180301e050301c03903e50f100910341c0e48a00c2801510040032202280035004600d1101c1600c40302d11500c0380140d605d1300500b08103800c00301000c1c5841d605641c2103007194020b1007009102075504031041e0b00250301142211b8400160f0004a841d01c00c2e40202411903244401408208001c0418824462030140e881d00070580c0d9070720410044a00864010703000c05d050308001400155548400c0380c0c0240c00034083c43c484c00401034070a180d40c025400101c0b05079500c0e0081c1c00a03a90141803c0001c0c018480114510b2824840c01085504240300c0d803814004044d58030fa5052010b4020380d11504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 66488159 1250 66486909 66486919
    0xf091109092109090c0c070b04060807120609090609030809160e04020d0c09060819031d03031c02030619030210080709181b050307050f07140a08040815010509190b 72
    0x2045c0181450b03160382c06441b40d50144d03c00c1981c0020010101ca0907034044440e40d80750740ea0155030365081030f01d50710180d00b1010300710383d90b408011918880c64820700410a004040014580b240c41c0740c09000c040d40503103404110307846406507441d40c1800110311400d95410310303010906074030b480c40810001101803c00030001e8490000218240c1d44a50000040f2516041102c400d00042071500d40090b00b100005000940b0158400e212001d101d078281c003801c00082c003164070b05040c040e8034150700200c20b072101038603a030000280620340c940040b001510f01104584004d11a00c0d540c00a65a098076030659800d00034900005291540207282a10082c81440304502082090100b4003000381540540c43c8512007080490000043c4250152449101251038242c0f80c800d4481040d89581c102c0d035011965010007940309c01d003a0500b40070441d0340e248900c0c8101d03215802d0001c05810561220081101c0140050040040f681d03140700d542c0d04510301090720220301080b03201c0300300500581a0580c2e006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 66489409 1250 66488159 66488161
    0x6060729011d010b0a05090616020603070302040512010209061209190309061d01080711030c03070b0103020a080606011205071b03020601180501120b09030d0f09110909210909 77
    0x41d0b015840042c0b0100041d4614519a0703296003842c8104e00458011100288081c4416036041c00c05500610400c2c6004c0c8040b1421402e90b130000340366500423202c41e0300007500414200442e080c188002c910b0b20034268000c0d4240341d5401d01040c0d080c0a8250b14502d14408000412040801400450601816041000d070540c1c0e503402c010b40804958446c007000202d903049604407680408840307c60101f8140d4070b869107615051801c0760900c0510f41028041e000421001c207580000700001e1090302d1145105014a40c5180108007441c40c40768403004954125804020341a139202400c812486154640090a82c80e5103204076504007581d070060041940e00001c1105058000640c9412101070a200075001f10700c03140f40300d0070f0700c00c00e200f03002e030b80c07400c3c0369180000481c11049543e00c07014100840382800c00d0080044241d40000a10352f0445070b940711418188443c40400d8484804240d9541c1c000b81011020281d843c001000c202014202040242c0008142c2000710b40040d88010b05803903003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 66490659 1250 66489409 66489419
    0x230c13090209130b03120f04080f06090708120901081e0a05040c060c021c17040b04030c0501090b07021002030405060703030501140a030f060533090a050606072901 72
    0x35030001d030040c3d1140b14810701d04541006180201050110050b01074204500d035048014001e800902e5003088241e8148400719046004000e05407140701440020281810007400781401c001c0d4a40010403260044600c1d0220303140350354200c501c402401c4c81c2030034140c2c0e241820704008801c10030561000445200038080f0081807500014041c50043c2901c10070150390721401d91300410710b6000250040442c0c00f0440342050a0f00b1048801800340c40c041005030950642c1034150347c81500246980c01c1c001c2824410f0050030340b0b40d4000760100703081107010541050700c040c3c1c10b8010400024840c16a902059030464070034001d98000701400f42180b9100d414034507000d80540300034024000d2894062403240340c546400242c4200300d0b9004004000c030b4500f140c0758440506001003068441c0e404051085c0401c101c01000c03403000180c2030301e41c5010903000710f08104540002900e014603071400c0800b440410b42c0c1d980c0071a48490341c400745801c0da071b00069001c2c291007c040201004603c0000c400029 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 66491909 1250 66490659 66490661
    0x40602070212030a091208040e042301060f0504020c10020d1e0b0f09040f020d150b0d0201051603140705010501050109090213030209090c09090d020c04230c1309 71
    0x3030580308072103105410142c5901e590360390003903407201000211000b6003000700c1c010814941341c0c043c2c005c00081e8900b03a19007101c0485c2d9102a101101e003041500d2441001810110040d1000c15440b00203104461426040076134480c1c9034083d4a114940c00555440d00d40c0041065000040188000350340f1041c2c90401c00340200031142c030a03c0311190100c40c0f102c002005109201100c00000d114103800f1040b4000c4c004607070801401180c60062081d8111b0150303a802c034140c1442d40c0300700c5a0100d402402c0c094071050352061102680556064401d1400507a0032500b902c80005026008120070a114142200d0558207003228034002d171400a407003014000d040d00308034140c550030f03290401d6190740e42801c28200c0c419403412203161908140207000502d410800141c100ca07008007240d86a00c04200001e0110000760380c803104c00d03485502070340601c0c1c0e0103010700c6141e070004980070000c1e140200d926001c2e0811100d46400060769513800101e1500140341078907122920407907905034035500c54041d58 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 66493159 1250 66491909 66491917
    0x608070503010b0f130b1507050a0201170f0a020f0d1a0405010509070c020613080d1808070305100b0d050a0305070303050c0306130e0f010903030510050613060521040602 75
    0xa4001e50070643c80a4041c02c1c00344003101c1000300607004680c0740301c000c8680785c004c00502c1c070041d034032440c2c20350144203500e500005045014019009818030322280d20000d03004244501d54002c000799640e0421001d4117030892001c0c3d20030000c0e000961340701140c000b41d40b4944200c0040c604103a1410400d000081380c500c90300c02c107403102500c041000da43c0b510200201c04004850150015000100c59001418100c02070840c201e03030901c81f24251034650603101d040c10040040100005ea400400d4030460544105180003803040320042e0607503900310384071251038021290402c01c495888044007030f074603192a19403005c0940c004003964140300c141d1038020031035803265405800184c00e220204114031824400c41c2e025280c01000188410500c210080241102d01c050382170602828800703290f0070000780140c00c99284607a40001c0c591030040c0000480782c1280c2c002900840f070501501111810054000094031101e0a0450b182e80d042d240e500f690311015058012910b007460184020400c036a0054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 66494409 1250 66493159 66493169
    0x20100203070c06090503030d1e0f020c010c1e03200f040e0105100c0b0601090b030a0603150903050403170d021903051b04060c0201050c010516020d08010323030706060807 75
    0x10030700040e51043c04075455142c900071194140c000300500b24005290b584071a002000039210005018210704103207013260018103681c1c1095400084200003c0801c0c03180b0401443e090424030355508018a4002d000284030b4010030a03da80e420314005103019003400c40701d0b10340380c62881a0b958103085410030400d41280c4212107001100c400041006e250207500550522500d0381c4100500715261204143c6100c00742000b414401c03a4130010502c0c03164030006500c81d800012001c503601d03256180105e01c4a651601d4084102d1400c80c54100081d400011913007200d0b0402075400910b03246215800943c4034030740103100800d20000d0b4094004101e01140380303200c1e0b803035201008160307907104100e401514060f10031000c4032410002400032601554000104034018541107040907081b000715400c44a040d40c2c009401c4000007282d0f000103504100c04030102c4480d01c1c141c4100d5156903a880c40341e01d03805041c8e0000c0011282440300c0000d080003921500d6800c00018091070ba50349410030349036040d40c060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 66495659 1250 66494409 66494423
    0xf07120c03170f04061a030703051b010203070804052b1b05010c030807030507020106030503040807031e0b0a09020d050d030b03061609050d0201200d08010905090a2010020307 77
    0x182c0300051109010051082001148030b19550f5515540c0030000c080c0780c0c15280e013403440400c03a00c055482c10004d9102039072140004140c3e445070051030302c0d40029000d101904541c003c10035100040e840d54140c50440e1030980c0c040311b08038807440031001c400c20015507620000981c0d04e1080d040c001507200240c4a2107654801080d560348407801101c24114079030014012070802c8001c180300b640b2941c0001c1c2c0c4084103200004440f500c9a0300c40303046510641c400050f5500500080c0107121a1680b206108010180c404241c0070701c654a421005000410040d03020342c1d07175020403003952203150748049a83c2d400801d984030600c0f01e9001074001c000d03422140e4002d11406001800c01148580d440c000c050803910390002a52a100812402840740f140490400c0301d0f443c130080181502d20441c850404042d405495407000c4100000c10346001603010684180c103001c1030064101011545502c880d80010200d0b040d040c8542c080039102d413040d100c0c1900050005810180c150340840603005403842605 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 66496909 1250 66495659 66495677
    0xb031e01090e0a030c030201110406050d0f0b01120906090206041707060503150405040503070b070807020d0203040501090308030709080f0705040b0907020d0c031112090102010b0405040809060f07120c03 89
    0x400c034011542e803410a80e060760710948086011034010080e00c00c096203e88004214192480181d10058001c0e52000c0301092011840b001e010105001e0000d54030b03410b0740d042210b01c1c40c0c000001c019200d03805c00709403410b81d9480c0c030809003d0140c2203884507a4024088079038459640030b14400354001c0b481221224002c00301d022500d11311840031240030306410702c1c0d00c520245880c41040000c00004d002103c10388000c2010800061100310340e0b522488942d20750844501d03080c90060704000c01010780000315001000140616030b000403144c4180c80d0030500d201e8581d41c81d0101651648042c3c0c01000c0c01d4441d600000c44400000146402564030588051103080c808905019021400759000805a00102d840000c2e081c400c140c0440014020f00d00010900c00c0c51041c2800d0240c22910f550031400006512505560240038000a00009980410052401c0c1d1a9840d075030003124841882644001144c0d02101100c130306031a0105c2d004418661040480f0034007420003401d003030b4120f020880d050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 66498159 1250 66496909 66496919
    0x60504090e0105010303081504140f06090c0a02120d0b0d060218040501030c170a080c0715020a170a030902040e0a03080f0907030201050a0306030b090d02010e030c0a02040e070b031e01 81
    0x800f07a10b048a90585400c50f003030711404070f081111142c45101da500704c0d940701d4449c2ea18032001d1540501480401c0d00c0c01485091404c00d1100c1100c006100e00314080e000c001e064100e6034005000780c0c12021151801c0d03140c6803a805000040d21a1818040d40401548030110500541d5401024426007041600410001d020144010f8400900c405401b6060100301040541403000000d1070508180056400344000365559a810342c00013001844560b02c007050601a80c0d0400000c080194040e00040c0b002811560fa6510f6035058120303200c01074503002c104081d203103004e1b8104c000c0c00d50340280b06001001c60340301c2c03840d40e5001c2d00006500040c00d80000c02c4e20f0503203d0000d00d00800940000d05040c0d400d58006442c1548620071403000c0660751500000800c40384240346001c0d0408001910140b8210a802805c2d00d00004c2000401c1e081086160f05000e00010070062983d4141e501040b5440001d1481c2c1c1044020303840f1909074900001000b29281c4481d4540c066000c03d905004802c1e600c1d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 66499409 1250 66498159 66498161
    0x30e130e16030c05040b04020418050a11070f030f11070608061e0102191b030f0b06040216110402130b0301060906030501030309033c0b1b09060d0213060504090e01 72
    0x28800584842010882070082e1704040d0486210b0f510058400341c40d25644402038411b00e5034071075040b0300d0150b942d0240321615101d4002c88400741d81d0020341604003200d5449070a43c0204200c0003c0900c004146261041c1c2d0007015a100c1400541055909030380ea9650094881c01f012a00181f043c0c90102c2e0301ca44240801940100541d410790080c81808026040c6441c1d40c080d180094400419521030b40c00c1494040078000c3c040c5100380340c079400070a4036190088000c90081c0c019442a8014855203c1c446898500e40f02c42030382290080d1301005c0d1080104000b8850342e400000200001200420505050001181200c0c240e68800701030503030fa448100c1c02c0360028080200042c54044041001c6074408180e660080b40460b601d100c10b070200d03900d061001e601041d201e140c21004400c12010b00000d00c027150340c4016040f48104c042901803142c40858443e44040314800c0741c01090100c1c000c0d003182d0580784c844031050300c4555155282e1340e0182c0030740c00600c946c80d0040e003805d086079054201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 66500659 1250 66499409 66499453
    0x1290a03030206160210020714010506040e1209060c010c03090b091c0309050309030601030b010906091103010312050d05040b01050a0602030901090306020a120f021201060206070c020d030e130e 85
    0x1940600126194000204050051310080d082180708144c10325181d42001c1c4003e041e41d900c140445040301c40807406e0b0b242580c5d0300401091003180b51100200600c0b00c003081c40e5100e910407401481d0b44840030130006580740914400c1411a620703150781500314580690046412500030b40720402c641d520040110340d035074409064122844840b0096045580c000d41040f0201da00c90700690342480403100110386007000c00d9005458000d215001088070701400d00c940006000342000a104001007414401480d102c184801400010401d109a15891080c0c041e1030a00205007002c0c44181004e0601410345d4000780540f0707104100c1d421001403902c4c000401c5407070861040c4c4491031011324586405000750001026030701400344604401130410410b02c681543d180d8034440050b290520322070030440020058110304190360012083c401c8554105100c0d01003180d045071400025038203440c086640030004440207401c41c4016005000e0407a898202d01d05d100502c000300c400d0032494050140740c01c0d003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 66501909 1250 66500659 66500663
    0x9040807020d02010c0506090c0922020f0a030c03050a02100f0206040b1801020406050d14060303030f10050402120405010e0d0e370f050603040b0a0b01090801290a03 73
    0x1040000d50014100b40306000c1a00e07005050084401d0029240e46003031800846000380903070020600f03010186480d080c1c041c0c0000448064410a548103030480801440000c0c1c003901c18603207210b8a900351380d98001c2040180d03900504410046a60b031a1480c1c1c4c0d02010641240301d060800010140c092140340c091a00300d140c4d50081200d900e440e110307541e011001401010089005c10310960404500340001d20040c4a0303a41c8450795203400a4004089561002d00000700c03d2421040c00610355000003501d4001010003540c44454880c0c1c0640741030203556a1100c0d400c076002007400d49505030200b40070351085000306d00902c0b2030083c0185443d15258034101d0400130586010703418082d81424519202d01c404c1450314901c2d0000341990b4001103030390000e0744541d0961604414440f000194443c80000c1106a40040c10360400e44d03541056100020081c00980da0b842145104680c8140780700402080004020007003c94860709046d2942c400a2100055a80d080142d146a06144010a0840b5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 66503159 1250 66501909 66501923
    0x3030924060402030403140a020a0b01050915130603150903110a0b0a0e030c0a0b070f05030106050403020409050a020904030e0a06091805070c0506090109110103180803060105040306090803040203010b0904 90
    0x5038907541004025003001d0800e0b010003482400203920703003540500800c0e40c03141039001020034032150300e0624000300050300407501444440e82446401044210004106141100c0584001c2ca108103190000d100c198400f03031002e070060b2180d81c600c202541c819403a860003562440d42e070120040c4503a40c2c52400c004000d008407540c50000e90b00310200d81c0074000f18081d501c241c0780b4000003110074500d82103142200707440c0e09180400780810b0700d4101c00e081c6001d41c65814002e003503616111015040380102e12010b8011900e50001d40c080201c14440b8048060b4000d0420906041604000701501c58490120f8020060b01c140801c1482c01048100700700c035036202250482210b20603006000e00700c090a001c00340445032082c500064424004c0c103203c0c003080000040c04201a00f4100718a103d0844018145450504800c0e0354104002c46000b00640101160361780e070301d400004840700e105650020f8071540c41c140851082150000c0214003d5002702d00034841082d01d0810060044800d480040c800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 66504409 1250 66503159 66503161
    0x18090b0a06171909020301060f080c01020706020604030806010909051017010902060706020c01021605010b0a0504050712051b0703090503010606031401150207030f060510060f090b0f040f060203030924 88
    0x4250f41e401c0241c3d0319528401284102d07882e40481d09480b45c54000b807491203e010310a10150342c0030400b402030510244020403126141500203500c48001500250070800c04d500000c28590040032031000608110303d00b0010b501e4040f5042c2e40c0000c2c540140c125001d0701d001403000d601814011414011380052400e4a0200c2c2c03907a49070000d501100ca001d4255400348480754001c0b24040780c50000742e0040303002144140030f8108004400c5005c0d00118030640c6440e042c001c0d15940024402090740c0510b000045540300c607d0b01400701c0e40b113400c0340c40c8444000a485e10030140c2c8070940004440c8150000e011030358483c42c0590070759400600c15002c1c981c01c540100300d50040c00c0e410b4012445076005548090341c481e1603550845803070740c03415100140c9034014014481e50501c0c00c00002c3c1001c0c9441c51100d10040b800800c1c40c0710f90300c50a41201d501003241e1036140d09110454000b084e2409180061303035605d800180d201e0304103c540808a010302003c3c80c100e86a043c500c280110250410501d00e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 66505659 1250 66504409 66504421
    0x90509070501030203060414040b010e060a0e07030b040e07080d09080c0d021012020f1801020705060306040209010306170f07090e1005090a0c081c050f031618090b0a0617 75
    0x25007000384003c0d8000c0d00c03011231580450040503910b0081c0d025202c100c03865070401441841440010b8032850180400490401030700c11581c002c282c015400b45408243c2084040000b0080d00e081c000d14846402800400110f00d840054809a054042d803512400c1581e41c0014a440303001c40c04a40380c00c129003180081c0180f9000c0e24441032211581481c10340c2056801080040b42c1100111740c40560000403800100040c01502e400d041c5001d01c000c0c002282014003048443c0000b40410b8020303a000700d900f048580c003c0d0454806000100b2801300c20700c059200e6a5a2404a050200c4541c02000707030128208801e8003801c401c0c450345038018601c0d100c40d104504020100201003c4803030050000c10f80c002603095441c40c0003400060000d041d18110588100440890385500c58148001000006039040d2200103807540080c400340c81c054100110302007514070030031240c0c0c15001e01c0206440802c48034041d6000414800007640c040325030949440069400d0070307120a0b117240541c034502c00100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 66506909 1250 66505659 66505661
    0x2090402060f040b040501171504050603150f041b060503010605030711250504090b040b070c15060e070f0203030414030904020a0806190b0307050d2c0709050907050103 74
    0x9009032001d0041450000401d1851405811540003148903d00c00102003040d9a881a405540800d280121f1601c4d0304114080c01205280498068084d540707640008095a5050100100c200c1c00440d010800d46000f01800d284654204c6045410b020002e4007400c038840d40e002078500780c07003054135004d255900300b00064a80d42c000604410400403900040080e001081c011885890030406d4040c0c41494843ea803a400c117061900868042c500c1c000c4807201250391a042d41c2c1e006030701716245005d00d1b101d24808844001180c900503081c98054200d4000712901c681c00001105e070624180b40c8151240b24044440141c500700d10801a1720610120380030420607103080c40041400340440c6d140001c000d01150aa82003410441d0119010000700016820402540c04035003221b880d9800c0003508000100540b03000142400d010806c010440c00c41403119684083c01990003820b08216050120f1185101148400060704541c0034081c00092003030242c0c05118050007589001d0070105003000d00441c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 66508159 1250 66506909 66506911
    0x9030304081303060e0a03170903090f031011030a05070206070509040c030b120706030e0a0f0f05031201030807050d02010b010f0f020a0c0602010b03190b01030201030b0126010614030105030a0209 86
    0x290141e02c4660000f000456520960b402040c00001074001d64000e801c0241c031110507400c82d01100400c600c204904004040119110f86108960814a821024020070725220b0b0180c484e110341032408007800218082c1c100610b110707500181050013180d803000001c0340c0340c090035183e01001c0b50342402038110328500780e089041241d246145c005107880c500800a001d02100300c06851180e0441003041c481c80ea8076000b02004040d02c5802059021003aa440c0000c2080300e0201a156000300203070f03841080b0050045820359200220310215558503418078000b2a0b005030342c21a002d200307030102c002c0600d0040c0a00794003444161242e9160340308010080c0d82c003442c0004502c0460113280c403001c2c0010150b85100000e492940c1c0006440d400c034505151400203d405e0b0100c040c0c401400540006010b2001203054950a20340818044803290051b61082904030002e2048600200b0041d207082c440c1075001e049540e00e50f00c0419802c0e01d440f41625610081c010f990700354102e40b40020244c05d01501c02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 66509409 1250 66508159 66508177
    0x910060b09090c070c03030f02190209070c0507080105070e10180311010314090d080106050c030a0e0d060e100b0d0503071205071a0610170a05041e0b0604140903030408 74
    0x41881c04d0340a030b0310000c43c88555001100032845600f0194141130307040002c00f100a580c100c0745c9130041c2c0076800150b0b41e090000c0c04031041103200c0d5040401c03c40c0c240007140040071510f00a200c01c0c10000c5025020304e10b0300d003c40f8001c0d0703d050040e1480f80d1103160700344500640e0081d503008039415074a0740ba0340d00b60300140a5050503250002d0054080007840114414075044019140e206c41d0003400400e600d006034004e10401c102031116903141340000c030844460302c5050504107251080d000100b112a610002c0280507549482c84280711043d012900404c00c3c4420384007000489102410400200d48541001d00b00703510501900001814070840c501e0980d2083c00c1c000c2c00e00d01d5039610b1800341c0ac061994200c1108140080c0220360601041209540c2d4190506561100000700c1c80445c2200003007035100301d9925440464107125803414003c010304409818484209141c0c182030000d003100341c4160b8000c0d031070001001150004062051b008015030400346d46144c846d030b2640002500b00d0400d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 66510659 1250 66509409 66509431
    0x70507060c0e030d031a03070302130c02070e0a02030f0106090f051507170d0f09020117060f0402130501020601050604030f02010c08160c08010b0306060a1701091401050910060b0909 80
    0x4104543ea4100040e02d60042a60f40201d8103441008840002104d880c8809000b5400b881c0c2c01d00041c2d491303409500390081d0460300003448041e4120200e143c10b05ca82d000440401008043c410f075a03820350001c40c42003441203100710050b6600d40c821103241c9214483c804c0c400100da1400d001510f005200c210b11618502559804d180c00c5840704812103281000c030b201c240000040d410040341142c0a58034455a0881c010070807a0890380020f0312540c241d8100c185161603c600080b00c941d0341025900300313504081c1003151601160b00c0a0f6180b00994080c07240540300b864000034181c600881201c0541e54010441c0d6003102283c2d0055480d5a1980d90031a17080300140034000a02c811000240411405042800c98241c0341c80d80c1030b4210b840e5010b40c00e00036004070003006031a1702e41d009840f04642414000d03100d0280084120b500403c44203130000c02c07028070360b03001940d1100150041030042500005a99141103101404412100184140100030206101d0740c015841c1003644e09500c011303182d807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 66511909 1250 66510659 66510677
    0x2010f02030c04080f0309010c060b0126011a190509010c080c06100b0c280203010504060b1203180f01030204051201060e100b180415060e01030c030203070507060c 72
    0x581607030011500340c621160003040070080c5007010070602d98050b40400140d40303003071401e0000800e502049500580441d07158029a4410b0340b090310305052000d514002a0301c0c04030780901610100000b80316604a204045102d500707220486022504c4504140b1100b80c00045041d60a6070b050304014002811300446c0d1680c440440c1201c3c00802001d404400644111300e004900080180d216400640401c0020b0011091302e8500052043d02040020700c0280d04007004499600c0a800c41e8100075059404e082c244400c01c54260040001103400f110b0600329003114200495483c042d9100d0040743d02c0c201000d80307416080614030030300450010314001d8074241c1c6075008108040045402d509860703650704400c0081c4d00c000b2600c40d42015404502c020402d2400410000354010060100015201c40808443e0b13a5203d43c00614010707212014001d09541c2e8817009845605100b1415004c40c1c1042261a032645c464821a0302c20b80c0a51103890920401c0c0d00c3d41001405444070500c00c2c07001d441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 66513159 1250 66511909 66511931
    0x2280c03020a0308030403030c0905010f0e13110405090f060307090b0a0b07050f101802130b0d030504060f081323060114040609020f160809060304030507110901060813030201 77
    0x82c0b031000c0510f0150b113030240c0d00c0c2801e28004007221402142d07001044541d400901042c0e9128001d0909901c15280200c2e90740d10000c0010b100c0a40038198003207030b618041c0140a4400701b00c01410880380200c076800001ea0340da02c0040c04005d800c544207940368018800500c0420b94940c003000480401501410407591143c030b82d203080303074400b0100340c030154081c1076a007580c6a402c220f4021f1006680d0018050a00800190400302250f090001c2c03207120480311645031050317981c0c0b002c0035140e001000940141294203010304294405c0c003801d0000341138159008421800b41103081d005055254158501891586403004001d050fa8180d030f009110454075001117401c04c000306400f03042c0d04103480c554101c84108110071035032964030800c0401d00500c401c4841d2881da00503910416141c00d60001c1c0c190051402c65443d20488058980c005800b00c180024154400e01030092948604581c0da0109001d50802403d288248030700c40004031000001340310714a110b00034442d014424000810381c18908 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 66514409 1250 66513159 66513169
    0x6090c25030306030203010c0e150c030c07060e010215010803090105070219030b1f031101050c0a080c010207020a081f0b2b0b0c0301350105070305040501050702280c0302 75
    0x100d40140e00280e21035030240306601e000e2248000c2034885003081c03406a8007078404a1381c42001d8814041c0c500a0124000102c081d06004952140340c213003040c0c031045520740c03001a081000f0160788a005108081c0309140c1c0c40c4500403018142c40d0207070011401d0041300342c01150294404482282c00c41115000c1c1e0f090f4080304203050025521a00c21000b551415040982c2414102e80e980c604109984404201241c2260b06103040f072030080c038000da03072100c0c000101c1d4504a50060020203040f80064081014001075000d403e58502c02c0703410318441603170b0301d42c0b90303541d04040c543e459200c0740c01c00da40d80140003250f44802d45181c400f0700341844485100e44110a05080b0341502c02e0002d40c485d03010000c000141c3c0e007451340803041d40142800c6504183c2400b0030500b82d0742d044541076880a111169810300c0300c0004080c4041c0d08024032461401810017009040140e0b0200c52075800c2001142002d4004902035664080d0902040c501043c40540c050103c0304c0303030034241c80c42815100040003584038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 66515659 1250 66514409 66514477
    0x70305041d0403021c05120405030f120906010f05030606090711150a1116030c02030a06050106031d19020103051b0307020307030e0a12020d110301020d06050a080606090c 75
    0x1c005155203150508010f4141584c0d0070f440080380c1c0300401c0800040780c0010030b8604855884082e0b6070959501e00c0c00c940345200d40c4203003500941c40031a07403200110781100c210f4483c11510302501c0050f40d94a903001586000c50040c0e9030b15810140000d001401c18400c420b501c09001e250842c81c1c00780c80030321581483c80040d82d81654011080c104080c010045c024150313081c5148102c180b41a1385204000000c43c00400c00074100002d2000c0501035640401210203020341140c410042560b607004043c0007403280e0110301003018000c0031001e000d000003150302141c00404c003242d0440b0200c44e42c0114014000240350f4000c0c0382466141300049a4074501440c4508580d400039640c1e2003044c100900301c807004c824140d00c590240c3c44140135016401490240a55064455250308909480c20426061482108540540c400b04038441c0842da1908140b046800035076041c04036507100d001490f11510100c031416000b2550802058111903541d00801c202007521680041c0e86118180303000318525 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 66516909 1250 66515659 66515699
    0x61d040e0705190b030402121510080c0d03020c040b0607050106030506061905010905040b060904090b100f050a29030109140123060c070b030a090309060c03021207030504 75
    0x44441410b011900784040109007800401021800c070a143c1043e5010611005100078041ca031250b0341400c80d00c8040040d032400060b81c5052240e03500c2c042c1c0949178228654881c1d214035203c1c6c034000c3c20180c140414030502c207580681c068104d8040035810300c0098002500900d820417010016100030500a1042c13201851203400542a11f0400301d0400980502544e4000c060303110040d410403040c0c2e0030600c2c0c0021a0300640e03000c01d1a642080000309035009550711701c2d4005040100620401c100340510741c7c860210281102c3c0b42c0350712070112202e0003c40b0f0103000c0c1c200c05c12400512400042071041140190b02e000025241001040548119082a8040350340c89440300c0050000300c0100a002d40503002007103034a1400c1c44840084c44118a0668042e405020300003485d4035015800e22200d0040e00701c4150496817814800a4030000340070303404003036000030040c1401180607441820071510320340d059402020044103d4000c01c1581d848480200c0a120307082100051841900700902860303a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 66518159 1250 66516909 66516913
    0x50108010b010f0906050a180b0705101811060c010e0d030b210309040b0a0902040602060610180308030a1503050102070302062a07050307020607051b0303030709061d040e 75
    0x20700600000d498004050000001c0c410500b40c01d1004036444000e6683e0106240f8000e41c001031010600c8440a500ba00300440c00d450008500051003000a2a1000c40d45442070811085001c403840c00090071030800300604e45d480700c460080306494181c000d0b160007280a00001a0720b01c0d9202224648140760828001003901c482c400d0340141b44c110800007518115070400301c2c10003410f40301c080e100d20640d0751492203181c0e10090b020081d2110f801d12000382418400455a03252540d00c00303940da510803a132881c820080007001c201410701c946035079145103590810820070142103a4805496810043c140350005640d14215504406a100184001c60180b0300050f80e036101414002d003008001028691904018041802508062184001a5144455a941c0340c040a00e0726a0a61180c00c0300030354080d502142034810300c140410340846541140c060304418104040900d9280c0c00115119070201d01c40d00700c00c01c0110302444246405044101504000301c940700300003001c841c981c10000030b5503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 66519409 1250 66518159 66518171
    0x60c101404210503010510120f0f0b06070b0601080a020c0a11030d0807020c01030e01060902041d0a090510180212030301150302070816050a0b040f031209020a050f0d0605010801 78
    0x885101411140080035107611501a115a64000f60aa10042c03103003034000d4400c0d0319511440c0748030342031107103040d04102803e20650050210742070144c0020303142c0078003145c90010317a44140c0c80c0400c00c662880c3d5005500003060742d990401035401d2007008100c4c62085400b003141428034030061201107060b42c03007038240c2003c030040181410714052100c0d036203009006180c401c0c0a003040e00003c10245c242024070f0301281c04410401900d02510059009828450020a0200d4071a80c148011002142e05081020741980c03a00e041e4401d803040b4541c0500349070081c2000b0054007516400030f80c440000f041400180c0341550b07020608001515100280c1a0030110060260208030300c0d83c10807010241c0780130743c1840300c0303501c1d912114455201c800409049200b094030800005000a50495400000c0942c0e00e181c01d04043c00340e07551002003103000035120031000303881c131000e031196074242a00a000051030909000900202030312070983c2c0f980c050845a030034000034005004050103012408008100c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 66520659 1250 66519409 66519413
    0x305040f1e060b030312041202030409060e160203120403080a06030f030c02030c0103110d2c010b13090803040f02040209060a0c0c06080702060a11041503050916050f060c101404 78
    0x1124040f03c50035100e0340082001c810300e05402d0000390b80141d00001a594010403c102c140c0c034600c070355442400704a00f07010002034250032440b4168400c080b0401c00203045503204108036241d11451051800f1500700c0408100401d00c1108139640c452005100056055100d84071001015880101180020050310001d001c6050a02c40300c0c40003402030034280556540800100007030f0040b0342c03d01c642107644a01801580d0822020348850030060840d0b160030302d41c001c16040c040e090703811010b4040c81010001280b065110310900c040b458201d0341c0c0c141507484a595217003401b1140b9000380c0c0e0094090004460603680c0c440280325202c55074650584002003454140c0c40c03070b920b990040d024003160f14200302c80d50790045010740d0f01210200b400190900b4030f04c13880d0910b000d08c0d00301c5030b115480003250500d12600340d1f1141c3e00031441101100c8410b202d8a0301040341c940300e80038043c0c001d180c4c02c100582c5420301e640582855815641900c0d01681484a42c2d4220b91580344450309409914080c002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 66521909 1250 66520659 66520661
    0x1103040605100b0c210d0c090f08030a14090d0b011202090c03270f0303130303050f04030906180504020c0604020a0b0903061503190b01050102101b0305040f1e06 71
    0x189005201182400f42c0c4d854059194074580172542c550320580380c2101101d100300c0f0115031344003011b040100082e040c11400140341012030300681609038101803011a006a001007075481008840c0d498001c20329040e942c41038644c1040f541e040d00b200741e50300080001142030625601801a50200040301303046401046101d80c0c002c1e1002000190030002d10a500c02c015160360700e400c030042c2c1540205000540150310389406040c4900c031a000220501c4102500f04004011090090f81d05000701d0326401c00c04100841d0545004000c5104420308010042c000c80000000c0401003100d48900c656950100741a644480d0300c030402c42d04030100700021440c0042d0716402501d00c0c040d02c2820700906a011175139842020380419850708041c0b081e00b0a40d9010400b03600f000601545004541200b0310307084510240070b01580e405405040c0110381b80007413901c164410800600005000d10006c40d8003500281005401541c4c0c614071168254007140001c0c42031a5050005604040d825080d800d0001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 66523159 1250 66521909 66521941
    0x11060c0d060e040f02060c0a17031014090a0518010905071706042f0409030906030e0309060f160c1401080f010302030303070e0105130602160602061e0601031103040605 74
    0x8506290708000c1c000071400b0341c0070701c2c440305905446c1290707078114004c40c1c2894500c3c1a400248118002200d0b0068024a00d015500910b101f403098040700303880710030180c00d00e02a002c0b0315400401c41c0001031102181c0b5000b16410001c0d0403103e280144071541600c0c20741d070031130800341c9482d03100840030080c140f4811018642640080003a01c103a092035603540280d02039010480e00880c04070a04040d800300354040e400b00d064401002000036114034903018010070100d100b002c02103031910003e81582c2c030011080700c402c000002d01052408a28200060280e000142d004c003010040c00c0e0010000f43c282c450080c0038082e403903e42145a40413000040100344020000600c41c200c0b4001080140c4002041d00d800007064101214259495401201c20340074508107100000d10508002454680100d8508040304590418641041c1c544000307030790701c4c402a144024070181503180301d03c14031844c0a265801500524021508106004003015140c1040c1c030305640c0a95540d051002d5040050014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 66524409 1250 66523159 66523169
    0x509090303070801030609060b3001051306051e01180509030403170c0c06040906030b060301090201050306090c0f0403030302040e070201060303020c0607030905030f06010305160f0b0a11060c0d06 86
    0x103500c0d501d4042001403450806110040c0100d031074400c0d01080005540203804d1180c0e01070f101e145e140070b02058009181c80c0102d103034050031518000790041010180207451180c084100c0001200016945100060100901e002c03000641c1e00704000d42d80301d040c40514024107404680007640b0b501703a1807082c22244040d0640340d10b45d00401041002401d009030000400032000a0242c540d02c90b0000d05040c1b1100320700c1d06502050010300401d01500075400901500d006101c0d082c915900e04003814222424814041d0118800b400000c02d60719010741d2495101c0d030b940c00000d081a20a4040c1c1d11240c00641017203000c81e8012405122400112120542c041c0c00d910081c0051851501d0294070307051040d08150165a00148880505002d0101d92005040c058211a0400d88a1200b15150314007030204480134000c24a03010902d0380140c00300420799200703070100340701d031031070042103803200d51200050b10309001641203a841c204000b0b0042c144503125840036a0b9440390406111001c0701c80039008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 66525659 1250 66524409 66524413
    0x114010602010b01091a0c06091c0203031504090c090903030204031406070801031509050a0b0105040606140a030515101716021c051e07020a0509040b0a0b01030e0f030301050909 78
    0x4003a40e43c1c1c0c043d00b03110071102c00500e45042120b40d401440c010344610178404442d80b09108c10f0100040b800981000070301005910b0305150340b002101240c80740b200b9503608601024002d0000031a00d407643c01000c02c1c81c4520740720004070b90390718003007402d03546609421741c0030a501060400902c40b1248007403000840110280c201441c001c800600668810701010b0300010007022405200500d03036111a100f00d4000c0d080b24485c4000d842d000b41c42035003d01a941c01203080480000d03030076004411859260329030828083c20401200ca003100280401408610385ea1400f2028003415111503800c4259000300b541d495019040007c61034a40c110003a000d1640c0702031196100030341d25404200000b58a001e045565031a00308a441100c40340200c8000251100e15054500c901c9600780d80200503041c400c0d240303c60740707560ba041084014074049401502140644c40002c503426010b070301008031030405040001d00c1c0003d0030441740c504841c448080815a2000005001c04d10f4500c0540340d210b030007040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 66526909 1250 66525659 66525671
    0xc01030e03070f02031603150c11190f060911040b01020c0d02091e010b041502120f070c0312020705130b0f0d050106030b0a091a0108030405012003030702011401060201 74
    0x403115a4074842c00202400d4400a10445000c41d41c00f80808982520708480d120700054403818003103075003620f00c3c4400c502c0c0361034020307110741660090549020050380301000c0c1410540d05021800e0a0080e40c00417240d00c00b102044100148551046c0c1000741e0141e4800540d03001d204041c0011140800c985905552100c5540c80d03040da5041c1281d4040c940c10340d00c24401d40c8800c10100685100c40c2900c0c00344010050020a100c00c200001e0412036007001d8a80c002004e00b841c060f81c451030091041c04882a0800140380c16014031402804180e02ca100340d00300442c3c0d25150203030356400b0300e84c1f504010b03001141c0070041490441d6000e100440700440400c4400d5001000a44d004030840d1f205018440c41e115110134800b081d4424401175400a44405181c5441200c51008103125602107521140200c40c40500c40032042009045e1014117008529143c1004019112011449071300c0c42403c600d44095034504078103101079800340c021a0000f0400080c2500360030401c44050b0801d504680c134001e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 66528159 1250 66526909 66526931
    0xb011b0b0109020f070501020a050307021501030b01030320010603051c03150302101707030902100503090c040e0709020c0c150f0d02090103021b0a03022401170c0a090e0c0103 77
    0x20402811511010001613071107030500d0052001d401001c1c8054529440403481d1240e41da080001103220308810341c290780964003403199016201e5802e00015000c20b04690041c40081d010f060300b00c4c0441900502c4460310740e8241c0d0894251000b80d00300300e80b0340d0030203240720425042854450300d010519017024030950b002c3d0707054000144810b100180c0704078400c080240c5c0c0d1030300910b659403004850303451075901490b00c00009000780c04a80e0049008003c0d04100b65126481101960b000c0c1803101c0c09085404c42480030440646a41d426045d494010500300007040d41c40c620080c100c45441c030002c1c0104860000030004402d800c0940b501a608042101e01d101206032012a4090450202c0c016150341c00c13100124020702803146042c8402032941104100200c0010b403022600b4032a03801c4820303140c0c02040880000b0420041156000001d400501540d030008131300c2070740450980301700c0f0f68031030341d440002d00e204040b6481070302c0180d0f44404d183ca00c41c0044c030149101c01020300f0240910b003418 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 66529409 1250 66528159 66528173
    0x1614030403031209060b060301080105011401210515060c01051602010b0907030504110409030509030d050901020d0e0409051507020c0105120402040b0a0312030f0608070501020d050a050c0601090b011b 88
    0x400030018184da1032880070104080c07540210b01114010344510745030342c3c48034041c900808082c0200f14060b8000c1c0130444496110705d4552000150103a41e00c94042400300781c0102030325000c0d041103942105120024050345490000c1d00b44408008008125820140048144110280c044008590601c1c403003010648601c0100c0703801041b54603000030540e40e1410b0040c0540d01e400c00984d0300c03034104050f00091650010141010100840c1507411051501c402900c036480344442d100c6c05a0444810940c020f03018010f000aa08801b92001c6200d81195850a0400300400c10301c400d14800202071104036681005032001821080c28164503080341c04c41c40403443c00006100034800c6485140051964840083c03080046500008620740c0884c0070a010f80030309403078803034105094900000003959082c0041d854003110010f8005d40f4a444400b107007203c40394449210101404810400e151032031200304030050085c001a200094000e02740030004080340040c014842c000b007011070301c0380d0104500d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 66530659 1250 66529409 66529427
    0xb030a240e13021807020a02030106030c050f010305090607030f0209060415020d02120313060b13051e0c03061018030507050111010e0705330d0c11100b0109030206161403040303 78
    0x3031080b400580c0d18010100d1810401100094065080032f10002c2001504001501614400c4031580d003035140350001102100d104860300c0303202d548000e0224807124002e0b84441058002c480c405407501c031518000c90a558095032221401e41c0180070000c00141d030601030b1080c40101440034109080c202c408141003400080c1c400a913480c422010b501c01c01c46160301c5640c00d0240070304441e0200c600080e45900424080360741250540180d002a0010b507100c111241c40307102e0054209045854400070b2004c841c6040c02d07440240a0306203140303030500302e1412400006600c00d0004008003409c01000520800700051014031700da0500020003404180446c2c1c4809644040e140841401c452200c01101c003d030b0501020b580d038003200c101d03019030250749000341000c00c480381081c4488941164100c907003040c0c1030350100c0d50313820204211240c6d00320342c4c100c06403d0005240110816413240c000961a510907045064000722591407003082044241c00c1040030003451b0003550602d4035640300605250f103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 66531909 1250 66530659 66530689
    0x309030406032705060a061e09020d090f0803092a151b06040c08070609060309080910050309010b01030c05070303050a06090603051501080a08040b030a240e1302 71
    0x501d5074860341c00c06101250b0701c0701d83c101c5a140b0541c5004907003841902c2e45416504080d1040c145038000c0b88032101400c201c0c0f040a00003664551461520034a500250491166405225214488200880c0340e001540925038000d0180ca9524144034a00310314000704d1124008004c039000d0001190326010b420105c1c4035050a680c1034a111000d00043c9900c0e210303440e0000009038401920403806003000030300703a02c034a11031440411415103600015543d80d5180c0304040c0001d600c1e130340c02d0000c188a03420032508288503403461414038260300300141c4007100361952500054004010452100d000340038040309444203017810861580703000001003ca2241c0c541c0501896241e1000c140c088103554040300040c5084402081f086880385070441c4c803140b42d0800b21032a11503110000c651300b80080360403050f00e603000c50b1003803529282c0314120415810041100141c9640c17068019509080000c070752503010310002c081c4280e40e003403814010707105c0740180c59454a1700c00f103255440142c941500c0040340d01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 66533159 1250 66531909 66531911
    0xa050904060e0a051006060e04061a0a02150c07030e0d030914120105250527042009040f0b030d1815031406010305060d060b010203090a030b011a030903040603 70
    0xb00360a880301c0c5040d42a01000706030340300780403800c140c0003031a910250a0b20700c5991071400d070714014030820068902a0040401ca041140d06d11141c0703071041401401075003007500598180820035103c140130313017600701c80200a00d00001001d4017003662103600d001d000c0c0b90440d007401d02c02c8055100203054500a020b120401d8003030321340c6105240d40e0ba902040702c03600d14100900651030310b0300700d021200d1103c41144001030240810200c2d118000c500740c4014080510414500181d00c00182100c60741c2091025009684c030382c1a111100821440303d1807544800c200a41d030b51084909000c02c403296002840d0b01c072441e10300281c0c6141e401052400c0c408030b207850400401d0404071510310399010310780d1040005006040c2011121501034100c50080702c1d0000c04001030341d0311a1300640c1038500440700181d200c1e521020640008100781e210b081c0c400c2e41032040324101400d03c000300343d600300c0c2e5401c1600e007414003100404c01c420501d50b420b401c0c182010a10340c1941031000a00e0354a000d18081c000900d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 66534409 1250 66533159 66533171
    0xb0a0906140708030a140f01080d0c140105070306030c050109180902060f030405060603100c020606090411040603060209030105010b0715050c07080a0309110f03030406050c0106030204060b0307030b0a05090406 92
    0x508803001c16240b4440e003107460a96241008100403004142c64050780d8a00300304c11b000107041c01d800f94075081c1250f03090360140811300c4440c00c0c2203602450f0010100c0d00b0200030052050400001d2285500c14005902c0c0020031070b0031820864001e1500741e000c181041580340701400064103d5060f040030b03c200304000b0440080d51310014854ac0903800c1a8100c40001000300418020001600c6015100580036a107004503100e054009444150b070031240940d01c07040119034142040104258400d005080507403581070f03d500001d0035107140b60b00595006402149400803481d00384109801048001503603403900720160f4601300b1240000440301e00705075035100002c083d8410307142291103050f4041c0d0495600e12019030042c0061035506019180c0c020000e043c4001800d1880d01c04104c80c800070011810645040c40881e01684480b420101075500c4141c0040140c81d103000790b1340504103200c203103601da01c1c00102c000c00700c3d03140410760b07485000f2906040081c0c0e01c81203215600182c202c0c00200394 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 66535659 1250 66534409 66534437
    0x102060129071e030909050108070302150304260405031212070c060207170c010b040501050916110304031406091906111c0c030e06040203030a1b0803090d03060b0a0906 74
    0x102409108000220005600d0400130140d004260805540c1304031000c0106980729444140c0d90900ca0000940003a105106031528000d29006036a03c280b00340a80c07800444498818903120002c000f66007815040403130180f0062600303100502c03481919040ca903080601c031043c02901c0d000003034501801d0102629500091085640444040d0b07a04851070304028486200e83c500c0c1988429009070301946400c0c07140080d85064001c1c103040f154020040956525011208100043c20410035818800c0312600b11854600601c090401580100c0312000d000151111160078400300520300d8000303401040d86900d481d000c600c4004401900003100040010704400700307511a100c0e60b10070085040c031009082450320060b401800c18914240e8003440640501c03100c29543d06e01c10f0710002e47c190811300060340c81e18811a41552065a0411004100b00071500c5a902e141d1094409a0355600042d0325040095010f0180c13000500b0500d0011b49405400d010080c800c1070540101d100300404440c0c841c034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 66536909 1250 66535659 66535673
    0x151602060915090f0f0a0210030b0f01050c010e06010b0d0507080103030824032d1b10031808030714090d030e0105090424050402090d0f03021911010206012907 70
    0x1094000034001c48022005c07102d016961800700117000c03131284219003070400b81584030b030213110500c0401a00142602a40c107006455941045034601c4180d0350312801000c0040c41002254001c040130030601e65142198030050703065503030040044041c400d0f50801080007039401440f0942c4039202c004286070824691070300c107030b05030360500380550b02d4445c1d104100398401c410340445081c0403171070341d51540056407061f60a403103030340144660200c0402049580200d0030030b8000401041002d140004581c6007001c0e4210910f1501e14003603500d01c0c004803c000e040764102d0300903d201500030644030300f00745031400010030902c1c0712040101005071030005210646d01800540c0d002441c010414450300080402508444003c081c2203014840900400625801d0500c2215000c0760042d14100c224000381c0c4860000c8000c3c410110114811211005003950034100161511441200140111960340c1d00091a064040c1c0000b003d8101d01c01e68a0a004040b40348840c1e4030b1403185195844881a080c500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 66538159 1250 66536909 66536923
    0x60f1506120c28020c040b03010609090311060105011d010e19060c0b01050d05030406180e01030c08011406010219110a03030512011205060c030402040b0315160206091509 75
    0xc81c141020040c032007a00b9028025124101d000441d1114030340d2800740000640322800f40c1c030310158100d2142c3c1d8000b424940c0007081d0b00d01024002080880c1d8030a140c00480d15540410f500140c02111341c00c808810030300c446d600400707003480d282000a100c15420387c1d003424001e150506101c1540c2e0a410161114a1044c0d8884012030010b003036166240c10183c00703080c82c0e20007200c80a108500104e900c1c40c0a15404181640200045040a040181c292903130980c0940c107024002c4440800100206980c1e000d5028500c01c6c41c800d83c0e4549040451800e40d4a51040351300140466020003080d039900007009040b6480c0f00141031400c0100382025031002202081c001d410a501c444d001c024582c001000301101803114080300020784c0d8802182008810b120700040c91b54006a01007041d07041190f01958120340002c01c00030303901c80c0e00c80001c0e00c0c0c001520300d0710058101c0d09040140c524240d200c0c0c0e00e500781190016108614222002685502c4015505464031505501164880000300414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 66539409 1250 66538159 66538177
    0x7060302040b0a0804021914030c0301091203020c0f0a0305070201090608060f0603060112110406020705060a0c0605061c030215011e03061107020604090b131e0903050c191103060f1506 81
    0x1021022380300c0c4180b00b83c51070f012100078040c0c810702c0c100c1c0b00d09040500c650b800c41038100140300c683d94007004044000e0750080b07a40240c41c0c0b01d9044000340c0c400060002000303e81c402d4542035582c100341c3c400904190125070008080c01048001c000081e2681c4580c4c00c8038a104403440d50356540da00c00140d0300c3e02041180c18510500c0c4c100c490b200500d021000b00180c4015400700c2d90b0306903035941006101d2088141060015014482c1c00e800503910341c021070382040b4020300b8640200c0c40302c1c1034505244903040c802e8006138010380407d10810100c0080501400c04450100554035416103940d452404503c8014882c6a0301c50000001c075040c00f058a0619500400d0300380d54176541c02ca44e00141c20f8554099100d06680411040c810956201d205100020b100c0400650140303184003078014066464290140301040202442041c01402550003440b034411070600a02c03402d091100e03207101841c035218000c0e03108000340980e000c1c01c258090740c4030250160030710000c007442d00413070b00e1400f544603a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 66540659 1250 66539409 66539449
    0xb06030411060d0204032d051005130206070302060a0b060a0c030c020d08070c090f050709060c030c0c060216080106080a02100e040c11010b04090b0c1605061807060302040b0a080402 80
    0x400f02c100300c1c804661f842120006411508641c1c1c1900e01703468000001440142685d00c0a074120049490720307080254488010401d00001c0c1d9aa500810403c1c2d1000c1801c43c010f0700103000704420a000c8d446003480d4004103540c3c03a8148001118050003501940c0c03805410701c84110b80140865a446047c0c40095501401d0a038640550385046803aa1400303001e100b42042c10490600c00842032407003101d10514084d0365101500d89452019902c1402814064040080040201c00071400070401c4038020701442d4014030001214213103203041000300340c0203401964108038080004840005405030090b404981c5105e9600041d203095036011401c0509507003141c14198110710003038000220103a8802290000d201c1d400c0f007402003100329964042d0051070705011a0101d20840812000707010303120b200c4911040440a0750300d0312442c01600b00d88204401e008114485c0100d50240300f10340040c09103003000d43c00c0c6400d0108106050040b003100b40108015070002070295500c000c4403014030084000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 66541909 1250 66540659 66540667
    0x70816030306030218042310090503040f0b0c0709050603030c07032d0b010b0c0a020303030108071e060512130818040e030901080103020f030703020306070507060f0b06030411060d02 80
    0x14014028040e6403105038070070345c1400d8a202c180960000d03072911a650013090401950142d000400c221000c103c58440e1902c035503c0204c0002030306120307291650340103e00842d111071030b205019014109940002c910300c1e0080c812816400800030301d02050f984408008925562140c0c0407a182d1300410035061910311415400000f4003050050030320055100301372a04c040d40048545100400141c1801014802050010403102403100050000080c115040e101498225000030385590000c0e008a0501e400c118410041900c06002c3c408503490b030240081c605900d0140c0107884d60103040c002c040c3c80c410000000d041d4203ca0594108181ea104030466120310b072205085101d000340c000418015490005d1a100540000059603140d810594583c081c9a082d039092180007410700f0b0205800d881580d5000c00181e6080c030420344560383c259100f940340c201c5801c050b03064070001008481420b2030640d4003034541d2500f100f121360050308420380c059a1f6070914007140c00c80c440e00c00c0150b140c1c1c0c8045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 66543159 1250 66541909 66541913
    0x9020a030303020a0806012607031e060e0f0601020d0804020a050a0312030501050319060902120111070b060d020108070c1410150e1e18030409020304140105010806060402070816 78
    0x2a000d440052956070300d00f945d0b41e80c2c002c01912005603101c0c3c07807500400c070b000e00325203664020020b95900049603d40401c0709040740099840101081411504641d02d40405012000d0001225640409804200d16090904600103511002c544000d402080340d03000c005400d6441d80390312000180303c042c041040c16070f40c074180b8501820302c028a041c0040e0510000146c603140000f0040f0342c59400d1400340c80c04e42242c2e50340c0002403003000d8040342c01a20044a10300d00203000c1c490000101100f0f1405941c3c2c28181ca0a24580700c1d000b41428031407c4091a1040541d84c403580e07440c3d00c48582d0415400c5404182880e4030300b9440000081494840c41d0003c030380b080d40340d030440e00c144420740340b00380c4a490b10344a10580c4800b04a03014880c04c2c042e140507a0b41c9200c0e2100d200e4200301450840c441301e2859902250456020b43c03c280c00607600001408100000550300d0220003003500c0080195504100c070b926100c19010345020302c03031500410008144001c94040703e040c0380401340340c41702c0c080c1e480c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 66544409 1250 66543159 66543161
    0xa0e0403020c1f111f02091507060c0f0504360504050d02070b040308031513050a050f060301020306150a050409060e0709060815010f0905061813020403020612070309020a030303 78
    0x1c1c1550f64005039001200c044a10700005180580303210504802c3c088400c2c5d1101e44c4025002089002d510000d44190302424059010080c007080d40a5600800c0001c48400c02034407a07984c2039240340410208110811440c40d101c1a4200840c18152420100400d00c041da51804850f00c8441d400e00c3c0d1030601400108400004e6014840610b50250380f1410342d03881c4400c184d03001d1071001500d490400c10020350404100c0b5070b96450000e00626407050034003020180400c446040301c542c81902c0c0e54400780b0058818100f50790764402c100302c00951943c038044000c50301390a4010040c1e00c06560102d14103041030f0050050f14081c04003084104051503403000d08280d050415100940070454078000071801d01d20408081d88120b043c440748181c85100400112107044102e0785400801c04a50070100d50383c0d5840000b0580e007aa0488121403c0c81104100301740c0c490300025904600c5e104200410050704c1d44001d8800a0180d04122006551400000c2e4040e00107100c0081d400034112102004144d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 66545659 1250 66544409 66544459
    0xf050406050604020c070e090f06040b0702060a020406020307030806041107060207170703091e0902030705030601020f0d09091806020a021506010921150606020f1504020a0e0403020c 80
    0x280d8014816500c851081c00204e20078019081d099410070b075000d1014130401c3c55041e420440c1a403c40e0444a04001013904010040c0d03011200c00004100b48a49181e0412655800040c8500210b140034a4408060f540f881540c2004052080740c60000e10980e03035543c81800449112540c0c1c40e5200010329000d0029071003440101c80310522040a1644040c81d00e054500d103584c543c46008145060607400540c21000c1052854582030b0880041040c000c103001440c000c04e10b42c0c451035100d0801030006414480905003070107155002c0c085680d05140d0207141c80007164464180060300180e401c0d801403c4640501000d003030240001019506140c4c001502d048802071075030107a0503911070f540110b800185d1f5100c0c58143d03005190030b040c05285c03006003981c0c0741071040c00070340f841c4155005c401050f01c40c01c2c0e1195000d60010342060842400078400c040d81210007000e000602d00d450f6000a8021515024012460042034005404c040c02008860340c01500102031500f0101d1001840c203c55030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 66546765 1106 66545659 66545663
    0x2701050603040f02030d0905010e030f1e0a0b01030506010608090c0108010510020120030108010608010b0312090a08031305040b012c0f0a030525140d060b040f0504 72
    0x582080086c00c515040c0c0c8030004c00916240014041c10784600c5800e000c0d800c5143e50200c407603808640e00407141240051440d40c10022a6014075106440707400402e80200c5000100c28841d0000f416412541c0e581d40d044c0c141e5550b91401a00c0e2055200b03c5804103503420014045c91a1000d0529145091440002001001c1d2301100344d1800e40e62201c2030480000100501c5461028000d081c0a46683c0c4000d03c24400d1342c03000310399100c4001d51038144141000c03030040c081340d0761070303c0d000e00811504081301e45841c025a80d20392104000d11440d4415840c04401030581d500070320b103014090010354000c0c002d0004076031240e4200303208046500e41c401c1c00030b00c0102c0d15a44100c0300340f0141d4058402031001c2c0390000d0325811454590400f41c0c260300c01d1030604200110580c201d00c200060140c0c3c101e1050040b520b4010041c10644a4082d8010700f00103c0c010304021941c440da02c100c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 66366909 66546765 := by
  have h0 := BRFrame.cov_init 66366909
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66366909 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 66366909 ≤ n) (h2 : n < 66546765) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
