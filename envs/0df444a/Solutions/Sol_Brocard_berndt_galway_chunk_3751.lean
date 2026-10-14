-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3751
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:34:11.385463+00:00
-- url     : https://prove2.me/submissions/460c9d2e-f8dd-45b8-a0b0-d1f970cc9711

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 674460431 ≤ n < 674640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 674461681 1250 674460431 674460439
    0x102040806090d110d08040827010207050a0e04061808030a0515090105060a03090323070b0901050c07110a03081c0507050429070602071203050609190e0c 68
    0x40395a400819581d500a40d03021006000e007010000300180070300080380026119101408102c810301d60b00b59103095000703209a6040303071f0803c140070402d10603c000c070096041c000e51800e0080c0342100024904425508064010407213034400303100d18180c45888542c0594860401b2404407001d609000010b40c400030014101c040110038800c100140343c115610801c0809144280b0210907820401c0d04a000c2c8a000d800040412001c5951803013904010241c50180c03e101c002d20310361550400184626280c407404486000c2054020020030441450f04840c1120007402241402e44041c4c0b21407081c0c00c00200700d0407856199035240d80750014240700441c0c10888245e140c2e41600c2500590f018052260345100b440c0c5400285a140280c00740c400380e038810030701803100211600e250028071114440d150112202031110300001000c5000600b506c03842540f04403080c000c1e00901030b00b40c07074001e0500d901c26032084d0204525810f00e0b8000116050380080041180d0700400d030113604040c280c221072500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 674462931 1250 674461681 674461687
    0x1e21020904030206190207020603010302060d1b0507030305100f06121b03022107050a051e030408130b04120206030604180606080f0a050a0201082206050a0e15010312030e0102 77
    0x80c95008110948507207005418001701d9141d0000803002c0f44510070009602c1841400140094102080035000705001100001440c0c0b086c3c0207000d100c40c212504c60b00000300005440700415030305005540c0c10805503800c1c544214101011080050401d0064000700000600b642e03c80c03100c1a00451180070b1034160300100302c0c0f40000028042d52000c1c01d80301c01c0c0303107549086400c4103510f84000d506c28000390765100c1c1080d41d03c4004440c664004042921140c041040c09260aa200002503009d248609025270b510494480c264003030b0a560f60040d2010542800100310340c3c0452160408800d60440304181e130f9685110019000f0300c2d941d441c520b1071004410101c410000c1c29805030050310100001ca43c4422030031004e49075148103602c4020400e400450740c40c0015400360800980092400c254003410520310a00b0f80348803003280303009542c030710340310320900440464070304c0780c4c6a0945010002d4240a0020380295501c0311043c403008100d06031446000a005104e5409500300e4400303e0000d40d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 674464181 1250 674462931 674462933
    0x912031b0f040f0b28080c030c0403080d0b030706021212181014091204051201180812060913030806030c0a090501080c0d020a0306021612030e071e21020904 69
    0x21302c0e0400f11200c6031603160403480f0000b0b405502200b02c010b440c01d40d600c041a55030140080b1940e04080d081960105c424440400002c2e0380801800c52090708a4001407240d400742c0c10149401010f91095096400145071714007462401811120000c02000c011241601c8606460140840703001041e00c403402100e883c9004030031541c1000c8a8801000004013640e101c910741c0350f450341500f0002c1120004100010000740c182008442c2661848800001d070410206400340300003800e09500715101800006d4203280130f04c02102e10340c1c215100f9a50305805141c80c088501c1c80c040d182d000038003804907071000246a507400304200112628082e04114980e9640d010140c0500428011100c0c940507001c14211103080560008014540051030446410301c0c41d100d440003503008101884040040340101c1001ca082500880c2404006940c0000d030030340d0402c540350502240b5000084602411014a000c4030840c2ca142c0302521509040c18464090302201045107006849009402c915030300304004c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 674465431 1250 674464181 674464199
    0x1d0a0806070201060e09190204060801021b01061a0a08180d0c0606080109020d1e0204061401080a0b0a050f030c0406320901030b070c1403030912031b0f040f 69
    0x15000c0d4105400904c82c00751141c0580f1310494003240c0d600a15031203400c1d04141868a4200c0303842560015000040054580380c81a01760390000c103003050160304000c07541c0098002485100c00905525161000e442c0411442420603c554012841000300c5180421002010501c208190144544c200e58034038950400c09040090301550907203603180b80c040001003407401805030440c103d80c010000070000c003803036960020010507858a0540ca0b04c015030120016284d03480341c280a01140071800c100404124001485407000806e400010341c24550301000c241c07103005851040c1d4908582e4418810044000b00e03280c10841e4880c1c40d84541013900000c0e6150700440170604840c0c02420700d10380f02c029200000f10603409118a607800074a084010000706090340c0020342c0240d094500812030140f02d1322424450346a4104515058100209022440d441001107101141c41040b6050951405583c4202d2601800a81d22082030001804040c075001600849000d04a0002d00100180c0c0f5a0285 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 674466681 1250 674465431 674465443
    0x1306020c040e06010b09060304081b0304090b010e090612030f03040b070915020307261810111c0c02031005150111030d09170703020312010f0302101d0a08 68
    0x618056442c20540040da0030b03003ca280380c180c82425140b2440c0c045400d0a000941d40b00074010307141c80d83d003030003601c00e900312030060211941070607001180c44908002106080701c1d84014542e0500100343c4242c40c25845460034264468811203c805400d901400010b0540c45481c090042444002040008000a00b90b030f0600880b02666020241703919030350803003510054840441c002d640180501400030351070f00400800003443d8010310411040c40301604140760440010b152030382000c2d500c00325040c20003c2407200031010714507041101c428080050303a02e42d00b07002e2022400c220402900074a00380106280c0360515800b030219035840742d540a4050090500fa580d0b904501e070f00800f1001558400c98003e41c1450300b44020310b01d840c90f6103d204000b041c41240464000100301c0022804450b407101034492140203401956554101070700218040e10141c0091607090031128080c400f5032258621540d8455650401c41d807841094000e0401c50a0000350140c4d009419080102c0c45000100340c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 674467931 1250 674466681 674466703
    0xf190203153f060a0209060706050a2a021015060c0609021c06050105030d080114010c02030102030c1b0102071106031b030a1406010206091f09061a01110312040204020d02130602 78
    0x196103003070703c4e0303c3c80703070001da105100c100f41e4400818080c0002142c1258001908a130151500013240395488151b080c001a40503981204661026a1b24601c103405000c0c010320205851000c10400400f404840c0f0304490134002c09081122581294081003041c0d40402c243c190014440c0c1c13401c0110041144010078003a408a42c0030b0300b000000562400d001482c3d03011103074651101085603090100000400d42401d210f02d040008211203500582c600b0710086009a1b00140d115980d014003c520412040d0240c80050340390788100020170101b110440440c030744410403030b038540d925101c040111140600c100e1146004800c00020b0110300840c0c0c4d482000880c0b0f4090000281d03503120001a0780300c40302101e08103426000141c441c080c1031440c400e0b01009110003040040d8503c00c42d01c417001260300c0240300c1001e0006070302a08101e0b6800c03400b0045102c8a400c01076140500c0050742c842c0700c400151000f800741d600450f002941c0c940613016070302303502c0c00c864942c1c2e40e0580da007000950b074085840f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 674469181 1250 674467931 674467933
    0x11031503120f07020d050114090d090f0e0f07050717030a060e0402091909060912080610140a0509030f01050105010e0414060f03070e0f190203153f 65
    0x30129001080e510181c0751070702c0d11226850305107203098091012030048001c003180c1d103558500704c1e10500502440c0d10340c0141d07442c00c000c1c0003030301c003040002d415800d082c0c2103a10143c400b0034042100d04008c01c42594442c2005600d880203485200701030700e81d8002e81a0050500d0303500c03400c0000c4c03030244402451089191140602400d551900082e621786420f6030040d403c02e40701400174018a002d1100c01c0040001c0c03240015000c0303910348030b51046070030320358003207410314440650700c00b107203600400203500204125648144034030314000103801d540303c020001401010102d00984114025801c2e95a6200301800751048000c03004401402000c0034020280440c0f039400b02c4581504142c491000c3d03200d100d62462a954885c402007020700440d60810f00d40c50b10484202003031220404000a00449001c4d00070310f86800c1c918070b10441020300c2810f603542c0910502c1001007103015000e0300c1e891203c040d030f80520b5461051081603010030302e18840b94000c0d0040b0728540c0942d941d01210105601c030b040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 674470431 1250 674469181 674469193
    0x110304121a070e04090302070b070809030607030e060114010e1002030c1605030a08030a0b06160302190b06130f0536030405060c03040801050c0c010c09060219030311031503 76
    0xd24000540e00c00b60749100c0014881c03003514800e030600f94080d0000718000d00445a52603039072280c00b942d590003658102c44510020030144480d040400c4010380020032420b0501ca2500ca58151950b41c074014070070074520300e1855003208141e0340941c02d48a000c91006d0300101c519141100069031342d901c02507a00b05030b40318010300f42c0c0c85080040c3d0680260781c401000b9207181c0e0303407907125031480350401340c240c90b0079503034940d00e1420f181e58050050030301560304001c01d40034502ca07003006030800c0700d92140c4040c12441200320b600080d00303100740d959100008594900101e02100c03409402000006481000d0502e00401e00905541d5014019a00c6120305460080003480048408d04018059110b0302c9a5200784404e209031316084001e0020010810203c03030800b940c80c0d590b282035580a0b42d95440c20300c80000c41c05d188110a000d0404100c030282060150b072450040000d42c0c454054404250080855040000b014800e401c0307050101003002200f911790915820300030140081c0a4070504c00d120396 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 674471681 1250 674470431 674470463
    0x40b0d0504140a150b01031d0610060c0809060315040e1c02070e0a0b0d050619060e06030a03080705070501093c0f1110090807050a031502090111030412 67
    0x2440311000c50740b011311440600301c007200200c05405a15141818503854210b04108105810240112038035898001c3c1901c0c02c20252001950855400a03002c011504240401003135004040340d0f081ca400399004e5a0766034540b1031080311101c9100007107920500b0b0000b41e8403208070000700c100095040c4e0308038620802441d203050ba40c0304c14500c103545010b06003400080c0c403001143d101e4264800c1c0540003039441c1c0703e1a61000d042000481e071010020220b4618011b0400300e52182001a0180380b0032301c103280c1444400680c0d22144c0042c024200403016000800d064071401c19100110b502100a0042004078034107040d00940e81640200081c0c01e4006e15070300790405070042c07000b8241c41060042110070b5501c0b1f101d400c50411200b6694003030101c003041056100d05640151844184d0f50b1120028108610581031001c26400180703d84e410740c0c001d01c0031a506075400741080d21013440c01030f526420500140d0315800d4450140322203001c0442d0008101030311100f00001140b20321140c0c8004982 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 674472931 1250 674471681 674471683
    0xe0109020a081b040b0705060702060a0207051b040608100f0f0b010c080702190e070e030c0a0501120617060f070206070503070818030c0114130224040b0d050414 71
    0x3811241d01c0008080324003040400010100302540c3d0300d014001070345415140d11200c4a41d520a40c000c0740d80368070102c10071004550610086800c40c225000551929140b81c41c1d031076aa03003c0c010000c500180031503868101c1c0d600c0354030a400400784901030320404035444950310020074012103410895030600a1503064130901c0e1144600c3c104050b110750703210070950345540509401c0414203e801c140d80705c1045c501941d040c1c0f074003c000c0c418030100d850585410300000304031600c8082c206000f03500901c0d20a00c039941d6040d884054860a1800078249407602d401d15019144660191110000d41c6c0c0b00070800070400700b405441046991502e8296403150300040381d4415040701c0c100000380d81400032841587c07080c6081600065100c52101d0040002051030b4150740c0020b4a01c450341c0c0d03650485444c000400d0030703095800301c41070169034032006040d00800d040c850001044805811581e0020115011310001c0e280a002d00710384035501d500600440030000e21046d2401d5400105650f0041d03c0484 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 674474181 1250 674472931 674472937
    0xb150408121c050109060305210d0f0f0c0201051806090303040b07020c0a060f0f02150a02090307030605100306060b16080a020f161d0403022e02030f010e010902 71
    0x2240e10041159a50340034000c54640c20001001e8180c0c01c4601008078425518000d0324081c041583c400101c2c5c901d54071f8100e00d003140c0502010080d15030344415019000d00202500c2c400300017907001080ca6884100210300420343c040969149914003c4441c91007541580020310030344000000300f005248640707030140e543c5406c461410403941b00f000010300250b4404e80d800d8001b0440d004030b0756501c0099001985c003400d542c00c031100003000324070f00b81130080d072052110080180500180c0340200d1440074080d001000105200c050640008800c0c4041d01c0401c507000007503401801c2040241440746041c141050240320503036400382800400324155004030202c2c0d9202c1d40c04214054030502c10380c0d54440980100c6280400e41c02498484914803100707001d071041018010b44a001070604103158000c40c0c4050020240b000a006001c000000360009825000c0c01c080500c50070f40344402d100e84c0303a00c89031840d0f02d202c03044e070012050100203c110070106068a005510070f0f1001da0301d8942500c1240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 674475431 1250 674474181 674474189
    0x1a0a090b18071a09091f05130b030d02010c080c0703020a140a17040305120c0a0204050a1b021516020601120615061e18090b0a08011104031109060d14070f090b1504 72
    0x1403a8800400c4540b5000808440410352232030301161940040d0002400c0c80202c682d02c40250f51203d0a242601c0d604c1002168080a410440c508241c100c1c0c030029078802800100402280d501c180c00b16071010100301181ca16580801640110307000c840102d0300540162004a441d40700b144d08404103074010200b42d6000c11451001006105000d8007000081c0601801c880c1445a46582d507000c221b00e00c00051034200040d070010200891742e2030b002c009255004051484807009060b0250000c1e9000c107445046941081088201c1c0c1607030b081c808001c180e11100c1000310354a251001455a0300306090080702041011010058800150300b1350300d1480c08099800d0015400209100c2640c040e444a4a0385101400d002c1943c0c0d102c104507030850341035100801c0d0010020504104010500c9080c00c0c2280003511001e026081c88404243d0729030584000400e0950080b000141c5a20100301000051001201c1c0308000c55582d007201008000324400903003c1c3d5500785046250b0070891086078121 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 674476681 1250 674475431 674475481
    0x1821020c03011407260a02130b07020139112403060d050f0706050c0601170316060e0d20030705030405042003041a0a090b18071a0909 59
    0x19595200c0c221000c105881005c11414002c506080054008030f1751180b05506104005965a40c640b03507620117510180c1c44048a01410049100182d91082045040c04d8214083c50b0500c1c0c1d50341c0f01d82c00c50281442064003268419840f62041c012407001810301c1d65000d80d0201000c00c058255031518000420543c070400800300080341c05400d040c0c00a5403424081d405407004884603800c501d00308010390344480001900071914818004050140f580100610ba550b81020b1044075441c544a004e03448584440c00d440441000500c9200d40050305140f50180c1030f03c6018420b180040c0800700710341c148544135a05034a0302240c0d180000100d82c80c1c550080c00940c1010314000800010b04145007100302c041c0c0811303048e51b04510318500954052481030f80e142a541040c3e200010002c030005050340b4800d0700b0082c004001c1440c4122217900300f09164040b2450842040107545480c11983c48a60300075000303251056255030807406005d0f602402c407a0a010354440f11984040001650035161203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 674477931 1250 674476681 674476721
    0x1f110702030c060a021005010e150603010f05010305040f0602030f0703051e0426070f0302010c08071710050316151110021e0414150f07061821020c0301 67
    0x102c0d1900360b010f041400c202d07204640000f541e00c4400030039580f003a440402c95034510010300492200c17400c0580740030726003600d8003411503150980b034101002d618450141030582e168089000c0c440740d4110407280c5038116206541d02e003003100c0907a00c5c00c0c0088490100007441c0c08081010300105034011800e0007040c0d5040d024079100da0f1100001c01402403506510340c02402070a59a142d01d507000740100501400b0511a001c002e41006829603507558500c000308a201c2c400c08c920280c0000b004088035406101e85100b6540d10b071000d00b46011503403c0958584641c5820504607050785c0f5801094903861000740302544a51101515201c04980d150320360342d040300071840101d03072180d40a000a00c540840c407111411809021540d503a0280d00182c1d00308035954051691400d1016010140101001d0001e1900810b1100900180158000108000d8460203134115000e1101131540040c0d4018031b801c0b0b201c1e91524030780c15011420001c410054090f030782c0e001e50b907485c061040d8038082880c01c4100d0a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 674479181 1250 674477931 674477953
    0x4020a0203090609060403170d060b1204030e0409020a180b060708070f0c050d0f050105071d0103020a0c1e0b010611031b03130603061a07050c011b051f11070203 71
    0x840e810070184e90790480303800d00000010a02c50b0300d20b05111990603100030364172029110030206940c4543c01ca01e051442c208040f07620b0a401007015030344150907240c610280a02400060040d0807042c10207035000e40101070106086082884007981c404c42508100201c2d6150740500c00326000f1240050300511090000101107a940510344003a64800c178094401c03a6224000980c031101002c00986000021440078010031000740701b031540000d460300b00025610707410380d00b101600014404107410560085407143c101c0e030003404c20b17150040d40143c490650b0764695241c41b000c82008602136a807550114000a0194003a0521a11000c40d800241d49080c02007900c0c1c00326503000015448680c44101300c8001c81c40b00d0b440c1800c025100b90b9402051952524060101249140502d280029410807015000940000d10303c041c8180c00e00744540740c1c0003c28401c801540d143c2c07002070b0160164024000076120700580312a860f0703010002c05c000700ca00001440c10b4501032090029019404052418 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 674480431 1250 674479181 674479189
    0x3010608060d330528020405151306140d1107050609011b020c0d120201150305014106060d0f0b0f01020102030708010b0703020312010b1804020a020309 67
    0x990004002c1c0110070416819698203030342c12510b9450b0b001025060b68000c1c51841c540b41a80b500380d038896800d0005041c600e00603082210750081c403c0107208050490000f250351a0169401000028140521425000303000d6140e503000c080304680ca042c0f203032004075070720f030255000300351040840c0000740c2010a003060000040c4134040b20181014424007400340020001c100c8580700c0c04c01d0100104040a8881c80040b011840d00705410070343d01302c030032908101c3c0c40307440e829005907801480604140e1940c01c0180d006100c0210301c0c0c450540c3c070b0a40031041c810150092105003501c1c4195020318007100d416686138400c641c2d035001d964040550600300e50301c90819003607080341c03000304040d2800c0040c45041007180e0600107000011601c2c2d6031041464509082500c501500030b0000f545580341c1010010095541401100c3c141e080100d090420316208209a407000c0c0c403418100d082c1942c481a17011031a07000030004080450b82000d5210342c0d800d20b07000740d81c0408603c2c0c00071801d1040100c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 674481681 1250 674480431 674480447
    0xd080402130203090604031202070602040b0705010c110a0b1509010303050c1c121e05090a0b130c05101404030b01080f0d0519050c150f0702030403020d03110a15050105040f0908030106 81
    0x8e05207030780c0901909004ca5200d10092004140c40c034280360b42c41080d1326100e42910740c000700c443c0a212070040b141d500f818000c54541c5070190300400c2004142d8810040d004900c60f08004560001d00c1039001004054001e0014880d10b105042220030f104404140f40071492580380003100041c8412400710042285600306104509841d0f00c1c0600132240d00648104a50f4100c0b1009003584c4032066113414805a200d000f07030460001c80514055075603503110004822401d10440d40100e0608000f0041c440c42a034035664211036441c01c09640e0ba540e070402300340c418028000d00c001c501803103001e515185000151000300b0345903034550301e0515038096003080c201c1402c083c9a80502c01c041001001c10314003400300a0101c01c1e500320701d45642c207000c00c9428107010028918001c3d903104201c10300c0942d03514000421410b5041c9006103000c2008038500e42456034900e4002e2103101d165002d034960403001d400540c160385068508100e030f09041464101521018540075106490800041c402c051180c191 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 674482931 1250 674481681 674481707
    0xa08040618120e030a020d0b0403090b03090a030f0e0a180209030f16170c0409060209040906051902071112070e010807090615021f0b030d08040213020309060403 71
    0x8880328091400509803070300900c2114180202d0305110041a082100d15a4014080c0c1c004c5c18140030381e0740811540004d0302e8002d8031114010f000101003511603211000a040030002194807410009003403a1f0710030340c0140480100b82080b9601504501c0340144540500c00104256200c924080c000b2168105c200d040c90b589540800c82000795807410400c101c20b40b1307030400c0281140800d140c035100000b001a044102503090303e0003071103441c80002956941c00030044a002400c00c42c03d2512000038821305030302d640c100c5c2c1403000030028003170107900440c4107811066012030342160002c5400704a00c06c507080140307030704a04583e045040c1852585000d40400306001c07101d180762551000ca0291409034480402540714072010711101c101405201d0052910a5141810000e0000040c0d12880c0d1030005c200502c2c0d00132489140c00f00a60010000f40c1e4000d0180e4910604075000103081400840d030136030095143c102440f0001c601803003200d10504d503070000303042c0c03d40702c40c1d0701217510b070300301000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 674484181 1250 674482931 674482943
    0x20c011215080a060b2e1205040b040209090d1704051204031410090c060e0a090e1e060f0c0307120614190e0615040807090902030f01050105060a0804 66
    0x700000c000500100c0410240c1400c000900d00c1c146145000b1040e10051a02c10f4000c03041c0c030601d09503c2000808080c0100202150080b44040800048a10400c8100d04080c9030342008144424401c2c401e01c0f0034040c0d402a14000440e5840741001a80c1d800e540030490002030030841c918800305400011039070094031800c01e60307040c4103401700ca80d2180c1d0029002038030345144844030554024010001d00382030058906052103a042c00d0b4460b044146000c2c802c02c0140108940e11070490396804045401078240c0030400c002084012078a60307601c41c19404c420704001841504280414070004031640720740c108090b00c201030768031049050302d1604050580001d0006048074010169294040c110180082030540d80c00003140300100149519220415680b05c0c0a0a01c1801800c04504000d640701d18181c50015101010b40c110030458443c980c0310002c6805880c00124060303803035410661031680200d007203078a004500d181080c02c0f5102032194903480a1304008121405000b880a1540540035035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 674485431 1250 674484181 674484191
    0xb0a0e0904031e18270c0f0201290d080c01020a0c110105030411060309030c01020d020901080f100312030239012f09100e0906040507020c0112 63
    0x6010840d85502a54210082048401542002da8402d0040360102d503c5141904403000c03601d40c138103820245401251171200101041c101040482281c0340c440360f00380c2c001048078110240c4000d1404112a800100550070b22001021144200005002844116a480c00c02c45038402c20001104110079040345d405205010300809076000f807020300000178158540c190a0001e034038045c030641820045450500109205101c0464010480c0320070030401550200d903130382c0b60108803038594052111546955800041d0f0f49404101a4016000d03604007030700d0b4000291034080488040990460b41000a42003c078001c10108500c0d4810100c22a110f0800504e1b00c076041c00e0181c0e244807903004010340d24901a08245580310508074410040b081030b0002c12112000d5240607041d2903403244420141c10b6002a020302613649802281c2c405100180403d0f60302c00d0410000e040600c1000d6124440e805139400140e080c2880e000e0b5902c11030050b8082c0c0007132141d400054581d031110303500d00c11580d0750f60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 674486681 1250 674485431 674485457
    0x3130807060207020f060705061803040504020c0c09060a05031513020a090203070f020303010f170123250504061d130b0f0301090f0b18030406090e06090106090b0a 72
    0x8802003591601031040580c1e180c80500500030368255030b400700c80c0030f01010400301001c948041035068000200f0142000000520011185540219007007182c0c000e100042e00f2082400018942c1110038094404607e556101020000d0040880c465940c241d000025814070300c0c501c56100ca60f005105800d9090403807140d4010071100c000e0b68008183d03ea0340041400070b940d0704505d815a04212070b1001b10310315030400400410070100ca20840d444003c05103000c022408081d01f000c0401c040305440c0c0b00c1c8028242c1100d418004080e00c290440700d1a00700e01d0054484840140c1207450a1a2581ea00c0c291034104201c41c00760340d00312540004025805170140503a500002001d102c00a550040344203599401044102410140c049200c2d0385400010400282c1c0c001400942039001138036220103646450002c810300c0340e14010b41026000008000c40c11503008001e200039651200c01ca82c003079968210500c00290303000e000e250041402100d0800a5109020060520b0303032091800c0c40c141d41c14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 674487931 1250 674486681 674486693
    0x20319110d05070501050f04080d09230a1b0608010506030c1201032d0210030b010c510b06090415050316030305180d050319030c0c05070b0313 63
    0x1a40710307840c00200c0c001422003e01009024240d084001600c1405482c1816981c83c4458490103600b10303101d5403144001428400c02941c8000000302c0c0f400d4101e6807400000b4040d880c0d08030322200700c07000705051210950b11090203039588240c0e901c985920b10146d09240410604d900000d01040660800300b0003c0d042085501160b030007075100e00500c0903220706603504940e54688a40160301e890300d806501c00c002d0303500c01030219a01200d5050001d841448840100d0300d42e020042e0140c00301418001001c0c03010986886000507022012400010390b503282020340c02d09954529150250711020600720710714000364844401c5200003400e82d031030001154081020b03980ea130641c0c1c9007220808481048103060034400344840e1529801c0c09182242180d8000e802400760024a80e10314940b580350300281d44618507254402c503000811240c6401c03920385203040d00881102044006420244142c5003580140070050b203965020014051032410230a01155507000100f040d15aa5590b0b5010404296 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 674489181 1250 674487931 674487943
    0x151003080c010b0a0b0a0801030f021206040f0201080705030403080613150e090d050421060209090420090601320712030506030607210f020d06060201061502031911 72
    0x90000718440c50350b5010040303010900d60045118172410410103141c03c1d4054440c6064a52102009142480b43e002180303441c0310720800091a40305040902040c07000c0c44d4030111415100b40d840701200c0d030754500c0444d5140001e4130002c2c0810303410808222140380070049103600c2200340030b001410300c030304140c0e8000103032403a40803a00c40d03040c02c4140454036000303029841c0354001a003040c0380382902d0000800c81e401c2c520380d581010703141c0d03403025541000459012680c0700c40c4014942042828242000b1010940c04003002c100810781c0d20116005040046503144140300584940946401600c21070b0b11440101d04c1483d0007451902d44501c0011400000d00b0050740038852942070354035201405000c0721800790441d4032176802a82084415170340190146a12008220a8403d1a43d4030310700c50040c2960021003a000c0e400420000c8260020340c0c003681c12158940d000f404055a00c001c0080703213a180035041801070f0010044040d42c1c0d921006007545003403262420340903001c8d00c0400076052503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 674490431 1250 674489181 674489197
    0xb04020d0b0306061005250c0303080a2f0c07080a03090f0807080d0311070b043509060a0c08040e01060801080c03071401120906060510080915100308 66
    0x303541c4070009402400d00300b0616611180c1503c8100c140d081c010f070003a02500610552046000a04021503c1011010030440040d0350280741c440540c1c5c0c482ca070181503907030221100300c0c22034500700e8000292030f89180c29500c50150000e4107040346a03411030b0302113964888862004948a01c03900000c858508101d007400150199582520450810038440c0608000b640910592f901026081c0f0440001081002407020541000201c0e1855400f0b01c000a010700750020340580000b104010601a5020b02d28804600781c4000411441202e02d0307500c40940203c2d43c40714050002d00c0140f60609100c0010200140d640c10b21407900e000540e0f481d18180e0294004000f140044001003000a41002c0c3c0503024000c400003408a64000c840442d40d216420b120b0644001e0b0060039440050740035500714803801c9070031141417006074000e003025000740c1080d1040c0387c044c070100d9001c40c1507144240566402071800302e01a004803c442400000e5240018180c503100e0304040a00100103114800184812 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 674491681 1250 674490431 674490457
    0xa05010f09260d0203040609060c020a1d1b1204080306180a0923060601030f150306020403050d0f0c06090501021b0a1a01051003051812040f060c080403080309010b0402 74
    0x8100008081802c24494071000c0781958014082032001903003121143e82070317030554580810042b00900001e210012240d000984c0c503050080540402414440400e10450320044400e1160744c0c1046116028860124003002d10340000300410000f6002e00f0046070486401000d1501c3d00309446c25009040105a40a4000030ba546480b4400c200c42400c052501104907426000c103c0c00c071488039501c81c07070020121030400d980e0f40100c43ca02c001d2035020300c501080d4049134082c013a49034a00740d4020340c0300d404161680c0c4158107003124890711130049403403445107581c0c400215203010382c0c515000d0001104201d0319550207001d0101c00901c84010a11000300c0600205410b42d9142801407903081200146165100300000510032074541d02c5000009440303910b00003882e0380e500d00002c05400780b0051002035501921050190050b00c15000e00155816115a004926501c0000780c80804501030001c1401400344002c001150034003020f0340e130210301c06002017044580000020100e80c0b00942e401c1d10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 674492931 1250 674491681 674491739
    0x12020109170f0d420b040b030105090a09120207170d020d050f0c0d0806040c02060705161109010f061706030a020625060c0306050f090103170f03010b091e0a05010f09 73
    0x500b480341c04c07415005003501c1450924041c00c3c405201c07000e11050003440d00500100340401c400c000980d1141c070905401c00480001c4064111000752038004500c1440c140d000710410780710400b46c020503d0946441c01c0e800400d010801920140c600f5008184291312a207806d02c154680180709008821114505649004062034500b04000469495881040455110808010600350081c085403242c2d600a165001c0d03144041c5014903d25100c03c000c41c4d0484c1048000080c80c41808a902081d41c7c1c1fa5224140c000503610440c1800500803906694103a024443c00e80c090f0425000800c0c2c80f240e56035072507204a02600103006400040001100c01941d0760301490802c0da418403900002d8a402c950120024203443c0c0010343c000410300000e4640e0310190800d804c91034104003101c035507100301a016500c0f980d41c0d1401100c00d0708140001c038043e24402e80707120050100e40c00c05003452500186400c208504100044640c000701c1980c8006010040c1c0000c40d000f0000c145005a0028000d44621 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 674494181 1250 674492931 674493041
    0x15150d170f09042427020705030d0e06070c020910090203180c03010606170a0b0306070f0201050c160b091011040f291612020109170f0d 60
    0x1003141c3d40031004c200002c009000550700600500352038012078200104002d001c1c2043c2d15422404001031070000390b5988001881c4080040110140c600341019020411000154034405038444900b00c50500010740c0d4040c15800601e82120781d1908101d810710949070356500e60404004a074800d46020a1602600145001c100ca0400a81c0104903058000f80718541c035112000c0e117180a4100110304c610000c400140c00e1141a0b80032a84040005084070003509008a002d4407242a0242c00720065080400240d82001d10700101c500810800e8510030300b10729140c035468007113000900800c4103401520b00c0c0d1500072920303004420403a00181e4161303954902e44104d1225204e11075200c2c1c240e148c1c4c0d61072440303d48004009072402494100c0074241e520441b500c003180f0702d11300c805001003e41e1103100a041e41c180d03055010300b1140b80315583d001411304602902e441c00d4080d03c9403940c5078a90410a0b10904400c0d03400180354110002c5d02c107103584080d0810310a12005a1610106c019074208000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 674495431 1250 674494181 674494189
    0x405130605012103030209040e03071b0503031602010c0c18061809080405090c071e021c0c0501030e031b010b011b0c05040908090312090315150d170f09 67
    0x107005082c5070369a03102000b075451240f0001441d5410241c145030303000c5142191038442e9003201e556101c0410960f590381c02240f901c0040001303e4050301400305140e03c804201403d00004032403010b80f4000c20300d00c054007198011148040789c03280c00c5610201c0024001010182000c2100c201000c20700041103450409200d210a00001c24024560f1410414001c0105a0f41422101904d1041c2c4501c4c40c555030741039102095200d43e4038010103a072100d2407819200c20304d0380b00b00c549280c400c480300407101c80d90450f41c024011210002506200e4050801c00940d8080d500810b16004200c0139207003080317018641e02c8201c22003d12151856511445145465a400102144440c0c001c0c074010311808000d8031040005100c50045501880e50381f100340e000c1c404c0300b00c20b40390302000082c1246c9a0401b000c604041980001100c14024440c0500703481d80303c5401282284100007220150541c83c104508000304900d14000c15201d00150071000a020840600148414001c94019941d1514108244 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 674496681 1250 674495431 674495441
    0xc080c161815030f06051b030c0d0e0303270c1306030b01080607080a020d060b070614060609130b0409020901120203160815040302011d060a0510080d0302160204051306 74
    0xc034060203680000e100003891340464108558114500055590b10744071442c40014800385103c644c69408030401c04802c48a50003880d004550304000c0c0641501003583c0c0d0355900080e078020b0341360410614020840b00350071500b0001c0b800d0300011030f0388201004c000b09a03c0c00c41c88003480c8202d51990740a00074000814481030040081c00001c00c414a0041d400400c0102c02070708442d0010b40020ba1074032550400e810034400740520110040c0d5840c4240342440040107410750709040556900000f0b502803424078103951031080c01404201844891000c61030080c80081c000c50b074415901c1d21040c1c09a11580a0745010b00b541c0c0c0113038002c0d00f2040c0105490300b07a421651b46180448210180241d82000c5041c1d2803000c6042128140c6031124038059000d4188249503807401c0c403908004c10840940015610700441102200f00312a0f01c641c1c40d00409500d0718011107000d0f6100d21401c0613200e100707600900440c41e0300e035501704c1040490790006040e80c0e000d40e4085012281d4502d0f51007440b847d4890 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 674497931 1250 674496681 674496701
    0x31305010b0a182f0c011e2a0203070b3409080c0d021c06020a02100e010b06030601050d110a091d01150f0201020d021204140601060c080c1618 63
    0x200c2246440750010b0100c2c042d48004c6107100e0031000b291058200009400003110041012010300c031030414500c2c408000c1038401805c0320541e0a40030500c0c5103c54800300741c6018481a0701540c58400c4a03260300411b002c1c050450800242c107903901903000d104841100c0008411841200d842c0d5030190f4005160702040d4000c11201d030040f01414402c0c1c0c1d1503444501e00a41c0c15507030307505041400c40c40c01c00442c1c1c0450300036060500000350b001002d82c1c045070700c0d004070342e0b140c4040118946282c5081e08035004041886e400c0002080401c0641d0b0082000d045023500c540350200700240002080080b6400012210022800407941402030505244010244004c80d11a400031980b40c1080384d603114514101d0542404414043d81800d01e100307404075401c202c801d0f841555a621162034404800d1070484081d52002d094000c0d5081d028008a0002d0403503446540b00360312002c0315207645249a11002948445115118090b11803a03401c19201d001000d8000c1e152148109450b114001d03110900d00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 674499181 1250 674497931 674497961
    0x2070c05090c0307090e040f0203010507020d02070e040b0f1902070803011a0c0d0f020c12070614040f06050f07140a0b011205030304060c091e030312050903031305010b0a18 76
    0x4225621741e1064803d0115111b1100b4511152103900f0510129510781070301030f416509240c00c01c500150001031800034084980c3c212041240d607450701303201102055a0050503504041c011448601c1e603164140c1c0c00504108a450001070741d503900c50126030040e00221108100440100040403010780c14604440c201c445c021724240c10181220340b64201c80f03c5210501c0710003e03403032005600c01c01102803035040160040301104080038500c2c2d13403001c9520506001030407035a4220500c0140341d00740c230100c4883c0070007002d0413410448147e40300d07009104dd032580c98006100b07090118010184c00c852800c481005414000308505141d01800e605800c0110503403606035030840050340000880f0341c415009000040d12001c1148121504800d640c8080503e2601d03020044070000241076030f4003103e1084c2c5820381082d1001d0400000e80e9000c0781e44a001d81c005000080d1b05880304440034042c80c0c4110b00016100850100044020f8034035040030302c400486640d0911040c02c2441560040c12583e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 674500431 1250 674499181 674499187
    0x30b060403050d0320041701060519060309030203120a020c0705010219060209040f110c0d080609160309080d0614030a0221160905040201020c011419090902070c05090c 74
    0xe02c035036598070b41ca20484820180e40b041c80c194036100482c240c045106094441555580d42d4003503800500001506070942c40d4a4084005060324001e0b1401441030003400c14405070780c2c0380600075402460381400580940c0010042c0409001c115042d440c0301e1808400d006844d0208140503910348031035a08000c0c10b40d40304115110408925554840304240c3c84800980da51034540081405841080315100c0030303d0412031088100925540604200c1d10040101d8050340c084400032500410306a40030350b005001e0001081091052010070540182c450a01145240c0b465468910300d6000d40c0d01d4010341c56907401c0600180003c1109602000c10031002420113800c2d640009400d85c2008070150502ea00c52108500d4615091010344168584200301c1055107a4582111028100c2101e0032401401410140c10140d8000d50140701d5500c030f640e04240c10b0021315400788041000102c0300341c060109113180014000541d00080c641f06108100c0000c0d220f251200344400c00e000903241042c030707034014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 674501681 1250 674500431 674500433
    0x40506070f090b0c0307020a030803040b240d020126060a060503090601171207060c08130b04060209010306090e0a020102120f16210e090105040903020a020618031c030b060403 77
    0x852242c16119064680d6589000e40f41c5024518854180000d420410f00c110000a206130840558421800b03601402c0c0a0754503e0940c1c00003480340c0104010b0f00040e400c01c07951a003040015485400d2060501c2d0340c0101101c00d100e240e4008045c03a51100110500402500e0f0404d441e5020041041d414280c1c11820300d201415100c1805000344101c5400c2404440c40d100c20820070510010340c640700f02507807001c0c2801c0103000740040f03c42481c081a00040420310000741002d100f1134054016200000383e88071551000081e5020740d40f101e04164407200e001c03039680082e00ca8402c1410085000b0516003020f880064100003001050540312102480200400340b126411a046140789610308209042d203460041003441c911200448105010010f44200c140c020501840c0100e049030b0000c000eaa98004201c1540e0b81c2610040041c2c00c42d510354801401c089014102c0003400011030005120315801007032402c139141c5942030102c007007180c540c1002c40e050b20442d00c901070103559035480c103419 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 674502931 1250 674501681 674501687
    0xf1c0b0111031b1504050303060a0f0e1902130906050310050402150c0a0c0803090a0e13030302090d021804140604030c150b0411090a050a121202010e060f040506070f 73
    0x1d80902c03028200c00c2018102c560701e0741401007240d1540c0a02d103c1075117041900704155660000c440d020b0151008120110f60032400c018041d0448001c3c0c5030144081e03440840150f1600510000029041d03001c2c010f00101600c5000701d1b0024120500c00010341d03c1c0361100f003602c0c008116140b195858a840d0922000d42c51705c032400da03095044940c0c80c0d542e40c0e02100110f40f8109200d5005030001c40c5105005c225120f010001700b030000e4085401c20f0b005a01d450000c4101c550646244840303800b50003030440028001d802030010f880000b0030710000d602060700031840054400720810081c1c05a50308200030001d403111030711111281000105840d10b4a42d502a012085001000d4004800050383c0c3d04038800d190845552603401420501c981300ea5081c40840301d400103890b442c811100c121000c00c85090140403181103941d0072003000c01d5a05036844034181806940040b8045540f0b03482d0307000704c039401000341c18040d01e1b580078620550300d01414260306151015043c0000c016035103084a400c243c2c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 674504181 1250 674502931 674502937
    0x403050d050c0f01050a1a0103110a030f0e03121015051206060c011a040c0201021e070203160315060e2412060f1501181404020f1c0b011103 62
    0x90401d10740d20303000c490314140360000064040c02c583d0b00f08020410364030517a40050b00b011107445158243c9031046401075040d103250103e8903169242c00e1103000380306032280d001090342c916880000541c0c0d8052301c2e001802c69015007007010403440041c00b4004c40c88440d400003401081031000800d49010272040050030391280c4d10100f92000c01110200b1044e5a0364030450350b61070fa8080c002c02555001783c81c207921540d100781103944114501642c0c550054018002c803006802555140700b4481c0c16a0b14100b800d800910b400c2e60548540310031818180d900c0d801c1071010350702410504000c806905840700541c1c00350341282e01c80c20403940500134130001c41140c4114041c010000104800c44140120700c05d5441c42d512113030584100424840fa50362480c2d07449010382044500e89400000840054528100c0925201304045044408120140b5410500201442e00a00142c42c00039003404520094000b0751641c03001c00c0e024289844584c0d0b140c03254818504081c01d20380080e0b4420080302e5241c0c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 674505431 1250 674504181 674504203
    0xf1106040305031b0c0105010311030c0904082a070503070b120a090212030a050318010e071503060b0c0c040614011407110d0305031e1b0a110d050d11040305 69
    0x8032000c004140d10701d59840c0c513600340310126240d243e110b411825003035018101c00e10003511190011886600c1c10300b800704401000800c00381c40510240c440703a40321060781d8400341d42068070f0464000c0036446090142c1ca24a040004440108201402c080405050440c154000f0480150820240e00704d62004074549610904904000602c2096030010a640103800079000340da90100051740762140790424091030040714202440917060310300300d611a088858110510542da40020420404d9040c80800000988010b203800318179644d8610030b90b205a0090000d01c0b285400009030300f02c280c00d2600c01c110003006803102100c448243c05001800d0b84034a0704681d529078500055900510a402d13000002848010f00f1106a000c03d5040042c002d8006881001d152880c541c600e108401140024a00920782410850b1080b4401a104001540a0000e007002c3c00100316034662428002d005410b0a40c016448a5907540c0790f4071020700c215089505025220b00d001e00c403d0021502c0010158029 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 674506681 1250 674505431 674505437
    0x3040c05060309120a03140903030603120d06090606050c06090c011b080f040306050f010b030f13050a050f07090b0105180603060102100906060303110c010206040215070c030507060f11060403 84
    0xd803542510f050600c4200010f18203001e1002804440080d8903074000c1104072504160b00b01c290b00ca01c01c000ea240d100c281d950603032640c094140321903a016014002c041000901d00d00103045550b43c0b40400c10350b101540050041500818003820341c250610420b0751118100014100b402d09480c000b8103a140800c40546a03510002070b9003040000d04400c80d641c9580c41c20b0700c0d94655a903460584007904048881080e840c03070100c00000c5101742d4400b56406160149081c5032940d031000340e124051500d0000c09c0c4c81d240710350324030b9101081042c02000480c110680240c05031500f00b0f050130007074800003007a00303041010030040c3c1e03054816081c5500e0110541212555641c0c2c60707210040b4901b074907840303150226515040d0000f081040715804103044900c41d4031006806040c424601d07844050b9902114096040100083c0051610750052480c0507260b040c101d0501c400c40c0c843d40071006031600202c80c03a074081c8005000c12500503090724501c00180c50190f01501d42881030649a0034094001424 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 674507931 1250 674506681 674506687
    0x30f091a100b1917090c01120204090203130209061005090607061401080a05100218040c20010207140303040c03060b130218010801091b0806041112010e0108010203040c0506 76
    0x507101c030444201009019408000342c640746400c1140881d610040c3c25400803811240b265010038606208403489010310001500390080c01000541c1c203039400070305400511b0381c20000440e519880d440614040d40351600c104071f11000c00c1c81030003860440500050b00c58510781c41c1c1d8000750b41d031050440d02d1960054135426107401141c94214080c100049a0052500c8040700100b90b00000060300383c20540540301b164461015806d0074402c910403050b808001e0000900018030030f08184c1c0204c80ea001191802c50b036203030348a06404d40601002c01e00d1002c075940008034030041c8601d14001c0d25485c6000009185581000d1b0b80b40300380319480d440024078044e1035403c20010b40d61051600740050700c0c0e420082d55201d800c0c1c888680c0f801c0348080441d0208200500108500b1060b10030260788207900000b54406a11001c000d42e07284400030030881d1f0040d00c40318840ca1070100b10340580101041923100819a5040900b6018003240581042c0d03414cc0c414800c1202092001d1400411910b05032001c980d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 674509181 1250 674507931 674507941
    0x30e09090304051909050c0a230301140a0b160b06090c1b07051503160306060f120b0d080c0607021c0c03180806090106084e030403030f091a 62
    0x44c0b01c0c0c40c9640100b000701d00c1d180801444882040082410414550710281d10700041c80380e20560b4988180503401411003440140810b00c0c1c104c07c403443c0c210340144050303c030316a50b41000640764400e44c8070064400442c841030040040e0115201e400c2501203410302007901d8000c101b82154048c3d0f03201000f031480514120381ca40300080c00210060030b0042c0c540c1130a001c0740c155040c1c1c1684240c905c0000f445503602ca010425119110b5482030711026540c0d803400c0d030750512040b14590016040501000e69454003e03065650302103a58007c184142412501c6220480149040c00d00080c445804d641003140b4000307072003051440b218018030213803c0c1415101d0a909040f100e156904136400342c60711841c0e1021400c14400507480784524112802880b54a8072002100d46a000c08450f203c15880380c90300f0610a8043c50b04143c80303201c04520f145211002130900300103001c8080003040821007002051101303140d8503020b6440c0507011007805001c9115141c1d144c01c07102d9048251703e2100f03180381c00400d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 674510431 1250 674509181 674509219
    0x2040b030f1f060c020f01020a0209040204020c01020d05011806060c210306090203040b01030209010506070c17030c1e011808030a0506130609051608070f03150f080604030e0909030405 81
    0x40750300b5542102d01d038a01a11160041c0503040110402d901c43c0044c40e00e05551584000703000000c16501408600050f1219404e0001a422a4004040d00d540030301051800008501c00c0f035000f00641300c88044110b0741c807010785088601c1a080b89081218510514004c01e980f05460f40091401035403091400241d160202d0003004150080301d0403a00000a100a1220301813455060b203008075a0a03000da60707641c0801c00d90f40300d00c50000300b1044840d0300800c6810b4005010442130710010080e6450401c00030003490a041c83c40c03686c100010105a500c0c00d20704400d2103419070b0a80004140200d52000d501d5000a5010040ac508046a1650000f03020340c1c0340c071401d0281c1b28950a030140300e0243c0701e65800303000d0502255041421070801503136003d064858503c03903008104a45034014a06420b071070480c040c0c90500c00c10041a00c1418001800b000f41140d81c1e030040c03448001414140c00c1a103401080340081c049184c1c400c414500c00c0c000c2d80c0c00040304541c00c03110101d40a0f6079aa82d194051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 674511681 1250 674510431 674510461
    0xb0d080a0e090c090307080106080c0d0c0312050309060c0405010c1e060614090606030c3a0219020a0203030d0915050406090b0c03041112012d0f02040b030f 69
    0x180b5044041581809540c10030340c0060503103000e0850503164040c2e00c07111118206c40c1c040c407620032607502012070b110842c185041c80007400780c010030501d0300c050f48070f48880d000381e0159032984000074000000c01049100500645400c000c005820314a440d1400000a1030460003003400b90210041c07207003162682c050380030503507030355984840f05106890b91850400009604115002e000d008a040050054541541101c1c860841280c0b0340c0d042814a0810301000e61154005115185110301405405945281402d80c1c1402c0001d026a40311900070340040c1c2071010b221180155803144080100507030700803043e140303015051040024100c80c6800d003003105110681c2d81e5246149410280300038424180c21420005005182d0383d038498941c3c0032010701d50310044401420300800400c00500d00c0c61300162003009200340d08004103482c500310000100115079480c2d0940d00d0210141003a032400d0081c05050600e005c5440118141131911850b8941880001c290204400c107a00020700030010b1034000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 674512931 1250 674511681 674511707
    0x7170a02100210110915040e011406070f05030405011b0c030b07030906090b0601020c0909032506020a081506070b0105040c1e080a0515062b09050a02090106030b0d080a 74
    0x8144138550020f081070031258031007492503002d5030100e04254401d000c00d0007100e08071105c555010704260f191080840355010705014095110400b0080c40c0d001c40e040c5105e140b08140107202a6a58900e460000342042080314640707074640700900081c0c030100c0c3e16040c031074080729081400025140c0ea00c080403030043c100f00b1401484c95140c141e072603003030000da000c04500c103580a0702218141d070003950400c40c00c00021540c4a895500801c41407082d4003208601c18200c413900c643c043c800c0c04545c0da9140690f00248444000940c41004001030107080031700602c0b0300402a41c0540c9850f60980352609030500502900b0f0107641ca9030000c03030400c0e201c0c110b41c00d600c3e59000d11a4000d4004500700518214080c0c0e015030031541080041001c9900c07160407003c810800410321440c21507581281200038a8080c0407144c40c10301e0341440d400c5484c150240d0644280300b0720180550f4981031041200c40d410603082081050320f424051071060315240050040c00da04442e099485248400084604140b4011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 674514181 1250 674512931 674512963
    0x50709031203051b0a021f050c0403031206050a170d05090d110a08060403090e06030c01050a0309030e060a170f06010c2a06210b1309140a08030907170a021002 70
    0x58402c1c1190f078007045085040b50801f18400800f484641c107101070310b00a403940040700744108400c000090180b200910348004601000c0341c15603450001501c1c40c0c4140c2d000712511074044140303104008042c410300780c00c0c1d2081c0c03d182e41048100400300b03140d800103d40040810402c200804555654004000002c0000300100d9200307161034580142202401d00c90001100c074880e0204416207000700d00008040010303036449040c00b01401044018200382070003070741880303046190300005441e100001c00f54001b080c0c071607031481d1041043c2806e0851000313000a20500e019000d10200760f034002c620f02c41d120740081c0006d80310394040c1c9c640d09003045403402e80c1d00790341018000001c2e400d420840c004981c0590b948601b00d80810410840240c500e00081940e201011031030a540006032640048103aa0054044000003540714141c3c51600c0d81c41003003550031220100400c1810082040988040c081c180300c0359a22000c3c40b91407568414100b02c00901c02c902c4034941d135a80d01d108000254451007801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 674515431 1250 674514181 674514187
    0x6090e01110415021e0307050d05040b0d0b040b0406080102250209070c14190b0108030307021e010b0307030503090a152c0306070f0207090b0604030f1106120a050709031203051b 78
    0x442d201d1b9640c1c0800c4080350580106405101003d00070001da070b040702d4441c0c1450349880404203400c00106110313805c00340d12030f540351a0050f00340c03074501c80d1a011701542400184d4407085004004454602c0401c2c01d19405060550030380140c507808403442d000f00304c0b0305142404456620703055a01d2100d10003039002e00d21464840081c41c103513007030000c03480394083c8100125507603c0310b21194683c40111940c5001d6400701c1520110b450003901c4030142d00c0c0e00f15000044440141d00040d003445029441550703564004a8100d5040c54841002c50041140c1580303070081b001540c1e00546410784403820030310480b00b054000b91380f030151000c40c070b0410030004068030050710300000003500d180718140c1ea02c0014410940081003d0803948542e075031485d0020704160606d0303d140d40300d1000b42402101290301000e01c0282c8182034640f8405403840700c6400581c20071920300200b8100840e680107114804101e0301040801c04214012100090181c06240200e160755803d4680010010160314010180c4400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 674516681 1250 674515431 674515483
    0x9040204051e0901050d0b240d060605030f03210415020307050d05061917070806010605030403020f150f040c2601060f0b040b0304140303010906090e0111041502 71
    0x8a0402c0450508940c0d02000d43d88900034050603c580c610020480b40c403000220f03000d9542810400408008418501c6441000c45d003c56042000c481c0c1c201e548589030310080c0010320303003400000c03224a800f400443c20085041c507103c041008505603078400d00e0340000030501f8007858140c0d50500040c0d921080d07540c0e04107007000a049901c2525a1510340e8a080c000c0303026898850101030302452000c85800000f4103043d00c8030003d00c40007038480c0c294812807000280d003150912050380204069202c19840e0302e0541070190420760245d0105280f5040b00c88200c00780700b0042507064002c83d003200c02581c150f40e589000190517896401052a00503901d01c0c0d040003060030615010901600e0009114055551851202410441c01641d01da40b07001d02c81840709600000c050341d07010740245000380d4145c40e143d80182c1168002c0c0c001201640d16070b8002c6c001d60180340210080d6000c24002080010b240b004115903030b014074061070340c03000c80c1c030103503907203418400c1210780540321405070b0b26910342c800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 674517931 1250 674516681 674516719
    0x1020a09050405150303041404020c07090902011101020307020601060507060e06090d110609070306050c130e1e091b0a0e0a051b030103120e0d050a050d0210060303140904020405 78
    0x101e1245900c61030520f0b002030316515910081e41c1d10000041c000714102420b001070003410041c0310461581080d428462a442d0b024200020802419940000110750085000050468030312225980c1280c2c010801d0104080c0e001813081d04641081c6401f5403200810700d0440c016104032002c07c4121b210303480a1180c0003402080100749145192a05c6409656400314980c81e1201100d42c2d003440c2c0c000719004c202213003031600410ba120144110580c500120074490301505035240c0c0151005034220001c008411603c00c2400305040ca000d100c40150f8581500203550361101003064075080415071401050503150103e20320040d00c003035030740000d0b54504600c0e484001c05044403900e01041443d8191800c14440e441140d040e40e4000d9042150700d400e41009071480c0340e03810b0390359800c40340c0c407820840403c02c02e01c900884544190041d110603108004003e1030100a402400d8040d450441c007000001d41205a04405c04099404682c588070707600005802402168070494100714024105c51035111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 674519181 1250 674517931 674517947
    0x1d040605060114031e010609031a040c0806011d0c091e130e0619050c0f0c1c08060a06021b0909010608010e07031b0303120e1c020d020c03030a0c0b1801020a 69
    0x383c5c0c0302e281c642c2e80c0c1d228100c070081001d21025068907007569407040303441251010542d0003401008a2001f965956400c94a0450268020007068814030382060545040c11000344e0081d0450310883d05040c0044001100781984c02128a44ca2580c0c60401105448082400b50401c2040000b0082940f29002c0a43ca41c8002c40e0001400c0346031b0844101070914074894140a181417007413460070100416072201b840c1e8044072002485128400c02d080f45680707013049407411b0400c0340c1c0d0ba440c0581040c0007440140c3d181d80d04a03070150b4020401070182d000400c0408400c800088a1007a29521500c407074900502c0e59410032629542000c1d41601602400105081103900c00c141204400b080c100340440440190b0200400050742915443d14403000c0342c0081008401540a07200d44203100ea0800d40c442a5646c0000e0242e002451640d64050b01403002d005011020340140d860060808801018540224401840035813800c0105403840c0c10041c44115103031281000719a15201c030440070386661 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 674520431 1250 674519181 674519221
    0x1202130e1023130b0c03130503040b1c09050d03090305090909061e153f0706030b0f060a0c08030a14090c030d080703150b03101d04060506011403 64
    0x440032401140203c1c114984016009800110762401d6898190080c005a4070207008903a503240010300d2040403410500c001e100409501142a0b500c00c2d100045940107500006550030840c0750600203004200089010545070085180c00a0015110715080d5814050100310a030004040c40400c1401040003400d20b000c0c22501c0c4494005500c000c1203100c0350f8004407840245a490300303e18001906088944080c10902031540600c0701160b2106040b51010600301525030300708151202c50000382c140403032000f501483c41d0a1000140e0f64001c10440d00100e0307001070103000300140a24806124800b1003910b103500a03106c9070303281441c9440c1e0b40074060314015080b01c20920310200f000104c001407040038801002e03010701010980094191102900240700200341902c900c0b04103000d581e00d0700b00d00042d00b105041c0c0c0d42c4034144a26420f61084583d001140c80d0352002c04107111112410503800c1c0e1144d40440d0200303050740e8540048070454412542800c8524011045c0300c004c40d0b94445241d803003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 674521681 1250 674520431 674520491
    0xe1003140115030b0a080c0f010c050316060b060c03070f170403050c030c01082e05061c0c0302030615031e0712150501090b13050a031a011202130e10 66
    0xb400a501080303504170b024881d2194a41c05084020f040382001c084031254460141400803c0510903100d02e815640810602e041203d1210020420800c05101e4070319443d0060351400c0c20310905d042c516039284245040603020707041800d02d060800002c060302c00e982c013071342031115a01e482e03a03403801559885407802a640f10307016180000e030155210301801031058800040e103404080c5034040d104088030136a401c40c011607100e0380d004501c0f07884510052100076900d0075a448103d03042c0184c40100c0e0304200340081058010002d10075180d40e00d40500b206035040045140d0390703031224940400300110004040860850b000c0c02c0140044d0403009041540c590720300280200c01d0044100c595866040c0240e82c04248017120612031903004202510402c200c400c080941c2540702c40010701321300a550310443c0d400c60820300c5c000b030600c0d00461640c010304100c044481030800d02c0d40000e854545800b01070780c41c136503202400201400104130515081807422000c22144001b040b9503c1541958015040f40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 674522931 1250 674521681 674521691
    0x20303160b06040b0603070c050a14100509070803030103080a02010b03060a020306030f071802090109030209010803190e01050a080702030d0915140405030702010c020a09060b0405090105040207030e100314011503 93
    0x5400c01d80507040307070140020b00192940c7d840d03c9054480d404a103005583d075120f03c0c8911000135261030181030403c1a86001080d84e851100342035001c3d40c0000340141150b0300f020a08000d10080001503a041da070340702040f41d40701c1d0540b40c0100e004004481c04c41d980751040350305110302114154019801644103900751003000254268482e5690080d11601c486180300742e80e03031920108554060072140300140343c0a140071382e82c1c0d00040c1031841c00383c1083c581c5130000944035030310a02d070000540c10030f901414206518030100c00040d000d80540980d400c1030000c041d0014280500c203000305c540c401d1291030104440740050a1660400d9440441c0d051002d00e07244103160f000c0d081f85034051040d584040114a0030303800c2d50044402c3c101a603030480c0c0240c000c0c040403609170254080c0e40050b21420407400e031103e1400040141c0c401c41a030215014602c100031380c1c40401e5122400326038414003030341c01c40129840004224010840445281008a00d40d80041400c40502c40a01c0b549901c6907410f00c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 674524181 1250 674522931 674522941
    0x12040603060515090a0603020d0f0e0f01060503060411040507030b031009050706170c09180a090209060a082505131b0e130b0d060e0606030f120406030207050703020303160b 76
    0x3c0e036101d403445076035008010500c1046418465002400b103c0c2440c0740101d141041d55211506031910745010104c50381000b0f40c0c03024800024841c5100900d0201c005010780c1c05c1545a168044080d000d501d801103032644009035416000383c0007000c0042c40a0102e0f00042c08000040c0700030988202e040320140902080003d015100b042200c00c9142014030407211a210400b4044050780f0440704150001c642c80c40020301c0949411a072841280300c0800801c9000f107620410082080c0201820310131034a02c2d03003d003e240000070711944d2440e000300081e0140c0d0b4441203104103962481d031005500581804182180c4007240e0025100e420700b40042c410303000f100e000103444410304040e000b0741183c601c00110201c00c1042c0c0240302081c0c00a8400604800a0b844000c00c0d0b82c900c0121056692110f000c2c800c960404000301c0100429080c0508500c18012800101500c1203100b10b00816401003407000038800c09000203030085034002d08580d40c4502e8012081000101c507081a2122001080042d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 674525431 1250 674524181 674524219
    0x6120b1b03150613081e010f02030c0901031a150c06060604050d0f153207021c020c10201902130b090406060513022505120406030605 59
    0x90148102c0307141d45001c00c9015050003090b0700080000e01844224110004000100703200a0f41031a06034050070700b150020040c800c1c01d60380d6440b50014000c0c8100100000f1850b41410b80c0e503c2038091030003003003042400c0110754000c5000440326901403105030749060500c42c03940003040b45045900944910341c1c1d8040070045540100d116140d0002e91050a03c80014840302003082d0803445160704061708064514040c0c00ca0315402c0300c82c0c60f4582d001c40381e500d000302c000c210740f02c40090b1500036440074901801c00035241c444509540c91010100452038101074000d100520001d00701518688921044250003080c0342e5030070001d90a080d12801e500100b20b5004100c1d070001c0380700303441c40d485008070035070138410403015144000c070350156180303000a0165a0420007078003d81c01080c000c90400d0901042001c1f6a0203800d6140000e4810400199507039507030152400b0f5460b070000c0c2510048040d0030b1950800c00700c0d030941011207800241c04038a194165000c0000d8030000e4a808600d4003102002d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 674526681 1250 674525431 674525437
    0xc0201090923011418040f02012d0c1e11040e030c01050f0a060f061430090d0c0c0b03070309020904062007031707030608010204260703031209020406120b1b 69
    0x3e41f4000c07111141d0009940030304400c03072510140301403120007604103041505200c50944507001c00102d0700300e1694107102803400c41500c040c4a000c040030002209660706050b4141840c1414099a2540490b80715800d0a2040d5210080c443c00240007034a02001001c8980d84200d4145414501d002004581d4040d40d44410003036400340e44400381011041034003043c554004040a0003000d02005d907030b0f55500c5800081103c00f0800369001e8106041c28500c1a06013449400d029040002c000c040602086451100d0422181c00b005042e50b01d45901d08103d000c3c050400002c5e402c81c0140c0c091000700070665001c1c24100034984039102c0245920700d0900054800c6400c090000744620141c002e28010404800d608014181000035000d82da8000d010709903041036010049058207103003a030006200d041c0c0300c20500c03000f0384042c1082a046650182c203076048140649011550340000004544031030788400082e200d40042d585403000140b419038881c8a04545000c44014501c07880d2840c01c0c00c43d026 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 674527931 1250 674526681 674526683
    0x30506010c0803041b03080307030509190f080d0e0d14180f0120100f060f0608070e1302091f020d12020f0a031b0c020109092301141804 60
    0x1e2128800403500d510782d0726040940b0544a60031400c0d07a6540301c1e001300b55031500441c80f98030029101c1c40d00660180445000420898040d0050b2030b410403451680b104020420790301c070500380d034400c1080c00d001e074103130260030700c5640524945500d110801100040029074003040e5552100c4072a115000c1c050140901d0a00c0c1114288000007030009203032800d03007203e10003010700d03100341d100c0702c0c00c0e00c000404030301d1040d9001305400c050045c6a00c04114020040e40c0e0402410a00c60b051a101c50011501130314440c580c10880d240c00400d41180c4034061401c02030740c00809201c80e0802c0303c2d9100000350300181042c1e20030301d10003040358520885c02c0143e881544c1160040e1080100210056504540d40d18040e44002e500b0026000380c020000040d00310b030451079400280c49880002c10b0104001c0b040c80403403d000ea1810034400607070703010981d44152159100041520841d206041c04008806001c00520801001c000b14406040c0903c450032048100c82040480100054a500400069034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 674529181 1250 674527931 674527937
    0xc090203092b050f07030c051606170408031602160e0106080f091e0309030a0507050f18011509030f240b0603040803180f06060406150c0210020f0a060b03060703050601 74
    0x210134004050b809002e003807120f001c1d0070076440071011580c2d0300342020a244650326001e101818244102d60380906002001080e04401841a08003900c4504850000030f00c1819121010f652500e1524400c0c0000006900300000506910341c60350704c0020074040c240034050003d6021000214503000b0f85401500404626000c1c00d5000680080703111160b0041586070090700c81003056040d20b407400c000b4001d0003030042c0050040d0345c0c20041040980c00f10008028030a6a201d09070426241d4400390782030464500c000107684004034900b064840355100d41c006007840880c12940003e200c00e2020015030040c03101c256803244206091208111000e421081d0313008541800041d00091410380119001403c82c0b81d1101605240144180b4008411040c5441038011742d0600686040500035035000c3d041003003071900f10118084005010f04502503010744582e00f018601c01040b4000d215500c044a041c40a4401030000d07820300303038041c040c042c94443c040e104180002d95140d11900c1040d018a00580d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 674530431 1250 674529181 674529187
    0x4090f0201081b2101060e091501020a020d050f1c050a0e061204031e030203240d080c010903020c060c06270706031a0118060c0c090203092b05 63
    0x20300119603402d00100001c61000d9100c8001c00c42c0f40d048009008000440300107008100001584600703000d10690115060000c80701418116070744040245a00c07510428070409103103010340040340390411620002c2d4000b00c10111316028003402156024006480c00c04465130300c02c61030700c20359800c2034219424000a80c10302c6000c200920649034160700120050160b428041e800d01d21800103541901c00300c02280d501203211b0030056000070061150350380e03070404501314a00403021850604114001d244c01d2111003a40c4022a900c082222505c00e07004200607032a05502816207008121016094025219207003500360185424000c8581a60400303010300716940f200c08284659001c400690320648001c103424010782c44041002c4001441c0c140d030082182280300c1500609050a503030017604100c1400f101c1500c41406901b402c00702c6182c1d00d0715540d484a02c0c1003070030f113242e0345400003290705000005005480341d00084a8502084268081003080b021440c240340c0062585a0385011130814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 674531681 1250 674530431 674530433
    0x8040c090c0e150306031207020a090e0102120103390504020307140a02010203071220030a02070f0c05030d02150103240906060e0c0705100e120708040e0604090f 71
    0x5400000c1e100c407003414465442c002d058001100c0f02165190500c0c544004020400306140c20021181d000882c410708514086564000c00d4000202d8003d03090244c1c0c8404c00000c43c4502581111014070140d0811081d0756100d1410198403800241c0100c0000818401c03000000710a81d80c4110a0302c8044405e81242d10340000e00c006508018032001c00d015881388450394444046000340a0103450703600061307803840d0501000d405003428081e15a61149407030954901400c00322031080c00305090000300b684a1b0f40e001341c890060300c03d110b001403950501e2411001081a1154004252401201a01c0f05401c244074201e96a4030a0a0360410810300701c0700400215030751207903042400c030711004260918040e012a00e800d8034505481220001e1352983c00b0440950f00e091000c1c1c106644040c0c0c00d140c19600d44500c0d54079612409074803040c41da110810440803404002c010500320100b010b580d1281c042c1c0c02c2c000f00c541c11a03c210001403030400000340b00f0f8901480384200140d807106007010401d0a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 674532931 1250 674531681 674531699
    0x100b03190305070b0c13090b03191b0b09040e01020712050a0921051501230a03050a03051c060b0a120b0a0f060210180803040c230102010c08040c 64
    0x60550280c050200801c002d00c0815070044e82d061081804654050781c0d020340341e00c83c5601e00e00983c440b030302040c1303010312508032a900442c000d2200c2c91900f20700c01486005040c0030312000340070940001c2c841c0c070340c1400041c14101c0b8006005500300494040001c0c210305007265081c0d1160104c02025444c940a000c0005400f03407004c2e107001c0c00c00e8074200c00007d031114840601d0325820010310000d0780081314400c0c00c0020030006d490303070b070b201c1c08140c6451940750a0140e41100307099984000ca4180c030002d101e0650700c503011030400441e0410201e03000203503a420060a0307540142c086100880b1901c0d1903031501140e6006100441320005a03603454000c9142e01103034070a06252101e20025200c0804885035541c0d07041d903801401c4c8842c034030f668207451b10001918054500d80307103c00080c1805041d41c02550040f880c40d05268021000c1e0b580ca58032860225500d0380190071902c844044415010514a005800c14803081000e8000704110784191320251a080d100300c400030b020b002d4442c002d00041107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 674534181 1250 674532931 674532973
    0x8060904081e09040c080f060a0308090f031c0305040209011703070201030507020f07080f0d1e03020c0307050a0819020f06071b17130509090703020603130204051602100b03 76
    0x4060442c00e428081c6042c001026500c410440d8030004840400b40407a03950508405608031034110390402c00c8520795030b00d000443c090501d131148201001c41d62889261002d210034100354201c6004c00da4804c0740c43c01d0180003020182c0e070503402044928001320f0615041000700491400c003500a50a000306540110040d010007040c0340214066000c8000000317808000300d00c0a0841d18002d041320200300401c2d036142440c00e546d141c040004c1c070704c1c454000d03241551101c50076a0040c0750250356528260341261a40c031601000910621640322a00c1c00d00241c14090656001c01c812a8080504100000c03603680e99464803500b010381180002c00c3c0410300450a0719400012007081181441d019104e24558000d0342c03c100600400001d0001030280302c0440c01400340034106d440c880c0900300441415503525075400700031700032500000440c0000304c08507018460542d00820520152402c00d0091281c41e88504140015100d020721040d03000314540144070103040050000d055100000b014482c52300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 674535431 1250 674534181 674534227
    0x6050d0207030c140c01020d2c0402040312081e0105100e03071809050c0102070f0905092e05060603220f050f060405190804030305090109091802010806090408 70
    0x81e103c81c184000341034180a00e0458890902400001c02c181d8006807c104a084032130003001501e103104540043c400c014110307564503e560b81801c00c4d0014010400030306c259080a441940c0c0c6e528500c03003a88c0e00440040c89100604240c001c1d1004024070101088028092554080c040c5051504098410b1404154481005044a041e1551082d50141076030700015480d00050301d03040c040041c02010880801c600c0020310040400f01d02d8410f003156201c101e07000c2c80c01c0c2d40e5213900100309506000c0140c510811400c002841e500281c500c5081001401e0568810505003001e00003800362a05906a034819440c0150440784010a824600382c05010101c0c203c8240c010200c021300403810030025a0364480c64100103280600f06400d1851a0003612120311084210401c243d000050448040d00c044075450308120392900b040000680b0060a0340d000000064030b0034042940d051006102460110700030b8030340003103546400080c40014141100c000e08800c00030408000509005d500c59a012 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 674536681 1250 674535431 674535437
    0x306120106030f3305100504060b180d11060a020102120f1611030d09083c09030d0f0e09070315060c0f020f01050f1207031d25050603040c08010c0906050d020703 71
    0xe203868500190803242e075a00400b440b011300bc110301141c4012502002c07010001180c55600360b1405607120b000c10821074100354003444000c50a500340c98003d4064450302c01c03214082442e14644520401001d04048944040c103040f40c0c110f01241500032500c00810034000400b03140740c110050510005000121070850b143d400402482840f800701c0c2030201c040140c0612001161446800e4130036446a00400200d0b121404011002190ba000607484c0707031000107414480d090b04000801a6540364032034218507001a151401c0000746a45640002d14000f0040030510403544c60750000c41703801002c100c000b850040c1b6180d100c0d002d0301d0203054a005e501014503105183c00744a4104440700c1d00301130585c2c0b400c43c0e552020300001907014000c0e0b400075811040100003a17840c0000440d0385800824110a1000d1410103140d1110314501080015200140c0001e90f607041038942900081410b202e030300c1c102d503e02000100194411400102100d1048d6582c3d81801c0c408a103050080d0300c89141103041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 674537931 1250 674536681 674536711
    0x121209050a24050c07021503010605251e02090907050906060f0c0a050f1b011b140d050903070f0506120a0f0c270b0403080306120106030f3305 63
    0x3aa585024081c840c0d0311413284140c0303425681c03050102d005040c1e84500f002c0c0c402400113011095201007a40d85c4800d00b4165400c4105050084115000e000c05014020b110050007000501c6801d4641403402e078400d139401030040d61039404158a8105500500c1e80c85420400803071001c2c07919070050505096800c1d8098070700b0400303000c01d0b0728122160b0000c43e0ba0f40c0003280200d542c018203104e0040e1f14045469416094600071000810444040503444180b140084840c002d0107034002d030115942074004100c0302150301c00c2a0151040d0000c4104900c648581100491610a0007000104a0b071f00944014100030384489012400300008018031a4540d130380100c20b000002500604180c3d1034251076080711200c400d000c003090101c01c94190306801c4041c1900708030703416618045400300c9030480fa4158880d00c1d100c001074a901c10006400c2d11039800e110011003031150b010084408144140d43d02d0b022400c82c0d15509001040910b015140d5000c1c0240310a941c0d07080303030416a40030902d0010025 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 674539181 1250 674537931 674537993
    0x30321090312011217040b0d1503050d030e0609011a0d111003090b0f010302030715031d06010609060e030604061e14011e0e0402010f09030f121209050a 67
    0x803030700c00b090380a42c0404240004940920408069084a680840c0503151501d810b00c81d10f24a94450f58151035815580e51591a5000401c1104000510b6002d0306544002d940d20b040200500b0321041403103407900910300030442e1000c0501c913503a00c02078600d007414400c1e00e60008200d07049400f0b0342c0617a0000907820b0469100d640303000414090b04829200002c121103e818030741c080040040c14502400600001070003d40e030001100c0301258000c01c84041995041c1c1c000b100940641c1243c142d1085c080c03514082420ba01141540c184c1d0480d684da2031038070740d072a0401c88c0d021640d0009581c240d04008007107801700c1c025800c0326101e01500d00d0090510510400c0b1041201d203216107403a044c2c441000140156001825082e0610601d00420f4a140f0304101032100c04c03020241000703041c4414141c2e0540300b9401228214000d40d041580d6402154507070402c0c24079500e000801e5400543d10000040f9460035500c25041d0385900400103021401080c3d4821402d02847d003100100d0a840b622244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 674540431 1250 674539181 674539207
    0x609060d0b0403081009050f0f100503030706020a0e030303040305030619121202070b091e010c0512030a0f0e0a0204110903160e010602011b0c11090a02030709050303210903 76
    0x68011807180d502c4448503e008080d01005c1601c54120007400ea00b003005001541d0b40340710b600d03a003051208035203443e103840b550741c0c0b80300f100d8503076100036014000852410140708450b03014003c422280d445003980e9050000805899103c11900100480c44c1440480d02c241002a0010151189181c00e8011340e03481c3e10110100c2c142542046446c0d00382084001c00c5254103001c42001090020040d90070600300d000000c28603400c0811040389500c500d03d02d10001d038855840ca000507600442a81d15240404002640f1a40200d451402c000d0800c1d4032101d5020a038402c00c6002c800c07000c090a014505642007002503c030b002682c2503000824020035485a509100125a911512081c69505032804c0100c0c061094140d2010003564984001d0240b1142400540901d0002d140340802c907a000350300d0000c1003042c1031000103800c91082010010303c214190700450158540b9101c01d0216591a42003558038400c540c1c05000a000e402c02290120110b401d10340d41021409090700e040c000420341138 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 674541681 1250 674540431 674540453
    0x30e030d090b0603010b09220f1205031b070f0201030203090703021909060b0a08011e1a0306091f060311160302031905030123120706081014090609060d 67
    0x140c8902d4008000e0142a00d0309204100e2003110590389409203280540700070500032580c40420f030340794202c2119102041442283c03054100e51241d00c02d0b64450b10403c000340503070000c075001d0702d030003045458600d01d243c0c03102c060355000da038800c1c204000f4881c07950044000c0d400140150a10344140c0002000681c0c902081c1039905d020070300340740402c901d002c80120540e44135a0126040340f104020641040d40d00a81c401e041d40c2d1881c000e0507640c21014414640102e0035484101d004408640618950010000540c02313544201c40c82034031a1505001c0340c00710500c0c00c00390805c4480c0180304121481c025004089010280340038241440446101c2402424140000b00d0040c3c00c0090700e40c5e2542e164034440c42c511800c91500c28110742c1000b00320b124001c0403258400b141c1d007003e028900103507604182c482160350480107450b0041d5444034050071a0b5001d80d840d02070703c41e1807a0301148424441040404d03410b40140320303103559203034101408842a0007a1406030414130321940b800c0071500e400310b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 674542931 1250 674541681 674541683
    0x151211030f100b060322032102040518090604060e0a1407050108010b0304080403170f0a0e0307170c040906060e07020c011701030b190f0603030203040503010608010507050a030e030d09 81
    0x94903050b050300c0400c408407481980c04074410f80b0203205002810342603108054000c1001050001c4034182810191110074108800401d070f111000c0312040d40c2d80c1150098003c07100d041e5a100c4400690068007240004100c40c0c6481544c007040000c0c0104010340c0146104400000c180c030041203080e12132400902202e6061502a07101127030412055a00907140744c01013450360856804d504051391044074074881e0384805001c8203118010710140c95444421500038080040ca0180d03201c40d41600070344041c0b42001031610074010240001044061200c4003003644100f040070b04010526401080024401c0c0c0c02d0a0b030b80345a80780c4c2e0120300c56001e10a03040c054001500200b140410082c00101044004e444035551800203000410019541510700358015040c0b844403904001e89440850060901c0c180c40180350b410311400105154000c03000380140d0700264000d11070561503100c242d003618810348110f4001030041003204030442c4a64002151041100b041d280fa010703112100a05844404034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 674544181 1250 674542931 674542933
    0xa060c110312010f2909031609050a060602010b060d1508032a07060f0815061605100e0c0d0c0807090b100c02061e1902060712151211030f 61
    0x50044014900c0541c0041425161641c14810410403580c10b115009800900f100d501041b10145650180a00d92503e64070407400a4003950b21080c0c03102800c0150351102030a0301d44103001c03c0c8103106008603200c100000c0d211624002001080c90011700c0d00d203001110103a0250000300e001c3d1400c0c0018200c0300c410742044280d402c01e4254103140c244d181c51845946a10070b91003081b08540109030040400c202e07040c01a0590b98a0f46060708400d0020010b5600c200c00040c0074200fa0381400389206018080d4007250b80d0905406100412110821140c613403542c099001101140b82089541b50154895200884100d0fa5a40424030300b0f82c0300e0300b081500d81d80f5452041d08608210b6003e44940e00c0a1038403491803415500401c18500c11300300c90701c102c003070700410510300d11b9120b070201ca400e00b01c2e40d5040c43c5442418031009413585820786015000810300150f100720641306001d000c0c144400c903a44507a10038507244113019206614103040741d102e80a840300003c0790f641030040d1811021114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 674545431 1250 674544181 674544217
    0x5060c0a17070b101a0309100f150f0b030a0203040201110607080708070c0312020903070b040f03031808070b0d09050a050c10090e010306020a1106040c0e06060702030a060c1103 78
    0x880c2146a880c0000e00c02c0803c800b614604124291901e00c0726030f031740c61400c2440ca56030f4a03646060390030300403542010000f0a09108103440410301e2540098041d180308207903481709a4481403402c111030068424125104024004526184400c0e4011034001e48141003106200500b14200c0e41090012039085000c900c42c0c5041005181d0400001da50245061402246540d12903401404c550703007007203c41181c00d50104421296032010800301000c0c008209c20039231901d5450503125400355030703070004900084000d800781d901108880c3e1020207840002000c1d041c07ca0402210981ca030b0843c025040c0c1c0300c0d8850744c100c800704c1c1051022803642030094020703140407e41c1d0b074140403d1f0140d4115060030419900c0040100e50165207210341580d40c842800f507555003850400302c4542000e10642000740c01090288010003260522440c203c0b03a00350300c580096521007040120382c1c010b241c400b039090340120240000064465000618007a9581040301e81c24041440c01403454121002c507146a010603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 674546681 1250 674545431 674545433
    0x1080102070605060f030a0b090c060c01020d060501030e031e040e0a0b0306073006030c060f09050102160512010e060a0e060a0905030a08070e0d0c051008010303080105060c0a1707 79
    0x10f406115071110303044c1e41510007003d184011980e9600c941c03070003034020805807020410300c590501001006a100030b1542e80c03516204c1110038000d61094504504071460020001007550103800b0f82c0b6090721004010b10306001c2c903102a181c8080c12580e0404104400b00400702d500b03902c105d000c60003a99042c0f000500344915200f414602080500a2424450000d1114002d26070a5403429000601c0b601200190181c07400c0be074010340042d420042c400002c8030404507415a005d202c84940c005150703111000950390b80c00690311101502402c02c00801440400c0c003081c102602c014241d150307418000140c0c000341c410a00d08110044d03481c103203482c0d100da00c5c2080302030341046900c0d00080d560404110500c0f099881c59603e1254880f180180300e400000101898041c0d2403c10048402803d040e0702c904061410b076000000c035002e060701c03802d01030185102603442255454143da916496000c80780c0d0814042003241d80100644c070002c1c2c0715218604d40054003c0c07140500d08a200003001d51a4001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 674547931 1250 674546681 674546693
    0x50a0f05030715120603031d1801060f0c150b030d180b0a021f021e040e0f180f0607090801022a030d020f0301030b0708040b0408070c0506070c1701020405010c02100e090108010207 79
    0x4608d406500c45d4680d907008000d0402c90080183c1124402d0030003103180d4501c2c0c1c0060713913500c4611002501c0d00310845016028840035400a2016600480a03242c1c2088545400d480d00c025a010100c06004a00c80c00d100c00001d0368002c1004c500c00f03004442842d4482c40e80d5082d03480100b06040007903a00842c007082d58190001480f01c1e0321004c41c00081c20142040e0b03010744690300c010300d8000c15201e80e001140c00c1d041500111002184e2880941d080c010740d03440700c036031b482c03c05403040c0380000d04004002079403500620960305284824800000b00700c00400061480455212112030036000800c402c183c0c800309071005054600222440326160740c07442c01c080240800050900c020b10110204010005441d007040e594800e6000c0c40c1c01d030710b81210b401d082d01c0b402065000325421060000d848810700880282d50301c03c5440469510300e13070036100d0307011900740d020780d1085601084002c550000103190050600c102d60884d1303d0004000600341001411001c004e84c00012aa540041c1720024442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 674549181 1250 674547931 674547977
    0x4030b07030c0503151e1306060f020706021216050f03040602160608130c08030a0c140d050d09050c0a06030b0f010914060c011812090b0f04090506031510050a0f0503071512060303 79
    0x5038500160034330328030313081020b5201d042d01c400010014600051031480c031070702d08211840301034008045400e41202c44201e25500e41c0503000c1c3c08003511455410410001c400c0c0111015a041943d40110903260302c1002461900c080360126074001d042e4070003003650201000a020156a10303610542074580904004144207032198038007206030000400b40c0714844c1c1080c1151541280c2d404001007510071420712904040300d00d4582d541c818901040006c141e6899006983c45600c11101c100c025064074006503440207051049810b011903138240c1551515140c0060040701000b00b0001c680010254403d40c03040c801008120f442000b66011094031640c003042c036102420070b500030301e49028a810500c20740303030049101d20101c40d500d0703000050040e10284004251004994212a51420044210341100e9201d0080d40d000703003902c3e4800640701c12900c240d84101c0324060041d101ea02d090007007428201084440d00002d00c1081d402200d034100b9148107040c003c5009039a0744040d51442103000315040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 674550431 1250 674549181 674549207
    0x3030310031401110406140d0501060309110f13090c030b0705040810050903070f032f0c030616030b032806050c0a020c0402130b04030b07030c0503151e130606 70
    0x380c540000b4042e40f8401104445c01e45a4030700b404102c501880741941c0c005d1207500341c910310082c05e00c4000100103030907401031203159216030f41c10384101c2034600c10f0005c01da000845440d4044032074941408064480e50018003594014056070340200d44030389620060030020398070a000520002070400c6280014849030701001e99041050100b41052800f9503540c1c050100701074200c0040c00781c04000c250140c00031040003000300d5021495540c50707517504049210780703090748061b07400f481001c004507182c04984148030359603001040000303408440d0102e004006100c0d2194251040510440c0704000003040482c032100c0410362001a400b180c03810350103860f000340480c1c50300c00007440040302e29a0080381850f0360700426500181c890204000d201d05042540e0301c4005101070004010080c804928400c82c403e00140d1414040301b103c0c048101d8003844200c5108450310300d03908540380300385020500346000c240c069074031005041c00c94001131490034a540180c42c4a55544600300119500981250404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 674551681 1250 674550431 674550433
    0xa021009030c03080d0e060f04020f0109060503010b030c090a0b030604140126190501141b2d0d090203010e0c01020717031e0d050109020322060b030303100314 70
    0x24038541d104960500c160000030013001c004280621219283c0d8800c4500b039003554101d1720b50781000010314200700406c0c4c9080e800b5545004854405500903105070089410940d2101e140d81c0c03920746410b241da00f000d4940c01039008200b005140555500400c400039050761721495030f0328103028080000303c3d01c1085d2000306103d0601c00400884e010300003086204045600514690b03942041e8940c1402c20048040030000d100c1c42e80701050141c158400320708c0c5d208130701d4001a5622168410340c08000d03c0100200003e90401c54080c0b44000481001d805984943d000d6508000342120009503400100403144550741d00d003001429403809018003104490650040e0032000da0000000303440c1c1c02e10b8042c40c0074a4031a50244032012800308202c03090f640e80c0500c0b118002104840304082a80b24003111003c1c541800b0011031402c40350320807640901140400101c6502c3c2c0c0e1291146800748081080d0f861940d80c02c80400c040e141440114820700004020701c3c0070078154a00214440c126100c1301e05d039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 674552931 1250 674551681 674551697
    0xd0b0f13030903060c030608010501060210051f050d0f06020703081504050f240604060c0b0a020a02030d2c01050a0f05090318060f0c0102030703240311060409020304050a0210 77
    0x2003034000e2621030030f4039044039000c0340c80156003405a000c1c0c502a03000c29585d40ca45800081c1c2668080f07582c04202030b1002051186840d000c29240c14078500079105550184840c0040000d0b24103070005402c0c807031080c041400c00407001e0720b17000d0480c0c105070800d40c08a056a002c01040e14001c0c03030603641d1844112800c0145007419403413001c1889000346800310106c4003090691003046a1030040759180e038000c01065441d900c03800014400480040d040b50a0b805100c0401e4132802c05000340d441d0741000e179005509150101071140060303c043c60300c00180c854644001c18020ba44182c0104e00da43c034000000c101810480c01620131034520320ba082d900c541c603241c00c0c800f003841c000c0125440111905001d008007040c08001030100c0c0700d034251800e0713500d40002d02c0b210030030419009548100307015101089403194820030341740c40d110504090090301d40281000e00c00105010b081d480b0544029004500b000c0d121090502203910544003503416500106100341103150440c96405001014078110341 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 674554181 1250 674552931 674552933
    0x9180302060402040f020403080c0d0e030a050604500d09170f0f0106140d02220213061e0e0303030408070618030c1205030c0a110c0d0b0f13 62
    0x1d00ca20001e40020712560325188900501900b03038064070083c541121561b40e031410710004050780d074080c0d045c7c3c00c0081741110311540307440d10340400e04420140e04000548a20341d42d5560308008030044064601c1c4000d401c61894100a0070358800c904800c03801c0c0070500b2104900069200c03003402c00324000000742d00141284911660040260007220326880b000d490502c06101070605003914004010018410700c941c682c40c01c441500302e00304603036281c182e02101075040000c2c48800360010101135040003192010404404099400c07114142503032000500300464110683d40c0b9000f00d80c007400001e40c0340f540c100103411100ca00e812000e0300d94180340d040b5001da640465104e02001b0000303030003003c01007580000e0140a030010440d182c050340d2940309019180ca009081c00644c48803d44008a200185800b2680900c0c02c42c1c0c01000040c44caa0b0030948038000c00c507028003d154019805001c0c5003c142020b4554a50301000e041c81030360302032a107241800c82c1001d03124004018100120582c01840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 674555431 1250 674554181 674554183
    0x3210e03090a090b0f191a030f06010e0d08090f09070504030c0e0412080a0b09180f01141501170f1803040501050409020304061b02030c190b0106050703020708010e0709180302 77
    0x5c4421542a59541144a046006805400c1007544488000284003c0c0c0105044420340118410f0288680a0001c0c0c0c84007001181c0001c0040c0b400ca8000280e0031140b0301142c01000900100c03440141210494840580801c54000c010b0b141c503000328402080c00d00401600c11079040c05410b020142800919240d115640003010756050035051108200c08500541d10301e400089442d00090402d00c10341c04c0c003074543c4402d40e141c83c12070f802d68000ea0175111480790041c010b140070001c94000c2c58480d03440708080c5240d6131103400c6489060042d0034100002c43c0d031074015414801e8002c40c071401010f242030302d1400d02c40b01c0c40e41c0d0070b40c2c1c40e5041080300f030040e0707070f0820141c1d02603594580006803243e0302d900d0904000d01451148000180344d68400d000da03a83c2c00030003004a41580c206035461071500c07074251038814801c1c0000030714408801c0e00501100e0f2050780a0072042c1d000344122035001c0d42d65200a800c43d6040c60094055030000103042c810b40701280948004c080c1221859810910551402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 674556681 1250 674555431 674555449
    0xd0f2f011d0a120336051903080306180c0406020607080405060703021c0e0a030207090204030c03120201150e092a0f120114010e0906100303210e03090a090b 69
    0x3594108003d0400c02e0502c2080e80441624010a40800070702000f01d00c01c1d6548126203042090740326602005c03525041404003440030140c140601d000940c2159150045a00001c0c05103821822404400fa5484050002140902034a41c802070b42e460412400a051120092000b000c1c00b046009102c0064400036410340c3c402c405240c0141c86544840c01201c10030303a1110490100c90410b40110304220300802c2c2d04020700e00c2502194205681e40c100f42d82603000342e01c0040c04400800c07400b00045200c02565046c1c8450700d20000400300003a8500c03000c8088160060032140387d0711400c011680030b0070806003d0382c850b120a0500800e02d1981000515401502c80c03900845100301101100e8607448a4606440500030090091100d910508621070f2001d00c1022482000706000c80c11141000c58503a02480c010600080b405013107403001d40700c409101c80051804a010101441d802c4000d110350240c0e110300c800034540d40d0070390408022100042d0740003003003054a44080220265603102c24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 674557931 1250 674556681 674556689
    0xd0c091706010b1b010603120203030a0c020d121808070515150901050d050a05010524060405030304050d08040b07030c030e03060f061009090c030605010f0e0d0f2f011d0a 75
    0x2e5842104980013140380940010740c0000c003e29400c0c6e010402c0d4030b8010000d0741c4a06e250f132200704004005c1003c201d07911480c03403078402d010480c0e0250b003011130f00315601709483e240102480b04000304140c2e40c03602d0709a4415001600c8580103428403182c0020b9002d845a0800051842d152030300f612180064100c0c00c044c81540e02c5a682c000f820b204008051100c800c02a4010001b00104c1c030b0100d030300501404800404080e140344880c2d0ba081c0c280307021f02c01d460a80e07e020300258103090816041c80101005160243e6840106010004001042000405429209a481c20304910b074600e0003900303804c86000a584a5000003007001598614040020752051044404005a20003d1400c2d107500c201038212105190412036203900b06a00358101400f200d100f030b40d45444100108000312403005a003600f40c0e500c003601d841d001c004a00e0310341f4210807803070003502038010220b000701c0690119001b518006450304a40d1454282c10344c0c001140201c1d2603010b81c1c1c045403400c1e00c0c2e80054082c0d03000b406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 674559181 1250 674557931 674557957
    0x1710050a0b0d0b0d0c0503161d0910020d02120a09020d0201080c0f03090a120c0c05010f091211040e0106030206160c030c060806100f0507170d0c091706010b 69
    0xb907851040034040c0c005800140004c4c220080005450500408803907080c01080d0192140302840170489055103a800121850300f600c03880361500040020304081405000c41070b0707030310402d02c1e81d036080c00141c4005c1c10200300d84500165901c00c03200d00f888000b100200214500b62510741014096110043c0e4a0040e0b50309103054400c039650840104624040c01051346403101008c0108242c070342c4001903440003540200c070075112181c4a0102124180c48140004100c020103100410195014034145110011170f07040071030603a80c40d40507640b140c40544500f9030f5101140781c0c5400040c00d05100380c001029880c0000d001e661705603000b2650070b208420348502594260141001481002d0400c44065070388a03550499051766038400400d41a42920058800c0d918902c821540700c0c003c404210b1504d0341c60f1600c0b4100145500e030401054106082c070f01081d0420844080150240d00c181d203408600d98480180707140c202440d42c00c5903e03000d83c908203240d100400610841201c20165032405500f00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 674560431 1250 674559181 674559187
    0x60a17040302071805090609030c03070b060a030b040b070e040606021902060408030a02150f15010503060112050c0c1002030c0403080f0705030d0f05070c0c050d0309151710050a0b 79
    0x1c6412864614140e10009400a100e503900c441c8489079004240907480b408101d07680d80e140d050a0517102c1c4141c2e02104a01c0c0e00400a0400155594000c5640080010b061382c0300660b40f41c0300c001e150081107504451040044c401c1000790b82e0015005261004240d504200c800e041000203559002e5856078150000d4508100004640e1200301f100c02130009182681d031122645103020396100201d00407181c10780d8002f40010008641d0341d02c2c4903c902201c148131b007040618000190342a41c00504843d0401171860041907048400740a894011845600410b41e03c05881b501c50381810000300624888500420a00c10503160484c01c5e0744c00e503038100c0d044aa468141c07150188061003034880062183c00081540314400007540e00c09a1480c0d100d080038050f90b910107030308071105030744204000c241180d0002d0501140c18052040c41843c0d01c40d08000441c2521041c45100b4007254041150000d4241c0f0b100d20a10756022880b25088405d28592020250a100c001000501c4600511072940004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 674561681 1250 674560431 674560433
    0x20d05102a08190f0b030a0b04050d0804120c05011503050d0f020f060609060112050c090f060c0a0809010903062a090609060c0c150806040e03041a07050c030f010204080c060a1704 79
    0x17a441603802e6080203040328282e08240c90203840c46901124141e50320300920381055003050184482c5d620503640612040e4050300000c0c01690a0f2010142c02d0702c2c50740da03440e4815600c9181801402c090760040300104025040708100610103040401d1000454004030004054280c0000700c00e0b400c04000ca4003142076958810049584014007041c0100b03e42c00c00040c4004080680c00070b202070782d01910300c804400800801d110551098000c2c0c0d041da0780c402018500401c480c070010700042d400501d004005503560303494050989811124100c1c83e803020b840c4108000700101c205607440496401c2c1448460300e030030760251600c4614031a450510154110300001c100580507414090b24800020094918204c44001d01c0c48400301c44050155150040c00c0001d50000810b65040310800000d00300070301c24141007844160054a0100c445100344a41e070b03056543d0510400450120140c0010b844030300e400328851030080c144031034074080d410400041c40f15650100c528240c50503480d048828988075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 674562931 1250 674561681 674561711
    0x204090807020d0809150403050316060f0e1c03181203060b03071110060b09060c030712110601090501060507201e0112110403020d05102a0819 63
    0x921000940c40307001e43c0b10880c104100030001d0040c519050b0b031840d10502d6041d2104c0c0703452190307001c0a04280d0003401000303201402c03003841c0440588258400b090001e61000302800740d8003042c2440c84aa0003040c481d800703107070218a802880306e403180380034018801c0001264071504501c40b00a0121444400b44512140c000d030001b0004040d1020b0603952071800500c0200140d0100f04450024040c942c60b84144030494040d0b201602e01d0301d24080d1901a200782044400e40c40701105011a00050004001207000260710048606240e111009a008203814681c00e15105070401710401d46814014404c440c2e1010075a0845980074656400c03840d4080107800c030b0801c1c0740f4440c641c0304000c856414103210b420a40c1c01041c0c842170321210104d583c04420002030724148800d15555103000d10040001d4a40a142020500c0c000c500340d41c1c0b4184958032010950745501c811009440440e40031095400d41c80e0f280044184062070305401030704001d01200c0c0d00308100305118104a44849406c03c1b2103807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 674564181 1250 674562931 674562937
    0x140d05030a0c300c1a100e0609090d0c030207081015170316060b03160f0f1a0f0c12121302010f0f030e0703060e0106300f060e150105041802040908 65
    0x251900d10b83d0340a01c6c0c140c4443c4030140e00d601407a82d603026007502007045170400016103402003c1200280c80b00010855040b9014612408143e04500c105100011b10707200c00e10404203000d030b82c80400304811001c10485201c203c81c0307034000700710482c10a1541c00c1d224408400d40d15800d048078140c4480c00e03c1410840060010541096810b0180000f400040401d44407013008031607036082241d03421035855440b001881040d114480070707004840d8011071042c07004002043c14041340300c032a80c14900c41042840c80c054417084100d001d00c43c009401a4031004c1520070b154040741c4506c00301890449036000800254160800405002c100c0c200d045c416400f035041421000c004204651102d03582c3d08128008d4035125030f5400481d4079004c40460340da00c0600f01003000e000e08580d0350fa2214216200581c4c04e048100003074560802c00c2155900007401030042d0707039114010500801c1c0035100e140d40c1503080401a0700c9144035518155410414980b1110b41406180d0100c0d000a4400e00d02d00b00070030284 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 674565431 1250 674564181 674564213
    0x13219090f091205160f080c03030a09060f0209060a08090f0a0503090901120201020a08071506080d030608010204121103030c030a0f02010e0a0309140d05030a0c300c 73
    0x2504142a140c0e04076016844400c000f8080c20284000c60581c010a84940c81103480c070039101a050300061000c03940030664484039511501101d442d02003a410910704642043d140d51943e55192544013045c80118050342c083c0c08468074045203007950b0a00003803043c1c070a0b400c0c0a070074442c2c40310009090050901c00300094140c4031060311416405031801c20344a0b480710138200c0c0728001d41c000104440c401d030b0005019856045e00100f40b41c03102900d4110564101c034604507142201840b0394003440305113000b07d03801403000c400200503646104001400340d5506400c5500542e1043c0400c200c014201040c1a0700c40d60000105155295034030042801e5119505810080f4840041c9008041d075001c004004c51500542c001c001050680701d400d9212803003c0006070005e44480c60502c128286c65000c0d2000030b000a0400006000aa0f2620309607004a1007120120700c000d0040400d04c808621858a4894030180307805285004810341c00880043c1c90702c0760100315251103040e00301722220754146500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 674566681 1250 674565431 674565449
    0xe13020316030b010902130b072a0303110c030705010e06090a060c02030f0109020907080a1401060f020c2b0201090b220b0a0e040b0a030b0906013219 66
    0x440d402007205580e8101c61104982e00d0000500006100341c091007607c840388400ca0346001000d2810040a511745c00501069031070b40c0207078150402d50401c50414030b402e0600c41101199051039410017600110080c0c3c000e00b41908041a0b1000c80d580105042c400d42d0000d0a1040c203030b1340da24020401c1c0d80a0180020f8104020032804a0b0407904a8085410076100300c1c203c50f0704240c1c0da02010309840d81a41d000307410000b01804108014020140d80d503020342d00740d1002034003203598a00508901400e82c400c6000c90020710096800307550501c01da11240b001581c0b101e001801011100342c8821905840000c80c51a03543c4a00031607116106102c0101103114101d82c0b1402c01c00310b00a910041240f41510040c10740000103406207020050314400102510307074080c120b9405060001600c0a18011644041030305c002000141521009034090f4041000134078071581014004074030340360801c55502c0c4001e2215103110641801240e44403102509031482e1801910401c42c82060758183c1c1c000d035080d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 674567931 1250 674566681 674566693
    0x20922020408100b1516060207110405070f080a0606080f0a060b04082a0f0919090803100803030417090120010506030c011115091e15011a03010e130203 67
    0x2110182c00421310203104607060364083c1c455810803045445102400400072084100c03c6002c81e00036401350000c02d00620b848001c0440c0d0030001000c448040f42c8880112b6407903211035045a0703014410310b0340000c180038100003170b5007080300c05070054100410120714115410000750000758207401c01c40040c2940f414058655844200745511080078203c072950100390007420715080c0395569290689002d000e06160302d0403040070b0074812180340051484240040c9811241c118003801e216001e0342c00e0117884200c3d16400c0101c10b1f9181040c00d6405020a5403062040c800450b0618540c07204803400021140d0b640d6403c240180c4441f4000e034025107400d00184010340e803221041d040b446c440c42c021000e560b1199684c0005441000da19803200e00594070110314150b08031600c40e10036400040081c200d98510101c4030880388030032400c5800d03442e160003072042da01e07804030640f5107103016010201504030060500c81c3c06c0c40c0140414452a2803200010b000701d0f642030700b0600800a400c2d009010f0b21340d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 674569181 1250 674567931 674567953
    0x105040311180c0406020f030301050120010603080a050702240316090b030f07030c02010c14180a1d0108150a09030c0c030c140109030f03030c1101050a1e020922020408 74
    0x10f56500180306805c00b5014031003001806c1480841202c2c160390058548803010246000404030718100142282c40c990360355000400440c2c0c2d48005010003020a503501035890f0050701c18441e6000c81c0101d002c0030032040341c803180e650b00a2202541d03030225101c108007078000119082203480c07003c00e5000d41c0300d0301000401d1143d034444c2c111004d4801c44080d00c061100742201d440803800c80c3c1c01503d6050000301300c0d03641031340344061400080c47e100a0015400741300c1001040002c0d440007442d070000f448080c040140381800080071030301c0ea00422104000d45a0300031450b0004801900060040858946d900c4030102094060045c15a40c55000714250f02e42d141c136450f113040005e00c24040c200065090710014099580b0031f1100300286c1e5030044041c81d81c40c50566040d07024015040c0b1990038000d64481d9051a00001d20905110700303614a07010400c2c2481502c0200b466400b08000420f890040280740b038162250302200c56004054681843c4541ca81c2c0c040384000e0003207422074202805a039400350 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 674570431 1250 674569181 674569201
    0x40b1b0706020d0b031506090901021c020c01050924130f060605120a03053c040f060e031e010e1501080c030703170307030b0933010504031118 63
    0x10f12031a01e660030400751506a040640d00c684015002620841810018040b81044500f42d074103d452030b000035007041590a10301d45c2d164000314004d60100c2d80803401401500e02400f5850304968204050282004111003ca40030900d03407061200884101c80818900386c900d441c81c5500f82d411000c144141d898031325141014090038402e0610506010502021010300030400300b10980d80360700d0301883c0000719075907484e10303051030790662031010b500c015211000303d004611100e84039100d200e0682e07138600f40140c9204100741504024200003c02458120b191400110005402c0d102440001441444139206014041036446078205020304030380e0040c403106900ca00d5058414090a0f80c160740b06d500103040d991489440060300090610800000c0501c20034015508073b0207524000c198038840d03501082d010541619003004100000c01d1608040300c5100e4081ca10000204000d1344400502c40002d010f406070f40805000001821401d54141d6969408500c5c1d20b1055440801c0b03a250103940c070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 674571681 1250 674570431 674570437
    0xc2c0d060618050f010b12090a08070c03050601060203090f090a0609061401030f0203060604062015160c050c01031d1603150b10080c0c06010b03010f0f030b040b1b070602 75
    0x201c151103041c0320104040c480c0c20140c9034181c403106c000c1c2c541000074402c01145408406441004c0900607100c0c0c02300810310007801854224000e5282d0110701d4514608140f505d0416400b440454005003d0302c0403555402002690004044a42d40d0007500c503280c03070034001c1200340c0c48000d407030740742c03080000d00380509079001e034036000090328100521100c41c000c0406074401110300c0e5900580403c030601c40c940c003904543d80c500c0c891403035a44110280d0f03070500d80392401c4007840d250208001d6040003d035a16491051402c0003880c0340c80201c0500300e03a1140d40d510500c10540d8141a210b008000541c0390800341c0e0401d101c01d2604445440d0311804500e080d82c0c206000c1551030f4640303c041da20004070140100c508041c4043e10b0442407041000085a4208000d00303101c3c042c801c01c01500040c108200031190203484040716959403035141117000c414825650b404580000d21008007000841c811409881e40075070045031726140e603611498641c80158244955020100303000c15624240102c42d400303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 674572931 1250 674571681 674571719
    0xc02010b03120301030b01051203120907091a031b01020f010603120e0613151101020d0b24120c040e040308010f0e0402060d1a220c2c0d0606 62
    0x207445140d042c92600302101c1c442400301804042e07460004010fa420b068078540e27040c01041096034200201d0007070440d50400c003901c400f04183d00200d018080c0c40298407400c4070060301010805050060203020a03240c10802c3e08240d180c030540e14510125034000c0c820302c140380900000800600f512850725084005031800035000154821100107150300f080070440b03a08140c00c44950386007901d0501110a440c284200c16000c0003051440f40e8140c01d000d0002d84103210046a0205503a04150f046c003560395042409040c0455184038880808255001100e156044d10862550941d84903111460184101c2d449080310f414184100400d059011030464181c400603881c13242c10070341c0d91504450100040d1000b0390b100c84100452001648240c0c00303641d6500481519050141c00c84002840f01c000c0401620b00008004400c501c01c89014400c94860310082e080003001944a0743d6400f8580403008000368650501e11032159056030303650740001c0b1095201314144110b584829680f1500060030350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 674574181 1250 674572931 674572933
    0xd170a0503041e150902040b04060b030f1b04060804140a08030f01050301020a09091503020319020f0603040c03030503190501060f032a0e12070602030c0d08010b1605100c02010b03 79
    0x4030b00d803c807010104190003400d0300324000e41c0140c0c090620440c024017219500b2a4062340c0c4540c080c606807220701601005080c007408aa0300c0e8501500c070880800e034001c1c0010100d5045044000d81e11803040306803010b9034030629200c8000e68903417600b510b03000c1c1d5402c9000c0c540c0c401e40fa002810004040c001790700ca200701c0c007602403040e42c2e18000d00d400d03070003000320b1000070401041c018030018000d175021001140720084c075041c0c4280c0e60b0300828217200c1045442c8001e911004504015410980c0a15101c00410b8030100d14502e4152500c2d1400240341c080101003001c00000700b104000032281550640402d02020407655a65480151020160f40ca0b1314020a082405040400300429968865049003140c04400741c00ca441085034a034440e01c0768a030b80140798880390f0101302c800300802000340042e60005c5590f9041880e078036140a5906910b1801c22850b1001071040b140380e0783c141c5054107480e642d00c0c200c0c407601e803a00030b0811825110124030240780116030540564150018010075030150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 674575431 1250 674574181 674574203
    0xf150602030f0315061b0d030c0c0b1302010c0503030f060109120c09180c08070905090d0f080a020c0f07150f0c02150915030a06140d020d170a050304 66
    0x11400340e0712401002e440d1103800800b840080d01050300b503c01039100c403000800c1e0318580306800b100e56029010202031900f285d400310411800503609403045a0f01201142001113190905d42d035044054000100710f40303503c0310380380c00140c00c40e401280414607080e840300c02d5944901e480c00ca1038100c101d0891303a45000409a0100150140ca404520f25403540c00c080101f034114105400c10028040e412104051406e0140105000c01c0c401e25400001d81100e1016018880c501103144080d154060711000d00c0e504400b040340b000da504154558816000c2d400c02c410140d6130b420002000303002d0100030765454003d100303504020f0100402e034481a103901c40e1115050702000c01c1c0846140e4041d10703e40022070700031104200075180203120200c141d10100c0c9990315000c102408202c100f030400c1c410350003201d00070090003401001d9005071405010746001c1100c8859055001504200c690301010740180856030a04080c80401c02c40200d80c404010303c2259100342d81c1c08010710f140d2085038151074a841c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 674576681 1250 674575431 674575439
    0x1912021005041511040b04090f1b02060f0c090402070b07080a0509071e080106080a11040b0604120c05090112021206152704081b0705220f0f15 63
    0x41c46900c1c09560802c90040080e10042c500d00004d04035001e0b0243d1130002844005446031001000b8006004150720102c0c40400d2044d449007a14045012801c0303408501c010f200a0310f07030019000303a0004828805a8540d01d6a03403804411384034004c902038200c0c1c0000385a00078840707441c60143c0682c082c4e075659115960740741c05501c11140265082082ca4010722400c220b00319007001c62a02c00d003042c0d0a00368a440c3c0c1c03240128211215944004d0710384e04042c0e104024084200d032071040e5135005903014082c07045a10300207a41c910440c014061208a0134070100c00303002e07032000341030003078803019201b1384955843d100814004400c2c2c010491044000c00340b0100c2e6010301159540c042c3e00950340002001b0881d90030400d1000300001000380e03000c2d040700c0400c03007a0102101e032400b5034000e055541c1d964081e07041d48603181c2d50112121107180d010140070041c80d1110b00c12040440d102806451381e5244041e0300a010f05080c00c0d034201f0740d50401c074281e84500c009038070001d030012203408056107403555 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 674577931 1250 674576681 674576713
    0x509011b1709060906070b01030b010803040321020a060f0b19121e06090803010e07020328170a0b030c010207141e120d021207050a060b03191202 64
    0x114500802150700440700d0401d0014901c05041c441c0d0008084500344115030011495582088401343d4010b88001c00400c28440c000c8000760142116074003a528040c11519203045070701603c0c540441f11300040310040e010500c01d20206490780d50088080c411070704030f0680100a07104440006114100712000d2180c8001500e400c20100c800300c1d00031a1820000d80c441c1900199401d075004400c84a52041e200040c081d4401c16803058811100e07680c503541400104901e00d400100000195802085070f0045d42d1042c0f1250665503024200c401c3c0e00a016650854103d0180300048240311012800d1008000e80d88d044100000402d40449040068500c012a41d074541c0c2d214010342c4006441e902d0f201400d00d80703030f0001c0822080200c408900e5408001c150201e00a40c0c18603803076007040f15201c0030160f0600c060603070100c07040d03540350910034980c840540720030501e01c004141b0b41ea58501d101c0c09403414095803a54180c03c600e0101104841e04040d4400a08000c03404012b0051000031501c20304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 674579181 1250 674577931 674577977
    0x270a1e3f170c0904060503030d14060a06080402150d0f20040b031306090209070c03031508151005090108100e01051009051b0c0d0e09060d03140d0903050901 69
    0x6103030855086552100c0e80071503100d40c4241003c0d034016880d0600490180c8080000b03001840d03260500041410300708510800581000d415148110740b804410400c031030344010810340080d0110381c4a0301ca4008001c000d0114811202d5109201e400d04d50ba02034288295808480c107500e031a40c2d0460041c0da000c40d80c0d44544218003554640c01e0091010840c28580768054038071951098100050300b03541030700040c0300704030201c0e040400a0000380000c4201a03050103250b1449e0b60780b0704140c3e1a40d0030300440b251a04038600e041d11070780c4620400200f44040d00c0030040003c101c01361610701f05584841c80e00ea1a418034802958407281031600d6803c800405120390303403282c190511502e6029041000010140201502c89601c4080c061b041151104124008040c4641c004005120301d031100003018088040322201d0512800b24001040010f84a01161602c815454a008030a4541c070891030102030140b04e00c102d01951410044104254002001f40304044090302c0f0020600001000f030000070fa = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 674580431 1250 674579181 674579207
    0x2502010c09150915020709060b0417010501030209070e0604051801030506010e1314030c060a050105130203090309010c0c080703320a02060306011205270a1e3f 70
    0x8095240400c110902d0341001302c00440648107075610181c0c0d4007100801c0d01d2480e041401600d1000030204660006408402c1180c07850900a200ca17600d142c0015503040d07402024038040c0710740c0c0c0c40b14400681e07865080700e0103040d000308484032000d104200310941d000709000480c2c01d449140008a403a0b100e02c0c04440c450107101d00700900040e12a03551400805500c401741a0300d1105201d080b071703032039002d0100303a204010488001910398034010401015040700245410000e10420900c5010680030044a807482e50a00307028000e0b840b54940040e074000994042504d40c01040d4003c410040b142c204504207100813011091160048036546402da02259021551548044280c0d40142403080c091940020705050900b00160000c84690950324100c83c150603510324444070486000b0703490f0f09000403241500007030800c0246a61201c40c03298454038030a40c500c402030800d204120700160f00d08030600140741c01031018101c80e514145001181c4c50b0403404610504421482140310b095456504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 674581681 1250 674580431 674580437
    0x6060f0613260607030c030c051c09052803030501050a21140a0c05030709022b110f0a030b090c0703030203090304031b080c1e04052502010c0915 64
    0x81d49012040d00c90750300c41c00b801c1400c00158501c0d084000606005440c40303880243c802040e112074174a0000e08a46d032560480041c0035013030061602442d0310010007c400060380000142c120114180549060707032801801c44d626068480034601452010079070000d440c8031f9141030080ba41c80388100266040d560181c05242900d554090313907a04820400802da40b03014246024910840710a0b840c201040c6d2403082e10008014081000141001c100400c0140b035071010031402c0805980d008101c264030341290b0f002403828025481c69080050340491880c5014109080d922a5950304440081d0807403009400800c0c0340400b1507080d42000d51441d41700d0481400300f58608001640c041d0003d4001800c100107520040c0001301c000b03291f0300080c0d02503030080e0380407691403441c2c00c812030300e0030f208074019a009062041e126a132001c901030241c00310090407503000c40ca950701c0d0402161600c2030302c00c0c8404000e444030480c0880310340640c09065071840d1692040c5e82c02d0b440d240d8103103015040340c445c9800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 674582931 1250 674581681 674581717
    0x6120212061c0b0117070905070e21060a0501031208010b0307051e1204260406030c0c0213050106120b060703080603032b050105010f02071a12010806060f06 69
    0x42e1504809001030b403081040306101c2c01d60281c56092480b102608010306180d9115a85007800004010030700041c03802c40b00900062411070401048030a0580f9010b0003003200049005071149030341c42584e01a4900130850f585443c0050801018290a100949a103202c005d0180c803079520416100d07058414100c561851521010021141c40e8011620ba56405948500c0e18850250030001050b0300b0252040c521650301f4941040c41000c0164941c0f44e0151000c11090f0f403921100d4010354044400d507050006450680c1d420648001d1092580294403141c03c2540d4408007846510450584440c3c2c1d60342000001030b441810212100003440c00e5000b03105105a03170003e44142c0c85950b000202400f82c80c01c080c10346641c1100303a90003141d80f4510305050b061003544c0c1c5005214050050909190441c0c3e44280f0749006922140103005001407111000d407c1c050080d03580040703030348003143c20605440350341c0e48843c0241c85400507030b900c600c070380c1902c0c0c02c0302c0c7d071858110f050341c14030501c1c4003109030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 674584181 1250 674582931 674582941
    0x304020a0e0c1b0c01020705030f06010317041e06020d03090b1501030204031424161d0d0602090a060c021503130b15102a06090b040c06120212 63
    0xc0c0104014035040045204100080604043c90b00e03504420364000300920555001c2e20001e418a20660070440c080e80c4851054041c403440002c1d80ca045a400c5260419506031903402c0c2d811034030a40c1c005920200040032a001e950781302e86805d83c00c0314416070a85032169500c680460a454001c01c0143c09091400049801c01c0741e440d01d014945101410014a001c0d966070b40c480a802250f4080d007141e03006203107800800840008005c07003c2c0889440da01d80c1c2c2c5010510049910010340c040e408004941d44000d00c400b184000a88011340d0041504c601c6800b185450f0010390f0201518a010700e0919100094440c041e880301d0320101c0e4000c02116a95042c2c1d40c0c44002500001d03c08501c40030039041c4000890760350902c03180580404441900181c1201d005c2c00181ea4554510300100724083c01c0250810141d9026000241c0380003c644000e545c00c0e00740a00584112100030382414400310a11082214a074403035811200151034640c00c1070800440042240200700e46005080b10040002e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 674585431 1250 674584181 674584199
    0xc05031303030216051609060608040f0323040b0d06140a15030b0d0804030b0619090902030a1a0108060108070509010308090418060e0f010203040f0b0723030a0c03020304020a 77
    0x10030300c003403c444820907009803140307882c003c0345030601207200041c11401d014500c80c0f402342c90083d100b242001c0c1d13202d080071340d244049042120409800c00006005201d44180078a000105400310003078070a440e81e4907440c003c100c80c4d010210b482680780c40c104000030381050841054841081c010034010000e85440f00078240250b408452508151780c3e407510b00629034503400340340300060007610700e2a182c0d800d40c0350460519001420161258103180c041012207241c03030030369070180c6003170300408214500f291011a15046103400c00405194005010110039042d003001e482c12101881c1c12500180d80e1401c466440d01c4550140304d80048001c00140003140451008122100d005070001030010000003400840c84001902290643c0d02e445581c0070900c07007040924180c4101000031455818141d5480300c80b98680c602c0100300031101d0f00006e140350f0140440f01c09110701c80c2480d04c6403031106010746c600b1383c1c011524500501d14010540700381ea0700c80d1003943c3c0302e568050603c0c0e1021341071910324 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 674586681 1250 674585431 674585437
    0x20708010621140f0a030314040b16020c1f08010b040e07140408160509100819061409210301060e09150301181109040f03030e010603020d050a02040c050313030302 72
    0x380c0d460100c0c0f034030410014100700880c16805141101801e0140200e00d40101902c111141a25440082c0c40c203100201c6c80c00703810260401200c01c04203411203100c80082c0c0c180f1840702041ca902103a0700b01741810060008294584014280da07403003415a8840c11000c0c680d005601071410106ca0040c00282114001d04105000c5801030080b14203103582c0d1004240380804418101448510501003046942003142080d504070704c010388051105410121000e07510010b0140866004078510703041c2040c056107074040501e030210391b02206011b28081c92155a2101c0003502c8601c000008101c8103849072181061340d041e6036480e990200c0c40c20b40d01c02000a0005c0c003034908044641d20440f54801c03507500f40321300003c41e40b03a4808c0c060008900d041503602c220214070741500401d405801c00c00000c0c00000c10352446030b450b040000d048001080041e0041040c0d400080d003210000e2000c1090060001c0c00f1000c90307108440510055200c94412a05404207039000100e0300d46a00081000174040d03005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 674587931 1250 674586681 674586683
    0x5030705070c150c05011a031002070f02060714070803070210030b0a0f081501080c09220209041a061e0d061104060906170402010e0603060f04051501020708010621 72
    0x85025010303202c03551002c48070b03a00d0003800007052904940d04c081020030300440c0700181861800c40341100c90304010a0316039000e030b00c0c0c0c40015540007440da400c001c51001400d0100d500a803000341c5448071032916202c041c400440741e55080c4201f0720001040c04c3d000040300c2c0e0060340038256a080c00c4c004003060780900b00c003110903075014120081c04030b14014581c1c8160010070100004061b03082400c801c010150074180c108a900380c10003038801c6690380322540b003140c0110400341c81c8079000216a4042c860b20080d600003d6200c00a0307400e21007072003801c2880e80001e03000c0115194145c1c840d40200443c940203181a003400c2c1c039042202e0112442c0006010400364064031002c6205040024444400d0340a500804d01113010803c06100d9242c2c08030f1204a41c1c230aa0480a0b010300f448c2d0000381c8035090811442e03100d03400020028140b0b0f01c50b01001c0c148464003070410f001a080060000114101104590b40184540c140004018505000300c900300d0301031550b60051450080c003095280c00c04107078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 674589181 1250 674587931 674587943
    0xf040b0103020c0105091606110307030f02070b070c050a0b1305040b0409062306030607120519090501050a1109180a0e120301030203060a050105010516111c1a01060503070507 77
    0x4416840c0c120f083c0246403084070800c001d00a55041c490003030304141e81da0341114081240200d070401d50014000110f0700300d01d40500b000c40ca0320501c14002c9291840c80e8000b03c03280e0f84042221000c0144070220881501c9080314048030464540c818600940107a00410340d441c10541010420380c05d1507800400380ca00080e00110b015141511064140e031200382c040305418044481b030040700c800780c105890304410218003910712030400e040c0007044454984088011150394038003042290000c07c452500c0c2182000c418400381c0e0303880c01c1c014000c1c0310440e03681d13803000d04101c01c101c0701c0d00400048a800880040c4245104502030402444518005024808150b5603054484a8107000c110300b0102c0c80c148001c8681d29810b510500d828a1009054001528141401401107030b81040c2620140040105842e905280f503041404c40c010700c1041c9150000d450001700e8090882c0011014003990080d180c02000002040072954408024030a0200084044c401309518074402e00c010003540b400f900c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 674590431 1250 674589181 674589187
    0x170f04120f0216140907030b090109151701050a0e0f1504080d02070c15021c05030405011127090402280e07030504060e0715120f0f27020f040b010302 66
    0x140030f020030b40c91150484200400c0d900d03055400c0349000202d40b54041080d14041c80401c20342d4012481c558018000c100350f1a84684151070b0315880c0222007130050215908503500501c04c002110300811041c0e92400c1458200520500304e0100040c500c40b41d00d0001000b0a040c1040c44800340f02c07180d02a0007111188001c00c0316117881c00e120b0020f4001180207180b0000d00c140303005072110707015900d12042015500f000f131400d6004407405001544000707c07400d1503566913445240c6540142116000c28500d004045008181c20488920301840407103a000d00900c5600b000d0100b204200d4202d4000703511844400140072000742d0014114020441500c20040c078030b071140300d030000062049400e000026915420441404464010f00403008a20009001c2d501d040c800c262042900d0f4080300c5040c07000360300c020700c04008140d00160802004140820040300c0b1200d8a8002c0c006103500d1000c0401010400006480b1030822800c1176a030003081c4081701d95402c0140030280c440a081c1a0505500b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 674591681 1250 674590431 674590453
    0xf011d0111030f04052403040f020f04090c050f0102120412050a0b0a0c030b040209010f03110717191b290a09170c060a050402040e030a170f04120f02 66
    0x400160003c460001102c03a115800c0ca01488480800c031164544c0310390f41030160910054062080f2034009400c00e21043d1003e416001085002c0200d142554004d807810701d840e02030001c4c040c802001d039041220b0030b1071041580c000480c1d0354000c03081c0d42c0100c0f5a0030031080001c0345d0030040728030325984524199010b6020a40761107031409030860b90582d840d61074038006c42d100d562512482e000620208c9003142003500f5403000a2000307034000102000e00d96541a1900d90070740c041c05860700141d1002000c60b030300f0510320403145207030003038040000c800309007150f0a401c0c20b01800e44201407520b1115001e4005a4a071030f822048105d0324052440e2411510306400f419105030462407045100100c0411003c51a00d0694000b408200c102040c1a4061002070320104003c1611900a2501d000125061702d607800004c000740b1100c1c01109481c03100003118428541c100c621415100e080340e901024a50360102030f040058403c0b9001451000c130710407101d40c1e06000e12400055000c842c8115072191800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 674592931 1250 674591681 674591683
    0x4090b0109180e0d1103160602040f0b09040c0e0d0b04020a15080603100b011b1406040f031b02060706051b040f031b050f101b11040b0f011d0111 64
    0xb2460300d403a616881c2e00c1a89031160301040000240c02261030800854403003100d9541e240d010300d0404407840e01c150f007901c006014040c1c040c2c0740604040d4591210355650f4807102d602036409420300130301440c00d281103042e0040c0500e200300c3e54070602802031401401c8a542d052100000100220f9000b01611401310701143c00c20f005440c001025207074102e150504c8030405140c421007c1104002504041032000c41d41da105040660f0348202c2210b00e00c0070016403034101c941585030800c90b0701c0b40c45075500700701c1400541140010070301e0007904c80d981400079038244800080d000400107500008200107502c0022080d82c001070b84400713080c0309128025440201140980d000d9488180120b1a50b1014014848400051204420a80900b4505900e048040742603408460040741c851900c06080fa4012400b90381100449110f01c40d0319010b4541c6883c040d03000c030500300c445038000c0f860107524502d80c0c184103100b0440600c0c140c490411419007101101c0314040300d9015907042284075010030301507800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 674594181 1250 674592931 674592959
    0x213021909170f1209040603080a020c092a030601030905070305060910020c0c040c051303031706041a040506040b03030c0d081f1401031409010501031203020a0504090b0109 76
    0x80c60381d00d000400c2d15001d40e50000c11802e00842840f41c01c030040ca55806040003038007004101c030340304e115610303144801d00080040c8980d51019011041c0004e00c1d03030702c09501203943c0340040d004450310780254561543e40841c4141c40d484c140e0b100188500801e50900d041005551b101005150100c1c02c074859035074030b604241e06540111059401482800b007042c01c18081140c41d1007000004609107407042c0d1403d42d9851002004074005c03a5555190036445104000700c2d14030f01d940648102e6070582c0c9280c001c005100140f500c1c140c0c40b07245008509507151a000b0240e0003d240c186442c070000740402008020500504030360b6006560341c101112688052000d031a811082101800c00305200c2003025200704c40c02040300c0c02c030440071403a01d8103401516800c0c5007581c0c040c8440303090320480c600c016402801c600c40101c0030b03141c0901c100016a40150005816284903906078842892013030010f40c01d1340070305103490b00422810b12043c800b0407034540c05180200d10516108148550b038000110160b6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674595431 1250 674594181 674594227
    0x90d060507020c0f1809071512060909080304030e030c0a090218010305090a0602070512030108010c020c0102071d130b040309210309060810260709050f04021302 71
    0x1a10350301002a40d54051201281510703058a289500c0d422410000c3c01003514548440012a168004102c00000c00c10004000c0c24042400007440505220b003c0c00ca00400081c07592007501b0007501250a800c1802040e8005a10040392802e549a41e43c0c10780c0c214115100b070b15050701c6007003080705481e030380c81403564000c04120a005035600300b01c210080c0d6440780300074100c0c1030500300390502401000025190005c80c0e040200141c0312200ea1a00324101100c20071800c9a6080c08000803e1019040d03201c22000d5150f0b800304e0318542e07a04001a03840c0e007014807a401c0400c5e202c0110302107240980c0c9003140d02074840c06910401c140d50341d80d5040400000e9806030002412100140700304c0003030003106103c8440c0701002040d00300e050b9030024601005800307a5010408200c003c03032225000400220080e05503880c1102d90581403140811030411a004144003d200360040003c0c0240c00d0322480e4054142402c003039005507241d0702440070740030035501c10400c03980d400c00490400f0100f42512001c0c1c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 674596681 1250 674595431 674595443
    0xf1701060909061406040320041409010e0c0f0d020f0306130c0f05130b1804120207140d0206070507240806040b030715140c070602010606110601120206090d 69
    0x40782008030b004203c8183d900302c00001c00c002074460075aa80ca28080d074080300d40c8464600c1c01c2003159507080043d05040d420711600241421070160341040c0d1000d15034802c4000700020015a403041c82c03000d54030405002c58540041e00c0004003500d03802c10f546c003004814000341c29001c16850100210b4948901201c0110010500c0e2907071908101600520800404102d083c2040d46401d101c0080d0441c1045000008800e0369804152900d80b190712662200d03100c6800160f04600d03107400c20600d00c89400034407a00500032110042002d804001024194032405092488036115075824061300d036114a000361407600c260940010584018070380741400d001c131006041031a100b50302d00981140000741c50315106074200603504c08651800542101220004003095080d0500411b05a4280c3d003489a4194101d9000410300e40e00c0c40c0000e00762089800c0c0b64001c009055880b103080301c140801702d950300310700d4006000400030400c410740310400e00e500041c00d4500e0b1040e940001034960410b02c2c0100c1340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 674597931 1250 674596681 674596697
    0x60402030c01080106020312040f0605090f0d30110d0e1c050915041d01140d050303011a0d021b0c09090c01030e01230411010c11010f170106 62
    0x2103040500880070350781402c1c02c0030000f6504100002c1d49902a0100119007116001c000070140400031568000403900004204007509107000700907210403c9001201d0700384291000740c003200e03104441c098084c0d829945245201980310040700b0a080040d807078519030940b10036900c02004029401020904401f900026000b15214a00390030040c0022408441402261080c000240c0010486043c42c00445106100c0f520307401c24040240516040251400c001d4000f1550744485040450306039070204c882c0c90344450810f8200408120104002403264100340010440c0342c03001001c1000c0041e070b58076114241504400644126008990380d001e8450100d0000300f0711640520400c06016025500044245032448407540d80700308902a103810182d490119184445013035201030301151004441d0350003180ea500201c0700b0400b00ba14180c1c0d4a20000010040b1513002d800d03101d503c654080700c1203070b8240049006640c41000c00800200b4002c89228940700a090654018003030000e5442e5008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 674599181 1250 674597931 674597933
    0xb181302040806070210061d0c0a0210050a0204030c0e0402010e0d0c052e020a2018090109021002161208120a06090e010b0a09020a050415020c09070804020f0f0a170604 74
    0xa48146920900290414200c80001090702031000c99102c0b006103000c0740c0d21000c1d003c00706d240c00383340c100880b082c40c80d0500b8400c04015075001442228002e0440b0645c0686a0b00f103802031a0007a07900230301184100d0501e94060600e601c12214690142954018503540d440200b100411174842d4084200e8503e04080810341103102d004420144038801003e203400b40743c1c0c40340054811001c3c0c215000c0e441e0208034895685501044031003050111588102e41003500206001c2c00300703544101d11640d8034005102c0e015100090049420344000035100d19180b811000b1191040700314020365504c070040080d4003032151054000c6000781031104000402c0d5162003800c20890b591b0000d44a8140d04004000c031031643c90014038015100c046000580e1180420000c1c2d82c1481941c0c4408581b020f4120742242c0c4540201d5080f41c0008213a42e40170b06981d0300f031800c440c1010200d400941c0030b604804150403070b09181c0041100f071a0043c15000d8000d8a600072007030049054510707450242c1c01101004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 674600431 1250 674599181 674599213
    0x1506091b0201150501180f090f20160c151d0303040302090a02090301061a090102120f070f03261008010507021f0b0d08130b1813020408060702 63
    0x1030041041440208020501c0080c84601c9110510540b810081e500340c100f0032807a00f80c030030b03034008100e0f0031485114640c0e2940010041d00a283d0400c003040d04c0d02c030580c140380035203c00c0e40366411003100183c0d00d01161000758180310000302d00161102e5a815101013855210326540741c840c03110301d44441d1103407050514210942080940894026001808104010b8440b440304e150401c40c0d43c5000750b154450040424010072055101030700c084000c3c41601c4c103082d803140c01042059000e07402d40c0c001c40d5140d41d0042c00740c4516501c6140045003004075802040d02840111000b42c8203140480c040455882249030110100e0b0a0701045114a0306201c084010702202a008189010081c08180303080100a0b4403203140d020f00d403e10308102d109038644010305600241290750000c001219002d541e045c8070419801085882c0003200602101241c081800400d81c0c454451031108088203411540522217981c0b00c51104440b06502130001161007001402882d200d101d00b0707402000710611300500c035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 674601681 1250 674600431 674600471
    0x3040b010510050a0e1f0c1209050a0905070e060d0e1506210c0303030a0b1e090105040207020d140f0d09060905060703121506030e030301050d020409150609 69
    0x80c8280004002e407415a60008243c0d0740c1400030341000400480e4903004a41c031245003400752142c80c071511300110003050b084040c5030002405240048010851114103840d00300890240c5d991140c50035000300301a5019400c881da00280500c4c0c02c0c48041c801c140805c0d1903410040d03504840076111841c050740d0319410498410044100082c3c03810034140880410484030062032a441600c0f144070040703600201c200044881402c01800700d0f56a0720f07211142900506068800f1071080c3e462241d82280f070b2202d0441c6c054105d500500d07000141c0d182c003003000003d61101b403040b81c10485105c80d520201d5058002c101d40a980d00d0003414417500b182032044c1c10100d45211060038045805801d006460b8088038000c162442590300071342c0d0340c0c21810144da1381e140820802220f03900303000203580c0154011b0303080402c417010780d1410b016031501414000d032680024024603401c030300402d410b5005440e14ac2c2000d40c003e030080b403519011541030005039050b1754454110b034403100d0b150a40c202194101040b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 674602931 1250 674601681 674601689
    0xa0302062d18041e02030c0c120403110603091005060411040305070e0c04150c11030a05070302030d030e15040f050d21110307080a2903010c02210c0106031703040b01 73
    0xc100c1201107a4600d05544200e07851680a585c0c0400007131000f281c80012034050004032401ca80308000602c244c15803a5225000c202d5200e0040c181064503801c0c81406e07280121480310180441c00201400345e0014203000700082d500c15110841503001d61444002000603500840c0a040450f04041d0940d4242401800e80321507074038100401c02681070407107a110071030440361512106400d403a0512540c2a01d00c1000d0380d5150044c40720b1401040000a10101120310070740c16103500b07003030b440070540484900f2800540d8603040082d0201400e4a0302d03400b80e034024841d035044112007120781c4805280c24140040000840c190360f40411f214a2400140152040590010311603c400c4880c13129031808041c1c1410244403110307020426000041d006817189020582602c0c050707542190303c0403d035400d0464414000c0d442d224402c40680e10104020b00d440450315140c5031400c6c001d04050426078443c04d0600130a542e901d80100014842400544007501c01c42e8040340c40c2c0c00c00741402c200c41101a80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 674604181 1250 674602931 674602939
    0x50105060108190b030a0c0806100b0a09030204090507270b1009050103090317090a02210606060703090b040b0a020c0a05010f03020c1609140a0b0a0302062d18 70
    0x10070441610001c2d0f4055111002150340828064074070408286800d52060004140340121100842c0321040015203610942c08113911140441c3e5491600d299071007980c40d03603400110350307c40a00250816400c41400c05108800700d5100c250341ea00d01c4800201d9207841340fa03a813184007801040059803400f035642d1740c000c119490282e1608810010b04a0320ba280310351414140c50b40b58400500d03002e40780007800c16048250481c03980c50701c030b01c009858084060b8203e20420000c0c411440c2e00244002c000d66500711b5000a20030750300d504e801c2245513002900b08a04011103150040f0340100f29801800082c600081141d0712021000d00103418000800c11030703130107113421407820001c0703a90164420b00704200c2418016525000c00411509150042c01a003000000c070030400291000e040e807002140c10841c641c903c62a4403180b1003038042e6485542c240e0350041031401d00340054a4000300038090146480c042080c00d07003002030000381c81c51000100388089070000c90300d008045c403901c02d0756450020072a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 674605431 1250 674604181 674604197
    0x3040e101a040b04030b0c070507030303020a090e160818010204090504020a2c06030a050105090303010509010f03030507030806011101051302010908070509161103070b010f0b0a021027030c0501050601 88
    0x180c2c5000f034600a0303100c003a000010b02000300c5d09107890b04048a101c980c02005030f42c0c1003510b0b400d000e0701030343c862003064000400300000012415800d41c40035000f9140e4280c000305946242e242181c1030a009442c0070800c0c100090100c0040e43c091001700010003180c42c010a003450301e4010030001071021741c05801d544815016007510b107245001d000ba11501c103898405256100e21001c0707031601c1c0340107500804642c03a1005000e40507070b0010180d8100d4808688489090b0f80b90104006032032401e12001b4013140c010301075440020b000b50b443d00d0340844185004486c501c00c1c41002800d598064488040d10303003244a1100c00d550b4030030850f501610043c001400114070b4040820387c030b07040c0208410201059004a0000948514444614041414200c0b80c60f02402c4c02c050781100c0080c0300f600c0c420300282000040c110641c0d0140c680040e600d07009800c44000700d030151405802318170f0481c0c0310344c098040b80050300d41e00384000580310380c004d50310300c920103020b460190700311040944481c1c10b0107402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 674606681 1250 674605431 674605439
    0xf09050f06030c01082d190905030a0525030e010e01020c0a0b0f0c030309071e0e060402090a170a0302100e0706051b060a090204050609100b090303040e101a04 70
    0x12100520704081c07a0600d05d61396081000615a664100d0099101080f0340041e4420a410400d15019044640d00381c00142c0c02e1940e0342d0111381041c40000c117950820702c01c0e03141c8140182d018051382c00e100784410080200d01a80703038101103940744084000c1000210042440e5074071821200e0685020f00080c644800f0032000103105510912030b141c2c90f06000910b240f9141049015902c54904e55000c981c2c40c2e0400a0425844140c24041c104500a440102000e402c90144486045809000e00b82c500b40e181c0d8001d000280d03005100c5a0342104c040180010310407510350b2203503408a0007801800301e10781c0c50300e8020b00303103e221400100240d0400c06840e0401401144010468006042940d0b461007000300e4950b010b0035900d1500414041d030002c0014070f2515400000c1c185208071001c1010381d603184204811441c05941c00700d1840d41e119000c1c021601910001c00380c0050080850f07041c6983c03648100b940302001c455245030320084000410a01091050fa2020103007140869801c05040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 674607931 1250 674606681 674606683
    0x3002063103051009080d061410170a0209010c140c19030b060607020d05070b0a12290303090d0819020318090a060b07061e0b0d0602030c12010f09050f0603 68
    0x815002c030f0519990403140d0100042d0300704450755200c4544081c44a2030703540386070102902155616a002d02400c80040000c0c07442880480340180d03000c90f6034106034840c01d54001c001d400002003a414005402000804103100300300e10317140702c4081c60013007041000c400b0a202411000c00b2070035481540101d07003400011803840345182c3c004001c0d607406484121030300020780092001007000c0c1950085460100d0950040001810781d070700e05403074a4441200310344941d8110348401d0b45502e12244403510080300400d031101c0d201c0c800d11005007143e083c0901080004c584c4030407414200d402c00000200610900c05400400d00d02d0804d9001840c10002a081404070240e840705105105041c0315000440c0d041e21640420302404185801d00c0e241d00b03461400c3c03801004070104560060506030001445c040311402090b450041c0909002035480040c0d80741c2c8083e400150901d00c1e03c42080c00801e2044c11160441402441148403803e0036519140906044600240c0362240c030407400c00812841c0e0314 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 674609181 1250 674607931 674607943
    0x50d11073504060e0d020a12060902040b01050c0c1021020403020f090f0f040503070b07021b0405190e0102090402070c1a07020a1511060a0903090e01300206310305 72
    0x40181e170117405105032840064042a07891f0420140030000303014003002d100443d0301510045100b40d030304002641240b00156075034041c185200f440fa51280d40060100c1c1401c0c8800088000a03043c40f41e0700301031a4030720b482801302000b05070a025a02290410071340c602886151454030341a90011a14145008030340789248000740b07210000e020b00b45c00300e81000b404008450485420854001403400c0100c0c0003522043c8080c84128410f00c0805052050300c1c1a1040b94015007942c1880002c0400d0301c0e240c01c0186c90202c0301640d06540c20b000082e9941c485d070000701256072240c028400f881c0d00f8403014000d51241042c007890341c05028410400103071500d503503003419903111500d0f45840b910040700444105441284814050040ca070600c0b0b440c080c990850a061440303034503182001d0b40c4401944000400034800d002e42114525071003046204108442d1003034444000c3c0b6554140f01540202d21f03207502686012400349515207649510708044450a1540e9100041c1c0307101940c81c5403141a40c0d11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 674610431 1250 674609181 674609207
    0x30f112b140c030c0c0a030903061409100c0207030623090606031b1f091406120609061503100f0b1306080a0204030212010e0d020a03050d1107350406 66
    0xb400040030600c1002c0c15401d41d40c0e491a490b0490300c0c100e020b03160081018103140b0089440340d003084000d9040041c4512014403422040d0000e150300f8840d2164036015101030311040041d809204004008101640203190704002e0780000740c11940b07400309042100400041040c2e442d60841c0f01805140d50307021502e1480c6105038400c4011490341c240008107208604031701c00800300c41c580c0e901d4140c81d4001100f041140c4e000311001462086040610015100c0e8201c3c3d221580602c0c00040c0316403a106128a030840409080c140c800c01054541002c0c90b40180c501c034282c080014002c010301c2c060429801702500c031036094982050300f81e903008401c10106000314024070080e9000140c150700d8a81c162002560010b080d401806030907198940240703e460b204240e81d01592125005050000482c40085581035039810b1411201d100b0b0035006014402c14400050f00070080c040c0491010103c1e400c1c1340341c0421160141c405182d8840d91b0209503c0c000d1041072106000c10014036030044940c100903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 674611681 1250 674610431 674610451
    0x70b070203120103240c08010312050901020c0d0501020432010905010206070f03020c011a040e070320010504030206030c0a0815060a08060609030d020703050c0105031501030f112b14 80
    0x20350100b440c96210041c0410f94000c1c0c17901c0d040300e00d42190f40c01203280b412240651000e010b41000320108686c28072842003441d01503408901c400015083c117060300c5443d24040c5c000142801c3c1c90f40c0e00080095800c03800103803e2030300c51980ca516031152050b10b1b14889000d08004600b1481c0400113915010b000b031040d014041d4640d510358250707010f90100c0781c110420000800c5080c1e40c0990003100c00d40440e0b11980214501900901112000a0300c1816a9044005202108041c3c07569031034807401a807616042010034000040103072901e501640c001c0040c01180c603200c458400c0c00030848000144a6510100c800c050302c4011340300d01048a01c8088a032070b05c1d000300d80d1500c022400511520000681501c10780b80c000800b5940070a4410540f031007142682c1006031048011201d9001c00e030380446040303040340c0441d05907600030343c4155000d84660502240d24145d81c0184200d54116004c4094010001c88505091400c81e030500198400c41003002c002804d880030f02c0302000000180381c0d00700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 674612931 1250 674611681 674611703
    0x1a010804050705041104260712050102070b1816050603061002070803040b0a1e09170c19080d0c08040e060120010c0809010209010c12090b03010308070b070203120103 73
    0x6128081c011070b006400080c005105003207a61161440d81d40c41441183d5881400451280003091014107125041e00800000d000c050708085842d450300401c40e5003120741c1d6600b0081c00c0b001480c04249144034100c0565280e04103145184500e0401031000d103410154001494144569034400381640d030003002c00d452580c410340510900f645000700e603400c9403980c1e11001c6000100140d5003c014514a61035588d64160b00d80e0003142c81041d40205c080304070200300700c20824813002501c405880704c8030384090102c0c1c041c418030718045002e401c89494079000225500105029904003004940c01c50440d9242450308036020f40c0364503038140264000c80340d004136210041200340e0720a040480d40741490114010030320500c0300c6014000c020703408054010a0941c070000380300ea8010701c25a562084181c442003000070503a030760340c4142240c0325862014002d00c400301161403080000a14042d41c45907440780c2d40c544042c102204000e40050406086507c10131001c2d004010184800d0b0449a00513003182d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 674614181 1250 674612931 674612933
    0x16050c0c0a1202040b03070b03040b0717090706110d0522030206030c090f100c030806060c07090504061d07060305090a080d09141b060d0f09030906090503011a010804 73
    0x41440000d5605076400440d03030700d001c00d02d00c1a80301202041442200c08001384a400d5051680740d020310b10803214078050510021700030841d0b002013240d0140180c9003039000c6110030b2510f502081019a000c07925584415070500c08036400c42e45010050412100600e012307845210001c0c028803170301d2050348403d41d0001101c804200c0000205014580c000d14154aa02d042a405403860b00108089445100403010843e02c0c1d04010703212000f01c0300f032540c41101148080c0c40660b0001d8000d058a900020204401d00f0108420300070310003e058820000310302804c0c1030a040c8140c40652a4424003450480c00c041c0d081800040d0b09802c40d01a81800b0515949d1070b0034060410f2102c1c2005021440001032020901110380e1000c0d801a03c40c1c0c01e143c1034840d84410b8655206072b8103504c9103246807148040d0b03a4915000e030181445081440f0b010580c0886003144200303940b10100128040392000806115880d0070154000c040c12040d002080400b05034840000782482031742a482c1801903410101e8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 674615431 1250 674614181 674614183
    0x5011509140a03020d17040b190507030813020a080d02030d1410051923011b20031009061e0c0804172115040209100f092103030b01020616050c 63
    0x10a1b17055400c4606480741d03551403915450340c2c054045500d00e03003020503803551024010800d440e0700b56015a2929116501c680215030600307003440007a42c5c000b610200000d4800c1080100461b5054a0f901441d100d10016180c502500c2c00d41e0500000c0041c040100030b072101005000004540044527006aa00c1100405801c2054550800c80c1076451018220010b52004020308115030002c1c0e8580400f40724031100b819480301030103030051134000e85802e51280031507030038a10960400c0040c03d132100d00b03001038000411260180340807141d172511440486802c1010769061040c03101c08100901c03581c5030301e4500400c001c400420040031200804681000d0140c04400e0701d00d21158100054401c4180c1102026031503803c490f0041290007050490056082030b00940380181ca01070951591905040010b0b550520400c044e9070810032200400250400030403004000307040c488400301081c0860303060082c1070f10410103680e410f40d0b001c1c8041c8104c0241001c040c1198039028a04280c80e041c0981401e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 674616681 1250 674615431 674615453
    0x50d23070f0c0f080d1205071e02031c0c02010c0c0302060c1e120105030105070302070203101d0a0b041a0f0613151e12030f0f1205011509140a03020d 66
    0x100c1010074891000c00c0004c0c0004110b80e00013029280e074640a00c0f02d001d04000d607141100c0c40800103400034402c0524008140c42e0003000200d60068038102144461038480000700004040483c58684120b8401c2d580c0a00c1040d0300d030185d17443e061080500c6601c0c082e60b115000b5110f6402100300140b00c038640c12100a034000c840f010035954550380c4804540c50700e1010020300400d0f207c5c1d460080400e140c035000e403084030f4840b079028020300303c05015080044000c00208140b07842c4070401c3d2031000724140c0140032800049100301000300040c10715051a16010900e1600c0c158880b000c0001e0249001c1c41c0020164010821243c0040078280f0300340c0d80016110844840306040013041011910700c11000080c40360b0411020102c3d002682c910b8614092852802c000e804926408002c071320321032007030101c4e0400300e01505003c0541b042a40e0030f242117440903400703158a0400c0481c0d40c120301d544000d030b94000700204500403002140c0f040c00500800074912000388503a00c1d40661008000c2034040d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 674617931 1250 674616681 674616689
    0x30503072f0109050609070f03030c0204240311062a0f0601061101240b0d020c060109020403050d110c10020708030f030105120304060801090b0f030a050d23070f0c 72
    0x81951551010041c45019002e011400c0340d09009040000c1c1c08500d000a180007140d05001145500c02e1030340c0c40544107806065410f81e0080d071205400caa0301400b1190340040c80346190f00807040c481c0345003081c071021340c0881c030a50b11900b01045050030a83c4203000e001c580001a50a5040300101d1644451420404204100c0e00d0f005174030000440c40d4000841200b6842003074000d1003071840900c03283d4003040200a07000650740c284042131181c10380b0440070f0b03d040d107004040149000c01c041000d80c60304009a0288070500d030006014402c122090003600101138260a00c00c0f43c1d90a050b88041e26000691222401000346006140e070340d9200700300007401445403105499494202c0901c949040d4001d026031405075000c00d9040c1e5030400700004482c11550944c0d10314440b41d083c0b401000c06008585c01c466030080c031803c0908041d5070300380400c3c0106031151008100e128200703500a84400c4255403440c0c01e8060040524020b018a03208841c072060388607842280901403860051700c041241d0b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 674619181 1250 674617931 674617997
    0x80d0f1805011b083601060339050402091c110a0509040c060834030f090b0a0e0f070312080c0c0d0e0f18100602060403050307 56
    0x80380340140801075121407080c400c56900c0c200342c1c442c3d40c40b0648103400c040c0c0e880760403100d85024951240c24803401a00390501030f00468824240c4010350b00e42911100d400541c0d450b401c1307203a0300034022048409004034915605003001c003c8805c1b8500b2002c210075200d0240503640019011449641d040b82c640e03800240c000b00e920084800703052445207041e860880030300807880510081098509494000d1045900070425080399080c0601100c1440003d000303022600709525907610001c00c0c80c030381008071048158100c01d1020a8080040642d0700b130b1505141801d1a0101060100b008000419070000c1840f00200362400306403030035480d1446045400440c0d000d030803004020810030920780341c01c00002d41e49410f15a103d03400c0030a40f505c50002121310685c4140280d00d1030704e0090038070581000e001810341150780c5027000071400328050f440155001d058040f040000c000803100e6076030058503440c4014005464556000340107840702420307517410702c208180b580d50b00e00745d00c50f030400d0b00d560285 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 674620431 1250 674619181 674619221
    0x5030f07051b0301090b040318090c0e030d0516060203041109040302030a030b03060112033b03100b0108010303050f0d020403030e030d030c09050111150c0903070b07080d0f 76
    0x400c2158484203804501526994000c0014420f8038050061100494211001210503180e50340c060320021183c110184490801110010300301c407103031061950031030040e140c0c40340c1c02c40302404243c102020b250403e41800420b11030382511145202501c04529844000141e0380d07110303401c103400c0c402508102036078030400440401c000c05601001a00c40080d49480601c0364503020701c20540c844a003402050199074860100c000400c3c45228180b0f1003810200300f401ca0242074100b010f14900e0801046000c1102d600c41d031100604040241407441588104200044144180001c04061041c400a010841c000c140b032062045808122050210015070071540c0700d60b68a000303440103210480f00fa110f401002c151451142c0a8081d040041d402c035074034186600d0410b001540c0d503002d1001c0031540341c4202140040d0f90420f40801c00c0c0950004480c0c1616075071001d0802d0f00e0440650030074042d180c0e0a00511001a1240041d0b5405540359130020030241c280d216840c00400c0d640150300c6401001d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 674621681 1250 674620431 674620433
    0x2070b0a051e040510081e2d0c0a0e0105131206240e150a0e2a0d0f0905060a06050a1a07080309190302060709060801120f05030f07 58
    0x10040c01d400b104001040002d09045000c0d1401980f003240c3d080080013411075140da200350617850f807120702c1b0601c107411850140c040160900b01195001d243c12460104e001c03d0511a850040c080401113070241c1a07842c125204000f6802103016070f205109200c0302c2e0943d568004d00569101e103880201d0585030313940d2203000041060000106941252508880610301007180604019045595905610300351602c7e40c24001900b006107650880e40b041140c0c10400d075140c0320316000a01c10414016554104503207011140014010800d402c2004044201080c10140d8184c4c2e031a20003a010010702621020f0102c0003030300009900400601820003000700089483d80b26405072003007520000f100c0d54a4429454100b4852960301c80d00c078500b4020f020004000c0300003180c0c842020000c0c0ca0502000000c040c080e02d6074542d04401603000a0201300f4425885488080107007880c2c5402242940b51071101002040000d901400380b0340040e881d40c041c00403c00c125040802420109556408a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 674622931 1250 674621681 674621687
    0xc040b07060b1c02060a0c080c070b1e04061b170c06150303160204201207020f0703020a0510200c0901150516030306050405040807140a0b1602070b0a 66
    0x25400203948a00e040c512a81c40003c03010403a41c2e125030340503096910301040b4450607070701d1698041c070840b001002046075524071081446000c000340080c03036080351518045901c9403c0c0440020544820b40c00a01080152030341c007100f03111400d0608016400c00b40c07080d085c082500751594020800d8940d00040b01803582c1b0000031384a00c034074840c40c0d004581d800c05004264581c8603036100c400c1e12403408000800540b405501003010010b2900851740e040714810b0016000d9009640300131003540b40b180030010042c5d0144a510f4004180c8006400d42c14190f40c0000d113280401c0c002c10b8024a80901d035099010300403280101c15500c3c088054003c02c600c01302c034a81d111a104d1103140070715010000014100e08030100049544090b488240c06d00c005040304000700c04d9052070940c201070b15002e001a003611503110b054000e502030034540f40d41e0f00c05401c3c010444100014104142e0388081480710100302c40407001d58200784000003504071044491000c0b4980714994100034038905000440315110380d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 674624181 1250 674622931 674622941
    0x6030c17071e05060a030219091706070807030c050903120a080906010f03150e0a050715080c040b0a12060e010e09030901270512060f0105031b1c0b040f110d0c0504050c040b0706 78
    0xf41d070301d85019134ac0380071514a40c9408080e545040800c00c2240450007440c080c0d0801c411300481890501d0500e041000000d2030101490346015070706030001003445185600046065001030990010070343d44d45806021081d40d41c46100181240d040000c8807000c8074490f81041000c9690b601c0bc981c2101042d04040b61204042d10a1040c0112102c41e41c0c1140350060701700a01c244000701c149400c0c245030034130504075030b0310054440e01004140030148880071035500ca0304000d04000b065500c1150706203041d8600c040f40203041c596041d4030a1140400320381c0e00c4521100b801c00c49074803019004054040c7d444183d90309800145e4400c40031103840e03407200d100040c41c0788101d121000400f40399a90300c040c5a2034040b500400d0300c2000c52965070440b28107001740c1d01100781e03800e240052204c414940f01d6410105081e601141c00c060500c40f61001d2228040000c800c400003110b40c108046411b5403007100a640503c43c040c003030b5454070005a0720000c075800760303802055a200080c0c0d89c9c0001d49410b0b00200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 674625431 1250 674624181 674624189
    0x2a06060905071b02060d060f080304030606170d0c060f020c0a05010b011b062304050a060506220b1507050d0311160b06030106030c17071e05060a03021909 68
    0x107403815000401003841082402000300e006200d04004000c0350302804120f0303101c0d280c840902c0740c5401000810b090740e0244d00c0002c103c4000a903403507a0440c40d00c401038501e21f03480221550341c0e00306d0801c4e6041d030118844e2035130021810040705102807883d040f80580009c1c0394009281c2d2012941034002d00c8003052440349184240001c0140100d81d0005449d10034070f031140e40305a0307100c2030050000155950311119072544020007801400c0740184500c3c0708120122011105600050f03105070400c0b04e0b41c0101d81e080f507001c031440b01c640c0e8907407058000110321115034001401c0c2c44520414958a07003d211010307014403841510b41e11340c0c9500341350b41d403001d00641440009290003189105102c592040d106550000003c05120b84020707180c8003200e08021b081140d16558039030000001454204a01005043c0305032681d24540642c08011b040004a5002500035085203011000c0070b56a1001c2c21706949003110040c0d250044514210000c0c0541080c40640c540903036200108141c1000e9414102e17 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 674626681 1250 674625431 674625449
    0xf0313080706051905160c0e1524040b030423060f06010c03021f1505220c0909060b0702040b04090b1b160c090605010c122a0606 57
    0x5564004480d030700c018912442c1c00096003400040000d00f101d030f005101940701864a6400c000009890f00b9a1807002d2100311500c0042450402c100100035001581c8600d0102010000c001c100c03020072100b4400e03070b002d005d00350003180b90380210051507800d0344c028109902c05c280e120700d800c1c601502c1620f085100d299041d21140b148841e64800000c0241c82811190384002880d00d4032001500c0390089245c08906600500315441c4910040c50155103203c618000080361034040a5442100d100507900a00d00400b5903402d90803003a0100d641400717414100c80320002c4d410191b048100c60a03125070b080321841c1410200002200401c034809010494002c4408001d070380340352070400044800404006090201940c00101001500e01081011200c4006581e2920982ca2240750085502010072500c1c4c0035500c0041c0859603107803090001801d82800c0904802480f070311282802d601d402c1d850401c00811116400d03c5005d4452408107441ca03850414100c8900340c41c1c0340c00502901c8c0140440c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 674627931 1250 674626681 674626717
    0x5070b010b070c150c0f020f030f06041101020d0e090718140102190308241201050907060f0206010b0a0513090203060102010510120611090d0c0602060105030706090902090a03050f03 80
    0x8124140d004000d00340c4c4030b580703c185108040b50340d03c000903440c42c401a030388600040e00c0c40206031030910a19102504001c064952440c1a1030712002c01d601556001d03045511509010b145507030000011082c41d2000c8429016075540d00004440c2c06282d0141c140780d903d01c5030800101031200754015002c4e03030400d0b02502e081e04030018441c40e226078001c4010300000e03d020301103580701d9a025100400f880700c403001c411200c40c2981c00b0800c0c07032070490040c4901784c1d0342d8004c0000741c00d0103000220103064a4500388418450160000b5650f040c18050fa0032000c0300007030f00d0140300c1d004404581c03c0d80b00c2d203c412412280d451031000006c0d00102c40060240d401c000c000741c07070074010341705100c1030f111a002003000310001030321010001c048840c8900a03801d0104a8801c29a0340d0102c500c0c2c102d40b01d61400900d840c01c00c03074024100034040c0c6c0154069881150700b07110060300f000d03500d01a954201030040e111100381c000203001c10301c903620285c40c6015090f0000c4621030040010103507000c02d07848442c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 674629181 1250 674627931 674627939
    0x5070606090615084803010b04050f030601050105190c020310020a0f083c0f0702070b07150522050c0f010905090a0c090803040608040b0609090d0f05070b010b070c 72
    0x40801124040c100c14040c0510855515603200c0c402ca01741c80585580c0c04000012010b804102e80c1c420f81201c2405000400c0400140c84c003100c08050b548020340c00740003294540ba0020f080c0f406551450b00007020b0392440f15900c18421a112a8802e400400b2102040500c1814500a40c011851100010302c6281401103040c01403020754060704902c81360301c0202145501c0c100720102c0300300b80c41e4036451401c00d81140c0701d980007544902455070108a0a024140180060b10709a00d90f8800d40180d502401007501003115003403c0c100f04c8040c09000300e52583d8041420511203035000c0c4a1040d5003601407008140000090400d0b125030b003d8034071200303042c100c200546001d0318030f10400340d00101c503200081810140307070003100304240715040c440c480c0c44d1200e0b1684c0c21a00035800250025420780c2c104414890b0106045070003280541c0d00c10b80c07504001c503900e5100c03070312500e000c000d012000d801041c00902c9141102c0450340c101c01d6150465840e181005202ea00420054440901d4424041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 674630431 1250 674629181 674629201
    0x50609090a1101050c0f0304150f14030402060a03060e0702060a05010f0503060a0b03011d0d0909050103050c0919020c1b090c040e0c0d02040e1b040b09010507060609061508 76
    0x380140c1d0081d0000141d050b0050045031a035000820040490060b00f83c0045c06900c00c0020704094040c0340041c000054039004000c2810301940a603008218040201c031155005200c00c0708d40080c0c040d50040d43d1038071204d00c190042c1c282540f0495842501d0010803912941c0030070441e0003564810001c2c011030b683c0380510303401583c41380141c0e5416040300010641d0071000d40d004c00520000030700003042c00c55110070305902c000c60b075065200f000d030480c10000c0311843e440624100a04500c20f000c01655045403200c2d9520140c0340e4829001d000003c02059100c0c090b094680e40030031b407070601995240c0394021281c0d00c035841d00c0c548408158401700c0300000c602c0c03c040d40c41e102d0100c20760014101032900c80091075110b0041d00581041e0f5081010400024240c0020000f0f44401c541520460428400d05000d01d0140020700e0341200c400e21003403003040a09400c685549100f480d050b0348840413030800d840101003552010300c18501d44007000071076400425819070007550a480b162127903510b0080d06 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 674631681 1250 674630431 674630443
    0x10b040b0f09040c030819020111040b0d020a0909020d0e0c0f030d08041407030803091009020105090d020604090c20010e070e041b0605040911040308121f03030305060909 75
    0x395405499640d00c0c02881c1404002258440d00070031005940301d0380c0341c450150660111510300450301050706000e0358241c0900a51070420b00300101c1c149018070700110b1023124007800e49904000c54000985d4003526104000380710207810091000c42d034a15000e030052000f8203502c8004010b500032210034100600d0700030f400c01306808014002e061540d4440d002100c0c6084002d0048a020100c200d0000c1950782c1081804003451144020956a04116000614004801c0301c4000800d04100c0c0c5540144d90010550302d418006503149040140c441c400181d2602403034000711500d9281942ca00d00c80b40d805011200d90410140c10a10341c503080102040c01d0f606494600034250b4040541005001081c000b00c650041c007581d88101c0f03a419841000c03640030718607404a4006a0082003d0003074620501c10446044019410a40b030303c3d195036a0396903240140340d983e84980d40c000f800100002c1040b4405050b4040f00c1c0141c100d21500c07450080c0040070213458841c050100c000005042010001d59 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 674632931 1250 674631681 674631701
    0xb030c04021821060412032a03050a180b01210c0b0d0f020c0106140102010e0616020102041d070e0409050a0f03022a1912030c08120a0e010b04 63
    0x2050415a8000d00b44283c1141e280041903607080c400d41646034420080c000a4092840f0b11141c558080031324400a042e144e20310f803024480c4500d0703c02942000c10008100e421603e0b20308010a40382e607000f10000013042510b0488070b00e2081103802d10108446440154161012002d01c3c2e040b044951150304080c03030307480c03000800104440d20300340310302070b00e2002400b0300e46d00c1480e003c0b40141421429900b0b0782c21100303400005a44401040c41b10800302e0b0907800c140f01c000e1008110329607011000c2030352014082c00f007040b0902d101c4480607100341300b03404440c06071602c405c81c2c1c1881905580030303909284040b581e41000503568541001a45424000c04841d60b030824000c20514006486040e000d84914408030250311807810180025041c40c051842040c3c2070214240c1c030307101c0c12010b120602101c082e103c100c2250140b8144130314218991039051381605454240307800d10381e03071403d440f03240b081228a5440d400d0303100c03c000c3d00c1520364000c2644141070200910400f070811b0144801d6488101e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 674634181 1250 674632931 674632957
    0x1223070f17030324030a08040b1201210201080c04030b0c0408060a150b0a1e03290109150504080105180f010c0906120b0604090c1b0807120e03060702010b030c0402 72
    0xe500d94441e013041d040080c1068010f003519072004c02a070303d05071240d12030fa00003550004046441400241004900f500601d200722080d00c11000d144c1141000d8400c8010003814805490007190254551400361005158801e405100c0c81c2050110320102e82c10500c02c1440b5031007400e002030b82d10440d5020b054421503201440c10340c0c0c81c2c10000103212940085048004001040d041113001080c0c246041001c9900354500207054451007000d42021401d0401003445001e204501400b907982c41804c6a08582c10b00e401c0340c0150030600e100325414416913201c00f60f03541c00c0c00c0c00d105403000300c07122440113101c00004840002c000126207500340c4121022010106d00a10f4007009800d005100e07208004030041800104248048002200ca40041c1c00000101d999607172152101c1c2d8105480c0d0200407100d44041d4066112551120380d03612400b0070081203103400114a2256a000c1c0b50001c500e148010296446403600100003802030000340c04241c030078402c0c0340b1005500d050038403c03218402c42144c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 674635431 1250 674634181 674634211
    0x60108120d0b0609030a121b0b0a0e033007020d0906050913020705010b01170f360d03060b09060405040b010c020303070809040507091223070f170303 66
    0x5050800821902c8011a0811000c0242010681c0c041c014070740214030070400c003102651320550080000580b61140e800e0040710b05200400310700881c0565030b120342c800e1400311f80c909200310424118040e1036103801902518140071020300b6000708150034980e840000c41c800903903402a080303036101c148101d8400071851070b4005008052180b40180303007c078409018400300300f00b4603038507104a900180b0182c9050750340308091a402d6031f11100003040c056050410b00b65604000c1d407021036284015049100c1603003800441240300703011110030000d011240c038410414106c0114902d03112718000542c880081e00d05000410012100000c0e954988809000f10382004c1c1803409101c002c0510520336414007130b00300f001c600142d1f010402000014811040315071550b40c28009e201c01c0c0c07040940b030b0409000d880401884000c29a041d00c44100e900951000320303082c6140d181d643e18103c1c0c80b0925440b0300480c540031900c45c000701d000c141116844501440a13201c105d031800e07260b00040d92103044550840b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 674636681 1250 674635431 674635447
    0x1202070b060f061303030e04240e070c0602190f050c0c0f0402040e16030c0e100c020d02100f08061503011a040b0a0f080603010908044406010812 64
    0x30b40c42500d08010301801d441d2400e8000707403268211303100396802100041c180301c40e1086507003001e0003171000d080c1e03016403020922a01050000c80e07410b540d01880e000c00e901c400009444500c0b840040c0c1d03030a60021400c55507202182402601c00030a000f600380407031940c1c102100101c3c80760045179802281d0902402013020040108444e440105040e154016003d0101048000403500d41c075005519000c40c86904040c10500075007a03d00c5142d13044144084454046026113a034824000b064400789004018142e0f0f03840007603440040c1d0f00019400c0100380000807200360f0003200b0704404c0c2d552600d80103080e41c0e800c03081100243c491840c0c2604c1c10b0b410702c010801c5820212142c0d412017140040c89007016110300341c040f20303074000c0110100000d036203c080340b514580001d0b0958026000b90000d000042d0113813148080c5120714410f4036001c1c421010444002c02031080d00018000c0c0300c0c1d008628001085890000c5904a99400f0840d4003855000003010400001d0055a0400448407182040d1103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 674637931 1250 674636681 674636689
    0x18060c0705030d15061202031b03060316030303020409180203120a050c06090604120206060d02060d060905010f080d050403050a021009080a03180609060c02060a02190609031202070b06 81
    0x8440d030111414403041c001c0324510301c081e001d040e1500300303454402105589480790007003402643d1112078215034410407e01c0b5000040c4d04040c80002804c8030515581e442c3c80002c42e1529581c0286800c01c0000d82c03002008050780354000b40b04540300718109011010001e40e40005a02c100240250306511118120044200c01406818209000d05206043c080c001c20800d061400032502c001da25000320381008100404c0e00417000c100346062000f000f5034909100412070400c1c0c0c44070082d02c00c00c4049401003401a440c2c203d40301034030312420140115690380320a0080200c941c02801c145000d88840b00d00c20902c54019a401c5030b412400610f006140ca40078804e0f8469070320b0503003040140015010812800411003910498031030b645002c10780100880d03000402c40150003803820400005000c105050b8004806036015404441d01c60f0f50f0000500309a24191a10700781c0c0b21400440c400c00414880f0a5000001a90103611040c000c1072a420f921402c0740702d0b0b64401440919094041019418 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 674639181 1250 674637931 674637937
    0xa0506010e10050a0f0e09040f050f19050c0103020a02030706020f070602070f0201030506010306050f0909011503030c06060e040b0c1b030f130b0910050a0e060d0e0618060c 76
    0x40c1000200081c0c0340000c1103841a564103800e0101d14001480c00d0038992158410b00049498986000c500c40034600141540c403014202801240c08215001c0c14000180140c940e0b04400d9000c4035070000c0308100400340360031200070030364003801034070a403406550107402215142c0d0000d070301940c6001020b6403150020b400c10094040350000500aa0002452510003044400c2c000c0307840406403032061000500b5a90300800450416007492401c0140d92200c06600d0150041103d0115455891902d414018044503050005109c0451400000d044d0040303400410303140212800c0c040c0c19101c2080d4442110140e0740108455071070303000030b0b02a200c80405030405200d00041c0e05101c860745900740386140c10030b00c80d143e1102c00001d0302d41d03101c01c17111800c880140101540f0038144600080040c2c00004000c0c505820700200141003507855214410750380d101e00b00141031a03114011441c030200107089014000c602e610840c004528510070601c0c01180f1004c0e018000c09696a80c0004144160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 674640287 1106 674639181 674639191
    0x9050a0e0a02090115030e01050c03090d080f0c0a0507020325050405040b0720060a0204090f020c0a020112020714010c02070b1201030609080c01020c0606030120030a05 74
    0x81c43d06035245045841044904074408071104055001d03129a540f14403141d4602030030850b581c9014030245006280b49001c580424956800960300b000003038401046008a40000a6000314284020a8450514a0900e0500d64a03a010915007554a10262805600941082d403012054a0428018502124140310724203044c1c03107408011030054081e00070410802d180b10382490340d40d180110f48100540882c0d940340b401c16440030003500303c2c1c002c2c098182c8c101140403070800258000d5540c42c10760305024002c060020360041d54910f80c00011000240c4d005e00400d40400d551007a011020000c01e070000c60803200041c4000d0411140e40c2000354041ca0500032600c40d00c2c2407542c0c16054075804003000450380ca1030b041c8100d80380500074125000d50300001c0d03241b00500012400c1d03409603000381e00902c000078001d5070098180001500c00c0229110a0001034103004080c0c02c060307041 = true := by decide +kernel

theorem cover : BRFrame.Cov 674460431 674640287 := by
  have h0 := BRFrame.cov_init 674460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 674460431 ≤ n) (h2 : n < 674640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
