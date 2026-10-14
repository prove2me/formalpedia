-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0247
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:00:44.524561+00:00
-- url     : https://prove2.me/submissions/0f8782f4-cc03-4c5e-a46c-03105cdbaaae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 44244608 ≤ n < 44424464 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 44245858 1250 44244608 44244611
    0x714060714071112070515070308150607050f07090c090b0405060901180801050106140316030c0909090c03030806030304030c030f02060c01051906090608190c0302030d030911010f0e04 81
    0x80c501005903402200f60084802418800801108118181d8a106a0141c1d0b405150300c0c00980c50181c11100c280d90070700d41e2581d0365003860303903444da031044140840001140d0820300038000700002540910103104680b80350070061000701c1ca8000403006880303010484c001171000000d0188400d000741d05c11101965410b40e1610b0380c0f160240c0040356008004c66540c1111740003104049003408064001074100c80059441c60030107080b00000140d02c0c032040d9030203a0681c240307228500e01d05004e0340100c4589401d6003800c004d440d81d2040554181d03210141d0494181c0c0b1400c40500405400c1100280c0103041039000b582028195940c9a00010190001401d54040303a42141c00310740e510380071107141050100c000c6c08a8181949401e030050000703003078008814180030002c1010242441040e044980b40070052400440e684400c102100c401001520708900740c0f04040b025840420640d865952280c0d0700140088003411701a0150000c00d40c0b00d410041c489034036801140d4407610b0100b4000003280c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 44247108 1250 44245858 44245867
    0x5060c0403020105090405130b0a02070314090603180304360e0303040602030c090d051005070806010e090a110f0d060b09010807110a02031b0117060303031611030d020714060714 78
    0xd41648c02d02009004141030300501c2040f00c6400c8540180000a100c0e45a4440001200b032014445026541d0420f400020600c0003501c0700c107401144203130014038074007541d1809440304a040c003680502403400c41c1c41c01c101e40640c1c915181d025a4034403001d07000c8100b08101c40079800142d0702c0f440040c1c006881c1940220201d90003003c0b0004a030102e410042880c400b003211842d01c50388500f50180f42c14a5245014005425117010760102031080720140e5500880008900c00c00110b148054a0600303001e0340e0700e08000744000c101c0018820719454025240d10782056041038030548030b242c0c101c4d00001c0000d12801040e66004105039402aa41341400c00a415401c40114641145040013035890710501c0302d40c24414001203241e03041c5110a83c1d4190701158684040e044c0400207440881d050b80c070400001d400051400c500150403082c03490b0496100700365588091031900440b40340645203500040750301c100440050600d00c0c4980c04c00c0500101d2070440405015143d60840c00d824800c00081d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 44248358 1250 44247108 44247121
    0x405240f0f040b0403060b010e09160f18060806030618100914010c050d0b0a080a060c1215060306090c0f031d070b093c0109050d050a05060c0403020105090405 70
    0x41910082c0c4415220309031919583e0404802401614024601040c41c9c4a00d01c0350a090030f04001d0310603890002c4035801e102d85254201d504000b04c80c82503042008258551a03040c03405c0400300021300355a514145a8105441098180000500710b001e84142101540d2a185004503003500208800e5000140468850500e40c6070f103a48886041c4041d440c01240b0780441360030102070000c100d0681e804108050101041c040184010701820440f5840b07103401000195240c2c10600241c0741c1890b105111030544c41c0e001c416604c0c4119542d40f841e200350001e101e00c2c2d5051081d0802089035842c20302a404c8508401b4001c050054039110401d07440d652100040107001806c02c10811a0b032080b070340142d5942c0c4904105400c49a00580324606a11416200314403160424090202543e80c2183c04420340080c24069000800d00a0520038035031030000f025591002014055400740000d48540102494107604184000340f003404480010320040c805030740d0010070390301141e00c2075500045546402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 44249608 1250 44248358 44248387
    0x100e09040311060a0515010203090a05150c03030906160806010f0f0201020408030c06011401080103030212090301110307020a03170106050405090405150420060319021b01020a02030405240f 83
    0x110a1101039118140902113241083d5200c0c2d44a808403102e1501c40d41000c8004a072207100f2035124030ba000001580501251034480aa900704041c851315542c900079107520514103681088440d034107183c101000700f1001c0e0001c08540348000030985449201480e202c03001070181004840d011041009801842036254000d5044802601504e000c5940f2200c4469a084e9215004d0045101e01464010b1240e00755020750080d9058079410380250141c01c1341c504070000703213412101c8000d074550b403190360340000062044021402940d41c0d034064a2595803030309000d814098450618401584540c0041080310b600ca0169000c0d00e1003220034404035241c900b461450903010360446004a0140018001000040310075040180700c10808a02440e9550040141030300080f202c0074140c2142102c03001c000071003039004010b6404008960b00b02021080d240c03908a0b002009400050303407000a060009241001c8050043c0080080d000003030005140035956901601320401071050f00410030407281c00c03c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 44250858 1250 44249608 44249627
    0x9060306031208041a10080f070b0f030c0f190815030706110a0605070c020112060503060c070311060f0109060b03090c0603090a0b190e01090302120a0201060306020d050f06100e090403 81
    0x1215421182000099501e01c00a1b51250010074490420306240701040460040100d92a000f40c0c982003112200c0d9480706980000c001c0901418100304d020000381601c0040c00142c0700c015518640100106005411300d100500305036082510719045002d250380002380f400c03e90398a450244864145519420301d002617000740200110f0401d4100107800b81d0107011525414001d0f42c859192840409071401120300c24012940c040e00100001806200489d0050030050f1082c40c140807040040550241450016200a029100800b00400c900001e5028541c0070b800715041491460030007403000c5540d0110002100d006803c04400128032410500009840c43e8011008001d10310300300d240761000c0480001962425454010740080c925030500c80c20100d16850380090005104250203076903141c00c481c0c2c000007150b4a5601c00b100254482c005403105550842000c106400c0000040b040004010704c500d0056003c05a444400d6074404864180154140c42d1045207890741c0c01c085818424 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 44252108 1250 44250858 44250893
    0x604030206030a021e03010e150105040e0a29030316050312130303051303020d12020c0a1b06050304020a09020304020d020d050c0103060530010b1f0906030603120804 73
    0x740802004000021a0010f1100c01c442e030000740401c1e500f1060340401400207002d100d04074404035000940c550b04001c1917010203103050400d60700f0030f81c5d030300d043d400c00c034a048641c401c2e41034998443c0d1803084685507080202042e0b40c3c0180c00700d00480c0d00800d079a802503a0910205565000440040c804144116105d60520845400c1e4074548074803c480880800072040b00024584800120560000c0459191140c1e01d0303030140c05650421401220004880703c541054141e003080080c0c0d03506410050881941d20902951440714251158809074090310b44c886814403008004100050350b58400359002c0d00c042d0f120043e141e0700c0b03d0021030028101207a000b904007501990380302c00c0c441c000034401c500c800300b66018030410782c66405104580250190190450300003152205400b071028024000e8034180c50000260407030403e0001d0340e8072130744048121030745002d0741600d10503690120302c50010301014101801941d28681e2844081c049c020800303000c020408002c10104420340341161400030f13 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 44253358 1250 44252108 44252119
    0xb130c140d06030f0308040b090105040c0e0601030f0c0c031404060f050a020a0b0124020c030d0507060b0303030a06030b0a05010602030a050901180810060501030905060411030709020708190c02130b06040302 91
    0x2030322450301410100c02942c048e0345490300b000029a02400500907244110341c040720440c41c452802005200b0180040d0059050640b44c825200024040d840750a202d180d0a540f4040820064280500b0349908544c20128241c010001882007541142c01c00c5400804c914009640700740f82d04080f4108403c1010040140d0340310fa0000a02c02e10481c07c01e05200208091055559400b101c141d949840d4050303400d805401402407680e0b00307405040601821070241384040303100c40758200000d007558021075030314000320b035120028014024072070121540821010410445541070040183d600d00402c8010020454000380008803a440380311001c440342c039082d400c0fa114a80b111122910f070103a403201401c242d40344c00c2000400350320034040c1740c008a401c036010f01450345980e101c00715400ca401d10340e16007510400c1e5001074814641d03c010100240648201500c5610646c60307860b1825154514804101c00c40c500031026135102400540c107078011190000d205a85038020980a010329032002e036100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 44254608 1250 44253358 44253383
    0x70606080307020a0902031501030506130e03030411030a0b130614070e0112021303080307031b02030901090608040b2404090302030c1603210302070204020a030b130c140d0603 77
    0x3200000203085040c0c4200c0e42c540f46140c40e440c0c410100c4c0022108000c09122a58000c000c1d54080d030b1241d03401840c0034081c216038605200d42ca10a40700c110a01c017100703078000010401402100110b002c03d000040313015041c0038480340c54202071500c0c0a000204201080c2d00002c0c10010a6400715200c00c0301820440f0561070044005000001c0d21180c0f1404501c100300d050a008203a8400c070f503c1c0101850349914010308546a40c5001c0c0c00040050307041c0350340c0700381c43d1300c038a11260080702c00b540c82a03004642d0740b410340c2c0006003140200c4c3d00070b0701800315480c2070000045022844e1a400001c00e03200c941e0708004092092603050010b000c594200d40b030484440d090503404402041ca484600044800100603802d0014120312944005000990040215503017244c4000320100306003000e1401604007100da0f00058100d03405110f07102d002c642d03035511526040c24911003051080944040400c00e42e0300c825000f501c0000034201200031101c0000d03103428000d00030740c8028003640d004001c04824 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 44255858 1250 44254608 44254619
    0x2040c0509090108010204050a03110303040b160c060302031b090a03081b060115050901080a020409060b03060301050a1104062106030602090307080a110409140d0302090f040501050a120206070606 86
    0x240d0301c411a1980038040c510000b0408100500841d01250009044801c243e4910303156500d124030356603d01076260104010000e10000224007a040502c5002102c07603900da81860003074041309040d030001d4207050043c0b0402c850080c011981c6001d0300074902082da600d820b4400003c46554264200805c40300700031401d60003214080190b5115048920704807251030341ca0701c1d1000c00c0309040244090003c0d204004005c40ca503c01c1000c00d810050b5400c0c05402e094540c0c0d80101500e101380c00c00b8000040100c104219440d01340603843c0c1140e05810100100c80c0300018190452249000340c40500c00248005c41042c503144a1400b40c40740e07007100420516481e40381000195001c145964824070400d40c010403c4c6002040f5001d40c6640401c2d0301c000c0007542e00900003e8001d1078820b581c10b9204480386160b107442405009400c0700f0701e41d0016920000c0c201007100d500140001103005611786001405036440d028005000c0e0394440d804040d0188281c40015803622800ea4000c0140d410070100054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 44257108 1250 44255858 44255867
    0x1804050f070201061a070305070c12050a06060509060916110f06040302160f060f0521040c120209040209340807030504150e01060504060e0a0b040902030601060e030a02040c 76
    0x800c40e690003401200d585407010307412178104000e92621550100320a81c0000d010300002c040f014030440200c850b46603a01c1c1d414035850125a41a1201d400c4800842d04108141c40b4410141204031000030300c1c1c0c107005000c505001402400d05a421800c03503a08141d16014401080c8041c40306011245904a10604151981410f441c00c801512850305080d02a002d50348601e01600d000303100f03210001d8035009044500f888a80d840744107220341000503c0a10883c4a011054144055031030500790070945002107400200c2d5110642d00750b0000d00e44030059581c0420240c2047d012142001e550302d0301542448440703100b40c03080c4444181c2c1c4405103055168070410400082054a5800c4541d841e41019401c0d50400c0b00e0040c602c0d102505200c003000419440021051000d03000000c055460340c010400b01c51060f000050401c00342402c0001c08415402002c070280e00c02d640034891040c240d80801e40e1901c3c103018003014800110340c1d02440342c8082080c070380c109400031301c107000c0614051805007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 44258358 1250 44257108 44257111
    0xb0301060b0403060e1c0f0309020a060302070b06030303100b09030c090f07030b1008042006040801020c0c0d030203071203140a060311010206071409010c06050901240e0c1804050f 79
    0xc0f0ba90f410300f841100c0d80171010171090700701e110714125518101c000100440da0454a4a4400305040e510002800540c44101128002e481d09850050b9510502e0401035112880103021501c240c0c81042041400321261710781070110707085083c00701e0700c2e00e410318002402d000c410f8203203d17000080d00c820000001c68180070280110b44a442c20002d40b201001031005502c810031408012401c8000454000313050f00782480c110841c0c41c070300380d80c0940300880000c507540e005900c20030007070b074000c03c1019044c0701c1880085a4250101c56540350b26216941c040d4803801415000307409400c0300003501044502940041007103003024951509645010580c100003000103010684204404481803241540001252801400340391500182c050000c0860f98140d408480038504209a0040ba000081d4507800351a0007041c2e483c2c004202c1c1d0003c0000b44559000006103210313a007103404000c01280d07142d443c2458010700c4400705181c1e0340514240e460744078458180d201d40c00ca07140c02d00b00912003440b0031015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 44259608 1250 44258358 44258363
    0x30c0d090e16050720041401091a09070807021002040b040e01092309011805010b1c12050706020c0303040c050108010f0602030409020d1d0c03012306010c0201030b0301060b0403 78
    0xc0741c403620354188860a2042c5101d40d0004100304100c1c0b03038081090105c042680e28080803045030390a54140206007581c2c0800840800c140340790005101c860040d01400140006500041468980c680c00213041310350050544000d1000d844003082c010761003800f00410b03440420005654a5668040c2c04000798041e105013541071000c40004203202c0a03070301590742c8205048071f59200080d80c2c440c5580b070000000e840d10031a50350b905d102c0059400300c0c44c4002d8400c1d000e40300001c1d440303c0070001d104001d001480640c0441c0580b44850000403d88920a02100c8107440d01030b0322120b042c94400c00134820500401d18502c40403040000b00003842851106951082e40c640300d1320703665960755400c038000714000d540c05600144401e03c600441707076001c0d00c7d07407004d00c1801103210005034182415002401080346519004942030940504090041000d40e64183c1c1000e82c2511020400074080e400250400341002000348030b05003503a1080e0001c3e410b07410b0080003004099034070b01d0400388641c02407208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 44260858 1250 44259608 44259629
    0x121602032b030506130b0f040f0f05070e0a290408061501020d09051c0c060206090d0e0a051201060b0a0507020a05040204030215030903070b0a1418030a0f02030c0d09 73
    0x40000c018030900500340038043c0034004588003450b50710184050980401c004c7e42002c40c1c039580382d0042da26030045041008030150001210000034a914003611001403d102c10b000c6000711240158032804e4408040310510100390191454a07404402c0c03400403101000d0444d0004503011907155800700d02c403405610300044501d83c00300321400682e01ca42c230070200200411540b59080200c3d080c070041e592141444041c1100d1400d0542d0b441e5150102260403290059101204202c00c1c40801c0001c45103d000c581040801000e00200081020f5009d0281c1c0e8001c0304500d12111322982c003500030801408428642c00c0e151040c000740106a90802c400680c8500851600043c55050500c00c4178240d83d000b4000b6a14038070007403400842c640c0060490407030761100700480000f2411141c00540604204000880d4414848100c0c50331490040d000e11031b02c180182400712002400402c843c40c440a030f0903c000c00c10b8042c902a8214000c090801045014207002070420a0380070800c0c074103840100c0719 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 44262108 1250 44260858 44260933
    0xf0f0d060608150702061e01060509040b031603020319020904020d02130914070506030903031314120d1103060109050f0f09090f0607050406091a0c0307032c010212160203 75
    0x468807c009a4284000080d01d100c401403208601c240010091128003030408036a240d00341c00030a151103c0c00f14880408950a41d061045182c14842030a105a80c1d190141a160343c40d00000d6420902800080c881c114802c00f00d4110749680544816441c4520010444180039040014075410402c032a14441c1c00303082004150742c0307400c0060300d0061240c0d030011400e51f0381c0d030240441c0721441c0005c01e031030524600312a01c0c24a0343c1042102d224442054900c1d80300c030421090181982c03c6034045466040d8144100b1505991000600b801c841c411100d0036404071000e0701207444810340c20305a5800c40700010810428210006090103008000000c80f15940d5a40000311100d006900403040050b41c000300400420030082541c2d1051901000c20a2401040d42c44a52555020b1142200814900786150002000c410241703911645214a503510035600c480000352102c1c0c80c1081c5e000340c840007085c1307210b60480c8101041021a4040c0444490700031a01a4a0701790141000c0052200f60301c41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 44263358 1250 44262108 44262121
    0x10902040609020a050d0b0102030403020a080d09090c0806040b040227180f01060509011701080a1202010b01050417011503030c0b0601170a09051c0e010e0f0f0d06060815070206 78
    0x2013100c03d034070844e684281c2440580748900018100d024210303411031009101c040056510380406100511304180200201065070b03801800c0394115034449041246803c00c030a00d01c0d508a2403080d1b1044048400003068818840018000e000e08001d4050b00d19010401c14220301d240354403c070700c075a0200c444a03001c951b0400f491601800813a906682e6007011401001828012005025003840c14109290416044017140101101c01d034883d178440e034000b940741c4040c861103504030307101240d00e0320003401108024070003c0c1c914401d40c42080c180c00300031001741c1c03500902940007002c2080700c01641641c0954a040007022500c00704d0041c0c40f04407640e008555558003680e600d099119898000d24029564515008020400c0c1e40003a0b4036030055100032103400b90101c0b00865a150b503034072043c0440c030461000415001c0c0c25110300f40507080c032100082c880c0d5242649100500e000b19040084101d0350325040000d0f0595500281e451311600514880d0f155992803100d101d00b10650854280381c1e81c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 44264608 1250 44263358 44263361
    0x6090509160503070318030e090f0403050405060708161a0a05040b1302040b0a06110d050313080f0c01090303060302040f020306011413080a0503040e01080607021b01120e010902040609 81
    0xc1e6200201c0c014209021503415004401941d070042c52801c000504a84035114400c485c601000228005020240c0c450b0399071030b000e95001e03004190034414032560319050390042d1046c8202d0003424421280170498404200411040300c0e0502102029039a41c514146400e03000c80c80000d050301416151000018010407442c4100e6102c0c1c1d40040305079107580c42c0c0d580c4580d00400009000ea130480c0d2566104036591b1122003010004010654505110b0140198032909100c0782161600400000700240856151500e800140d10b5800420480c1e03588610795414105200f48040c205955007012041018150998002e408a030b0003640d060003061000380d40c01040b44411919117011894507080300158144060241c21041b501c00b00300784616807683e00c0e080c81d01c50940011503181e400040c040c009050f008940d00e00410103400145003a0402600194071741310551841300b40e400d00781500401d40d0b0706c1121100d0709481c00038020000d001020041601a207503080040e801076040ca000050b40300c0b440d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 44265858 1250 44264608 44264611
    0x190306080a151505060309060106030c0f080f0c0c070e0a0f02030105010c060506030c04090b060f030106030816030905040603080c0111090609040b060d020a0c030201150b0a05030711120406090509 86
    0xc1c0310344640268002c0401c0248900c2d1088802500d2a0030085082d07100d80b00214003918102c401000290702d0100000d05032541c65528504224064101c1030b0304581150440c4e1304500703007840001c0390b581c0e584d094078058007a00400d03101506c590301b40040e035210b401d811140078102d031980c14016445035032112008d031700c0284a5a07001650301049880490310940c881500a54010181d0740c186017a40002000e4810f0315038140c851400007000c0c02864035103051288607503041500240800751031a207a90140d0301403a2461500e444065143c0c40400d0b00c03940301c1c0d41c081d260090081203820340340d00b4404c148ac3c02011045e021980380000c4c0c51654100c6009458811100a08651074a50070405100c0907100001380a50001e00600100302e01c07002c940081c12200d48107658412480d80c0c1c4d814002c0c00d486008501240102015006100ca040300404807001e5152508180e6629107454004031001d58028076104010701075100c100ca0034502581c02402101c12507a600c92000e0b13250010481c00110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 44267108 1250 44265858 44265863
    0x30801090908120403020f061e011a0703110114010605030f070206010b03010504090501090b0a0209090114060306010f020a0f030906030f05060a060c051e07050103050a02120403030e0307020303190306080a 90
    0x206104060340b0f41c0d10948055072140c4a407041e61780c40c4005075a0707603140c010142c03864500a40880081c41d095510a0b03040e50040220540507110183c1c0094003031180c2c416014064201305003202150b034200004d41200c418510984c2c0580c0d015a03444100400b140c0041d25800d108528450208403240d2001070380d00c2c10b03522100780480c0340d640f030034007004010803084404840d69504d9041c41c00200c2d00c0102101d2040c1c0300350101584e6400000100000480143c001c84c801c5c040014420510340c0f80c1c3d6040e80d030300060a003400010b10f44024001da1070044207000080113070560454490404d17900c42622811110345441c00e000640140c0e11074016144200d134880d0b00040d0000c02000030b00d214080d2890424000e02c10f489419080d801342d00c400b2240122000c1e1154071080c010081c07968180b185907440700c0e800c2d8007142003403070f144141c4002000290002d010141c07520740c07002d440d8905100b280d030999030003004c5980c1d5260019140c06101074914030080445d01c2c180c40000d00610103e544c054159 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 44268358 1250 44267108 44267123
    0x2091302011d1201060b03060a0f060e010e060702030a06090b060f18150a1409011a070f020103061502060a05060105030606070b0a06090c0809011118130b0402160308010909 76
    0x15549030401c040c03000311042d156004070754014400c01c90300e0a104041c09001c1d00d1019681d286854000d00c00d200c01c03154490500f64000010410103d94030009400326540c0134600a80101c9001c80005c01501440d0b1000c0d5241c012011000c0400c00d0070350000200611502c00143d01c2e66444040111b40d80240d108150001c2050f55441c01081c13204004030340c442c02100301c0080702244840030480f40c0c1c3c41c41d0444801045050341c00c3c04076141507542c060040ca901000c0c9480c4e0b544850908c1000e01403044024141d500300240303101103a010b60480e070b020340300c00046110b242c0c4001800940d00c01c170503a0313484003062905022a2155214030704580c49590007400c2145843e95558848240d203400600e501541a50303620049104070150246481d0f5a045a88041300c41c24540c80c42030071546010007014990108018440d9100c0f161262420b0140d4129005100c19980c03000d420083e041c20040194007610000e00900c00d41c0a1488402c41c00d0300a60710b81e1190b03a02c4040220031a030140b44060700c3d48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 44269608 1250 44268358 44268377
    0x90b0c07061202040305010c09030501050901111c060b0a1709030c0604020d031e050301081603020f1903020402070501060303021e06040b06180c0301060f090308160f0b10030209130201 81
    0x7503018480c003840020300440010b241ca42c0e00d440b5503084032814030805001400d40b203c00c1061103800d0103400e8100100000030070070400d10a007800381c20701c1001c81c030030400149a080040300302c04a511130801000341000c469501c1d80c84520040030380243c22140340c28035a0001c041540203030004142e41c9008030440091030151210303002c000200c0700350f103401c80c10030080201401c0306104681100f81d01c000c0e25241e0716269410180341d50304080c41c086014034165140401000542c0c0c440c1e140000b0000213852004030245010105900140160000b079046800001e1702010000c0550000c0b045900aa090340c054010364614074800306580040104290710040c0800d02040030024102c1d00002d005054a0103041d400006c500d21201c2100c3c0503031ba615006c0010040c141d00020704941c1c00c0c030140b811403111421548c07595183d010302011a40b03c0c03a038500c455001c002200008061090308890341d80c0e10361510040e4040704601c903020403030190f0320340c1012501195001e000040c440d035050b143d01022 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 44270858 1250 44269608 44269619
    0x8030105011803080f09010908010e0c01080a0b0306010b1b06010605030a0b04140f040c050a0303120c020705030f0601091404021c030509040606030b0307060809060a050c121303090b0c07 82
    0xc0c0d0410b1503101901c0e808080040042e1551008003240d2400034515619004254000b405402d813607445000540d0404044c091084804075079041031610908050407a500d95192003001000c80c060400d4043c0308440c0042450b99008001d0080301c102c401030003452141103007003d6100c40c0280300f034601041040c0041591004680c00410b424600074000180402000120300c0c1d4108041c2c4100740700c40050010301060101c001d003030001410007524030071005465684c00804407402d84c5080e041041d41e0300c0072245007500c240120340003420020100c40d0070900b80880c0c140c0b00c14080c0301e0300701c8003441c19600e068084d642010b010b10460f0000e24104240c90941900b4204c00f840110881c1004800c0014100d180c2c1d85100c0c0358007034210fa950000741646060107140c5444c0d0075030000c50521450204100c0ca440b40090583d0b444034810f01c003c59036803a202d110308882c0c0611900c841c200b81d00e00042004180c400710103c10b409000340c3c4c8811000e503403840340800328812a0420703c40b980020406000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 44272108 1250 44270858 44270867
    0x11040c0e1c051501030b09070602010b1813080408030c06150105070f1104020d0204030c0504050606030718030203070603021903090816020a030503030a02070201021b0109050f040f0e0d0f030501030803010501 91
    0x34080c00b800543d12081440000c030001400240c204443e480e01c0c0d4410701c040b05c40d0400030351011f401e10380000c11411122a0028003c6421103804410b0000208006048000f805090008165000480a031200d0326110f00c241c907a008846552141e10801c0c002a641c81e152019075081ca45040c0c449038039210030303611080b05c01042c03204240d5018490004103e02501c0d02d20003000032017807094005031640c2c103500d03103080d84110950000d0311440c145828231000740d460400300e0f508440181400000f024882b009640c2c1c001d265400030758107020b54000000c000d034164005181580c1515080540b140f00711105a049803114000941206030901c01c5d943c1c4c2c04060940c480c81180001c2c070343e2607229500d070f60342859a441211807078025a0040b42d14011560100000c080c540f00444201424410f01070009041e01c0b000d10449119219080b5001050303207072548440300d004507104090103c28400411642c1d12b0821051400002c1d000860325285035100b8480d0074140c95001d003030b807461a407a0000446 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 44273358 1250 44272108 44272159
    0x105010b0d02210106030b0102010c020606150325030f05010e04051b030c0303040305010f140f0f04030309050a0302060f160806040c02030c03130f0504050103050a021002160311040c0e 81
    0x4000d010943c1c002900240355a075580c0c005c0961b6a804180240b03494002401d6403c06000074043d54464801e02a0300d5a0751005182c500f1120300c501d540301e64502da00d07900352b4074180b201c1c00d181c00c001031460081c01c3d502d9000701d110b10a0000003131020703076650f500000c1c0108044502a107140c1040c4007602500c0849910b290a17444020201c0d00080629800641194000d6104031096950741c0072408034107010380580402c10044480d11002482c2070458058600380080c1b1000700c40d500200002c041501a6100380402c0d6000000c541c90f04101d4600a90740701010b8400081501541d4001340031708115400c10300720024036507990b0350161101030511005c0d0045810f0002913000c01d001d08485400c0c04c00c09040d86c070b00020b240e4110189010361007042e01035540c0146000e43e0402d0018008501c00050303032403400f503054420058200c6860b00c01c9007000040c0e000c0048141c0080070010900146243c1c42410200c119030403c80c000c2c6100c02a0344910700040c03169000404d182112410b608900d0450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 44274608 1250 44273358 44273377
    0x16080303130c0512100b010203031e040317090a030905060c1509071d0a050a11030402010c0c0302041104080610050306040f050102040b030708072c0609040902060c0114090105010b0d02 81
    0x40b0101c0d150000a6403000003030342c110310298402451104240030318000c0609105c001e00145140d802d2103a98442110800300c10900c43c09030000100d810540309442070403a500e030310b80c40c08905003408541c1c648c6441615405400050090b000417800c1c0c505181103501000c10080105a20450102d2030b03614160000c0110b00140500c000024075280c482c90103070303269a10001c1d540403d2411643c1801100c101a03ca186010b10700100e0100841c0d01504407900550242400164290710b031800d140100100d400007034001f8285050542d0111b00e04014005031020750b02504c00644d51450385284812192003200ea140c1e10039408207021640703801804180e1401403002524294944001c001030f5031098604c100019462800c0008030795100808404601580c1e507031210350701071b441040004030b0b01040310900c04c850001d0a056036549544c000d06844d94041d007115103c179038a01169008112080e00e11041503c0000046d0a10b0070610070103040e02e20a1400381e0504014541c6071000b508094080b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 44275858 1250 44274608 44274623
    0xf1602030904050705250209190b0a0906050102071a030a0b2106010e01091401050111010605130203010f0b0408100207060608011a10030b010804120c1a04051608030313 74
    0x2501c10761514061144030703e8071a01d840d036a551050800303502c05085c070440c0e0140003141d01c403a0f000581d600f4101a412502c1c51548030290f00006060100905501c400503078005d4183c3c600240003a82038120f401168400d800360344903c1c0d66030000c0c0d44503003900740345103006a0701003002a440c0d1500d07030303c01c8440c40009070414951341e128800c00c02d5110000c0c0c45500d0142d01c142c004010380310700c0480042c054054004180801070242c001d0040d40d03881070040c42e05100c0c0300112021621400d50110f402002c00801e807050b154218142200250b100707003e850441071451030045920100790701202c04440d4180c0091642c102c610204070000d4201d00411900251542c0c000240b40070b09006000c1d103000c1d10340c28008034003200001c20020b803540c0c000100a1500f1700104140b56070b04507100c1c0350b005810698005082603010170840d030000408070001c140c05401c030010407100e10242105d40c412172003002124100142c8410861014000c0c0c445e044d00da03801000000c80d080c2e142c04001c5d2015108240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 44277108 1250 44275858 44275867
    0x3060e07051201020d20180102030f0409051005040b060a0309020d0215030901050f07090b0702060408030a02100605011b0809030f07061101060914010501110c060a0c060b090f160203 80
    0xb50200082180c1c1400581d000309000080d026540700d51038002c070951000100c40d20310700746400d10501400180950f0307210918244000d40c2d00070300856941014520a0a50380d85d01c0700740703207001404141c8a81c100c144ca407080104103414548550503101c0c03c0100360300d09055001004078081e0004203801c9070030072030b0900064016221007899240c0b8000c0001c0340307502c2e80b1301040388900b1140c00a21850030b640802080c4820150030544141c00d030b03044005103c1ea07401560000c80c040c2e01c030390380c0800c015100001e0118140d590104108180f0302401c3c5003400425502e400440e400c1f484507d141031b11080d0900c00f130b00040c480354014070300d041c0701030103803550402082602c03828605a50301034004202d4180320700ca501c803c02e00c55800a80542081002016102c4008014061050040ca8188800c104d40d01129000070452040343c15801040303d81ea44d10900d400034008103003410101d03a0107050203a1041d103443c2c51207107a4412035082c030100e004c50781d940021590b01020103c244003940030410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 44278358 1250 44277108 44277119
    0x5090f07031b05030402090a1401150c0b040606031202010207080d0e0a0c080714040e03070201030203040203030409050c0a0f050a0c030f0c022d151c060b0c0d030c0c050703060e07 79
    0x2c0302c92100c619845041d01c0e49860f00600a50312801031403046141d01e80b403607030701c0000c044407011815541342d0b01801e00c650016903801e07940e1100804011301003400032800c0104002003900420203691042520600c0c1c2c1a1b0210141e0a0f40a1481d006181c1d00e800d00003030141004a501c4020103502c1041110300000142d142d10340503201b10740000038103802605050090b80c1d0900101c6a04010075101003182c0090702184a84a0141c0348000b4101a0000040b50656904200380d40c00741848072030801482c04c2ca0810800d807507200400003c0481c50038000ea42c2054040c400344c0d4084d43e0035441d1640001e500b0380c1c0031144002d403101c0b92414424600c0c082000b58451140311482d41c140d407016401802c0034600f21f0020000e03020500e510641030f001516013034044807001e80e8254005400c42d00307480070546107900040c010b0740d044401015004100a0340e404070000785802c3c840200e4030100084c0d1b40b4580c00702d45401c40004040c0c0a6802444d00704002a42c81c0d10504012078898240c0c1c1d442e03138642 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 44279608 1250 44278358 44278391
    0xe0625120207060f0e0a03050702090402011106010801050702100b1008100b040803040302040f090503041802190206060a0608010f120c08010501170705010503040308040807020f130c02070b030105090f0703 90
    0x403d403a6103540d9214400074003d184203203100049018020024414243e0700201030b0322811500078003c82110700843d0842e4000c11150032403071402e10649042d582c50b0781c02d00e8000c15046440d1801442000e030108a0226584203c211010b005081d094060700c00a0040d2020000a4020001c08018040004909501c4e82c0944003504c554805151384a24500407c4295000780340c1c0b00072440e252a0081001030340001c2104c0884403400c0184080000c00100d000080c0184440404150b09545000340711b2907005c01c000303124240c03c070b5818181700c2c3ca8010440350a4400d0040000001c0701c1d00c0103100c402c41e01007c03104064854210070721201d071101142c5095071003e81c4207540b154105c030b00117441d1020522112001c0c100a18041d8110310713081d1001414410082d1028042010001c0e0010540d280c1980c2c140540c1e01c05030408070700303060442c1c0990007400700d0020303d00180200d42011540441c9081102d0484000074025880d90722400c44002e1114006008d650a246c1e4034201146a04450f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 44280858 1250 44279608 44279617
    0x30a0b10060e060c030a0f0c0f0c05041b0203030c1b1b01080a0b030303180a051e0c030a02030a020105091903030504060f0c020307090507020a0c030b040302010e06251202 75
    0x2241144100501c0c0c55000b8000c0b072021800305204100038070401544002c000195010310003a407400110030f020400c015540046c00010242203a0314840440d01072000c244100c40803030304280c0d000c02540419400c60346011004104010040c1c1040010504442c003503409041c1c071011001c00181d41c140c943c00390038605400b14880035005542100d10000642c0c0105140c0e43c4003090a03000d002c0e9800003030004c0d880e440010b242d00d65590519050300c1100004120303281c03c480c1d1040440d44419131440105810300a6070f20b01c101c4078425440010503c0c00e000c03801815580d4003031700030620040070341d00544480e000600c00e00e8010680071880482e080d42c103501403000310b000340c54840c1c1e980c1c10450001d05442450b540c640c05e00c403807604880d0041e100001c10001710350030084000b46907215a0750403814000c0351a006000090506004030505c0030010070103000e43d110750020001e030791000c0b80158170380c0340440350510101c0c03c003840c018614101c2d00260306000c00d03514111402214080704001285c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 44282108 1250 44280858 44280871
    0x4020307110a110111060405060402010f120507020105061c0203150c09060d09031b030203030f09011508030c0c040605010518010306030204020705210c0a06020c010603081b010501060e060306010806030a0b 90
    0xa6600555083e540c10803100030301120040003401c882d2400762105543c9080240c4001d0401079100e41103a00c2038452982d10010f50003e400910460900e40c1c0700030301800f029502c0a2088034180d914040c9400031118070303400c160307000c0c0c06495a0081380c0d20340c1e1440301c80186608100c04080202c0c039041c0c0d03608802040c0000c01c51400150f00311071420002c04100f0b024003402a02d5509461400c00309030000207995205413044004c5015549000300c0c6c3e8098218000716900d81081c1c1d04021070b0440d0080040e0800805140407250b29203010070400080d1401c6100b400d000ca10104005640c1c50440401caa507a070006060101c0d00b80d0b0b913980803a04a034000c2c202038512343c201d801c190902c03000e8400d8a034a41c2e140f43d9a842d08249480c014580c981c84514001000e40760300040060f1003400079004a0000e40e0460f000a0f101c00300e25007a510024200712090340c6035482c00c03001081d814040e03050a07100000191141d400e580d62013005580708040942243c0e414490803081100203140400010700c42c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 44283358 1250 44282108 44282123
    0x4080d05010308030f0a0203010605040905070908070f0603050a1401120302031606020c100501050114070501090b04081e040602070308210103061512050303160c0611090f0f01090504020307110a 85
    0x11745030426108050014081030090785c01000104051365014040c1c1d0190740c440000061151503520050b01c090740c0a03805012180140700c0c0003e104d0744810142c0e0308480b019101401940c0d550140301c400c560403081800042d420300c800502c0300d84180303110000c60a00c2401201e07d0000340c100d024803030388520a0215181600011541201001844004048540c040c4140041e5061100217003400c1041025440900c03400301d00701082c4602508920215500006070107054246810300c58010391000c8081042c1c0d03510703588280180071145c0201c8084520310b502401c138550441e40c1d005119400b0121900c0300c50040d13036040b41c940d50b640f10054000c0d40300d081c00003004500c030055140038510359030103001c4d4024901d51034408150040201c1e544415501c0e87d41d4041c042e080010f0302e940c4031420f0050400ba190401d5884010b40308401440300e000110b4000904c0c0010808002c101d0310204001f81c00101e40c042e04000a05190300550f81000b01420404010480a41c1e10352811100400541d12a07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 44284608 1250 44283358 44283361
    0xa06030309060309120e030a060905030c010605180c0a090902190206010b04060c08030c0c0d090806012103030b13090305071109010b16051006090b101e0804080d0501030803 76
    0x254120541c1c5004010038101409019001c0e100c00c40c41050001008007401003445840049503424070440e182594003110400100e07145080042d5240c00019580b0340941c60301001040b985008034400c201c02c0c0c0f02d42c0400d1066981e490418880f500301d05400d106010903080d02252961150010f03080341d511024414210f00d0600900901e05081a4800c2c042000100030500011f98000e50600007030760032450241e030b04d440741240ea840303074400c007608075202c0e0013032102c0440200d074480801011a0780304001c5030301c942d8844260f041002c426400654800d9040040d01002034000c5c0c003c0b69420f0402444000d003a40c82d0400b41c000e4868050741100010000942d103020070040c41c02d825454101501d03002079542c14203003540c1861180101c00f0302c2c3c100e070703a17011a0100141003007007080e08040a2000d00042e41d0300c0007600050044481582d1182600076609031059102e0000e21003101c5c034050038003a83c040740e004140d950050142054410641c100302201494485002d0755008520600740240d8032f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 44285858 1250 44284608 44284613
    0x507020a0c090605030c060f1e0c010c0f0e010807020a0203030406030e01140402030a021903020604030b061e0108060d0f0803041a0702070315050c120405030301090c02150c1c02030a0603 82
    0x2165001e8100c51145840c207442130205440008507804444005d0720180c0d6a20350103000700b082e0740155100000107054407050030b40d40d0914a0060500180705130001e1140c622211020750741c00885c3e6503440d002400ba003210b290558481ca038403503041012030040d201341515a0300401d0840e4069041000407a8032100c1c1d00c800d01100744600c1d034200701c00fa0b51180c502d0401c0c1d80000c0d165490504040d1251080340c1020400e00c2a000c0440011940200a56602c07a43c0749004041d01d14116100d0340318400e07205801d884411400e42004c240c8205948819041c1d8601c0d08110040c0c1c268403060321245c1301e03c509c00b00091a003000943c041d0340609900040c518050004508002e00100000c04641000208000007000c410002505c84490500802d0503a41d480900000d4025045445600240c1034107010501c203011000318140d5078002414050390fa201c5070240d9580d030000078480494803200c00080e803d90b81c520094109a05510086001001d2440c050b90130f0307800075140d40e82003981c3c0391000c204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 44287108 1250 44285858 44285873
    0x9051006090e010e0717090a02010311031009050703020403021201060302030c0d030504030305090616150b0105040f0e0a090b010602060601122c070b041e090504050a06090302010207060507020a 85
    0x400c1203103850500e860411002604040d018031a04080e684040c022030300290040154400480d03010352000018540641ca01e5500e40c03404c142603000c2440e05903482c55900c0c51b03100303c030f211b0350940034011000c030320303041e4284d0043c50010080d008141d401c1c0804801a6112581d02114408520021035494214010181030000542070107202d5050940d0880000f40c21800f958100d80e01803c0854560310700101052140c41098501d407188607010340c0c10700c10081c1c81c110300c54211600312820010300b90320b54015252417159001d0403190401c0f039203040001d00050040b0907805030750302c40049450700041d03907a40d0804600b80c1282c0c0140c1c01500800038156805003a124900409042c1440a8240b400c506886070500308007106200d900040640c81001040128a0052003003001e92a611560b84900c0d501c5032403105405402503805003000903842d062401414002e0750094080c19682e071065542d4001000d1070300d0700301e055540901c00840811124459103202e000c407074000c0c009658150ac0c00c0750 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 44288358 1250 44287108 44287141
    0x60225020a09050112150b130c141c050604090605040b0717240d0506010602010b01110c01020723190602011803080c070201110105070504030309080309030a0201030f0e01060905 78
    0x82c0149014010009449480d10390303062641c10030025080c443c801d008220203440310380c0041e5041450180c103820000f04a03800100d45010682d00c0300850101d2420305500742c818100807451022071200c81038031051040d0301064010000410010f046038269580c032040d01d1045606482c40d18410003080400c58106040301100e0030361501d25012803900c015881691000418000350888800456401907240c410401c0c1038140c001007110703034540c2e58000c002c0c0079100081d580350000e030b141d800c01d00d0345500004840e003820380141c01030141c890400100042c20310502001014a0105400801300e580320045044400d001129510207440e08007030b00a402d4694110a0008071709042c4c0820011940c09200c1d02d40011000b24803c1e0383e01c0b084e00040b648003d40c410020060f510700014401301d10b030450000d0080b01c1c401d440e007180d120790f00c141c50740c0c99010303085200780c1580113a40c0c12001507200340d0254810300c80180c80000e050314550005400c44205400c10031115558000b442040001c03603149a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 44289608 1250 44288358 44288369
    0x9090305091c0f11030c04150f240807021009030306091d06010605030604091401050405120408030f0d110c06071103090114070302070e040f06060b0a0804020d060225020a 75
    0x9400080040d500c1031a010302c485006011505003104c20005603a05100c1207010801c024400e00207902e054079460042c003850b1080000603000d81c10001602081c444c4d041400355550300c0848060865000240c40c102c400a00060441c0202001c442c022880340c810a0a050300994000441c0c1c0d042010b0142180e01a420700d02c0070003103201c2403e420040000344141540c0f02d52810340e80321b0304c4150110b400303018905170007402445842480c3c1a00003056000b507200c3c501440460740d400030359000401151041c3c1c080e80e05590401c00040b504109403000a0a5240000b080020204140c03010a081e60f0070103d03080350190014000d11114a03801080322940350f4941020354900114540082d1004007000041c1c65025000302d46403041c1030080c0806c80c010000d520800c0940c1c500382c03401d0b04c0340300c841038002c070362640c50003801040c004100020f54400810740d4440b18403503203c98007000300a0840c90030840d40d45800304000c4130f4090001d1140c40c3c0a520020f16800c0c00444c0b07104000c0103c01e1078201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 44290858 1250 44289608 44289649
    0x30504060609110d090303020d1103040506070507030c03030b0607020423010504020901090e0c0c030703020d080708010f0303110f0706030c0210050610050d020405040203010605090909120306011103040909030509 93
    0x106101030300c640f00301c8480c1c00d5a000002000d0a030303071030700390040d0042c814900003a13031406c807030306800c90342902c01144224070500c1912181e03039030307034034207451600030300902600260890408034006402039010140000c0c2c0180010306100095001909072100750703400410910b500d001c4050440c0a075080c103400740200312419810000030400003460030000e0722850030340b184e01c0e00116504503c0b501c2210b4000b090700c020f40b603070390099080c080d42d40e6601c000a6000249a000040c404502c03407287e083c1070350100c80101580503c2c50701c0403038113021107680b8400d0302e0003081501d140d914020001c0340001d0905480100e60440004070190600b541c034078843c50241e081404005160340c641d03864104a60050401a4862045462040003070040b50801c981080c4004004901c031604403000e0041d8247c1213806007000e9541990761303600c07008114030b1260700e00c40c1800880c81c1c541c014090108403800c0e00003224102a9a0325245050b40d1585000b980840c60000b8242c4040c100602283d114580711101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 44292108 1250 44290858 44290871
    0x150512070e1f180b13050903030103061d06010e0916080c191806030c120c03030f0c2406061713060b0303071a0a0b01050f070302070f06030504060609 66
    0x380221010801096801407030b16880141c24081614120203016040350309141c114101010b610b40700400c01060b5091003110404103000141c460303405035502c135450050240d4150307440d41e510720024140c84003051200c1c0e44600d421060081c81005150300800f150010b05060f07040c410b174490b0600001d00341075401412a0074050017403410005524030030329015201c4003a800080007201c504080541c00c44201042c2c84607014518840d0f07074001c1d000740ca00540f82c1c40e003030541d120046610044850300c01441c141e440c3c4000c01c0801d00400d0311440324115402c01c0050210540d480e266030310b40e00300000340e20714522010100004428400c0c4400f0308664181008500520801d02c820a140107040840740d62811030440100b2110380c002c070510340c101800b120345401461a00840144100c03074200401d81000b0002884240203000e4485d640ea0f060310384914001000c3c00001e0b02d40d011103410f409600ca15003001170040c003201195070051040341e0380014581801d1610a084d6842c030b910142c5000e0a010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 44293358 1250 44292108 44292119
    0x60402150702180612100b09060d02010c03080c0f0d020301080c01080421020312010b0901020f0c0d080c0f121206041e090606080d02070302030c0d0b0105060703020f0115051207 78
    0x142644181c0380700540c1050360354184c001920b0204c8400f95001a010f42e1005c111301000c03a4029901c080401c8840100c00e03a1400c09003d9500c00100019000514007038107000424001c00440e9000303104e0304055031401c0c805500f64681d5600144920041170b80c00001045820002e02003c4512042445c0510a504060310f54090903000d06081104800c1070b410400031060081003120024400000029025a540e11144460f0b80048080b03a0150051182c3c0900080f8086110202140d00800d44d20540b42d1079128400d060b00080d10001e40351044025140301035508009a900b41d03004800e0255582d0b042c030002015400000d0103090089c1d09051414031207482001e02d100c40e607154003800080980e9581402006080f844e40908a18040c40c0d4141c40ca2650103d01942a28020303011203840a12007014050204007608024001c03410680c0140042d15116000382400f41c001c0c8101c9130110082c070140743c21102c07811a503400c0b2a01102082245007490791030900846407444c040c00005117042c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 44294608 1250 44293358 44293369
    0x20c0304030b0901090506010617070309030219020f03030c07170703020f0d06140108030c010e060c0405040903050f0a031a09040f060c020a0b0c040e090a1707020402070b0405060402150702 83
    0x14000100010b2800300060300c2e242003540720708804d54105d01181e082d96035404000c1e08201030390030103a0305030200030b00064200d406030040c1c405480d850741c01000300c04061103845091010040049901900480d40d040c15950b080010f0b0110880c3d02d00506107462a1807000508440e010483c0f500a4105074400c00160b0340d40e44400910140651316289944044c0c03038801c0c001c104e0074000c03e40024070300c0c001045051000015000c04042100200201c840d190845c07507035000304403064510480300300801d200a00b065085070201c00d100342425414019524955090b90b084403103081c1c00a0350340c07900c000c0006d10b841c031401e400f86001e4030205002c0c241a00c4003000c0201a18000d0038241d160300c440000300e40f0070442107001c41c0d0421545031950900c421019040e503c1131117100105c8001101042200b8408180c441440c0e9020440c4044c60385403002032801c94010410a2764015070078007005002c24180f6115a20031440b642c0505801d1400f4410021310b110072070081080e000041c40030300c0040c0c945 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 44295858 1250 44294608 44294617
    0x207080d0309030c05010203040b070e040b0d08090301061d04060f0203044709060702060601201207062009060d0207020406090c05070501060b0f0a080601030b0307060e090604020c03 80
    0x5071501048004060409841554851400500303a40c400410801813203800103106000d80941ea50342001076000f0300401040c3c03150100a03c1d0b01c03912801310000041c542a0003851424009000440c41d01c1e80c40343c04612542d400040220944213010800c0100101e601c00c03003949040000003141981402d8031100000e0b6082d21803c0f00508528410100c1c00d00c0c14040d4035481c01112101c5520030608044180c02030609861200d0544034031000310f100e607400424054031440b410783d2410419544508400805c229000400c107540c0a4a207402c50000000c8004000f2680185c002144d081e540d9030019100c500803142c0c109202c11b050000380402c2da100403c803a4036106a101c09a01d403640d50000800415240e4001c036800380c942407503210714540210141440501030002000b40f00e69501c0700d00c60600c0307440007427184030004101c607101c0140602010764202d5410314001404000a502203413078075207503402c0000421036030641c28a4524000b040302d58005030680b03040d8185a12079105036500e004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 44297108 1250 44295858 44295883
    0x60807170106050306040e01060302040c0c030806030309091f080118120801061e030b06120108060a140a0e15010b040f09200a1202040b0306040b0405071d01051204061506020708 78
    0x884601c07c81002100350840c1e0091a0018800c0021803050300000d403640d52000d81c1100410301102c00104503142c00300039035814200203031601c185e41d541c1c0c4040c3c0c5040450514507900c8400e4480e00840c2151003441001c0f40144d40e0745ca00f240c103900c41c2c00c0c031020034011a000441000086001401a0350703000d5500345034805072100c04908000803038401c0d030280100ca00000d07040180070840032070605c045070000d07040b81c1d40c00d02654002d03101c10700800159092100083c22a41000b000f08020f81d03d280c3c080e40414400000755240b9640c071400d40100d0140a174408401100c002c1403c1c00f00b144040052001082d40030420420380d0b400e080b1804180809003420215540c000c00d0440308240110301c20312440d03504000856480d602d4145502c950340081c0e07140341c001c0c0d151020781960341c18640708032401040a80c07103180070101c4ea1441c805250882040140c1000002c2c000e01ea1600815100300703000720301c1145d0100c1c10940b44408820000340552040301150f000020401c05038002241c030110522 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 44298358 1250 44297108 44297111
    0x911040e0102132912010302010906050f16060615030c0801051c08130b0a050c01050601090612090203010b150702030f1606050c0109021005030406050703051506031f06080717010605030604 83
    0x7060b41480707044c403140d4036100c02d0002d0800140c10301c2042c21481100e0507240300745c0382e40b0003690315004102d41a001b4009030941c54001002000545a80004a60245482144041a007a44400603003181340d481d07080300d5021039210200e8a1180c1c2c0c02c0030b10756014007001c0d07a0604000e035442d0180c2341421081c1c40e01a2441d08001948410414012443c2014188a010196440084546c002c1c0b4580c48811800c40d03079460035010860561240e100c641c111041c540d04e010440d1058254030006160303446081b6495980c0350407805a0b80c0714a21f002c00403034a03540340162100c3c01401858100704000e9401d031703a40e4001e201e40118a805000c2031400f82d9010303140031600c030700c03907498001d00502c0142400303544a1035a00e840f480880d03104008501c1a4401c220a02590f00c0300d0350f003074041e110107460038422500c060f000c2c900a42007000103580e201040c11640342c0341c1d154554804045100342d810220000b180c0a0411a5064200014204104400c60300b202d4562400b01e00070400d010240810b4406d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 44299608 1250 44298358 44298389
    0x403060f020d05090607090b090f04150e070c0209010902040e040b0a06030b01030602031f050307061101020d180311030316030509030c2b030204080303060d080d0911040e010213 78
    0x110a650581c0c03603008a02ea4100550f0800300d81040c2e07900803c80e0003130b0006404080110340352400b64240d0302d0001c8080e003072100d110780b110304210142590174500d540d514691000021a1000c0446a034022580d540314000c080d003c600603c42000b1058122000d41401000100f0100c4084c3c0300f281d03401604030354000c2050300c810301c3e15400b0304540d41c006420740d2a4580007006000d01940194000c00c0d280c146403281c69840ba080000da45a140b11f09a0726400880382085040d004046189060503540001460841220400e1044503842d80000e903214a554201c2810542c210690050441203000154214909907500c1400c1200391800c03041015110008030300d00150400c00d1b190000600c20a6942c5c01260200c0c0310450b00003851442800740600c00e0004641c0d0280c401c80d02035030110000340d403640e40c4810501c070b005055036000f01c0f904e03181009254510100d03441081140c600c140e0708240e13040c03004010442618485400704034140d10400c450202e50702c0c440705c00c0c012030714440084000e1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 44300858 1250 44299608 44299631
    0xe01030f0212031204080306130e07050105030a140c070c050d08040306110c0109030f021b01080f06190605040807060e09060f040b03070e010509090a05030412150905011a04050c040306 81
    0xa500520142d13143c8030000d82c00740401c125008024601c10881644c444030f9002c103020a42c2c0903184020f29821050f0414541031042e544118011541b145030380c440400c1d03101c00000740d94881070044521010117813012a40c08100415070000c0002414204c0c4c281392a100302c3e0b03ea03112540b0607440000c01c450354600700014181c1040040d980c0c034060340d500802041c8202d040150208002c4000c4c04014080d130700030083c43d014070a0040101030700685d607105250351981010081020701810743c41d488442522002c036050b0001d602d031b0018060507581ca0343c5072450161a149000c8954100209024952994401075200d840060741d024000721400078106450101003401480607050f040c0d0140504103010410605c1c1d800054103c40e020f8aa41c5000c0c3da91105103a107030404c02c600102181c0041000f00a409400c1032441e04c07050003801c03e00326006460078680101c0740311100c200d403244d4481c01481900790b00c0103141c4015000a540a128526021640c0c101911842c0001040310341c0e59000303400c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 44302108 1250 44300858 44300863
    0x30607030f1404030e0f0913030c020a050a170601080606010f05030411090c0705060a022503050c010f060e160e37031718090402040905010f0c03060e01030f0212 71
    0x2e81584050322090309040c04d04000f42004850b030140d500400c80144690103d0600d504080c1c810303242218030043c0381038180e80071284520000382c1139a002c9a011008075056480c0700400c801000c160410078100c54200e1203d500b0403805070b02c10f084c641c00c00b5041110070f1340c0160b411258016646401507480d9200d25100c2040c00d40b011085800c02110010007a1008500d802003001a004034211504c60b669450712106920038040003214080e0846448035a030100c154820904c281309007001c80c107280d1101c048a00311104c2048a60f00300c0c2d29003904006090010b6101a00003420881c2a81e40050b14100642000100003105010b144003000d402401c55583c3e4402d612136038081100e18144c1550540791100e500301e4003060360200150b8080a43c3e80c43e1f0030086030f000c001000008800b82c80c88404100340000010000d0703070040d80318200c2c4d2000400a01c141f01105901d02000541c0da08003801c014116403254000c500010441d000500110340c88140c0c111040d03604490b09200042c0b107413049070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 44303358 1250 44302108 44302121
    0x6030a0e0601030501020c0114061c0212060a0606090501051306050a0e040e06090115031203020a0507020d051f0608031e0f0309010c0e09040f020906120d021608030405030607030f 79
    0x28114060207001108120040d00140030112241d002800f12008400300300449000c1592035a52022204411402030a0900201c1e0303406400107021805600c448007415060441c22540e41e003020360b44200500c445608040440701409003883c20030704041d114030080f4401d030031600954003400404507030802d00c02d105a902e0104000c0240c41440084003c14207256a0b130360071356810035694201140410f014100c44400d0003280e400c800a41c10100404006400035031040b40d0003400c01c40c00300300810241c1c48142e1010803852184004100b14410002c10002c400c2d6651820010682003050421803c10000203540c407400114038000c1d00b0030022004900a48104080c0128407000030040020a01043d40328203580081034541070300043d030b43c004100080408443c01840700d813043d81560050f05100c0b4050f640004003400b942400381120518900e00b91401400d0746c0140c1c800b00310486008410700241c402410724400450800c0d0070100000d49411006100e44201a681e00102800380c500c1c0c0c00c42c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 44304608 1250 44303358 44303381
    0x3030b060d0207022407022e020105040510020309070e06011701030809150a020705090c04030c060203030712021c020d0908040b0a020c1903081e030703090618020306011802190201051e060102060606030a 89
    0xa88001841c010301032b000e81021a0251014017030032007180000c074070314000c5030b1050001c000500b100504041c0f0f40e00e11040050580b42c108143c0a0158010125002441e8080c5009003d801d0700c4020305810031080003040b0300c40c145004001e002c02d11501d500040c1803c00d940d011039000c03d80b99038000041c030301402190b2024003861158840014071076000300003180101030b0382da5051072515003181e11006038814040744c1f810103070a070038152001610f107a0180c4151045408085140c5206440b0701c581c1c2c1d0403582020507841030003d00e40f4a440c0c0c041102d41e412500a99440c2442c040156444810610724840a805200c000802500d40204400146145030380f40b018cc90301c83c10070403001401051414011148280b5041c020382840c40c41012124060364001c00401981c1e00384000b8590b00c25000b0361000f1f00030f809120078100d06c80d280620100800113580001081d20301801808100807141c0003d14a50319848103000710350740c0c0400e03420351000082d92107079682d0302da0402480050102c003900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 44305858 1250 44304608 44304679
    0x1090c0507020907030e0f0a05030708090f1513051807080403050f03070201050f0631090204020711040506120c01210e060f0108030a020604060903030b060d020702240702 75
    0x412240c05d415074050300d840540344003182c0f00c01400003007080d5111000300d40a0007a41c0f062148400040c0032000502d41500050041d90001c1001e10100b042d0041c98201050b00c442d01150340018541d080c1c0c44080184000c860b00740f1080b00036107601c4222200034100342c04004600c000034043c5070080c000c0300c40d88400c1004807540c81c50640c41c024001c04084e1074044c00110351102003255860003c040109005040314440d1610b0f038203024000c4841440407200d44a02c0d1200c01c15405680c44d44050400c00c2d010f0051008008180340400046600042805205140c64894030002c40780020384881c4911080c201260b000c082175004030781c61700003001d80c0c02d0350314180040b00c0343c4100c0204401c5e00420603000c060110741d894006180e2640030701c0307000000507441317200083d02056640d00000c2c052400303400d00151740600c0d0710101d83c00340e0111100c09130701500043c1480031030a280d00408500481803101c505030704266244400544551000603100b0800e0a4090858080c0c160042ca030700b030b40b80b245 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 44307108 1250 44305858 44305861
    0xb0319050c0901120302060601080709050406060e030106060906080408030604110307020102090f04050610080a090c0b04080c010c150527010906050603070501050405150c0618011a0901090c05070209 87
    0x14a19640e400040256000d90520b000000700c18100048405040383e040d00a4412603580a00440e05008000c0c48201004092000010036441318401d000207085941e03944403152059400303150964019070320020403c403000c0d40400c815a400781d403803030700281d01c010703a66a40e450b0302e0000783c060001c5d481401c014000c00424000700c42d805600918825200340c0395001142100f5082004940046074002c0d0454452100b901c0c280d4030814840b580000e1031080041c10300e902e602c80f0000c0002035004003203407000019090200000401ca02d80c2e01050900c0c0c0040d0300480b681d00d5024802050020500d440c0c0c540c0007003105503e00300100340ca6541c500c544160700c03860007c8101e020701000b4509680b268501404900f403802c010851400392001a11000d01d424940303030500c09d00e149101088036450009001c20001c4c4901800640d010304a4001403a440c401c0400341e80742183c103030768070b0606448040c0c800908251101c2c0c940d64115900150002503441821038291803d1180702c00003036101c1074010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 44308358 1250 44307108 44307113
    0x303050105120a3903050606090103170903010e010f150b0715090f0b0c0a0e04050103080a0507081204050303060a0b120403110f06010b040e1303020309060d0e0d090306110406050405040b0319 84
    0x486210440b40101b0480e8503940700c00080c070145002c28040544116881101c0710b50703c08030750004000100001c0d00000300d02c030381100c00900b15400c9420103100180c0f540408000b03002204034010261400758042d5240000540d81c90042c600030450741e003105612000f0b50030a11114540700425250002c110840700c0c94004441c0b644d07980081400c00100b60342110403081410184501c0b81070320f034080c070350501d491603610098500b07410100041340c524004005d4040c5e544030300d10705540960321030402540c89040c6072080200c10201c1c4d070040d800d145000c3c0110044902c0004100750495050b0519000841d83c03420303403a040c43c00c241c0c4482c40c40d2198100000d1200e00b00001001200d0a2081000b0181c8610144070780c040700d88400a40141d0040c88100028940300e00245400510400300040c807410300850349043ca40040c0c0e04401245034a0020010703c80700d40162400d2400000d10940380c10304100002d8024000c500441d40074555074031000a058504108000900c2d103142c100f40c0c4075a45a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 44309608 1250 44308358 44308463
    0x90201170f071407050303041e050a03090806060103020315150d0213090b0102060c030106050c010603150f360c050a12060b060f0904020c120f070303050105120a 71
    0x152042d1001034510202c442141c411982554241c031303030040c0903600c3d58555494101060603404a0040302c10104c0301404d001a4080204c2e054451080d210182c5061810002c1400d0007401049a410706004204002c2c0080080c040c0d00d442a00c200c0d03d5800d41c2c0840100c5250700d005121040c40a01c0c07000401641c485503001a100c201c5104141c203110001444004989584007601c918441c4402440180070360f42c0100082c0040711880c1000082d0702c0e9481e141c602102d021101404401070303a84424900b41f1250740511080b9441d40408103180040768041d400c1220b151045082940016101800820030a01411070080c0402000c056010fa15200030702d090004000b8101c41086c0f62914105143c2842010f54a42c6544100310030300740440310701031001951080c0e000c2c0b6400d024042441160b000d102004d042103101d220000c940b603154925000e012600103800040c0b04810f00e40c044401c0420000e600822681c1c01f24a00c0301a1178040d005101d413040c541c03800702000e5071701c0c148440f01840d03e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 44310858 1250 44309608 44309611
    0x60a15054b19080403030221010509100f120c05090c0a020609011518020c06010b030604060503030301050603070c05070e09030307030506011b0204050c090a0e0a050f07020a0303090201170f 83
    0x35000c080751510306402005030b01c501c100b10030b64200c81e00e4a0118050050301e42c90b5109019003400340c03070f140302401110040c1191080ba001c000d0200e00c0140f103141480c01c20554407504a58040c46024185401c840e445031140c89004c4074461010300303003010000039180100050001401d10185402d20101c00107050304110a0400148128800240303809414040c0350118420b10341c0c89889642004003106e44179050241c4a104182c00b00143c084808040060030300800c1c9103104507031642800d004201c1a10708a500003446503100740300501540e0303240c01c01c90750000703105d08141b00c10001030301e01142400440e5010541d002510b00c20840c0481010004603c51002c580d81080150f40301c0c8015681c04e60030405450110b00406512001400d0981c420750300018103d8003141807420040008c3d61a80f601d4100080b1740c1c0704002440382444013030013400d40003945442100380624103103600a50314041c2d19005010940c496100314250f9000700300e4458480c88007148200d8502c1e141c620b01c40920b40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 44312108 1250 44310858 44310967
    0x60105040e0303010303170402011e0e01030608010b01140c0c03030d020315090c0d0c020c100905090901050f0f04171b060702070b1e040807080d08060a1505 69
    0x501681c8140c42078080708490680781e26403113900d004102607011000c94000140201d0500161116401191400308a1160104131a90f14001e08100b90b50004065039899409444981e0403c0c07168404ea0380c00c9200204601c002d200c4007a00c4000c0c0c1d221162811643c000c0491305800300107034110404e00150010362280f40c441040a012049a40a1007042d003800c0301c20b000034250600070404840426046071241400c103204990503c21034600240020010241c5071001c0356001604001e01c2c2015412036601c62079550080005240109061000d13000007080428100340d42c0001400f00080214111300c0d166035049580e03120702e114a00c00142d4034016081c4459072191030006170034030740f0001f02c0c001581c424511650038600a60000e003400c031042c2818040440e030500021400c60320402039130000340401d400818449120140240c103000e0b01505040c02003a540d1800d00c0002480c41c1c2c01d032101502d42c54825a50103034182c0102d02181020040c40c007213000c124255501d1007030b00805204c240c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 44313358 1250 44312108 44312111
    0x20030406061a0d1503030c230610032a0302010c0602040b1c1503051009020a0302030d0302070c0e010807030807020d0b0a060906090504200105280f1107140103060b0c06010504 77
    0x1840710131418031845140c8801400a900841c01600007010740700c840c00844152912441e0900e44100700710b08041044503844a00807070100100103003c4007400451301c400360304600e00458201008500101c440e03501002c2d05104041400c1000c001b490350445004004401040b601c48111507529505106128500c40b203007414803403001101d4201c07080308421240c0c8903000f4529102d021a0a0b009010a104180d034010740482c800001358034107001c1c00241000a540c0180c2d565100c2c40c01155600307291700f008408040910040c00b2152000403048181c0350005e000640300c4400380300040402c480e4050041c102200071041c05030844a03038010f082070b04c0803c00240903480d2201501c4007180c404031006000100349183c80c90a61600e94481055400d06242613840c0c90701e185036101050102d074142119424104040802d09a0f02075460010081c1341d20340110700300b41d544517482d650541d601071490b0105909140c04066130081d801600200700b182e917a9600c072001e031f070421a2180300920035680140d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 44314608 1250 44313358 44313371
    0x609020403030f0206191112090a020a060f080423030d0b012303130f02030a050303070206060a03080316030e0f06041208011a0304080d0218030705030120030406061a0d 74
    0xf500100358144140044e022200400340d43c07102c0c0b44041c00b0075410714440180304000303101c11000c992030120f21410f03408004103405446032040c4050110a84c1c003a5003001442c481034403580743e10184460f00160492100d49e800020114494070990111011841c1da02c0b00203007940d4030711400d401103541d0388030907200d4440841c501c0c0c000103a115031441c1902c04006042001401e0120442140484036004042250040e0a40e41c0820b02d0030050480c1a155580080100f00d400c80e41000700c95408035042d03401c4508240b55076030f038520500001c0c1c01c410926240e04210700300c0b548207074851003441003090110f03580001c201d25102c0d150300064600361400c51501d003164600600a03c881e034100c5490380060400c80c0034240490307400e6000034201b00c4140c01e081042482c2c0403102d001a0600701007030007040a0505075a01058903000d800e0b8051402a414107102410794203d40c0c18034010544104c020b1940c913900e61070103900030903194000640141785d40504400030b4400740e000d0101107640d01c0003003200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 44315858 1250 44314608 44314637
    0x10110709060b0f1806121f0e1512070f090b100f0c060626060f090304050103180b04060b01021603050d21060602030a0f05070b060121060902040303 65
    0x41c0e40c0c1500070310306080c0c8100800804050203400800a0003046000a02e102c041c00c000122158030107001c2d590040c55407820f015112000c0091942110860009144d51620306100f40072040c41c028500b0680c8102d1614802003500e036480d02d000780007070413001d60310b003161120500d2050280902492040914000b0807440d03604001d50302c07151211868039492081d21026404a50f1248104401c42d1044d0301d940c40007940c2d891001002002c1c0700c103c040f040406000128040c07800c03900410301020800108203121403001e0200444040c1d4100786000300301016607026080d10741c001404000d2843c80704008010a200c0c0913801074500c1c2800b6800d61760103121140040461030f0240c01f01400c0340c2c008550291f40c0b50b01951454111a11100543c0e0400c030b1a0079211080b202c042d80440302580001502c00715007503110342081400b0805003881810400307680c0300c0741620900182400e041c0403e00e401c0072009030100c0b4046c110601841803e2250b41e40743d8210310b010b5003061200b10041341564089460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 44317108 1250 44315858 44315861
    0xc2402010e12070305040902030108030a08060f0901140103060302130504030f050c030a08100306090c0906050109030b0406050603190f020310050c0316030b030d020127020307060e01020102040510110709 89
    0x81c4400040040684100920140c0c569601041c0c0403800c2c8041040300055801403400554001c1141c24003a5440b001b180c007000d000c2590081c0b203a4465001d6001c501c403107a5556440e581542c0c0880d2907184a1140f00d00140e00400f40350701301950003001c0d401d8190b214100c0760085440340c0c0c407e5449a50222080c0e5090b1820300540c604165507030000d002d600f4206124400140c1d11060fa5000f200500b692511018212010740038265202c041e0003034240301d203400d50300030040140740038070384261203600c0c50701c0381d103a07116010b00000c003a0364494011884540e0304001120110940104041c1c0030405858402d01507604010128000d0007841c280c1319125400d4821030b07118481c250941480c55036402c000c61030418072030600340c2c10700d649c0c3c0400e07250580381000401740c1c0025036000000c0ca055106080e50341c0700c07850442d440080c505a0a8100140c070b001c25071200300c0c0c40d541052101c0010540050380a030046030042c681181ca00071500c664a6840000381e84560310950590307040301d86600c41c540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 44318358 1250 44317108 44317121
    0x5030705030a030e0103090812071706060f130314100605010503040804090c1205090f0712021807170411040e0106032604090c0507020a080309030c04020c01090c240201 74
    0x81e8150015031107880844d02a106600091505160010b400d043d01d42d6500c0070b58014240c440c16491601c5e0070421810740050035004c90008420041d603240c50281c0c0054164814642c0603580d00c00c0104000c00341741d0089405c0340145601034029901c07a45c0907840c059032040040d06c05403500f800d1a100007019400307041103134040c1d80c005003490718003414040c10302c0103000c60260710010021000c1c45e0700f00c0441c040c0309050140081c03101400c1c10480042c0c0503403a01b0190380003412803900c4012614010b82c0d038130341d84410fa5445204910515582d81c1f00a82d207440c1382c041d404c0301a000082c208000c0206440c07a40d2034400c3e04840411038038201134201400c031102c90100070702d40044010b81c22002079260006100500790104400d2030b2945030340080082d0740c2d44413904404604003140560852520f0b0b280389014102c2070000358180b1000f0310000340e0341e00c010754015000e00e50008000500d50801c1d000141410340105160580c02e5480000c103000d04544c50300f002800b03158046440c1210700c18003404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 44319608 1250 44318358 44318369
    0x60b04092c15131707020f03011b0e030c130b0109090f0203010302011409030a15020702060d05040507080a0312020a0c12020a0b09010c0804020f0f030d090e0a020406081816030c0f050307 82
    0x2410000c0084c0500c00260304c40d26042c0c0c0c3c4a000700e0342208060f0303024007400c0441521038001c1d004603064480044c002005507103034a48217402401c032112081d159001d6181c41840b4448010030701e84a44001a0f50030165900706030300072402c2071010280403802d9001141201d10030781e40d44810101d0034000b004680a681450759064110745c800704007080441820407900701a01c14011315220583c0d00241d0503074820070a00340c800d6101c004100a106003400310500034103134107000d840c1794603066038007e104a16907400d0041c4d80740e0203d90640b00503c9011a08440b0f80c0c01103c008071010140d0300a51ba408080d4000c4428480e14400103000c0c001c180a0401000103540300c0303c09139152982008034030f07010700740d21036041440b498500441d0340d42085486c09010b026210545207a060845101844800610840038103004001c20459180e20122142e8811030460100d924050052035090a10b140620122800701e407440010040c043d403070400307504440c0c03032403045014240d940c01030540310f034014030a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 44320858 1250 44319608 44319623
    0x702031806031501110309040204030c080c1503041e1a060a051002030a0c15020a0801060305090307020108130302010615030606020f160501050f0408060117060a060b04092c1513 78
    0x180c40343d070b50160000c02c2d0b0012200041c2c1c0d05001500e8085401c13070304550700540704071842c060204101c480501c42003011350025504800c042c449010308550034400640020b00c6032a20105110040d0070007104c4005050703010031280c4003804074410100703d88406840307052040c4040c803400100c0d454030b41064035030234210360003550814094100994881180000a0f15207054001c070b644000e14592006001c855807585816500d9414402c006045440003004c40320386a100300841c00150ba00400c101da48880c90b6121010701840ca840d0490140c90190f110182c0c10b41d14410b85c01406416400c45002d840c0c465084031a43e594070000390795101d60300c0d0703420650800041c20502040d413151004102c0720030700750142480c0980d1100c05078075145003640701e2221841119a14200340c0c07001d11655412080c005002c1c44594141b001c640403e01c51803080349601692400c060410016849000324140640740c002541c000c046480591501680000030740c2c00d80c5003000145091014031424086940c02001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 44322108 1250 44320858 44320891
    0x804060c0c15020c0304050a0605040305070909150506010c1505161e350103060506090405061f2606010806070903032105070e090612060a09020a0b03070203180603 72
    0x500b10029030004641c9600c3d400108000300d210346400c941203000f00000d5441a64942c44c2d41001b41c244019504504640c80c1080d84071004580c600c205085c200820031070014035070b206e6600580b881c4524201c002d0205110751044a46440c00758812841b81102106040c44846141c9088808200c01030018461080c810002402c461143c10f00040d8040300324884080101070000110580580919008442c4140b40051040207014082c060300030000ba141500c440c105a5107407070b1588001002d030000d042036041010411858440240e0003451a80d03400c0d005506c013400048812a10f00069182c0385c412440000707407002e000600148503c03c0703a56100c003180e08540c1c040301e40c00c00000821001c0c14010780007a01510007407040714040c0301c02c0d0710303151a10410381c0103000401c50f00071300300c5106100802c0700c807001010100b0240d034000002c10000850342c3e418800116001c43c49d402c44101c41c9000310030005029000001850121160000c032815240c0d05410400b01d440300300c4040750025040c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 44323358 1250 44322108 44322143
    0x50f04120c050a030b0108070b07020904020d020406120b0421091406130b030603010b030c0109090b19060f02150106050d0f0615020a03030e01020301060806120309030109030804060c0c 81
    0x40514110a1207650141049035540c00040c03001800c036001034074000960401001102c000b00304c40d000800d0181002c03070030302e24141c00203440b8110040019028100b030206a0b2304540e540d620440244c60a51420414158581031182e03045004841c01c9843c0f462444505620b034010085050004201b9510300540c0c03410316001c04070f00c4449918690304a101070085000c0c8100400641c400703003001c80c51581c0c403441c01800309402d494031580540e010f90402c219020050768403049100070f44400240129501200c1c001103203e040034601d00a9000614040101d90b6a502100c00384800104d0f50803104403101550212523030000c00c0c4144004100c0c100030070100621b0507004a560000c8010000451958a111244810700c0c1051082c0050300162160f00c1015010b04c108821055124001c600355070412401920030900a02860310500b0840788601c0d0114080084074140b10016009201803e0751f0315016080d00d0081e03d0807a68681082c40e101c082601c10800310b101035800c404144071070310048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 44324608 1250 44323358 44323379
    0x3121107020d061b08070f080c09010c1b030503070309080303010b0319200904060e09060606090a15050714030c100507020c030f0a110a03051209060d09060f0606050f04 74
    0xc040f2015a1644404582104000305207103d2002a0b2658520741c604404003c200000c00d1030002d05110858080c00031030705400068490003c002e080000d000c402500b0009498030303054403030404084413650003204000011024008880c425220540200d8641e4240343c2c80c0e0000340504900410140000f80401c800f005900e43e6440e4080000102c40c109640c0003075145400d001c1c0030209180000c0c0c144100e08040c41880c000f04543c1400200506260030034603260440540780d1481210f002c2000c103400d07520710091000402080400004251a02d100907182d07410400050300d8002d00190281030a1101004442809102e03c001d000070703803001e8001d400100005402002144150866021651010815000b601030317544010314100c4207520707000000248116003140a51a00001000003420004036010140c8264802ca5156048103000c03500e64024002c00034410742c102078422041c805660320104603081c4040040c002151601c000395207038401e1070391050310440100810020711142 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 44325858 1250 44324608 44324629
    0x12070515060a05030610060206070e01020a02090c13061d04061d0a1d03070210020705010207230907030902090f070c0809061b0708010e0706080c090d140a0312110702 73
    0x24003281402d51114082840d0041c103c802d030011000c451428001c0039010000c095000e101403504504110015000035190310090b60002e009244440c04581051071141c01d407000781440c2440c0200c1159070f000014404107d1069401e0300301d1240c841540365060901030103082e10b42c81600115400d0041a40d440c09203402412045e50a90760304562441c020755903403e802030b0b44010f00031901e40b2900e00400c040700b418050031406550204404104907600410340400b202d20b9814491284d000c142c1001107042420408143e11004a90402403031a40503840030340b5086c0281c54018072595000c40507070640c40b0940e2003a000c40d00403000c68001400c071100810355900060082401c20100703000e000740000d15600e42c80e07000d03086214107002c41c0e4402d1117800e0076800700c08000c04c00c1500d0228090501200070f88a51140600090554560748800707040f204e800d94032080000ca000142c0f00050744070524203000320000b4103ca010300c252400d10f8041c0d0030311820002c940502e41001542000f01c42d550303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 44327108 1250 44325858 44325871
    0x15060d0606030506150406090c08010b07050a02030d0807020105071701051002010f1a090a02030403050d0506031504080c0c091009050601142d1602011d03030403050c0312070515 78
    0x122540e001c00003c505110244c001e00d81050541a01c007800020003003034500d0b0750020310029160040a5002d25803111005044030081c0c6c1c60340343c0d9448241421380c104018400040d4045c882c106124030b0301e645c0403a449106018580c020001602c0e201811603401c200451420303d4108000c0c010301040c94801800c03803280031035000019000d5603e009040030307a1004061080c1b010b07114240c462060030b0900348a54001d0300550110725620717166030007070070030b000302c03c1004460b6a550002a01c551001c003e2440c00c0c40180442e03408526081c9065540c0e9071124080c509680030301c03421400c060400d40e12441c0204841c0045580e4135040c0070000e00100001450396040001d0046e41c11051507040000f40f140c0074802c244a1060f142004101200c0d00304002083c200712003c009403801900010a5040304540c2442c0c5140343c10070030648a10010028041d29626002c00100003040010010305109602002c3d000c0e55058035003107210403480e0191450181290b00310312031f8010f081d40819040f90b0b0200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 44328358 1250 44327108 44327111
    0x1a03070c14012009011812110402040302030a05010506010e03010b09062b1b060f0c0b1005031b0405090d08010612110a020d03050a020f070f020609030f07030309060215060d06 77
    0x44245060044043d080c00b0554401e900015480c0e542d5a100030010080c201620216008528000112588154000b000740c8000f01c81421080942d86940441e0300139600101190010b070454100240205826039010307002c01c6600000821a06042c065240351550040c511816691100c09004071b0017100303a200504146619061080c1c505040f403d805641e009021205040307111180703a00c80080f59803c071509024110112074074240d4000000700039550700030740300803542c2c450006d14102c1004c2d0780c00961b4180a024100400c80c0c0401000d05941c2c4411201413040762196000a0340303680003d0742140002d408180103200c0d03240a00070340071402c84113a00019494190740d148501d150000c034444001a0403640120b002c05a00d4065142c003c17810500031840d100c0b140e000c0c0c603c207100d00d0a00078500f441c80030280044d0b5a8123401c1e21003c15000e4140c415070304074075000a889420502049001c103070010340104031507200085a250760010340d41e443c0d0700e5444a8082180030942d880c42140d0f400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 44329608 1250 44328358 44328371
    0x5090307030f05030a020f01060e06060705070503071202040f020405060a110a020a06030e010b04060506220306020d060608011509030303051302030d0305160e0f0405100b0307091a03070c1401 84
    0x62000020401c02d5030043c4003568031030031042d0000b814062044000700f62030303040c02c8003400302e09500c41e8200d0f0040d400300d806c140e8640d81e9152a50070055903504c05685801030120001d0800111800819640d101321020000c0026050540b0120301a501441d42c2061081c0911070103d0301070103d10380500c16000c11a12b220601d40d0008140c1c01240e040a40001d1f00c0d0401c00e0382c1180240206184400122000d00c809070901c0089009405070440d0500a511903c0300b049a1040c0100701d41c0140d900541c05550311070241051802900f200d00c6400005517250b4000198070200c0c00354247d000c0d1895440300131062854070200d01800f40030b4060540c081c800c10104006980401c62102a413150b610701081e075103440c420010044110b0a90f510602c040e148280100365100c0582c030404110448000905445400c142e20908145030452000d00d1070000c1800009a042802c0100719854031100f18400c00c154100d600e2940425684e060200e4412034103000002c01007a584100700e2800c1000080030b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 44330858 1250 44329608 44329613
    0x2130e0408270405010e040f080d14010f050901080d090308180d060606030b18040b0711030d0605090106030207121409031e0c030703051002070203010b06030f060a0509070509010509030703 83
    0x2d4180350001c0085000c822242d8a010b03080c9405654018926586d0101003860103840e6110303003007401c101c001d10420000030800807440060f4010030034200c028180410568581d100e5110034251405100d110380d444c00d0000488400c0061414215000c07a5241041c22340355541e070345442d4201c6202510704808138000d25076141ca0700660402070500484004c52918600b00d8043c04862200011601401229000100f154102c8a07910f4005500010405080d5030f000c204403060390300e13000c00da442d0340000154041c044540d5040366040c1e9404442c0c26019981c4c47d0340035000c038814450700402c4000fa01580c4a011030007902c00001100314081c03001d10300f00302e401c00681070041b007842040c0c10801000203d402e58204105130300c070019050b8020300302541941c550540c0c84c464025079211094000500d5411500c081d00030055840c0058080744c1c0340c0c04c00411780041d05200b180c0342070154044950000d41890a0318135540540303415140c0500d4140e22200455195202c1070440360144600c0030000700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 44332108 1250 44330858 44330887
    0x201030209041e050903041202090915040312110717030403210c0908060408163002010c0f0e01031104050a0e040b0a02030114010c02031005010801060f0902130e0408 73
    0xc3c07a00500d04003009581c0410500341290006041c400213540180018440c90034860b0500c640d80f90112243d08030360303030f442c00d2161074100701c406520001c1c1a1201031008241d0424019044900550000d0120f26100745100c07086000301d200291510040e030000303007100380088000f1a0807074081e240401c01803003003016844001c140780200c1da038001da403410031820081d800700e007480241500c20054121810030b40c4a44405002e0319107807099190202c0303c8181004560702d05841e18400791846901580405089060809004804500554200109080c12501c94083c0392183d03005510303002c196242c00d031700440041040028551903d0700c00c10000c607465985c41000c400904045525a00620b41072030702c052465000707004041e0640c010b00041c000490b181c00302c65104807003882c001c2c10f08820350000078a00300360154400d40c460b15050000c80c182106400c01c0090b2102c0b00b112840c515564510a000c038852100b01440c0d0003c12a010b2104c00414282c01c4e030458000e065403410441d000c6007440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 44333358 1250 44332108 44332121
    0x3306060305090625140c070803040f0f14040c0507210816140a120905030d0c0503010b030703180803040308090c0a0e0c09040908030c13090b011d0102010f060303020303040b010b0901050d09020103020904 89
    0x2413a480403900700041412140040c020703160404083c00d18038540030001c8044c0100dd00c4803031055450b0311001805a100b001075603d042c2d045003a080301d00000d13100c850b40310252250b0b03030000202018006920702d6418215904004956078030782c6414040740c20a00c0741c90300140e20003003c104180c03a0420f1001c016024501d80c0e075000e80041c6a8031501c00c040079003164004904039003805020b0004100080469050300d03405851030034003150104808145000d44100c1490041800d80c02000703003c00e05510410551094a6542c02ca41d2400d040c40c3c10810110500d100c0e00c500d403081880026038086a0501500c02010027a10116502400b9600d88059400842d94420603030740102d00303151400b400d195100028220718604206244481d00024045800c030800860845a02d112709611342c1d100b503100019092080e40100704090b00c07860000d440342c1c0152819602e0b04e0300c03600040b178885110011108100c2050315442d00c0c0c5200503038042e000e0422020242c2c1856801d1007a5401501d0314000c9a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 44334608 1250 44333358 44333369
    0x60305011211041e0213050a060207090510030602030a09020909030306030a0204090f0204050103031805010e010507030f11061003060e010b030a0b0c0d0501060306060314043306060305090625140c07 87
    0xd80c03905101d80d10500d1b0b80707106622191003154403980c20040c40350082028415a418081d01040300e544e81e8503001e8680100e039000400480c030010070401c0200280e030290030142d02c03c44441821742c803a4990203030390740029101d5946c141c004080d6840117140c0740d070000e004a480351324409440941500010102d9509078000c0d000f00d0900341c1214000d82e000700d801c601501c402d007800c46030021404002800c90203016401801d04c00c2122400200030701540d44030303a003a80324000302c444515002034824000801031008032802420009410401c2006000344580108d02500908040c0c0480d121720b1501040a00350201c3d4090030000c0e016a0611030107a40e0203030006440c0441d07407929180b802000c4400484107602c1d400310000a000c0090350311094101c10f80e06142103210b0074000060544480300486503035400d50342c07500d03500040361500354209038442e00422055800316035800d401d8800600280d22102c08442e400407049400034002c0e03081c030350b11031080d804580c10b05d050b983c1d04610b40810398102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 44335858 1250 44334608 44334611
    0x714060717070c030f0e030307061d01060e0f161202160b0610170c04080106080a0c08150703020a09050d050a02030106090e0c06070305070b01140901060305011211041e 74
    0x400a02110480c6411040914001850f4415074030000c0c0380c03000c500c8031001002001194212640d42c01c1094a000701d4100004118000003003014040c1260001c00c500744135403c0141c00951240c00c2c0e1a0079209981560a08140780d030b40d00f41d80c8900201c0144081c0038802e01d28181d129101e410306c050a04500c018a40802440190400500c3d001004018912901c0e00074074150b0501d1344080340c207000c048402403000c1e032034580f0a60b64a40d4051900300070000d6103061800202d1101c00100c0d00308044c05103c01c4400162504407007601c444144440e442d90700c10070300c040703038030144a07900a00e0108100d16000002c2a1511b00103048a080050250340b140c3c80340b040001945428811100108040c00e01044060148402c0d0394840301c00341401072103180b01185500c103041c0107004444030258030040380d058968407184661000d10907040340c2801651190000308200e1b000b841901c3c1070b5001040c031050181c0d4195141c54610404030350554010b61103108140d42e43c3c0012000c4a42c41001040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 44337108 1250 44335858 44335877
    0x7031203021b010b0102370302030c01020c010624080f07090302100203030702010c02061005091003050f0303150405010b0403140a061a030105060a0302010905093312060601080105040207140607 85
    0x91804102542c0e1603002460040c03e1076045a044031791080c081c07c211a04031049940341000c0c0d0030b5000b05501c0c1c1d02994000640317070344c1910066001800f0380301449511340c80440034210708a40d1184070011070700480d540c600891001e1818a180c10b80c00009850070410807500c81d404a1040d0940c80080c40c00341e440802404239031a0280203141c4000003600c014207041c68443c00d10382981c1250700c2564014100800070990314418007617010041c40c2c00004850308103099003001d5640e58000c440c11884444001d100020520b0907001d250304130b651b07240c4070781e04041c11130311a030003203010000800145124084a0340700141080c09458007014040301641840145c18050500391400101624458a000401400180e070000000019181c068400f40b400ea981e0380f030b101148a548843c881c220310304c1380c0d0002d0740d0b844003200c14008144c07050300d02d0004045000d01c02075071303090155072040c04240391500500c054209540500311070b900510382011130124011240307080c203c042d62442d0004291f240e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 44338358 1250 44337108 44337131
    0x7050a0c031e020603060d0501090204050906040c060804050d0f110609010b0a05190303080408042301030e010b030604120201060e040c1a07080703050318100e0d03090507031203021b01 81
    0x300074501c04030902d080454040981d03400036242e44002000b1074865003a00e414030003485000d6005030240e50740907004122034100310401694681c41110200e6100e0b500000c08a00c65110b220a0341c010355100c4028100911214411b480009251074036408001d85c500e40c10041d0b150401c40d040c01440001c00005580482005011000c02143c225074003c84090500d10031080345800400200e13509407800c1e41e1380d512a072529016506c078960004203030405030103c00d000403001d0100c0303030f40352a0241c0b0b0400a5070940c0012900340e8030406a000ea264202c480041c020482646020070012024400056a0b375116000c0800000d0145e40950b00342d0b003500030600c03011182d10f010542c41d54801d007200e41041030558409450380310300d550003010000e01001085019030610600100d5080450a41c2c80b20200003085400074105003402c51554440c01d164001c620307009206209645420a028152803811a100c0b215103c446408030000c0550811070103410800d00c04c401b0f0004510140086001d011a8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 44339608 1250 44338358 44338373
    0x50a140105120601090b011407030203090315040209040b1807060203031902030405030a180b04030803071806020304050415080a080a02010b0105030105010e0d1104020a35040b0a0207050a0c03 84
    0x140c120318040d002e0b66440703540c100c0d0002985811941c040c03901180e00a00a40121050081c0c00c0042080d40c401103482010560044050054a0816812110890f01040300d403502c85905a0b07019402c070030fa200101c0c0107c0c07186120340340d10500d021074410201c00d45e04449482c00c1c040da0711100c016040030051142d40d402c1240000c00100321b00d0010360441c2400c1d12000e03102c0c0718803414141440b44c072030b03000100205050f41010042c580c20b41040e8480c0d1356414103896541c000c640c41c50000d0425900303c02c01c0000440c0360419283d403503008606003070a08003440002c0901e0a100e01100c0c0c80d803200040c111100304110348407648074604a540ba0031043c00060b0a50b161a00c582d81440f0051006021a1b60b00015003001082d080b240c1c02d140d0b000c00c2c101400d20103151024550840e000290315071010b81c004c46c1210b5008002c070742401d07480408410102d414010b61100c08034101812010030302182080e44416000300d249a4010324200480d0758071850403511301c0c030456640d41020710400178803091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 44340858 1250 44339608 44339611
    0xc1903030806060708040e04031115070e030715030209030c03010504051f020a0e13150608060a060908191407030b0a05070c0c0b0d02120109091101053406050a14 71
    0xa81c0c8080c280131503561051000d0041d40200440340d003841c400107051501c996510050040e40f05c05880141610745400c1021006c102d80c5034001c100c461072440242d040000780042190070b5040001003008295801718003075030004061a40c144546a001e800c2e5070307400e2050318000c5100790f00400078a00000c030010010f440048040d04a58030510294586540103e4400442a004c0b60b1a1501d1040024100020000b0721841c0c0750100f03001101040d041e8006040c43d000b2242201d00b0186144d0b5110120b811005a006a00c040e40082107035001303d03005c0c5a03a09108038070910810504040e4080b416280503543d40c8196442c1c1c00700e20a101500c2000d11904c0d401166900e000040100641c64142c9806258404c041924000045071501210740303506462004d00340042c084c2c01540d4604450018084100c002d8a810700985900344140d0701034003c50300340800c50108200340203522401d00700320b14114800f400e820104840c080e00001c80c644030390351040c84042400070341d001c0ba4000e1584810700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 44342108 1250 44340858 44340871
    0x1103030304050607201006090e0712020d0203030712030213061103120c090616060b010203071a0c07060e0f0c01050a020304090f020921060a020f07080901020c19030308 74
    0x4006100100e4804580d00d580079909040c84446808a2030740c0c0305400c500303d02d035455a03010314442e0600406e9503400c008100d81455109000700c403200350810b5142d80f498410003d0802103851440018140072175101e107600d000406480c03c0100741e8507655202c1c080e0072440d20002c0d500240034054500d5541d03155020749440e00e00b203884119249004c2c1d40e42c2c42401414111140900d00040400801c00c0885403266070140081d5103036810000c500241038041030342107401c0c0782006450030f00c552000007922402d6800c03c500c0b00703200f004284420342000000e0000700140d01c04000760f0020074154043c405000f1070380c000600d200359118140c1414404400070302410040c04009080d645540002910103030350304588001400421503414000a10440c1c1146400c240442c40b084d840c0c005068815840f002c03c1c1c02502c03100e91741c13407500e00304030721034070201c1070300c0160901503c80411895005441c10000600403180341d85410b000040c6c0c19150500c0c003215144200c0c038103008044d8050403142c0c04c6103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 44343358 1250 44342108 44342113
    0x20a0b1b04050402030a061a0a090806100512010b040623220b010207030c03290403050412020f09090309031908030a0510030b0903091e0102100c050915071103 70
    0x2400900388051920562044034425500480800c0e41c400595011400620b030340329035051081901c114440c0c15411000080d400309800d050000703111500810860321940e600010786007400d0410041110440302c071514940304e50350b070300d070301180d01d07241c0b0320501d80505070700c02c1401f00b00e240c0d0700c0d00c00c0025505050460300030b00140100381d242c01c030010400b00703904030b203940c1c082244107000300101d10f052401d600c0544203100c5000c0000038800c00810b1001c0d40d1a040c5a4031307501e15140c2520278a0914240d030002c0c0010010041000b10704803480c0d004810504c004c100c0160580300000141c031010058600c2e071450b401c00100c40f0f43c0f0303240c100001d60030b000c00ca11500342e0b60b03110f0703071520b0941e808000c125609254035030001035101c80e0105055800b035940040146900d08003240f0b82903881d000301c000c590040881c408140b00305019403050000c2d180e4161700404407112501401805800da484007081488000e20030f400d12961010400d00d030300140000480d0305c0343e446040c00c04085880b4010365002e034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 44344608 1250 44343358 44343391
    0x1a070816030b01020604110f0301050f10050109060f0c0c170c1c0c0302090714070305040608060603010e04060c030216060212010b04080307060504110a080a0201020c060a09060c05070510020a0b 85
    0x590300030442e254801d4000c40c0d0007c0000500f00882c1c49002030360200b95240d4a0201001914203549071a50301a511600703541c1802615100103461030005805000042402001207110080c4900300c000784192140101c2c3c007066640c1d8a10b0517007801e801c0c08001c0d080c0c1124610000034188205244220348400711000030301e01c11603c40108000c51070001034007850030400040d81c4c242c0501c40c0040b020b2140d414140d580c404a06005106401501034600040d110b00301144030781c940181a01c0c181c030140203000003591220340c1d0f240005c000d8290100d090640a0141c1d00081341d40303105034800540501001f5907074003201d00b14070074072100503003103030b03505c8641448184002c2000005884040b988802c000510761250f04200c0582a03501003c0d50f4480c810b030a01148a90703021610264281c400e03000c40300903c0c02e8030308101c42c0c0e0261200032400502201010003d00380300e0710081c034040d401001903592454492006c224856648c45643c0d0141e40412000c7c020001920700f00c0d54002202081d01019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 44345858 1250 44344608 44344631
    0xa06150f050d0807050d090e010e28060509010f061106010807030215130b0711010309020f10140703020d0807090503071a090d150c05120f041a07081603 67
    0x40400c140100780c0540e001d01048400c02506400f00d0f50995007240440b040f41504600041401d40d0501606012440440001444403132005203180220b9460851080c0e01c0e150800320040c803000c2c0c01041c1c030000e44440d8001030a07182c50882a0180000c030303001c0800d0600348080900f0225162007000c0040c0c2c0311500401041d0000304a801c2a00d40c100c030510500b01e4080c1201d221070007080d900c22519200c446000541c010010010599075110380305d0841c20038072080043d001c0f070714041c10194011001c0740c100010761030080c0f800c4003a09142d050000b413105442da01d0441a40090740100c0260707100340400c000307458010010a600020901c0c10201480c03d2401080d200c2c0c0c40c6106842d40010018a4500720310740031401c1d540800300150200f60845074a0800000c02860030015226051400100403842440348048610705108480b403902c0ca5110450b50701d141c00070082c400c4d103030a20584d40f80da8807140b10541190181d442961a002d407801c000e54421504100301003080141481e20180500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 44347108 1250 44345858 44345879
    0x1b020c090103060207080d020d020d0e0a0201120b0109090e0604140715050306040b04020a032004050604050d0203010b090a0621051903021608100b0d050604080d060e090a0615 77
    0x1960f601550258640500f8588540b0501070703025412480342c00030618480d91030f0141c1c05041c9140703e00b007042c00003c0307004019585908000070040c0c0001d90b2400ca200818500e82c0048c41c00b8007040c50405441540c1c0c0e5405411980c00f03400004c95500070005001c1440605504141007526450150880e903213800c8030315601d900c000d14100280440031000560030341c2d4a6009101003640038000350350741c00000100500801c0c04604031035000d40188a074120b03c10310b08090324199000a400380b0b262500f82400c0043c0c202e020304080740d0540d03c811701e02c042d58a400360480c0c09200f2010000c5115800c207002d0311490b86802c2440c495210034203920034040340c00060b40b603107559030401e0700c05440c4525040c120b04113410b5014410900c2c40404000520040000d901d800b42070000304204080b5051400b001140f50150102510f140e0043c0c0104d8082002c51000300f4010b005443e000070869500e03c4803d40c4443d0032101594160414100740051182074025000468800382c0080085820080f4000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 44348358 1250 44347108 44347111
    0x1e0507030c08040b06011e120c020f03070b09010213030c0801060905040f0210170709050a0512062404050f0403020c0d0308070c02010203040902040909021507030c020d020f09010305011b020c09 85
    0x901803003410003c00e803264001e10780c00c0014201905907c080b045490000342050b2607000700c905000e4604000c078419280b0120f07002c603214000ca00034514018540d26011040c00001d00801c446541c2003002d070301d04542c040095802544111105171010745401c4420f821288298002c1038464240b40400c0b0003e03604442803c4072940c100e440c01c50b030201a070300072100c16102c144950322440c0f035407081c01001d0f40c2081580d0304071201218400c0c41c55480d5130620aa02e0b0340c00491214035032003403001c0741100c14a4505004d100304404400448410480c00180a450060311000c05d1091404203110a040c3c0c140a1441600c0013510a61960481942e00411191005044e86c0410100c4800402107a01c06d0045400405401005541b159141d0003010001c00001c2d6089129602c40c0d900154068440021f40715010380603180e0100524a0b6000e202d403134505000102d0f8044184540102d1070b5544481ca98040d500800000822100c114168410559411101400e5511400000c80b031030b0384200505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 44349608 1250 44348358 44348363
    0x1a1302030f150609070c0209270f0d14071209030605011212030b0f13061403060403120b04020918100815060d0201091d0420100e0109091e0507030c0804 67
    0x11800780d070351005c0885000032081d04c02544810081c0a11414409116104250845d05040f07071420048500d84182e95030001c00c62001150000180166824060510400d44103041e0740583d240c2101031342d459039804550740c880c101003a00d640091084c48518403515001d4507a490f400700101599403600d07275015034203100071402c051700d0700f2403c3c14503100c5000c04c40c10000040c2401c02156061000d80024000c00d010340100394569050035034040c500011000d000b5605500c580901c0701c805840072024209030746006070025020003e034031181d02d07000440310028a52075560080b600307080206916024140d8441c01c41a4441c0c41101c0d40d11855188407034110008844040041c4500d2005a9035100c19501c1b1442c905003c0c5285c07083e0050700c041c214800d91140d00010702e201c030b4405050445a5408455682098420503500301d09402407840e02c0b0241c405042410050755134a041c41c090303440510318040804411170203282030303c1c45405001d41080781c0c0e044c240954032040d4401002d0a0000700701 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 44350858 1250 44349608 44349619
    0x110c040c120e0109110108040209180304050604080c030d0905011202130b03040c08060f040308040b06011106010f0302040b040507020a0213020702030304062007030b01050d1a1302030f1506 83
    0x580845004078030103500c00115900c140508070103410b55500810307110205a5050506802c841419885500240c0c4150703030007013028034547c94642002c1d0019442c1c0c1e00103640b62100300008611591000060002071840b540105a0f00d803100d400e1608256680324014248012100309001587e000310440d040798000c06d0740140c03a0008114040024011980320040070742e00013090006006180c0146000c0d110510200c68040c0c5444030400c1000c0b1040b100a80001d03801e401043c000740d105000c45070032040500d002c94211522055150800741c0030f80c0041040c000894040045062600035481a010210b80800480c0b90600019448442000e40284248450003407a82c40c0952541655010b0750007600302d9072901e031a6603000c0c080302401c02441c08001e00c3c20014070002c0c0000504101602d600141808181e441c0034203000c5440044201100c002080c0320351480403641030483c1c144507030001100442d85907124010300d800c2010700340c0b5080c20f5400503c506040c1c454036404030313038001034161807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 44352108 1250 44350858 44350871
    0x303031b0d09120206011e06030c17011410080c0d0209010507050102040902030103020406080102070c05040b03100e150c03100b160204022a0102040e0a05060406080a050601090507110c04 82
    0xa45042845004100384500d032900c0558824441680310f401850701482d02110b40317a03600c4840c1e03000009000c08501e0400581c10406100c0d40703200e904154038403003150410410800f00d9a0880c403281c04260840c1101c2e50a03d003803080305150130200c0f0084180c090a00301c501c0c3c1000044000b1610810f10f10010f026000501948a641306001312000d05070030100031900c40d1744031010000654400c0c4001c4c1d100398281200415010b1041c030031204000d40c070882d004e404520304800d001c042c114a003100d13645030180a040c484082400c0c014440c3c00d07680080900410707250001c01c0c0307100f8600641200c030440c60900402942c2c1842034582400e0b00d00c4122401d407074280301d2481454402d00d10b5030080d0081d00104032182142d4024200721460a0b10144084000b03860208141c200d0141d840303034010103400d001c046101064180d00440c0c10010142012402a44a0354201d140c031414001c02c48003944a1801001109450301c11260019480e1901000e0000000b1440d03550301d440c410324a1082e680c914 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 44353358 1250 44352108 44352151
    0x50714011103070305090307050a2312030d0b1005040302090f0a02040306110309010c08070f0309060b030102030115030b19050105130e0c0d061418040c0e04110f030c030303 76
    0x28903041181e14481140e0781e070b00240c82c00a2141c3c200c0721141b402441804004542c0c3e1a0000100054403c80310b108210440c692400402c1c07240b05008603a00540b0095000150000c01d000a107012402140d022503a209440e0030321683d032101c81a15000c004040c4407e2005075600c04035075410143c0308400a049455075420107000f44950303030004060600d4400780d1400403100101442c8210002d800801a0708800641902c1e2201c04840080020303001600301b4a1181c0268056001d45000780d8001a100344403801003400c9030b1007a041401820591460a50101d80c94001c0c04281c08080c2d0308038a49a41141480682e10074500400c4c0c140580070400003804144443c22070010202030b0008440740c100941042c1840d40f080f415000c1e0306050000204014500000c10102180090071103810300c00c1d52500048501c4001c1c0c404c4601c180340030400242c1002d0b4000c0c3e18000c0d800341100c880c0b041c4000742006001c0d0382d0046114041d8000c90071075511503401100b0780f50f104a1440040001c244c48a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 44354608 1250 44353358 44353367
    0x60a060f050d090b0610030e0c010c050307050d032a0203040302120a020a060f1808070302190f06031506110a0201030203090a050f0105010f061409041a06120f01090905071401 77
    0x102c03403034900189000d52180a002004001c0e60007007006464070703419502d6170501181030f00d2141c5601c102c0c6a126440d4100d59500c50308402803450b001c0c00036079050450030394995013080d4204600d500000e495614545922110b05804d0303806480000c80b22240c032024a002035200d000f10312010b481070100c1c62100241c0c120500c0403c2c00d00754020a054625a290f00300034020011a9458800150b40b41c030010900c400f0206515003a540b804000341000351840c0d00700107001e00001e10740380c42e501c4030501c0044e0308101c1031244005842507850109106000c81d140d9204d00149a11800070030201c1c0d141000115000704071600180d4080c40c01607980d0b91120f0805241c520b80443c0140b540c814201c8403e0f040c041075201505a0714249400c00c0c0d15a610f18040310416035081c004a090f4030308004118041c42c05a10440400805c4862084080ca010300094115080003c003807080026803420484140b481d188001d01402d040d000c1000044500e4441c0c0b070b40c801403401040544400039044047d1070780103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 44355858 1250 44354608 44354617
    0x61c060b040e1f0b01021603120c0b010b07020f06040b0a0e04110d0b040501050102060606030a0f0b09010b0705010c02161a041e0e10030b0f060d0c060201090c050405060a060f05 78
    0x3410b003110402c5030801c0b1141107082160900251161420340409003561000ca08811040350355140d03040f500f0b08580b61079601001441208050002621480000850b12107640b4020500207031034548401440c018003541c9010300e03000500c030b10810401071000300380802c141e900d01200b600c1c0c26020f8a26a038041402407190200b0110318400110b04c040f40800303182c001c0080d4040964003400f042c0d90b00d200590740c0305000d0394003c1c2c1c003a00030300004c1e42450803a40078034965002d07440045200007c08010038199602a00000aca10400050304801d02100b4015104003404074402403003169204014010680d805004810054149030900860000342034140c602401d154101003c401403112590b04100c00c0501c608110820700b00b0000b8641012091013004607074101100400f240e079402401d458a480060400b58000d0300c14a202001c04e070a801c441002e001a90000549545903042041200a017548460b101d9803c0008210035515501c0d000d50840315a420720041141400000303075040d004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 44357108 1250 44355858 44355881
    0x303030115031103131203090b0103080c0607110c04091704060509030f06010e0a050403030e06040b070201060b070f030807090b070503070c050409030e10020a06020d060e061c060b04 80
    0x1000100d00c80341840000a9070000782e45081000d100d84200d51549400b0880c2c0c1c07056030100c250201804a0726113580740c41d9044040c84c0024112000d65a8054540400c5c0c0003038840ca08041441c81007041c0c2081010307000b083c03034184601d91550280400350345403060841c103401651244107440030081c4c0440e0301040c2183c5858a0364481d40c607101c3c001c0203900301c080c03258800c1c0300d09036140c0142100400d660303060300c0200380240b40035603807900484090400030b00100c041503a80c0c03400364a4a0301c01d01006004078031903000100e440c1050003009007503a8482d01b22004862042001c4800640d9100340100c0e05949801e101445907184c42d0140c8000c2c015070f01078100403d00060800800c01c000c00282851807068004000c1c1584600500c801c0310303441400140440c5860380d15000d10726100000c05910505481262405611075032407205a822095041048545400b420b1050100581c1202c0d070001d426240405141121115034240e00301702400600300595400e0321010503196038115142818 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 44358358 1250 44357108 44357113
    0xf0f060f030a020d20040302091b070302010506040e010e0c0415051201020408011a06031906090e010501030c060c0b0c03060d0f0302060601080106180303120e16030b0609040c0e0a060503 82
    0x362110030744019500000c5050701d11441c20a05030511020150034038403104004c0b5030542424110307400d201070722780d01406c1e0f6103040e0840006c030000040d19100a0103210703c241e001094906180007030100f030701c0d000341d40408682d040ca20302e0301c81d88000041825014038201d60109004e54004031400000c40035404c160b42007102e03070b8059440c0240540040003180e841c2e10080002011180c02140c010204c011a568032a00401c0072a0081880c8865004c8280c510100000c000f1703940e15040c070031160b280d0640062a51140010014458040020001010b071030414410155513662a0100450300034091142401c0100c0400c540780c40e0b440c05101c4c090750009100c141000b050602a699640403124a80000c1443e000410034a220340094460038446044821010b425a501507815810044054000c19900e01921100c0482040303c105050b901c01503440007581181000c0c03440c03420080c151406041401d081c440007411424182e4101c8565201d048a162a8070701050b000e0030060340300c0f542c9407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 44359608 1250 44358358 44358361
    0x40c05030403021605010815010e03100905100e0a02100903020604030606090f1e0c0203070803250314060409050f0105070e030f07030c0e1801020301030305070b070804020f0f060f03 80
    0x1581180056008900075001c851000e6000203010741082060f000e8030b40000c80d500701041c1868041a61038108440505145114a001c0000319141a8000e84808009922260488207021090000c01001d058105040c441120000c4900d90380303502c0150003e01a180390740307014500900c2071841700c02441d801052541e032031fa50303403c10501130543c5014a0343c99a19005481c1d40c201098462506507824246108480f40b441a000b000104208181603055010400000340040c00580007540f150010340b44a00c0da55168007541c0940c0031421503030340c0070300d0324205400071a0100c07200c8082c0c0c00a81160301188620592804500707144251808021030340c2030500f40440940c03c2200c10808100583c1110b4992030100354007070352014103100280c10110111070500413084215261580312042c6d00720202c11401104038582240d200740d100b0b5001500100c2c9010401040c40109500060145031026141c2000d4000030100000740c28264801d448440280042c0d4032072000307881c0301c410f840b241c0076100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 44360858 1250 44359608 44359631
    0x70209040c0f030f061a010207090507090801050901150e13020f0f060304050a0516030305031906030f050a03030b0f210123010f0509091504050309090c0703090504020307050a18030204 81
    0x80f03180c4408202e900c10309141441c69061007210021046c5401680104131352498420301074003c21300a0000d00c10440304900129640209008040c095800840006003040041400001d0b1003c00e4010441c402800e01c10701190a4402160216094045400e1a042911200050029800ca1500c90b80124000c8100424010b001c40e000190a01075025107054448a422008812081c0d010080204809001040e900c041081752020340312403201c40015003507240c2d124180d0100400600f16065030003e12a03004050303140c050040d5800e820b4400b4614501e2002c00601701580b00401ca00f83d241140301500c41405013500a000101c20f049440300f1401c000f6000039055240c02d0284407000c5030b506200041c1030400c1d422840c807502169000d465000b0b0480d9401d000e660029006440d00e120502ca41551551010700b074a0142c01c3c0e819100b66205110320b4003a0a641440e80000d21462062007040300c41da8009084645c0b0929600e08038034102024919811200c1107074101941161600240228 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 44362108 1250 44360858 44360873
    0xf0903030902040605030304052b050f21090a050904020d08041706090a03051b0705090c0408011803050a0c02190306060806090703021f02010f14070f08060303070209040c0f03 77
    0x480d000f0b07241403210680b11401d01d65039101c0d40c0702e003d81240c10307500103600c040b03040c181100685512803500320721643e40d6101c607490308088000030940783c0c004010110002c00004205407440c01000e02c0141048070150014040c080c07e413041d54050a0300c4070002e02150348605080c0052a8458000343d00c9075280c5007140e40c14084045100510b114890220340720880019041c0851a45980c41615044840320580d807001d00c0701c12400c4240c462900045495030310820308900c9803210038151600e40340303020382c8942524614490340c5900d40840107104003180e401402c0f02e0f801d221604020318010000d10204800101ca400b503980200b2168034003008220303641d0003c1044616072400c4600070b403a030074020380e258030851000035817207110542220701c014665051707810303029501d000010341501c040c0901e0303068403841001100ca00700b0139004c00a0494105800030461205032400c2c403494604040400da0303a00c55848040d00c90000e020008041046e0103014601030041041480c4080c0c6c0e9030f141c001c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 44363358 1250 44362108 44362121
    0x519060c030b040207170906040b03070507060614090a051902070809150c0d12020904090f02030709060b03010e0402040902030703050d1409060a080903040f06050c070f05220f090303 80
    0x1000908020b018409480e207402a14011500a55100c1da40300c26010310b0011580f1461000d40c1055003440001141801400a98403528560301d1703003a40d411151601c3c0085801c036401115a21248452602c2a9181c1400c19030b804002e0307400009145d2200c4c101d0702071014000000501c51400000c004080020640150001c0c400c1aa00301c1141548803910103443c0c080c031a091803155001003d0b0428092251030140380145451000601d481c4c94400440d09036140c3c500d007924594000718100c0c04500b0100940d500400d59030700d040010302d08127044020036102c184100c4c6510f072104004030f41503550b25401107014a60040440320303000d0381ca06c0c2043c0c503050811000d802003052603415001c1081d4260485880000003444540350100c000402e44802c80e01800b60030b0644000e120200d0b4088001e00a2f20280c0383d1500c809031a0708012480a00c2c1c5141c5410640c600b0020403410081601c0e09440301740000201d810011a1000c0041902d00a203280c020003100e407030900001405240d050751008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 44364608 1250 44363358 44363381
    0x301110a02011b030507050a0e01090e0a0209090109230c041707090501080102120112030e040204080c09090a050703120315090203160207050306130c090203010b0a08010f06020c0d051906 82
    0xd10207881c0318411350803501c040741c02c180810710400c5a280c100c0c0c4074000c0c40d1040306050420808031a250540c0302c00380c1700c040b0b45403000c02713500085100c2e0500c0c104d01d0141c01441c65044c1800030f480c0c000d40b160028044409445900c00d007034000f044e0702d05c024805036070142c032551789840304107903440d4910b9031745040300d2040301da00302c0c90a4000b0460030818001c940090058403400e041903440d2504195204206403410b404012880385241c20039a580d000a000030400100241410b00e58101000142207000e1300c4521250312001d0761000080740072030403008407900400140c0308041440c130b094018121081d00b41c2400c810000780420300c81e45c15800746000d4810100c600d048102000c80a81c1c0e0341c1c3d824020950b06611050009404250b01a001c1303d00c1403040c800c030b580300399071240e0303503001c0c0d8100b03800c0a41110310109040f1021644200d40c81d00412022f0b0180948a180020180d243c0c0c40085020740503c0b00d0280b2402400307020010a42c0300300c803000341207156030b1060414030014007a0707015a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 44365858 1250 44364608 44364641
    0x5031203040b09030306060f0306030313090e011a10110307060c08010e01050301020a08060f0307030609060203040b0f01030c14011e02060109050703020c100b030c1809010c0912030e0301110a0201 86
    0x11a441110000551b07120324006011289801c503103940703980d03864100510003075061004000711014012400d680c0d00c010000c1e02c0001c00e01d80c583c99980c1e4251074000800500140742c1c820501210340d40c01000325821480360800a0100310b040c60a070341584100d040140981c0c0c00d2040040e45140c1c070100702070481d02100c3d07034110141d80710b90800d4245c0c8244414540051044c401055041c074040036000c855400040403a80c42d9a56030307490000384d41d2548001d50746a5404820001807085692006038800300c1202c02d809158150b99a03842d0348512401010b0841301082c161243e235034014100c110198024400030b0303140650703044d8029514007003405226149400e24000c101c21600034026144100d070f11001078050300112054880050941d00500ca515225203603078207601c0d80362100c548880c1e803e0f1240981c028540100c2e89801c0d038103d08035100c1049820a408c03c000070030407002c5800fa07903040c50400c60207000400040d0150414180140d1050b10000d03141c03002580540c0113198000003000c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 44367108 1250 44365858 44365861
    0x915160b0103020411030408070201080601051303060b0f040903020d1b2102011a0a1205071a03101e03020d05151302090f0112030804170316030f0b0a120c05031203040b 74
    0x4001810b404281d900800000080c441c400040d07020f220233503480281850001e042442c0c0110580040c03025a00a4414641c1da131504c4549041c10b1072100d04803a07042c0da060000703542547e0020f541e034008040c1c01c0304115401d01001905503034200d9400f000ca4119407100701804003001484a50f40010f100800950301c0c1c100701450a00303090707001c8000d0b01c5c0d00404000b074045c500005400d120906640884da030340036228000c07981e4840e1000d220300101001100684a00e0803580c0080d815801e40c0040200450955260388129100c03104c29094a0741a036910b07240704003514206161031000000f103a10b080008080004410f0712004544280d0300072500c54a00d2780310541107100d01202130198007281450010301d000840d0140d110319030010b218901804085090038035000c3d00390000e03104958003c1503c0c140c185402d525003c3c0d9030003950781130410004006690b0004030b07603113118070910f8440c181184403d01805004020000103040190668444101c00d982c118019802143c0403144a44101c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 44368358 1250 44367108 44367131
    0x5130b090a090c0504020a05070804080d02060901060b0f07030e03011406150301050d021c06050103110405160c030e0a0b04120c08030f0d0f0b060c100b01140915160b01030204 77
    0x3480c40610f4001c0703840040b4505000c144000380d4003000c0c036201404400c0201000103007160303004200600c0803a0140c11001103201000b0f08285000c2d05c2d05040da814154140a0200c18000b21411000841c6c0c0055940d48a0f140681d0b81001c04c0c0820740e455440e11a195a16026060004d4442c04e011280400d07021503401603000d05000a0148a4003c00d44803003040050810142e10481c07180c6058651100c1440c40e51040c091356001d0300222003030002d1328800000d5041a002d110340000300c0843c40bc003150031810009001112045002d420807a00d0340301214030ba110039161401504040c80303041e960b15182c000c0a80ca922910600f121885403985000400c0c240200503641e00c0c13060585414a00000c08064034064421150000b4040c0e0740c0710500c11640d9141c200800340b0f003004c60080c000c000350f0042900200d56540002c0c60600c00001c10050800e800c3c2d40032030310001c07021030b00e003d42140c207842c281040c0d0103904601d850b811420f440920910440c03508160403a4402c403001e010420598 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 44369608 1250 44368358 44368361
    0x503010c031404060f02040315060305010f0204080c0906060408030c010e070e0103050d03050603160305060717060d031d0a0f1401140d020714060a0605030f2d0705130b090a 76
    0x1500300b44200e02d440071500040803a00400c4030b9090058026082c107440740ca5480d030510350307202071820095884500f007003048002c0c0100080305070340100850419140c2a4030036128045048098800c24a40780010f0b40d555403d0181c4001d00038180c1100d441310044403056000340015a40c01d10944540000024240c0840003164140e82d4440c01500c1d040800003c00c0d0040d02014040c96814056500e000381800902010b100095004800034625418080c60140c083c100440a1070750b05d010354400c00c4401c2e101c022040d0803040d41490079030707950282001520b000c082e01440b29980149948400680c88408658140c01c1d075150072602503040702c2110040da24440d070321030824180342040c0619110488a68044e10150303014410125000700c5000d14182007960403078401540d556074010501003404c080040e0712800d4a804020129601c01a484210750300d040c043d24940700c80b00f03210b04090440207001c03c9004220180c40d60800c0201c079490a40034146a440007400b03041c003000011601800d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 44370858 1250 44369608 44369621
    0x21903050412060b100e0111011406120f060907050a080102030f06010c050f10020c0c01030207020f040e0a14030301090b0619050d1d100b0603160f0c0b0702070503010c03 75
    0x40e1112407416240940480c19a03059840a45406982e401c00c542039882c1e9880034407002003142c0c1e0700c441091100d0009440c2c0154035050f074409a140c2444001c45003103446e1215004903003103507203200d11080560260f25200310b0789241d103010f0140006100342c03984001090800d0b40e60884804103840e449001641c01c03800100c4440c094010308a0104180c0d500038241460b099000d103041e070300d912154586180c50010420b07140b0007210350010721521a40c209110b042003c03e0246019450800103800103440340c02d222214030301c41c41e9550350100d04030204121030481941d02c440604101c0f0380003c080e50b1030350030920031680c4003400c000c43c0b01c51038508102211014400e007044075010342201710302221540c03c034005012045036141c2510820140300c440242515206000070002d02c188503d12400380c4102c540f025010324403c0c014488107060041c0a502864000d10303050142c0e088615040350200c404d49009000d0300d1021041c03240e2164081881c10503110b042e0000d21034505d00b04400c5003100c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 44372108 1250 44370858 44370863
    0xc04170c1002161e03060e060703180203150a14040605040c0504060308072301060b0d110f160201050d09031205010b03070207180f0608100507030213030b0712020408010603030219 79
    0x210072800e0101420594410340c0c40380101080b400445d0700c0b55603090450b10a640b11150355440502040841d0b903140c002d200c030003098803210b00903840e1160302007079a4030711400d41142400071203000611110301c0d40c1e005651002201c540980141003e0600d103004000c103407400c0c0d981c000c05c3c1c0004515410240640d500302d90f444240140307444210b44408107a00c00d00034100f00038220b10300351000c002d14240030340b00c00f401039100c9507a40c40500d880c1010480d8152081c101c040c41050003440c01c3e44d100c00040c0c030304441901201c0400c044440c80101d42c1d80c030501d42c0c02d11f5200d00c0c0c0780300c680c10b141e40070f04150010b89000d0070800944e603c410610b1814081101d004006034031060050100500c8060000d01107050707018042840002141900c0994055400c00340c8240d004000c100c01e18200d5000741038004055007001c514004a090180c95410060b003c0a00000111001701e1180751007030205080b0300c592450211b4139942c8600300c0a002c2d0156110076001445040080140030700d20b00078003802140d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 44373358 1250 44372108 44372143
    0x1205011a03070903050607021f050c091e090a0902030f0604120302070501110c1c0503130303020f0702040e01020408010b060f070308250e0109120506010302090c04170c1002 76
    0x12410039000c240e550005042004020a6a02c0000014401c0101c54000e5140f600030700010306e5180300e02c040c0d1f042e040c03019003201424402803101c103020941c201c135000300c03050312412100d140d86001440c0c2c0d2503082c0c000315088600042001203280103a4803926800f032080701076651840d800314440c1ea5900c402d880180088014400c4481114060742c0144102841000082182c012174100010703683c0090746002c03ca908540c0f1280c3c041c40720747c811f038000110030703040180c1541007196445180c1200840c00406060b40000c1c0d0840c0c103a8510300351000c1540c010814400c408480b01d0341800303500b080c03140c1d514544c01c204601c2c0c1140741c020207403141c42d440c03405101d04150250b03c0480b40488040c28010110f195045642d00401c0446804c40f103a020310303255201804101000189046019480031080141030081c1c180001c0001c5441d504680e0111401005c80e103030004e03030504034811303903002440b1b03858407660705c0d240c3c1d882c042500c1550303038400c07903440081d142e00c84000d0303860f001c25541c5c04a000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 44374608 1250 44373358 44373389
    0xb07020a0e06190806060102070806070806061308011503030f030903080420120d0f0801080619020f1c150b1204060f0c03051008011b051606150303120501 68
    0x80707105440103a00c40c1000700624503802d4500042d55425409820050720f5811030350410035156010080a001008840018521480d04400042003040003900c403501c41e580c00500824412800c1900340c01805401c0300030071080d850b8070684202d82005100440104119400c0e40544034060701c54071000b10f030151151022555030b0703a02e07000c0c9031507024060000c0011030b001c015010b49039025000840c01c1c0240042080045820780544040c29141d100420820028010b01c030083c000300340140c020710940342080e03c3c000703150441d1000e1b000d6805140004040840c81009060b040b010070b50f20000d030084100700d0440e0b00c1980d4110800035028454041600b0400c6209142506401550060084100051407030119403258140c403442c06403140020344401c28450800d034800c510310010800d400c000c001303111000c1d80c3c2262500303503410381000b4088003007203240c00309490481006c0301c1e40d032102c01004901d42c1140600d8561603140420340018401d0850b4020481491042038185c800c1c061214812 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 44375858 1250 44374608 44374619
    0x91112010b18120304080604030801140609150c0c06030901020a09090b0607030f021002030a02031501020d020607030c090f09051f03050619090203010f02030711070e010501080624090a0b07020a 85
    0x14503072810109440d40b101704000140418141b100a00480c8030341d80301c05c1594501100000705100c1c0031081e0f4031413982084041401d40c2d4096a407042010130b0080503490b02e1107800051f041103446100541c11600000810000e88011343c01081d00c0d036890748800d501591252074500407501c0c3c80340c0d115046a4104051808240140500d03c40d070201481160110401c002101c0b0a90300141e130170200940d004030500803040380e280710a50381204288024801e4943e482d10081d41d4010242022040c9503840c0410740342d040c400c0310018058040400360144040e544c000090080c002150a078503040001041d84520098035894202182e8101005084c01d841c3c05140301200d02d008040c83d04400e40c1c030324a02005840a0051a4884250800041e12450811400303880d4011080e521101600001400e0090b448414070312810b45a080c60030401941c0c80002050410300407a1a520000c0890900c1012a00c0200024448418156420f1180710754441d181d40c01030140f03820084d804031000e85d080c0003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 44377108 1250 44375858 44375869
    0x303030e070f0305010902010806061611040204120507080c0102061e06010905100905040f020c0703080d141003032c010f031b0504031103030702011d0406091112010b18 74
    0x3030a90140a4902aa641d44010000204194011605079444140d190309540e00400034a501600660302c540c0b411036121000401a1050240140341030744061140c00c0b43d4945038165400b5084031210b992010625041c0781d5503e0200e48206c20b510f10403030380717801055440807450b14040c030240a801d03440c0b141c22050804996400a00c0c0c1130400c00071120001c2c3d6a40c076a1119100300100d6190b440c1c42506202c140011f0760b9040807005251401003003c07103d903410000d004000c69030017050310341c1c40c3c40d0070f402c0c0310002d1300306554a004540204824040c409405408075422a03200c1d0b01c40aa04001031014040b18000050b040240000c090060f6a81d0394050f071501c1070005018900010f0394908080780c80c454110709100540001d01c046414400c01c410740ea20300030452002c0740154284111070740001c10900340000c402c1411f5038901c0b28840c00341c403180c02c240040c00e151001400701d41c0756031844c06119000055102d4003411003100005041890380112010348030016000400554070000388034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 44378358 1250 44377108 44377121
    0x1120201080f040f08030403030e0c040b03030418020d06080304090605030a03090509070e030304062309031906021c0b010f030902011d0607080301150207090e061b070f0b06100306050307030303 85
    0x35131a002003030f2440d0018110000542c40390380320381c500284556114501615000c4040000c9009034500601c1d03480c10f590000981e000c032141d4a0940c40c490350081c4074800a409510180c0c06503d040c0880801c01d28808000740040e261080010044245e480c0205655815005409408600b0548060011b0f040040c00310b50710910b14103100840d030070010042495580543c0c03001d40086c003400c824050300f0f1000f1900d0000c03d00c0315070074a410044941e00190715030050614510100b2082c5600f201005440c1d019942101410b6a155000034001051301014080607005280091003021005030900c0c0a4401d8510880d01a5070b00800807240013200101140700c5407046a0148007172041c01c0c000b07540b010046011b8400500d80020000422001a1510035981c104080d000e0502c0b00114040c0000210903920100045031110b00110a10050145100303111024000103009550784085c0414640540e0103074000b982c40103858940380d1000c50441d05e560203041e9241d0016401040428881e81110707 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 44379608 1250 44378358 44378363
    0x809010519030b0a05030f0303070f020f10020403020f01110c0f130e0a05070b0c1b0105040806090601061d0307050d020307080d121b050d090507050607031701120201080f04 76
    0x1a440c0041e00341c0341080c0580d152a0140c002616a40c00c2489420225206402410309400a00030410040b207840c1c0c403400018109020082c81c110b40501140c800c12a94401c058030750b055030b0500103083d92601c080c2d4007500050303004180d80002461254850401aa4079083e01d50141a001080c3c2042000324450401000d90018102c154406d003007100e0b01c520111036540500800c1c50007002d10b802e904041d140d62250f4060f44040c0011140102c01180e448034070100456926007901d55100140d0b140d00440c0c024880c07a01c202410419800000107003a81641d140d501c40d04000f10560080d0540340607800c0c2110340582190300c0410090800440780749440784014213984145031544c81e041d280c02c1c400c4045170000740b00c0e105080680c00c1a071042c1049001130400f500c0544980b1400900188102c0e081240c407036507204060401d008081c080c1c0d1000c0c0600600d99a03440e1614103005103da03106d4403030150703640b001e48000940515079410b00c0c1e148a9042e10741608581d80c0311000060380c140100103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 44380858 1250 44379608 44379617
    0x60a0c0201140c060906070206060a03060b0112090305091906020a030e0a031a040b0f07080f0702070317040503010605090402030a1412040b0c060f0405072601061401080c040b0403080901 82
    0x140c4002e10034120107011218007410040c0101d01e030036041e081c506407020b04041c081d50403c90501040c1c2c2c40d414001c40c00ea903040700003c2100800d550040392a200d00201a1900b1460700000da030405030b200000b809008821503040700c04a02c1140108032200c1c2c0c5105800c096031000e107540d000a4000c50302100141002030056254907503940351440103145c40078082c0b5040d5504000c000800040303168854114101c0c2c4179503400752400c00b1000e8a82c9202400000003001070200054450340b08001c0400655400800e9014220004440000a410a01480c0e110b9400d240d000308250600060341442190020001e10241e00a034441102c0d18244d00c80b0038045002d0700720701d002e003103849a000308002d20b1042842e9550b07a0424a00a04281b4090808030200303024009000120700c000407641c094030340c184203840d1400700c0301c0c5401c200465403451428695003030060001d0407143c00400240c1c1e48000381c0b12061259105130160810f40700c0c5004501000c6800e110a00100c0e038050082c18125006041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 44382108 1250 44380858 44380877
    0x1d030307030b030f0d2601050a06110a0c03031805010c1109070c0c080d0e090415020a0e040908070506070203030c0a0507140610030c0f050310180b180c0609060a0c0201 74
    0x10b250610303040c8014000410b8040d803030313042c0446c0580d207031080071070700a0080d1032503505041c0000c01c400340521820040103c2154204020721f82807024070a010350050705060303442d81d00d1070040c001c0c208500f0f07a82a0300a540b40c0003e01075000325040c801301d56102965030007080c0d8850820010101c090108020047c503c1e49010000d0180c4228001506c084402416003000b07000005181c181d030b0b141c0450040b40800c003440b0010f620190115a20002e080000d038451504407000c0701c05180201305241e105051803031042c10b00c0301c00340c010182c05004001b960215a22250140d03568841030712005036140040060010b8148a00e001e040002c1c41b5420005041680311510780c034010040d2144403910f00c2c0e91000b001042440c3c10484c000303013404144601000c0c039100000c1e403510400e00c61802031a4440c0d500e907402c0c400c58448151125130113100350082c0e04040004c051020420f0030b00c003005225a12401d140e500d00f07d001d65030000001041c10b40b0b410040581122900e003800f0040b41407214210703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 44383358 1250 44382108 44382133
    0x1303020f030d020903060a14061e03030a09150201020a0c03050705070306110a0f0f020c040b03190813050307050d0201050c1002041707140f060304051507121d030307030b03 76
    0x30510805400b60250721050428101400c1004c0034000c0c0240a14100d4141d0040b0003560603554040c00c2103031128060002c2160a84c040c1c1408080c41c1d5050000041803200c0a070009503000680b003d101254150080e242401c1e4201d03c00c87d544400412254200c080c002032060004090b690310540640703086640d40d80d11401500c142d40700f544100c100c04144111295440b2640c01070704030703c5140c80d803114503e0440c0a5113608010302d0303060007540c507810800d806031000c2010f035541020322030f00c0f80d4448141d07080483c0180c02c541101000c1b51403201700001e185c58006150b43c1501e900410305003488851f54015500e0354012a0b02d005c2fa8020583c00240040b058800782c070081000c900c80310a600c4100d485241804403503000700b070802c411410f46840c41d441e80d144040140c40d068880d40e0740c0341c6039810003a1174044c1c10044190702d000c031507007007114966010440451100b8010300521a07140008905401141002c0242c04264000d00010304c40078480d0300720700c80848029080e20301840011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 44384608 1250 44383358 44383363
    0x705010204060c11010201151202040605061338070318030302100e060f040809030708101509020a020606060a0c0206070602130503030c0706181d0a0509030a081303020f 74
    0x207a10690104010010343d006104c02d0120b07000c4101400d03c02088007204400500c19050440c5c010704007061840300d6034034115200c60b4000d1018000003000207807281d404147d041d50800d00b50107a41c000076102554034038020007000340201000c610801d02d00c020200504598480d82158409908011020781c0c0d011f5002d22486088010310300903400780c1000d00d00340110106172000c051044d0702e203900074000c001c101605402e146800c182e0010384542d50f0300c0580c00081c90041c3d00d400000c2603010300940c00d4040c05481e845000710314050342d2004104c07940c81d04144220300452030b0381c00158004100081151805400414004071700b420010b01c0c090440d00400d00719003100000b11429640054001c072050001c80b104c6d00181800c030010740c9040741040d03006031640018840d0006000310340c10340321030301d40c29000d845010b044009000c012008035600d54440c840302c10380d024400300b4030f02800b00c0c26035040481214201802a02c3e200059141c2c5031800d444003010420a900f18024800030000d0725900703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 44385858 1250 44384608 44384617
    0x30c0304230106150504030f1103011d070f0608060609091f090b04050a11070f1e030c0204240b130503030307120b01050415030f110d270506010b070807050102 70
    0x2031030000100182044c1c01e40ca0421306110348101800001d0104200040e804407480e074015030300c0051003a11458903408640508000c030045841c005000c5529500c08000040c070344101c0d060f003030000d1070740c655501042e9512841515081d400c01c104004819007400c2825480b500820a07101e6121484030f181c0c425509100c01f42c0100c003c2070b450321460400e0386014007500fa00a68022810010a620b450200300c0314401c1d800006e05207855501a00144004403032034814900000120304416140c91a0040010030100c004910681c5420a01d0034100d00303c05d408403806074a440154000f41c10301c540020282c120303001e008800080c50385c02252030384003807001d18013600d241c0d1102c4141e1000745400c0c03815585d071025a64108801800708018800303805000344101d00e40341c10300007004140281404042c1400d582e807003905610000fa11411408194094090800603e4945110090691500c24101d0610001400d941d02010040c41103001c1280282029032180d007115250072070341e958080c2603800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 44387108 1250 44385858 44385923
    0xc080d020106030c080312040f0303020d091202160608010501050906190e03060a090803040201050a0c021207060f0203030402032509050a06050411070f030e010225050f01090b030c0304 81
    0x1181c403410030404c010010044054405440507604200e901d00340103402c264000e1020b4981c4244c880080d01703043c003d80c1220300780c036400c000c240407440c2d540c10103c0c0150891405d000c0107210b80701d000142d2103408140d0009507840c55580c180c041c3d10b41001100c46400808000d5800700e010803c11002d502c00404000c10780341c094a4140c20103520104240c2041c6008190440d01410500790000068000003181e51141d030909007152030741e500f08002c640218810030000e420025100002a203444001000710848180d941c0e60103450030303c001d08a07201e000648009405901408104401e0f0269180c143d81c0c0c070500030581d050f60f50360740c0200c10aaa03800d0b44d080b145944c3d00c020034021400d1038080c1540f1200100c81e058a0b043c2281c1c3c41d54000041c01ca0084c08001c0b0300c05094015a1091003103405032402075803040c2000c80d02c0c0042d041f01c00c2980c402d40e0700c145090400d208295008800000890740503120181c00c40c0e580c4c5452074400c1d0f1005000305c036030380e4240b200c41c000740e403083c4011054070a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 44388358 1250 44387108 44387111
    0x6062110050109050904031b080705010524010e0a0e04030201020c0a03050903010b041a0409060b13020d06050a060c0b1003120e030106090218061804092103050c0a0c0c080d0201 78
    0x41c9000005410901c1c1c542200e80254601010440840e07040450b001003003020031028036468005003015005800340d100c004010f0f5081405001c880340042c883d041142c4502160040c450103444015070b00c200c940c0c040c0c036070070601e80001045007401c44183c40e540580a40005480c210840b61001c0c01d11001240850214102240c1840c0317605091080c0f603811482a01e041003248451041c4004e09141010780c14400c0d174851844104002440d040003d040802905c038520010381841c00340003035003202449103d07480c54007100003490f160048448003114a50b444102d0302001907110407580042c000d0204020350381c403e800100050400c84020401003a650f20101444014410107003550001d61010010b40c3c0103224040f804620300d19a00c126200445407140e4802d0014900c0800181c000700d41030b4028609440c400c01e000f02c4000307001c05002e5608001580014081e0258102d800030740d0701b1181803c0038840700c00e595001d43c03810221030b4054094001016524038503c0c0c5400c100d41a902e0040c2d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 44389608 1250 44388358 44388391
    0x1050f0c090a061404080105070f170f130c030804170c04050c0313030c050a03031407020604030212090f04090506160309030801050411090a060504090606020a1502070807060e030414030102030f060621 88
    0x6540054bd4942000a01d0b151603594200110026031b045000303440b1184a494800110007000264500c0100a5034400019600c03aa66a03944850414041003007140c58000c04c4039841080c60503108151003055900100b5086869041c0005240e8403030080480500816110b1500400c80402009442c244070307607400b01d142808040e0802aa0300e02501d45803e41d0b02000a020029401050381050b1151440c260707512020000b0015080c00302c65031565400c81c3ca08180c281c1071003804a01d0034850a6604100c80200c81d19020440481b101400003500041e91100141301d245010307040001e02d1099840400e0800d60070704001a1590900d0740b119010500c0020f0410010800d4052240240490f00141030501a940c4031840300d210349500401030190b000600c40e0421400d00245c44403d50004e00400480c001054545e540380d2041c0140b6179181c50303540f0003190a1030140200c03032155445441514040c0c40304420302201b50000ea02c001c0017840b00601000b410f48011001a00ca600b041c440c81940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 44390858 1250 44389608 44389637
    0x7080604060902130e0c0603090c040608010c0e0a1202060327010b01091e1809050a06020a0806060301080a02151603020a0b0603030a0f050d110403030201050f0c090a06140408010507 80
    0x202e004c440003582001641d0010890100303a100c4000342c1555125030700c0d503403000030380d081004850104d03500502d0800e002c96048815401100007800d0b07a01e410318030f00850020440e000c0c1c02da1041c00400d40e0b40c1c0f1005401410108003440d0044029190701230508100d1103545074854402080380242d81d910301c00c081856a0020403980100241340c040051800103150418603440c1c80c0c040e241c82c05800014018981301268020300545070800705542d0404070030b01d0000081d502c081c03002d00015145030081445881c0c400100d0b130403034110348010b050b650699402e0103250300c4086440c0e0150384050090b14130800c030b6030343e4250256201e903002d4100319100f403400a1442d00050100d0307000364400c1c0188841310340c00040174030001000741091740d16420002c128030040c0c10500040d6522f0040841c001003090340540159000700440c0014440340c0d5240101e50310f15000b9010103a5004807211010003096001e011720030100030b14001c0300d41c581131f05c1e1070b58942541c8050b2112400141501c0000300d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 44392108 1250 44390858 44390869
    0x60804020a0603051b09030a021801090c091211040b04110c060a0b0901031b05030a110102012910050c01060308070b0a020c06040b06010314010f0510030203060901030b060307080604060902 83
    0x103065242401c001c2800c0ca05107104020b40b11150309018403000241c0e01c111b50781c0030805060517176030041448260000004018010306d0080c80ba219200f8244079198030302901075a0501e05960540e0b2005103510000c5c3c8400080d0062501d80540103940c414038941c0540300c6008615010780b00b00115aa1468200c201c5468400d00810000500d40b40c5890210300d503440c4c83c01141100d03005000803000503500c07010800381c4246940080e034140310702000d0300100a651903681c64002001d8000308409441040000c6403808101203203c40310003001c0324254145090818140802030600c0c0a0b401c00d2901b60701c09085603025001035443d00004101071082107030140030710798024032160055091903551460599521406080101b20740382420010300c5a9110740d000c50b01c00c00248850304810b5a4a0740c40c42201d820340d01545002e90001060008654000c0c02201d0198101820410881c0c0c41c1d912008424900500596810301541c200040c40c06000c0141c24091400340e440040c02140a104000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 44393358 1250 44392108 44392129
    0x60b1216091122080303090604020901081903050a0507021305061c0c03030302031b0a080906010b070506060609150712090f080616230408011d071208040f06080402 72
    0xc2060a042e41003260381d1007001910301002c503510b4002d65003894a0b144180f8989142c1005100d4400842040354240d000200305020b5802601c0c00302641c0d82f911911074494003610030409000c00802105070010b8400d90003440e5961842c43c3c05810b016240c0e0018440c242e18400c0e9403801ca49400a00100d85001c0c201003070b90826a0302d101c1240e030788c240d40340006c540c0300c1c1c84045c040c160f0200000d0313911703010700e01992916400c0d59015541d52214890180c1100c400303460078041485940000b0440701e22050803641d031030b40c004000b0001e59075208200074503030b0701c18074100b82c100e045210305c03141516000c030251031041d10881f1740c0d100c0c458001c80010311011a40d0304c804107405200d14100207071040401e6a503003104081104d926004440341050381c405081ca050416032440302d5100d17580b5200c0319005042610500d600903c906154501c504101c0030342c5141c100300c140c03c0080304000c40d2100314401010310b03120b0404c05082c41c0d522810200000801d502c0721300410030719030070071045103032444084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 44394608 1250 44393358 44393369
    0x501090b090303040c0603020901020a020a0e150306070c0609020f090106020d08130c0306050402010e0a060518041a091003120306090e1b01051303020a06020109050d03060b070b04060b1216 83
    0x1d50441c031305030311703404e03030303495081c0b15080615500049507070541c0d100b84075110101d5005412004029078031312440b41b040c4002c8076403040c01003030307459035082900d40810018000c0b961175840f15002d911a440d0075009020000c400c0360b1014140303400030740d030740c0720640901c0c000e007031540141445044a150240036804020f0034015081000701c4100d002800007507824003500d400080000302ea60382c91005840c0b2240c90103001d98850f81c1c8030000684190b01ca030007030003030000b01c181d060901004c0c0d6090200f070365080740482c00d241d4880780b40c41181d0308100003070f40d81c401d41c04102050300942d00c0e1a4010300c141c901104900098607140c05122041103802005802219240107004440304c0205078482e80074111707103d504011001845000419241400e00050b6400a194041303040d42c802020b4020988480202c4540c095640c02c0c5c4181707406442a481299440180e880c540b0049540b080a0010b004000b201d00035556001c003202502d808440e075100c4401d410003064a02070b000210a00d40300c065001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 44395858 1250 44394608 44394613
    0x1707030506010603050919080c070b0c1905030f040e071e08010504020a02031209030a0e0904120e1f0c062415030e060a0b0a0605090108151c0501090b09 67
    0x204006440001e0309811a00b40b0b18000a4a4a50345685800c025105c2c2e5410100022001140c062042c00e038010101076a5400446c1c0394561703103040400302d0f80203500d0510700b190000031000420101003510201110711030000d44c1c0c9004a003900c2113640760020b0b04030300401c00c1014100107425400c1200120b08544040407840b40d51000c0c14000c0140b101400b6180c012500840e89081541c02081030700c03804a405448401507160280d80250780e50001018840010141c0002200030700700100c2c4980101d03004554a00c01880d24072058841c40c0d207081e03a0540000503407110002d1a0804c0038040c81c0e188456958400c02e4070700781000000e503941001490880c4204400d1008114072007009102140e140400320710b06101074035815001001d01c918403c045024038010042c5054542e40302030480b00086030840300843c0c641404881500680c1d101c140480c116002103142c505000d040c035549854001c02d41c0d4018050400c0c4c00d00300a15650f81180e02c1d0b9100c104070410415011109a44403085100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 44397108 1250 44395858 44395873
    0x30603031b03040513050a0c0f021002090a0e07020a0b06030c0d0209130b010e0415110a110a02060c0309010201050a05040c1502010e07230a060504090f0b040f0617 72
    0xd48a201d0550403001c00c0602081c8800c600740140141c60050074018098201e114200300d240000d45811171f4845600c0d0701e4230720840e4085006034150421a03101da070040592480101202c0020343c00703094210390142e992040019460b5402d440c0501c503150582c06801d0305e680d145840d144043d0007034101d9101c0c2d00060410801504c0e204011444541c044401c0c00141e2030385100b402070f050040d000500b0f01c6050b4000800e210480d118950b01913480340c0070b815411007800040c1821201141e8803020044c00420112014511400040707004007c00d0b426182c421440b540050344036881220780641c80c2d0004142d18584d5a0284145a03200007031000900c20303490541e85451891429000c1c00e00401c508410110703210b8804d5102c1c1000c40e0362001202c0c1e4882e251400000452400e144450f0200d00489081020342010707014041100c0241d00d486040c18185000381018140c0c013854076110551f00c0d00074103507698880c0658409074100e40c00c0040e009042c0354507015404901c0400300d086070302003c2c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 44398358 1250 44397108 44397121
    0x3080601140d02090f130603050f0604080414030f060708060f0a05060403020405180d1707050c060601050f0706150504050f010e040204050a06030f0c170f15040201020a020a080c0f0603 81
    0x30202c62040d41c03100001652112068000f82e1201100720f0019001040c114886a000209900100940340100220341102c080c04591682e50002100c00820081c820b000170402c0385045900703260700700c2000703050710003551808504614000040700c604c0002000703001440942d040000c440060440f0546002cde61072820400469454425440020302442e41d03080041d08940c01d10b400d00d83c0c5090300500303075140090481d400a10341156038001d95411b4000700701160319113014904445d0012651030250229940300070054480360000480c600304050100291400192103104100c000760884459240303d5050100f84012900c0081022030454075400043c0082100b1900c0558810ba0485d40440c1c0c03662101e035041c0107090300d0761005011011001c5000100700d0760344054416640200071001180d20503410701955845101c0709540d04d500034501590071410034048043e403050060044a8200609a010449a02051f88280c0d01da811181301d00c006890485142c0c10300840c200d40e464190f06100d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 44399608 1250 44398358 44398397
    0xc030e0111071106090d030509010e0d030e10270f0801050606030406090614090d0314010f06030e010b0303040b0a030e150105040509010b030f030c070e010b030c0a0306030c0308040303080601 84
    0xda02500c001c140c3d044000240c0d68002c200c561113078015201003000103481c507000d000c58103c04101d41c0883c9101c45a1095414000800c006294241da16030032244007000c00c1c800c00304002c0e204401007080c0ca40c40c20790700311110301207040314260f031156407941240f030510788407181c0b503d64114406990500007844245e82d030b01c00c20350380c025410103400a0300d400c003898610000c00c04950302141580f00c1c11708000b0206c0c004100710705000c0960318203100c0f0384010082d0080c004001d000c0c487d991080c0960a0004070b04c25030040d80312500c00c1000003030003005400023716541065001004945002558008041c0d060040454203400c1c00c0090102c0c0720350440740f45000301c0c14011240541c1d40c501c0055802c0303800350040d40107a01c1c06825100d5a0b04a0490b1903141e503c0184010707014032400000160109d82e100c4240d0403070b49020300d8541507465241d40c603840f80d482808003008160b120000400802e00c10401d0400071071050141035034403891031402034080c440040c601da050105c80c080341d00100000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 44400858 1250 44399608 44399617
    0xf0607050d050310050a0b0a0305060f0102030307030f090f0803010602281421030105270408031e01060503010320010c0b0a02160803010602010e030a020c0108070e060d0c030e0111 79
    0x81d800c1407500c030b40d600590641044020340c051503001c0c0c104800010341c9a140c00c0100103810140e5401d00055848505100020310505e9100380140d10130030005448503c039602c5500c103005c0505012075184182d8480494031400e0402c01c0d075003c0c00003c01044025010410031010016854112008000c07103149003400800b1004040c0c02c0b410518046040c41d40203001481246c450f60311441384d0300e0000a90b40c0381c590030074000d86000b6001d1581d0302c10300441c2c030240701c00345520904c0c2d9240d5a03510742c1c0d500581c540007d8003000c4aa02840b01d04c441c4a60f0b8480d94502030b0501c1d5988036101d600d581880107074101500035078103558500080c2041c003a603010003940c01081e0018070215490701c481104500078400c02c14008516950900c0c0e004c200282070006504031030090b402030205483c00c1e03540989a1003010300640159002c4030711001d09500502d90150301400c01d0500c42400d407401c0000c504a9404406103c0601d40d0382c1da403181e051074061045026a0748288000c108100c025150305249204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 44402108 1250 44400858 44400883
    0xd0c05010c02010c050f070501030e030906030109090c030b0f07020705090405060a0528140901110d050403030f050f070314090a0308150301110706060e0c0a031d030412020f060705 79
    0x29003010744001c0d64043e0709652521503020044a002c0c04491205a03220010790041e00d002030b00307045514000324400400c0d01c00710b00c4000e040624507443c00107201d000b030142c0312044070901280da00c0000070818008846120704280410440e840c540514001d007007410582046201300c603c1e0050001107000003c81c15800140400700007815265241d65020303491050200414104c888005101e501e0026000200c500b0380c2c00507640c1039515020800b5017651031000004207080028054901c0c0c040d05030b00000d81140c02400c000508661f068003030001c5e81c4d012502a034a044541040c0600d9507407510032441040c90440f51440700e803c3c24401c940d11713070862050103020000c031000442c03100d5503da4840524120010000c200044203000b0303000c65904840360680e2070701e141100004a03081c80000d0184980140e440a41c50045c9002e07043d0020000030041290f11703150386000420000081000b00301400c410849074001c40e9860ac1000091505001e075180200001d1000c5000103100003000d0b4030820 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 44403358 1250 44402108 44402117
    0xf0b070f051501350a08070807050a030e12060105090a020a0e06040312020d02010209060f0a0e0a030602190311032205070e0f0901091527060b0405060d0c0501 70
    0x40e1504000b481e18072500128400112010300000700c600c2203221086032008010032464900e01d000008010707154914401c04100e4101c0d41808000075140030040c243c0070700c00c003802030030100183c8819103010f81101e412004a000c1550702c5881c0d14040300018042008440148025810a00411005200036111208854010500b00c54240c0a00454900c105015000903141c66490404081c11410b0311009e4015010f100070a1203620b2060085602d1001c02a0940307203070464040031030041da485110074a0411002078681402c5681d1018107400940c0101c4c809600c1c0c0a8079613a140440009101e10024986050300d048541100c07601542d602c00405040c82c80943c04080c0003403403601942100818602503040080b0b540721000400300d00880e6075103460741c0c07d079486c440c4407400c8075812000649051018124004070740450340002035800729020441d0210000480f94511062040d0012140b083c0c950b15040d8460030300380308481e40301508889105110103261500007205440c1d0040c0d03410803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 44404608 1250 44403358 44403383
    0x110a0213020903010b13020d0605010f050406050a120e210406090902030c04150207030303050c0708070b091009110f040b0a030f020f090103060506090109050c04061d09040305040f0f0b07 82
    0x255003c3d405001d1740c2c1c1c8040c2010300307012141c8111700000d6000c00303210140c1902d07000000c626544100110700440380b203030b21103514150030024140c0399030300a00308100400c19507850003151403860380292104041084003c00b08040400a031102c0c000e10042427804d210b5060108001c0d6607480502502268008400142c1d04d480748002144648100e0b0400244608001e2100d02d02d40e900251680841e402079508110607226010300440b103110302d06024080c1c220030f12400000c503034400b11142e0040d11420403508a080c070803ca060548070702079019078400c40342034a08080c600701900d146100d03110845081125056403000a6140820703804003a100c10380c0209000115140e00780e030440310040040c21035000e5270f5a450f06002030310301280c000340a200700c0000080c440109004540c000d136008213a171424603083c60310849500c0d00112508015242e50000c0c0e0300d8503204d112145018600070381d2a10f588038200703801400038800d9030744480406400104104a804603280564a00307591000511181 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 44405858 1250 44404608 44404627
    0xa120603050d11070b030c070212070e07030c02150603150702010204180506030d020d0503070e0303091302040e070c030c03050a03140106030e0c0d02150c0307051c110a021302 77
    0x400150300001d1503880341c4894010050b421122154640e40103400311408241c55003200966070106a4680301216001e021040052500c081e642408551410407640c0d005d0303980c0000c0321409002e990503400f1a0361688220156603050000c012030300b0b0001d0395402107090400209558000c800c20204c1c1842038032001c0b50a05200307404560040c90510000c5034a03003902d0424030f00070802501c41c03512034032400d0010078002d03002003440b400030042c40c1c49071425541d0758501642d800004001040e41030004200501103981c0d0f18081e505072800508005880368140214407050b010050f0104051055800003c00001e40c8907111042056040c6000b0f91540502c00702a0040d0001e2116201c0c10784000c00085031956040e845a80c0380c40303a110803525220002401d020217581040c0000e0b4100a041d503000c441c02c810b0a0080001c100c191045074500f0740340780c480e24140464072900100040d6189075030910b05611448075080d408402c406070000381340d2680024180c48a0b100e190340d00c150046401e070403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 44407108 1250 44405858 44405861
    0x10c02030d0c03140d0c03060e0f010509090a0203120c01050618010b0a090305010e0d020c04110904021605060403020a150c020c0108060a2102090a0506030a0f05010906060602061008010509030a12 86
    0x81850300c0450b403a103904042c92174030051724104d409107001130b25000002680c59844201140100141400c800b4640d00300028003d2040005001d200b030b074030610102100507101044010404005805541c2d01c500090784800d003035540141200e48103140d24059194007108080e40a070464074000352080e030f00d810f4804207958244680d4000b810310f518102d9080d44161000c0742c601c204210036030a48445c220400100021030b0100070b044565440180000101d0f401d295009045d10840d5031101c8083c0841c47e42c2d0320b0302d0010110380132001a00442c000f201080030a10140980c803104582c1880000f4681c0740007552004806509030401c00e6131404140e1703549074904004081c1000c44519085040503001e590600100c188089005942080008440148c203204d140d01402c0018080d000300d441ca0f884800c100da403501002d960035541c4401c00c4000032070030b01c252001088030380c01402452521500000e102c2c4419407240a8503414001041250344c008021540c0088541c00c04411442c6446070960 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 44408358 1250 44407108 44407127
    0x603071401120504060b09040302010906200409020c01090c030c03060b03010513020d03110d050a0e03030403020d0b041505181605100f1806020c12070303020c04021c1118010c02030d0c03 82
    0xc1e08000107a0230b10081c560306410164040d4008d210a100d988541e03510044c1c3c1003500360f103614083c40280320a012242260b001003c00120030000460701140a4a6810007070807268000c982c2e1b03100f944410800c0010074003032900e0100080f0700800040c0b5203440180c5c1009002d8000070301c41d0039110051010503000e4044401070b5555001101c02840b00389030003524543c0001c403044041080b01c0d021450718903000048405030b99014115041d0310150303a8031801181d80140085401100151800140e103005210705480386080b0078502c03400e5200d09680382e08154640b102c1c001c0d210340c00070303040c4001c0c0ca80d0701c4412401c00301171074014052043c000e4111000c5103900a07006401c00d0031940090040c0d0f00192070503070000101c0341143c42050030b102d05030707840e2064031006002da001049030086502c1d041d03016011002003400e40c00d140b0590103480d141110500840a01540d101107484e010b0300b1107265021114030020700f0031103000301e42500043d03542c040c44400c0e4020001c10b151030404151144034040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 44409608 1250 44408358 44408381
    0x9090a09061b0f090509190b0a0909050c01030b01170103021201020903100e0f06010609061d0303070c030b061503060603040f02090f071812030c080c030f03060307140112050406 78
    0x20b00d8803410500040682c004514490001440150041980d10301105d00034040c0740c0241c800c291594404101e003028042901c00e20394484c06001d0b000409592a010300c8400d02d11500141801003054000581111078011496041024051000b0b0847c54142c4030107055980444600b112110300000d40c0b4068401c4401c40b80c4c15010b80000080314a0090f04003e101e4000f1000f13490b404984a044640c1e290824417076000000d40341d80c0200501c44c00b41130010b501f034411460f02d40040c58000c000ca4078507032040c0f608880380c4036041010814001e40c1018181c10280485502403442c03440c0101e0700940c000a04107034454040000400e042014800896003130560183c20100145008841d4401c09071044904601080780280c004910314454040503007526805007006004024a031011a01810100811110740b80f0030000b500485508002804170180300f000700743e030fa80c40c000050605003d85079014295103000200c140c3e049a8000310300414100e030b0000006110340d02c0c3c3c00e04c0400f41c103000380c51 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 44410858 1250 44409608 44409641
    0x40b0303160804030b0a0228090f03031701080304151b06060803120f07090b030613050a0903030608010209030601061b061112090f1911031207030906020309090a0906 73
    0x207032010032031075501400031280a04e10800c459920720100c0800e0b486551800c1c3ca00485403c43c203000c0b401d0042d01c2c80341504403450815050740e1156541c080b01180c4d5001030700480d881804d0440000341010441c1e015104500145040501e82440c01e81c40d142404907103802e00c02c00000c090310724070b501d071150b580241d00001d045c0002c40c1c1d2184065100d42c440c031801b962000044002400c00c004420869000e10016500d05500900d0107900c3c460540016104d0740c0d0042c2c400f041180070000364014a806144c0d60040020781e140b00c2e25025045650f1584091800e900500601c2c40f9543d0100313529044801e83c2c200310b0301150341c5c0322000a000114800007850b051030034284034082641c070000381180b6820901f14450740e4072141c40359a540c010010b0f00c4071081d4484000c12a9030260851503290891056440309060b101080000c0e040501c51002c08043c1d5002040080034580d110421070b004203030b07a0000d035140007044e5000c02c41c54070005110035407154070340a90904010300790380081c440000b004003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 44412108 1250 44410858 44410897
    0x80a2102071b060509090c0a050c0106030b01060e0420030402030f0a06020301050901050405160f111207020123040308070206040504090c030b16020c101707020303040302070e070c02040b0303 84
    0x501c0b60400d079510082d501c2000c02c28001007962802401100c070000001058650560740e01c4021500c6a4460f08441003040001c0c07040e4010050240500000b462081c0344004441d070510a00508140c0103980441c45941031901100d0014041d640d54a61004140003041e600d544a002091030801400340d40002442052040002d0014680c0654181c9400f166240070590340c0f201080191102592100c85000c21820040c8244d8040d801d4000100c2c0107090941c0e100204404840c02e0201e5151004000000000c008085680c021826a1301d01d03418200c216208100c1180c2c10868011408002c051600000d019029984d5000c180c0340107220080052121088038034104122010034401200d903410588080741d01c140e0b00c41e281c4c0c03110301c41d282d00818880c0490780811600b0040850010f0600c148080c1c205204418160160300c950415002103a80381040e240003860124903a001c0c60100340c9003014090816030080442d65642c3d0101c1e0040342000d882c1700020704500c503821000350595403140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 44413358 1250 44412108 44412113
    0x50604090b0406051516020406050a0f03060c0201020a2001060320010e03060603030a0302071406010b071a060d060e15011413050601090302090a060305010212060f010903080a210207 80
    0xc101804000742590b05121465641301030194441103294492580c01040c030801c00343c00d103d0010b540036140014404284280c3d601c1c003090700460a0f0b000400541449041031080c480240030b00700501ea401d2008520307000c44440010706600c000d07240007200507003050b9094040d50003500002c000d1500590f2400364a8074030198401c00051540e030031030103c2e01103000041c00c0e140c040b82d424400d50000c1d004c0c0d40f50452420088000398003103042100c0045003002000c4c606403003008414060103c480d4031039529100c9003040025010512881901546110b08200f4152140d0710323811900c41d40030902045001e0400c40c0d280c241411b8442210741820703500c000181454508402009040b0192044440c41445a05030001d840040301d215001c114a551f0810040c180840f800c2d80c00701300c0a50000e007090700c0799911820b91b031003403200200345504c0b102407111900d410b40030500580b00074213002d0b002e145560b40d06031503070140038800030a22000e04140460750300742050554542c8024801195501c1c1d051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 44414608 1250 44413358 44413361
    0x506070314060307030c05060c0a05060103030305240f010302030606190905010f050c0622060501090212090102120f1f0b040303020c03030c0709020f070b0f07031808090409030905060409 82
    0x281e4040d00d00058503400b05160b418082252001c3e80d400000e417100c0746040509219581d44071900411044c4141400d010228000b031020030701a500c250360100385c90509a0303661968064441748180815002d00d9032003580d0fa51344070071046185007170a0160300c9035207440c00120ac038002c000f8007180c290f0f0060108031902c1d5008112105036403090300c0d13160084c9403103001104d850250314030003411540102c5c04221128100102240801070317240c401a80142c0b01c0d541c1b01d00380d81c0203074054520150042402021071800003aa254450544002103050074401c0c01080b1140c4009070150740011a0203003c65103407c641200310404004074222001210340c0c40c10568200c0c0e000e0f01c410340041c05810b00c2c4009c50300d0040b04942e2100414001031180c14180503420001798452107124900c06020040100081d0100b5109842030710a0303070400c00d141c50001c1c0b0140698503040303034403400151960368080004032407409403001caa43c240d80010300d4124614060307072455015042154014000f050005046509 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 44415858 1250 44414608 44414621
    0xa0305010c0806040e0a0c0b0708040b0a030f0b0603130609050c03071710050408040611010204170c01030b03010507090911040306050f070f0203160305090d14100501120b060112020705060703 84
    0x10380c4c081020080140220780c0351040c91200030022519107404010024a20000e81286402181042e2030a5030360280c101c0e0765170000c4415008682c5a08542103408600c0c460707a0612201030700c00030b103140b401c54a11690703500c00701c400800c190741d29160601805010042c5c811502c1019041340d1901c0e8607101210405004902a0750042c0306008280708881014000c2034016070744801c0c000d05103824103105548900000b1314998a039075084c03000041c0303400c901c0d005031040900900548210a00c0c000010223581e075100c00325000740c0c140818091300342e50000202049a02400f070014503200604814241c503c107580c4042d14680c1844240315030400794840b074034021202900d451181d20041d26050ba180d0180fa0384905500b914490a2804a8003a03001041c0c0c929008060120144590780d91802a4807484d00e042056440000c440d54001d420344039640c0540750f1051410304c282c00c155241464400d0044c416810411004514503901d01a03030180c40b40c080e030000503203169107801103008004269 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 44417108 1250 44415858 44415871
    0x30c041701022a0307020a030c090e06070207091d030a05030f0106080105010503060f030a0b07020609010609020c0307080703090306020f07060c05090102060703050601110604050c09010b0a021009020a0305010c08 93
    0x2111810800600d014421503211541c01c1142001181125034000002c00c01d240c031002c610b000402403c40140e0717402030301c0401b5601c200c940c400142d045c42881400c40e101e12404000641c042c00900450580010343c9a003240c1440502003001c0100d811110901c1e030080079428201d200c04a0641384054000e4095441011441008501d076039032950112030202d000c3c0300340c0d800700b042000818018203214600c03146402c000f8044910002c1c072681c0e1601e02000442d030800c01031f0003030401c0c0049140c0030f0203010000c0c0340003c000c0d400e120483c040d4544910a1040041140134005000303001c050080707907000c0065420220840d1101e619060303068150340034600031a00c15242c40150f4100301e00800c1030310184007040c1c2c014185039440641c00e0340180400360030117050149800e04440040700802c5618400c0c0c4c07092010300102c076200c100380582030030103810400321442c0c10302c041ca8203140c0c0000e4902c4c440c1e02050000c00d0300007040c00481c0c00c200458002408650818040103800343d0002842400b492 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 44418358 1250 44417108 44417129
    0xc1e0f170c01090303050a0806041107060e0606040902030c09090f0303010902070b01050604030305070609030201060812040504051302030312060d060216030e150f0304080d050124030c05190e06030c04 88
    0x1c010401101ca00a8070f02004000c030b1414001c4a0701c5602c41c043c15540f206c005000020382040c201c1c0f0740882c5400501c001c50703a42d40c940c01d04068460083c8101500940c0c203903000d0000440c0c980c0000d031100c0d140b4900324001d00c010b80009410701404c000307814401207004180c0b962540c4070034500d03000e50300c000000d035001460503000189a0400804540880390944c0d03d1a00f80000b0b80c0d1084041c0101510603030456480720404101c00d03106200c00e079110501c01002d569940e24203001d02095500017810103104020740b071282e801503240481116100c200d00c1244103a50b582d004000b8444294040000e0a10b62003c0b44079402510b05c5101d988043d070003615202400142a401c100014201d03011100f0711280c20301419583e090054040d41d041481401e18508001407129004200d4009900031601410000b8660700c02c003140031030040c0140c50078581480307882a080c2d03000d40300f84540d00d94200da41d000300944000062140702c86030410320000307002940c2c07070034060048a044c0c0c200b8050303003d004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 44419608 1250 44418358 44418373
    0x30304270c02030a0f03020c0a020402040609080c0901050105070f050f060c0d0b0f10050711040509060402011209030503130510060b030a0c0201140106051303050d080708130c1e0f17 80
    0x20b8000001e8400001443c2d54221102c0039400007100a50401304800e8203d2041d01d01110051761240003030f0010300b5840c0c1d42d0342314451404c2c250303070b04d0040140f021600540801c001846140d0340082114100c3e6044000a00c51009620b8020f1800c18892001c007a1805090140f0461880e041c000703000b139a540300b409100c00c207548010000101c28a0100d41d074050300310340441c403640e400341024062a41c051016503541c8424036000c10b09403001195020440d80002040104541e089a0790700800c85000d02c08200701280c555016200d44000b40181d00008100701c00003007041410405184501242e802c24442682d440c002c42d0f1942c0c000303a030484940e90a000201142a205110303000c41901904000d10442c4d00c6d080c0155503079030110707502c2c01200140e0741020021a10421140d6801211680e50a90900c0c100300010190240030304400d030b101204210303507000f050340c1007040019203403504001e00d18210390706096481d500c5c940e8008080c3c4003001c0300004010b0198040c049208060720180c1c0d070803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 44420858 1250 44419608 44419631
    0x3190203190b120c01030509010204170a060c0c0803040213020f070f020f010f09090f0605060c03070b0106030501080607110f011401031a010e0f0c0403150b01180815040203030427 79
    0xb10443e03210b10000758001800a25150300c203800280d00a000c081c001441c064903043c908098644010766031025074040802c400410825109000700000c035860032100d11074031559400c0661001400280c03013070b0440d0a04ca10907203050340c11101d43e50f41c04011640d880103146482e91010030f4410b41a40320300303100565807507a9406050226081c1c910766070741c1d1101c42c1c14000303410014000743c115404580d1342c4503000301d155103ea0000b802140e44130300c0110703100c045034604007a00001c1600000d041504050041000d00784c00100907030450050300b891241c0e980c2d861401480e1048c1001038a03003560a101349180c455011054690699000d00c0c82280002c601000082001a084c40383d20f2640214200003071340081c0e4200142d410060340c40045250a40d41d4450308465400a40b041544a03a074030868079156030070412031110810013181c0c11041c2c52510fa074098840b42034504006644100e0b0300003904640e020320071500038007000c007210600380f05100c038841d0403050b61300310b0f10096a141c0944c1034103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 44422108 1250 44420858 44420869
    0xf091503010b0105031501030f0b19030c050102160302090703090b0a02070203151312020307020a0902040503061b19050405101e030e2e0608010510090e1203190203190b 74
    0x1c81e030660312034402c105041d8401140140310084885005558803280c10030b032b555550860401c45203001c9216100385080d410310048a1100e0350119041d0340c07040d0081c42825050b0079000c4102c903011656000c80c1d42d5040004e8018011000004114200c02d5080042d112025806080198020340458a901c50074421203001004152210441c07404094017120025003035001060600140e8819641029010340c045207070070005030412440c0ca03402150600941c1010000c0035404170b81e00019600d103c94840c0d005085101d10381001487d000040000c0c0324030b9000e03808036802003d0242901182404a201c000c01c444040340074031080b685038203850442c25110f40144140c072401c800180c4a03101c40c03000c007030400254145100034143e00c0410620803c00d000e218040041c0302480020819140a0f04a41c105442c65000b11440501d4001b28003c101000618030702c0380140109001d5581d12010399030390b0104416045903002500000400032840440310343c2c0e04c40c290300c04034103102d1034400004004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 44423358 1250 44422108 44422111
    0x14010906020a2a0809030f0d0215160f0807090807150305010e09030d020a170906060f01110c0609010c0b01080a1106040b0901120e070e090609030f0a05090f091503010b010503 77
    0x40340700750f800c199010803801d20092130002d50090450f0440301c40e0001d42814400402c04e4280541c1140c00c100003a04c005101465200e1b500d08458442c80454031400b40c140c01c2049106000c1100c20000600460b010741030240241c00310350301320340407a0764072000c1141000f1440440030001e400c110000400c3c1c1d80818180340034400303403000b075030810070b00190800007508104158410061004101269a191000014000c0c2c4032903010b0501ca1501c4070510890910301c5903010304000324914800b0314004040b400d10071507182102c080355245040b400488030b0741c06021015000500708400010701070000104071181601c1005d1183c400c410400c01c000a40c0154400c44004241c06c018000c91507208405800c210090340d200003442e081e001d40110700d0045941c01c2004084222010b0000c440b0003009150713070214040740154541401502c016806000b4140d400042c02000b146c00e00a658450304130080c4c80c3d2004d08404001d281c404d65412140d04030000c9103000754030b05100d400840d44a4000c49 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 44424464 1106 44423358 44423417
    0x203090d0906050a0e011b020301050c040603051e070e01030905070b04140906011b050f0d120f090209130809040504030806011701120b0414010906020a 67
    0x2520311a06900312000f48241032202d440525840302142048030310030318203443c109450307030380261056035250b900039415400c00d020407406040000140c02281d000c4c4d542401140c60364880110301c00c80d035403c07110043c0482000124060300441024074060810b1400103014485078035a00e0409030f841d00444842c482c0040c0c10845603070360000d000d800301c0302110702040c01d090500c0041c080c90400400034a040c154001000180001400041c00c1001c8210942e0b00140b1031000041c11400741c13100c800407030b5240411110401c50031340b0400784440d6001d041800c281d115524650f1a941741244211009901000100d20f00d8075a0700805000710702c681c0310101c6c0c90516034000b41140b4141d0000500d1881784500400c40da5502c40780100e0000c1d0441c0d00c43d8482d444508000d43d000d07036400308015556080500050030440113500034850341c030b00c650321160380c05072051000c200344007200d081 = true := by decide +kernel

theorem cover : BRFrame.Cov 44244608 44424464 := by
  have h0 := BRFrame.cov_init 44244608
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 44244608 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 44244608 ≤ n) (h2 : n < 44424464) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
